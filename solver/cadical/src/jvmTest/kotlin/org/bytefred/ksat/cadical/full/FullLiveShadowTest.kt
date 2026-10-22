package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.DimacsCnf
import org.junit.AssumptionViolatedException
import java.io.File
import java.util.concurrent.ArrayBlockingQueue
import java.util.concurrent.ExecutionException
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.test.Test
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * LIVE shadow test (JVM only) for the FULL CaDiCaL 2.1.3 port: no golden trace files. For every
 * case the instrumented upstream reference `ksat-extra/shadow/cadical-full/build/cadical_full_trace`
 * (build it with `bash ksat-extra/shadow/cadical-full/build_and_trace.sh --build-only`) runs as a
 * child process with `LSTRACE=1` (proof tracer connected, LSPROOF unset); its stdout is streamed
 * line by line, filtered like build_and_trace.sh does (lines starting with `s ` or `c ` are
 * dropped), and compared incrementally against the lines [runShadow] produces for the same
 * arguments. Memory stays bounded: a bounded queue between the C reader thread and the Kotlin
 * sink, plus a 5-line ring buffer for the context of the first difference.
 *
 *   L1   -- identical trace (incl. RESULT and MODEL lines), same exit code.
 *   FAIL -- first differing line with +-5 lines of context, or a crash / timeout.
 *
 * On SAT the MODEL must also satisfy the CNF and the assumptions.
 *
 * Suites (each its own test, each skips visibly without ksat-extra or the C binary):
 *   cnfFull    every line `<file> <args...>` of shadow/cnf-full/OPTIONS under `--config=default`
 *              plus those args (`--name=value` options and `--limit:<name>=<n>` limits; both
 *              drivers get exactly the same arguments)
 *   cnfAssume  every shadow/cnf-assume/<name>.cnf with <name>.assume, under plain and default
 *   bigPhp     php_10_9 (shadow/cnf) under default, only with -Dbigtrace
 * Filters (forwarded by build.gradle.kts): -Dfullshadow.only=<case-name>,... (file name without
 * .cnf), -Dfullshadow.configs=plain (cnfAssume only).
 *
 * Timings: "kotlin ms" is the [runShadow] run including the comparison; "C ms" is a separate run
 * of the C binary with LSTRACE=1 and stdout discarded (the live run is throttled by the Kotlin
 * consumer, so it cannot be timed).
 */
class FullLiveShadowTest {

    private class Case(val name: String, val config: String, val cnf: File, val assume: File?,
                       val args: List<String>, val timeoutSeconds: Long) {
        val label: String get() = (listOf(config, name) + args).joinToString(" ")
    }

    private class Outcome(val case: Case, val level: String, val kotlinMs: Long, val cMs: Long,
                          val lines: Long, val detail: String?)

    /** Thrown from the sink to stop the Kotlin run once enough context after a difference is collected. */
    private class Stop : RuntimeException()

    private object Eof

    // ------------------------------------------------------------------ environment

    private fun locateShadowDir(): File? {
        var dir: File? = File(System.getProperty("user.dir")).absoluteFile
        while (dir != null) {
            val candidate = File(dir, "ksat-extra/shadow")
            if (candidate.isDirectory) return candidate
            dir = dir.parentFile
        }
        return null
    }

    private fun prop(name: String): List<String>? =
        System.getProperty(name)?.split(',')?.map { it.trim() }?.filter { it.isNotEmpty() }
            ?.takeIf { it.isNotEmpty() }

    private fun shadowAndBinary(): Pair<File, File> {
        val shadow = locateShadowDir() ?: skip("no ksat-extra/shadow found",
            "`git submodule update --init --checkout ksat-extra`, then `bash $BUILD --build-only`")
        val bin = File(shadow, "cadical-full/build/cadical_full_trace")
        if (!bin.canExecute()) skip("C reference binary $bin missing", "`bash $BUILD --build-only`")
        return shadow to bin
    }

    // ------------------------------------------------------------------ argument parsing

    /** The driver arguments: `--name=value` -> options, `--limit:<name>=<n>` -> limits. */
    private fun splitArgs(args: List<String>): Pair<List<Pair<String, Int>>, List<Pair<String, Int>>> {
        val options = ArrayList<Pair<String, Int>>()
        val limits = ArrayList<Pair<String, Int>>()
        for (a in args) {
            val m = Regex("--(limit:)?([A-Za-z0-9_]+)=(-?[0-9]+)").matchEntire(a)
                ?: fail("$TAG unsupported driver argument '$a'")
            val pair = m.groupValues[2] to m.groupValues[3].toInt()
            if (m.groupValues[1].isEmpty()) options += pair else limits += pair
        }
        return options to limits
    }

    /** Same reading as driver.cpp: whitespace separated signed integers, zeros ignored by assume. */
    private fun readAssumptions(f: File): IntArray =
        f.readText().split(Regex("\\s+")).filter { it.isNotEmpty() }
            .map { it.toIntOrNull() ?: fail("$TAG bad assumptions file $f") }.toIntArray()

    // ------------------------------------------------------------------ C process

    private fun command(bin: File, c: Case): List<String> =
        listOf(bin.path, "--config=${c.config}") + c.args + listOfNotNull(c.cnf.path, c.assume?.path)

    private fun processBuilder(bin: File, c: Case): ProcessBuilder =
        ProcessBuilder(command(bin, c)).also {
            it.environment()["LSTRACE"] = "1"
            it.environment().remove("LSPROOF")
        }

    private fun timeC(bin: File, c: Case): Long {
        val t0 = System.nanoTime()
        val p = processBuilder(bin, c)
            .redirectOutput(ProcessBuilder.Redirect.DISCARD)
            .redirectError(ProcessBuilder.Redirect.DISCARD).start()
        if (!p.waitFor(c.timeoutSeconds, TimeUnit.SECONDS)) {
            p.destroyForcibly()
            return -1
        }
        return (System.nanoTime() - t0) / 1_000_000
    }

    // ------------------------------------------------------------------ one case

    private fun runOne(bin: File, c: Case): Outcome {
        val (options, limits) = splitArgs(c.args)
        val assumptions = c.assume?.let { readAssumptions(it) }
        val cnfText = c.cnf.readText()

        val proc = processBuilder(bin, c).start()
        val queue = ArrayBlockingQueue<Any>(QUEUE_CAPACITY)
        val stopped = AtomicBoolean(false)
        val stderr = StringBuilder()
        val reader = Thread {
            try {
                proc.inputStream.bufferedReader().useLines { seq ->
                    for (line in seq) {
                        if (line.startsWith("s ") || line.startsWith("c ")) continue
                        while (!stopped.get() && !queue.offer(line, 100, TimeUnit.MILLISECONDS)) Unit
                        if (stopped.get()) return@useLines
                    }
                }
            } catch (_: java.io.IOException) {
                // process destroyed after a difference
            }
            while (!stopped.get() && !queue.offer(Eof, 100, TimeUnit.MILLISECONDS)) Unit
        }.apply { isDaemon = true; start() }
        val errReader = Thread {
            try {
                proc.errorStream.bufferedReader().forEachLine { if (stderr.length < 4000) synchronized(stderr) { stderr.appendLine(it) } }
            } catch (_: java.io.IOException) {
            }
        }.apply { isDaemon = true; start() }

        // Comparison state, only touched by the Kotlin solver thread (and read after it ended).
        val ring = ArrayDeque<String>()
        var lineNo = 0L
        var diffAt = -1L
        var cDiff: String? = null
        var kDiff: String? = null
        val kAfter = ArrayList<String>()
        var lastModel: String? = null
        var cTimeout = false

        fun nextC(): Any? = queue.poll(C_LINE_TIMEOUT_SECONDS, TimeUnit.SECONDS)

        val sink: (String) -> Unit = sink@{ line ->
            if (diffAt >= 0) {
                kAfter += line
                if (kAfter.size >= CONTEXT) throw Stop()
                return@sink
            }
            val cl = nextC()
            if (cl == null) { cTimeout = true; throw Stop() }
            lineNo++
            if (cl === Eof || cl != line) {
                diffAt = lineNo
                cDiff = if (cl === Eof) null else cl as String
                kDiff = line
                return@sink
            }
            if (line.startsWith("MODEL ")) lastModel = line
            ring.addLast(line)
            if (ring.size > CONTEXT) ring.removeFirst()
        }

        val exec = Executors.newSingleThreadExecutor { r -> Thread(r).apply { isDaemon = true } }
        val t0 = System.nanoTime()
        var error: Throwable? = null
        var kotlinRes = -1
        try {
            kotlinRes = exec.submit<Int> {
                runShadow(cnfText, c.config, options, assumptions, limits, sink)
            }.get(c.timeoutSeconds, TimeUnit.SECONDS)
        } catch (e: TimeoutException) {
            error = e
        } catch (e: ExecutionException) {
            error = e.cause ?: e
        } finally {
            exec.shutdownNow()
        }
        val kotlinMs = (System.nanoTime() - t0) / 1_000_000
        if (error is Stop) error = null

        // Kotlin finished without a difference: C must end here too.
        if (error == null && diffAt < 0 && !cTimeout) {
            val cl = nextC()
            if (cl == null) cTimeout = true
            else if (cl !== Eof) { diffAt = lineNo + 1; cDiff = cl as String; kDiff = null }
        }
        val cAfter = ArrayList<String>()
        if (diffAt >= 0 && cDiff != null) {
            while (cAfter.size < CONTEXT) {
                val cl = nextC()
                if (cl == null || cl === Eof) break
                cAfter += cl as String
            }
        }

        // C exit code (only meaningful when it ran to the end).
        var cRc: Int? = null
        if (diffAt < 0 && error == null && !cTimeout) {
            if (proc.waitFor(c.timeoutSeconds, TimeUnit.SECONDS)) cRc = proc.exitValue()
        }
        stopped.set(true)
        proc.destroyForcibly()
        reader.join(2000)
        errReader.join(2000)

        val problems = ArrayList<String>()
        if (error != null) problems += when (error) {
            is TimeoutException -> "TIMEOUT after ${c.timeoutSeconds}s"
            else -> "EXCEPTION ${error.javaClass.name}: ${error.message}\n" +
                error.stackTrace.take(12).joinToString("\n") { "      at $it" }
        }
        if (cTimeout) problems += "C reference produced no line for ${C_LINE_TIMEOUT_SECONDS}s"
        if (cRc != null && cRc != 10 && cRc != 20)
            problems += "C reference exited with $cRc; stderr:\n$stderr"
        if (cRc != null && cRc != kotlinRes) problems += "exit code: C $cRc, kotlin $kotlinRes"
        if (diffAt < 0 && problems.isEmpty()) {
            val model = lastModel
            if (model != null) {
                val values = HashMap<Int, Boolean>()
                for (l in model.removePrefix("MODEL ").trim().split(' ').map { it.toInt() }.filter { it != 0 })
                    values[kotlin.math.abs(l)] = l > 0
                if (!DimacsCnf.parse(cnfText).isSatisfiedBy { v -> values[v] ?: false })
                    problems += "MODEL does not satisfy the CNF"
                for (a in assumptions ?: IntArray(0))
                    if (a != 0 && values[kotlin.math.abs(a)] != (a > 0)) problems += "MODEL violates assumption $a"
            }
            if (problems.isEmpty()) return Outcome(c, "L1", kotlinMs, timeC(bin, c), lineNo, null)
        }

        val sb = StringBuilder("[${c.label}]\n")
        for (p in problems) sb.append(p).append('\n')
        if (diffAt >= 0) {
            sb.append("first differing line $diffAt\n")
            var i = diffAt - ring.size
            for (l in ring) sb.append("    %9d  ".format(i++)).append(l).append('\n')
            sb.append("  C > %9d  ".format(diffAt)).append(cDiff ?: "<end of C trace>").append('\n')
            for ((k, l) in cAfter.withIndex()) sb.append("  C   %9d  ".format(diffAt + 1 + k)).append(l).append('\n')
            sb.append("  K > %9d  ".format(diffAt)).append(kDiff ?: "<end of kotlin trace>").append('\n')
            for ((k, l) in kAfter.withIndex()) sb.append("  K   %9d  ".format(diffAt + 1 + k)).append(l).append('\n')
        }
        val level = when {
            error != null || cTimeout -> "CRASH"
            diffAt >= 0 -> "DIFF@$diffAt"
            else -> "FAIL"
        }
        return Outcome(c, level, kotlinMs, timeC(bin, c), lineNo, sb.toString())
    }

    private fun runAll(suite: String, cases: List<Case>, bin: File) {
        val only = prop("fullshadow.only")?.toSet()
        val selected = cases.filter { only == null || it.name in only }
        if (selected.isEmpty()) skip("$suite: no case selected (fullshadow.only=$only)", "drop the filter")
        val outcomes = ArrayList<Outcome>()
        for (c in selected) {
            val o = runOne(bin, c)
            outcomes += o
            println("$TAG $suite %-10s %8d kt-ms %7d C-ms %9d lines  %s".format(o.level, o.kotlinMs, o.cMs, o.lines, c.label))
        }
        println("$TAG $suite summary:")
        println("  %-10s %9s %8s %9s  %s".format("level", "kotlin ms", "C ms", "lines", "case"))
        for (o in outcomes) println("  %-10s %9d %8d %9d  %s".format(o.level, o.kotlinMs, o.cMs, o.lines, o.case.label))
        val bad = outcomes.filter { it.level != "L1" }
        for (o in bad) println(o.detail)
        assertTrue(bad.isEmpty(), "$TAG $suite not L1: ${bad.map { "${it.case.label}=${it.level}" }}")
    }

    // ------------------------------------------------------------------ suites

    @Test
    fun cnfFull() {
        val (shadow, bin) = shadowAndBinary()
        val dir = File(shadow, "cnf-full")
        val manifest = File(dir, "OPTIONS")
        if (!manifest.isFile) fail("$TAG missing $manifest")
        val cases = manifest.readLines().map { it.trim() }.filter { it.isNotEmpty() && !it.startsWith("#") }.map { line ->
            val parts = line.split(Regex("\\s+"))
            val cnf = File(dir, parts[0])
            if (!cnf.isFile) fail("$TAG $manifest lists missing ${parts[0]}")
            Case(cnf.nameWithoutExtension, "default", cnf, null, parts.drop(1), TIMEOUT_SECONDS)
        }
        runAll("cnf-full", cases, bin)
    }

    @Test
    fun cnfAssume() {
        val (shadow, bin) = shadowAndBinary()
        val dir = File(shadow, "cnf-assume")
        val cnfs = dir.listFiles { f -> f.name.endsWith(".cnf") }?.sortedBy { it.name }
            ?: fail("$TAG missing $dir")
        val configs = prop("fullshadow.configs") ?: listOf("plain", "default")
        val cases = configs.flatMap { cfg ->
            cnfs.map { cnf ->
                val assume = File(dir, cnf.nameWithoutExtension + ".assume")
                if (!assume.isFile) fail("$TAG missing $assume")
                Case(cnf.nameWithoutExtension, cfg, cnf, assume, emptyList(), TIMEOUT_SECONDS)
            }
        }
        runAll("cnf-assume", cases, bin)
    }

    @Test
    fun bigPhp() {
        val big = System.getProperty("bigtrace")?.lowercase()?.let { it !in setOf("false", "0", "no", "off") } ?: false
        if (!big) skip("php_10_9 live comparison needs -Dbigtrace", "add -Dbigtrace")
        val (shadow, bin) = shadowAndBinary()
        val cnf = File(shadow, "cnf/php_10_9.cnf")
        if (!cnf.isFile) fail("$TAG missing $cnf")
        runAll("big", listOf(Case("php_10_9", "default", cnf, null, emptyList(), BIG_TIMEOUT_SECONDS)), bin)
    }

    private companion object {
        const val TAG = "[full-live]"
        const val BUILD = "ksat-extra/shadow/cadical-full/build_and_trace.sh"
        const val CONTEXT = 5
        const val QUEUE_CAPACITY = 1 shl 16
        const val TIMEOUT_SECONDS = 240L
        const val BIG_TIMEOUT_SECONDS = 1800L
        const val C_LINE_TIMEOUT_SECONDS = 60L

        fun skip(reason: String, steps: String): Nothing {
            val msg = "$TAG SKIPPED: $reason. These are optional live trace-comparison tests (ksat-extra); " +
                "to run them: $steps."
            System.err.println(msg)
            throw AssumptionViolatedException(msg)
        }
    }
}
