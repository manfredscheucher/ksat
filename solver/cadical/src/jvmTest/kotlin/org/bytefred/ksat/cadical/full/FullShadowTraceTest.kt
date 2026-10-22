package org.bytefred.ksat.cadical.full

import org.bytefred.ksat.DimacsCnf
import org.junit.AssumptionViolatedException
import java.io.File
import java.util.concurrent.ExecutionException
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException
import kotlin.test.Test
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * Shadow test (JVM only) for the FULL CaDiCaL 2.1.3 port ([runShadow]) against the
 * instrumented real upstream solver (ksat-extra/shadow/cadical-full, see its README).
 *
 * For every `shadow/cnf/<name>.cnf` and every config in {plain, default} with a golden trace
 * `shadow/golden-cadical-full-<config>/<name>.trace`, run [runShadow] exactly like
 * build_and_trace.sh runs the C driver (`--config=<config>`, no further options, proof tracer
 * connected, no assumptions) and compare line by line:
 *
 *   L1 -- identical trace (this includes the RESULT line and, on SAT, the MODEL line).
 *   FAIL -- anything else: the first differing line is reported with +-5 lines of context.
 *
 * Independently of the trace, the verdict must match the golden RESULT and on SAT the
 * MODEL must satisfy the CNF.
 *
 * The golden trace is streamed and compared line by line (bounded memory). On a mismatch only the
 * context report (+-5 lines, a few KB) is written to
 * `solver/cadical/build/full-shadow/<config>/<name>.diff.txt`; the trace itself is never stored. Filters (forwarded by build.gradle.kts):
 *   -Dfullshadow.only=php_3_2,sat_small   only these CNFs
 *   -Dfullshadow.configs=plain            only these configs
 *   -Dbigtrace                            include php_10_9 (needs BIG=1 goldens)
 */
class FullShadowTraceTest {

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

    private class Outcome(val name: String, val config: String, val level: String, val millis: Long,
                          val lines: Long, val detail: String?)

    /** Thrown from the sink to stop the port once enough context after a difference is collected. */
    private class Stop : RuntimeException()

    /**
     * Streams the golden trace and compares each line of the port as it is produced, so memory
     * stays bounded (php_9_8 has 1.4M lines; holding both traces does not fit a 512 MB test heap).
     * Context: a ring buffer of the last [CONTEXT] equal lines plus up to [CONTEXT] lines after the
     * first difference from each side.
     */
    private fun runOne(cnfFile: File, goldFile: File, config: String, outDir: File): Outcome {
        val name = cnfFile.nameWithoutExtension
        val cnfText = cnfFile.readText()
        val gold = goldFile.bufferedReader()
        // Empty lines are skipped (none are expected; build_and_trace.sh keeps them).
        fun nextGold(): String? {
            while (true) {
                val l = gold.readLine() ?: return null
                if (l.isNotEmpty()) return l
            }
        }

        val ring = ArrayDeque<String>()
        var lineNo = 0L
        var diffAt = -1L
        var gDiff: String? = null
        var kDiff: String? = null
        val kAfter = ArrayList<String>()
        var lastResult: String? = null
        var lastModel: String? = null

        val sink: (String) -> Unit = sink@{ line ->
            if (diffAt >= 0) {
                kAfter += line
                if (kAfter.size >= CONTEXT) throw Stop()
                return@sink
            }
            val g = nextGold()
            lineNo++
            if (g != line) {
                diffAt = lineNo; gDiff = g; kDiff = line
                return@sink
            }
            if (line.startsWith("RESULT ")) lastResult = line
            if (line.startsWith("MODEL ")) lastModel = line
            ring.addLast(line)
            if (ring.size > CONTEXT) ring.removeFirst()
        }

        val exec = Executors.newSingleThreadExecutor { r -> Thread(r).apply { isDaemon = true } }
        val t0 = System.nanoTime()
        var error: Throwable? = null
        try {
            exec.submit<Int> {
                runShadow(cnfText, config, emptyList(), null, sink = sink)
            }.get(TIMEOUT_SECONDS, TimeUnit.SECONDS)
        } catch (e: TimeoutException) {
            error = e
        } catch (e: ExecutionException) {
            error = e.cause ?: e
        } finally {
            exec.shutdownNow()
        }
        val millis = (System.nanoTime() - t0) / 1_000_000
        if (error is Stop) error = null

        // The port ended without a difference: the golden trace must end here too.
        if (error == null && diffAt < 0) {
            val g = nextGold()
            if (g != null) { diffAt = lineNo + 1; gDiff = g; kDiff = null }
        }
        val gAfter = ArrayList<String>()
        if (diffAt >= 0 && gDiff != null)
            while (gAfter.size < CONTEXT) gAfter += nextGold() ?: break
        gold.close()

        val errText = when (error) {
            null -> null
            is TimeoutException -> "TIMEOUT after ${TIMEOUT_SECONDS}s"
            else -> "EXCEPTION ${error.javaClass.name}: ${error.message}\n" +
                error.stackTrace.take(12).joinToString("\n") { "      at $it" }
        }

        // Verdict + model (on a full match the RESULT/MODEL lines are the golden ones).
        val problems = ArrayList<String>()
        if (error == null && diffAt < 0) {
            val model = lastModel
            if (lastResult == "RESULT SAT") {
                if (model == null) problems += "SAT without MODEL line"
                else {
                    val values = HashMap<Int, Boolean>()
                    for (l in model.removePrefix("MODEL ").trim().split(' ').map { it.toInt() }.filter { it != 0 })
                        values[kotlin.math.abs(l)] = l > 0
                    if (!DimacsCnf.parse(cnfText).isSatisfiedBy { v -> values[v] ?: false })
                        problems += "MODEL does not satisfy the CNF"
                }
            }
            if (problems.isEmpty()) return Outcome(name, config, "L1", millis, lineNo, null)
        }

        val sb = StringBuilder("[$config/$name] ")
        if (errText != null) sb.append(errText).append('\n')
        for (p in problems) sb.append(p).append('\n')
        if (diffAt >= 0) {
            sb.append("first differing line $diffAt\n")
            var i = diffAt - ring.size
            for (l in ring) sb.append("         %9d  ".format(i++)).append(l).append('\n')
            sb.append("  golden > %9d  ".format(diffAt)).append(gDiff ?: "<end of golden trace>").append('\n')
            for ((k, l) in gAfter.withIndex()) sb.append("  golden   %9d  ".format(diffAt + 1 + k)).append(l).append('\n')
            sb.append("  kotlin > %9d  ".format(diffAt)).append(kDiff ?: "<end of kotlin trace>").append('\n')
            for ((k, l) in kAfter.withIndex()) sb.append("  kotlin   %9d  ".format(diffAt + 1 + k)).append(l).append('\n')
        }
        // Only the context report goes to disk (a few KB), never the trace itself.
        File(outDir, config).mkdirs()
        File(File(outDir, config), "$name.diff.txt").writeText(sb.toString())
        val level = if (error != null) "CRASH" else if (diffAt >= 0) "DIFF@$diffAt" else "FAIL"
        return Outcome(name, config, level, millis, lineNo, sb.toString())
    }

    @Test
    fun fullPortMatchesUpstreamTraces() {
        val shadow = locateShadowDir() ?: skip("no ksat-extra/shadow found",
            "`git submodule update --init --checkout ksat-extra`, then `bash $REGEN`")
        val only = prop("fullshadow.only")?.toSet()
        val configs = prop("fullshadow.configs") ?: CONFIGS
        val big = System.getProperty("bigtrace")?.lowercase()?.let { it !in setOf("false", "0", "no", "off") } ?: false
        val cnfDir = File(shadow, "cnf")
        val cnfs = cnfDir.listFiles { f -> f.name.endsWith(".cnf") }?.sortedBy { it.length() }
            ?: fail("$TAG missing $cnfDir")
        val outDir = File(System.getProperty("user.dir"), "build/full-shadow")

        val outcomes = ArrayList<Outcome>()
        var ran = 0
        for (config in configs) {
            val goldDir = File(shadow, "golden-cadical-full-$config")
            if (goldDir.listFiles { f -> f.name.endsWith(".trace") }.isNullOrEmpty())
                skip("no golden traces in $goldDir", "`bash $REGEN`")
            for (cnf in cnfs) {
                val name = cnf.nameWithoutExtension
                if (only != null && name !in only) continue
                if (name == "php_10_9" && !big) continue
                val gold = File(goldDir, "$name.trace")
                if (!gold.isFile) fail("$TAG no golden trace $gold; run `bash $REGEN`")
                ran++
                val o = runOne(cnf, gold, config, outDir)
                outcomes += o
                println("$TAG %-8s %-20s %-10s %7d ms  %8d lines".format(config, name, o.level, o.millis, o.lines))
            }
        }
        if (ran == 0) fail("$TAG no instance selected (filters only=$only configs=$configs)")

        println("$TAG summary (mismatch reports in $outDir):")
        println("  %-8s %-20s %-10s %9s %9s".format("config", "instance", "level", "ms", "lines"))
        for (o in outcomes) println("  %-8s %-20s %-10s %9d %9d".format(o.config, o.name, o.level, o.millis, o.lines))
        val bad = outcomes.filter { it.level != "L1" }
        for (o in bad) println(o.detail)
        assertTrue(bad.isEmpty(), "$TAG not L1: ${bad.map { "${it.config}/${it.name}=${it.level}" }}")
    }

    private companion object {
        const val TAG = "[full-shadow]"
        const val REGEN = "ksat-extra/shadow/cadical-full/build_and_trace.sh"
        val CONFIGS = listOf("plain", "default")
        const val TIMEOUT_SECONDS = 240L
        const val CONTEXT = 5

        fun skip(reason: String, steps: String): Nothing {
            val msg = "$TAG SKIPPED: $reason. These are optional trace-comparison tests (ksat-extra); " +
                "to run them: $steps."
            System.err.println(msg)
            throw AssumptionViolatedException(msg)
        }
    }
}
