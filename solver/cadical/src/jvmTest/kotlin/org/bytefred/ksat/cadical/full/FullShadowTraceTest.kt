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
 * On a mismatch the actual trace (up to 200 lines past the first difference) is written to
 * `solver/cadical/build/full-shadow/<config>/<name>.trace` for inspection. Filters (forwarded by build.gradle.kts):
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
                          val lines: Int, val detail: String?)

    /** Thrown from the sink when the port produces far more lines than the golden trace. */
    private class TooLong : RuntimeException()

    private fun runOne(cnfFile: File, goldFile: File, config: String, outDir: File): Outcome {
        val name = cnfFile.nameWithoutExtension
        val expected = goldFile.readLines().filter { it.isNotEmpty() }
        val cnfText = cnfFile.readText()
        val actual = ArrayList<String>(expected.size + 16)
        val maxLines = expected.size * 2 + 1000

        val exec = Executors.newSingleThreadExecutor { r -> Thread(r).apply { isDaemon = true } }
        val t0 = System.nanoTime()
        var error: Throwable? = null
        try {
            exec.submit<Int> {
                runShadow(cnfText, config, emptyList(), null) { line ->
                    if (actual.size >= maxLines) throw TooLong()
                    actual.add(line)
                }
            }.get(TIMEOUT_SECONDS, TimeUnit.SECONDS)
        } catch (e: TimeoutException) {
            error = e
        } catch (e: ExecutionException) {
            error = e.cause ?: e
        } finally {
            exec.shutdownNow()
        }
        val millis = (System.nanoTime() - t0) / 1_000_000

        val errText = when (error) {
            null -> null
            is TimeoutException -> "TIMEOUT after ${TIMEOUT_SECONDS}s"
            is TooLong -> "trace exceeded $maxLines lines (golden has ${expected.size})"
            else -> "EXCEPTION ${error.javaClass.simpleName}: ${error.message}\n" +
                error.stackTrace.take(12).joinToString("\n") { "      at $it" }
        }

        // Verdict + model, independent of the trace comparison.
        val verdictProblems = ArrayList<String>()
        if (error == null) {
            val goldResult = expected.lastOrNull { it.startsWith("RESULT ") }
            val result = actual.lastOrNull { it.startsWith("RESULT ") }
            if (goldResult != result) verdictProblems += "verdict: expected '$goldResult', got '$result'"
            if (result == "RESULT SAT") {
                val model = actual.lastOrNull { it.startsWith("MODEL ") }
                if (model == null) verdictProblems += "SAT without MODEL line"
                else {
                    val lits = model.removePrefix("MODEL ").trim().split(' ').map { it.toInt() }.filter { it != 0 }
                    val values = HashMap<Int, Boolean>()
                    for (l in lits) values[kotlin.math.abs(l)] = l > 0
                    val cnf = DimacsCnf.parse(cnfText)
                    if (!cnf.isSatisfiedBy { v -> values[v] ?: false })
                        verdictProblems += "MODEL does not satisfy the CNF"
                }
            }
        }

        val first = (0 until minOf(expected.size, actual.size)).firstOrNull { expected[it] != actual[it] }
            ?: if (expected.size == actual.size) null else minOf(expected.size, actual.size)
        if (first == null && error == null && verdictProblems.isEmpty())
            return Outcome(name, config, "L1", millis, actual.size, null)

        val sb = StringBuilder()
        sb.append("[$config/$name] ")
        if (errText != null) sb.append(errText).append('\n')
        for (p in verdictProblems) sb.append(p).append('\n')
        if (first != null) {
            sb.append("first differing line ${first + 1} (golden ${expected.size} lines, actual ${actual.size})\n")
            fun ctx(label: String, lines: List<String>) {
                sb.append("  --- $label\n")
                for (i in maxOf(0, first - 5)..minOf(lines.size - 1, first + 5))
                    sb.append(if (i == first) "  >" else "   ").append("%7d  ".format(i + 1)).append(lines[i]).append('\n')
            }
            ctx("golden", expected)
            ctx("kotlin", actual)
        }
        // Keep only the actual trace up to shortly after the divergence (disk space).
        File(outDir, config).mkdirs()
        val keep = if (first == null) actual.size else minOf(actual.size, first + 200)
        File(File(outDir, config), "$name.trace").writeText(actual.subList(0, keep).joinToString("\n", postfix = "\n"))
        val level = if (error != null) "CRASH" else "DIFF@${first?.plus(1) ?: "-"}"
        return Outcome(name, config, level, millis, actual.size, sb.toString())
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

        println("$TAG summary (mismatching traces in $outDir):")
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

        fun skip(reason: String, steps: String): Nothing {
            val msg = "$TAG SKIPPED: $reason. These are optional trace-comparison tests (ksat-extra); " +
                "to run them: $steps."
            System.err.println(msg)
            throw AssumptionViolatedException(msg)
        }
    }
}
