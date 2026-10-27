package org.bytefred.ksat.minisat

import org.junit.AssumptionViolatedException
import java.io.File
import java.util.concurrent.TimeUnit
import kotlin.test.Test
import kotlin.test.fail

/**
 * Live shadow test (JVM only) of [MiniSat] / [MiniSatSimp] against the instrumented real
 * upstream MiniSat, for both targets of the port:
 * - [portMatchesMasterLive]: default options of the port (meelgroup master 664490d) against
 *   ksat-extra/shadow/minisat-master (`build/minisat_master_trace`: master + fixes.patch, the
 *   bug fixes the port has, + trace.patch + driver.cpp);
 * - [csbCompatMatchesCsbLive]: [MiniSat.csbCompat] = true against ksat-extra/shadow/minisat-full
 *   (`build/minisat_full_trace`: meelgroup csb 9a0382d + trace.patch + driver.cpp).
 * No golden files: the reference is run with LSTRACE=1 for every case and its output is
 * compared line by line with the Kotlin trace produced by [MiniSatShadowDriver.run] (the Kotlin
 * mirror of driver.cpp). SKIPPED (visibly) when ksat-extra or a built reference binary is missing
 * (build with `bash ksat-extra/shadow/minisat-master/build_and_trace.sh --build-only` /
 * `bash ksat-extra/shadow/minisat-full/build_and_trace.sh --build-only`).
 *
 * Cases: shadow/cnf/, cnf-full/ and cnf-assume/ CNFs, core (--simp=0) and simp (--simp=1), each
 * under several upstream option sets (see [OPTION_SETS]). To keep the default test run short each
 * run compares only the first [QUICK_MAX_LINES] trace lines; env LIVESHADOW_FULL=1 compares the
 * complete traces (about a minute; php_10_9 additionally needs -Dbigtrace).
 * Filter: -Dliveshadow.only=php_3_2,sat_small (or env LIVESHADOW_ONLY=...)
 */
class MiniSatLiveShadowTest {

    private fun skip(reason: String): Nothing {
        System.err.println("$TAG SKIPPED: $reason")
        throw AssumptionViolatedException(reason)
    }

    /** Starts the reference binary with LSTRACE=1 (stderr goes to [errFile]). */
    private fun startReference(bin: File, simp: Int, opts: List<String>, cnf: File, assume: File?, errFile: File): Process {
        val cmd = ArrayList<String>()
        cmd += bin.path
        cmd += "--simp=$simp"
        cmd += opts
        cmd += cnf.path
        if (assume != null) cmd += assume.path
        val pb = ProcessBuilder(cmd).redirectError(ProcessBuilder.Redirect.to(errFile))
        pb.environment()["LSTRACE"] = "1"
        return pb.start()
    }

    /** Thrown from the sink to stop the port once enough context after a difference is collected. */
    private class Stop : RuntimeException()

    @Test
    fun portMatchesMasterLive() = compareLive("minisat-master", "minisat_master_trace", csb = false)

    @Test
    fun csbCompatMatchesCsbLive() = compareLive("minisat-full", "minisat_full_trace", csb = true)

    private fun compareLive(refDir: String, binName: String, csb: Boolean) {
        val shadow = MiniSatShadowDriver.locateShadowDir() ?: skip("no ksat-extra/shadow found")
        val bin = File(shadow, "$refDir/build/$binName")
        if (!bin.canExecute())
            skip("reference not built: run `bash ${File(shadow, "$refDir/build_and_trace.sh")} --build-only`")
        val big = System.getProperty("bigtrace")?.lowercase()?.let { it !in setOf("false", "0", "no", "off") } ?: false
        val only = (System.getProperty("liveshadow.only") ?: System.getenv("LIVESHADOW_ONLY"))?.split(',')?.map { it.trim() }?.toSet()

        val full = System.getenv("LIVESHADOW_FULL")?.let { it !in setOf("", "0", "false", "no", "off") } ?: false
        val cases = ArrayList<Pair<File, File?>>()
        for (dir in listOf("cnf", "cnf-full", "cnf-assume")) {
            val cnfs = File(shadow, dir).listFiles { f -> f.name.endsWith(".cnf") }?.sortedBy { it.name }
                ?: fail("$TAG missing ${File(shadow, dir)}")
            for (cnf in cnfs) {
                if (cnf.nameWithoutExtension == "php_10_9" && !big) continue
                if (only != null && cnf.nameWithoutExtension !in only) continue
                val assume = File(cnf.parentFile, cnf.nameWithoutExtension + ".assume").takeIf { it.isFile }
                cases += cnf to assume
            }
        }

        val failures = ArrayList<String>()
        var n = 0
        val errFile = File.createTempFile("minisat-live-shadow", ".err").apply { deleteOnExit() }
        for ((cnf, assume) in cases) for (simp in 0..1) for (opts in OPTION_SETS) {
            if (simp == 0 && opts.any { it.substringBefore('=').removePrefix("--") in SIMP_OPTIONS }) continue
            n++
            val label = "[$refDir ${cnf.name} simp=$simp $opts]"
            val proc = startReference(bin, simp, opts, cnf, assume, errFile)
            val ref = proc.inputStream.bufferedReader()
            fun nextRef(): String? {
                while (true) {
                    val l = ref.readLine() ?: return null
                    if (l.isNotEmpty() && !l.startsWith("s ")) return l
                }
            }
            val ring = ArrayDeque<String>()
            var lineNo = 0
            var diffAt = -1
            var truncated = false
            var upDiff: String? = null
            val ktAfter = ArrayList<String>()
            val sink: (String) -> Unit = sink@{ line ->
                if (truncated) return@sink   // lines from `finally` blocks unwinding after Stop
                if (diffAt >= 0) {
                    ktAfter += line
                    if (ktAfter.size >= CONTEXT) throw Stop()
                    return@sink
                }
                val g = nextRef()
                lineNo++
                if (g != line) { diffAt = lineNo; upDiff = g; ktAfter += line; return@sink }
                ring.addLast(line)
                if (ring.size > CONTEXT) ring.removeFirst()
                if (!full && lineNo >= QUICK_MAX_LINES) { truncated = true; throw Stop() }
            }
            try {
                MiniSatShadowDriver.run(sink, simp, opts, cnf, assume, TAG, csb = csb)
            } catch (_: Stop) {
            } catch (e: Throwable) {
                if (diffAt < 0) { diffAt = lineNo + 1; upDiff = nextRef() }
                ktAfter += "EXCEPTION $e"
                for (f in e.stackTrace.take(8)) ktAfter += "    at $f"
            }
            if (diffAt < 0 && !truncated) {
                val g = nextRef()
                if (g != null) { diffAt = lineNo + 1; upDiff = g; ktAfter += "<end of kotlin trace>" }
            }
            val upAfter = ArrayList<String>()
            if (diffAt >= 0) { upDiff?.let { upAfter += it }; while (upAfter.size < CONTEXT) upAfter += nextRef() ?: break }
            proc.destroy()
            if (!proc.waitFor(60, TimeUnit.SECONDS)) { proc.destroyForcibly(); fail("$TAG reference hung: $label") }
            if (diffAt < 0 && !truncated && proc.exitValue() !in setOf(0, 10, 20))
                fail("$TAG reference failed (${proc.exitValue()}): $label\n${errFile.readText()}")
            if (diffAt >= 0) {
                val ctx = StringBuilder("$label first diff at line $diffAt\n")
                for (l in ring) ctx.append("    = ").append(l).append('\n')
                for (l in upAfter) ctx.append("  up> ").append(l).append('\n')
                if (upAfter.isEmpty()) ctx.append("  up> <end of upstream trace>\n")
                for (l in ktAfter) ctx.append("  kt> ").append(l).append('\n')
                failures += ctx.toString()
            }
        }
        println("$TAG [$refDir] compared $n runs (${if (full) "full" else "quick: first $QUICK_MAX_LINES lines each; LIVESHADOW_FULL=1 for complete traces"}), ${failures.size} failing")
        val report = File(System.getProperty("user.dir"), "build/live-shadow/report-$refDir.txt")
        report.parentFile.mkdirs()
        report.writeText(failures.joinToString("\n"))
        if (failures.isNotEmpty()) fail("$TAG ${failures.size} mismatches:\n" + failures.take(10).joinToString("\n"))
    }

    private companion object {
        const val TAG = "[live-shadow-minisat]"
        const val CONTEXT = 6
        const val QUICK_MAX_LINES = 20_000
        val SIMP_OPTIONS = setOf("asymm", "rcheck", "elim", "grow", "cl-lim", "sub-lim", "simp-gc-frac")
        val OPTION_SETS: List<List<String>> = listOf(
            emptyList(),
            listOf("--rnd-freq=0.1", "--rnd-init=1", "--rnd-seed=12345"),
            listOf("--ccmin-mode=1", "--phase-saving=1", "--luby=0", "--rfirst=7", "--rinc=1.3"),
            listOf("--ccmin-mode=0", "--phase-saving=0", "--gc-frac=0.01", "--min-learnts=5"),
            listOf("--asymm=1", "--rcheck=1", "--grow=2", "--cl-lim=-1", "--sub-lim=3", "--simp-gc-frac=0.01"),
            listOf("--elim=0", "--gc-frac=0.001"),
            listOf("--asymm=1"),
            listOf("--rcheck=1", "--rnd-freq=0.05", "--rnd-seed=7", "--phase-saving=1"),
        )
    }
}
