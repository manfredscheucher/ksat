package org.bytefred.ksat.microsat

import org.bytefred.ksat.DimacsCnf
import org.bytefred.ksat.SatResult
import org.junit.AssumptionViolatedException
import java.io.File
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * File-driven shadow test (JVM only, needs filesystem access).
 *
 * For every `shadow/cnf/<name>.cnf` that has a matching golden trace
 * `shadow/golden/<name>.trace`, run the Kotlin [MicroSat] with a trace sink and
 * compare its trace line-for-line against the golden trace produced by the
 * instrumented C reference. Golden traces are regenerated (and the CNFs
 * generated) by `shadow/tools/regen_golden.sh`.
 *
 * This complements the embedded-string [ShadowTraceTest] (which runs on all
 * targets) by covering the bigger, generated instances -- in particular the
 * ones that exercise the RESTART / REDUCE code paths. Those cases are asserted
 * to actually contain RESTART/REDUCE lines so a regression that stops hitting
 * them is caught (see [restartReducePathsAreCovered]).
 */
class ShadowTraceFilesTest {

    /** `ksat-extra/shadow` (an optional submodule), found by walking up from the working dir. */
    private fun locateShadowDir(): File? {
        var dir: File? = File(System.getProperty("user.dir")).absoluteFile
        while (dir != null) {
            val candidate = File(dir, "ksat-extra/shadow")
            if (candidate.isDirectory) return candidate
            dir = dir.parentFile
        }
        return null
    }

    /** The shadow dir, provided ksat-extra is checked out and its golden traces are generated.
     *  Otherwise the test is SKIPPED (a JUnit assumption, reported as skipped), not failed:
     *  ksat-extra is optional and the golden traces are generated artifacts. */
    private fun shadowDir(): File {
        val shadow = locateShadowDir() ?: skip(
            "no ksat-extra/shadow found",
            "`git submodule update --init --checkout ksat-extra`, then `bash $REGEN`",
        )
        val goldDir = File(shadow, GOLDEN)
        if (goldDir.listFiles { f -> f.name.endsWith(".trace") }.isNullOrEmpty()) {
            skip("no golden traces in $goldDir", "`bash $REGEN`")
        }
        return shadow
    }

    /** Every shadow/cnf/<name>.cnf (minus [BENCHMARK_ONLY]) paired with its golden trace.
     *  The golden dir exists and is non-empty here, so a missing CNF dir or a CNF without its
     *  trace is an inconsistent half-generated state and fails the test. */
    private fun cases(shadow: File): List<Pair<File, File>> {
        val cnfDir = File(shadow, "cnf")
        val goldDir = File(shadow, GOLDEN)
        val cnfs = cnfDir.listFiles { f -> f.name.endsWith(".cnf") && f.nameWithoutExtension !in BENCHMARK_ONLY }
            ?.sortedBy { it.name }
            ?: fail("$TAG missing $cnfDir (part of ksat-extra; is the submodule checkout complete?)")
        if (cnfs.isEmpty()) fail("$TAG no .cnf files in $cnfDir")
        val cases = cnfs.map { cnf -> cnf to File(goldDir, cnf.nameWithoutExtension + ".trace") }
        val missing = cases.filter { !it.second.isFile }.map { it.first.name }
        if (missing.isNotEmpty()) fail("$TAG no golden trace in $goldDir for $missing; run `bash $REGEN`")
        return cases
    }

    private fun runOne(cnfFile: File, goldFile: File) {
        val cnf = DimacsCnf.parse(cnfFile.readText())
        val expectedTrace = goldFile.readLines().filter { it.isNotEmpty() }

        val solver = MicroSat(cnf.numVars)
        val trace = ArrayList<String>()
        solver.setTraceSink { trace.add(it) }
        for (clause in cnf.clauses) solver.addClause(clause)
        val result = solver.solve()

        assertEquals(
            expectedTrace, trace,
            "[${cnfFile.name}] Kotlin trace differs from C golden trace",
        )

        // Derive the expected verdict from the golden trace's RESULT line.
        val resultLine = expectedTrace.lastOrNull { it.startsWith("RESULT ") }
            ?: fail("[${cnfFile.name}] golden trace has no RESULT line")
        val expectedResult =
            if (resultLine == "RESULT SAT") SatResult.SAT else SatResult.UNSAT
        assertEquals(expectedResult, result, "[${cnfFile.name}] verdict mismatch")

        if (result == SatResult.SAT) {
            assertTrue(
                cnf.isSatisfiedBy { v -> solver.valueOf(v) },
                "[${cnfFile.name}] returned model does not satisfy the CNF",
            )
        }
    }

    @Test
    fun allGoldenTracesMatch() {
        val shadow = shadowDir()
        val cases = cases(shadow)
        for ((cnf, gold) in cases) runOne(cnf, gold)
    }

    /**
     * Reports whether any *default-threshold* generated instance drives MicroSAT's
     * RESTART / REDUCE paths.
     *
     * With the upstream `maxLemmas=2000` and restart heuristic (`fast > slow/100*125`),
     * no *fast* instance reaches REDUCE — even php_8_7 (13k trace events) triggers
     * neither. Rather than add an impractically large/slow instance, REDUCE is now
     * trace-covered by [lowMaxLemmasForcesReduce] using the `maxLemmasInit`
     * (Kotlin) / `LSMAXLEMMAS` (C) test-only knob, which shadows byte-for-byte at a
     * tiny `maxLemmas`. This test therefore only *reports* the default-threshold
     * coverage (plus whether the low-maxLemmas golden carries REDUCE); it never fails.
     */
    @Test
    fun restartReduceCoverageReport() {
        val shadow = shadowDir()
        val cases = cases(shadow)

        var sawRestart = false
        var sawReduce = false
        for ((_, gold) in cases) {
            val lines = gold.readLines()
            if (lines.contains("RESTART")) sawRestart = true
            if (lines.contains("REDUCE")) sawReduce = true
        }
        // The low-maxLemmas goldens (below) are the ones that actually cover REDUCE.
        val lowLemmasReduce = File(File(shadow, "golden"), "php_5_4_lemmas3.trace")
            .takeIf { it.isFile }?.readLines()?.contains("REDUCE") == true
        println(
            "[microsat coverage] RESTART=${if (sawRestart) "yes" else "no (only via low-maxLemmas goldens)"} " +
                "REDUCE=${if (sawReduce || lowLemmasReduce) "yes (php_5_4_lemmas3 forces reduceDB)" else "no"}",
        )
    }

    /**
     * Trace-covers MicroSAT's REDUCE path (reduceDB), which the default
     * `maxLemmas=2000` never reaches on any fast instance. We drop the initial
     * `maxLemmas` to 3 via [MicroSat]'s `maxLemmasInit` knob and shadow against the
     * C reference re-traced with `LSMAXLEMMAS=3` (golden `php_5_4_lemmas3.trace`,
     * regenerated by shadow/tools/regen_golden.sh). This finally exercises the
     * dual-location watch-pointer compaction in `reduceDB` — the single most
     * error-prone watched-literal translation pattern — byte-for-byte against C.
     *
     * If the Kotlin trace ever diverges from the C golden here, it is exactly the
     * reduceDB port bug the methodology warns about: debug MicroSat.reduceDB.
     */
    /**
     * Trace-covers MicroSAT's REDUCE + RESTART paths. Upstream `maxLemmas=2000` +
     * `restartFactor=125` never reach reduceDB on a fast instance, and REDUCE is gated
     * behind RESTART in `solve()`, so BOTH knobs must be lowered: `maxLemmasInit=3` and
     * `restartFactorInit=20`. The C golden (`php_5_4_reduce.trace`) is generated with the
     * matching `LSMAXLEMMAS=3 LSRESTARTFACTOR=20`. This finally exercises the dual-location
     * watch-pointer compaction in reduceDB — the most error-prone watched-literal pattern —
     * byte-for-byte against C. If it diverges, that IS the reduceDB port bug the methodology
     * warns about.
     */
    @Test
    fun knobsForceReduceAndRestart() {
        val shadow = shadowDir()
        val cnfFile = File(File(shadow, "cnf"), "php_5_4.cnf")
        val goldFile = File(File(shadow, "golden"), "php_5_4_reduce.trace")
        if (!cnfFile.isFile) fail("$TAG missing $cnfFile (part of ksat-extra)")
        if (!goldFile.isFile) fail("$TAG missing $goldFile; run `bash $REGEN`")

        val cnf = DimacsCnf.parse(cnfFile.readText())
        val expectedTrace = goldFile.readLines().filter { it.isNotEmpty() }

        val solver = MicroSat(cnf.numVars, maxLemmasInit = 3, restartFactorInit = 20)
        val trace = ArrayList<String>()
        solver.setTraceSink { trace.add(it) }
        for (clause in cnf.clauses) solver.addClause(clause)
        val result = solver.solve()

        assertEquals(
            expectedTrace, trace,
            "[php_5_4 reduce] Kotlin trace differs from C golden -- likely a reduceDB port bug",
        )
        assertTrue(expectedTrace.contains("REDUCE"), "golden must contain REDUCE")
        assertTrue(expectedTrace.contains("RESTART"), "golden must contain RESTART")
        assertEquals(SatResult.UNSAT, result, "[php_5_4 reduce] verdict mismatch")
    }

    private companion object {
        const val TAG = "[shadow-microsat]"
        const val GOLDEN = "golden"
        const val REGEN = "ksat-extra/shadow/tools/regen_golden.sh"

        /** Skips the running test (JUnit assumption; Gradle reports it as SKIPPED). The reason
         *  goes to stderr too, which the jvmTest task logs, since Gradle doesn't show it. */
        fun skip(reason: String, steps: String): Nothing {
            val msg = "$TAG SKIPPED: $reason. These are optional trace-comparison tests (ksat-extra); " +
                "to run them: $steps."
            System.err.println(msg)
            throw AssumptionViolatedException(msg)
        }

        // -Dbigtrace enables the huge php_10_9 comparison. A bare -Dbigtrace (empty value) is ON;
        // "false"/"0"/"no"/"off" (or absent) leave it off.
        private fun bigtraceEnabled(): Boolean {
            val v = System.getProperty("bigtrace") ?: return false
            return v.lowercase() !in setOf("false", "0", "no", "off")
        }

        // php_10_9 is a large BENCHMARK instance; kept OPT-IN via -Dbigtrace for consistency
        // with the other solvers (microsat's trace is only 4 MB, so it does not need the heap
        // bump, but stays benchmark-only by default). php_9_8 always compares.
        // See doc/benchmarks.typ and doc/repo-split.md.
        val BENCHMARK_ONLY: Set<String> =
            if (bigtraceEnabled()) emptySet() else setOf("php_10_9")
    }
}
