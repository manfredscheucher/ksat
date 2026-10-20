package org.bytefred.ksat.kissat

import org.bytefred.ksat.DimacsCnf
import org.bytefred.ksat.SatResult
import org.junit.AssumptionViolatedException
import java.io.File
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * Assumption shadow test (JVM only) for the Kotlin [Kissat] port: the byte-for-byte
 * guarantee extended to solve-under-assumptions.
 *
 * For every `shadow/cnf-assume/<name>.cnf` with a matching `<name>.assume` and a golden
 * trace at `shadow/golden-kissat-assume/<name>.trace` (produced by the instrumented C
 * kissat run as `kissat_trace <cnf> <assume>`), run the Kotlin Kissat under the same
 * assumptions via [Kissat.solve] and compare byte-for-byte (L1), else event sequence (L2),
 * always the verdict + model respecting the assumptions (L3).
 *
 * This is the strong check for the assumption path that the earlier failed-literal bug
 * (a conflict among assumptions wrongly learned as a unit) slipped past a purely
 * functional test. Golden traces: shadow/tools/regen_golden_kissat_assume.sh.
 */
class ShadowAssumeTraceFilesTest {

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

    private data class Case(val cnf: File, val assume: File, val gold: File)

    /** Every shadow/cnf-assume/<name>.cnf with its <name>.assume and golden trace. The golden dir
     *  exists and is non-empty here, so a missing case dir, or a CNF without its .assume or
     *  trace, is an inconsistent half-generated state and fails the test. */
    private fun cases(shadow: File): List<Case> {
        val caseDir = File(shadow, "cnf-assume")
        val goldDir = File(shadow, GOLDEN)
        val cnfs = caseDir.listFiles { f -> f.name.endsWith(".cnf") }?.sortedBy { it.name }
            ?: fail("$TAG missing $caseDir (part of ksat-extra; is the submodule checkout complete?)")
        if (cnfs.isEmpty()) fail("$TAG no .cnf files in $caseDir")
        val cases = cnfs.map { cnf ->
            val name = cnf.nameWithoutExtension
            Case(cnf, File(caseDir, "$name.assume"), File(goldDir, "$name.trace"))
        }
        val noAssume = cases.filter { !it.assume.isFile }.map { it.cnf.name }
        if (noAssume.isNotEmpty()) fail("$TAG no .assume file in $caseDir for $noAssume")
        val missing = cases.filter { !it.gold.isFile }.map { it.cnf.name }
        if (missing.isNotEmpty()) fail("$TAG no golden trace in $goldDir for $missing; run `bash $REGEN`")
        return cases
    }

    private fun readAssumptions(f: File): IntArray =
        f.readText().split(Regex("\\s+")).filter { it.isNotBlank() }.map { it.toInt() }.toIntArray()

    private fun l2(trace: List<String>): List<String> = trace.filter { !it.startsWith("ASSIGN ") }

    private fun runOne(c: Case): String {
        val cnf = DimacsCnf.parse(c.cnf.readText())
        val assumptions = readAssumptions(c.assume)
        val expected = c.gold.readLines().filter { it.isNotEmpty() }

        val solver = Kissat(cnf.numVars)
        val trace = ArrayList<String>()
        solver.setTraceSink { trace.add(it) }
        for (clause in cnf.clauses) solver.addClause(clause)
        val result = solver.solve(assumptions)

        val resultLine = expected.lastOrNull { it.startsWith("RESULT ") }
            ?: fail("[${c.cnf.name}] golden trace has no RESULT line")
        val expectedResult = if (resultLine == "RESULT SAT") SatResult.SAT else SatResult.UNSAT
        assertEquals(expectedResult, result, "[${c.cnf.name}] verdict mismatch (L3)")
        if (result == SatResult.SAT) {
            assertTrue(
                cnf.isSatisfiedBy { v -> solver.valueOf(v) },
                "[${c.cnf.name}] returned model does not satisfy the CNF (L3)",
            )
            for (lit in assumptions) {
                val v = kotlin.math.abs(lit)
                assertEquals(lit > 0, solver.valueOf(v), "[${c.cnf.name}] model violates assumption $lit (L3)")
            }
        }

        return when {
            trace == expected -> "L1"
            l2(trace) == l2(expected) -> "L2"
            else -> {
                val a = l2(expected); val b = l2(trace)
                val firstDiff = (0 until minOf(a.size, b.size)).firstOrNull { a[it] != b[it] } ?: minOf(a.size, b.size)
                fail(
                    "[${c.cnf.name}] assumption trace diverges even at L2.\n" +
                        "  expected[$firstDiff]=${a.getOrNull(firstDiff)}\n" +
                        "  actual  [$firstDiff]=${b.getOrNull(firstDiff)}\n" +
                        "  expected events=${a.size} actual events=${b.size}",
                )
            }
        }
    }

    @Test
    fun allAssumptionGoldenTracesMatch() {
        val shadow = shadowDir()
        val cases = cases(shadow)
        val levels = LinkedHashMap<String, String>()
        for (c in cases) levels[c.cnf.name] = runOne(c)
        println("[shadow-kissat-assume] per-instance level:")
        for ((name, lvl) in levels) println("  %-24s %s".format(name, lvl))

        val degraded = levels.filterValues { it != "L1" }.keys
        assertTrue(
            degraded.isEmpty(),
            "L1 regression on the kissat assumption path: $degraded dropped below byte-for-byte L1.",
        )
    }

    private companion object {
        const val TAG = "[shadow-kissat-assume]"
        const val GOLDEN = "golden-kissat-assume"
        const val REGEN = "ksat-extra/shadow/tools/regen_golden_kissat_assume.sh"

        /** Skips the running test (JUnit assumption; Gradle reports it as SKIPPED). The reason
         *  goes to stderr too, which the jvmTest task logs, since Gradle doesn't show it. */
        fun skip(reason: String, steps: String): Nothing {
            val msg = "$TAG SKIPPED: $reason. These are optional trace-comparison tests (ksat-extra); " +
                "to run them: $steps."
            System.err.println(msg)
            throw AssumptionViolatedException(msg)
        }
    }
}
