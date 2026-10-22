package org.bytefred.ksat.facade

import org.bytefred.ksat.SatResult
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * IPASIR failed-assumption core: after UNSAT under assumptions, failed(lit) reports whether a
 * signed DIMACS assumption was part of the core (jointly inconsistent subset). Ported 1:1 from
 * CaDiCaL's failing() (assume.cpp) and MiniSat's analyzeFinal (Solver.cc; also through MINISAT_SIMP,
 * whose re-solves here only assume variables its first solve froze during elimination). kissat has no upstream
 * failed-core API and microsat no assumptions, so they are not covered here.
 *
 * The assertTrue checks are what every valid core must contain. The assertFalse checks are not
 * guaranteed by the IPASIR docs (cores need not be minimal); they hold for both ported algorithms
 * because failing()/analyzeFinal only collect assumptions that are assigned and take part in the
 * conflict. [assertCoreRefutes] adds the doc-level property: the core alone is still UNSAT
 * (upstream checks this in debug builds, solver.cpp).
 */
class FailedAssumptionsTest {

    private val solvers = listOf(Solver.CADICAL, Solver.MINISAT, Solver.MINISAT_SIMP)

    /** Re-solve under only the assumptions reported as failed: must still be UNSAT. */
    private fun assertCoreRefutes(k: Ksat, solver: Solver, assumptions: IntArray) {
        val core = assumptions.filter { k.failed(it) }.toIntArray()
        assertEquals(SatResult.UNSAT, k.solve(assumptions = core), "$solver: core ${core.toList()} alone must be UNSAT")
    }

    @Test
    fun unitCoreIsJustTheForcedAssumption() {
        for (solver in solvers) {
            // (-1) forces x1=false at the root. Assuming [1, 2]: x1=true clashes with the unit, so
            // UNSAT, and the core is {1} alone — assumption 2 is irrelevant.
            val k = Ksat(solver, numVars = 2)
            k.addClause(intArrayOf(-1))
            assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(1, 2)), "$solver: assuming 1 clashes with unit (-1)")
            assertTrue(k.failed(1), "$solver: assumption 1 is in the failed core")
            assertFalse(k.failed(2), "$solver: assumption 2 is NOT in the core")
            assertCoreRefutes(k, solver, intArrayOf(1, 2))
        }
    }

    @Test
    fun clashingAssumptionsBothInCore() {
        for (solver in solvers) {
            // No clauses forcing anything; assume [1, -1] directly. The two clash, both are the core.
            val k = Ksat(solver, numVars = 1)
            assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(1, -1)), "$solver: assuming 1 and -1 clash")
            assertTrue(k.failed(1), "$solver: 1 in core")
            assertTrue(k.failed(-1), "$solver: -1 in core")
            assertCoreRefutes(k, solver, intArrayOf(1, -1))
        }
    }

    @Test
    fun multiAssumptionCoreViaImplication() {
        for (solver in solvers) {
            // (-1 OR -2): x1 and x2 cannot both be true. Assuming [1, 2, 3]: UNSAT with core {1, 2};
            // assumption 3 is unrelated.
            val k = Ksat(solver, numVars = 3)
            k.addClause(intArrayOf(-1, -2))
            assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(1, 2, 3)), "$solver: 1 and 2 jointly falsify (-1 OR -2)")
            assertTrue(k.failed(1), "$solver: 1 in core")
            assertTrue(k.failed(2), "$solver: 2 in core")
            assertFalse(k.failed(3), "$solver: 3 not in core")
            assertCoreRefutes(k, solver, intArrayOf(1, 2, 3))
        }
    }

    @Test
    fun failedAfterSatFollowsUpstream() {
        // CaDiCaL: solver.cpp REQUIREs the unsatisfied state, so failed() after SAT is an error.
        // MiniSat has no guard; conflict is cleared at solve start, so it reports false.
        for (solver in solvers) {
            val k = Ksat(solver, numVars = 2)
            k.addClause(intArrayOf(1, 2))
            assertEquals(SatResult.SAT, k.solve(assumptions = intArrayOf(1)), "$solver: assuming 1 is satisfiable")
            when (solver) {
                Solver.CADICAL -> assertFailsWith<IllegalStateException>("$solver: failed() after SAT must fail") { k.failed(1) }
                else -> assertFalse(k.failed(1), "$solver: no core after SAT")
            }
        }
    }

    @Test
    fun coreIsResetBetweenSolves() {
        // Two UNSAT solves on one instance: a stale bit from the first core must not leak into
        // the second. Both algorithms stop at the first root-falsified assumption in order.
        for (solver in solvers) {
            val k = Ksat(solver, numVars = 2)
            k.addClause(intArrayOf(-1))
            k.addClause(intArrayOf(-2))
            assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(1, 2)), "$solver: first solve UNSAT")
            assertTrue(k.failed(1), "$solver: 1 in first core")
            assertFalse(k.failed(2), "$solver: 2 not in first core")
            assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(2, 1)), "$solver: second solve UNSAT")
            assertTrue(k.failed(2), "$solver: 2 in second core")
            assertFalse(k.failed(1), "$solver: stale bit for 1 must be gone")
        }
    }

    @Test
    fun rootUnsatFoundDuringSearchGivesEmptyCore() {
        // PHP(3,2) is UNSAT on its own and the assumption (var 7) occurs in no clause, so no
        // assumption takes part in the refutation. The core is empty
        // (upstream: learn_empty_clause marks the core as computed, failing() never runs).
        val php32 = listOf(
            intArrayOf(1, 2), intArrayOf(3, 4), intArrayOf(5, 6),
            intArrayOf(-1, -3), intArrayOf(-1, -5), intArrayOf(-3, -5),
            intArrayOf(-2, -4), intArrayOf(-2, -6), intArrayOf(-4, -6),
        )
        for (solver in solvers) {
            val k = Ksat(solver, numVars = 7)
            for (c in php32) k.addClause(c)
            assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(7)), "$solver: PHP(3,2) is UNSAT")
            assertFalse(k.failed(7), "$solver: unrelated assumption 7 is not in the core")
            assertCoreRefutes(k, solver, intArrayOf(7))
        }
    }
}
