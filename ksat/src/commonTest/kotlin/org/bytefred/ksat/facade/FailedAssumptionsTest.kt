package org.bytefred.ksat.facade

import org.bytefred.ksat.SatResult
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * IPASIR failed-assumption core: after UNSAT under assumptions, failed(lit) reports whether a
 * signed DIMACS assumption was part of the core (jointly inconsistent subset). Ported 1:1 from
 * CaDiCaL's failing() (assume.cpp). kissat/minisat/microsat have no upstream failed-core API,
 * so this is CaDiCaL-only here.
 */
class FailedAssumptionsTest {

    private val solver = Solver.CADICAL

    @Test
    fun unitCoreIsJustTheForcedAssumption() {
        // (-1) forces x1=false at the root. Assuming [1, 2]: x1=true clashes with the unit, so
        // UNSAT, and the core is {1} alone — assumption 2 is irrelevant.
        val k = Ksat(solver, numVars = 2)
        k.addClause(intArrayOf(-1))
        assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(1, 2)), "assuming 1 clashes with unit (-1)")
        assertTrue(k.failed(1), "assumption 1 is in the failed core")
        assertFalse(k.failed(2), "assumption 2 is NOT in the core")
    }

    @Test
    fun clashingAssumptionsBothInCore() {
        // No clauses forcing anything; assume [1, -1] directly. The two clash, both are the core.
        val k = Ksat(solver, numVars = 1)
        assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(1, -1)), "assuming 1 and -1 clash")
        assertTrue(k.failed(1), "1 in core")
        assertTrue(k.failed(-1), "-1 in core")
    }

    @Test
    fun multiAssumptionCoreViaImplication() {
        // (-1 OR -2): x1 and x2 cannot both be true. Assuming [1, 2, 3]: UNSAT with core {1, 2};
        // assumption 3 is unrelated.
        val k = Ksat(solver, numVars = 3)
        k.addClause(intArrayOf(-1, -2))
        assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(1, 2, 3)), "1 and 2 jointly falsify (-1 OR -2)")
        assertTrue(k.failed(1), "1 in core")
        assertTrue(k.failed(2), "2 in core")
        assertFalse(k.failed(3), "3 not in core")
    }

    @Test
    fun failedIsFalseAfterSat() {
        // On a SAT solve under assumptions, failed() is meaningless and returns false (IPASIR: 0).
        val k = Ksat(solver, numVars = 2)
        k.addClause(intArrayOf(1, 2))
        assertEquals(SatResult.SAT, k.solve(assumptions = intArrayOf(1)), "assuming 1 is satisfiable")
        assertFalse(k.failed(1), "no core after SAT")
    }

    @Test
    fun coreIsResetBetweenSolves() {
        // A stale core from a previous UNSAT solve must not leak into a later solve.
        val k = Ksat(solver, numVars = 2)
        k.addClause(intArrayOf(-1))
        assertEquals(SatResult.UNSAT, k.solve(assumptions = intArrayOf(1)), "first: 1 clashes")
        assertTrue(k.failed(1), "1 in core after first solve")
        // Now a SAT solve under a different assumption: the old core must be cleared.
        assertEquals(SatResult.SAT, k.solve(assumptions = intArrayOf(-1)), "assuming -1 agrees with the unit")
        assertFalse(k.failed(1), "core cleared on the new solve")
    }
}
