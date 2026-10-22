package org.bytefred.ksat.minisat

import org.bytefred.ksat.DimacsCnf
import org.bytefred.ksat.SatResult
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * Target-independent tests of the upstream-level API of [MiniSat] (core Solver) and [MiniSatSimp]
 * (SimpSolver) that the live shadow test (MiniSatLiveShadowTest, driver flow only) does not reach:
 * released/free variables, user polarity, decision vars, budgets and interrupts, implies,
 * substitute, toDimacs, and the simp adapter's verdict/model on random formulas.
 */
class MiniSatApiTest {

    private fun lit(d: Int): Int = if (d > 0) mkLit(d - 1) else litNeg(mkLit(-d - 1))
    private fun vec(vararg d: Int): IntVec = IntVec().also { v -> d.forEach { v.push(lit(it)) } }

    /** Deterministic pseudo-random 3-CNF (LCG), for verdict/model cross-checks. */
    private fun random3Cnf(seed: Long, vars: Int, clauses: Int): DimacsCnf {
        var x = seed
        fun next(n: Int): Int { x = (x * 6364136223846793005L + 1442695040888963407L); return ((x ushr 33) % n).toInt() }
        val cs = ArrayList<IntArray>()
        repeat(clauses) {
            cs += IntArray(3) { (next(vars) + 1) * (if (next(2) == 0) 1 else -1) }
        }
        return DimacsCnf(vars, cs)
    }

    @Test
    fun simpAndCoreAgreeAndSimpModelsSatisfyTheCnf() {
        var sat = 0
        var unsat = 0
        for (seed in 1L..60L) {
            val cnf = random3Cnf(seed, 30, 128)
            val core = MiniSat(cnf.numVars)
            val simp = MiniSatSimp(cnf.numVars)
            for (c in cnf.clauses) { core.addClause(c); simp.addClause(c) }
            val rc = core.solve()
            val rs = simp.solve()
            assertEquals(rc, rs, "seed $seed: core and simp verdicts differ")
            if (rs == SatResult.SAT) {
                sat++
                assertTrue(cnf.isSatisfiedBy { simp.valueOf(it) }, "seed $seed: simp model (with extendModel) violates the CNF")
                assertTrue(cnf.isSatisfiedBy { core.valueOf(it) }, "seed $seed: core model violates the CNF")
            } else unsat++
        }
        assertTrue(sat > 0 && unsat > 0, "random instances should cover SAT and UNSAT (sat=$sat unsat=$unsat)")
    }

    @Test
    fun simpEliminatesVariablesAndKeepsFrozenOnes() {
        // x1 occurs in two clauses only -> eliminable; freeze it and it must survive.
        val s = MiniSatSimp()
        repeat(4) { s.newVar() }
        s.addClause(vec(1, 2))
        s.addClause(vec(-1, 3))
        s.addClause(vec(2, 3, 4))
        s.setFrozen(0, true)
        assertTrue(s.eliminate(false))
        assertFalse(s.isEliminated(0), "frozen variable was eliminated")
        assertTrue(s.solve(IntVec()))

        val t = MiniSatSimp()
        repeat(4) { t.newVar() }
        t.addClause(vec(1, 2))
        t.addClause(vec(-1, 3))
        t.addClause(vec(2, 3, 4))
        assertTrue(t.eliminate(true))
        assertTrue((0 until 4).any { t.isEliminated(it) }, "nothing was eliminated")
        assertTrue(t.solve(IntVec()))
        val m = { v: Int -> lbEq(t.modelValue(v - 1), L_TRUE) }
        assertTrue(DimacsCnf(4, listOf(intArrayOf(1, 2), intArrayOf(-1, 3), intArrayOf(2, 3, 4))).isSatisfiedBy(m))
    }

    @Test
    fun simpAdapterRejectsEliminatedVariables() {
        val s = MiniSatSimp()
        s.addClause(intArrayOf(1, 2))
        s.addClause(intArrayOf(-1, 3))
        s.addClause(intArrayOf(2, 3, 4))
        assertEquals(SatResult.SAT, s.solve())
        val gone = (1..4).first { s.isEliminated(it - 1) }
        assertFailsWith<IllegalStateException> { s.solve(intArrayOf(gone)) }
        assertFailsWith<IllegalStateException> { s.addClause(intArrayOf(gone, 1)) }
    }

    @Test
    fun simpAdapterKeepsAssumptionVariablesAndReportsCore() {
        val s = MiniSatSimp()
        s.addClause(intArrayOf(-1, 2))
        s.addClause(intArrayOf(-2, 3))
        s.addClause(intArrayOf(4, 5))
        assertEquals(SatResult.UNSAT, s.solve(intArrayOf(1, -3)))
        assertTrue(s.failed(1) && s.failed(-3))
        assertFalse(s.isEliminated(0) || s.isEliminated(2), "assumption variables must be frozen")
        assertEquals(SatResult.SAT, s.solve(intArrayOf(1)))
        assertTrue(s.valueOf(1) && s.valueOf(2) && s.valueOf(3))
    }

    @Test
    fun releasedVariablesAreReusedAfterSimplify() {
        val s = MiniSat()
        repeat(3) { s.newVar() }
        s.releaseVar(lit(3))                       // var 2 made true and released
        assertEquals(3, s.nVars())
        assertTrue(s.simplify())                   // moves it to free_vars
        val v = s.newVar()
        assertEquals(2, v, "released variable must be reused by newVar")
        assertEquals(3, s.nVars())
        assertTrue(lbEq(s.valueVar(v), L_UNDEF))
    }

    @Test
    fun userPolarityDrivesTheModelOfAFreeVariable() {
        for (pol in listOf(L_TRUE, L_FALSE)) {
            val s = MiniSat()
            val v = s.newVar(pol)
            s.newVar()
            s.addClause(vec(1, 2))
            assertTrue(s.solve(IntVec()))
            assertTrue(lbEq(s.modelValue(v), if (pol == L_TRUE) L_FALSE else L_TRUE),
                "user_pol true means sign=true i.e. the negative literal is decided (upstream mkLit(v, user_pol == l_True))")
        }
        val s = MiniSat()
        s.newVar(); s.newVar()
        s.setPolarity(0, L_FALSE)
        s.addClause(vec(1, 2))
        assertTrue(s.solve(IntVec()))
        assertTrue(lbEq(s.modelValue(0), L_TRUE))
    }

    @Test
    fun nonDecisionVariablesStayUnassigned() {
        val s = MiniSat()
        s.newVar(L_UNDEF, true)
        s.newVar(L_UNDEF, false)
        assertEquals(1L, s.decVars)
        assertTrue(s.solve(IntVec()))
        assertTrue(lbEq(s.modelValue(1), L_UNDEF), "a non-decision variable in no clause is never assigned")
        s.setDecisionVar(1, true)
        assertEquals(2L, s.decVars)
    }

    @Test
    fun budgetsAndInterruptGiveUndef() {
        val cnf = random3Cnf(7, 60, 270)
        val s = MiniSat()
        for (c in cnf.clauses) s.addClause(c)
        s.setConfBudget(1)
        assertTrue(lbEq(s.solveLimited(IntVec()), L_UNDEF))
        s.budgetOff()
        s.interrupt()
        assertTrue(lbEq(s.solveLimited(IntVec()), L_UNDEF))
        assertFailsWith<IllegalStateException> { s.solve(IntArray(0)) }
        s.clearInterrupt()
        val r = s.solveLimited(IntVec())
        assertFalse(lbEq(r, L_UNDEF))
        s.setPropBudget(0)
        assertTrue(lbEq(s.solveLimited(IntVec()), L_UNDEF) || !s.okay())
    }

    @Test
    fun impliesReturnsTheConsequences() {
        val s = MiniSat()
        repeat(4) { s.newVar() }
        s.addClause(vec(-1, 2))
        s.addClause(vec(-2, 3))
        s.addClause(vec(-3, -4))
        val out = IntVec()
        assertTrue(s.implies(vec(1), out))
        assertEquals(listOf(lit(2), lit(3), lit(-4)), out.toIntArray().toList())
        assertFalse(s.implies(vec(1, 4), IntVec()))
        assertEquals(0, s.nAssigns(), "implies must backtrack to level 0")
    }

    @Test
    fun substituteReplacesAVariable() {
        val s = MiniSatSimp()
        repeat(3) { s.newVar() }
        s.addClause(vec(1, 2))
        s.addClause(vec(-1, 3))
        assertTrue(s.substitute(0, lit(-2)))      // x1 := -x2
        assertTrue(s.isEliminated(0))
        assertTrue(s.solve(IntVec(), false, false))
    }

    @Test
    fun toDimacsWritesTheReducedFormula() {
        val s = MiniSat()
        repeat(4) { s.newVar() }
        s.addClause(vec(1))
        s.addClause(vec(1, 2))        // satisfied at level 0: skipped
        s.addClause(vec(-1, 3, 4))    // -1 false: dropped from the clause
        val sb = StringBuilder()
        s.toDimacs(sb, vec(-4))
        assertEquals("p cnf 2 2\n-2 0\n1 2 0\n", sb.toString())
        val bad = MiniSat()
        bad.addEmptyClause()
        val sb2 = StringBuilder()
        bad.toDimacs(sb2)
        assertEquals("p cnf 1 2\n1 0\n-1 0\n", sb2.toString())
    }

    @Test
    fun simpReleaseVarFollowsBothUpstreamBranches() {
        // use_simplification still on: releaseVar only adds the unit (variable never reused).
        val s = MiniSatSimp()
        repeat(3) { s.newVar() }
        s.releaseVar(lit(3))
        assertTrue(s.simplify())
        assertEquals(3, s.newVar(), "with simplification on, a released variable is not reused")
        // after eliminate(true): a variable created later (>= max_simp_var) is really released.
        // (No clauses, so simpDB_props = 0 and simplify() does not skip its pass.)
        val t = MiniSatSimp()
        repeat(2) { t.newVar() }
        assertTrue(t.eliminate(true))
        val v = t.newVar()
        t.releaseVar(lit(v + 1))
        assertTrue(t.simplify())
        assertEquals(v, t.newVar(), "a variable created after simplification was turned off is reused")
    }

    @Test
    fun freezeVarAndThaw() {
        val s = MiniSatSimp()
        repeat(3) { s.newVar() }
        s.addClause(vec(1, 2))
        s.addClause(vec(-1, 3))
        s.freezeVar(0)
        assertTrue(s.eliminate(false))
        assertFalse(s.isEliminated(0), "frozen by freezeVar")
        s.thaw()
        assertTrue(s.eliminate(false))
        assertTrue(s.isEliminated(0), "eliminable again after thaw")
        assertTrue(s.solve(IntVec(), false, false))
    }

    @Test
    fun repeatedSimpSolveKeepsAssumptionVariables() {
        // upstream default solve(assumps, do_simp = true, turn_off_simp = false): every solve
        // freezes its assumptions temporarily and may eliminate more.
        val s = MiniSatSimp()
        repeat(4) { s.newVar() }
        s.addClause(vec(-1, 2))
        s.addClause(vec(-2, 3))
        s.addClause(vec(3, 4))
        assertTrue(s.solve(vec(1)))
        assertFalse(s.isEliminated(0))
        assertTrue(lbEq(s.modelValueLit(lit(3)), L_TRUE))
        assertTrue(s.solve(vec(1), true, false))
        // x3 was not frozen in the first solve and got eliminated: assuming it is upstream's
        // assert(!isEliminated(v)) in solve_ (kept as a check).
        assertTrue(s.isEliminated(2))
        assertFailsWith<IllegalStateException> { s.solve(vec(1, -3)) }
    }
}
