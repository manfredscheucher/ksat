package org.bytefred.ksat.facade

import org.bytefred.ksat.SatResult
import kotlin.test.Test
import kotlin.test.assertEquals

/**
 * IPASIR incremental contract: a clause added AFTER a solve() must take effect in the next
 * solve() on the SAME instance. This is what enumeration-by-blocking needs.
 *
 * XOR(x1,x2) = (x1 OR x2) AND (-x1 OR -x2) has exactly two models {x1,-x2} and {-x1,x2}.
 * Solve, block the found model (add the OR of its negated literals), solve again — after both
 * models are blocked the instance must be UNSAT. A solver that ignores clauses added after a
 * solve would keep returning the same model (or stay SAT) forever.
 */
class AddClauseAfterSolveTest {

    private val solvers = listOf(Solver.MINISAT, Solver.CADICAL, Solver.KISSAT)

    private val xor = listOf(intArrayOf(1, 2), intArrayOf(-1, -2))

    private fun modelsByBlocking(s: Solver): Int {
        val k = Ksat(s, numVars = 2)
        for (c in xor) k.addClause(c)
        val seen = HashSet<List<Boolean>>()
        var rounds = 0
        while (k.solve() == SatResult.SAT) {
            val model = listOf(k.valueOf(1), k.valueOf(2))
            if (!seen.add(model)) return -1 // repeated model: block was ignored
            k.addClause(IntArray(2) { i -> if (model[i]) -(i + 1) else (i + 1) })
            if (++rounds > 4) break
        }
        return seen.size
    }

    @Test
    fun blockingClauseAddedAfterSolveTakesEffect() {
        for (s in solvers) {
            assertEquals(2, modelsByBlocking(s),
                "solver $s: XOR should yield exactly 2 models then UNSAT (add-after-solve must take effect)")
        }
    }

    // A non-trivial formula where the first SAT leaves a level>1 trail, so a re-solve over a
    // stale high-level trail (the old hack) differs from upstream's root restore. Enumerate all
    // models by blocking and check the count against a fresh-solver reference.
    //   (x1 OR x2 OR x3) AND (-x1 OR -x2) AND (-x2 OR -x3)
    private val tri = listOf(intArrayOf(1, 2, 3), intArrayOf(-1, -2), intArrayOf(-2, -3))

    private fun enumerateCount(s: Solver, nVars: Int, cnf: List<IntArray>): Int {
        val k = Ksat(s, numVars = nVars)
        for (c in cnf) k.addClause(c)
        var n = 0
        while (k.solve() == SatResult.SAT) {
            val model = (1..nVars).map { k.valueOf(it) }
            k.addClause(IntArray(nVars) { i -> if (model[i]) -(i + 1) else (i + 1) })
            if (++n > 64) break
        }
        return n
    }

    @Test
    fun enumeratesNonTrivialFormulaAfterSolve() {
        // reference via MINISAT (add-after-solve known-good) to pin the true model count
        val expected = enumerateCount(Solver.MINISAT, 3, tri)
        for (s in listOf(Solver.CADICAL, Solver.KISSAT)) {
            assertEquals(expected, enumerateCount(s, 3, tri),
                "solver $s: model count on re-solve must match the reference")
        }
    }

    @Test
    fun unitAddedAfterSolveConstrainsNextSolve() {
        // Add a UNIT clause after a SAT, then re-solve: the unit must survive backtrack(0) and
        // force its variable in the next model (the reviewer-flagged add-unit-after-SAT path).
        //   (x1 OR x2) AND (x1 OR x3) is SAT; after solve, force x1=false via the unit (-1):
        //   then x2 and x3 are both forced true.
        for (s in solvers) {
            val k = Ksat(s, numVars = 3)
            k.addClause(intArrayOf(1, 2))
            k.addClause(intArrayOf(1, 3))
            assertEquals(SatResult.SAT, k.solve(), "solver $s: first solve")
            k.addClause(intArrayOf(-1)) // unit: x1 must be false
            assertEquals(SatResult.SAT, k.solve(), "solver $s: still SAT with x1=false")
            assertEquals(false, k.valueOf(1), "solver $s: unit (-1) must force x1=false after re-solve")
            assertEquals(true, k.valueOf(2), "solver $s: (x1 OR x2) with x1=false forces x2")
            assertEquals(true, k.valueOf(3), "solver $s: (x1 OR x3) with x1=false forces x3")
            // and an unsatisfiable unit afterwards makes it UNSAT
            k.addClause(intArrayOf(1)) // now x1 both false and true
            assertEquals(SatResult.UNSAT, k.solve(), "solver $s: contradictory units -> UNSAT")
        }
    }

    @Test
    fun plainResolveWithoutAddingIsStable() {
        // calling solve() twice with NO clause added must give the same verdict + a valid model
        for (s in solvers) {
            val k = Ksat(s, numVars = 3)
            for (c in tri) k.addClause(c)
            val r1 = k.solve()
            assertEquals(SatResult.SAT, r1, "solver $s: first solve")
            val m1 = (1..3).map { k.valueOf(it) }
            val r2 = k.solve()
            assertEquals(SatResult.SAT, r2, "solver $s: second solve (no clause added) must stay SAT")
            val m2 = (1..3).map { k.valueOf(it) }
            // both models must satisfy the CNF (not necessarily identical, but valid)
            for (model in listOf(m1, m2))
                for (c in tri)
                    assertEquals(true, c.any { lit -> model[kotlin.math.abs(lit) - 1] == (lit > 0) },
                        "solver $s: model $model must satisfy clause ${c.toList()}")
        }
    }
}
