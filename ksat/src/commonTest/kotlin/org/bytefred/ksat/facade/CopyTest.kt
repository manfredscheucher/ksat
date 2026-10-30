package org.bytefred.ksat.facade

import org.bytefred.ksat.SatResult
import kotlin.math.abs
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

/**
 * CaDiCaL 2.1.3 `Solver::copy` through the facade (cadical.hpp: "Copy 'this' into a fresh 'other'.
 * The copy procedure is not a deep clone, but only copies irredundant clauses and units ... such that
 * both solvers have the same models. Assumptions are not copied."). Checked against brute-force model
 * sets of small random 3-CNFs. Only CaDiCaL has copy; the other ports must throw.
 */
class CopyTest {

    private fun satisfies(clauses: List<IntArray>, assignment: Int): Boolean =
        clauses.all { c -> c.any { l -> ((assignment shr (abs(l) - 1)) and 1 == 1) == (l > 0) } }

    private fun models(clauses: List<IntArray>, n: Int): List<Int> =
        (0 until (1 shl n)).filter { satisfies(clauses, it) }

    private fun holds(model: Int, lit: Int): Boolean = ((model shr (abs(lit) - 1)) and 1 == 1) == (lit > 0)

    private fun random3Cnf(seed: Int, n: Int, m: Int): List<IntArray> {
        val rnd = Random(seed)
        return List(m) { IntArray(3) { (rnd.nextInt(n) + 1) * if (rnd.nextBoolean()) 1 else -1 } }
    }

    private fun loaded(clauses: List<IntArray>, n: Int): Ksat =
        Ksat(Solver.CADICAL, n).also { k -> for (c in clauses) k.addClause(c) }

    /** Under every single-literal assumption [k] answers like brute force, with a valid model. */
    private fun assertSameModels(k: Ksat, clauses: List<IntArray>, n: Int, label: String) {
        val all = models(clauses, n)
        for (v in 1..n) for (lit in intArrayOf(v, -v)) {
            val want = all.any { holds(it, lit) }
            val got = k.solve(intArrayOf(lit))
            assertEquals(if (want) SatResult.SAT else SatResult.UNSAT, got, "$label: assumption $lit")
            if (got == SatResult.SAT) {
                val model = (1..n).fold(0) { acc, x -> if (k.valueOf(x)) acc or (1 shl (x - 1)) else acc }
                assertTrue(satisfies(clauses, model) && holds(model, lit), "$label: model under $lit is not a model")
            }
        }
    }

    @Test
    fun copyHasTheSameModelsAsTheOriginal() {
        val n = 8
        for (seed in 0 until 30) {
            val cnf = random3Cnf(seed, n, 30)
            val original = loaded(cnf, n)
            original.solve() // learn something first: the copy must still have the same models
            val copy = original.copy()
            assertSameModels(copy, cnf, n, "seed $seed copy")
            assertSameModels(original, cnf, n, "seed $seed original after copy")
        }
    }

    @Test
    fun copyIsIndependentInBothDirections() {
        val n = 8
        for (seed in 0 until 30) {
            val cnf = random3Cnf(seed, n, 25)
            if (models(cnf, n).isEmpty()) continue
            val original = loaded(cnf, n)
            val copy = original.copy()
            copy.addClause(intArrayOf(1))
            assertSameModels(copy, cnf + listOf(intArrayOf(1)), n, "seed $seed copy + unit 1")
            assertSameModels(original, cnf, n, "seed $seed original untouched by the copy's unit")
            original.addClause(intArrayOf(-2))
            assertSameModels(original, cnf + listOf(intArrayOf(-2)), n, "seed $seed original + unit -2")
            assertSameModels(copy, cnf + listOf(intArrayOf(1)), n, "seed $seed copy untouched by the original's unit")
        }
    }

    @Test
    fun copyKeepsUnitsAndUnsat() {
        val units = listOf(intArrayOf(1, 2), intArrayOf(-1), intArrayOf(-2, 3))
        val copy = loaded(units, 3).copy()
        assertEquals(SatResult.SAT, copy.solve())
        assertTrue(!copy.valueOf(1) && copy.valueOf(2) && copy.valueOf(3), "units / implied literals lost in the copy")

        val unsat = loaded(listOf(intArrayOf(1), intArrayOf(-1)), 1)
        assertEquals(SatResult.UNSAT, unsat.solve())
        assertEquals(SatResult.UNSAT, unsat.copy().solve(), "copy of an UNSAT formula must stay UNSAT")
    }

    @Test
    fun onlyCadicalSupportsCopy() {
        for (s in listOf(MICROSAT, MINISAT_CORE, MINISAT_PRE, KISSAT)) {
            val k = s.ksat(2).also { it.addClause(intArrayOf(1, 2)) }
            assertFailsWith<UnsupportedOperationException>("solver $s") { k.copy() }
        }
    }
}
