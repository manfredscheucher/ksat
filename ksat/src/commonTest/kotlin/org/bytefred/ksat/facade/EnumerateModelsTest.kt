package org.bytefred.ksat.facade

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

/**
 * Tests the shared [enumerateModels] all-SAT helper (the same one the ksat-extra demo uses).
 * XOR(x1,x2) = (x1 OR x2) AND (NOT x1 OR NOT x2) has exactly two models {x1,-x2} and {-x1,x2}.
 */
class EnumerateModelsTest {

    private val allSolvers = listOf(Solver.MICROSAT, Solver.MINISAT, Solver.MINISAT_SIMP, Solver.CADICAL, Solver.KISSAT)

    // XOR(x1, x2)
    private val xor = listOf(intArrayOf(1, 2), intArrayOf(-1, -2))
    private val xorModels = setOf(listOf(true, false), listOf(false, true))

    @Test
    fun freshSolverEnumeratesAllSolvers() {
        for (s in allSolvers) {
            // .take(8) is the lazy safety net (Sequence is otherwise unbounded).
            val models = enumerateModels(s, numVars = 2, cnf = xor).take(8).toList()
            assertEquals(2, models.size, "solver $s: XOR should have exactly 2 models")
            assertEquals(xorModels, models.toSet(), "solver $s: wrong model set")
        }
    }

    @Test
    fun incrementalEnumeratesForAddAfterSolveSolvers() {
        for (s in listOf(Solver.MINISAT, Solver.CADICAL, Solver.KISSAT)) {
            val models = enumerateModels(s, numVars = 2, cnf = xor, incremental = true)
                .take(8).toList()
            assertEquals(2, models.size, "incremental $s: XOR should have exactly 2 models")
            assertEquals(xorModels, models.toSet(), "incremental $s: wrong model set")
        }
    }

    @Test
    fun incrementalThrowsForMicrosat() {
        assertFailsWith<IllegalArgumentException>("incremental must throw for MICROSAT") {
            // the require() runs eagerly, before the sequence is iterated
            enumerateModels(Solver.MICROSAT, numVars = 2, cnf = xor, incremental = true)
        }
    }

    @Test
    fun incrementalThrowsForMinisatSimp() {
        assertFailsWith<IllegalArgumentException>("incremental must throw for MINISAT_SIMP") {
            enumerateModels(Solver.MINISAT_SIMP, numVars = 2, cnf = xor, incremental = true)
        }
    }

    @Test
    fun enumeratesUnderAssumptions() {
        // assume x1 = true -> only the {x1, -x2} model remains
        for (s in listOf(Solver.MINISAT, Solver.MINISAT_SIMP, Solver.CADICAL, Solver.KISSAT)) {
            for (incremental in listOf(false, true)) {
                if (incremental && s == Solver.MINISAT_SIMP) continue   // see incrementalThrowsForMinisatSimp
                val models = enumerateModels(s, numVars = 2, cnf = xor, assumptions = intArrayOf(1), incremental = incremental)
                    .take(8).toList()
                assertEquals(listOf(listOf(true, false)), models, "$s (incremental=$incremental): assuming x1 leaves exactly one model")
            }
        }
    }

    @Test
    fun microsatRejectsAssumptions() {
        assertFailsWith<IllegalArgumentException>("MICROSAT has no assumptions path") {
            enumerateModels(Solver.MICROSAT, numVars = 2, cnf = xor, assumptions = intArrayOf(1)).toList()
        }
    }
}
