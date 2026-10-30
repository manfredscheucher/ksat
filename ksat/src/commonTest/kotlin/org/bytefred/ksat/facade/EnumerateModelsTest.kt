package org.bytefred.ksat.facade

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

/**
 * Tests the shared [enumerateModels] all-SAT helper (the same one the ksat-extra demo uses).
 * XOR(x1,x2) = (x1 OR x2) AND (NOT x1 OR NOT x2) has exactly two models {x1,-x2} and {-x1,x2}.
 */
class EnumerateModelsTest {

    private val allSolvers = ALL_CONFIGS

    // XOR(x1, x2)
    private val xor = listOf(intArrayOf(1, 2), intArrayOf(-1, -2))
    private val xorModels = setOf(listOf(true, false), listOf(false, true))

    @Test
    fun freshSolverEnumeratesAllSolvers() {
        for (s in allSolvers) {
            // .take(8) is the lazy safety net (Sequence is otherwise unbounded).
            val models = enumerateModels(s.solver, numVars = 2, cnf = xor, options = s.options).take(8).toList()
            assertEquals(2, models.size, "solver $s: XOR should have exactly 2 models")
            assertEquals(xorModels, models.toSet(), "solver $s: wrong model set")
        }
    }

    @Test
    fun incrementalEnumeratesForAddAfterSolveSolvers() {
        for (s in listOf(MINISAT_CORE, CADICAL, KISSAT)) {
            val models = enumerateModels(s.solver, numVars = 2, cnf = xor, incremental = true, options = s.options)
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
    fun incrementalThrowsForMinisatPre() {
        for (pre in listOf(emptyMap(), mapOf("pre" to 1))) {
            assertFailsWith<IllegalArgumentException>("incremental must throw for MINISAT with pre=1 ($pre)") {
                enumerateModels(Solver.MINISAT, numVars = 2, cnf = xor, incremental = true, options = pre)
            }
        }
    }

    @Test
    fun enumeratesUnderAssumptions() {
        // assume x1 = true -> only the {x1, -x2} model remains
        for (s in listOf(MINISAT_CORE, MINISAT_PRE, CADICAL, KISSAT)) {
            for (incremental in listOf(false, true)) {
                if (incremental && s == MINISAT_PRE) continue   // see incrementalThrowsForMinisatPre
                val models = enumerateModels(s.solver, numVars = 2, cnf = xor, assumptions = intArrayOf(1),
                    incremental = incremental, options = s.options)
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

    @Test
    fun optionsAreCheckedEagerly() {
        // the checks run before the sequence is iterated
        assertFailsWith<IllegalArgumentException> { enumerateModels(Solver.CADICAL, 2, xor, options = mapOf("nosuch" to 1)) }
        assertFailsWith<IllegalArgumentException> { enumerateModels(Solver.KISSAT, 2, xor, options = mapOf("pre" to 0)) }
    }
}
