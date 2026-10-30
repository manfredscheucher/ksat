package org.bytefred.ksat.facade

/** A [Solver] with the options a test runs it with (MiniSat runs both with and without `pre`). */
data class SolverConfig(val solver: Solver, val options: Map<String, Number> = emptyMap()) {
    fun ksat(numVars: Int): Ksat = Ksat(solver, numVars, options)
    override fun toString(): String = if (options.isEmpty()) solver.name else "${solver.name} $options"
}

val MICROSAT = SolverConfig(Solver.MICROSAT)
/** MiniSat's core `Solver` (`pre` = 0): no preprocessing, fully incremental. */
val MINISAT_CORE = SolverConfig(Solver.MINISAT, mapOf("pre" to 0))
/** MiniSat's `SimpSolver`, the default (`pre` = 1). */
val MINISAT_PRE = SolverConfig(Solver.MINISAT)
val CADICAL = SolverConfig(Solver.CADICAL)
val KISSAT = SolverConfig(Solver.KISSAT)

val ALL_CONFIGS = listOf(MICROSAT, MINISAT_CORE, MINISAT_PRE, CADICAL, KISSAT)
