package org.bytefred.ksat.facade

import org.bytefred.ksat.Copying
import org.bytefred.ksat.ExternalPropagation
import org.bytefred.ksat.ExternalPropagator
import org.bytefred.ksat.FixedAssignmentListener
import org.bytefred.ksat.FixedListening
import org.bytefred.ksat.ForcedPhases
import org.bytefred.ksat.SatResult
import org.bytefred.ksat.SatSolver

/**
 * The ported solvers you can pick between. Their upstream options are passed to [Ksat] (see
 * [solverOptions]).
 *
 * [MINISAT] is MiniSat's `SimpSolver` by default (option `pre` = 1, as the upstream binary:
 * subsumption, bounded variable elimination, model reconstruction), used as upstream
 * `SimpSolver::solve(assumps, do_simp = true, turn_off_simp = true)`: the first solve eliminates
 * variables (its assumption variables are frozen), later solves run the plain search. A variable
 * eliminated by the first solve must not appear in a later clause or assumption (that fails
 * loudly), so incremental use (adding clauses after a solve, or assumptions on other variables)
 * needs `pre` = 0: MiniSat's core `Solver` (no preprocessing, fully incremental, like the IPASIR
 * wrappers of MiniSat).
 */
enum class Solver { MICROSAT, MINISAT, CADICAL, KISSAT }

/**
 * One uniform entry point over the ported SAT solvers, in the spirit of PySAT: the
 * CNF you feed in and the SAT/UNSAT + model you get back are the same regardless of
 * which [Solver] runs underneath, so switching solver is a one-word change.
 *
 * ```
 * val s = Ksat(Solver.CADICAL, numVars = n)
 * for (c in clauses) s.addClause(c)
 * if (s.solve(assumptions = intArrayOf(-mine)) == SatResult.SAT) {
 *     val isMine = s.valueOf(v)   // model of that solve
 * }
 * ```
 *
 * [Ksat] is itself a [SatSolver], so game/library code can hold the interface type
 * and stay solver-agnostic; the concrete choice is made once at construction.
 *
 * `numVars` is a capacity hint (as in the underlying ports): variables are created
 * lazily as clauses reference them.
 *
 * [options]: upstream option name -> value (see [solverOptions]), applied before any clause is
 * added; an option not passed keeps the upstream default. An unknown name, a value the option does
 * not take, and any option for [Solver.MICROSAT] / [Solver.KISSAT] throw [IllegalArgumentException].
 */
class Ksat private constructor(
    val solver: Solver,
    internal val delegate: SatSolver,
) : SatSolver, ExternalPropagation, FixedListening, ForcedPhases, Copying {

    constructor(solver: Solver, numVars: Int, options: Map<String, Number> = emptyMap()) :
        this(solver, newSolver(solver, numVars, options))

    override val numVars: Int get() = delegate.numVars

    override fun addClause(literals: IntArray) = delegate.addClause(literals)

    override fun solve(): SatResult = delegate.solve()

    /** Solve under [assumptions]; see [SatSolver.solve]. Delegated to the chosen port. */
    override fun solve(assumptions: IntArray): SatResult = delegate.solve(assumptions)

    override fun valueOf(v: Int): Boolean = delegate.valueOf(v)

    /** Failed-assumption core after UNSAT under assumptions; see [SatSolver.failed]. */
    override fun failed(lit: Int): Boolean = delegate.failed(lit)

    // ---- IPASIR-UP (only for ports that host an external propagator, i.e. CaDiCaL) ----

    private fun host(): ExternalPropagation =
        delegate as? ExternalPropagation
            ?: throw UnsupportedOperationException("solver $solver does not support IPASIR-UP external propagators")

    override fun connectExternalPropagator(propagator: ExternalPropagator) = host().connectExternalPropagator(propagator)
    override fun disconnectExternalPropagator() = host().disconnectExternalPropagator()
    override fun addObservedVar(v: Int) = host().addObservedVar(v)
    override fun removeObservedVar(v: Int) = host().removeObservedVar(v)
    override fun resetObservedVars() = host().resetObservedVars()
    override fun isDecision(lit: Int): Boolean = host().isDecision(lit)
    override fun forceBacktrack(newLevel: Int) = host().forceBacktrack(newLevel)

    // ---- fixed-assignment listener (only CaDiCaL) ----

    private fun fixedHost(): FixedListening =
        delegate as? FixedListening
            ?: throw UnsupportedOperationException("solver $solver does not support fixed-assignment listeners")

    override fun connectFixedListener(listener: FixedAssignmentListener) = fixedHost().connectFixedListener(listener)
    override fun disconnectFixedListener() = fixedHost().disconnectFixedListener()

    // ---- forced decision phases (only CaDiCaL) ----

    private fun phaseHost(): ForcedPhases =
        delegate as? ForcedPhases
            ?: throw UnsupportedOperationException("solver $solver does not support forced phases")

    override fun phase(lit: Int) = phaseHost().phase(lit)
    override fun unphase(lit: Int) = phaseHost().unphase(lit)

    // ---- copy (only CaDiCaL: upstream Solver::copy, no learned clauses) ----

    /**
     * A fresh, independent [Ksat] over the same formula on the same [solver]; see [Copying].
     * Upstream `Solver::copy` also copies the options, so the copy runs with the same options.
     */
    override fun copy(): Ksat {
        val host = delegate as? Copying
            ?: throw UnsupportedOperationException("solver $solver does not support copy")
        return Ksat(solver, host.copy())
    }
}
