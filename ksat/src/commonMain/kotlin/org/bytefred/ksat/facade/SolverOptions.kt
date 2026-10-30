package org.bytefred.ksat.facade

import org.bytefred.ksat.SatSolver
import org.bytefred.ksat.cadical.CaDiCaL
import org.bytefred.ksat.kissat.Kissat
import org.bytefred.ksat.microsat.MicroSat
import org.bytefred.ksat.minisat.MiniSat
import org.bytefred.ksat.minisat.MiniSatSimp
import kotlin.math.floor

/** Value type of a [SolverOption]. BOOL options take 0 / 1, INT options an integral value. */
enum class OptionType { BOOL, INT, DOUBLE }

/**
 * One upstream option of a [Solver] (see [solverOptions]): its upstream [name], [type], upstream
 * [default] and range [min]..[max] (Int for BOOL / INT, Double for DOUBLE; [minInclusive] /
 * [maxInclusive] are false only for the open ends of MiniSat's `DoubleRange`s), and the upstream
 * [help] text.
 */
data class SolverOption(
    val name: String,
    val type: OptionType,
    val default: Number,
    val min: Number,
    val max: Number,
    val minInclusive: Boolean,
    val maxInclusive: Boolean,
    val help: String,
)

/**
 * The options [solver] accepts in [Ksat] / [enumerateModels], with the upstream names, defaults,
 * ranges and help texts. Nothing is set unless the caller passes it; an option not passed keeps
 * the upstream default.
 *
 *  - [Solver.MINISAT]: every `Option` of core/Solver.cc and simp/SimpSolver.cc (meelgroup/minisat
 *    master 664490d, the port's target) plus `pre` of simp/Main.cc (default 1: the solver is
 *    MiniSat's `SimpSolver`; `pre` = 0 gives the core `Solver`, which takes no SimpSolver option).
 *  - [Solver.CADICAL]: every option of upstream's options.hpp (CaDiCaL 2.1.3), set through upstream
 *    `Solver::set`. All are integers; a range of 0..1 is BOOL, as upstream's usage text shows it.
 *  - [Solver.MICROSAT], [Solver.KISSAT]: none.
 */
fun solverOptions(solver: Solver): List<SolverOption> = when (solver) {
    Solver.MINISAT -> MINISAT_OPTIONS.map { it.option }
    Solver.CADICAL -> CaDiCaL.optionTable.map {
        val type = if (it.min == 0 && it.max == 1) OptionType.BOOL else OptionType.INT
        SolverOption(it.name, type, it.default, it.min, it.max, true, true, it.description)
    }
    Solver.MICROSAT, Solver.KISSAT -> emptyList()
}

/**
 * Checks [options] against [solverOptions] and returns them with Int values for BOOL / INT and
 * Double values for DOUBLE options. Throws [IllegalArgumentException] for an unknown name, a
 * non-integral value of a BOOL / INT option and a value outside the option's range.
 */
internal fun checkedOptions(solver: Solver, options: Map<String, Number>): Map<String, Number> {
    if (options.isEmpty()) return options
    require(solver != Solver.MICROSAT && solver != Solver.KISSAT) { "solver $solver has no options, got ${options.keys}" }
    val byName = solverOptions(solver).associateBy { it.name }
    return options.mapValues { (name, value) ->
        val o = byName[name] ?: throw IllegalArgumentException("unknown $solver option '$name'")
        o.checked(solver, value)
    }
}

private fun SolverOption.checked(solver: Solver, value: Number): Number {
    val d = value.toDouble()
    if (type == OptionType.DOUBLE) {
        val lo = min.toDouble()
        val hi = max.toDouble()
        require((if (minInclusive) d >= lo else d > lo) && (if (maxInclusive) d <= hi else d < hi)) {
            "$solver option '$name': value $value outside ${if (minInclusive) "[" else "("}$lo, $hi${if (maxInclusive) "]" else ")"}"
        }
        return d
    }
    require(d == floor(d) && d >= Int.MIN_VALUE && d <= Int.MAX_VALUE) { "$solver option '$name' takes an integral value, got $value" }
    val i = d.toInt()
    require(i >= min.toInt() && i <= max.toInt()) { "$solver option '$name': value $value outside $min..$max" }
    return i
}

/** The port behind [solver], with [options] (checked) applied before any clause is added. */
internal fun newSolver(solver: Solver, numVars: Int, options: Map<String, Number>): SatSolver {
    val opts = checkedOptions(solver, options)
    return when (solver) {
        Solver.MICROSAT -> MicroSat(numVars)
        Solver.MINISAT -> newMiniSat(numVars, opts)
        Solver.CADICAL -> CaDiCaL(numVars).also { s -> for ((name, value) in opts) s.setOption(name, value.toInt()) }
        Solver.KISSAT -> Kissat(numVars)
    }
}

/** Whether MiniSat runs with `pre` = 1 (its `SimpSolver`, the upstream default) under [options]. */
internal fun miniSatPre(options: Map<String, Number>): Boolean = (options["pre"]?.toInt() ?: 1) == 1

private fun newMiniSat(numVars: Int, opts: Map<String, Number>): MiniSat {
    val pre = miniSatPre(opts)
    val s = if (pre) MiniSatSimp(numVars) else MiniSat(numVars)
    for ((name, value) in opts) {
        if (name == "pre") continue
        val o = MINISAT_OPTIONS.first { it.option.name == name }
        require(o.simp == null || s is MiniSatSimp) { "MINISAT option '$name' is a SimpSolver option and needs pre=1" }
        o.core?.invoke(s, value)
        if (s is MiniSatSimp) o.simp?.invoke(s, value)
    }
    return s
}

/** A MiniSat option and the port var it sets ([core] on `Solver`, [simp] on `SimpSolver`). */
private class MiniSatOption(
    val option: SolverOption,
    val core: ((MiniSat, Number) -> Unit)? = null,
    val simp: ((MiniSatSimp, Number) -> Unit)? = null,
)

private const val MAX = Int.MAX_VALUE
private const val INF = Double.POSITIVE_INFINITY

private fun bool(name: String, def: Boolean, help: String) =
    SolverOption(name, OptionType.BOOL, if (def) 1 else 0, 0, 1, true, true, help)

private fun int(name: String, def: Int, lo: Int, hi: Int, help: String) =
    SolverOption(name, OptionType.INT, def, lo, hi, true, true, help)

private fun double(name: String, def: Double, lo: Double, loIncl: Boolean, hi: Double, hiIncl: Boolean, help: String) =
    SolverOption(name, OptionType.DOUBLE, def, lo, hi, loIncl, hiIncl, help)

// Upstream (meelgroup/minisat master 664490d): the Option declarations of core/Solver.cc
// (category CORE) and simp/SimpSolver.cc (SIMP), in their order, then `pre` of simp/Main.cc. An
// IntOption without IntRange has upstream's default range INT32_MIN..INT32_MAX; HUGE_VAL is INF.
private val MINISAT_OPTIONS: List<MiniSatOption> = listOf(
    MiniSatOption(double("var-decay", 0.95, 0.0, false, 1.0, false, "The variable activity decay factor"),
        core = { s, v -> s.varDecay = v.toDouble() }),
    MiniSatOption(double("cla-decay", 0.999, 0.0, false, 1.0, false, "The clause activity decay factor"),
        core = { s, v -> s.clauseDecay = v.toDouble() }),
    MiniSatOption(double("rnd-freq", 0.0, 0.0, true, 1.0, true,
        "The frequency with which the decision heuristic tries to choose a random variable"),
        core = { s, v -> s.randomVarFreq = v.toDouble() }),
    MiniSatOption(double("rnd-seed", 91648253.0, 0.0, false, INF, false, "Used by the random variable selection"),
        core = { s, v -> s.randomSeed = v.toDouble() }),
    MiniSatOption(int("ccmin-mode", 2, 0, 2, "Controls conflict clause minimization (0=none, 1=basic, 2=deep)"),
        core = { s, v -> s.ccminMode = v.toInt() }),
    MiniSatOption(int("phase-saving", 2, 0, 2, "Controls the level of phase saving (0=none, 1=limited, 2=full)"),
        core = { s, v -> s.phaseSaving = v.toInt() }),
    MiniSatOption(bool("rnd-init", false, "Randomize the initial activity"),
        core = { s, v -> s.rndInitAct = v.toInt() == 1 }),
    MiniSatOption(bool("luby", true, "Use the Luby restart sequence"),
        core = { s, v -> s.lubyRestart = v.toInt() == 1 }),
    MiniSatOption(int("rfirst", 100, 1, MAX, "The base restart interval"),
        core = { s, v -> s.restartFirst = v.toInt() }),
    MiniSatOption(double("rinc", 2.0, 1.0, false, INF, false, "Restart interval increase factor"),
        core = { s, v -> s.restartInc = v.toDouble() }),
    MiniSatOption(double("gc-frac", 0.20, 0.0, false, INF, false,
        "The fraction of wasted memory allowed before a garbage collection is triggered"),
        core = { s, v -> s.garbageFrac = v.toDouble() }),
    MiniSatOption(int("min-learnts", 0, 0, MAX, "Minimum learnt clause limit"),
        core = { s, v -> s.minLearntsLim = v.toInt() }),
    MiniSatOption(int("rdb-at", 0, 0, MAX, "k : Call reduceDB at each k conflict. 0=use minisat strategy"),
        core = { s, v -> s.reduceDBAtConfl = v.toInt() }),

    MiniSatOption(bool("asymm", false, "Shrink clauses by asymmetric branching."),
        simp = { s, v -> s.useAsymm = v.toInt() == 1 }),
    MiniSatOption(bool("rcheck", false, "Check if a clause is already implied. (costly)"),
        simp = { s, v -> s.useRcheck = v.toInt() == 1 }),
    MiniSatOption(bool("elim", true, "Perform variable elimination."),
        simp = { s, v -> s.useElim = v.toInt() == 1 }),
    MiniSatOption(int("grow", 0, Int.MIN_VALUE, MAX, "Allow a variable elimination step to grow by a number of clauses."),
        simp = { s, v -> s.grow = v.toInt() }),
    MiniSatOption(int("cl-lim", 20, -1, MAX,
        "Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit"),
        simp = { s, v -> s.clauseLim = v.toInt() }),
    MiniSatOption(int("sub-lim", 1000, -1, MAX,
        "Do not check if subsumption against a clause larger than this. -1 means no limit."),
        simp = { s, v -> s.subsumptionLim = v.toInt() }),
    MiniSatOption(double("simp-gc-frac", 0.5, 0.0, false, INF, false,
        "The fraction of wasted memory allowed before a garbage collection is triggered during simplification."),
        simp = { s, v -> s.simpGarbageFrac = v.toDouble() }),

    MiniSatOption(bool("pre", true, "Completely turn on/off any preprocessing.")),
)
