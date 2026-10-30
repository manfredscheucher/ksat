package org.bytefred.ksat.facade

import org.bytefred.ksat.SatResult
import org.bytefred.ksat.cadical.CaDiCaL
import org.bytefred.ksat.minisat.MiniSat
import org.bytefred.ksat.minisat.MiniSatSimp
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertTrue

/**
 * Solver options (ksat-extra/doc/solver-options.md): the upstream names and defaults, values
 * reaching the port, and loud failures for unknown names, bad values and option-less solvers.
 */
class SolverOptionsTest {

    // Upstream meelgroup/minisat master 664490d: core/Solver.cc, simp/SimpSolver.cc, simp/Main.cc `pre`.
    private val miniSatUpstream: Map<String, Number> = mapOf(
        "var-decay" to 0.95, "cla-decay" to 0.999, "rnd-freq" to 0.0, "rnd-seed" to 91648253.0,
        "ccmin-mode" to 2, "phase-saving" to 2, "rnd-init" to 0, "luby" to 1, "rfirst" to 100,
        "rinc" to 2.0, "gc-frac" to 0.20, "min-learnts" to 0, "rdb-at" to 0,
        "asymm" to 0, "rcheck" to 0, "elim" to 1, "grow" to 0, "cl-lim" to 20, "sub-lim" to 1000,
        "simp-gc-frac" to 0.5, "pre" to 1,
    )

    /** The port var behind each MiniSat option (bools as 0 / 1). */
    private val miniSatVar: Map<String, (MiniSatSimp) -> Number> = mapOf(
        "var-decay" to { it.varDecay }, "cla-decay" to { it.clauseDecay }, "rnd-freq" to { it.randomVarFreq },
        "rnd-seed" to { it.randomSeed }, "ccmin-mode" to { it.ccminMode }, "phase-saving" to { it.phaseSaving },
        "rnd-init" to { if (it.rndInitAct) 1 else 0 }, "luby" to { if (it.lubyRestart) 1 else 0 },
        "rfirst" to { it.restartFirst }, "rinc" to { it.restartInc }, "gc-frac" to { it.garbageFrac },
        "min-learnts" to { it.minLearntsLim }, "rdb-at" to { it.reduceDBAtConfl },
        "asymm" to { if (it.useAsymm) 1 else 0 }, "rcheck" to { if (it.useRcheck) 1 else 0 },
        "elim" to { if (it.useElim) 1 else 0 }, "grow" to { it.grow }, "cl-lim" to { it.clauseLim },
        "sub-lim" to { it.subsumptionLim }, "simp-gc-frac" to { it.simpGarbageFrac },
    )

    private fun miniSat(options: Map<String, Number>): MiniSat = Ksat(Solver.MINISAT, 0, options).delegate as MiniSat
    private fun caDiCaL(options: Map<String, Number>): CaDiCaL = Ksat(Solver.CADICAL, 0, options).delegate as CaDiCaL

    @Test
    fun miniSatOptionsAreTheUpstreamOnes() {
        val opts = solverOptions(Solver.MINISAT)
        assertEquals(miniSatUpstream.keys.toList(), opts.map { it.name })
        for (o in opts) assertEquals(miniSatUpstream.getValue(o.name), o.default, o.name)
        val rdb = opts.single { it.name == "rdb-at" }
        assertEquals(SolverOption("rdb-at", OptionType.INT, 0, 0, Int.MAX_VALUE, true, true,
            "k : Call reduceDB at each k conflict. 0=use minisat strategy"), rdb)
        val decay = opts.single { it.name == "var-decay" }
        assertEquals(listOf<Any>(OptionType.DOUBLE, 0.0, 1.0, false, false),
            listOf(decay.type, decay.min, decay.max, decay.minInclusive, decay.maxInclusive))
        assertEquals(Int.MIN_VALUE, opts.single { it.name == "grow" }.min)
    }

    @Test
    fun miniSatWithoutOptionsHasThePortDefaults() {
        val s = assertIs<MiniSatSimp>(miniSat(emptyMap()), "no options = pre=1 = SimpSolver")
        for ((name, get) in miniSatVar) assertEquals(miniSatUpstream.getValue(name), get(s), name)
    }

    @Test
    fun preSelectsCoreOrSimpSolver() {
        assertIs<MiniSatSimp>(miniSat(mapOf("pre" to 1)))
        val core = miniSat(mapOf("pre" to 0))
        assertFalse(core is MiniSatSimp, "pre=0 is the core Solver")
        assertEquals(0.5, miniSat(mapOf("pre" to 0, "var-decay" to 0.5)).varDecay)
    }

    @Test
    fun miniSatValuesReachThePortVars() {
        val values: Map<String, Number> = mapOf(
            "var-decay" to 0.9, "cla-decay" to 0.99, "rnd-freq" to 1.0, "rnd-seed" to 7.0, "ccmin-mode" to 0,
            "phase-saving" to 1, "rnd-init" to 1, "luby" to 0, "rfirst" to 50, "rinc" to 1.5, "gc-frac" to 0.3,
            "min-learnts" to 10, "rdb-at" to 2000, "asymm" to 1, "rcheck" to 1, "elim" to 0, "grow" to -3,
            "cl-lim" to -1, "sub-lim" to 5, "simp-gc-frac" to 0.25,
        )
        val s = assertIs<MiniSatSimp>(miniSat(values))
        for ((name, get) in miniSatVar) assertEquals(values.getValue(name), get(s), name)
        // integral values of any Number type are taken
        assertEquals(3, miniSat(mapOf("rfirst" to 3L)).restartFirst)
        assertEquals(3, miniSat(mapOf("rfirst" to 3.0)).restartFirst)
        assertEquals(2.0, miniSat(mapOf("rinc" to 2)).restartInc)
    }

    @Test
    fun miniSatRejectsBadOptions() {
        val bad: List<Map<String, Number>> = listOf(
            mapOf("nosuch" to 1), mapOf("verb" to 0), mapOf("rnd-pol" to 1),   // not upstream solver options
            mapOf("pre" to 2), mapOf("luby" to -1), mapOf("elim" to 0.5),     // bools take 0 / 1
            mapOf("rfirst" to 0), mapOf("ccmin-mode" to 3), mapOf("cl-lim" to -2), mapOf("rfirst" to 1.5),
            mapOf("rdb-at" to Int.MAX_VALUE.toLong() + 1),
            mapOf("var-decay" to 0.0), mapOf("var-decay" to 1.0), mapOf("rnd-freq" to 1.01),
            mapOf("rinc" to 1.0), mapOf("gc-frac" to 0), mapOf("rnd-seed" to Double.POSITIVE_INFINITY),
            mapOf("var-decay" to Double.NaN),
            mapOf("pre" to 0, "elim" to 0),                                     // SimpSolver option on the core Solver
        )
        for (options in bad) assertFailsWith<IllegalArgumentException>("$options") { Ksat(Solver.MINISAT, 1, options) }
        // the inclusive end of rnd-freq is allowed
        assertEquals(0.0, miniSat(mapOf("rnd-freq" to 0)).randomVarFreq)
    }

    @Test
    fun caDiCaLOptionsAreTheUpstreamTable() {
        val opts = solverOptions(Solver.CADICAL)
        assertEquals(177, opts.size, "options.hpp of CaDiCaL 2.1.3 without the LOGGING-only log / logsort")
        val fresh = caDiCaL(emptyMap())
        for (o in opts) {
            assertEquals(o.default, fresh.getOption(o.name), "${o.name}: nothing is set without options")
            assertTrue(o.minInclusive && o.maxInclusive)
            assertEquals(if (o.min == 0 && o.max == 1) OptionType.BOOL else OptionType.INT, o.type, o.name)
        }
        assertEquals(SolverOption("elim", OptionType.BOOL, 1, 0, 1, true, true, "bounded variable elimination"),
            opts.single { it.name == "elim" })
        assertEquals(SolverOption("arenatype", OptionType.INT, 3, 1, 3, true, true, "1=clause, 2=var, 3=queue"),
            opts.single { it.name == "arenatype" })
    }

    @Test
    fun caDiCaLValuesReachGet() {
        val s = caDiCaL(mapOf("elim" to 0, "seed" to 42, "arenatype" to 1.0))
        assertEquals(0, s.getOption("elim"))
        assertEquals(42, s.getOption("seed"))
        assertEquals(1, s.getOption("arenatype"))
        // the copy keeps the options (upstream Solver::copy copies them)
        val k = Ksat(Solver.CADICAL, 2, mapOf("seed" to 42)).also { it.addClause(intArrayOf(1, 2)) }
        assertEquals(42, (k.copy().delegate as CaDiCaL).getOption("seed"))
        // and solving works with preprocessing off
        val p = Ksat(Solver.CADICAL, 2, mapOf("elim" to 0, "subsume" to 0))
        p.addClause(intArrayOf(1, 2)); p.addClause(intArrayOf(-1))
        assertEquals(SatResult.SAT, p.solve())
        assertTrue(p.valueOf(2))
    }

    @Test
    fun caDiCaLRejectsBadOptions() {
        val bad: List<Map<String, Number>> = listOf(
            mapOf("nosuch" to 1), mapOf("log" to 1), mapOf("pre" to 0),
            mapOf("elim" to 2), mapOf("elim" to -1), mapOf("arenatype" to 0), mapOf("seed" to 0.5),
        )
        for (options in bad) assertFailsWith<IllegalArgumentException>("$options") { Ksat(Solver.CADICAL, 1, options) }
        // the adapter itself rejects (upstream would clamp) as well
        assertFailsWith<IllegalArgumentException> { CaDiCaL().setOption("arenatype", 4) }
        assertFailsWith<IllegalArgumentException> { CaDiCaL().setOption("nosuch", 0) }
    }

    @Test
    fun kissatAndMicroSatHaveNoOptions() {
        for (s in listOf(Solver.KISSAT, Solver.MICROSAT)) {
            assertEquals(emptyList(), solverOptions(s))
            assertFailsWith<IllegalArgumentException>("$s") { Ksat(s, 1, mapOf("seed" to 0)) }
            assertEquals(SatResult.SAT, Ksat(s, 1, emptyMap()).solve())
        }
    }
}
