package org.bytefred.ksat.facade

import org.bytefred.ksat.ExternalPropagator
import org.bytefred.ksat.FixedAssignmentListener
import org.bytefred.ksat.OutBoolean
import org.bytefred.ksat.SatResult
import kotlin.math.abs
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

/**
 * CaDiCaL 2.1.3 forced phases (`Solver::phase` / `unphase`, cadical.hpp: "Force the default
 * decision phase of a variable to a certain value") and the `FixedAssignmentListener`
 * (cadical.hpp: "notified whenever the truth value of a variable is fixed";
 * solver.cpp connect_fixed_listener: "previously found fixed assignments are not sent out").
 * Only CaDiCaL has these; the other ports must throw.
 */
class PhaseAndFixedListenerTest {

    private val solver = Solver.CADICAL

    private class Recorder : FixedAssignmentListener {
        val lits = ArrayList<Int>()
        override fun notifyFixedAssignment(lit: Int) { lits.add(lit) }
    }

    private fun satisfies(clauses: List<IntArray>, assignment: Int, n: Int): Boolean =
        clauses.all { c -> c.any { l -> ((assignment shr (abs(l) - 1)) and 1 == 1) == (l > 0) } }

    private fun models(clauses: List<IntArray>, n: Int): List<Int> =
        (0 until (1 shl n)).filter { satisfies(clauses, it, n) }

    /** [lit] is implied by the clauses (true in every model). */
    private fun implied(clauses: List<IntArray>, n: Int, lit: Int): Boolean =
        models(clauses, n).all { m -> ((m shr (abs(lit) - 1)) and 1 == 1) == (lit > 0) }

    private fun random3Cnf(seed: Int, n: Int, m: Int): List<IntArray> {
        val rnd = Random(seed)
        return List(m) {
            val vars = (1..n).shuffled(rnd).take(3)
            IntArray(3) { i -> if (rnd.nextBoolean()) vars[i] else -vars[i] }
        }
    }

    private fun modelOf(k: Ksat, n: Int): Int {
        var m = 0
        for (v in 1..n) if (k.valueOf(v)) m = m or (1 shl (v - 1))
        return m
    }

    // ------------------------------------------------------------------ phase

    @Test
    fun forcedPhasesThatFormAModelAreTheModel() {
        // PORT-CONFIGURATION behaviour, not an upstream guarantee: upstream only documents "force
        // the default decision phase". It holds here because this port has no lucky phases, local
        // search, rephasing or elimination; upstream's default opts.lucky=1 tries lucky
        // assignments first and may return another model.
        // decide.cpp decide_phase reads phases.forced before target/saved phases, so every
        // decision takes the forced value. If the forced values are a model M, unit propagation
        // under any partial assignment contained in M only implies literals of M (no conflict),
        // so the solve returns exactly M. Every model is forced in turn on one instance
        // (incremental: the forced phase also overrides the saved phases of the previous solve).
        for (seed in 1..5) {
            val n = 6
            val clauses = random3Cnf(seed, n, 10)
            val ms = models(clauses, n)
            if (ms.isEmpty()) continue
            val k = Ksat(solver, numVars = n)
            for (c in clauses) k.addClause(c)
            for (m in ms) {
                for (v in 1..n) k.phase(if ((m shr (v - 1)) and 1 == 1) v else -v)
                assertEquals(SatResult.SAT, k.solve(), "$solver seed $seed: SAT")
                assertEquals(m, modelOf(k, n), "$solver seed $seed: model must equal the forced phases")
            }
        }
    }

    @Test
    fun forcedPhaseOfFreshVariableCreatesItAndIsUsed() {
        // External::phase internalizes the literal, so a variable no clause mentions is created
        // and decided with its forced phase. The value of the fresh variable is PORT-CONFIGURATION
        // behaviour (no lucky phases / local search here, see above).
        for (lit in intArrayOf(3, -3)) {
            val k = Ksat(solver, numVars = 2)
            k.addClause(intArrayOf(1, 2))
            k.phase(lit)
            assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
            assertEquals(lit > 0, k.valueOf(3), "$solver: fresh var 3 takes forced phase $lit")
        }
    }

    @Test
    fun unphaseRestoresDefaultDecisions() {
        // phases.cpp unphase clears phases.forced, so decide_phase falls back to the default
        // chain: the run equals one where phase was never called.
        for (seed in 1..5) {
            val n = 6
            val clauses = random3Cnf(seed, n, 10)
            val ref = Ksat(solver, numVars = n)
            for (c in clauses) ref.addClause(c)
            val refResult = ref.solve()

            val k = Ksat(solver, numVars = n)
            for (c in clauses) k.addClause(c)
            for (v in 1..n) k.phase(-v)
            for (v in 1..n) k.unphase(v) // unphase ignores the sign of its argument
            assertEquals(refResult, k.solve(), "$solver seed $seed: same verdict after unphase")
            if (refResult == SatResult.SAT) {
                assertEquals(modelOf(ref, n), modelOf(k, n), "$solver seed $seed: same model as never forced")
            }
        }
    }

    @Test
    fun unphaseOfUnusedVariableIsIgnored() {
        // External::unphase: "resetting forced phase of unused external ... ignored" (no variable
        // is created).
        val k = Ksat(solver, numVars = 2)
        k.addClause(intArrayOf(1, 2))
        val before = k.numVars
        k.unphase(10)
        assertEquals(before, k.numVars, "$solver: unphase must not create variable 10")
        assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
    }

    @Test
    fun phaseRejectsInvalidLiteral() {
        // solver.cpp REQUIRE_VALID_LIT
        val k = Ksat(solver, numVars = 2)
        assertFailsWith<IllegalArgumentException>("$solver: phase(0)") { k.phase(0) }
        assertFailsWith<IllegalArgumentException>("$solver: unphase(0)") { k.unphase(0) }
        assertFailsWith<IllegalArgumentException>("$solver: phase(INT_MIN)") { k.phase(Int.MIN_VALUE) }
        assertFailsWith<IllegalArgumentException>("$solver: unphase(INT_MIN)") { k.unphase(Int.MIN_VALUE) }
    }

    // ------------------------------------------------------------------ fixed listener

    @Test
    fun originalUnitsAreNotified() {
        // clause.cpp assign_original_unit -> mark_fixed. With the unit first, the root-false
        // literal is dropped from each later clause, so each one is again an original unit.
        val k = Ksat(solver, numVars = 4)
        val r = Recorder()
        k.connectFixedListener(r)
        k.addClause(intArrayOf(-1))
        k.addClause(intArrayOf(1, 2))   // simplified to the unit (2)
        k.addClause(intArrayOf(-2, -3)) // simplified to the unit (-3)
        k.addClause(intArrayOf(3, 4))   // simplified to the unit (4)
        assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
        assertEquals(setOf(-1, 2, -3, 4), r.lits.toSet(), "$solver: all root-fixed literals with their signs")
        assertEquals(r.lits.size, r.lits.map { abs(it) }.toSet().size, "$solver: each variable fixed once")
    }

    @Test
    fun rootPropagationIsNotified() {
        // The unit comes last: assign_original_unit -> mark_fixed (-1), then its root propagation
        // assigns 2, -3, 4 by search_assign at level 0 -> learn_unit_clause -> mark_fixed.
        val k = Ksat(solver, numVars = 4)
        val r = Recorder()
        k.connectFixedListener(r)
        k.addClause(intArrayOf(1, 2))
        k.addClause(intArrayOf(-2, -3))
        k.addClause(intArrayOf(3, 4))
        k.addClause(intArrayOf(-1))
        assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
        assertEquals(setOf(-1, 2, -3, 4), r.lits.toSet(), "$solver: all root-fixed literals with their signs")
        assertEquals(r.lits.size, r.lits.map { abs(it) }.toSet().size, "$solver: each variable fixed once")
    }

    @Test
    fun onlyImpliedLiteralsAreNotified() {
        // Fixed means implied by the formula (cadical.hpp `fixed`), so every notified literal must
        // be true in all models, and no variable is fixed twice (flags.cpp asserts ACTIVE status).
        for (seed in 1..20) {
            val n = 8
            val clauses = random3Cnf(seed, n, 30)
            val k = Ksat(solver, numVars = n)
            val r = Recorder()
            k.connectFixedListener(r)
            for (c in clauses) k.addClause(c)
            val res = k.solve()
            assertEquals(models(clauses, n).isNotEmpty(), res == SatResult.SAT, "$solver seed $seed: verdict")
            for (lit in r.lits) assertTrue(implied(clauses, n, lit), "$solver seed $seed: notified $lit is not implied")
            assertEquals(r.lits.size, r.lits.map { abs(it) }.toSet().size, "$solver seed $seed: each variable fixed once")
        }
    }

    @Test
    fun learnedUnitsAreNotifiedBeforeUnsat() {
        // Without unit clauses nothing is fixed at the root initially; UNSAT is only concluded by
        // a conflict at the root, which needs fixed literals, i.e. learned units (analyze ->
        // search_assign at level 0 -> learn_unit_clause -> mark_fixed).
        val clauses = listOf(intArrayOf(1, 2), intArrayOf(1, -2), intArrayOf(-1, 2), intArrayOf(-1, -2))
        val k = Ksat(solver, numVars = 2)
        val r = Recorder()
        k.connectFixedListener(r)
        for (c in clauses) k.addClause(c)
        assertEquals(SatResult.UNSAT, k.solve(), "$solver: UNSAT")
        assertTrue(r.lits.isNotEmpty(), "$solver: at least one learned unit must be notified")
        assertEquals(r.lits.size, r.lits.map { abs(it) }.toSet().size, "$solver: each variable fixed once")
    }

    @Test
    fun unitsFixedBeforeConnectAreNotReplayed() {
        // solver.cpp connect_fixed_listener: listeners are real-time, previously found fixed
        // assignments are not sent out.
        val k = Ksat(solver, numVars = 3)
        k.addClause(intArrayOf(1))
        k.addClause(intArrayOf(-1, 2))
        val r = Recorder()
        k.connectFixedListener(r)
        assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
        assertTrue(1 !in r.lits && 2 !in r.lits, "$solver: 1 and 2 were fixed before connect, got ${r.lits}")
        k.addClause(intArrayOf(-3))
        assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
        assertTrue(-3 in r.lits, "$solver: unit -3 added after connect must be notified, got ${r.lits}")
    }

    @Test
    fun disconnectStopsAndReconnectReplacesNotifications() {
        // solver.cpp: disconnect_fixed_listener clears the listener; connecting a new one
        // disconnects the previous one.
        val k = Ksat(solver, numVars = 3)
        val a = Recorder()
        val b = Recorder()
        k.connectFixedListener(a)
        k.addClause(intArrayOf(1))
        k.disconnectFixedListener()
        k.addClause(intArrayOf(2))
        k.connectFixedListener(a)
        k.connectFixedListener(b)
        k.addClause(intArrayOf(-3))
        assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
        assertEquals(listOf(1), a.lits, "$solver: a gets 1 only (disconnected for 2, replaced for -3)")
        assertEquals(listOf(-3), b.lits, "$solver: b gets -3 only")
        k.disconnectFixedListener()
        k.disconnectFixedListener() // ignored without a listener
    }

    // ------------------------------------------------------------------ IPASIR-UP paths

    /**
     * Eager propagator that tracks its decision level (notify_new_decision_level /
     * notify_backtrack; the level it sees is never above the solver's) and, only above the root:
     *  - propagates the unassigned literals of [propagations] in order, each with its reason;
     *  - hands out the clauses of [externalClauses] once each.
     * It suggests [decision] as decision literal while that variable is unassigned.
     */
    private class ScriptedPropagator(
        val propagations: List<Pair<Int, IntArray>> = emptyList(),
        val externalClauses: List<IntArray> = emptyList(),
        val decision: Int = 0,
    ) : ExternalPropagator {
        var level = 0
        // var -> level seen at notification. That level is never above the real one, so an entry
        // is only dropped on backtrack when the variable really is unassigned (kept out-of-order
        // literals are re-notified); a stale entry only suppresses a propagation.
        val assigned = HashMap<Int, Int>()
        var nextClause = 0
        var pending: IntArray? = null
        var pendingPos = 0
        var onCallback: (() -> Unit)? = null

        override fun notifyAssignment(lits: IntArray) { for (l in lits) assigned[abs(l)] = level }
        override fun notifyNewDecisionLevel() { level++ }
        override fun notifyBacktrack(newLevel: Int) {
            level = newLevel
            assigned.entries.removeAll { it.value > newLevel }
        }
        override fun cbDecide(): Int = if (decision != 0 && assigned[abs(decision)] == null) decision else 0
        override fun cbCheckFoundModel(model: IntArray): Boolean { onCallback?.invoke(); return true }
        override fun cbPropagate(): Int {
            onCallback?.invoke()
            if (level == 0) return 0
            for ((lit, _) in propagations) if (assigned[abs(lit)] == null) return lit
            return 0
        }
        private var reasonPos = 0
        private var reasonOf = 0
        override fun cbAddReasonClauseLit(propagatedLit: Int): Int {
            if (reasonOf != propagatedLit) { reasonOf = propagatedLit; reasonPos = 0 }
            val reason = propagations.first { it.first == propagatedLit }.second
            return if (reasonPos < reason.size) reason[reasonPos++] else { reasonOf = 0; 0 }
        }
        override fun cbHasExternalClause(isForgettable: OutBoolean): Boolean {
            if (level == 0 || nextClause >= externalClauses.size) return false
            pending = externalClauses[nextClause++]
            pendingPos = 0
            return true
        }
        override fun cbAddExternalClauseLit(): Int {
            val c = pending!!
            return if (pendingPos < c.size) c[pendingPos++] else { pending = null; 0 }
        }
    }

    private fun assertSoundOnce(r: Recorder, clauses: List<IntArray>, n: Int, what: String) {
        for (lit in r.lits) assertTrue(implied(clauses, n, lit), "$solver $what: notified $lit is not implied")
        assertEquals(r.lits.size, r.lits.map { abs(it) }.toSet().size, "$solver $what: each variable fixed once, got ${r.lits}")
    }

    @Test
    fun externalUnitClauseAboveRootIsNotified() {
        // clause.cpp:488-494: an external unit clause added at level > 0 backtracks
        // (handle_external_clause) and is assigned by assign_original_unit -> mark_fixed; its
        // root propagation (search_assign at level 0) fixes 2.
        val direct = listOf(intArrayOf(1, 2), intArrayOf(3, 4))
        val external = listOf(intArrayOf(-1))
        val k = Ksat(solver, numVars = 4)
        val p = ScriptedPropagator(externalClauses = external)
        k.connectExternalPropagator(p)
        for (v in 1..4) k.addObservedVar(v)
        val r = Recorder()
        k.connectFixedListener(r)
        for (c in direct) k.addClause(c)
        assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
        assertEquals(1, p.nextClause, "$solver: the external unit must have been handed out")
        assertTrue(-1 in r.lits && 2 in r.lits, "$solver: -1 (external unit) and 2 (its propagation) notified, got ${r.lits}")
        assertSoundOnce(r, direct + external, 4, "external unit")
    }

    @Test
    fun unitReasonsLearnedDuringExplanationAreNotified() {
        // The propagator decides d=1, then above the root propagates u=3 (reason (3)) and L=4
        // (reason (4 -3)). Then (-1 -4 2) and (-1 -4 -2) conflict, and
        // explain_external_propagations learns the reasons lazily:
        //  - (3) is a unit learned with force_no_backtrack -> clause.cpp:486 mark_fixed (3);
        //  - (4 -3) then has real level 0 -> external_propagate.cpp:634 learn_unit_clause (4).
        val direct = listOf(intArrayOf(-1, -4, 2), intArrayOf(-1, -4, -2))
        val hidden = listOf(intArrayOf(3), intArrayOf(4, -3))
        val k = Ksat(solver, numVars = 4)
        val p = ScriptedPropagator(propagations = listOf(3 to intArrayOf(3), 4 to intArrayOf(4, -3)), decision = 1)
        k.connectExternalPropagator(p)
        for (v in 1..4) k.addObservedVar(v)
        val r = Recorder()
        k.connectFixedListener(r)
        for (c in direct) k.addClause(c)
        assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
        assertTrue(3 in r.lits && 4 in r.lits, "$solver: 3 and 4 notified, got ${r.lits}")
        assertSoundOnce(r, direct + hidden, 4, "explained units")
    }

    @Test
    fun fixedListenerCannotBeChangedFromPropagatorCallback() {
        // solver.cpp: connect/disconnect_fixed_listener REQUIRE_VALID_STATE, i.e. not while solving.
        val k = Ksat(solver, numVars = 2)
        val p = ScriptedPropagator()
        var connectThrew = false
        var disconnectThrew = false
        p.onCallback = {
            try { k.connectFixedListener(Recorder()) } catch (e: IllegalArgumentException) { connectThrew = true }
            try { k.disconnectFixedListener() } catch (e: IllegalArgumentException) { disconnectThrew = true }
        }
        k.connectExternalPropagator(p)
        k.addObservedVar(1)
        k.addObservedVar(2)
        k.addClause(intArrayOf(1, 2))
        assertEquals(SatResult.SAT, k.solve(), "$solver: SAT")
        assertTrue(connectThrew, "$solver: connectFixedListener during solving must throw")
        assertTrue(disconnectThrew, "$solver: disconnectFixedListener during solving must throw")
    }

    // ------------------------------------------------------------------ other solvers

    @Test
    fun otherSolversRejectPhaseAndFixedListener() {
        for (other in listOf(Solver.MINISAT, Solver.KISSAT, Solver.MICROSAT)) {
            val k = Ksat(other, numVars = 2)
            assertFailsWith<UnsupportedOperationException>("$other: phase") { k.phase(1) }
            assertFailsWith<UnsupportedOperationException>("$other: unphase") { k.unphase(1) }
            assertFailsWith<UnsupportedOperationException>("$other: connectFixedListener") { k.connectFixedListener(Recorder()) }
            assertFailsWith<UnsupportedOperationException>("$other: disconnectFixedListener") { k.disconnectFixedListener() }
        }
    }
}
