package org.bytefred.ksat.facade

import org.bytefred.ksat.ExternalPropagation
import org.bytefred.ksat.ExternalPropagator
import org.bytefred.ksat.OutBoolean
import org.bytefred.ksat.SatResult
import kotlin.math.abs
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFails
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

/**
 * IPASIR-UP (external user propagator) behavioral contract, written from CaDiCaL 2.1.3's
 * documented semantics (cadical.hpp: `ExternalPropagator` and the IPASIR-UP block of `Solver`)
 * and from upstream's own test propagator (`MockPropagator` in mobical.cpp). Independent of the
 * port's implementation.
 *
 * Every scenario splits a CNF F into clauses given to the solver directly and clauses known
 * only to a [ClausePropagator]. Whatever the propagator does (lazy model checking, eager
 * propagation with reasons, forced decisions), the verdict must equal F's true verdict (brute
 * force, tiny formulas) and a SAT model must satisfy all of F.
 */
class ExternalPropagatorTest {

    // ---------------------------------------------------------------- formulas

    private class Cnf(val name: String, val numVars: Int, val clauses: List<IntArray>)

    /** PHP(p, h): p pigeons into h holes; var(i, j) = pigeon i sits in hole j. UNSAT iff p > h. */
    private fun php(pigeons: Int, holes: Int): Pair<List<IntArray>, List<IntArray>> {
        fun v(i: Int, j: Int) = (i - 1) * holes + j
        val atLeastOne = (1..pigeons).map { i -> IntArray(holes) { j -> v(i, j + 1) } }
        val atMostOne = ArrayList<IntArray>()
        for (j in 1..holes) for (i in 1..pigeons) for (k in i + 1..pigeons) atMostOne.add(intArrayOf(-v(i, j), -v(k, j)))
        return atLeastOne to atMostOne
    }

    /** Seeded random 3-CNF over [n] vars with [m] clauses (deterministic, no flakiness). */
    private fun random3Cnf(seed: Int, n: Int, m: Int): List<IntArray> {
        val rnd = Random(seed)
        return List(m) {
            val vars = (1..n).shuffled(rnd).take(3)
            IntArray(3) { i -> if (rnd.nextBoolean()) vars[i] else -vars[i] }
        }
    }

    /** A split of a formula into solver-side clauses and propagator-only clauses. */
    private class Split(val name: String, val numVars: Int, val direct: List<IntArray>, val hidden: List<IntArray>) {
        val all: List<IntArray> get() = direct + hidden
    }

    private val splits: List<Split> by lazy {
        val (php32Alo, php32Amo) = php(3, 2)
        val (php22Alo, php22Amo) = php(2, 2)
        val (php43Alo, php43Amo) = php(4, 3)
        val exactlyOne = listOf(intArrayOf(1, 2, 3))
        val amo3 = listOf(intArrayOf(-1, -2), intArrayOf(-1, -3), intArrayOf(-2, -3))
        val list = mutableListOf(
            Split("PHP(3,2) direct=at-least-one, hidden=at-most-one", 6, php32Alo, php32Amo),
            Split("PHP(3,2) direct=at-most-one, hidden=at-least-one", 6, php32Amo, php32Alo),
            Split("PHP(3,2) all clauses hidden", 6, emptyList(), php32Alo + php32Amo),
            Split("PHP(4,3) direct=at-least-one, hidden=at-most-one", 12, php43Alo, php43Amo),
            Split("PHP(2,2) direct=at-least-one, hidden=at-most-one", 4, php22Alo, php22Amo),
            Split("PHP(2,2) all clauses hidden", 4, emptyList(), php22Alo + php22Amo),
            Split("exactly-one-of-3 hidden=at-most-one", 3, exactlyOne, amo3),
        )
        for (seed in 1..6) {
            val f = random3Cnf(seed, n = 8, m = 36)
            list.add(Split("random3cnf(seed=$seed) odd clauses hidden", 8,
                f.filterIndexed { i, _ -> i % 2 == 0 }, f.filterIndexed { i, _ -> i % 2 == 1 }))
        }
        list
    }

    // ---------------------------------------------------------------- ground truth

    private fun satisfies(clauses: List<IntArray>, value: (Int) -> Boolean): Boolean =
        clauses.all { c -> c.any { lit -> value(abs(lit)) == (lit > 0) } }

    /** Brute-force verdict of [clauses] plus unit [assumptions] (numVars <= 12 here). */
    private fun bruteForce(numVars: Int, clauses: List<IntArray>, assumptions: IntArray = IntArray(0)): SatResult {
        val all = clauses + assumptions.map { intArrayOf(it) }
        for (mask in 0 until (1 shl numVars)) {
            if (satisfies(all) { v -> (mask shr (v - 1)) and 1 == 1 }) return SatResult.SAT
        }
        return SatResult.UNSAT
    }

    private fun assertModel(k: Ksat, clauses: List<IntArray>, what: String) {
        val bad = clauses.firstOrNull { c -> c.none { lit -> k.valueOf(abs(lit)) == (lit > 0) } }
        assertTrue(bad == null, "$what: SAT model violates clause ${bad?.toList()}")
    }

    /** Solver with [Split.direct] loaded and [p] connected, observing every variable 1..numVars. */
    private fun solverWith(split: Split, p: ClausePropagator): Ksat {
        val k = Ksat(Solver.CADICAL, numVars = split.numVars)
        for (c in split.direct) k.addClause(c)
        k.connectExternalPropagator(p)
        p.host = k
        // Upstream: every variable of an external/reason clause must be observed; an observed
        // variable may be fresh (never mentioned in a clause yet).
        for (v in 1..split.numVars) {
            k.addObservedVar(v)
            p.observed.add(v)
        }
        return k
    }

    private fun assertNoViolations(p: ClausePropagator, what: String) {
        assertTrue(p.violations.isEmpty(), "$what: IPASIR-UP contract violations:\n" + p.violations.take(10).joinToString("\n"))
    }

    // ---------------------------------------------------------------- 1. lazy clause provider

    @Test
    fun lazyClauseProviderViaModelRejectionGivesTrueVerdict() {
        // cadical.hpp cb_check_found_model: "If it returns false, the propagator should provide
        // an external clause during the next callback". The solver must then keep searching and
        // end with F's verdict; mobical's MockPropagator works exactly like this.
        for (s in splits) {
            val p = ClausePropagator(s.hidden, eager = false)
            val k = solverWith(s, p)
            val expected = bruteForce(s.numVars, s.all)
            assertEquals(expected, k.solve(), "${s.name}: verdict with lazily supplied clauses must equal F's")
            if (expected == SatResult.SAT) assertModel(k, s.all, s.name)
            assertNoViolations(p, s.name)
            assertEquals(expected, Ksat(Solver.CADICAL, s.numVars).also { d -> s.all.forEach { d.addClause(it) } }.solve(),
                "${s.name}: plain solve of F must agree with brute force")
        }
    }

    @Test
    fun rejectedModelLeadsToClauseRequest() {
        // Fully hidden PHP(3,2): with no direct clauses every complete model is checked by the
        // propagator; at least one rejection is followed by
        // cb_has_external_clause + cb_add_external_clause_lit.
        val s = splits.first { it.name == "PHP(3,2) all clauses hidden" }
        val p = ClausePropagator(s.hidden, eager = false)
        val k = solverWith(s, p)
        assertEquals(SatResult.UNSAT, k.solve(), "PHP(3,2) only known to the propagator is UNSAT")
        assertTrue(p.modelChecks > 0, "cbCheckFoundModel must be called for a formula with no direct clauses")
        assertTrue(p.externalClausesAdded > 0, "a rejected model must be followed by external clause addition")
        assertNoViolations(p, s.name)
    }

    // ---------------------------------------------------------------- 2. eager propagation

    @Test
    fun eagerPropagationWithReasonClausesGivesTrueVerdict() {
        // cb_propagate returns an implied literal; cb_add_reason_clause_lit later delivers its
        // reason clause (literal by literal, closed by 0, containing the propagated literal).
        // Our propagator only propagates literals unit-implied by its clauses under its notified
        // assignment, so every reason is a clause of F and correct w.r.t. the propagator's view.
        var totalPropagations = 0
        for (s in splits) {
            val p = ClausePropagator(s.hidden, eager = true)
            val k = solverWith(s, p)
            val expected = bruteForce(s.numVars, s.all)
            assertEquals(expected, k.solve(), "${s.name}: verdict with eager external propagation must equal F's")
            if (expected == SatResult.SAT) assertModel(k, s.all, s.name)
            assertNoViolations(p, s.name)
            totalPropagations += p.propagations
        }
        assertTrue(totalPropagations > 0, "no external propagation happened in any scenario (cbPropagate never effective)")
    }

    @Test
    fun reasonClausesAreRequestedOnlyForPropagatedLiterals() {
        // cb_add_reason_clause_lit(propagated_lit) is about "a previous external propagation step
        // (done by cb_propagate)": it must never be asked for a literal we did not propagate.
        // ClausePropagator records any such request as a violation. Reasons must actually be
        // requested somewhere: upstream option exteagerreasons defaults to 1 (options.hpp) and
        // makes conflict analysis ask for all external reasons eagerly (analyze.cpp ~908), and the
        // UNSAT splits produce conflicts after external propagations.
        var requests = 0
        for (s in splits) {
            val p = ClausePropagator(s.hidden, eager = true)
            val k = solverWith(s, p)
            k.solve()
            assertNoViolations(p, s.name)
            requests += p.reasonRequests
        }
        assertTrue(requests > 0, "cbAddReasonClauseLit was never called over all splits")
    }

    // ---------------------------------------------------------------- 3. notifications

    @Test
    fun notificationsFormAConsistentTrailMirror() {
        // notify_assignment / notify_new_decision_level / notify_backtrack let the propagator keep
        // a per-level trail (as MockPropagator does). Invariants checked inside ClausePropagator:
        //  - a non-root assignment is never notified twice without a backtrack below its level
        //    (root-level assignments may be re-notified: renotify_full_trail, external.cpp);
        //  - notify_backtrack(newLevel) never exceeds the current level (MockPropagator asserts it);
        //  - at cb_check_found_model every mirrored observed var agrees with the passed model
        //    (MockPropagator asserts compare_trails() there).
        // Notifications are not eager, so nothing is asserted about WHEN they arrive.
        for (eager in listOf(false, true)) for (s in splits) {
            val p = ClausePropagator(s.hidden, eager = eager)
            val k = solverWith(s, p)
            k.solve()
            assertNoViolations(p, "${s.name} (eager=$eager)")
        }
    }

    // ---------------------------------------------------------------- 4. cbDecide / isDecision

    @Test
    fun forcedDecisionsKeepVerdictAndAreReportedAsDecisions() {
        // cb_decide: "Ask the external propagator for the next decision literal." is_decision:
        // true iff "it is an observed variable and it got assigned by a decision during the CDCL
        // loop". Checked inside cbPropagate for the literal we decided while it is still assigned
        // on the level it opened; other literals on that level were propagated, hence false.
        var checks = 0
        for (eager in listOf(false, true)) for (s in splits) {
            val p = ClausePropagator(s.hidden, eager = eager, decide = true)
            val k = solverWith(s, p)
            val expected = bruteForce(s.numVars, s.all)
            assertEquals(expected, k.solve(), "${s.name} (eager=$eager): verdict with propagator decisions must equal F's")
            if (expected == SatResult.SAT) assertModel(k, s.all, s.name)
            assertNoViolations(p, "${s.name} (eager=$eager, decide)")
            checks += p.isDecisionChecks
        }
        assertTrue(checks > 0, "isDecision was never checked for a propagator decision (cbDecide never effective?)")
    }

    @Test
    fun decisionOnUnconstrainedFormulaIsUsed() {
        // XOR(1,2) AND XOR(3,4): nothing is implied at the root, so the solver must decide; with a
        // propagator that always proposes a decision, cb_decide must be asked and its literal used.
        val s = Split("two XORs", 4, listOf(intArrayOf(1, 2), intArrayOf(-1, -2), intArrayOf(3, 4), intArrayOf(-3, -4)), emptyList())
        val p = ClausePropagator(s.hidden, eager = false, decide = true)
        val k = solverWith(s, p)
        assertEquals(SatResult.SAT, k.solve(), "two XORs are satisfiable")
        assertModel(k, s.all, s.name)
        assertTrue(p.decisionsMade > 0, "cbDecide must be consulted when the solver has to decide")
        assertTrue(p.isDecisionChecks > 0, "the proposed decision must show up as a decision (isDecision) in cbPropagate")
        assertNoViolations(p, s.name)
    }

    // ---------------------------------------------------------------- 5. isLazy

    @Test
    fun lazyPropagatorOnlyChecksCompleteModels() {
        // is_lazy: "lazy propagator only checks complete assignments". Verdicts must still be
        // F's; cb_propagate / cb_decide must not be asked of a lazy propagator: upstream returns
        // early on external_prop_is_lazy in external_propagate (external_propagate.cpp ~238) and in
        // notify_assignments / notify_decision / notify_backtrack / ask_decision (~929-992).
        for (s in splits) {
            val p = ClausePropagator(s.hidden, eager = false, decide = true, isLazy = true)
            val k = solverWith(s, p)
            val expected = bruteForce(s.numVars, s.all)
            assertEquals(expected, k.solve(), "${s.name}: verdict with a lazy propagator must equal F's")
            if (expected == SatResult.SAT) assertModel(k, s.all, s.name)
            assertEquals(0, p.propagateCalls, "${s.name}: cbPropagate called on a lazy propagator")
            assertEquals(0, p.decideCalls, "${s.name}: cbDecide called on a lazy propagator")
            assertNoViolations(p, s.name)
        }
    }

    // ---------------------------------------------------------------- 6. disconnect

    @Test
    fun afterDisconnectNoCallbacksFireAndPlainSolveWorks() {
        // disconnect_external_propagator: afterwards the solver runs without the propagator.
        // Callbacks during the disconnect call itself are not counted (upstream may notify a
        // backtrack while resetting the observed vars).
        val s = splits.first { it.name == "exactly-one-of-3 hidden=at-most-one" }
        val p = ClausePropagator(s.hidden, eager = true)
        val k = solverWith(s, p)
        assertEquals(SatResult.SAT, k.solve(), "exactly-one-of-3 is SAT")
        assertModel(k, s.all, "with propagator")
        k.disconnectExternalPropagator()
        val before = p.totalCallbacks
        for (c in s.hidden) k.addClause(c)
        assertEquals(SatResult.SAT, k.solve(), "after disconnect, F loaded directly is SAT")
        assertModel(k, s.all, "after disconnect")
        assertEquals(SatResult.UNSAT, k.solve(intArrayOf(1, 2)), "after disconnect, assuming 1 and 2 violates (-1 OR -2)")
        assertEquals(before, p.totalCallbacks, "no propagator callback may fire after disconnectExternalPropagator")
    }

    @Test
    fun disconnectBeforeSolveMeansNoCallbacks() {
        val s = splits.first { it.name == "PHP(3,2) direct=at-least-one, hidden=at-most-one" }
        val p = ClausePropagator(s.hidden, eager = true, decide = true)
        val k = solverWith(s, p)
        k.disconnectExternalPropagator()
        val before = p.totalCallbacks
        // Without the hidden at-most-one clauses the remaining at-least-one clauses are SAT.
        assertEquals(SatResult.SAT, k.solve(), "only the direct clauses remain after disconnect: SAT")
        assertModel(k, s.direct, "after disconnect")
        assertEquals(before, p.totalCallbacks, "no propagator callback may fire after disconnectExternalPropagator")
    }

    // ---------------------------------------------------------------- 7. API misuse

    @Test
    fun otherSolversRejectExternalPropagators() {
        for (solver in listOf(MINISAT_CORE, MINISAT_PRE, KISSAT, MICROSAT)) {
            val k = solver.ksat(numVars = 2)
            assertFailsWith<UnsupportedOperationException>("$solver must not accept an external propagator") {
                k.connectExternalPropagator(ClausePropagator(emptyList(), eager = false))
            }
            assertFailsWith<UnsupportedOperationException>("$solver has no observed vars") { k.addObservedVar(1) }
        }
    }

    @Test
    fun observingWithoutConnectedPropagatorHasNoEffect() {
        // external.cpp add_observed_var: without a connected propagator the observed flag is not
        // set (upstream returns after a LOG). So the variable is not observed by a propagator
        // connected later, and the call is not an error.
        val k = Ksat(Solver.CADICAL, numVars = 2)
        k.addClause(intArrayOf(1, 2))
        k.addObservedVar(1)
        val p = ClausePropagator(emptyList(), eager = false)
        k.connectExternalPropagator(p)
        assertEquals(SatResult.SAT, k.solve(), "plain formula is SAT")
        assertTrue(p.lastModel!!.isEmpty(), "var 1 observed before connect must not be observed, model ${p.lastModel!!.toList()}")
        assertTrue(p.notifiedVars.isEmpty(), "no observed vars, but notified: ${p.notifiedVars}")
        assertNoViolations(p, "observe-before-connect")

        k.disconnectExternalPropagator()
        k.addObservedVar(2)
        val p2 = ClausePropagator(emptyList(), eager = false)
        k.connectExternalPropagator(p2)
        assertEquals(SatResult.SAT, k.solve(), "plain formula is SAT after reconnect")
        assertTrue(p2.lastModel!!.isEmpty(), "var 2 observed while disconnected must not be observed, model ${p2.lastModel!!.toList()}")
        assertNoViolations(p2, "observe-while-disconnected")
    }

    // ---------------------------------------------------------------- 8. incremental reuse

    @Test
    fun incrementalSolvesWithPropagatorAndAssumptions() {
        // Same instance, propagator stays connected across solve calls (IPASIR incremental use).
        // exactly-one-of-3 where the at-most-one part is known only to the propagator.
        val s = splits.first { it.name == "exactly-one-of-3 hidden=at-most-one" }
        for (eager in listOf(false, true)) {
            val p = ClausePropagator(s.hidden, eager = eager)
            val k = solverWith(s, p)
            assertEquals(SatResult.SAT, k.solve(), "eager=$eager: 1st solve, exactly-one-of-3 is SAT")
            assertModel(k, s.all, "eager=$eager 1st solve")

            val clash = intArrayOf(1, 2)
            assertEquals(bruteForce(3, s.all, clash), k.solve(clash), "eager=$eager: 2nd solve under [1, 2] must be UNSAT (hidden -1 OR -2)")

            val ok = intArrayOf(-1, -2)
            assertEquals(SatResult.SAT, k.solve(ok), "eager=$eager: 3rd solve under [-1, -2] must be SAT")
            assertModel(k, s.all, "eager=$eager 3rd solve")
            assertTrue(k.valueOf(3), "eager=$eager: under [-1, -2] the only model has x3 = true")

            assertEquals(SatResult.SAT, k.solve(), "eager=$eager: 4th solve without assumptions is SAT again")
            assertModel(k, s.all, "eager=$eager 4th solve")
            assertNoViolations(p, "incremental eager=$eager")
        }
    }

    @Test
    fun incrementalUnsatUnderAssumptionsOnRandomSplits() {
        for (s in splits.filter { it.name.startsWith("random") || it.name.startsWith("PHP(2,2)") }) {
            val p = ClausePropagator(s.hidden, eager = true)
            val k = solverWith(s, p)
            val expected0 = bruteForce(s.numVars, s.all)
            assertEquals(expected0, k.solve(), "${s.name}: first solve")
            if (expected0 == SatResult.UNSAT) {
                assertNoViolations(p, s.name)
                continue
            }
            for (a in listOf(intArrayOf(1), intArrayOf(-1, 2), intArrayOf(1, -2, 3), intArrayOf(-3, -4))) {
                val expected = bruteForce(s.numVars, s.all, a)
                assertEquals(expected, k.solve(a), "${s.name}: solve under ${a.toList()}")
                if (expected == SatResult.SAT) {
                    assertModel(k, s.all, "${s.name} under ${a.toList()}")
                    for (lit in a) assertEquals(lit > 0, k.valueOf(abs(lit)), "${s.name}: model must satisfy assumption $lit")
                }
            }
            assertNoViolations(p, s.name)
        }
    }

    // ---------------------------------------------------------------- 9. forceBacktrack

    @Test
    fun forceBacktrackInsideCbDecideBacktracksAndNotifies() {
        // cadical.hpp force_backtrack: "Can be called only during 'cb_decide' ... If the call had
        // an effect, the External Propagator will be notified about the backtrack via
        // 'notify_backtrack'." Internal::force_backtrack acts iff new_level < level
        // (external_propagate.cpp ~208) and backtrack() calls notify_backtrack synchronously
        // (backtrack.cpp ~100). MockPropagator calls it from cb_decide as well. Checked inside
        // ClausePropagator: notifyBacktrack(target) arrives during the call and the level drops.
        var forced = 0
        for (s in splits) {
            val p = ClausePropagator(s.hidden, eager = true, forceInDecide = true)
            val k = solverWith(s, p)
            val expected = bruteForce(s.numVars, s.all)
            assertEquals(expected, k.solve(), "${s.name}: verdict with forced backtracks in cbDecide must equal F's")
            if (expected == SatResult.SAT) assertModel(k, s.all, s.name)
            assertNoViolations(p, "${s.name} (forceInDecide)")
            forced += p.forcedBacktracks
        }
        assertTrue(forced > 0, "forceBacktrack inside cbDecide was never exercised (no cbDecide on level >= 1)")
    }

    @Test
    fun forceBacktrackOutsideCbDecideHasNoEffect() {
        // cadical.hpp force_backtrack: "Invoking in any other time will not have an effect."
        // (forced_backt_allowed is only true around cb_decide, external_propagate.cpp ~995-998.)
        // ClausePropagator calls forceBacktrack(0) from cbPropagate on level >= 1 and records a
        // violation if a notifyBacktrack or level change results.
        var tries = 0
        for (s in splits) {
            val p = ClausePropagator(s.hidden, eager = true, forceInPropagate = true)
            val k = solverWith(s, p)
            val expected = bruteForce(s.numVars, s.all)
            assertEquals(expected, k.solve(), "${s.name}: verdict with no-op forceBacktrack in cbPropagate must equal F's")
            if (expected == SatResult.SAT) assertModel(k, s.all, s.name)
            assertNoViolations(p, "${s.name} (forceInPropagate)")
            tries += p.forceOutsideTries
        }
        assertTrue(tries > 0, "forceBacktrack outside cbDecide was never tried (no cbPropagate on level >= 1)")
    }

    // ---------------------------------------------------------------- 10. removeObservedVar

    /** Exactly-one-of-3 plus (4 OR 1), (-4 OR 2): models {1,-4} and {2,4}; x4 is never root-fixed. */
    private val sideDirect = listOf(intArrayOf(1, 2, 3), intArrayOf(4, 1), intArrayOf(-4, 2))
    private val amo3 = listOf(intArrayOf(-1, -2), intArrayOf(-1, -3), intArrayOf(-2, -3))
    private val sideSplit = Split("exactly-one-of-3 + x4 side clauses, hidden=at-most-one", 4, sideDirect, amo3)

    @Test
    fun removeObservedVarBetweenSolvesStopsNotificationsAndModelEntries() {
        // cadical.hpp remove_observed_var: allowed "only between solve calls". Afterwards the var
        // is unobserved: notify_assignments filters on observed() (external_propagate.cpp ~928)
        // and the cb_check_found_model model is built over external->is_observed only (~846).
        for (eager in listOf(false, true)) {
            val s = sideSplit
            val p = ClausePropagator(s.hidden, eager = eager)
            val k = solverWith(s, p)
            assertEquals(SatResult.SAT, k.solve(), "eager=$eager: 1st solve is SAT")
            assertModel(k, s.all, "eager=$eager 1st solve")

            k.removeObservedVar(4)
            p.observed.remove(4)
            p.notifiedVars.clear()
            val checksBefore = p.modelChecks
            assertEquals(SatResult.SAT, k.solve(intArrayOf(-1)), "eager=$eager: under [-1] the model {2,4} remains")
            assertModel(k, s.all, "eager=$eager 2nd solve")
            assertTrue(k.valueOf(2) && k.valueOf(4), "eager=$eager: under [-1] x2 and x4 must be true")
            assertTrue(p.modelChecks > checksBefore, "eager=$eager: cbCheckFoundModel must be called on the 2nd solve")
            assertTrue(p.lastModel!!.none { abs(it) == 4 }, "eager=$eager: removed var 4 in model ${p.lastModel!!.toList()}")
            assertTrue(4 !in p.notifiedVars, "eager=$eager: removed var 4 was still notified")
            assertNoViolations(p, "remove eager=$eager")
        }
    }

    @Test
    fun removeObservedVarDuringSolveFails() {
        // cadical.hpp remove_observed_var: "not during it [solving]"; Solver::remove_observed_var
        // has REQUIRE_VALID_STATE (solver.cpp ~1034), which rejects the SOLVING state. The call is
        // made from inside cbCheckFoundModel with assertFails; nothing is asserted about the
        // solver afterwards (upstream aborts on a failed REQUIRE).
        val p = ClausePropagator(sideSplit.hidden, eager = false, removeInsideCheck = 3)
        val k = solverWith(sideSplit, p)
        k.solve()
        assertTrue(p.removeInsideAttempted, "cbCheckFoundModel was never reached, removeObservedVar not tried")
    }

    // ---------------------------------------------------------------- 11. resetObservedVars

    @Test
    fun resetObservedVarsBetweenSolves() {
        // cadical.hpp reset_observed_vars: "Removes all the 'observed' flags". The next model is
        // built over observed vars only (external_propagate.cpp ~846), so it is empty, and no
        // assignment of a formerly observed var is notified (~928).
        for (eager in listOf(false, true)) {
            val s = sideSplit
            val p = ClausePropagator(s.hidden, eager = eager)
            val k = solverWith(s, p)
            assertEquals(SatResult.SAT, k.solve(), "eager=$eager: 1st solve is SAT")

            k.resetObservedVars()
            p.observed.clear()
            p.notifiedVars.clear()
            val checksBefore = p.modelChecks
            assertEquals(SatResult.SAT, k.solve(intArrayOf(-1)), "eager=$eager: direct clauses under [-1] are SAT")
            assertModel(k, s.direct, "eager=$eager after reset")
            assertTrue(!k.valueOf(1), "eager=$eager: model must satisfy assumption -1")
            assertTrue(p.modelChecks > checksBefore, "eager=$eager: cbCheckFoundModel must still be called (propagator connected)")
            assertTrue(p.lastModel!!.isEmpty(), "eager=$eager: model after reset must be empty, got ${p.lastModel!!.toList()}")
            assertTrue(p.notifiedVars.isEmpty(), "eager=$eager: formerly observed vars notified after reset: ${p.notifiedVars}")
            assertNoViolations(p, "reset eager=$eager")
        }
    }

    // ---------------------------------------------------------------- 12. observe inside callback

    @Test
    fun observingNewVarsInsideCbCheckFoundModelContinuesSearch() {
        // cadical.hpp cb_check_found_model: on false "the propagator should provide an external
        // clause during the next callback or introduce new observed variables during this
        // callback". add_observed_var is VALID_OR_SOLVING and unassigns an already assigned,
        // non-fixed var by backtracking (external_propagate.cpp ~23), so the CDCL loop sees an
        // incomplete assignment and continues (internal.cpp ~289). Only x1..x3 start observed;
        // hidden clauses over x4 make the propagator observe x4 on demand. x4 is never root-fixed
        // by the direct clauses plus at-most-one (models {1,-4} and {2,4}), which matters:
        // upstream accepts the model if a newly observed var stays assigned.
        val cases = listOf(
            "SAT: + (-4)" to amo3 + listOf(intArrayOf(-4)),
            "UNSAT: + (-4 OR -2), (-1 OR 4)" to amo3 + listOf(intArrayOf(-4, -2), intArrayOf(-1, 4)),
        )
        for ((name, hidden) in cases) {
            val p = ClausePropagator(hidden, eager = false, observeOnDemand = true)
            val k = Ksat(Solver.CADICAL, numVars = 4)
            for (c in sideDirect) k.addClause(c)
            k.connectExternalPropagator(p)
            p.host = k
            for (v in 1..3) {
                k.addObservedVar(v)
                p.observed.add(v)
            }
            val all = sideDirect + hidden
            val expected = bruteForce(4, all)
            assertEquals(expected, k.solve(), "$name: verdict with on-demand observed vars must equal F's")
            if (expected == SatResult.SAT) assertModel(k, all, name)
            assertTrue(p.observedOnDemand > 0, "$name: the propagator never had to observe x4")
            assertNoViolations(p, name)
        }
    }

    // ---------------------------------------------------------------- 13. forgettable clauses

    @Test
    fun forgettableExternalAndReasonClausesKeepVerdict() {
        // cb_has_external_clause(is_forgettable = true): "Forgettable clauses are allowed to be
        // removed by the SAT solver"; are_reasons_forgettable: "Reason external clauses can be
        // deleted". Deleted clauses are re-supplied on model rejection, so verdicts are F's.
        for (eager in listOf(false, true)) for (s in splits) {
            val p = ClausePropagator(s.hidden, eager = eager, forgettable = true, areReasonsForgettable = true)
            val k = solverWith(s, p)
            val expected = bruteForce(s.numVars, s.all)
            assertEquals(expected, k.solve(), "${s.name} (eager=$eager): verdict with forgettable clauses must equal F's")
            if (expected == SatResult.SAT) assertModel(k, s.all, s.name)
            assertNoViolations(p, "${s.name} (eager=$eager, forgettable)")
        }
    }

    // ---------------------------------------------------------------- 14. second propagator

    @Test
    fun connectingSecondPropagatorReplacesFirst() {
        // cadical.hpp: "Only one external propagator can be connected"; Solver::
        // connect_external_propagator disconnects a previous one first (solver.cpp ~994), and
        // "Disconnection of the external propagator resets all the observed variables".
        val s = splits.first { it.name == "exactly-one-of-3 hidden=at-most-one" }
        val p1 = ClausePropagator(s.hidden, eager = true)
        val k = solverWith(s, p1)
        assertEquals(SatResult.SAT, k.solve(), "with 1st propagator: SAT")
        assertModel(k, s.all, "1st propagator")

        val p2 = ClausePropagator(s.hidden, eager = true)
        k.connectExternalPropagator(p2)
        p2.host = k
        val p1Calls = p1.totalCallbacks

        // Observed vars were reset by the implicit disconnect: p2 has observed nothing yet.
        assertEquals(SatResult.SAT, k.solve(), "2nd propagator, nothing observed: SAT")
        assertTrue(p2.modelChecks > 0, "cbCheckFoundModel must be called on the 2nd propagator")
        assertTrue(p2.lastModel!!.isEmpty(), "observed vars must be reset on reconnect, model was ${p2.lastModel!!.toList()}")

        for (v in 1..s.numVars) {
            k.addObservedVar(v)
            p2.observed.add(v)
        }
        assertEquals(SatResult.UNSAT, k.solve(intArrayOf(1, 2)), "2nd propagator: [1, 2] violates hidden (-1 OR -2)")
        assertEquals(SatResult.SAT, k.solve(intArrayOf(-1, -2)), "2nd propagator: [-1, -2] is SAT")
        assertModel(k, s.all, "2nd propagator under [-1, -2]")
        assertEquals(p1Calls, p1.totalCallbacks, "the replaced propagator must get no further callbacks")
        assertNoViolations(p1, "1st propagator")
        assertNoViolations(p2, "2nd propagator")
    }
}

/**
 * Reusable test propagator enforcing [hidden] clauses (signed DIMACS), modeled on upstream's
 * MockPropagator (mobical.cpp): it mirrors the solver's trail of observed vars per decision
 * level, rejects models violating a hidden clause and then supplies that clause as an
 * external clause. With [eager] it also unit-propagates its clauses via cbPropagate with the
 * clause as reason. With [decide] it proposes the negation of the lowest unassigned observed
 * var as decision (as MockPropagator returns `-lit`). Only clauses whose vars are all in
 * [observed] are evaluated (upstream requires external clauses over observed vars); with
 * [observeOnDemand] a model leaving such a clause undecided makes it observe the missing vars.
 *
 * Contract violations are recorded in [violations] (not thrown, so the solver is never left
 * mid-callback); runaway callback loops throw to fail loudly instead of hanging.
 */
private class ClausePropagator(
    private val hidden: List<IntArray>,
    private val eager: Boolean,
    private val decide: Boolean = false,
    override val isLazy: Boolean = false,
    private val forgettable: Boolean = false,
    override val areReasonsForgettable: Boolean = false,
    private val forceInDecide: Boolean = false,
    private val forceInPropagate: Boolean = false,
    private val observeOnDemand: Boolean = false,
    private val removeInsideCheck: Int = 0,
) : ExternalPropagator {

    var host: ExternalPropagation? = null
    val observed = HashSet<Int>()
    val violations = ArrayList<String>()

    /** Every variable seen in any notifyAssignment, observed or not (cleared by tests). */
    val notifiedVars = HashSet<Int>()
    var lastModel: IntArray? = null
        private set

    var totalCallbacks = 0
        private set
    var modelChecks = 0
        private set
    var externalClausesAdded = 0
        private set
    var propagations = 0
        private set
    var propagateCalls = 0
        private set
    var decideCalls = 0
        private set
    var decisionsMade = 0
        private set
    var isDecisionChecks = 0
        private set
    var reasonRequests = 0
        private set
    var forcedBacktracks = 0
        private set
    var forceOutsideTries = 0
        private set
    var observedOnDemand = 0
        private set
    var removeInsideAttempted = false
        private set

    // Trail mirror: levels[l] = observed literals notified while on level l.
    private val levels = mutableListOf(mutableListOf<Int>())
    private val litOfVar = HashMap<Int, Int>()
    private val levelOfVar = HashMap<Int, Int>()
    private val currentLevel get() = levels.size - 1
    private var backtrackNotifications = 0
    private var lastBacktrackTo = -1

    // Decisions we proposed: level opened by the decision -> decided literal.
    private var pendingDecision = 0
    private val decisionAtLevel = HashMap<Int, Int>()

    // External clauses and reasons.
    private val queued = ArrayDeque<IntArray>()
    private val addedAsExternal = HashSet<List<Int>>()
    private var current: IntArray? = null
    private var currentPos = 0
    private val reasons = HashMap<Int, IntArray>()
    private var reasonLit = 0
    private var reasonPos = 0

    private fun tick() {
        if (++totalCallbacks > 200_000) throw IllegalStateException("runaway: more than 200000 propagator callbacks")
    }

    private fun violation(msg: String) {
        violations.add(msg)
    }

    private fun fullyObserved(c: IntArray) = c.all { abs(it) in observed }

    private fun mirrorValue(lit: Int): Int {
        val l = litOfVar[abs(lit)] ?: return 0
        return if (l == lit) 1 else -1
    }

    // ---------------------------------------------------------------- notifications

    override fun notifyAssignment(lits: IntArray) {
        tick()
        for (lit in lits) {
            val v = abs(lit)
            notifiedVars.add(v)
            if (v !in observed) continue
            val existing = litOfVar[v]
            if (existing != null) {
                val lvl = levelOfVar[v]!!
                // Root-level (fixed) assignments may be notified repeatedly upstream.
                if (lvl == 0 && existing == lit) continue
                violation("var $v notified as $lit on level $currentLevel but already assigned $existing on level $lvl without a backtrack below it")
                continue
            }
            litOfVar[v] = lit
            levelOfVar[v] = currentLevel
            levels.last().add(lit)
        }
    }

    override fun notifyNewDecisionLevel() {
        tick()
        levels.add(mutableListOf())
        if (pendingDecision != 0) {
            decisionAtLevel[currentLevel] = pendingDecision
            pendingDecision = 0
        }
    }

    override fun notifyBacktrack(newLevel: Int) {
        tick()
        backtrackNotifications++
        lastBacktrackTo = newLevel
        if (newLevel < 0 || newLevel > currentLevel) {
            violation("notifyBacktrack($newLevel) while on level $currentLevel")
            return
        }
        while (levels.size > newLevel + 1) {
            for (lit in levels.removeAt(levels.size - 1)) {
                litOfVar.remove(abs(lit))
                levelOfVar.remove(abs(lit))
            }
            decisionAtLevel.remove(levels.size)
        }
        pendingDecision = 0
    }

    // ---------------------------------------------------------------- model check

    override fun cbCheckFoundModel(model: IntArray): Boolean {
        tick()
        modelChecks++
        lastModel = model.copyOf()
        if (removeInsideCheck != 0 && !removeInsideAttempted) {
            removeInsideAttempted = true
            assertFails("removeObservedVar inside cbCheckFoundModel must fail (upstream REQUIRE_VALID_STATE)") {
                host!!.removeObservedVar(removeInsideCheck)
            }
        }
        val value = HashMap<Int, Int>()
        for (lit in model) value[abs(lit)] = lit
        for (v in observed) if (v !in value) violation("model passed to cbCheckFoundModel lacks observed var $v")
        if (!isLazy) {
            for ((v, lit) in litOfVar) {
                val m = value[v]
                if (v in observed && m != null && m != lit) violation("mirror has $lit but cbCheckFoundModel model has $m")
            }
        }
        val bad = hidden.firstOrNull { c -> fullyObserved(c) && c.none { lit -> value[abs(lit)] == lit } }
        if (bad != null) {
            if (!forgettable && bad.toList() in addedAsExternal) {
                violation("model violates ${bad.toList()}, already added as an irredundant external clause")
            }
            queued.addLast(bad)
            return false
        }
        if (observeOnDemand) {
            val undecided = hidden.firstOrNull { c -> !fullyObserved(c) && c.none { lit -> value[abs(lit)] == lit } }
            if (undecided != null) {
                for (lit in undecided) {
                    val v = abs(lit)
                    if (v in observed) continue
                    observed.add(v)
                    host!!.addObservedVar(v)
                    observedOnDemand++
                }
                return false
            }
        }
        return true
    }

    // ---------------------------------------------------------------- decisions

    override fun cbDecide(): Int {
        tick()
        decideCalls++
        if (isLazy) violation("cbDecide on a lazy propagator")
        if (forceInDecide && decideCalls % 3 == 0 && currentLevel >= 1 && forcedBacktracks < 5) {
            val target = currentLevel / 2
            val before = backtrackNotifications
            host!!.forceBacktrack(target)
            forcedBacktracks++
            if (backtrackNotifications == before || lastBacktrackTo != target) {
                violation("forceBacktrack($target) in cbDecide was not followed by notifyBacktrack($target)")
            }
            if (currentLevel != target) violation("after forceBacktrack($target) in cbDecide the mirror is on level $currentLevel")
            return 0
        }
        if (!decide) return 0
        val v = observed.sorted().firstOrNull { it !in litOfVar } ?: return 0
        decisionsMade++
        pendingDecision = -v
        return -v
    }

    private fun checkIsDecision() {
        val h = host ?: return
        for ((level, d) in decisionAtLevel) {
            if (level > currentLevel || d !in levels[level]) continue
            isDecisionChecks++
            if (!h.isDecision(d)) violation("isDecision($d) false for our decision on level $level")
            for (lit in levels[level]) {
                if (lit != d && h.isDecision(lit)) violation("isDecision($lit) true for a non-decision on level $level (decision was $d)")
            }
        }
    }

    // ---------------------------------------------------------------- propagation

    override fun cbPropagate(): Int {
        tick()
        propagateCalls++
        if (isLazy) violation("cbPropagate on a lazy propagator")
        if (decide) checkIsDecision()
        if (forceInPropagate && currentLevel >= 1) {
            forceOutsideTries++
            val before = backtrackNotifications
            val levelBefore = currentLevel
            host!!.forceBacktrack(0)
            if (backtrackNotifications != before || currentLevel != levelBefore) {
                violation("forceBacktrack(0) in cbPropagate had an effect (level $levelBefore -> $currentLevel)")
            }
        }
        if (!eager) return 0
        for (c in hidden) {
            if (!fullyObserved(c)) continue
            var unassigned = 0
            var free = 0
            var satisfied = false
            for (lit in c) {
                when (mirrorValue(lit)) {
                    1 -> satisfied = true
                    0 -> { free++; unassigned = lit }
                }
            }
            if (satisfied || free != 1) continue
            reasons[unassigned] = c
            propagations++
            return unassigned
        }
        return 0
    }

    override fun cbAddReasonClauseLit(propagatedLit: Int): Int {
        tick()
        val reason = reasons[propagatedLit]
        if (reason == null) {
            violation("reason asked for $propagatedLit, which was never propagated by cbPropagate")
            return 0
        }
        if (reasonLit != propagatedLit) {
            reasonLit = propagatedLit
            reasonPos = 0
            reasonRequests++
        }
        if (reasonPos < reason.size) return reason[reasonPos++]
        reasonLit = 0
        reasonPos = 0
        return 0
    }

    // ---------------------------------------------------------------- external clauses

    override fun cbHasExternalClause(isForgettable: OutBoolean): Boolean {
        tick()
        isForgettable.value = forgettable
        if (current != null) violation("cbHasExternalClause while the previous clause was not closed with 0")
        var next = queued.removeFirstOrNull()
        if (next == null && eager && !isLazy) {
            // A clause falsified under our view (assigned in one solver BCP batch): add it so
            // the solver analyzes the conflict ("Falsified clauses trigger conflict analysis").
            next = hidden.firstOrNull { c -> fullyObserved(c) && c.all { mirrorValue(it) == -1 } }
        }
        if (next == null) return false
        addedAsExternal.add(next.toList())
        externalClausesAdded++
        current = next
        currentPos = 0
        return true
    }

    override fun cbAddExternalClauseLit(): Int {
        tick()
        val c = current
        if (c == null) {
            violation("cbAddExternalClauseLit without a preceding cbHasExternalClause = true")
            return 0
        }
        if (currentPos < c.size) return c[currentPos++]
        current = null
        return 0
    }
}
