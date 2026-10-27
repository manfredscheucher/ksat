package org.bytefred.ksat.minisat

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * `interrupt()` from another thread stops a running `solveLimited` (l_Undef), and the solver can
 * go on afterwards (clearInterrupt + a budgeted solve). Relies on [MiniSat]'s asynchInterrupt being
 * @Volatile (port addition; upstream's plain bool).
 */
class MiniSatInterruptTest {

    /** PHP(holes+1, holes): far too hard to finish within the test. */
    private fun php(s: MiniSat, holes: Int) {
        val pigeons = holes + 1
        fun x(p: Int, h: Int) = mkLit(p * holes + h)
        while (s.nVars() < pigeons * holes) s.newVar()
        for (p in 0 until pigeons) {
            val c = IntVec()
            for (h in 0 until holes) c.push(x(p, h))
            s.addClause(c)
        }
        for (h in 0 until holes) for (p in 0 until pigeons) for (q in p + 1 until pigeons)
            s.addClause(litNeg(x(p, h)), litNeg(x(q, h)))
    }

    @Test
    fun interruptFromAnotherThreadStopsTheSearch() {
        for (s in listOf(MiniSat(), MiniSatSimp())) {
            php(s, 12)
            var ret = -1
            val t = Thread { ret = s.solveLimited(IntVec()) }
            t.start()
            Thread.sleep(300)
            assertTrue(t.isAlive, "${s::class.simpleName}: PHP(13,12) finished within 300 ms")
            s.interrupt()
            t.join(10_000)
            if (t.isAlive) fail("${s::class.simpleName}: interrupt() from another thread was not seen within 10 s")
            assertEquals(L_UNDEF, ret, "${s::class.simpleName}: result after interrupt")
            s.clearInterrupt()
            s.setConfBudget(10)
            assertEquals(L_UNDEF, s.solveLimited(IntVec()), "${s::class.simpleName}: budgeted solve after clearInterrupt")
        }
    }
}
