package org.bytefred.ksat.minisat

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

/**
 * [parseDimacs] (core/Dimacs.h port) on the coverage-audit inputs; the expected outcomes are those of
 * the upstream binaries (checked live in the JVM test MiniSatDimacsLiveTest).
 */
class MiniSatDimacsTest {

    private fun solve(text: String, strict: Boolean = false, out: MutableList<String> = ArrayList()): Int {
        val s = MiniSat()
        parseDimacs(text, s, strict) { out += it }
        return s.solveLimited(IntVec())
    }

    private fun error(text: String): DimacsParseError =
        assertFailsWith<DimacsParseError> { parseDimacs(text, MiniSat(), false) { } }

    @Test
    fun clausesBeyondTheHeaderAreRead() {
        assertEquals(L_FALSE, solve("p cnf 1 1\n1 0\n-1 0\n"))
        val out = ArrayList<String>()
        assertEquals(L_FALSE, solve("p cnf 1 1\n1 0\n-1 0\n", strict = true, out = out))
        assertEquals(listOf("PARSE ERROR! DIMACS header mismatch: wrong number of clauses"), out)
    }

    @Test
    fun acceptedVariants() {
        assertEquals(L_TRUE, solve("p cnf 2 1\n1 2 0 c a comment\n"))
        assertEquals(L_TRUE, solve("1 -2 0\n2 0\n"))
        assertEquals(L_TRUE, solve(""))
        assertEquals(L_FALSE, solve("p cnf 3\n1 0\n"))   // the 1 is read as the clause count, then the empty clause 0
        val s = MiniSat()
        parseDimacs("p cnf 1 1\n5 -3 0\n", s)
        assertEquals(5, s.nVars())
    }

    @Test
    fun parseErrors() {
        error("p cnf 2 1\n1 2\n").let { assertEquals("PARSE ERROR! Unexpected char: ÿ", it.message); assertEquals(true, it.toStderr) }
        error("p wcnf 1 1\n1 0\n").let { assertEquals("PARSE ERROR! Unexpected char: w", it.message); assertEquals(false, it.toStderr) }
        error("p  cnf 1 1\n1 0\n").let { assertEquals("PARSE ERROR! Unexpected char:  ", it.message); assertEquals(false, it.toStderr) }
        error("p cnf 2 1\n1 2 0\n%\n0\n").let { assertEquals("PARSE ERROR! Unexpected char: %", it.message); assertEquals(true, it.toStderr) }
        error("p cnf 2 1\n1 c x\n2 0\n").let { assertEquals("PARSE ERROR! Unexpected char: c", it.message) }
    }
}
