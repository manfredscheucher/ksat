package org.bytefred.ksat.minisat

import org.junit.AssumptionViolatedException
import java.io.File
import kotlin.test.Test
import kotlin.test.fail

/**
 * [parseDimacs] (port of core/Dimacs.h + utils/ParseUtils.h) against the reference binaries on
 * crafted, partly malformed CNFs (the coverage-audit cases and more): the complete stdout (trace,
 * MODEL, `PARSE ERROR!` lines printed to stdout, the `s ...` verdict), the exit code (3 for a parse
 * error) and a `PARSE ERROR!` line on stderr must agree. --simp=0/1, --strict=0/1, master default
 * (ksat-extra/shadow/minisat-master) and csbCompat (minisat-full). The CNFs exist only as temp
 * files during the test. SKIPPED (visibly) when ksat-extra or a reference binary is missing.
 */
class MiniSatDimacsLiveTest {

    private fun skip(reason: String): Nothing {
        System.err.println("$TAG SKIPPED: $reason")
        throw AssumptionViolatedException(reason)
    }

    @Test
    fun parserMatchesMasterLive() = compare("minisat-master", "minisat_master_trace", csb = false)

    @Test
    fun parserMatchesCsbLive() = compare("minisat-full", "minisat_full_trace", csb = true)

    private fun compare(refDir: String, binName: String, csb: Boolean) {
        val shadow = MiniSatShadowDriver.locateShadowDir() ?: skip("no ksat-extra/shadow found")
        val bin = File(shadow, "$refDir/build/$binName")
        if (!bin.canExecute())
            skip("reference not built: run `bash ${File(shadow, "$refDir/build_and_trace.sh")} --build-only`")
        val failures = ArrayList<String>()
        var n = 0
        val seen = HashMap<String, Int>()   // case name -> exit code (simp=0, strict=0), for the summary
        for ((name, bytes) in CASES) {
            val cnf = File.createTempFile("minisat-dimacs-", ".cnf")
            try {
                cnf.writeBytes(bytes)
                for (simp in 0..1) for (strict in 0..1) {
                    n++
                    val label = "[$refDir $name simp=$simp strict=$strict]"
                    var ktExit = -1
                    var ktErr: String? = null
                    val cmd = listOf(bin.path, "--simp=$simp", "--strict=$strict", cnf.path)
                    val r = LiveCompare.run(cmd, label, { it.isNotEmpty() }) { sink ->
                        var result: String? = null
                        val emit: (String) -> Unit = { if (it.startsWith("RESULT ")) result = it; sink(it) }
                        try {
                            MiniSatShadowDriver.run(emit, simp, emptyList(), cnf, null, TAG, csb = csb, strict = strict == 1)
                            ktExit = when (result) { "RESULT SAT" -> 10; "RESULT UNSAT" -> 20; else -> 0 }
                            sink(when (ktExit) { 10 -> "s SATISFIABLE"; 20 -> "s UNSATISFIABLE"; else -> "s UNKNOWN" })
                        } catch (e: DimacsParseError) {
                            ktExit = 3
                            if (e.toStderr) ktErr = e.message else sink(e.message!!)
                        }
                    }
                    if (simp == 0 && strict == 0) seen[name] = r.exitCode
                    val upErr = r.stderr.lineSequence().firstOrNull { it.startsWith("PARSE ERROR!") }
                    when {
                        r.diff != null -> failures += r.diff
                        r.exitCode != ktExit -> failures += "$label exit code: upstream ${r.exitCode}, kotlin $ktExit\n${r.stderr}"
                        upErr != ktErr -> failures += "$label stderr: upstream '$upErr', kotlin '$ktErr'"
                    }
                }
            } finally {
                cnf.delete()
            }
        }
        println("$TAG [$refDir] compared $n runs, ${failures.size} failing; upstream exit codes: $seen")
        if (failures.isNotEmpty()) fail("$TAG ${failures.size} mismatches:\n" + failures.take(10).joinToString("\n"))
    }

    private companion object {
        const val TAG = "[dimacs-live-minisat]"
        private fun b(s: String) = s.toByteArray(Charsets.ISO_8859_1)
        val CASES: List<Pair<String, ByteArray>> = listOf(
            "more_clauses_than_header" to b("p cnf 1 1\n1 0\n-1 0\n"),
            "fewer_clauses_than_header" to b("p cnf 3 5\n1 -2 0\n2 3 0\n"),
            "missing_final_zero" to b("p cnf 2 1\n1 2\n"),
            "missing_final_zero_nl" to b("p cnf 2 2\n1 0\n1 2"),
            "p_wcnf" to b("p wcnf 1 1\n1 0\n"),
            "p_two_spaces" to b("p  cnf 1 1\n1 0\n"),
            "p_tab" to b("p\tcnf 1 1\n1 0\n"),
            "p_cnf_no_space" to b("p cnf3 1\n1 0\n"),
            "p_missing_count" to b("p cnf 3\n1 0\n"),
            "p_trailing_token" to b("p cnf 3 1 x\n1 0\n"),
            "percent_tail" to b("p cnf 2 1\n1 2 0\n%\n0\n"),
            "comment_after_clause" to b("p cnf 2 1\n1 2 0 c a comment\n-1 0\n"),
            "comment_inside_clause" to b("p cnf 2 1\n1 c x\n2 0\n"),
            "comment_lines" to b("c first\nc second\np cnf 2 2\nc mid\n1 2 0\n  c indented\n-2 0\nc end"),
            "no_header" to b("1 -2 0\n2 0\n"),
            "header_after_clauses" to b("1 0\np cnf 1 2\n-1 0\n"),
            "var_beyond_header" to b("p cnf 1 1\n5 -3 0\n"),
            "plus_sign" to b("p cnf 2 1\n+1 -2 0\n"),
            "minus_zero" to b("p cnf 2 1\n1 2 -0\n-1 0\n"),
            "empty_clause" to b("p cnf 1 1\n0\n"),
            "empty_input" to b(""),
            "only_whitespace" to b(" \n\t\n"),
            "crlf" to b("p cnf 2 2\r\n1 0\r\n-1 2 0\r\n"),
            "vtab_formfeed" to b("p cnf 2 1\n1\u000b2\u000c0\n"),
            "clauses_on_one_line" to b("p cnf 3 3 1 2 0 -1 0 -2 3 0"),
            "dangling_minus" to b("p cnf 2 1\n1 - 2 0\n"),
            "non_ascii" to b("p cnf 2 1\n1 ä 0\n"),
            "letter_in_number" to b("p cnf 2 1\n12x 0\n"),
            "glued_literals" to b("p cnf 3 1\n1-2 0\n"),
            "big_var" to b("p cnf 1 1\n70 0\n"),
        )
    }
}
