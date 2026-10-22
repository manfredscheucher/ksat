package org.bytefred.ksat.cadical.full

import org.junit.Assume.assumeTrue
import java.io.BufferedInputStream
import java.io.File
import java.util.concurrent.TimeUnit
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * Proof output and proof checkers of the FULL CaDiCaL 2.1.3 port (JVM only) against the real
 * upstream solver (ksat-extra/shadow/cadical-full, driver option `--proof=-`).
 *
 * [proofBytesMatchUpstream]: for every CNF in [CNFS] and every proof format in [FORMATS], the C
 * driver is run as `cadical_full_trace --quiet=1 --<option>=<value> ... --proof=- <cnf>` (upstream
 * default configuration plus 'quiet' so no 'c' messages go to stdout, LSTRACE unset) and its stdout (the proof bytes followed by the `s ...` line) is
 * compared byte by byte, streamed, with the port run through [runShadow] with the same options
 * and a [FileSink] that reads the C stream as it writes. Nothing is stored; on a mismatch the
 * byte offset and the next bytes of both sides are reported.
 *
 * [checkersAcceptProofs]: the same CNFs with `check=1` and `checkproof` 1 (DRUP [Checker]),
 * 2 ([LratChecker]) and 3 (both), and `externallrat=1` ([LratBuilder]) with `checkproof=3`;
 * the port must not report an error (the checkers throw), must give the upstream verdict and
 * the checkers must have checked derived clauses. The LRAT proof written alongside is compared
 * with the C driver as above.
 *
 * Skips visibly when ksat-extra or the C driver binary is missing (build it with
 * `bash ksat-extra/shadow/cadical-full/build_and_trace.sh --build-only`).
 */
class FullProofTest {

    private fun locateShadowDir(): File? {
        var dir: File? = File(System.getProperty("user.dir")).absoluteFile
        while (dir != null) {
            val candidate = File(dir, "ksat-extra/shadow")
            if (candidate.isDirectory) return candidate
            dir = dir.parentFile
        }
        return null
    }

    private class Setup(val binary: File, val cnfs: List<File>)

    private fun setup(): Setup {
        val shadow = locateShadowDir()
        if (shadow == null) System.err.println("FullProofTest SKIPPED: ksat-extra/shadow not found")
        assumeTrue("ksat-extra/shadow not found", shadow != null)
        val binary = File(shadow!!, "cadical-full/build/cadical_full_trace")
        if (!binary.canExecute())
            System.err.println("FullProofTest SKIPPED: C driver $binary missing (build_and_trace.sh --build-only)")
        assumeTrue("C driver $binary missing", binary.canExecute())
        val cnfs = CNFS.map { File(shadow, it) }
        for (f in cnfs) check(f.isFile) { "missing CNF $f" }
        return Setup(binary, cnfs)
    }

    /** Thrown from the comparing sink at the first differing byte. */
    private class Mismatch(msg: String) : RuntimeException(msg)

    /**
     * A [FileSink] comparing every byte the port writes with the next byte of [c] (the C
     * driver's stdout). [offset] counts compared bytes.
     */
    private class ComparingSink(private val c: BufferedInputStream) : FileSink {
        var offset = 0L
        val recent = ArrayDeque<Int>()

        override fun put(b: Int) {
            val expected = c.read()
            if (expected != b) {
                val more = StringBuilder()
                for (k in 0 until 16) {
                    val x = c.read()
                    if (x < 0) break
                    more.append(hex(x)).append(' ')
                }
                throw Mismatch(
                    "byte $offset: C ${if (expected < 0) "EOF" else hex(expected)} (then $more) " +
                        "vs port ${hex(b)}; previous bytes ${recent.joinToString(" ") { hex(it) }}",
                )
            }
            recent.addLast(b)
            if (recent.size > 32) recent.removeFirst()
            offset++
        }

        fun putAll(s: String) {
            for (ch in s) put(ch.code)
        }

        companion object {
            fun hex(x: Int) = x.toString(16).padStart(2, '0')
        }
    }

    private fun statusLine(res: Int) = when (res) {
        10 -> "s SATISFIABLE\n"
        20 -> "s UNSATISFIABLE\n"
        else -> "s UNKNOWN\n"
    }

    /**
     * Runs C and the port with [options] and an upstream proof to stdout, compares the bytes.
     * Returns null on success, else a failure description.
     */
    private fun compareProof(binary: File, cnf: File, proofOptions: List<Pair<String, Int>>): String? {
        // 'quiet=1': upstream otherwise prints 'c ...' messages to the same stdout.
        val options = listOf("quiet" to 1) + proofOptions
        val args = ArrayList<String>()
        args.add(binary.path)
        for ((n, v) in options) args.add("--$n=$v")
        args.add("--proof=-")
        args.add(cnf.path)
        val proc = ProcessBuilder(args).redirectError(ProcessBuilder.Redirect.INHERIT).start()
        val c = BufferedInputStream(proc.inputStream, 1 shl 16)
        val sink = ComparingSink(c)
        try {
            val res = runShadow(cnf.readText(), null, options, null, sink = {}, proofOut = sink, lstrace = false)
            sink.putAll(statusLine(res))
            val rest = c.read()
            if (rest >= 0) return "port ended after ${sink.offset} bytes, C has more (next ${ComparingSink.hex(rest)})"
            if (!proc.waitFor(30, TimeUnit.SECONDS)) return "C driver did not exit"
            if (proc.exitValue() != res) return "C exit ${proc.exitValue()} vs port $res"
            return null
        } catch (e: Mismatch) {
            return e.message
        } catch (e: Exception) {
            return "port threw after ${sink.offset} bytes: $e"
        } finally {
            proc.destroy()
        }
    }

    @Test
    fun proofBytesMatchUpstream() {
        val s = setup()
        val failures = ArrayList<String>()
        for (cnf in s.cnfs) {
            for ((format, options) in FORMATS) {
                val t0 = System.nanoTime()
                val failure = compareProof(s.binary, cnf, options)
                val ms = (System.nanoTime() - t0) / 1_000_000
                val tag = "${cnf.name} $format"
                if (failure == null) println("PROOF OK   $tag (${ms} ms)")
                else {
                    println("PROOF FAIL $tag: $failure")
                    failures.add("$tag: $failure")
                }
            }
        }
        if (failures.isNotEmpty()) fail("${failures.size} proof mismatches:\n" + failures.joinToString("\n"))
    }

    @Test
    fun checkersAcceptProofs() {
        val s = setup()
        val failures = ArrayList<String>()
        for (cnf in s.cnfs) {
            for ((label, extra) in CHECK_RUNS) {
                val tag = "${cnf.name} $label"
                // 1. The port alone through the Solver API, to inspect the connected checkers.
                val solver = Solver()
                for ((n, v) in extra) assertTrue(solver.setLongOption("--$n=$v"), "option $n")
                val vars = IntRef(0)
                assertEquals(null, solver.readDimacs(cnf.readText(), "<cnf>", vars, 1))
                val res = try {
                    solver.solve()
                } catch (e: IllegalStateException) {
                    failures.add("$tag: checker error: ${e.message}")
                    println("CHECK FAIL $tag: ${e.message}")
                    continue
                }
                val checkers = solver.internal.statTracers
                val wantDrup = extra.contains("checkproof" to 1) || extra.contains("checkproof" to 3)
                val wantLrat = extra.any { it.first == "checkproof" && it.second > 1 }
                val drup = checkers.filterIsInstance<Checker>().singleOrNull()
                val lrat = checkers.filterIsInstance<LratChecker>().singleOrNull()
                val builder = solver.internal.lratbuilder
                val problems = ArrayList<String>()
                if (wantDrup != (drup != null)) problems.add("DRUP checker connected=${drup != null}")
                if (wantLrat != (lrat != null)) problems.add("LRAT checker connected=${lrat != null}")
                if (extra.contains("externallrat" to 1) && builder == null) problems.add("no LratBuilder")
                // The DRUP checker stops at the first inconsistency (unsat_small: the original
                // clauses already propagate to a conflict), so only require it to have seen clauses.
                if (drup != null && drup.stats.added == 0L) problems.add("DRUP checker saw no clause")
                if (lrat != null && lrat.stats.derived == 0L) problems.add("LRAT checker saw no derived clause")
                if (builder != null && builder.stats.derived == 0L) problems.add("LratBuilder built no chain")
                // 2. Same options plus an ASCII LRAT proof, compared byte by byte with C (also
                // checks the verdict against upstream).
                val failure = compareProof(s.binary, cnf, extra + listOf("lrat" to 1, "binary" to 0))
                if (failure != null) problems.add("proof vs C: $failure")
                val stats = "drup=${drup?.stats?.added}/${drup?.stats?.checks} lrat=${lrat?.stats?.checks} builder=${builder?.stats?.checks}"
                if (problems.isEmpty()) println("CHECK OK   $tag res=$res ($stats)")
                else {
                    println("CHECK FAIL $tag: ${problems.joinToString("; ")}")
                    failures.add("$tag: ${problems.joinToString("; ")}")
                }
            }
        }
        if (failures.isNotEmpty()) fail("${failures.size} checker failures:\n" + failures.joinToString("\n"))
    }

    private companion object {
        val CNFS = listOf(
            "cnf/php_5_4.cnf",
            "cnf/php_6_5.cnf",
            "cnf/hard_rand_unsat_60.cnf",
            "cnf/unsat_small.cnf",
            "cnf-full/transred_parity40.cnf",
            "cnf-full/lucky_horn.cnf",
        )

        // Upstream options per format ('binary' defaults to 1).
        val FORMATS: List<Pair<String, List<Pair<String, Int>>>> = listOf(
            "drat-ascii" to listOf("binary" to 0),
            "drat-binary" to listOf("binary" to 1),
            "lrat-ascii" to listOf("lrat" to 1, "binary" to 0),
            "lrat-binary" to listOf("lrat" to 1, "binary" to 1),
            "frat1-ascii" to listOf("frat" to 1, "binary" to 0),
            "frat1-binary" to listOf("frat" to 1, "binary" to 1),
            "frat2-binary" to listOf("frat" to 2, "binary" to 1),
            "veripb1" to listOf("veripb" to 1),
            "veripb2" to listOf("veripb" to 2),
            "veripb3" to listOf("veripb" to 3),
            "veripb4" to listOf("veripb" to 4),
            "idrup-ascii" to listOf("idrup" to 1, "binary" to 0),
            "idrup-binary" to listOf("idrup" to 1, "binary" to 1),
            "lidrup-ascii" to listOf("lidrup" to 1, "binary" to 0),
            "lidrup-binary" to listOf("lidrup" to 1, "binary" to 1),
            "lrat-externallrat" to listOf("externallrat" to 1, "lrat" to 1, "binary" to 0),
        )

        val CHECK_RUNS: List<Pair<String, List<Pair<String, Int>>>> = listOf(
            "checkproof=1" to listOf("check" to 1, "checkproof" to 1),
            "checkproof=2" to listOf("check" to 1, "checkproof" to 2),
            "checkproof=3" to listOf("check" to 1, "checkproof" to 3),
            "externallrat+checkproof=3" to listOf("check" to 1, "checkproof" to 3, "externallrat" to 1),
        )
    }
}
