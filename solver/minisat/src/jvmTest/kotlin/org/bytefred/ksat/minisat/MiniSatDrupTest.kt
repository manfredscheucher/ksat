package org.bytefred.ksat.minisat

import org.junit.AssumptionViolatedException
import java.io.BufferedInputStream
import java.io.File
import java.io.InputStream
import java.util.concurrent.TimeUnit
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.fail

/**
 * Live comparison (JVM only) of the master features of the port (DRUP/DRAT proof output, option
 * rdb-at, show_info counters) against the instrumented meelgroup/minisat master reference
 * (ksat-extra/shadow/minisat-master: master 664490d + fixes.patch + trace.patch + driver.cpp with
 * -DMASTER_FIXES; binary proof build `minisat_master_trace`, ASCII proof build
 * `minisat_master_trace_ascii`). Nothing is written to disk: the reference output is read from its
 * stdout and compared while the port runs. [upstreamBugsReproduceAndAreFixed] runs the raw master
 * builds (`minisat_master_raw_trace*`) to show each fixed upstream bug.
 *
 * - [proofsMatchMaster]: proof bytes (binary and ASCII) of the port vs. the reference `--drup=1`,
 *   byte for byte, incl. the binary 2 MB buffer semantics (what is flushed when) and the final
 *   empty clause written by the driver (simp/Main.cc).
 * - [tracesMatchMasterRdbAt]: LSTRACE traces (L1, line by line) with rdb-at / show-info, core,
 *   and SimpSolver with proof generation on (`--drup=devnull` / a discarding sink), plus the
 *   number of reduceDB calls counted by show_info.
 * - [unsatProofsVerifyWithDratTrim]: only when env DRAT_TRIM points to a drat-trim binary: the
 *   port's proofs of the UNSAT cases are piped into `drat-trim <cnf> /dev/stdin` and must verify.
 *
 * SKIPPED (visibly) when ksat-extra or the reference is missing (build it with
 * `bash ksat-extra/shadow/minisat-master/build_and_trace.sh --build-only`). php_9_8 only with
 * -Dbigtrace (php_10_9 never). Traces compare the first [QUICK_MAX_LINES] lines unless
 * env LIVESHADOW_FULL=1.
 */
class MiniSatDrupTest {

    private fun skip(reason: String): Nothing {
        System.err.println("$TAG SKIPPED: $reason")
        throw AssumptionViolatedException(reason)
    }

    private class Setup(val shadow: File, val binBin: File, val binAscii: File, val cases: List<Pair<File, File?>>)

    private fun setup(withAssume: Boolean): Setup {
        val shadow = MiniSatShadowDriver.locateShadowDir() ?: skip("no ksat-extra/shadow found")
        val binBin = File(shadow, "minisat-master/build/minisat_master_trace")
        val binAscii = File(shadow, "minisat-master/build/minisat_master_trace_ascii")
        if (!binBin.canExecute() || !binAscii.canExecute())
            skip("reference not built: run `bash ${File(shadow, "minisat-master/build_and_trace.sh")} --build-only`")
        val big = System.getProperty("bigtrace")?.lowercase()?.let { it !in setOf("false", "0", "no", "off") } ?: false
        val cases = ArrayList<Pair<File, File?>>()
        for (dir in if (withAssume) listOf("cnf", "cnf-full", "cnf-assume") else listOf("cnf", "cnf-full")) {
            val cnfs = File(shadow, dir).listFiles { f -> f.name.endsWith(".cnf") }?.sortedBy { it.name }
                ?: fail("$TAG missing ${File(shadow, dir)}")
            for (cnf in cnfs) {
                val name = cnf.nameWithoutExtension
                if (name == "php_10_9" || (name == "php_9_8" && !big)) continue
                cases += cnf to File(cnf.parentFile, "$name.assume").takeIf { it.isFile }
            }
        }
        return Setup(shadow, binBin, binAscii, cases)
    }

    private fun start(bin: File, args: List<String>, lstrace: Boolean, errFile: File): Process {
        val pb = ProcessBuilder(listOf(bin.path) + args).redirectError(ProcessBuilder.Redirect.to(errFile))
        if (lstrace) pb.environment()["LSTRACE"] = "1" else pb.environment().remove("LSTRACE")
        return pb.start()
    }

    private fun finish(proc: Process, label: String, errFile: File, checkExit: Boolean) {
        proc.destroy()
        if (!proc.waitFor(60, TimeUnit.SECONDS)) { proc.destroyForcibly(); fail("$TAG reference hung: $label") }
        if (checkExit && proc.exitValue() !in setOf(0, 10, 20))
            fail("$TAG reference failed (${proc.exitValue()}): $label\n${errFile.readText()}")
    }

    /** Thrown from a sink to stop the port at the first difference. */
    private class Stop : RuntimeException()

    /** A [DrupFile] that compares every written byte with the next byte of [ref]. */
    private class ComparingDrupFile(private val ref: InputStream) : DrupFile {
        var offset = 0L
        var diff: String? = null
        private val recent = ArrayDeque<Byte>()

        override fun write(buf: ByteArray, off: Int, len: Int) {
            for (k in off until off + len) {
                val r = ref.read()
                if (r != (buf[k].toInt() and 0xff)) {
                    val ahead = ArrayList<Int>()
                    while (ahead.size < 24) ahead += ref.read().takeIf { it >= 0 } ?: break
                    diff = "first diff at byte $offset: up=${if (r < 0) "<end>" else hex(r)} kt=${hex(buf[k].toInt())}\n" +
                        "    before: ${recent.joinToString(" ") { hex(it.toInt()) }}\n" +
                        "    up>   ${ahead.joinToString(" ") { hex(it) }}\n" +
                        "    kt>   ${(k + 1 until minOf(off + len, k + 25)).joinToString(" ") { hex(buf[it].toInt()) }}"
                    throw Stop()
                }
                recent.addLast(buf[k]); if (recent.size > 24) recent.removeFirst()
                offset++
            }
        }

        private fun hex(b: Int) = (b and 0xff).toString(16).padStart(2, '0')
    }

    @Test
    fun proofsMatchMaster() {
        val st = setup(withAssume = false)
        val errFile = File.createTempFile("minisat-drup", ".err").apply { deleteOnExit() }
        val failures = ArrayList<String>()
        var n = 0
        var bytes = 0L
        var nonTrivial = 0
        for ((cnf, assume) in st.cases) for (simp in 0..1) for (opts in PROOF_OPTION_SETS) for (binary in listOf(true, false)) {
            if (simp == 0 && opts.any { it.substringBefore('=').removePrefix("--") in SIMP_OPTIONS }) continue
            // rdb-at=7 on the cnf-full instances: proofs of several GB (minutes), so only shadow/cnf.
            if (opts.any { it.startsWith("--rdb-at=") } && cnf.parentFile.name != "cnf") continue
            n++
            val label = "[${cnf.name} simp=$simp $opts ${if (binary) "binary" else "ascii"}]"
            val args = listOf("--simp=$simp", "--drup=1") + opts + listOfNotNull(cnf.path, assume?.path)
            val proc = start(if (binary) st.binBin else st.binAscii, args, lstrace = false, errFile = errFile)
            val ref = BufferedInputStream(proc.inputStream, 1 shl 16)
            val sink = ComparingDrupFile(ref)
            try {
                MiniSatShadowDriver.run(null, simp, opts, cnf, assume, TAG, drup = sink, binary = binary)
            } catch (_: Stop) {
            } catch (e: Throwable) {
                sink.diff = "EXCEPTION after ${sink.offset} bytes: $e\n    " + e.stackTrace.take(8).joinToString("\n    ")
            }
            if (sink.diff == null) {
                val extra = ref.read()
                if (extra >= 0) sink.diff = "kotlin proof ends at byte ${sink.offset}, upstream has more"
            }
            finish(proc, label, errFile, checkExit = sink.diff == null)
            bytes += sink.offset
            if (sink.offset > 2) nonTrivial++
            if (sink.diff != null) failures += "$label ${sink.diff}"
        }
        println("$TAG proofs: compared $n runs, $bytes proof bytes ($nonTrivial runs with more than the final clause), ${failures.size} failing")
        if (failures.isNotEmpty()) fail("$TAG ${failures.size} proof mismatches:\n" + failures.take(10).joinToString("\n"))
    }

    @Test
    fun tracesMatchMasterRdbAt() {
        val st = setup(withAssume = true)
        val full = System.getenv("LIVESHADOW_FULL")?.let { it !in setOf("", "0", "false", "no", "off") } ?: false
        val errFile = File.createTempFile("minisat-drup-trace", ".err").apply { deleteOnExit() }
        val failures = ArrayList<String>()
        var n = 0
        for ((cnf, assume) in st.cases) for (simp in 0..1) for (opts in TRACE_OPTION_SETS) {
            // SimpSolver with proof generation on (proof code paths active; the search does not
            // depend on it), the core solver without.
            if (simp == 0 && opts.any { it.substringBefore('=').removePrefix("--") in SIMP_OPTIONS }) continue
            val drupArg = if (simp == 1) listOf("--drup=devnull") else emptyList()
            n++
            val label = "[${cnf.name} simp=$simp $drupArg $opts]"
            val args = listOf("--simp=$simp") + drupArg + opts + listOfNotNull(cnf.path, assume?.path)
            val proc = start(st.binBin, args, lstrace = true, errFile = errFile)
            val ref = proc.inputStream.bufferedReader()
            var refReduceInfo = 0
            fun nextRef(): String? {
                while (true) {
                    val l = ref.readLine() ?: return null
                    if (l.startsWith("c [reduceDB]")) { refReduceInfo++; continue }
                    if (l.isNotEmpty() && !l.startsWith("s ")) return l
                }
            }
            var lineNo = 0
            var diff: String? = null
            var truncated = false
            val ring = ArrayDeque<String>()
            val sink: (String) -> Unit = sink@{ line ->
                if (truncated || diff != null) return@sink
                val g = nextRef()
                lineNo++
                if (g != line) {
                    diff = "first diff at line $lineNo\n" + ring.joinToString("") { "    = $it\n" } + "  up> $g\n  kt> $line"
                    throw Stop()
                }
                ring.addLast(line); if (ring.size > CONTEXT) ring.removeFirst()
                if (!full && lineNo >= QUICK_MAX_LINES) { truncated = true; throw Stop() }
            }
            val discard = DrupFile { _, _, _ -> }
            var s: MiniSat? = null
            try {
                s = MiniSatShadowDriver.run(sink, simp, opts, cnf, assume, TAG, drup = if (simp == 1) discard else null)
            } catch (_: Stop) {
            } catch (e: Throwable) {
                diff = "EXCEPTION after line $lineNo: $e\n    " + e.stackTrace.take(8).joinToString("\n    ")
            }
            if (diff == null && !truncated) {
                val g = nextRef()
                if (g != null) diff = "kotlin trace ends at line $lineNo, upstream continues: $g"
                // show_info: the reference prints one "c [reduceDB]" line per counted call.
                else if (s != null && s.reduceDBCall != refReduceInfo.toLong())
                    diff = "reduceDB_call ${s.reduceDBCall} vs upstream ${refReduceInfo} 'c [reduceDB]' lines"
            }
            finish(proc, label, errFile, checkExit = diff == null && !truncated)
            if (diff != null) failures += "$label $diff"
        }
        println("$TAG traces: compared $n runs (${if (full) "full" else "first $QUICK_MAX_LINES lines each"}), ${failures.size} failing")
        if (failures.isNotEmpty()) fail("$TAG ${failures.size} trace mismatches:\n" + failures.take(10).joinToString("\n"))
    }

    /** Runs [bin] without LSTRACE, returns (exit code, stdout bytes). */
    private fun runRef(bin: File, args: List<String>): Pair<Int, ByteArray> {
        val pb = ProcessBuilder(listOf(bin.path) + args).redirectError(ProcessBuilder.Redirect.DISCARD)
        pb.environment().remove("LSTRACE")
        val proc = pb.start()
        val out = proc.inputStream.readBytes()
        if (!proc.waitFor(60, TimeUnit.SECONDS)) { proc.destroyForcibly(); fail("$TAG reference hung: $bin $args") }
        return proc.exitValue() to out
    }

    /** Signed DIMACS ASCII proof lines -> master's binary encoding (binDRUP / byteDRUP). */
    private fun encodeBinary(ascii: String): List<Byte> {
        val out = java.io.ByteArrayOutputStream()
        for (line in ascii.lines().filter { it.isNotBlank() }) {
            val toks = line.trim().split(' ')
            val del = toks[0] == "d"
            out.write((if (del) 'd' else 'a').code)
            for (t in toks.drop(if (del) 1 else 0)) {
                val l = t.toInt()
                if (l == 0) continue
                var u = 2L * kotlin.math.abs(l) + (if (l < 0) 1 else 0)
                do {
                    out.write(((u and 0x7f) or (if (u ushr 7 != 0L) 0x80 else 0)).toInt())
                    u = u ushr 7
                } while (u != 0L)
            }
            out.write(0)
        }
        return out.toByteArray().toList()
    }

    /**
     * The upstream bugs fixed in the port (minisat-full-port.md, bug list), each shown on raw
     * master and checked fixed in the fixed reference and in the port.
     */
    @Test
    fun upstreamBugsReproduceAndAreFixed() {
        val st = setup(withAssume = false)
        val raw = File(st.shadow, "minisat-master/build/minisat_master_raw_trace")
        val rawAscii = File(st.shadow, "minisat-master/build/minisat_master_raw_trace_ascii")
        if (!raw.canExecute() || !rawAscii.canExecute()) skip("raw master builds missing (build_and_trace.sh --build-only)")
        val php54 = File(st.shadow, "cnf/php_5_4.cnf")
        val php32 = File(st.shadow, "cnf/php_3_2.cnf")
        val php76 = File(st.shadow, "cnf/php_7_6.cnf")

        // FIX 1: trim proof lines without a proof file. Raw ASCII build: SIGSEGV (fprintf to NULL).
        assertEquals(139, runRef(rawAscii, listOf("--simp=0", php54.path)).first, "$TAG FIX 1 repro")
        assertEquals(20, runRef(st.binAscii, listOf("--simp=0", php54.path)).first, "$TAG FIX 1 fixed reference")
        val s1 = MiniSatShadowDriver.run(null, 0, emptyList(), php54, null, TAG, binary = false)
        assertEquals(false, s1.okay(), "$TAG FIX 1: port (UNSAT, no proof sink)")

        // FIX 2: rdb-at without show_info: raw master runs reduceDB before every decision once
        // conflicts >= k (more REDUCE than CONFLICT events); fixed = raw master with show_info.
        fun countEvents(bin: File, opts: List<String>): Pair<Int, Int> {
            val pb = ProcessBuilder(listOf(bin.path, "--simp=0") + opts + php76.path).redirectError(ProcessBuilder.Redirect.DISCARD)
            pb.environment()["LSTRACE"] = "1"
            val proc = pb.start()
            var reduce = 0
            var confl = 0
            proc.inputStream.bufferedReader().forEachLine { if (it == "REDUCE") reduce++ else if (it == "CONFLICT") confl++ }
            if (!proc.waitFor(60, TimeUnit.SECONDS)) { proc.destroyForcibly(); fail("$TAG reference hung: $bin") }
            return reduce to confl
        }
        val (rawReduce, rawConfl) = countEvents(raw, listOf("--rdb-at=7"))
        if (rawReduce <= rawConfl) fail("$TAG FIX 2 repro: raw master REDUCE=$rawReduce CONFLICT=$rawConfl")
        val infoReduce = countEvents(raw, listOf("--rdb-at=7", "--show-info=1")).first
        assertEquals(infoReduce, countEvents(st.binBin, listOf("--rdb-at=7")).first, "$TAG FIX 2 fixed reference")
        var ktReduce = 0
        MiniSatShadowDriver.run({ if (it == "REDUCE") ktReduce++ }, 0, listOf("--rdb-at=7"), php76, null, TAG)
        assertEquals(infoReduce, ktReduce, "$TAG FIX 2: port")

        // FIX 3: binary proof tail lost when eliminate proves UNSAT: raw master writes only the
        // final "a 0"; fixed = the ASCII proof in binary encoding.
        val proofArgs = listOf("--simp=1", "--drup=1", php32.path)
        assertEquals(listOf('a'.code.toByte(), 0.toByte()), runRef(raw, proofArgs).second.toList(), "$TAG FIX 3 repro")
        val expected = encodeBinary(String(runRef(st.binAscii, proofArgs).second))
        if (expected.size <= 2) fail("$TAG FIX 3: ASCII proof of php_3_2 is empty")
        assertEquals(expected, runRef(st.binBin, proofArgs).second.toList(), "$TAG FIX 3 fixed reference")
        val kt = java.io.ByteArrayOutputStream()
        MiniSatShadowDriver.run(null, 1, emptyList(), php32, null, TAG, drup = { b, o, l -> kt.write(b, o, l) })
        assertEquals(expected, kt.toByteArray().toList(), "$TAG FIX 3: port")

        // FIX 4: rcheck with master's elimination order drops every resolvent: raw master answers
        // SAT on the UNSAT php_3_2; fixed reference and port UNSAT.
        val rcheck = listOf("--simp=1", "--rcheck=1", php32.path)
        assertEquals(10, runRef(raw, rcheck).first, "$TAG FIX 4 repro")
        assertEquals(20, runRef(st.binBin, rcheck).first, "$TAG FIX 4 fixed reference")
        val s4 = MiniSatShadowDriver.run(null, 1, listOf("--rcheck=1"), php32, null, TAG)
        assertEquals(0, s4.model.size, "$TAG FIX 4: port must not find a model")
        println("$TAG upstream bugs 1-4 reproduced on raw master, fixed in reference and port")
    }

    @Test
    fun unsatProofsVerifyWithDratTrim() {
        val dratTrim = System.getenv("DRAT_TRIM")?.let(::File) ?: skip("env DRAT_TRIM (path to a drat-trim binary) not set")
        if (!dratTrim.canExecute()) fail("$TAG DRAT_TRIM=$dratTrim is not executable")
        val shadow = MiniSatShadowDriver.locateShadowDir() ?: skip("no ksat-extra/shadow found")
        val cnfs = listOf("cnf", "cnf-full").flatMap { d -> File(shadow, d).listFiles { f -> f.name.endsWith(".cnf") }!!.sortedBy { it.name } }
            .filter { it.nameWithoutExtension !in setOf("php_9_8", "php_10_9") }
        var verified = 0
        val failures = ArrayList<String>()
        for (cnf in cnfs) for (simp in 0..1) for (binary in listOf(true, false)) {
            val label = "[${cnf.name} simp=$simp ${if (binary) "binary" else "ascii"}]"
            val proof = java.io.ByteArrayOutputStream()
            val s = MiniSatShadowDriver.run(null, simp, emptyList(), cnf, null, TAG, drup = { b, o, l -> proof.write(b, o, l) }, binary = binary)
            if (s.okay()) continue   // SAT: no refutation to check
            val pb = ProcessBuilder(dratTrim.path, cnf.path, "/dev/stdin").redirectErrorStream(true)
            val proc = pb.start()
            val reader = Thread { proc.outputStream.use { proof.writeTo(it) } }.apply { start() }
            val out = proc.inputStream.bufferedReader().readText()
            reader.join()
            if (!proc.waitFor(60, TimeUnit.SECONDS)) { proc.destroyForcibly(); fail("$TAG drat-trim hung: $label") }
            if (out.lines().any { it.trim() == "s VERIFIED" }) verified++
            else failures += "$label not verified (${proof.size()} bytes):\n" + out.lines().filter { it.startsWith("s ") || it.startsWith("c ERROR") || it.contains("WARNING") }.take(5).joinToString("\n")
        }
        println("$TAG drat-trim: $verified UNSAT proofs verified, ${failures.size} failing")
        if (failures.isNotEmpty()) fail("$TAG ${failures.size} proofs not verified:\n" + failures.take(10).joinToString("\n"))
        assertEquals(true, verified > 0, "$TAG no UNSAT case checked")
    }

    private companion object {
        const val TAG = "[drup-minisat]"
        const val CONTEXT = 6
        const val QUICK_MAX_LINES = 20_000
        val SIMP_OPTIONS = setOf("asymm", "rcheck", "elim", "grow", "cl-lim", "sub-lim", "simp-gc-frac")
        val PROOF_OPTION_SETS: List<List<String>> = listOf(
            emptyList(),
            listOf("--ccmin-mode=0", "--phase-saving=0", "--gc-frac=0.01", "--min-learnts=5"),
            listOf("--asymm=1", "--rcheck=1", "--grow=2", "--cl-lim=-1", "--sub-lim=3", "--simp-gc-frac=0.01"),
            // (no --show-info here: upstream prints its "c [reduceDB]" lines to stdout, into the proof)
            listOf("--rdb-at=7"),
        )
        val TRACE_OPTION_SETS: List<List<String>> = listOf(
            emptyList(),
            listOf("--rdb-at=1"),
            listOf("--rdb-at=7"),
            listOf("--rdb-at=7", "--show-info=1"),
            listOf("--rdb-at=50", "--show-info=1"),
            listOf("--rdb-at=3", "--show-info=1", "--asymm=1"),
        )
    }
}
