package org.bytefred.ksat.minisat

import java.io.File
import kotlin.math.abs
import kotlin.test.fail

/**
 * Kotlin mirror of the shadow reference drivers (ksat-extra/shadow/minisat-full/driver.cpp and
 * ksat-extra/shadow/minisat-master/driver.cpp), shared by [MiniSatLiveShadowTest] and
 * [MiniSatDrupTest].
 */
internal object MiniSatShadowDriver {

    /** Upstream option names (driver `--<name>=<value>`) -> port properties. */
    fun applyOptions(s: MiniSat, opts: List<String>, tag: String) {
        for (o in opts) {
            val (name, value) = o.removePrefix("--").split('=', limit = 2)
            fun b() = value == "1"
            when (name) {
                "var-decay" -> s.varDecay = value.toDouble()
                "cla-decay" -> s.clauseDecay = value.toDouble()
                "rnd-freq" -> s.randomVarFreq = value.toDouble()
                "rnd-seed" -> s.randomSeed = value.toDouble()
                "ccmin-mode" -> s.ccminMode = value.toInt()
                "phase-saving" -> s.phaseSaving = value.toInt()
                "rnd-init" -> s.rndInitAct = b()
                "luby" -> s.lubyRestart = b()
                "rfirst" -> s.restartFirst = value.toInt()
                "rinc" -> s.restartInc = value.toDouble()
                "gc-frac" -> s.garbageFrac = value.toDouble()
                "min-learnts" -> s.minLearntsLim = value.toInt()
                "rdb-at" -> s.reduceDBAtConfl = value.toInt()          // master only
                "show-info" -> s.showInfo = value.toInt()              // master driver only
                "asymm" -> (s as MiniSatSimp).useAsymm = b()
                "rcheck" -> (s as MiniSatSimp).useRcheck = b()
                "elim" -> (s as MiniSatSimp).useElim = b()
                "grow" -> (s as MiniSatSimp).grow = value.toInt()
                "cl-lim" -> (s as MiniSatSimp).clauseLim = value.toInt()
                "sub-lim" -> (s as MiniSatSimp).subsumptionLim = value.toInt()
                "simp-gc-frac" -> (s as MiniSatSimp).simpGarbageFrac = value.toDouble()
                else -> fail("$tag unknown option $o")
            }
        }
    }

    /** End of upstream simp/Main.cc: the pending binary proof (BUG FIX 3: master never flushes it
     *  there; minisat-master/driver.cpp with -DMASTER_FIXES does), then after an UNSAT result the
     *  final empty clause. */
    private fun drupEnd(s: MiniSat, unsat: Boolean) {
        val f = s.drupFile ?: return
        s.binDRUPFlush()
        if (!unsat) return
        val bytes = if (s.binDrup) byteArrayOf('a'.code.toByte(), 0) else "0\n".encodeToByteArray()
        f.write(bytes, 0, bytes.size)
    }

    /**
     * driver.cpp: parse_DIMACS, assumptions, then core `solveLimited`, or SimpSolver
     * `eliminate(true)` + `solveLimited`. With [drup] (master driver `--drup`) also simp/Main.cc's
     * proof handling: `parsing` true while reading, the proof sink set before reading, the final
     * empty clause after an UNSAT result. [csb] = [MiniSat.csbCompat] (the csb reference
     * minisat-full; default: master, minisat-master). [strict] = driver `--strict=1`.
     */
    fun run(
        emit: ((String) -> Unit)?, simp: Int, opts: List<String>, cnf: File, assume: File?, tag: String,
        drup: DrupFile? = null, binary: Boolean = true, csb: Boolean = false, strict: Boolean = false,
    ): MiniSat {
        val s: MiniSat = if (simp == 1) MiniSatSimp() else MiniSat()
        s.csbCompat = csb
        applyOptions(s, opts, tag)
        if (emit != null) s.setTraceSink(emit)
        if (s is MiniSatSimp) s.parsing = true
        s.binDrup = binary
        s.drupFile = drup
        // parse_DIMACS(in, S, strict) (the port of core/Dimacs.h); its header-mismatch line goes to
        // stdout upstream, i.e. into the trace stream. A parse error propagates (upstream: exit 3).
        parseDimacs(cnf.readBytes(), s, strict, emit ?: { println(it) })
        val assumps = IntVec()
        if (assume != null) {
            for (tok in assume.readText().split(Regex("\\s+")).filter { it.isNotEmpty() }) {
                val lit = tok.toInt()
                if (lit == 0) continue
                val v = abs(lit) - 1
                while (v >= s.nVars()) s.newVar()
                assumps.push(mkLit(v, lit < 0))
            }
        }
        val ret: Int
        if (s is MiniSatSimp) {
            for (i in 0 until assumps.size) s.setFrozen(litVar(assumps[i]), true)
            s.parsing = false
            s.eliminate(true)
            if (!s.okay()) {
                emit?.invoke("RESULT UNSAT")
                drupEnd(s, true)
                return s
            }
            ret = s.solveLimited(assumps)
        } else {
            ret = s.solveLimited(assumps)
        }
        drupEnd(s, lbEq(ret, L_FALSE))
        if (lbEq(ret, L_TRUE) && emit != null) {
            val sb = StringBuilder("MODEL")
            for (i in 0 until s.nVars()) {
                if (lbEq(s.model[i], L_UNDEF)) fail("$tag kotlin model value of variable ${i + 1} is undefined")
                sb.append(' ').append(if (lbEq(s.model[i], L_TRUE)) i + 1 else -(i + 1))
            }
            emit(sb.append(" 0").toString())
        }
        return s
    }

    /** Thrown by [runScript] where driver_script.h dies (exit 1). */
    class ScriptError(message: String) : RuntimeException(message)

    /**
     * Mirror of the drivers' incremental script mode (ksat-extra/shadow/minisat-full/driver_script.h,
     * `--script=<file.ops>`; format and output documented there): runs the operations of [script] in
     * order on one [MiniSat] ([simp] = 1: [MiniSatSimp]), every output line (OP, RET, VAR, MODEL,
     * FAILED, interleaved with the trace) goes to [emit].
     */
    fun runScript(emit: (String) -> Unit, simp: Int, opts: List<String>, script: File, tag: String, csb: Boolean = false): MiniSat {
        val s: MiniSat = if (simp == 1) MiniSatSimp() else MiniSat()
        s.csbCompat = csb
        applyOptions(s, opts, tag)
        s.setTraceSink(emit)
        val ss = s as? MiniSatSimp
        val newvars = ArrayList<Int>()
        val assumps = IntVec()
        var lineno = 0
        // Lines as fgetc up to '\n' (a last line without '\n' counts); tokens split at ' ', '\t', '\r'.
        val text = script.readText()
        val lines = text.split('\n').let { if (text.endsWith('\n') || text.isEmpty()) it.dropLast(1) else it }
        for (line in lines) {
            lineno++
            val t = line.split(' ', '\t', '\r').filter { it.isNotEmpty() }
            if (t.isEmpty() || t[0][0] == '#') continue
            fun sfail(what: String): Nothing = throw ScriptError("$tag script line $lineno '$line': $what")
            fun num(x: String): Long? {
                if (!Regex("-?[0-9]+").matches(x)) return null
                return x.toLongOrNull()
            }
            fun lit(tok: String, create: Boolean): Int {
                val neg = tok.startsWith("-")
                val body = if (neg) tok.substring(1) else tok
                val v: Int
                if (body.length > 1 && body[0] == '@') {
                    val n = num(body.substring(1))
                    if (n == null || n < 1 || n > newvars.size) sfail("bad @k reference")
                    v = newvars[(n - 1).toInt()]
                } else {
                    val n = num(body)
                    if (n == null || n < 1 || n > Int.MAX_VALUE / 2) sfail("bad literal")
                    v = (n - 1).toInt()
                    if (create) while (v >= s.nVars()) s.newVar(L_UNDEF, true)
                    else if (v >= s.nVars()) sfail("variable does not exist")
                }
                return mkLit(v, neg)
            }
            fun variable(tok: String): Int {
                if (tok.startsWith("-")) sfail("a variable must be positive")
                return litVar(lit(tok, false))
            }
            fun lits(out: IntVec) {
                out.clear()
                if (t.size < 2 || t.last() != "0") sfail("literal list must end with 0")
                for (i in 1 until t.size - 1) out.push(lit(t[i], true))
            }
            fun flag01(tok: String, key: String): Int? {
                if (!tok.startsWith("$key=")) return null
                return when (tok.substring(key.length + 1)) { "0" -> 0; "1" -> 1; else -> sfail("flag value must be 0 or 1") }
            }
            fun lbool(x: String): Int = when (x) { "t" -> L_TRUE; "f" -> L_FALSE; "u" -> L_UNDEF; else -> sfail("polarity must be t, f or u") }
            fun dimacs(p: Int): Int = if (litSign(p)) -(litVar(p) + 1) else litVar(p) + 1

            emit("OP " + t.joinToString(" "))
            when (t[0]) {
                "add" -> {
                    val l = IntVec()
                    lits(l)
                    emit("RET " + (if (s.addClause(l)) 1 else 0))
                }
                "assume" -> lits(assumps)
                "solve" -> {
                    var doSimp = 1
                    var turnOff = 0
                    for (i in 1 until t.size) {
                        if (ss == null) sfail("solve takes no flags without --simp=1")
                        flag01(t[i], "simp")?.let { doSimp = it }
                            ?: flag01(t[i], "turnoff")?.let { turnOff = it }
                            ?: sfail("unknown solve flag")
                    }
                    val ret = ss?.solveLimited(assumps, doSimp == 1, turnOff == 1) ?: s.solveLimited(assumps)
                    emit("RET " + (if (lbEq(ret, L_TRUE)) "SAT" else if (lbEq(ret, L_FALSE)) "UNSAT" else "UNKNOWN"))
                    if (lbEq(ret, L_TRUE)) {
                        if (s.model.size != s.nVars()) fail("$tag model has ${s.model.size} values for ${s.nVars()} variables")
                        val sb = StringBuilder("MODEL")
                        for (i in 0 until s.nVars()) {
                            sb.append(' ').append(
                                if (lbEq(s.model[i], L_TRUE)) "${i + 1}" else if (lbEq(s.model[i], L_FALSE)) "${-(i + 1)}" else "?${i + 1}"
                            )
                        }
                        emit(sb.append(" 0").toString())
                    } else if (lbEq(ret, L_FALSE)) {
                        val sb = StringBuilder("FAILED")
                        for (i in 0 until s.conflict.size()) sb.append(' ').append(dimacs(s.conflict[i]))
                        emit(sb.append(" 0").toString())
                    }
                }
                "release" -> {
                    if (t.size != 2) sfail("usage: release <lit>")
                    s.releaseVar(lit(t[1], false))
                }
                "simplify" -> {
                    if (t.size != 1) sfail("usage: simplify")
                    emit("RET " + (if (s.simplify()) 1 else 0))
                }
                "newvar" -> {
                    var pol = L_UNDEF
                    var dvar = 1
                    for (i in 1 until t.size) {
                        if (t[i].startsWith("pol=")) pol = lbool(t[i].substring(4))
                        else dvar = flag01(t[i], "dvar") ?: sfail("unknown newvar flag")
                    }
                    val v = s.newVar(pol, dvar == 1)
                    newvars += v
                    emit("VAR ${v + 1}")
                }
                "polarity" -> {
                    if (t.size != 3) sfail("usage: polarity <var> t|f|u")
                    s.setPolarity(variable(t[1]), lbool(t[2]))
                }
                "decision" -> {
                    if (t.size != 3 || (t[2] != "0" && t[2] != "1")) sfail("usage: decision <var> 0|1")
                    s.setDecisionVar(variable(t[1]), t[2] == "1")
                }
                "budget" -> {
                    val a = if (t.size == 2) t[1] else ""
                    val n = if (a.startsWith("conf=") || a.startsWith("prop=")) num(a.substring(5)) else null
                    when {
                        a == "off" -> s.budgetOff()
                        a.startsWith("conf=") && n != null -> s.setConfBudget(n)
                        a.startsWith("prop=") && n != null -> s.setPropBudget(n)
                        else -> sfail("usage: budget conf=<n> | prop=<n> | off")
                    }
                }
                "interrupt" -> { if (t.size != 1) sfail("usage: interrupt"); s.interrupt() }
                "clear-interrupt" -> { if (t.size != 1) sfail("usage: clear-interrupt"); s.clearInterrupt() }
                "freeze" -> {
                    if (ss == null) sfail("freeze needs --simp=1")
                    if (t.size != 3 || (t[2] != "0" && t[2] != "1")) sfail("usage: freeze <var> 0|1")
                    ss.setFrozen(variable(t[1]), t[2] == "1")
                }
                "eliminate" -> {
                    if (ss == null) sfail("eliminate needs --simp=1")
                    var turnOff = 0
                    for (i in 1 until t.size) turnOff = flag01(t[i], "turnoff") ?: sfail("unknown eliminate flag")
                    emit("RET " + (if (ss.eliminate(turnOff == 1)) 1 else 0))
                }
                else -> sfail("unknown operation")
            }
        }
        return s
    }

    fun locateShadowDir(): File? {
        var dir: File? = File(System.getProperty("user.dir")).absoluteFile
        while (dir != null) {
            val candidate = File(dir, "ksat-extra/shadow")
            if (candidate.isDirectory) return candidate
            dir = dir.parentFile
        }
        return null
    }
}
