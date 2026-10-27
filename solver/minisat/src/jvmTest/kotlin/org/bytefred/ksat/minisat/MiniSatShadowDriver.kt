package org.bytefred.ksat.minisat

import org.bytefred.ksat.DimacsCnf
import java.io.File
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
     * minisat-full; default: master, minisat-master).
     */
    fun run(
        emit: ((String) -> Unit)?, simp: Int, opts: List<String>, cnf: File, assume: File?, tag: String,
        drup: DrupFile? = null, binary: Boolean = true, csb: Boolean = false,
    ): MiniSat {
        val s: MiniSat = if (simp == 1) MiniSatSimp() else MiniSat()
        s.csbCompat = csb
        applyOptions(s, opts, tag)
        if (emit != null) s.setTraceSink(emit)
        if (s is MiniSatSimp) s.parsing = true
        s.binDrup = binary
        s.drupFile = drup
        // parse_DIMACS: readClause creates variables lazily, then S.addClause_(lits).
        for (clause in DimacsCnf.parse(cnf.readText()).clauses) {
            val lits = IntVec()
            for (parsed in clause) {
                val v = kotlin.math.abs(parsed) - 1
                while (v >= s.nVars()) s.newVar()
                lits.push(if (parsed > 0) mkLit(v) else litNeg(mkLit(v)))
            }
            s.addClause_(lits)
        }
        val assumps = IntVec()
        if (assume != null) {
            for (tok in assume.readText().split(Regex("\\s+")).filter { it.isNotEmpty() }) {
                val lit = tok.toInt()
                if (lit == 0) continue
                val v = kotlin.math.abs(lit) - 1
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
