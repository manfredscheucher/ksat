package org.bytefred.ksat.minisat

import java.io.File
import java.util.concurrent.TimeUnit
import kotlin.test.fail

/**
 * Line-by-line live comparison of a Kotlin run against a running reference process (no trace
 * files): every line the Kotlin side emits is compared with the next stdout line of the reference
 * as it arrives. Used by [MiniSatIncrementalShadowTest] and [MiniSatDimacsLiveTest].
 */
internal object LiveCompare {

    class Result(val diff: String?, val exitCode: Int, val stderr: String)

    private class Stop : RuntimeException()

    private const val CONTEXT = 6

    /**
     * Starts [cmd] with LSTRACE=1 and compares its stdout (ISO-8859-1, so every byte maps to one
     * char; lines for which [keep] is false are skipped) with the lines [kotlin] passes to its sink.
     * An exception thrown by [kotlin] is a difference. [Result.diff] is null when both streams are
     * identical, else the context of the first difference.
     */
    fun run(cmd: List<String>, label: String, keep: (String) -> Boolean, kotlin: ((String) -> Unit) -> Unit): Result {
        val errFile = File.createTempFile("minisat-live", ".err")
        try {
            val pb = ProcessBuilder(cmd).redirectError(ProcessBuilder.Redirect.to(errFile))
            pb.environment()["LSTRACE"] = "1"
            val proc = pb.start()
            val ref = proc.inputStream.bufferedReader(Charsets.ISO_8859_1)
            fun nextRef(): String? {
                while (true) {
                    val l = ref.readLine() ?: return null
                    if (keep(l)) return l
                }
            }
            val ring = ArrayDeque<String>()
            var lineNo = 0
            var diffAt = -1
            var upDiff: String? = null
            val ktAfter = ArrayList<String>()
            val sink: (String) -> Unit = sink@{ line ->
                if (diffAt >= 0) {
                    ktAfter += line
                    if (ktAfter.size >= CONTEXT) throw Stop()
                    return@sink
                }
                val g = nextRef()
                lineNo++
                if (g != line) { diffAt = lineNo; upDiff = g; ktAfter += line; return@sink }
                ring.addLast(line)
                if (ring.size > CONTEXT) ring.removeFirst()
            }
            try {
                kotlin(sink)
            } catch (_: Stop) {
            } catch (e: Throwable) {
                if (diffAt < 0) { diffAt = lineNo + 1; upDiff = nextRef() }
                ktAfter += "EXCEPTION $e"
                for (f in e.stackTrace.take(8)) ktAfter += "    at $f"
            }
            if (diffAt < 0) {
                val g = nextRef()
                if (g != null) { diffAt = lineNo + 1; upDiff = g; ktAfter += "<end of kotlin output>" }
            }
            val upAfter = ArrayList<String>()
            if (diffAt >= 0) { upDiff?.let { upAfter += it }; while (upAfter.size < CONTEXT) upAfter += nextRef() ?: break }
            if (diffAt >= 0) proc.destroy() else while (ref.readLine() != null) { /* drain */ }
            if (!proc.waitFor(60, TimeUnit.SECONDS)) { proc.destroyForcibly(); fail("reference hung: $label") }
            val diff = if (diffAt < 0) null else buildString {
                append("$label first diff at line $diffAt\n")
                for (l in ring) append("    = ").append(l).append('\n')
                for (l in upAfter) append("  up> ").append(l).append('\n')
                if (upAfter.isEmpty()) append("  up> <end of upstream output>\n")
                for (l in ktAfter) append("  kt> ").append(l).append('\n')
            }
            return Result(diff, proc.exitValue(), errFile.readText(Charsets.ISO_8859_1))
        } finally {
            errFile.delete()
        }
    }
}
