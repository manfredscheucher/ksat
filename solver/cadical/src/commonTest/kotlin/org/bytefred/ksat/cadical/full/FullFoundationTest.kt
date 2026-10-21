package org.bytefred.ksat.cadical.full

import kotlin.test.Test
import kotlin.test.assertEquals

/**
 * Checks the foundation of the full CaDiCaL port bit for bit against upstream C++: libc++
 * std::sort with ties ([cxxSort]), the radix sort [rsort], the PRNG [Random], the radix heap
 * [Reap], the bias corrected [EMA] and the binary [Heap] with the 'score_smaller' order. The expected checksums are printed by
 * scripts/probe/probe_cadical_foundation.cpp (built against upstream CaDiCaL 2.1.3 with
 * Apple clang 16 / libc++ 18.1), which runs exactly the same sequence.
 */
class FullFoundationTest {

    private fun mix(h: ULong, v: ULong): ULong = h * 1099511628211uL + v

    private val sizes = intArrayOf(0, 1, 2, 3, 4, 5, 6, 7, 23, 24, 25, 31, 32, 33, 100, 128, 129, 200, 1000, 5000)

    @Test
    fun matchesUpstream() {
        val random = Random(42u)

        // std::sort with many ties.
        var h: ULong = 0u
        for (n in sizes) {
            for (k in intArrayOf(1, 2, 3, 10, 1000000)) {
                val keys = IntArray(n)
                val v = IntArray(n)
                for (i in 0 until n) {
                    keys[i] = random.pickInt(0, k - 1)
                    v[i] = i
                }
                cxxSort(v, 0, n) { a, b -> keys[a] < keys[b] }
                for (x in v) h = mix(h, x.toULong())
            }
        }
        assertEquals(2651816962125519358uL, h, "sort")

        // rsort with 64 and 32 bit ranks.
        h = 0u
        for (n in sizes) {
            var bits = 0
            while (bits < 64) {
                val ranks = LongArray(n)
                val v = IntArray(n)
                val w = IntArray(n)
                for (i in 0 until n) {
                    val r = random.next()
                    ranks[i] = if (bits != 0) (r shr (64 - bits)).toLong() else 0L
                    v[i] = i
                    w[i] = i
                }
                rsort(v, 0, n) { a -> ranks[a] }
                rsort(w, 0, n, object : IntRank {
                    override fun rank(a: Int): Long = ranks[a] and 0xffffffffL
                    override val bits: Int get() = 32
                })
                for (x in v) h = mix(h, x.toULong())
                for (x in w) h = mix(h, x.toULong())
                bits += 9
            }
        }
        assertEquals(3631290638447749230uL, h, "rsort")

        // Random.
        h = 0u
        for (i in 0 until 1000) {
            h = mix(h, random.pickInt(-7, 1000 + i).toLong().toULong())
            h = mix(h, random.pickLog(3, 100000 + i).toLong().toULong())
            h = mix(h, random.generateDouble().toRawBits().toULong())
            h = mix(h, if (random.generateBool()) 1uL else 0uL)
        }
        assertEquals(5725222195009461622uL, h, "random")

        // Reap.
        h = 0u
        val reap = Reap() // the solver never calls 'init' (shrink.cpp only pushes, pops, clears)
        for (round in 0 until 50) {
            val base = 0u
            for (i in 0 until 40) reap.push((base + random.generate() % 5000u).toInt())
            while (!reap.empty()) h = mix(h, reap.pop().toUInt().toULong())
            reap.clear()
        }
        assertEquals(15145391093261756999uL, h, "reap")

        // EMA.
        h = 0u
        val ema = EMA()
        initEma(ema, 33)
        for (i in 0 until 1000) {
            ema.update(random.pickInt(0, 50).toDouble())
            h = mix(h, ema.value.toRawBits().toULong())
        }
        assertEquals(1177828431189049890uL, h, "ema")

        // Heap with the 'score_smaller' comparator (ties broken by index).
        h = 0u
        val stab = DoubleArray(2001)
        val scores = Heap { a, b ->
            val s = stab[a]
            val t = stab[b]
            if (s < t) true else if (s > t) false else a > b
        }
        for (idx in 1..2000) {
            stab[idx] = random.pickInt(0, 20).toDouble()
            scores.pushBack(idx)
        }
        for (i in 0 until 3000) {
            val idx = random.pickInt(1, 2000)
            if (!scores.contains(idx)) continue
            stab[idx] += random.pickInt(0, 3).toDouble()
            scores.update(idx)
            if (i % 3 == 0) h = mix(h, scores.popFront().toULong())
        }
        while (!scores.empty()) h = mix(h, scores.popFront().toULong())
        assertEquals(5263603180530082548uL, h, "heap")
    }
}
