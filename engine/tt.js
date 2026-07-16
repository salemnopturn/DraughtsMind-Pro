"use strict";

// ═══════════════════════════════════════════════════════════════════════════
// tt.js — Transposition Table for DraughtsMind Pro Engine
// Synchronized with renderer/scripts/app.js TT implementation
// ═══════════════════════════════════════════════════════════════════════════

const TTS = 1 << 18;
const TE = 0, TL = 1, TU = 2;
// Layout: tt0/hash, tt1/data (primary), tt2/hash, tt3/data (secondary)
const tt0 = new Uint32Array(TTS), tt1 = new Uint32Array(TTS);
const tt2 = new Uint32Array(TTS), tt3 = new Uint32Array(TTS);

// data layout(32 bits): move(12) | score_scaled(10) | depth(8+128) | flag(2)
function ttPack(mv, sc, dp, fl) {
    const d = (dp + 128) & 0xFF;
    const s = Math.round(Math.max(-512, Math.min(511, sc / 20))) & 0x3FF;
    const m = mv & 0xFFF;
    const f = fl & 3;
    return m | (s << 12) | (d << 22) | (f << 30);
}

function ttUnpack(v) {
    return {
        mv: v & 0xFFF,
        sc: (((v >> 12) & 0x3FF) << 22) >> 22,
        dp: ((v >> 22) & 0xFF) - 128,
        fl: (v >> 30) & 3,
    };
}

function ttStore(hash, depth, score, from, to, flag) {
    const i = Number(hash & BigInt(TTS - 1));
    const hh = Number(hash >> 32n);
    const mv = (from << 6) | to;
    const v = ttPack(mv, score, depth, flag);
    const e0d = ((tt1[i] >> 22) & 0xFF) - 128;
    if (depth >= e0d) {
        // Preserve old slot 0 in slot 1 before overwriting (aging-friendly)
        tt2[i] = tt0[i]; tt3[i] = tt1[i];
        tt0[i] = hh; tt1[i] = v;
    } else {
        tt2[i] = hh; tt3[i] = v;
    }
}

function ttProbe(hash) {
    const i = Number(hash & BigInt(TTS - 1));
    const hh = Number(hash >> 32n);
    if (tt0[i] === hh) return ttUnpack(tt1[i]);
    if (tt2[i] === hh) return ttUnpack(tt3[i]);
    return null;
}

function ttClear() {
    tt0.fill(0); tt1.fill(0); tt2.fill(0); tt3.fill(0);
}

module.exports = { TTS, TE, TL, TU, ttStore, ttProbe, ttClear };
