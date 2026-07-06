"use strict";

const TTS = 1 << 18;
const TE = 0, TL = 1, TU = 2;
const tt0 = new Uint32Array(TTS), tt1 = new Uint32Array(TTS);
const tt2 = new Uint32Array(TTS), tt3 = new Uint32Array(TTS);
let ttGen = 0;

function ttPack(depth, score, from, to, flag) {
    const sc = Math.max(-9999, Math.min(9999, Math.round(score / 20)));
    return ((from & 0x3F) << 6 | (to & 0x3F)) | ((sc & 0x3FF) << 12) | (((depth + 128) & 0xFF) << 22) | ((flag & 0x3) << 30);
}

function ttUnpack(data) {
    const mv = data & 0xFFF;
    const sc = ((data >> 12) & 0x3FF);
    const dp = ((data >> 22) & 0xFF) - 128;
    const fl = (data >> 30) & 0x3;
    return { mv, sc: (sc << 1) - 9999 + 9999 ? (sc >= 512 ? sc - 1024 : sc) : sc, dp, fl };
}

function ttUnpackScore(data) {
    const raw = (data >> 12) & 0x3FF;
    return (raw >= 512 ? raw - 1024 : raw) * 20;
}

function ttStore(hash, depth, score, from, to, flag) {
    const idx = Number(hash & BigInt(TTS - 1));
    const data = ttPack(depth, score, from, to, flag);
    const age = (ttGen & 0xF) << 24;
    if ((tt0[idx] & 0xFF000000) <= age || depth >= ((tt0[idx] >> 22) & 0xFF) - 128) {
        tt2[idx] = tt0[idx]; tt3[idx] = tt1[idx];
        tt0[idx] = data | age; tt1[idx] = Number(hash >> 32n) & 0xFFFFFFFF;
    } else {
        tt2[idx] = data | age; tt3[idx] = Number(hash >> 32n) & 0xFFFFFFFF;
    }
}

function ttProbe(hash) {
    const idx = Number(hash & BigInt(TTS - 1));
    const h1 = Number(hash >> 32n) & 0xFFFFFFFF;
    if (tt1[idx] === h1) {
        const d = ttUnpack(tt0[idx]);
        d.sc = ttUnpackScore(tt0[idx]);
        return d;
    }
    if (tt3[idx] === h1) {
        const d = ttUnpack(tt2[idx]);
        d.sc = ttUnpackScore(tt2[idx]);
        return d;
    }
    return null;
}

function ttClear() {
    tt0.fill(0); tt1.fill(0); tt2.fill(0); tt3.fill(0);
    ttGen++;
}

module.exports = { TTS, TE, TL, TU, ttStore, ttProbe, ttClear, ttGen: () => ttGen };
