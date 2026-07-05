"use strict";

const { State, saveMP, restoreMP, move2Str } = require('./state');
const { ttStore, ttProbe, TE, TL, TU } = require('./tt');
const { LMP_TABLE, EMPTY } = require('./constants');

let nodes = 0, searchStartTime = 0, searchTimeLimitMs = 30000, searchAborted = false;
const killers = new Int32Array(256);
const histTable = new Int32Array(4096);

function storeKiller(ply, m) {
    const idx = ply * 2;
    if (killers[idx] !== m.from * 64 + m.to) {
        killers[idx + 1] = killers[idx];
        killers[idx] = m.from * 64 + m.to;
    }
}

function scoreMove(m, hfm, htm, ply) {
    const hk = m.from * 64 + m.to;
    if (m.from === hfm && m.to === htm) return 1000000;
    if (m.captured.length > 0) return 100000 + m.captured.length * 1000 + (m.capKings || 0) * 100 + (m.promo ? 50 : 0);
    if (m.promo) return 95000;
    const idx = ply * 2;
    if (hk === killers[idx] || hk === killers[idx + 1]) return 90000;
    return histTable[hk] || 0;
}

function orderMoves(moves, hfm, htm, ply) {
    for (let i = 1; i < moves.length; i++) {
        const key = moves[i], ks = scoreMove(key, hfm, htm, ply);
        let j = i - 1;
        while (j >= 0 && scoreMove(moves[j], hfm, htm, ply) < ks) {
            moves[j + 1] = moves[j]; j--;
        }
        moves[j + 1] = key;
    }
}

function qsearch(state, alpha, beta, ply) {
    nodes++;
    if ((nodes & 4095) === 0 && searchTimeLimitMs > 0 && Date.now() - searchStartTime > searchTimeLimitMs)
        { searchAborted = true; return alpha; }

    const sp = state.eval();
    if (sp >= beta) return beta;
    if (sp > alpha) alpha = sp;

    const poolPos = saveMP();
    const capMoves = state.getCapturesOnly();
    if (capMoves.length === 0) { restoreMP(poolPos); return alpha; }

    const tte = ttProbe(state.hash);
    const hfm = tte ? tte.mv >> 6 : -1, htm = tte ? tte.mv & 0x3F : -1;
    orderMoves(capMoves, hfm, htm, ply);

    for (const m of capMoves) {
        const undo = state.makeMove(m);
        const sc = -qsearch(state, -beta, -alpha, ply + 1);
        state.unmakeMove(m, undo);
        if (searchAborted) { restoreMP(poolPos); return alpha; }
        if (sc > alpha) { alpha = sc; if (alpha >= beta) { restoreMP(poolPos); return beta; } }
    }
    restoreMP(poolPos);
    return alpha;
}

function search(state, depth, alpha, beta, ply, prevFrom, prevTo) {
    nodes++;
    if ((nodes & 4095) === 0 && searchTimeLimitMs > 0) {
        if (Date.now() - searchStartTime > searchTimeLimitMs) { searchAborted = true; return alpha; }
    }
    if (state.checkDraw()) return 0;

    const isPV = beta > alpha + 1;
    if (depth <= 0) return qsearch(state, alpha, beta, ply);

    const hash = state.hash;
    let hfm = -1, htm = -1;
    const tte = ttProbe(hash);
    if (tte) {
        hfm = tte.mv >> 6; htm = tte.mv & 0x3F;
        if (!isPV && tte.dp >= depth) {
            const tsc = tte.sc;
            if (tte.fl === TE) return tsc;
            if (tte.fl === TL && tsc >= beta) return beta;
            if (tte.fl === TU && tsc <= alpha) return alpha;
        }
    }

    const poolPos = saveMP();
    const moves = state.getMoves();
    if (moves.length === 0) { restoreMP(poolPos); return -9999 + ply; }
    const hasCaptures = moves[0].captured.length > 0;

    let extension = 0;
    if (moves.length === 1 && ply < 16) extension = 1;

    if (hfm < 0 && depth >= 3 && !hasCaptures) {
        search(state, depth - 3, alpha, beta, ply, prevFrom, prevTo);
        if (searchAborted) { restoreMP(poolPos); return alpha; }
        const tte2 = ttProbe(hash);
        if (tte2) { hfm = tte2.mv >> 6; htm = tte2.mv & 0x3F; }
    }

    let staticEval = null;
    if (!isPV && depth >= 4 && !hasCaptures && beta < 9000 && beta > -9000) {
        const pc = state.wP + state.bP + state.wK + state.bK;
        const sideKings = state.turn === 1 ? state.wK : state.bK;
        const isPureKingEG = (state.wP === 0 && state.bP === 0 && pc <= 6);
        if (!isPureKingEG && (pc >= 10 || sideKings > 0)) {
            staticEval = state.eval();
            if (staticEval >= beta) {
                const oldTurn = state.turn; state.turn = -state.turn; state.hash ^= require('./constants').zt;
                const R = depth >= 9 ? 4 : depth >= 6 ? 3 : 2;
                const nullScore = -search(state, depth - 1 - R, -beta, -beta + 1, ply + 1, -1, -1);
                state.turn = oldTurn; state.hash ^= require('./constants').zt;
                if (searchAborted) { restoreMP(poolPos); return alpha; }
                if (nullScore >= beta) { restoreMP(poolPos); return nullScore; }
            }
        }
    }

    if (!isPV && depth <= 2 && !hasCaptures && alpha > -8000) {
        if (staticEval === null) staticEval = state.eval();
        const razorMargin = depth === 1 ? 320 : 540;
        if (staticEval + razorMargin < alpha) { const qs = qsearch(state, alpha, beta, ply); restoreMP(poolPos); return qs; }
    }

    orderMoves(moves, hfm, htm, ply);

    const origAlpha = alpha;
    let bestScore = -Infinity, bestFm = -1, bestTm = -1;
    let quietCount = 0;

    for (let i = 0; i < moves.length; i++) {
        const m = moves[i];
        const isCapture = m.captured.length > 0;
        const isQuiet = !isCapture && !m.promo;

        if (!isPV && isQuiet && depth <= 5 && quietCount >= LMP_TABLE[Math.min(depth, 5)]) break;
        if (isQuiet) quietCount++;

        if (!isPV && depth <= 3 && i >= 2 && isQuiet && bestScore > -8000 && alpha > -8000) {
            if (staticEval === null) staticEval = state.eval();
            const margin = [0, 120, 220, 340][depth];
            if (staticEval + margin <= alpha) continue;
        }

        const undo = state.makeMove(m);

        let score;
        if (i === 0) {
            score = -search(state, depth - 1 + extension, -beta, -alpha, ply + 1, m.from, m.to);
        } else {
            let lmrR = 0;
            if (isQuiet && depth >= 3 && i >= 2) {
                lmrR = Math.max(1, Math.floor(Math.log(depth) * Math.log(i + 1) / 2.2));
                if (depth >= 5 && i >= 5) lmrR = Math.min(lmrR + 1, depth - 2);
                if (depth >= 8 && i >= 10) lmrR = Math.min(lmrR + 1, depth - 2);
            }
            score = -search(state, depth - 1 - lmrR, -alpha - 1, -alpha, ply + 1, m.from, m.to);
            if (!searchAborted && score > alpha && (lmrR > 0 || isPV)) {
                score = -search(state, depth - 1, -beta, -alpha, ply + 1, m.from, m.to);
            }
        }
        state.unmakeMove(m, undo);
        if (searchAborted) { restoreMP(poolPos); return alpha; }

        if (score > bestScore) { bestScore = score; bestFm = m.from; bestTm = m.to; }
        if (score > alpha) alpha = score;
        if (alpha >= beta) {
            if (isQuiet) {
                storeKiller(ply, m);
                const hk = m.from * 64 + m.to;
                histTable[hk] = Math.min(histTable[hk] + depth * depth, 200000);
                for (let j = 0; j < i; j++) {
                    const mj = moves[j];
                    if (!mj.captured.length && !mj.promo)
                        histTable[mj.from * 64 + mj.to] = Math.max(histTable[mj.from * 64 + mj.to] - depth * depth, -200000);
                }
            }
            break;
        }
    }

    if (!searchAborted && bestFm !== -1) {
        const flag = bestScore <= origAlpha ? TU : bestScore >= beta ? TL : TE;
        ttStore(hash, depth, bestScore, bestFm, bestTm, flag);
    }
    restoreMP(poolPos);
    return bestScore;
}

function getBestMove(state, maxDepth, timeLimitMs, bookProbeFn) {
    const poolPos = saveMP();
    const moves = state.getMoves();
    if (moves.length === 0) { restoreMP(poolPos); return { move: null, score: -10000, depth: 0, nodes: 0, pv: [], isBook: false }; }

    if (bookProbeFn) {
        const bookMove = bookProbeFn(state);
        if (bookMove) {
            restoreMP(poolPos);
            return { move: bookMove, score: 0, depth: 0, nodes: 0, pv: [bookMove], isBook: true };
        }
    }

    if (moves.length === 1) {
        const res = { move: moves[0], score: state.eval(), depth: 1, nodes: 1, pv: [moves[0]], isBook: false };
        restoreMP(poolPos);
        return res;
    }

    for (let ki = 0; ki < killers.length; ki++) killers[ki] = 0;
    for (let hi = 0; hi < histTable.length; hi++) histTable[hi] = 0;
    nodes = 0; searchAborted = false;
    searchStartTime = Date.now(); searchTimeLimitMs = timeLimitMs || 0;

    let bestMove = moves[0], bestScore = -Infinity, reachedDepth = 0;

    for (let depth = 1; depth <= maxDepth; depth++) {
        if (depth > 2) {
            for (let hi = 0; hi < histTable.length; hi++) histTable[hi] = (histTable[hi] * 3) >> 2;
        }

        let score;
        if (depth >= 5 && bestScore > -9000 && bestScore < 9000) {
            let delta = 10, ok = false, wc = bestScore;
            while (!ok && !searchAborted) {
                score = search(state, depth, wc - delta, wc + delta, 0, -1, -1);
                if (searchAborted) break;
                if (score > wc - delta && score < wc + delta) ok = true;
                else { wc = score; delta = Math.round(delta * 1.5); if (delta >= 9000) { score = search(state, depth, -Infinity, Infinity, 0, -1, -1); ok = true; } }
            }
        } else {
            score = search(state, depth, -Infinity, Infinity, 0, -1, -1);
        }
        if (searchAborted) break;

        const tte = ttProbe(state.hash);
        if (tte && (tte.mv >> 6) >= 0) {
            const f = moves.find(m => m.from === (tte.mv >> 6) && m.to === (tte.mv & 0x3F));
            if (f) { bestMove = f; bestScore = score; }
            else if (score > bestScore) bestScore = score;
        } else if (score > bestScore) { bestScore = score; }
        reachedDepth = depth;
    }

    {
        const _totalPc = state.wP + state.bP + state.wK + state.bK;
        let VARIETY_CP, VARIETY_TEMP;
        if (_totalPc > 18)       { VARIETY_CP = 15; VARIETY_TEMP = 9; }
        else if (_totalPc > 8)   { VARIETY_CP = 8;  VARIETY_TEMP = 6; }
        else                     { VARIETY_CP = 3;  VARIETY_TEMP = 3; }
        searchAborted = false;
        if (reachedDepth >= 2 && bestScore > -9000 && bestScore < 9000 && moves.length > 1) {
            const rootScores = [];
            for (const m of moves) {
                const s2 = state.clone();
                s2.applyMove(m);
                const sc = -search(s2, 1, -Infinity, Infinity, 1, m.from, m.to);
                if (searchAborted) { rootScores.push({ m, sc: 0 }); searchAborted = false; }
                else rootScores.push({ m, sc });
            }
            const bestRS = Math.max(...rootScores.map(x => x.sc));
            const candidates = rootScores.filter(x => x.sc >= bestRS - VARIETY_CP);
            const expScores = candidates.map(x => Math.exp(x.sc / VARIETY_TEMP));
            const sumExp = expScores.reduce((a, b) => a + b, 0);
            let r = Math.random() * sumExp, cum = 0;
            for (let ci = 0; ci < candidates.length; ci++) {
                cum += expScores[ci];
                if (r <= cum) { bestMove = candidates[ci].m; break; }
            }
        }
    }

    const pv = [bestMove];
    let pvState = state.clone();
    pvState.applyMove(bestMove);
    for (let pvDepth = 1; pvDepth < 5; pvDepth++) {
        const ttePV = ttProbe(pvState.hash);
        if (!ttePV || (ttePV.mv >> 6) < 0) break;
        const pvMoves = pvState.getMoves();
        const pvNext = pvMoves.find(m => m.from === (ttePV.mv >> 6) && m.to === (ttePV.mv & 0x3F));
        if (!pvNext) break;
        pv.push(pvNext);
        pvState.applyMove(pvNext);
    }

    restoreMP(poolPos);
    return {
        move: bestMove,
        score: bestScore,
        depth: reachedDepth,
        nodes,
        pv,
        isBook: false,
    };
}

function abortSearch() { searchAborted = true; }

module.exports = { getBestMove, abortSearch, search, qsearch, nodes: () => nodes };
