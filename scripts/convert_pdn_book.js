"use strict";
/**
 * convert_pdn_book.js — Converte linhas de abertura (notação algébrica)
 * para o formato comprimido (char-pair) usado pelo book.js do DraughtsMind Pro.
 *
 * Uso:
 *   node scripts/convert_pdn_book.js < arquivo_com_lances.txt
 *
 * Cada linha deve conter uma sequência de lances em notação algébrica:
 *   c3-b4 f6-e5 b4-a5 b6-c5 ...
 *
 * Linhas comentadas (#) ou vazias são ignoradas.
 */

const { State } = require('../engine/state');
const { getPieceIdx, M64, zp, zt } = require('../engine/constants');

// ── Mapeamento interno do book.js ─────────────────────────────────────────
const DARK_SQUARES = [0,2,4,6,9,11,13,15,16,18,20,22,25,27,29,31,32,34,36,38,41,43,45,47,48,50,52,54,57,59,61,63];
const BOOK_ALPHA  = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdef';
const sqToChar     = Object.fromEntries(DARK_SQUARES.map((sq, i) => [sq, BOOK_ALPHA[i]]));
const charToSq     = Object.fromEntries(BOOK_ALPHA.split('').map((c, i) => [c, DARK_SQUARES[i]]));

// ── Conversão algébrica → índice interno ─────────────────────────────────
// NOTA: a notação algébrica do engine assume row 0 = rank 1 (topo).
// No book.js o mapeamento é direto: A=idx0, B=idx2, …, f=idx63.
function algToSq(sq) {
    if (!sq || sq.length < 2) return -1;
    const col = sq.charCodeAt(0) - 97; // a=0 … h=7
    const row = parseInt(sq[1], 10) - 1; // 1→0 … 8→7
    if (col < 0 || col > 7 || row < 0 || row > 7) return -1;
    return row * 8 + col;
}

// ── Converte lance algébrico → par de caracteres comprimidos ─────────────
function moveToPair(moveStr) {
    const parts = moveStr.split(/[-x:]/i);
    if (parts.length < 2) return null;
    const from = algToSq(parts[0]);
    const to   = algToSq(parts[parts.length - 1]);
    if (from < 0 || to < 0) return null;
    const cf = sqToChar[from];
    const ct = sqToChar[to];
    if (!cf || !ct) return null;
    return cf + ct;
}

// ── Converte linha completa de lances algébricos → string comprimida ────
function convertLine(line) {
    const tokens = line.trim().split(/\s+/);
    const pairs = [];
    for (const tk of tokens) {
        if (!tk || /[{}()\[\]?!]/.test(tk)) continue;
        // Remove números de lances (ex: "1.", "1...")
        const clean = tk.replace(/^\d+\.*/, '').trim();
        if (!clean) continue;
        if (/^[a-h][1-8]([-x:][a-h][1-8])+$/i.test(clean)) {
            const pair = moveToPair(clean);
            if (pair) pairs.push(pair);
        }
    }
    return pairs.join('');
}

// ── Valida a linha comprimida usando o State ─────────────────────────────
function validateMoves(compressed) {
    const s = new State();
    for (let i = 0; i < compressed.length; i += 2) {
        const from = charToSq[compressed[i]];
        const to   = charToSq[compressed[i + 1]];
        if (from === undefined || to === undefined) return false;
        const moves = s.getMoves();
        const match = moves.find(m => m.from === from && m.to === to);
        if (!match) return false;
        s.applyMove(match);
    }
    return true;
}

// ── MAIN ─────────────────────────────────────────────────────────────────
const readline = require('readline');
const rl = readline.createInterface({ input: process.stdin });

let total = 0, valid = 0, invalid = 0;

rl.on('line', (line) => {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) return;
    total++;
    const compressed = convertLine(line);
    if (!compressed || compressed.length < 2) { invalid++; return; }
    if (validateMoves(compressed)) {
        console.log(compressed);
        valid++;
    } else {
        invalid++;
    }
});

rl.on('close', () => {
    console.error(`\nProcessadas: ${total}  Válidas: ${valid}  Inválidas: ${invalid}`);
});
