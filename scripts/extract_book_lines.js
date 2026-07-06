"use strict";
/**
 * extract_book_lines.js — Extrai linhas de abertura validadas
 * do arquivo Damas_Knowledge_Base_Updated.md e converte para
 * o formato comprimido (char-pair) do book.js.
 *
 * Estratégia: extrai TODOS os tokens de notação algébrica do texto,
 * agrupa sequências contíguas e valida cada grupo contra o State.
 *
 * Uso:
 *   node scripts/extract_book_lines.js <caminho_para_knowledge_base.md>
 *     [--min-moves 4] [--max-moves 14] [--dedup]
 */

const fs = require('fs');
const { State } = require('../engine/state');

// ── Mapeamento interno do book.js ─────────────────────────────────────────
const DARK_SQUARES = [0,2,4,6,9,11,13,15,16,18,20,22,25,27,29,31,32,34,36,38,41,43,45,47,48,50,52,54,57,59,61,63];
const BOOK_ALPHA  = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdef';
const sqToChar     = Object.fromEntries(DARK_SQUARES.map((sq, i) => [sq, BOOK_ALPHA[i]]));
const charToSq     = Object.fromEntries(BOOK_ALPHA.split('').map((c, i) => [c, DARK_SQUARES[i]]));

// ── Opções ─────────────────────────────────────────────────────────────────
const MIN_MOVES = 4;   // min pairs (8 half-moves)
const MAX_MOVES = 12;  // max pairs (opening depth)

// ── Helpers ────────────────────────────────────────────────────────────────
const MOVE_RE = /\d*\s*\.\s*([a-hA-H][1-8][-x:][a-hA-H][1-8])/g;
// More general: find any token starting with optional digits+dot followed by algebraic
const TOKEN_RE = /(?:^|\s)(?:\d+\.\s*)*([a-hA-H][1-8][-x:][a-hA-H][1-8](?:[-x:][a-hA-H][1-8])*)/g;

function algToSq(sq) {
    if (!sq || sq.length < 2) return -1;
    const col = sq.toLowerCase().charCodeAt(0) - 97;
    const row = parseInt(sq[1], 10) - 1;
    if (col < 0 || col > 7 || row < 0 || row > 7) return -1;
    return row * 8 + col;
}

function tryMatchToken(state, token) {
    token = token.toLowerCase();
    const parts = token.split(/[-x:]/i);
    if (parts.length < 2) return null;
    const tokenFrom = algToSq(parts[0]);
    const tokenTo   = algToSq(parts[parts.length - 1]);
    if (tokenFrom < 0 || tokenTo < 0) return null;

    const moves = state.getMoves();

    // Exact match
    let match = moves.find(m => m.from === tokenFrom && m.to === tokenTo);
    if (match) return match;

    // Abbreviated capture: token shows only first hop
    const isCapture = /x/i.test(token);
    if (parts.length === 2 && isCapture) {
        const firstHop = tokenTo;
        match = moves.find(m => {
            if (m.from !== tokenFrom) return false;
            if (m.captured.length === 0) return false;
            return m.path.includes(firstHop);
        });
        if (match) return match;
    }

    return null;
}

function validateAndConvert(line) {
    // Extract all algebraic move tokens from the line
    const tokens = line.split(/\s+/);
    const cleanMoves = [];

    for (const tk of tokens) {
        if (!tk) continue;
        // Skip if it looks like a result or annotation
        if (/^[10]-\d|\*$/.test(tk)) continue;
        if (/^[{}()\[\]?!]+$/.test(tk)) continue;
        // Remove move number prefix
        let clean = tk.replace(/^\d+\.*/, '').trim();
        // Also handle "6-D4XB6" format (hyphen after number)
        clean = clean.replace(/^\d+-/, '').trim();
        if (!clean) continue;
        // Check if it matches algebraic notation
        if (!/^[a-hA-H][1-8]([-x:][a-hA-H][1-8])+$/i.test(clean)) continue;
        cleanMoves.push(clean);
    }

    if (cleanMoves.length < MIN_MOVES || cleanMoves.length > MAX_MOVES) return null;

    const s = new State();
    const pairs = [];

    for (const moveStr of cleanMoves) {
        const move = tryMatchToken(s, moveStr);
        if (!move) return null;
        const cf = sqToChar[move.from];
        const ct = sqToChar[move.to];
        if (!cf || !ct) return null;
        if (pairs.length === 0) {
            // Only first 4 moves are stored for the opening book
            // But we need the full sequence for validation
        }
        pairs.push(cf + ct);
        if (pairs.length >= MAX_MOVES) break;
        s.applyMove(move);
    }

    if (pairs.length < MIN_MOVES) return null;
    return pairs.join('');
}

// ── MAIN ────────────────────────────────────────────────────────────────────
const kbfile = process.argv[2];
if (!kbfile || !fs.existsSync(kbfile)) {
    console.error('Uso: node scripts/extract_book_lines.js <knowledge_base.md> [--dedup]');
    process.exit(1);
}

const dedup = process.argv.includes('--dedup');

const text = fs.readFileSync(kbfile, 'utf8');
const lines = text.split('\n');

let total = 0, valid = 0;

for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) continue;

    // Skip lines that don't look like they contain game notation
    // (must have at least one letter followed by digit + separator)
    if (!/[a-hA-H][1-8][-x:][a-hA-H]/.test(trimmed)) continue;

    const result = validateAndConvert(trimmed);
    if (result) {
        console.log(result);
        valid++;
    }
    total++;
}

const stats = { total, valid };
console.error(JSON.stringify(stats));
