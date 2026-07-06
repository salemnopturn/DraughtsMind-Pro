"use strict";
/**
 * convert_pdn_book.js — Converte linhas de abertura (notação algébrica)
 * para o formato comprimido (char-pair) usado pelo book.js do DraughtsMind Pro.
 *
 * Suporta notação abreviada de capturas: "a5xc7" é aceito mesmo que o motor
 * encontre uma captura múltipla (ex: a5xc7xe5xg3).
 *
 * Uso:
 *   node scripts/convert_pdn_book.js < arquivo_com_lances.txt
 *
 * Cada linha deve conter uma sequência de lances em notação algébrica.
 * Linhas comentadas (#) ou vazias são ignoradas.
 */

const { State } = require('../engine/state');

// ── Mapeamento interno do book.js ─────────────────────────────────────────
const DARK_SQUARES = [0,2,4,6,9,11,13,15,16,18,20,22,25,27,29,31,32,34,36,38,41,43,45,47,48,50,52,54,57,59,61,63];
const BOOK_ALPHA  = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdef';
const sqToChar     = Object.fromEntries(DARK_SQUARES.map((sq, i) => [sq, BOOK_ALPHA[i]]));
const charToSq     = Object.fromEntries(BOOK_ALPHA.split('').map((c, i) => [c, DARK_SQUARES[i]]));

// ── Conversão algébrica → índice interno ─────────────────────────────────
function algToSq(sq) {
    if (!sq || sq.length < 2) return -1;
    const col = sq.toLowerCase().charCodeAt(0) - 97; // a=0 … h=7
    const row = parseInt(sq[1], 10) - 1; // 1→0 … 8→7
    if (col < 0 || col > 7 || row < 0 || row > 7) return -1;
    return row * 8 + col;
}

// ── Tenta casar um token algébrico com um movimento legal ─────────────────
// Aceita tanto notação completa ("a5xc7xe5xg3") quanto abreviada ("a5xc7").
// Retorna o objeto MOVE (que pode ter path maior que o token) ou null.
function tryMatchToken(state, token) {
    token = token.toLowerCase();
    const parts = token.split(/[-x:]/i);
    if (parts.length < 2) return null;
    const tokenFrom = algToSq(parts[0]);
    const tokenTo   = algToSq(parts[parts.length - 1]);
    if (tokenFrom < 0 || tokenTo < 0) return null;

    const moves = state.getMoves();

    // 1) Tenta casamento exato (from + to)
    let match = moves.find(m => m.from === tokenFrom && m.to === tokenTo);
    if (match) return match;

    // 2) Captura abreviada: o token mostra só o primeiro destino (ex: a5xc7)
    //    mas o motor achou uma captura maior (ex: a5xc7xe5xg3).
    //    Procura qualquer captura partindo de tokenFrom cujo path contenha tokenTo.
    const isCapture = /x/i.test(token);
    if (parts.length === 2 && isCapture) {
        // parts[0]=from, parts[1]=firstHopDest
        const firstHop = tokenTo;
        match = moves.find(m => {
            if (m.from !== tokenFrom) return false;
            if (m.captured.length === 0) return false;
            // O token mostra até o primeiro destino da captura
            // Verifica se tokenTo está no início do path
            for (let i = 0; i < m.path.length; i++) {
                const p = m.path[i];
                // Para captura, o caminho tem tamanho 1 ou mais
                // Se achou tokenTo em alguma posição, é compatível
                if (p === firstHop) return true;
            }
            return false;
        });
        if (match) return match;
    }

    return null;
}

// ── Converte linha completa de lances algébricos → string comprimida ────
function convertLine(line) {
    const tokens = line.trim().split(/\s+/);
    const pairs = [];
    const s = new State();
    for (const tk of tokens) {
        if (!tk || /[{}()\[\]?!]/.test(tk)) continue;
        // Remove números de lances (ex: "1.", "1...") e marcadores de resultado
        const clean = tk.replace(/^\d+\.*/, '').trim();
        if (!clean || /^[10]-\d|\*$/.test(clean)) continue;
        // Só processa tokens que parecem notação algébrica
        if (!/^[a-hA-H][1-8]([-x:][a-hA-H][1-8])+$/i.test(clean)) continue;

        const move = tryMatchToken(s, clean);
        if (!move) return null; // linha inválida

        const cf = sqToChar[move.from];
        const ct = sqToChar[move.to];
        if (!cf || !ct) return null;
        pairs.push(cf + ct);
        s.applyMove(move);
    }
    return pairs.join('');
}

// ── MAIN ─────────────────────────────────────────────────────────────────
const readline = require('readline');
const rl = readline.createInterface({ input: process.stdin });

let total = 0, valid = 0, invalid = 0;

rl.on('line', (line) => {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) return;
    total++;
    const compressed = convertLine(trimmed);
    if (!compressed || compressed.length < 2) {
        invalid++;
        return;
    }
    console.log(compressed);
    valid++;
});

rl.on('close', () => {
    console.error(`\nProcessadas: ${total}  Válidas: ${valid}  Inválidas: ${invalid}`);
});
