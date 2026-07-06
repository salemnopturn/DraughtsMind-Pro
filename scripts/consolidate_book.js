"use strict";

const fs = require('fs');
const path = require('path');
const { State } = require('../engine/state');
const book = require('../engine/book');

// ── Internal book mapping ──────────────────────────────────────────────────
const DARK_SQUARES = [0,2,4,6,9,11,13,15,16,18,20,22,25,27,29,31,32,34,36,38,41,43,45,47,48,50,52,54,57,59,61,63];
const BOOK_ALPHA  = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdef';
const sqToChar     = Object.fromEntries(DARK_SQUARES.map((sq, i) => [sq, BOOK_ALPHA[i]]));
const charToSq     = Object.fromEntries(BOOK_ALPHA.split('').map((c, i) => [c, DARK_SQUARES[i]]));

function algToSq(sq) {
    if (!sq || sq.length < 2) return -1;
    const col = sq.toLowerCase().charCodeAt(0) - 97;
    const row = parseInt(sq[1], 10) - 1;
    if (col < 0 || col > 7 || row < 0 || row > 7) return -1;
    return row * 8 + col;
}

// Universal move matcher matching tryMatchToken in extract_book_lines.js
function tryMatchToken(state, token) {
    token = token.toLowerCase();
    const parts = token.split(/[-x:]/i);
    if (parts.length < 2) return null;
    const tokenFrom = algToSq(parts[0]);
    const tokenTo   = algToSq(parts[parts.length - 1]);
    if (tokenFrom < 0 || tokenTo < 0) return null;

    const moves = state.getMoves();
    let match = moves.find(m => m.from === tokenFrom && m.to === tokenTo);
    if (match) return match;

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

// Convert an algebraic PDN line to compressed char-pair format
function convertPdnLine(line) {
    const tokens = line.split(/\s+/);
    const cleanMoves = [];
    for (const tk of tokens) {
        if (!tk || /^[10]-\d|\*$/.test(tk) || /^[{}()\[\]?!]+$/.test(tk)) continue;
        let clean = tk.replace(/^\d+\.*/, '').trim().replace(/^\d+-/, '').trim();
        if (!clean || !/^[a-hA-H][1-8]([-x:][a-hA-H][1-8])+$/i.test(clean)) continue;
        cleanMoves.push(clean);
    }
    const s = new State();
    const pairs = [];
    for (const moveStr of cleanMoves) {
        const move = tryMatchToken(s, moveStr);
        if (!move) break; // Truncate at first invalid/illegal move
        const cf = sqToChar[move.from];
        const ct = sqToChar[move.to];
        if (!cf || !ct) break;
        pairs.push(cf + ct);
        s.applyMove(move);
    }
    return pairs.join('');
}

// Validate a compressed char-pair line from the starting position
function validateCompressedLine(line) {
    const s = new State();
    const validPairs = [];
    for (let i = 0; i < line.length - 1; i += 2) {
        const fsq = charToSq[line[i]];
        const tsq = charToSq[line[i + 1]];
        if (fsq === undefined || tsq === undefined) break;
        const moves = s.getMoves();
        const found = moves.find(m => m.from === fsq && m.to === tsq);
        if (!found) break; // Truncate at first invalid move
        validPairs.push(line[i] + line[i + 1]);
        s.applyMove(found);
    }
    return validPairs.join('');
}

function main() {
    const allLines = new Set();

    // 1. Load existing BOOK_DATA
    const existingBookData = book.BOOK_DATA.split('|');
    console.error(`Loaded ${existingBookData.length} lines from existing BOOK_DATA`);
    for (const line of existingBookData) {
        if (line.length >= 4) allLines.add(line);
    }

    // 2. Load existing BOOK_DATA_EXT
    const existingBookDataExt = book.BOOK_DATA_EXT.split('|');
    console.error(`Loaded ${existingBookDataExt.length} lines from existing BOOK_DATA_EXT`);
    for (const line of existingBookDataExt) {
        if (line.length >= 4) allLines.add(line);
    }

    // 3. Load existing PDN_EXTRA_LINES and convert them
    console.error(`Converting ${book.PDN_EXTRA_LINES.length} lines from existing PDN_EXTRA_LINES`);
    for (const pdnLine of book.PDN_EXTRA_LINES) {
        const comp = convertPdnLine(pdnLine);
        if (comp.length >= 4) allLines.add(comp);
    }

    // 4. Load newly extracted lines from Damas_Knowledge_Base_Updated.md
    const extFile = path.join(__dirname, '..', 'extracted_lines.txt');
    if (fs.existsSync(extFile)) {
        const extContent = fs.readFileSync(extFile, 'utf8');
        const extLines = extContent.split('\n');
        console.error(`Loaded ${extLines.length} lines from extracted_lines.txt`);
        for (const line of extLines) {
            const trimmed = line.trim();
            if (trimmed.length >= 4) allLines.add(trimmed);
        }
    } else {
        console.error("Warning: extracted_lines.txt not found");
    }

    console.error(`Total unique candidates collected: ${allLines.size}`);

    // 5. Validate and filter all lines
    const validatedLines = new Set();
    for (const line of allLines) {
        const validated = validateCompressedLine(line);
        // We require at least 2 moves (4 plies, 8 characters) for a useful opening line
        if (validated.length >= 8) {
            validatedLines.add(validated);
        }
    }

    console.error(`Total valid lines after engine verification: ${validatedLines.size}`);

    // 6. Split into base book and extended book
    // Base book: lines of length exactly 8 or 12 characters (short lines) or first N lines
    // Let's sort lines by length and then alphabetically to be deterministic
    const sortedLines = [...validatedLines].sort((a, b) => {
        if (a.length !== b.length) return a.length - b.length;
        return a.localeCompare(b);
    });

    // We can split: first 800 lines (or lines of length <= 16 chars) into BOOK_DATA
    // and the rest into BOOK_DATA_EXT
    const baseBook = [];
    const extBook = [];
    for (const line of sortedLines) {
        if (line.length <= 16) {
            baseBook.push(line);
        } else {
            extBook.push(line);
        }
    }

    console.error(`Split: baseBook (BOOK_DATA) has ${baseBook.length} lines`);
    console.error(`Split: extBook (BOOK_DATA_EXT) has ${extBook.length} lines`);

    const result = {
        BOOK_DATA: baseBook.join('|'),
        BOOK_DATA_EXT: extBook.join('|')
    };

    // Output JSON string
    console.log(JSON.stringify(result, null, 2));
}

main();
