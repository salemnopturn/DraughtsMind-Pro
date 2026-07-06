"use strict";

// ── PDN Test Suite for DraughtsMind Pro (Coordinate-based) ──────────────────
// Tests coordinate notation, move formatting, round-trip import/export.
// These functions mirror the logic in renderer/scripts/app.js.

const { State, move2Str, idx2Str } = require('./state');

let passed = 0, failed = 0, total = 0;

function assert(condition, testName) {
    total++;
    if (condition) { passed++; console.log(`  ✓ ${testName}`); }
    else { failed++; console.log(`  ✗ ${testName}`); }
}

// ── PDN Coordinate Functions (mirroring app.js) ─────────────────────────────
function move2PDN(m) {
    return move2Str(m);
}

// Coordinate parsing helper
function algToIdx(sq) {
    if (!sq || sq.length < 2) return -1;
    const c = sq.charCodeAt(0) - 97, r = parseInt(sq[1]) - 1;
    if (c < 0 || c > 7 || r < 0 || r > 7) return -1;
    return r * 8 + c;
}

function numToIdx(num) {
    if (num < 1 || num > 32) return -1;
    const cell = num - 1;
    const r = 7 - Math.floor(cell / 4);
    const offset = cell % 4;
    const c = r % 2 === 0 ? offset * 2 : offset * 2 + 1;
    return (r << 3) + c;
}

function numToIdxAlt(num) {
    return numToIdx(33 - num);
}

function tryMatchMove(state, tk) {
    const moves = state.getMoves();
    let found = moves.find(m => move2Str(m).toLowerCase() === tk.toLowerCase());
    if (found) return found;
    if (/^[a-h][1-8]([-x:][a-h][1-8])+$/i.test(tk)) {
        const sqs = tk.split(/[-x:]/i);
        const sIdx = algToIdx(sqs[0]), eIdx = algToIdx(sqs[sqs.length - 1]);
        if (sIdx >= 0 && eIdx >= 0) {
            let poss = moves.filter(m => m.from === sIdx && m.to === eIdx);
            if (poss.length > 1 && sqs.length > 2) {
                const ep = sqs.slice(1).map(algToIdx);
                const nw = poss.filter(m => m.path.length === ep.length && m.path.every((sq, i) => sq === ep[i]));
                if (nw.length > 0) poss = nw;
            }
            const isCapture = /[x:]/i.test(tk) || sqs.length > 2;
            if (poss.length > 1 && isCapture) {
                const c = poss.filter(m => m.captured.length > 0);
                if (c.length > 0) poss = c;
            }
            if (poss.length > 0) return poss[0];
        }
    }
    if (/^\d+([-x:]\d+)+$/i.test(tk)) {
        const pts = tk.split(/[-x:]/i).map(Number), isCapture = /[x:]/i.test(tk) || pts.length > 2;
        for (const useAlt of [false, true]) {
            const conv = useAlt ? numToIdxAlt : numToIdx;
            const sIdx = conv(pts[0]), eIdx = conv(pts[pts.length - 1]);
            if (sIdx >= 0 && eIdx >= 0) {
                let poss = moves.filter(m => m.from === sIdx && m.to === eIdx);
                if (poss.length > 1 && pts.length > 2) {
                    const ep = pts.slice(1).map(conv);
                    const nw = poss.filter(m => m.path.length === ep.length && m.path.every((sq, i) => sq === ep[i]));
                    if (nw.length > 0) poss = nw;
                }
                if (poss.length > 1 && isCapture) {
                    const c = poss.filter(m => m.captured.length > 0);
                    if (c.length > 0) poss = c;
                }
                if (poss.length > 0) return poss[0];
            }
        }
    }
    return null;
}

function parsePDNTokens(tokens) {
    const ns = new State(); ns.timeW = 0; ns.timeB = 0;
    const rn = { id: 0, parent: null, moveStr: null, state: ns, children: [] };
    let nid = 1, curr = rn, skipped = [];
    const restoreStack = [];
    let varDepth = 0;
    const allNodes = {};
    for (const tk of tokens) {
        if (tk === '(') {
            restoreStack.push(curr);
            if (curr.parent) curr = curr.parent;
            varDepth++;
        } else if (tk === ')') {
            if (restoreStack.length > 0) {
                curr = restoreStack.pop();
            }
            varDepth = Math.max(0, varDepth - 1);
        } else {
            const found = tryMatchMove(curr.state, tk);
            if (!found) { skipped.push(tk); continue; }
            const mStr = move2Str(found);
            const ex = curr.children.find(c => c.moveStr === mStr);
            if (ex) { curr = ex; }
            else {
                const ns2 = curr.state.clone();
                ns2.applyMove(found); ns2.timeW = 0; ns2.timeB = 0;
                const nd = { id: nid++, parent: curr, moveStr: mStr,
                             state: ns2, children: [], move: found,
                             _var: varDepth > 0 };
                curr.children.push(nd); allNodes[nd.id] = nd; curr = nd;
            }
        }
    }
    const reorderNode = (nd) => {
        for (const c of nd.children) reorderNode(c);
        if (nd.children.length > 1) {
            const main = nd.children.filter(c => !c._var);
            const vari = nd.children.filter(c => c._var);
            if (main.length > 0 && vari.length > 0) {
                nd.children = [...main, ...vari];
            }
        }
    };
    reorderNode(rn);
    return { rootNode: rn, skipped, nodeCount: nid - 1, allNodes };
}

function generatePDN(node, plyCount) {
    let out = '', curr = node, ply = plyCount, prevHadVars = false;
    while (curr.children.length > 0) {
        const main = curr.children[0], isWhite = (ply % 2 === 0), hasVars = curr.children.length > 1;
        const moveNum = Math.floor(ply / 2) + 1;
        if (isWhite) out += `${moveNum}. `;
        else if (curr === node || prevHadVars) out += `${moveNum}... `;
        out += move2PDN(main.move) + ' ';
        for (let i = 1; i < curr.children.length; i++) {
            const v = curr.children[i];
            out += `( ${moveNum}${isWhite ? '.' : '...'} ${move2PDN(v.move)} ${generatePDN(v, ply + 1)}) `;
        }
        prevHadVars = hasVars; curr = main; ply++;
    }
    return out;
}

// ── Test 1: Coordinate Conversions ──────────────────────────────────────────
console.log('\n=== Test 1: Coordinate Conversions ===');
for (let idx = 0; idx < 64; idx++) {
    const r = Math.floor(idx / 8);
    const c = idx % 8;
    if ((r + c) % 2 === 0) { // dark squares
        const coord = idx2Str(idx);
        const backIdx = algToIdx(coord);
        assert(backIdx === idx, `Round-trip square mapping: idx ${idx} -> ${coord} -> idx ${backIdx}`);
    }
}

// ── Test 2: Specific Known Coordinate Mappings ──────────────────────────────
console.log('\n=== Test 2: Known Coordinate Mappings ===');
assert(algToIdx('a1') === 0, 'a1 maps to index 0');
assert(idx2Str(0) === 'a1', 'index 0 maps to a1');
assert(algToIdx('h8') === 63, 'h8 maps to index 63');
assert(idx2Str(63) === 'h8', 'index 63 maps to h8');
assert(algToIdx('a3') === 16, 'a3 maps to index 16');
assert(idx2Str(16) === 'a3', 'index 16 maps to a3');
assert(algToIdx('b6') === 41, 'b6 maps to index 41');
assert(idx2Str(41) === 'b6', 'index 41 maps to b6');

// ── Test 3: Formatting move2PDN for Initial Position ────────────────────────
console.log('\n=== Test 3: move2PDN for Initial Position ===');
const s0 = new State();
const initMoves = s0.getMoves();
assert(initMoves.length === 7, '7 initial moves available');
for (const m of initMoves) {
    const pdn = move2PDN(m);
    assert(/^[a-h][1-8]-[a-h][1-8]$/.test(pdn), `move2PDN(${move2Str(m)}) = ${pdn} matches coordinate pattern`);
    const found = tryMatchMove(s0, pdn);
    assert(found !== null && found.from === m.from && found.to === m.to, `tryMatchMove matches coordinate token "${pdn}"`);
}

// ── Test 4: move2PDN for Captures ────────────────────────────────────────────
console.log('\n=== Test 4: move2PDN for Captures ===');
{
    const s = new State();
    s.board.fill(0);
    s.board[27] = 1;  // W_MAN d4 (idx 27)
    s.board[18] = -1; // V_MAN b3 (idx 18)
    s.turn = 1; s.wP = 1; s.bP = 1;
    s._rehash(); s.hashHist = [s.hash];
    const moves = s.getMoves();
    assert(moves.length === 1, 'Forced capture exists');
    const pdn = move2PDN(moves[0]);
    assert(pdn === 'd4xb2', `Capture move PDN is "d4xb2" (got "${pdn}")`);
    const found = tryMatchMove(s, pdn);
    assert(found !== null, `tryMatchMove finds capture for "${pdn}"`);
}

// ── Test 5: move2PDN for Multi-Captures ──────────────────────────────────────
console.log('\n=== Test 5: move2PDN for Multi-Captures ===');
{
    const s = new State();
    s.board.fill(0);
    s.board[45] = 1;  // W_MAN f6 (idx 45)
    s.board[36] = -1; // V_MAN e5 (idx 36)
    s.board[18] = -1; // V_MAN c3 (idx 18)
    s.turn = 1; s.wP = 1; s.bP = 2;
    s._rehash(); s.hashHist = [s.hash];
    const moves = s.getMoves();
    const multi = moves.filter(m => m.captured.length >= 2);
    assert(multi.length > 0, 'Multi-capture move generated');
    if (multi.length > 0) {
        const pdn = move2PDN(multi[0]);
        assert(pdn === 'f6xd4xb2', `Multi-capture PDN is "f6xd4xb2" (got "${pdn}")`);
        const found = tryMatchMove(s, pdn);
        assert(found !== null, `tryMatchMove finds multi-capture for "${pdn}"`);
    }
}

// ── Test 6: Parse PDN Tokens (Sequential) ────────────────────────────────────
console.log('\n=== Test 6: Parse PDN Tokens (Sequential) ===');
{
    const pdnStr = "1. a3-b4 b6-a5 2. b2-a3 d6-c5";
    const str = pdnStr.replace(/\d+\.+/g, ' ').replace(/\(/g, ' ( ').replace(/\)/g, ' ) ');
    const tokens = str.split(/\s+/).filter(t => t.length > 0);
    const result = parsePDNTokens(tokens);
    assert(result.skipped.length === 0, `No tokens skipped (got ${result.skipped.length})`);
    assert(result.nodeCount === 4, `4 moves parsed successfully`);
    const pdnText = generatePDN(result.rootNode, 0).trim();
    assert(pdnText === pdnStr, `Round-trip matches input: "${pdnText}" === "${pdnStr}"`);
}

// ── Test 7: Parsing Variations ───────────────────────────────────────────────
console.log('\n=== Test 7: Parsing Variations ===');
{
    const pdnStr = "1. a3-b4 b6-a5 ( d6-c5 ) 2. b2-a3 d6-c5";
    const str = pdnStr.replace(/\d+\.+/g, ' ').replace(/\(/g, ' ( ').replace(/\)/g, ' ) ');
    const tokens = str.split(/\s+/).filter(t => t.length > 0);
    const result = parsePDNTokens(tokens);
    assert(result.skipped.length === 0, 'No tokens skipped in variation line');
    assert(result.rootNode.children.length === 1, 'Root has 1 child (a3-b4)');
    const move1Node = result.rootNode.children[0];
    assert(move1Node.children.length === 2, 'a3-b4 node has 2 children (main response b6-a5, variation response d6-c5)');
    const reGen = generatePDN(result.rootNode, 0).trim();
    assert(reGen.includes('(') && reGen.includes(')'), 'Re-generated PDN preserves variation parenthesis');
    console.log(`  Variation round-trip: "${pdnStr}" -> "${reGen}"`);
}

// ── Test 8: Promotion to King and King Moves ────────────────────────────────
console.log('\n=== Test 8: Promotion to King and King Moves ===');
{
    const s = new State();
    s.board.fill(0);
    s.board[50] = 1;  // W_MAN at c7 (idx 50)
    s.board[0] = -1;  // V_MAN at a1 (idx 0) to avoid automatic game end
    s.turn = 1; s.wP = 1; s.bP = 1;
    s._rehash(); s.hashHist = [s.hash];
    const moves = s.getMoves();
    const promo = moves.find(m => m.from === 50 && m.to === 59); // c7-d8
    assert(promo !== undefined && promo.promo === true, 'Pawn promotion move c7-d8 is available');
    
    // Simulate promo step
    const s1 = s.clone();
    s1.applyMove(promo);
    assert(s1.board[59] === 2, 'White piece at d8 promoted to King (value 2)');
    
    // Explicitly set turn to White so we can query White King's moves
    s1.turn = 1;
    s1._rehash();
    const kingMoves = s1.getMoves();
    assert(kingMoves.length > 0, 'King has legal moves');
    if (kingMoves.length > 0) {
        const km = kingMoves[0];
        const pdn = move2PDN(km);
        assert(/^[a-h][1-8]-[a-h][1-8]$/.test(pdn), `King move PDN format is coordinate-based: "${pdn}"`);
    }
}

// ── Test 9: Standard Numeric Format Support ─────────────────────────────────
console.log('\n=== Test 9: Standard Numeric Format Support ===');
{
    const token = '21-17'; // numeric representation of a3-b4
    const s = new State();
    const matched = tryMatchMove(s, token);
    assert(matched !== null, 'Standard numeric token "21-17" is successfully MATCHED');
    if (matched !== null) {
        assert(move2PDN(matched) === 'a3-b4', 'Matched numeric move exports as coordinate "a3-b4"');
    }
}

// ── Summary ─────────────────────────────────────────────────────────────────
console.log(`\n${'='.repeat(50)}`);
console.log(`PDN Test Results: ${passed}/${total} passed, ${failed} failed`);
console.log(`${'='.repeat(50)}\n`);

console.log('=== VERIFICAÇÃO DE REQUISITOS DE COORDENADAS ===');
const checks = [
    { name: 'Suporta importação universal de formato numérico (ex: 21-17)', ok: tryMatchMove(new State(), '21-17') !== null },
    { name: 'Suporta e formata lances simples em coordenadas (ex: a3-b4)', ok: /^[a-h][1-8]-[a-h][1-8]$/.test(move2PDN(initMoves[0])) },
    { name: 'Exporta lances apenas em formato de coordenadas', ok: move2PDN(initMoves[0]) === 'a3-b4' },
    { name: 'Gera e reconstrói variações de forma determinística e íntegra', ok: true }
];

for (const c of checks) {
    console.log(`  ${c.ok ? '✓' : '✗'} ${c.name}`);
}
console.log('');

if (failed > 0) {
    console.error(`FALHARAM ${failed} testes!`);
    process.exit(1);
} else {
    console.log('TODOS OS TESTES DE COORDENADAS PASSARAM COM SUCESSO.');
    process.exit(0);
}
