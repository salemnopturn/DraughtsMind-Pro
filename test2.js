const fs = require('fs');
const appJsCode = fs.readFileSync('renderer/scripts/app.js', 'utf8');

// We just need the State class
let stateClass = appJsCode.substring(appJsCode.indexOf('class State {'), appJsCode.indexOf('// ════════════════════════════════════════════════════════════════════════\n    //  TABELA DE TRANSPOSIÇÃO'));

const script = `
const EMPTY = 0, W_MAN = 1, V_MAN = -1, W_KING = 2, V_KING = -2;
const M64 = 0xFFFFFFFFFFFFFFFFn;
const CENTER_BIG = new Set([27, 28, 35, 36]);
const CENTER_SM = new Set([18, 21, 42, 45]);
const PST_M = new Int32Array(64);
const PST_K = new Int32Array(64);
const ZP_SIZE = 64 * 5;
const zp = new BigInt64Array(ZP_SIZE);
for(let i=0; i<ZP_SIZE; i++) zp[i] = BigInt(Math.floor(Math.random() * 1000000000));
const zt = 123456789n;
function getPieceIdx(p) {
    if (p === 1) return 0;
    if (p === -1) return 1;
    if (p === 2) return 2;
    if (p === -2) return 3;
    return 4;
}
function idx2Str(i) { return String.fromCharCode(97+(i&7)) + ((i>>3)+1); }
function move2Str(m) {
    let s = idx2Str(m.from);
    if (m.captured.length > 0) for (const p of m.path) s += "x" + idx2Str(p);
    else s += "-" + idx2Str(m.to);
    return s;
}
function algToIdx(sq) {
    if (!sq || sq.length < 2) return -1;
    const c = sq.charCodeAt(0) - 97, r = parseInt(sq[1]) - 1;
    if (c < 0 || c > 7 || r < 0 || r > 7) return -1;
    return r * 8 + c;
}

let movePool = [];
for (let i = 0; i < 2000; i++) movePool.push({ from: 0, to: 0, path: [], captured: [], capKings: 0, promo: false, score: 0 });
let movePoolPos = 0;
function allocMv() {
    if (movePoolPos >= movePool.length) movePool.push({ from: 0, to: 0, path: [], captured: [], capKings: 0, promo: false, score: 0 });
    const m = movePool[movePoolPos++];
    m.path = []; m.captured = []; m.capKings = 0; m.promo = false; m.score = 0;
    return m;
}
function saveMP() { return movePoolPos; }
function restoreMP(p) { movePoolPos = p; }

${stateClass}

const s = new State();
const moves = s.getMoves();
const m1 = moves.find(m => move2Str(m) === 'c3-b4');
if (m1) {
    s.applyMove(m1);
    console.log("Applied c3-b4");
    const m2List = s.getMoves();
    console.log("Black moves after c3-b4:", m2List.map(move2Str));
}
`;
fs.writeFileSync('test_run_2.js', script);
