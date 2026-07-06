const fs = require('fs');
const appJsCode = fs.readFileSync('renderer/scripts/app.js', 'utf8');

// We just need the State class and generatePDN logic
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

const DIRS_ALL = [[1,1],[1,-1],[-1,1],[-1,-1]];
const DIRS_W = [[1,1],[1,-1]];
const DIRS_B = [[-1,1],[-1,-1]];
const NO_CAPTURES = [];

let movePool = [];
for (let i = 0; i < 2000; i++) movePool.push({ from: 0, to: 0, path: [], captured: [], capKings: 0, promo: false, score: 0 });
let movePoolPos = 0;
function allocMv(from, to, path, captured, promo, isPawn, capKings) {
    if (movePoolPos >= movePool.length) movePool.push({ from: 0, to: 0, path: [], captured: [], capKings: 0, promo: false, score: 0 });
    const m = movePool[movePoolPos++];
    m.from = from; m.to = to; m.path = path||[]; m.captured = captured||[]; m.capKings = capKings||0; m.promo = promo||false; m.score = 0;
    return m;
}

` + stateClass + `

const s = new State();
const moves = s.getMoves();
const m1 = moves.find(m => move2Str(m) === 'c3-d4');
s.applyMove(m1);
const m2List = s.getMoves();
const m2 = m2List.find(m => move2Str(m) === 'f6-e5');
s.applyMove(m2);

console.log("Game successfully simulated to some point.");
`;
fs.writeFileSync('test_pdn.js', script);
