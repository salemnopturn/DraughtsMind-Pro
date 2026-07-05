"use strict";

const { State, move2Str, saveMP, restoreMP } = require('./state');
const { getBestMove, abortSearch } = require('./search');
const { ENGINE_VERSION } = require('./constants');

let passed = 0, failed = 0, total = 0;

function assert(condition, testName) {
    total++;
    if (condition) {
        passed++;
        console.log(`  ✓ ${testName}`);
    } else {
        failed++;
        console.log(`  ✗ ${testName}`);
    }
}

function testBasicPosition() {
    console.log('\n=== Test: Basic Position ===');
    const s = new State();
    assert(s.turn === 1, 'White starts');
    assert(s.wP === 12, 'White has 12 pawns');
    assert(s.bP === 12, 'Red has 12 pawns');
    assert(s.wK === 0, 'White has 0 kings');
    assert(s.bK === 0, 'Red has 0 kings');
    const moves = s.getMoves();
    assert(moves.length === 7, 'Initial position has 7 legal moves');
}

function testForcedCapture() {
    console.log('\n=== Test: Forced Capture ===');
    const s = new State();
    s.board.fill(0);
    s.board[27] = 1;  // W_MAN at d4
    s.board[18] = -1; // V_MAN at b3
    s.turn = 1;
    s.wP = 1; s.bP = 1;
    s._rehash();
    s.hashHist = [s.hash];
    const moves = s.getMoves();
    assert(moves.length === 1, 'Forced capture: only 1 move available');
    assert(moves[0].captured.length === 1, 'Capture contains 1 piece');
}

function testMultiJump() {
    console.log('\n=== Test: Multi-Jump ===');
    const s = new State();
    s.board.fill(0);
    // W_MAN at f3 (index 45), capture V_MAN at e4 (index 36), land d5 (index 27),
    // then capture V_MAN at c5 (index 18), land b7 (index 9)
    s.board[45] = 1;  // W_MAN at f3
    s.board[36] = -1; // V_MAN at e4
    s.board[18] = -1; // V_MAN at c5
    s.turn = 1;
    s.wP = 1; s.bP = 2;
    s._rehash();
    s.hashHist = [s.hash];
    const moves = s.getMoves();
    const multiCaptures = moves.filter(m => m.captured.length >= 2);
    assert(multiCaptures.length > 0, 'Multi-jump available');
}

function testPromotion() {
    console.log('\n=== Test: Promotion ===');
    const s = new State();
    s.board.fill(0);
    s.board[50] = 1;  // W_MAN at f7
    s.turn = 1;
    s.wP = 1;
    s._rehash();
    s.hashHist = [s.hash];
    const moves = s.getMoves();
    const promoMoves = moves.filter(m => m.promo);
    assert(promoMoves.length > 0, 'Promotion move available');
}

function testKingMovement() {
    console.log('\n=== Test: King Movement ===');
    const s = new State();
    s.board.fill(0);
    s.board[27] = 2;  // W_KING at d4
    s.turn = 1;
    s.wK = 1;
    s._rehash();
    s.hashHist = [s.hash];
    const moves = s.getMoves();
    assert(moves.length === 13, 'King in center has 13 moves');
}

function testDrawDetection() {
    console.log('\n=== Test: Draw Detection ===');
    const s = new State();
    s.halfMoveClock = 40;
    const draw = s.checkDraw();
    assert(draw !== false, '20-move rule triggers draw');
}

function testEval() {
    console.log('\n=== Test: Evaluation ===');
    const s = new State();
    const eval1 = s.eval();
    assert(typeof eval1 === 'number', 'Eval returns a number');
    assert(eval1 === 0 || Math.abs(eval1) < 100, 'Initial position is roughly equal');
}

function testSearch() {
    console.log('\n=== Test: Search (depth 4) ===');
    const s = new State();
    const result = getBestMove(s, 4, 5000, null);
    assert(result.move !== null, 'Search finds a move');
    assert(result.depth >= 1, 'Search reaches at least depth 1');
    assert(result.nodes > 0, 'Search visits nodes');
}

function testClone() {
    console.log('\n=== Test: Clone ===');
    const s = new State();
    const c = s.clone();
    assert(c.turn === s.turn, 'Clone has same turn');
    assert(c.hash === s.hash, 'Clone has same hash');
    assert(c.wP === s.wP, 'Clone has same white pawns');
    assert(c.bP === s.bP, 'Clone has same red pawns');
}

function testFEN() {
    console.log('\n=== Test: FEN ===');
    const s = new State();
    const fen = s.toFEN();
    assert(fen.includes('/'), 'FEN contains slashes');
    const s2 = new State();
    s2.loadFEN(fen);
    assert(s2.turn === s.turn, 'FEN round-trip preserves turn');
    assert(s2.hash === s.hash, 'FEN round-trip preserves hash');
}

function testMoveGeneration() {
    console.log('\n=== Test: Move Generation ===');
    const s = new State();
    const moves = s.getMoves();
    for (const m of moves) {
        assert(m.from >= 0 && m.from < 64, `Move from is valid: ${m.from}`);
        assert(m.to >= 0 && m.to < 64, `Move to is valid: ${m.to}`);
    }
}

console.log(`\n${'='.repeat(50)}`);
console.log(`DraughtsMind Pro Engine Tests v${ENGINE_VERSION}`);
console.log(`${'='.repeat(50)}`);

testBasicPosition();
testForcedCapture();
testMultiJump();
testPromotion();
testKingMovement();
testDrawDetection();
testEval();
testSearch();
testClone();
testFEN();
testMoveGeneration();

console.log(`\n${'='.repeat(50)}`);
console.log(`Results: ${passed}/${total} passed, ${failed} failed`);
console.log(`${'='.repeat(50)}\n`);

process.exit(failed > 0 ? 1 : 0);
