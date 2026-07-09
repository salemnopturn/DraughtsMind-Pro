window.onerror = function(message, source, lineno, colno, error) { console.error('Global Error:', message, source, lineno, colno, error); };
"use strict";
// ══════════════════════════════════════════════════════════════════════════════
//  DraughtsMind v31.2 — Knowledge Base Integration
//  Damas Brasileiras (CBD, 8×8), 100% offline, HTML único.
//
//  Engine: PVS+LMR+NMP+IID+qsearch, Zobrist 64-bit BigInt,
//  TT compacta 262K (Uint32Array 2-way), PST+centro+borda eval
//
//  UI: Board Editor, PDN import/export, análise, relógio, histórico
//  Book: +3100 linhas maximais com softmax adaptativo
// ══════════════════════════════════════════════════════════════════════════════

    const ENGINE_VERSION = "32.0.0";
    const EMPTY = 0, W_MAN = 1, V_MAN = -1, W_KING = 2, V_KING = -2;
    const NO_CAPTURES = [];
    const DIRS_ALL = [[1,1],[1,-1],[-1,1],[-1,-1]];
    const DIRS_W = [[1,1],[1,-1]];
    const DIRS_B = [[-1,1],[-1,-1]];
    const LMP_TABLE = [0, 5, 9, 15, 22, 30];
    const MODE_HVH = 0, MODE_HVM = 1, MODE_MVH = 2, MODE_MVM = 3, MODE_SAND = 4, MODE_TABLITA = 5;

    // Move object pool (stack allocator)
    const movePool = [];
    let movePoolPos = 0;
    function saveMP() { return movePoolPos; }
    function restoreMP(pos) { movePoolPos = pos; }
    function allocMv(from, to, path, captured, promo, isPawn, capKings) {
        let m;
        if (movePoolPos < movePool.length) { m = movePool[movePoolPos]; }
        else { m = {}; movePool.push(m); }
        movePoolPos++;
        m.from = from; m.to = to; m.path = path; m.captured = captured;
        m.promo = promo; m.isPawn = isPawn; m.capKings = capKings;
        return m;
    }

    function cloneMv(m) {
        if (!m) return null;
        return {
            from: m.from, to: m.to,
            path: m.path ? m.path.slice() : [],
            captured: m.captured ? m.captured.slice() : [],
            capKings: m.capKings || 0,
            promo: m.promo || false,
            score: m.score || 0
        };
    }

    let cfgDepth = 10, cfgMode = MODE_HVM, cfgView = 'W', isAnalysisOn = false; // [FIX-V31-DEPTH] padrão 10
    let isComputing = false, gameEnded = false, gameStarted = false, gameResultType = null;
    let editMode = false, editStartTurn = 1, ttGen = 0;
    let timeLimit = 0, timeW = 0, timeB = 0;

    // [ENG-V18-3] Memória e continuidade estratégica da partida.
    // Registra a trajetória de cada posição: material, mobilidade, fase e desvio de plano.
    let gameTrajectory = [];  // { plyIndex, material, totalPieces, phase, mobBalance }
    let trajectoryPhase = 'opening'; // 'opening' | 'middlegame' | 'endgame'
    // NOTE (v21): trajectoryPhase is now ONLY used for UI display and trajectory tracking,
    // not inside eval(). The eval() uses local position-based phase detection instead.
    const TRAJ_MAX = 120;            // máximo de entradas mantidas (60 lances completos)

    // [V21-STATS] CPU × CPU statistics tracker
    const cpuStats = { wWins: 0, bWins: 0, draws: 0, games: 0 };
    function updateCpuStats(result) {
        // result: 'w' = white wins, 'b' = black wins, 'd' = draw
        cpuStats.games++;
        if (result === 'w') cpuStats.wWins++;
        else if (result === 'b') cpuStats.bWins++;
        else cpuStats.draws++;
        const el = document.getElementById('cpu-stats');
        if (el) {
            el.innerHTML = `<span style="color:#4a9;">⚪${cpuStats.wWins}</span> `
                + `<span style="color:#888;">½${cpuStats.draws}</span> `
                + `<span style="color:#e76;">⚫${cpuStats.bWins}</span> `
                + `<span style="color:#aaa;">(${cpuStats.games} jg)</span>`;
        }
    }

    let clockInterval  = null;
    let clockLastStamp = 0;

    // [ENG-V24-SYNC] Sinergia de Transição Livro→Motor:
    // Rastreia quantos lances consecutivos foram jogados FORA da teoria.
    // Nos primeiros 2 lances fora do livro, triggerCPU usa cfgDepth+1 (Overclock).
    let nonBookPlyCount = 0;

    let rootNode, currentNode, allNodes = {}, nextNodeId = 1;
    let pendingBranchMove = null;

    // Tablita mode state
    let tablitaGameNum = 1;
    let tablitaMatchScore = { w: 0, b: 0 };
    const TABLITA_MAX_GAMES = 2;
    let tablitaSubMode = MODE_HVH; // sub-mode within Tablita (0-4)
    let tablitaManager = null;     // TablitaManager instance when match active
    let tablitaGameInProgress = false; // Track if a Tablita game is actually in progress

    // ════════════════════════════════════════════════════════════════════════
    //  TABLITAS — Official Tablita definitions (derived from opening book)
    // ════════════════════════════════════════════════════════════════════════
    const TABLITAS = [
        { name: 'Clássica',    moves: ['c3-d4', 'd6-c5'] },
        { name: 'Cruz',    moves: ['c3-d4', 'd6-e5'] },
        { name: 'Cruz JV', moves: ['c3-d4', 'd6-e5', 'b2-c3', 'e7-d6'] },
        { name: 'Pioneiro',    moves: ['c3-d4', 'b6-c5'] },
        { name: 'Pioneiro NU', moves: ['c3-d4', 'b6-c5', 'd4xb6', 'a7xc5'] },
        { name: 'Flank',    moves: ['c3-d4', 'f6-g5'] },
        { name: 'Flank NR', moves: ['c3-d4', 'f6-g5', 'd4-c5', 'd6xb4'] },
        { name: 'Russa',    moves: ['c3-b4'] },
        { name: 'Russa WS', moves: ['c3-b4', 'f6-e5'] },
        { name: 'Russa UR', moves: ['c3-b4', 'b6-c5'] },
        { name: 'Russa VS', moves: ['c3-b4', 'd6-e5'] },
        { name: 'Russa XT', moves: ['c3-b4', 'h6-g5'] },
        { name: 'Russa WT', moves: ['c3-b4', 'f6-g5'] },
        { name: 'Russa MQ', moves: ['c3-b4', 'b6-a5'] },
        { name: 'g3-f4 VS', moves: ['g3-f4', 'd6-e5'] },
        { name: 'g3-f4 WT', moves: ['g3-f4', 'f6-g5'] },
        { name: 'g3-h4 VS', moves: ['g3-h4', 'd6-e5'] },
        { name: 'Cruz Profunda',   moves: ['c3-d4', 'd6-e5', 'b2-c3', 'e7-d6', 'e3-f4', 'b6-a5'] },
        { name: 'Pioneiro Prof.',  moves: ['c3-d4', 'b6-c5', 'd4xb6', 'a7xc5', 'b2-c3', 'f6-g5'] },
        { name: 'Russa Profunda',  moves: ['c3-b4', 'f6-e5', 'b4-a5', 'b6-c5', 'g3-h4', 'e5-f4'] },
        { name: 'Turca',           moves: ['c3-d4', 'd6-e5', 'b2-c3', 'b6-a5', 'a3-b4', 'c7-b6'] },
        { name: 'Americana',       moves: ['c3-d4', 'b6-c5', 'd4xb6', 'a7xc5', 'b2-c3', 'f6-e5'] },
        { name: 'a3-b4',   moves: ['c3-d4', 'd6-e5', 'b2-c3', 'b6-a5', 'a3-b4'] },
    ];

    // ── Tablita match manager (inline) ──────────────────────────────────────
    class TablitaManager {
        constructor() {
            this.currentTablita = null;
            this.gameNumber = 0;
            this.matchResults = [];
            this.playerColor = 1;
        }
        selectTablita() {
            const idx = Math.floor(Math.random() * TABLITAS.length);
            this.currentTablita = TABLITAS[idx];
            this.gameNumber = 1;
            this.matchResults = [];
            this.playerColor = 1;
            return this.currentTablita;
        }
        getTablitaNotation() {
            return this.currentTablita ? [...this.currentTablita.moves] : [];
        }
        getTablitaDisplay() {
            if (!this.currentTablita) return '';
            const moves = this.currentTablita.moves;
            let display = '';
            for (let i = 0; i < moves.length; i++) {
                const moveNum = Math.floor(i / 2) + 1;
                if (i % 2 === 0) display += `${moveNum}. ${moves[i]}`;
                else display += ` ${moves[i]}`;
            }
            return display;
        }
        getTablitaName() { return this.currentTablita ? this.currentTablita.name : ''; }
        recordResult(result) { this.matchResults.push({ game: this.gameNumber, result }); }
        startGame2() {
            if (this.gameNumber !== 1) return false;
            this.gameNumber = 2;
            this.playerColor = -1;
            return true;
        }
        isMatchComplete() { return this.matchResults.length >= 2; }
        getMatchResult() {
            let pw = 0, ow = 0, dr = 0;
            for (const r of this.matchResults) {
                if (r.result === 'win') pw++;
                else if (r.result === 'loss') ow++;
                else dr++;
            }
            return { playerWins: pw, opponentWins: ow, draws: dr,
                     matchResult: pw > ow ? 'win' : pw < ow ? 'loss' : 'draw' };
        }
        reset() { this.currentTablita = null; this.gameNumber = 0; this.matchResults = []; this.playerColor = 1; }
        getPlayerColor() { return this.playerColor; }
        isPlayerWhite() { return this.playerColor === 1; }
    }

    // ── Reconstruct position by replaying tablita moves ─────────────────────
    function reconstructTablitaPosition(tablitaMoves) {
        const s = new State();
        for (const moveStr of tablitaMoves) {
            const parts = moveStr.split(/[-x]/);
            const from = algToIdx(parts[0]);
            const to = algToIdx(parts[parts.length - 1]);
            const moves = s.getMoves();
            const found = moves.find(m => m.from === from && m.to === to);
            if (!found) { console.warn(`Tablita move ${moveStr} not legal`); return null; }
            s.applyMove(found);
        }
        return s;
    }

    // ── Auto-select random tablita and reconstruct board (no game start) ────
    // Called when user selects Tablita mode from the dropdown.
    function autoSelectTablita() {
        if (!tablitaManager) {
            tablitaManager = new TablitaManager();
            tablitaManager.selectTablita();
        }
        tablitaGameNum = tablitaManager.gameNumber || 1;
        tablitaMatchScore = { w: 0, b: 0 };
        tablitaSubMode = parseInt(document.getElementById('tablita-submode').value);
        updateTablitaUI();

        const notation = tablitaManager.getTablitaNotation();
        const ns = new State();
        timeLimit = parseInt(document.getElementById('cfg-time').value);
        ns.timeW = timeLimit; ns.timeB = timeLimit;
        timeW = timeLimit; timeB = timeLimit;

        // Build rootNode chain by replaying tablita moves
        rootNode = { id: 0, parent: null, moveStr: null, state: ns, children: [] };
        nextNodeId = 1; allNodes = { 0: rootNode };
        let curr = rootNode;
        for (const moveStr of notation) {
            const parts = moveStr.split(/[-x]/);
            const from = algToIdx(parts[0]);
            const to = algToIdx(parts[parts.length - 1]);
            const moves = curr.state.getMoves();
            const found = moves.find(m => m.from === from && m.to === to);
            if (!found) { console.warn(`Tablita move ${moveStr} not legal`); break; }
            const ns2 = curr.state.clone();
            ns2.applyMove(found); ns2.timeW = timeLimit; ns2.timeB = timeLimit;
            const nd = { id: nextNodeId++, parent: curr, moveStr: move2Str(found),
                         state: ns2, children: [], move: cloneMv(found) };
            curr.children.push(nd); allNodes[nd.id] = nd; curr = nd;
        }
        currentNode = curr;
        gameState = currentNode.state.clone();
        lastM = currentNode.move || null;
        selIdx = -1; valTgt = [];
        nonBookPlyCount = 0;

        // Set view: human sees from their color's perspective
        // MVH → human plays Red → Red at bottom ('B')
        // All others → human plays White (or neutral) → White at bottom ('W')
        cfgView = tablitaSubMode === MODE_MVH ? 'B' : 'W';
        document.getElementById('cfg-view').value = cfgView;
        updateCoords();

        gameStarted = false; gameEnded = false; isComputing = false; gameResultType = null;
        tablitaGameInProgress = false; // Reset Tablita game progress flag on mode switch
        document.getElementById('modal').style.display='none';
        render();
    }

    // ── Zobrist 64-bit ──────────────────────────────────────────────────────
    const M64 = 0xFFFFFFFFFFFFFFFFn;
    const ZS = 0x9E3779B97F4A7C15n;
    const zp = new Array(256);
    let zt = 0n;
    (function() {
        let h = ZS;
        for (let i = 0; i < 256; i++) {
            h = (h ^ (h >> 12n) ^ (h << 25n) ^ (h >> 27n)) & M64;
            zp[i] = h;
            h = (h * ZS) & M64;
        }
        h = (h ^ (h >> 12n) ^ (h << 25n) ^ (h >> 27n)) & M64;
        zt = h;
    })();
    function getPieceIdx(p) { return p===W_MAN?0: p===V_MAN?1: p===W_KING?2: 3; }

    // ── PST tables (reengineered) ────────────────────────────────────────────
    const PST_M = [
        0,0,0,0,0,0,0,0,  0,5,0,5,0,5,0,5,
        5,0,10,0,10,0,8,0,  0,12,0,17,0,17,0,12,
        13,0,20,0,20,0,18,0,  0,20,0,24,0,24,0,20,
        22,0,26,0,26,0,25,0,  0,0,0,0,0,0,0,0,
    ];
    const PST_K = [
        3,0,3,0,3,0,3,0,  0,7,0,8,0,8,0,3,
        4,0,13,0,12,0,11,0,  0,9,0,18,0,17,0,9,
        5,0,17,0,18,0,13,0,  0,9,0,13,0,14,0,5,
        4,0,8,0,9,0,8,0,  0,3,0,3,0,3,0,3,
    ];
    const CENTER_BIG = new Set([27, 36, 34, 29]);
    const CENTER_SM  = new Set([18, 20, 25, 38, 43, 45]);
    // ════════════════════════════════════════════════════════════════════════
    //  STATE
    // ════════════════════════════════════════════════════════════════════════
    class State {
        constructor() {
            this.board = new Int8Array(64);
            this.turn  = 1;
            this.hash  = 0n;
            this.wP = this.bP = this.wK = this.bK = 0;
            this.hashHist      = [];
            this.halfMoveClock = 0;
            this.endgameClock  = 0;
            this.isEndgame     = false;
            this.endgameLimit  = 10;
            this.timeW = 0; this.timeB = 0;
            this.init();
        }
        init() {
            this.board.fill(EMPTY);
            this.wP = this.bP = this.wK = this.bK = 0;
            for (let i = 0; i < 64; i++) {
                const r = i >> 3, c = i & 7;
                if ((r + c) % 2 === 0) {
                    if (r < 3)      { this.board[i] = W_MAN; this.wP++; }
                    else if (r > 4) { this.board[i] = V_MAN; this.bP++; }
                }
            }
            this.turn = 1; this._rehash(); this.hashHist = [this.hash];
            this.halfMoveClock = 0; this.endgameClock = 0; this.isEndgame = false; this.endgameLimit = 10;
        }

        clone() {
            const s = Object.create(State.prototype);
            s.board         = this.board.slice();
            s.turn          = this.turn;
            s.hash          = this.hash;
            s.wP = this.wP; s.bP = this.bP; s.wK = this.wK; s.bK = this.bK;
            s.hashHist      = this.hashHist.slice();
            s.halfMoveClock = this.halfMoveClock;
            s.endgameClock  = this.endgameClock;
            s.isEndgame     = this.isEndgame;
            s.endgameLimit  = this.endgameLimit;
            s.timeW         = this.timeW;
            s.timeB         = this.timeB;
            return s;
        }

        _rehash() {
            let h = 0n;
            this.wP = this.bP = this.wK = this.bK = 0;
            for (let i = 0; i < 64; i++) {
                const p = this.board[i];
                if (p === EMPTY) continue;
                h ^= zp[i * 4 + getPieceIdx(p)];
                if (p === W_MAN) this.wP++; else if (p === V_MAN) this.bP++;
                else if (p === W_KING) this.wK++; else if (p === V_KING) this.bK++;
            }
            if (this.turn === -1) h ^= zt;
            this.hash = h & M64;
        }
        isValid(r, c) { return r >= 0 && r < 8 && c >= 0 && c < 8; }

        getMoves() {
            const captures = [], simples = [];
            for (let i = 0; i < 64; i++) {
                const p = this.board[i];
                if (p === EMPTY || Math.sign(p) !== this.turn) continue;
                const isKing = (p === W_KING || p === V_KING);
                const caps = this.getCaptures(i, i >> 3, i & 7, isKing, [], i, []);
                if (caps.length > 0) captures.push(...caps);
                else if (captures.length === 0) simples.push(...this.getSimples(i, i >> 3, i & 7, isKing));
            }
            if (captures.length > 0) {
                let maxC = 0;
                for (let i = 0; i < captures.length; i++)
                    if (captures[i].captured.length > maxC) maxC = captures[i].captured.length;
                const filtered = [];
                for (let i = 0; i < captures.length; i++)
                    if (captures[i].captured.length === maxC) filtered.push(captures[i]);
                return filtered.sort(moveSorter);
            }
            return simples.sort(moveSorter);
        }

        getCapturesOnly() {
            const moves = [];
            for (let i = 0; i < 64; i++) {
                const p = this.board[i];
                if (p === EMPTY || Math.sign(p) !== this.turn) continue;
                const isKing = (p === W_KING || p === V_KING);
                const caps = this.getCaptures(i, i >> 3, i & 7, isKing, [], i, []);
                if (caps.length > 0) moves.push(...caps);
            }
            if (moves.length > 0) {
                let maxC = 0;
                for (let i = 0; i < moves.length; i++)
                    if (moves[i].captured.length > maxC) maxC = moves[i].captured.length;
                const filtered = [];
                for (let i = 0; i < moves.length; i++)
                    if (moves[i].captured.length === maxC) filtered.push(moves[i]);
                return filtered.sort(moveSorter);
            }
            return moves;
        }

        getSimples(idx, r, c, isKing) {
            const moves = [];
            const dirs  = isKing ? DIRS_ALL : this.turn === 1 ? DIRS_W : DIRS_B;
            for (const d of dirs) {
                for (let step = 1; step <= (isKing ? 7 : 1); step++) {
                    const nr = r + d[0] * step, nc = c + d[1] * step;
                    if (!this.isValid(nr, nc)) break;
                    const nIdx = nr * 8 + nc;
                    if (this.board[nIdx] !== EMPTY) break;
                    const isPromo = !isKing && ((this.turn === 1 && nr === 7) || (this.turn === -1 && nr === 0));
                    moves.push(allocMv(idx, nIdx, null, NO_CAPTURES, isPromo, !isKing, 0));
                }
            }
            return moves;
        }

        getCaptures(idx, r, c, isKing, curCap, origFrom, curPath) {
            const moves = [];
            for (const d of DIRS_ALL) {
                let enemyIdx = -1, step = 1;
                while (true) {
                    const nr = r + d[0] * step, nc = c + d[1] * step;
                    if (!this.isValid(nr, nc)) break;
                    const chk = nr * 8 + nc, p = this.board[chk];
                    if (p !== EMPTY) {
                        if (Math.sign(p) === this.turn || curCap.includes(chk)) break;
                        if (enemyIdx === -1) { enemyIdx = chk; if (!isKing && step > 1) break; }
                        else break;
                    } else if (enemyIdx !== -1) {
                        // CBD Art.13 / Regra 7: A pedra que durante o lance de captura de
                        // várias peças apenas passe pela casa de coroação SEM AÍ PARAR
                        // NÃO será promovida a dama. A promoção só ocorre quando a pedra
                        // TERMINA a sequência na casa de coroação.
                        curCap.push(enemyIdx);
                        curPath.push(chk);
                        const origP = this.board[idx];
                        this.board[idx] = EMPTY; this.board[chk] = origP;
                        const nextCaps = this.getCaptures(chk, nr, nc, isKing, curCap, origFrom, curPath);
                        this.board[idx] = origP; this.board[chk] = EMPTY;
                        if (nextCaps.length > 0) {
                            moves.push(...nextCaps);
                        } else {
                            const atCrown = !isKing && ((this.turn === 1 && nr === 7) || (this.turn === -1 && nr === 0));
                            let capKings = 0;
                            for (const cIdx of curCap) if (Math.abs(this.board[cIdx]) === 2) capKings++;
                            moves.push(allocMv(origFrom, chk, curPath.slice(), curCap.slice(), atCrown, !isKing, capKings));
                        }
                        curCap.pop();
                        curPath.pop();
                        if (!isKing) break;
                    }
                    step++;
                    if (!isKing && enemyIdx === -1 && step > 1) break;
                }
            }
            return moves;
        }

        applyMove(m) {
            let p = this.board[m.from];
            this.hash ^= zp[m.from * 4 + getPieceIdx(p)];
            this.board[m.from] = EMPTY;
            if (p === W_MAN) this.wP--; else if (p === V_MAN) this.bP--;
            else if (p === W_KING) this.wK--; else if (p === V_KING) this.bK--;

            for (const cap of m.captured) {
                const cp = this.board[cap];
                this.hash ^= zp[cap * 4 + getPieceIdx(cp)];
                this.board[cap] = EMPTY;
                if (cp === W_MAN) this.wP--; else if (cp === V_MAN) this.bP--;
                else if (cp === W_KING) this.wK--; else if (cp === V_KING) this.bK--;
            }

            if (m.promo) {
                const sign = Math.sign(p);
                if (sign === 1) { this.wP--; this.wK++; }
                else { this.bP--; this.bK++; }
                p = sign * 2;
            }

            this.hash ^= zp[m.to * 4 + getPieceIdx(p)];
            this.board[m.to] = p;
            if (p === W_MAN) this.wP++; else if (p === V_MAN) this.bP++;
            else if (p === W_KING) this.wK++; else if (p === V_KING) this.bK++;

            if (m.captured.length > 0 || m.isPawn) this.halfMoveClock = 0;
            else this.halfMoveClock++;

            // Returns 0 (not endgame), 4 (1D×1D: 2-move rule), or 10 (other: 5-move rule)
            const { wP, bP, wK, bK } = this;
            const endgameLimit = (() => {
                if (wP === 0 && bP === 0) {
                    // Art.59.D: 1D×1D — empate em 2 lances (4 meios-lances)
                    if (wK === 1 && bK === 1) return 4;
                    if (wK <= 2 && bK <= 2 && wK >= 1 && bK >= 1) return 10;
                    if ((wK === 3 && bK === 1) || (bK === 3 && wK === 1)) {
                        const loneColor = wK === 1 ? W_KING : V_KING;
                        for (let i = 0; i < 64; i++)
                            if (this.board[i] === loneColor && (i >> 3) === (i & 7)) return 10;
                        return 0;
                    }
                }
                // Art.100 (64 casas): 2D+1P vs 1D (dama solitária na grande diagonal a1-h8)
                if (wP === 1 && wK === 2 && bK === 1 && bP === 0) {
                    for (let i = 0; i < 64; i++)
                        if (this.board[i] === V_KING && (i >> 3) === (i & 7)) return 10;
                    return 0;
                }
                if (bP === 1 && bK === 2 && wK === 1 && wP === 0) {
                    for (let i = 0; i < 64; i++)
                        if (this.board[i] === W_KING && (i >> 3) === (i & 7)) return 10;
                    return 0;
                }
                // Art.100 (64 casas): 1D+2P vs 1D (dama solitária na grande diagonal a1-h8)
                if (wP === 0 && bP === 2 && wK === 1 && bK === 1) {
                    for (let i = 0; i < 64; i++)
                        if (this.board[i] === W_KING && (i >> 3) === (i & 7)) return 10;
                    return 0;
                }
                if (bP === 0 && wP === 2 && bK === 1 && wK === 1) {
                    for (let i = 0; i < 64; i++)
                        if (this.board[i] === V_KING && (i >> 3) === (i & 7)) return 10;
                    return 0;
                }
                if (wP === 0 && bP === 1 && wK >= 1 && bK >= 1 && wK <= 2) return 10;
                if (bP === 0 && wP === 1 && bK >= 1 && wK >= 1 && bK <= 2) return 10;
                // Art.59.E.C: 1D+1P × 1D+1P — empate em 5 lances
                if (wK === 1 && bK === 1 && wP === 1 && bP === 1) return 10;
                // Art.59.F: 1D solitária na grande diagonal + 2P vs 1D — empate em 5 lances
                // (as 2 pedras bloqueadas antes da diagonal da dama solitária)
                if (wK === 1 && bK === 1 && wP === 0 && bP === 2) {
                    for (let i = 0; i < 64; i++)
                        if (this.board[i] === W_KING && (i >> 3) === (i & 7)) return 10;
                    return 0;
                }
                if (bK === 1 && wK === 1 && bP === 0 && wP === 2) {
                    for (let i = 0; i < 64; i++)
                        if (this.board[i] === V_KING && (i >> 3) === (i & 7)) return 10;
                    return 0;
                }
                return 0;
            })();

            if (endgameLimit > 0) {
                // Reinicia o clock se: (a) nunca estava em modo final, OU (b) ocorreu uma captura
                // (captura altera o material e invalida a contagem anterior — CBD Art.99/100)
                if (!this.isEndgame || m.captured.length > 0) {
                    this.isEndgame = true; this.endgameClock = 0; this.endgameLimit = endgameLimit;
                } else {
                    this.endgameClock++; this.endgameLimit = endgameLimit;
                }
            } else {
                this.isEndgame = false; this.endgameClock = 0; this.endgameLimit = 10;
            }

            this.turn *= -1;
            this.hash ^= zt;

            if (m.captured.length > 0) this.hashHist = [];
            const h = this.hash;
            if (this.hashHist.length >= 256) this.hashHist.shift();
            this.hashHist.push(h);
        }

        makeMove(m) {
            const hh = this.hashHist;
            const hhLen = hh.length;
            const shifted = hhLen >= 256 ? hh[0] : 0n;
            const undo = {
                capsP: m.captured.map(sq => this.board[sq]),
                fromP: this.board[m.from],
                wP: this.wP, bP: this.bP, wK: this.wK, bK: this.bK,
                hash: this.hash,
                turn: this.turn,
                hmc: this.halfMoveClock,
                hh, hhLen, shifted,
                ec: this.endgameClock, ie: this.isEndgame, el: this.endgameLimit,
                tw: this.timeW, tb: this.timeB
            };
            this.applyMove(m);
            return undo;
        }

        unmakeMove(m, undo) {
            this.board[m.to] = EMPTY;
            for (let i = 0; i < m.captured.length; i++) this.board[m.captured[i]] = undo.capsP[i];
            this.board[m.from] = undo.fromP;
            this.wP = undo.wP; this.bP = undo.bP; this.wK = undo.wK; this.bK = undo.bK;
            this.hash = undo.hash;
            this.turn = undo.turn;
            this.halfMoveClock = undo.hmc;
            if (m.captured.length > 0) {
                this.hashHist = undo.hh;
            } else if (undo.hhLen >= 256) {
                this.hashHist.pop();
                this.hashHist.unshift(undo.shifted);
            } else {
                this.hashHist.length = undo.hhLen;
            }
            this.endgameClock = undo.ec; this.isEndgame = undo.ie; this.endgameLimit = undo.el;
            this.timeW = undo.tw; this.timeB = undo.tb;
        }

        checkDraw() {
            if (this.halfMoveClock >= 40)
                return "Empate: 20 lances consecutivos de damas sem captura ou movimento de pedra (CBD).";
            if (this.isEndgame && this.endgameClock >= this.endgameLimit)
                return this.endgameLimit === 4
                    ? "Empate: limite de 2 lances em 1 Dama × 1 Dama (CBD Art.59.D)."
                    : "Empate: limite de 5 lances no final (CBD Art.59.E/F).";
            if (this.hashHist.length >= 9) {
                const cur = this.hash; let cnt = 0;
                for (const h of this.hashHist) if (h === cur) cnt++;
                if (cnt >= 3) return "Empate: mesma posição repetida 3 vezes (CBD Art.98).";
            }
            return false;
        }

        loadFEN(fen) {
            this.board.fill(EMPTY);
            this.wP = this.bP = this.wK = this.bK = 0;
            const parts = fen.trim().split(/\s+/);
            const rows = parts[0].split('/');
            for (let r = 0; r < 8; r++) {
                let c = 0;
                for (const ch of rows[r]) {
                    if (ch >= '1' && ch <= '8') { c += parseInt(ch); }
                    else {
                        const idx = r * 8 + c;
                        if (ch === 'W') this.board[idx] = W_MAN;
                        else if (ch === 'B') this.board[idx] = V_MAN;
                        else if (ch === 'K') this.board[idx] = W_KING;
                        else if (ch === 'Q') this.board[idx] = V_KING;
                        c++;
                    }
                }
            }
            this.turn = (parts[1] === 'W') ? 1 : -1;
            this._rehash();
            this.hashHist = [this.hash];
            this.halfMoveClock = 0;
            this.endgameClock = 0;
            this.isEndgame = false;
            this.endgameLimit = 10;
            for (let i = 0; i < 64; i++) {
                const p = this.board[i];
                if (p === W_MAN) this.wP++;
                else if (p === V_MAN) this.bP++;
                else if (p === W_KING) this.wK++;
                else if (p === V_KING) this.bK++;
            }
        }

        toFEN() {
            let fen = '';
            for (let r = 0; r < 8; r++) {
                let empty = 0;
                for (let c = 0; c < 8; c++) {
                    const p = this.board[r * 8 + c];
                    if (p === EMPTY) { empty++; continue; }
                    if (empty > 0) { fen += empty; empty = 0; }
                    if (p === W_MAN) fen += 'W';
                    else if (p === V_MAN) fen += 'B';
                    else if (p === W_KING) fen += 'K';
                    else if (p === V_KING) fen += 'Q';
                }
                if (empty > 0) fen += empty;
                if (r < 7) fen += '/';
            }
            fen += ' ' + (this.turn === 1 ? 'W' : 'B');
            return fen;
        }

        // ── Avaliação v4 — clean, phase-aware ────────────────────────────────
        eval() {
            const totalPieces = this.wP + this.bP + this.wK + this.bK;
            const ph = Math.min(totalPieces, 24);
            const kv = 300 + (24 - ph) * 6;
            let sc = (this.wP - this.bP) * 100 + (this.wK - this.bK) * kv;

            let wMob = 0, bMob = 0;

            for (let i = 0; i < 64; i++) {
                const p = this.board[i];
                if (p === 0) continue;
                const sign = Math.sign(p);
                const r = i >> 3, c = i & 7;
                const isWhite = sign === 1;

                if (p === W_MAN) sc += PST_M[i];
                else if (p === V_MAN) sc -= PST_M[63 - i];
                else if (p === W_KING) sc += PST_K[i];
                else if (p === V_KING) sc -= PST_K[63 - i];

                // Edge penalty (scaled by phase — more important in endgame)
                if (c === 0 || c === 7) {
                    const edgePen = 7 + ((24 - ph) >> 1);
                    sc += isWhite ? -edgePen : edgePen;
                }
                // Center bonus (scaled by phase)
                const centerBonus = 8 + ((24 - ph) >> 2);
                if (CENTER_BIG.has(i))      sc += isWhite ? centerBonus + 3 : -(centerBonus + 3);
                else if (CENTER_SM.has(i))  sc += isWhite ? centerBonus : -centerBonus;

                // Mobility: count attackers toward opponent's half
                const inOppHalf = (isWhite && r >= 3) || (!isWhite && r <= 4);
                if (inOppHalf) {
                    if (Math.abs(p) === 2) {
                        if (isWhite) wMob += 2; else bMob += 2;
                    } else {
                        if (isWhite) wMob++; else bMob++;
                    }
                }
            }

            // Mobility balance (small bonus)
            sc += (wMob - bMob) * 3;

            return this.turn === 1 ? sc : -sc;
        }
    }
    // ════════════════════════════════════════════════════════════════════════
    //  UTILITÁRIOS DE JOGADA
    // ════════════════════════════════════════════════════════════════════════
    function idx2Str(i) { return String.fromCharCode(97+(i&7)) + ((i>>3)+1); }
    function move2Str(m) {
        let s = idx2Str(m.from);
        if (m.captured.length > 0) for (const p of m.path) s += "x" + idx2Str(p);
        else s += "-" + idx2Str(m.to);
        return s;
    }
    function moveSorter(a, b) {
        const sa = a.captured.length*100 + (a.capKings||0)*10 + (a.promo?50:0);
        const sb = b.captured.length*100 + (b.capKings||0)*10 + (b.promo?50:0);
        if (sa !== sb) return sb - sa;
        return (a.from * 64 + a.to) - (b.from * 64 + b.to);
    }

    // ════════════════════════════════════════════════════════════════════════
    //  TABELA DE TRANSPOSIÇÃO v2 — 64-bit BigInt, 2-way cluster
    // ════════════════════════════════════════════════════════════════════════
    // data layout(32 bits): move(12) | score_scaled(10) | depth(8+128) | flag(2)
    const TTS = 1 << 18, TE=0, TL=1, TU=2;
    const tt0 = new Uint32Array(TTS), tt1 = new Uint32Array(TTS);
    const tt2 = new Uint32Array(TTS), tt3 = new Uint32Array(TTS);

    function ttPack(mv, sc, dp, fl) {
        const d = (dp + 128) & 0xFF;
        const s = Math.round(Math.max(-512, Math.min(511, sc / 20))) & 0x3FF;
        const m = mv & 0xFFF;
        const f = fl & 3;
        return m | (s << 12) | (d << 22) | (f << 30);
    }
    function ttUnpack(v) {
        return {
            mv: v & 0xFFF,
            sc: (((v >> 12) & 0x3FF) << 22) >> 22,
            dp: ((v >> 22) & 0xFF) - 128,
            fl: (v >> 30) & 3,
        };
    }
    function ttStore(hash, depth, score, fm, tm, flag) {
        const i = Number(hash & BigInt(TTS - 1));
        const hh = Number(hash >> 32n);
        const mv = (fm << 6) | tm;
        const v = ttPack(mv, score, depth, flag);
        const e0d = ((tt1[i] >> 22) & 0xFF) - 128;
        if (depth >= e0d) {
            // Preserve old slot 0 in slot 1 before overwriting (aging-friendly)
            tt2[i] = tt0[i]; tt3[i] = tt1[i];
            tt0[i] = hh; tt1[i] = v;
        } else {
            tt2[i] = hh; tt3[i] = v;
        }
    }
    function ttProbe(hash) {
        const i = Number(hash & BigInt(TTS - 1));
        const hh = Number(hash >> 32n);
        if (tt0[i] === hh) return ttUnpack(tt1[i]);
        if (tt2[i] === hh) return ttUnpack(tt3[i]);
        return null;
    }    // ════════════════════════════════════════════════════════════════════════
    //  KILLER MOVES + HISTÓRIA (v2)
    // ════════════════════════════════════════════════════════════════════════
    const MAX_PLY = 64;
    const histTable = new Int32Array(4096);
    const killers = new Int32Array(MAX_PLY * 2);
    let orderSc = new Int32Array(64);

    function storeKiller(ply, m) {
        if (ply >= MAX_PLY) return;
        killers[ply * 2 + 1] = killers[ply * 2];
        killers[ply * 2] = m.from * 64 + m.to;
    }

    function scoreMove(m, hfm, htm, ply) {
        if (hfm >= 0 && m.from === (hfm >>> 0) && m.to === (htm >>> 0)) return 2000000;
        if (m.captured.length > 0) return 1000000 + m.captured.length * 10000 + (m.promo ? 5000 : 0);
        if (m.promo) return 900000;
        if (ply < MAX_PLY) {
            if (killers[ply * 2] === m.from * 64 + m.to) return 800000;
            if (killers[ply * 2 + 1] === m.from * 64 + m.to) return 799000;
        }
        return histTable[m.from * 64 + m.to];
    }

    function orderMoves(moves, hfm, htm, ply) {
        const n = moves.length;
        if (n > orderSc.length) orderSc = new Int32Array(n);
        for (let i = 0; i < n; i++) orderSc[i] = scoreMove(moves[i], hfm, htm, ply);
        for (let i = 1; i < n; i++) {
            const si = orderSc[i], mi = moves[i]; let j = i - 1;
            while (j >= 0 && orderSc[j] < si) { orderSc[j + 1] = orderSc[j]; moves[j + 1] = moves[j]; j--; }
            orderSc[j + 1] = si; moves[j + 1] = mi;
        }
    }    // ════════════════════════════════════════════════════════════════════════
    //  LIVRO DE ABERTURAS v15
    //
    //  Mapa de squares (32 casas escuras, A-Z a-f):
    //    A=a1  B=c1  C=e1  D=g1   E=b2  F=d2  G=f2  H=h2
    //    I=a3  J=c3  K=e3  L=g3   M=b4  N=d4  O=f4  P=h4
    //    Q=a5  R=c5  S=e5  T=g5   U=b6  V=d6  W=f6  X=h6
    //    Y=a7  Z=c7  a=e7  b=g7   c=b8  d=d8  e=f8  f=h8
    //
    //  Formato comprimido: 2 chars por jogada (from+to). Linhas separadas por '|'.
    //  buildOpeningBook() valida cada linha através do motor.
    // ════════════════════════════════════════════════════════════════════════
    const DARK_SQUARES=[0,2,4,6,9,11,13,15,16,18,20,22,25,27,29,31,32,34,36,38,41,43,45,47,48,50,52,54,57,59,61,63];
    const BOOK_ALPHA='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdef';
    const charToSq=Object.fromEntries(BOOK_ALPHA.split('').map((c,i)=>[c,DARK_SQUARES[i]]));

    // ── BOOK_DATA: linhas validadas em formato comprimido ───────────────────
    // Inclui todas as linhas do v14 + extensões v15 (Russa, Cruz, Pioneiro etc.)
    const BOOK_DATA =
        "IMUQEIVS|IMUQEIWS|IMUQEIWT|IMUQEIYU|IMUQEIZU|IMUQKNVR|IMUQKNWS|IMUQKNWT|IMUQKNXT|IMUQKNYU|IMUQLPWT|IMUREIWS|IMUREIWT|IMURMQRM|IMVRMVaR|IMVSEIWT|IMVSKNXT|IMVSMQWT|IMWSLPbW|IMWTMQTP|IMWTMRUN|IMXTLOUR|IMXTMQTP|IMXTMRUN|IMXTMRVM|JMUQEJWT|JMUQEJZU|JMUQFJWS|JMUQFJYU|JMUQLOQJ|JMUQLPQJ|JMUQMRVM|JMUREJWS|JMUREJWT|JMURFJWS|JMURFJWT|JMURKNRK|JMURKOWS|JMURKOWT|JMURLOWT|JMURMQVS|JMVSEJWT|JMVSEJZV|JMVSFJaV|JMVSFJWT|JMVSKOaV|JMVSKOUQ|JMVSLPSO|JMVSMQaV|JMVSMQUR|JMVSMQWT|JMWSEJaW|JMWSEJbW|JMWSEJSO|JMWSEJUR|JMWSFJbW|JMWSKOaW|JMWSKObW|JMWSKOUQ|JMWSKOUR|JMWSLOSL|JMWSLPSO|JMWSMQUR|JMWSMRUN|JMWSMRVM|JMWTEJbW|JMWTEJTO|JMWTEJTP|JMWTEJUQ|JMWTFJbW|JMWTFJUQ|JMWTKNaW|JMWTKNTO|JMWTKNTP|JMWTKNVR|JMWTLObW|JMWTLOUR|JMWTLPTO|JMWTLPUQ|JMWTMQTO|JMWTMQTP|JMWTMRUN|JMWTMRVM|JMXTFJbX|JMXTLObX|JMXTLPbX|JMXTLPTO|JMXTLPUQ|JMXTLPVS|JMXTMQWS|JNUQEJVR|JNUQEJVS|JNUQEJWS|JNUQEJWT|JNUQEJYU|JNUQEJZU|JNUQFJZU|JNUQKOWT|JNUQKOYU|JNUQKOZU|JNUQLOWS|JNUQLOWT|JNUQLOZU|JNUQLPVS|JNUQNRVM|JNUQNSWN|JNURNUYR|JNURNUZQ|JNVREJaV|JNVREJRM|JNVREJWS|JNVREJWT|JNVREJXT|JNVREJZV|JNVRFJaV|JNVRFJWS|JNVRFJWT|JNVRFJZV|JNVRLOWT|JNVRLOZV|JNVRLPWS|JNVRLPWT|JNVRLPXT|JNVRLPZV|JNVRNSWN|JNVSEJaV|JNVSEJSO|JNVSEJUQ|JNVSEJUR|JNVSEJWT|JNVSEJZV|JNVSFJaV|JNVSFJUR|JNVSFJZV|JNVSLOSJ|JNVSLOSL|JNVSLPSJ|JNWSNWaT|JNWSNWbS|JNWTEJaW|JNWTEJbW|JNWTEJTO|JNWTEJTP|JNWTEJUQ|JNWTEJUR|JNWTEJVR|JNWTFJaW|JNWTFJbW|JNWTFJTP|JNWTFJUQ|JNWTFJUR|JNWTFJVR|JNWTIMTO|JNWTLOaW|JNWTLObW|JNWTLOUQ|JNWTLOVR|JNWTLOVS|JNWTLPaW|JNWTLPbW|JNWTLPUQ|JNWTLPUR|JNWTLPVR|JNWTNRUN|JNWTNRVM|JNWTNSVO|JNXTEJbX|JNXTEJTO|JNXTEJTP|JNXTLObX|JNXTLOTP|JNXTLPbX|JNXTLPUQ|JNXTLPVR|JNXTLPVS|KNURNUYR|KNVRFKWS|KNVRFKWT|KNVRGKZV|KNVSFKaV|KNVSIMUQ|KNVSIMXT|KNWSNWbS|KNWTFKbW|KNWTFKTP|KNWTGKbW|KNWTGKTP|KNWTJMTP|KNWTJMVR|KNWTLPbW|KNWTLPUR|KNWTLPVR|KNXTLPVS|KOUQGKWS|KOUQGKWT|KOUQGKYU|KOUQJNVS|KOUQJNWS|KOURFKYU|KOURGKYU|KOURGKZU|KOWSFKSN|KOWTFKTP|KOWTGKTP|KOWTJMTK|KOWTOSVO|LOUQHLYU|LOUQJMQJ|LOUQJNWS|LOURJMWS|LOVRJMaV|LOVRJNWT|LOVSOVZS|LOWSGLbW|LOWSHLbW|LOWSHLSN|LOWSHLUQ|LOWSHLUR|LOWSHLXT|LOWTHLTP|LOWTJMbW|LOWTJMUR|LOWTJNbW|LOWTJNTP|LOWTJNVR|LPUQGLYU|LPUQGLZU|LPUQHLWS|LPUQHLYU|LPUQJNWT|LPUQKNVS|LPURJNWS|LPVRHLZV|LPVRJMUQ|LPVSHLXT|LPWSGLSO|LPWSIMUR|LPWSJMSO|LPWSJMUQ|LPWSJNSJ|LPWSKNaW|LPWSKOSL|LPWTPWaT|LPWTPWbS|LPXTGLTO|LPXTKOTK|IMUQEIYULP|IMUQEIZUAE|IMUQEIZUBE|IMUQKNVRMV|IMUQKNVSGK|IMUREIRNKR|IMWSMRUNKR|JMUQEJYUJN|JMUQEJZUJN|JMUQLOQJEN|JMUQMRVMIR|JMUREJWSKO|JMVSEJSOLS|JMVSFJaVJN|JMVSMQURKO|JMVSMQURLP|JMWSEJbWJN|JMWSEJbWKO|JMWSLPSOKT|JMWSMQbWEJ|JMWSMQSOKT|JMWSMQURLO|JMWSMQURLP|JMWTKNVRMV|JMWTLObWMR|JMWTMRVMIR|JMXTLPbXGL|JMXTLPbXHL|JNUQEJVSLO|JNUQKOYUNS|JNUQLPWTPW|JNUQNRVMIR|JNURNUYRFJ|JNVREJaVJM|JNVREJaVLP|JNVRLOZVNS|JNVRLPZVGL|JNVSEJaVLO|JNVSEJUQLO|JNWSNWbSEJ|JNWSNWbSIM|JNWTEJTPNS|JNWTLPUQPW|JNWTLPVRPW|JNXTLObXNR|KNURNUYRJM|KOUQGKZULP|KOURFKYULP|KOWSGKaWIM|KOWTGKTPCG|KOWTOSVOLS|LOUQJMQJFM|LOUQJNWSNW|LOUQOTXOKT|LOWSGLbWLP|LOWSHLURJM|LOWTJMbWMQ|LPUQHLXTLO|LPUQIMXTMR|LPVRGLaVLO|LPVSIMUQEI|LPWTPWbSJM|IMUQEIVSKOaV|IMUQEIVSKOYU|IMUQEIWSKObW|IMUQEIWSMRVM|IMUQEIWTKNTP|IMUQEIWTLPbW|IMUQEIWTMRVM|IMUQEIXTMRVM|IMUQEIYUAEUR|IMUQEIYUAEVS|IMUQEIYUKNcY|IMUQEIYUKNVR|IMUQEIYUKNWS|IMUQEIYULOUR|IMUQEIZUAEUR|IMUQEIZUAEVR|IMUQEIZUAEVS|IMUQEIZUAEWS|IMUQEIZUAEXT|IMUQEIZUBEUR|IMUQKNVRMVaK|IMUQKNWSNWaT|IMUQKNWSNWbS|IMUQKNWTGKTP|IMUQKNWTLPYU|IMUQKNWTNSVO|IMUQKNXTLPbX|IMUQKNXTLPVS|IMUQKNXTNSVO|IMUQKNXTNSWN|IMUQKNYUFKVR|IMUQKNYUNSWN|IMUQLPWTPWaT|IMUREIWSKObW|IMUREIWSLPYU|IMUREIWTJNbW|IMUREIWTLObW|IMUREIWTLOTP|IMURMQRMEIWT|IMURMQRMJNMI|IMURMQRMLPWS|IMURMQRMLPWT|IMURMQWTLObW|IMURMQWTLPTO|IMVRMVaRLPZV|IMVSEIWTKOTK|IMVSKNXTMQaV|IMVSKNXTMQbX|IMVSKNXTMQTP|IMVSMQWTKNTP|IMWSLPbWGLUQ|IMWSMQSOLSVO|IMWSMRUNKRVM|IMWSMRVMJQUR|IMWTMQaWLPea|IMWTMQTPJNbW|IMWTMRUNKRVM|IMWTMRVMJQTP|IMXTKNbXMQUR|IMXTLOUROXRI|IMXTMQTOKTWP|IMXTMQTPJNWS|IMXTMQTPKNVS|IMXTMRUNKRVM|IMXTMRVMJQTP|JMUQEJWTAETO|JMUQEJWTLPTO|JMUQEJZUKOUR|JMUQFJWSLPZU|JMUQFJWTBFTP|JMUQFJYULPUR|JMUQFJZUBFUR|JMUQLOQJFMWT|JMUQLOQJFMYU|JMUQLPQJFMVS|JMUQMRVMIRWS|JMUQMRVMIRWT|JMUQMRVMIRZU|JMUQMRVMIRZV|JMUREJWSAEaW|JMUREJWSAEbW|JMUREJWSAESO|JMUREJWSKOaW|JMUREJWSKObW|JMUREJWSKORN|JMUREJWSMQRM|JMUREJWTJNbW|JMUREJWTLObW|JMUREJWTLOTP|JMUREJWTLPTO|JMUREJYUMQcY|JMURFJWSKOaW|JMURFJWSKObW|JMURKNRKGNVS|JMURKNRKGNWT|JMURKOWTLPTK|JMURLOWTEJbW|JMURLOWTGLTP|JMURLPWSHLSO|JMURLPWSPTXO|JMURMQVSKOaV|JMURMQYUEJRN|JMVRMVaREJea|JMVRMVaREJUQ|JMVRMVaREJWT|JMVRMVaREJZV|JMVSEJUQKNZU|JMVSEJWTLPTO|JMVSFJaVMQea|JMVSFJUQBFZU|JMVSFJWTKNbW|JMVSFJWTMQSN|JMVSFJWTMQTO|JMVSKOaVFKUR|JMVSKOaVFKWT|JMVSKOaVGKUR|JMVSKOaVMQea|JMVSKOUQOVQJ|JMVSKOWTOVZS|JMVSLOSLHOUQ|JMVSLPSOKTXO|JMVSMQaVIMUR|JMVSMQaVIMWT|JMVSMQaVLPea|JMVSMQUREJRN|JMVSMQURFJRM|JMVSMQURKNRK|JMVSMQURKOaV|JMVSMQURKOSN|JMVSMQURLPSO|JMVSMQWTEJTO|JMVSMQWTKOTK|JMWSEJaWKNea|JMWSEJaWKNXT|JMWSEJaWMQea|JMWSEJbWAEeb|JMWSEJbWAEfb|JMWSEJbWAEWT|JMWSEJbWKNUR|JMWSEJbWKOUQ|JMWSEJbWLOSL|JMWSEJSOKTXO|JMWSEJSOLSVO|JMWSEJURKOaW|JMWSEJURKORN|JMWSEJURKOYU|JMWSFJbWKNXT|JMWSFJbWMQWT|JMWSFJURLOSL|JMWSKOaWEJWT|JMWSKOaWFKUQ|JMWSKOaWFKWT|JMWSKOaWGKWT|JMWSKOaWMQea|JMWSKOaWMQUR|JMWSKOaWMQWT|JMWSKObWEJUQ|JMWSKObWEJUR|JMWSKObWFKUQ|JMWSKObWFKUR|JMWSKObWFKWT|JMWSKObWGKUQ|JMWSKObWMQWT|JMWSKOUQEJZU|JMWSKOUQGKQJ|JMWSKOUREJaW|JMWSLOSLHOUR|JMWSLOSLHOVR|JMWSLPbWMQSO|JMWSLPSOKTXO|JMWSMQbWEJWT|JMWSMQbWLPSO|JMWSMQURLPSO|JMWSMRUNKRVM|JMWSMRVMIRUN|JMWTEJbWAEfb|JMWTEJbWAETP|JMWTEJbWJNfb|JMWTEJbWJNUR|JMWTEJbWLOfb|JMWTEJbWMQUR|JMWTEJbWMQWS|JMWTEJTOKTXO|JMWTEJTOLSVO|JMWTEJTPAEUR|JMWTEJTPJNUQ|JMWTEJTPLObW|JMWTEJTPMQbW|JMWTEJTPMQXT|JMWTEJUQMRVM|JMWTEJVSKOTK|JMWTEJVSMQSN|JMWTFJbWJNVS|JMWTFJUQBFTP|JMWTFJUQBFVS|JMWTFJUQLPZU|JMWTKNaWNSWN|JMWTKNbWMRVM|JMWTKNTOLSVO|JMWTKNTPMQXT|JMWTKNVRMVaK|JMWTKOTKFOaW|JMWTKOTKFObW|JMWTLObWEJfb|JMWTLObWEJTP|JMWTLObWEJUR|JMWTLObWEJVS|JMWTLObWEJWS|JMWTLObWHLUQ|JMWTLObWMQWS|JMWTLObWMRUN|JMWTLObWMRVM|JMWTLOTPEJbW|JMWTLOTPMQbW|JMWTLOTPMRVM|JMWTLOUQMRVM|JMWTLOUREJbW|JMWTLPTOKTXO|JMWTLPUQPWQJ|JMWTMQbWLPTO|JMWTMQTOKTXO|JMWTMQTOLSVO|JMWTMQTPEJbW|JMWTMQTPEJUR|JMWTMQTPEJXT|JMWTMQTPLOUR|JMWTMQURLObW|JMWTMRUNKRVM|JMWTMRVMIRUN|JMXTFJTPMQWS|JMXTKOTKFOWS|JMXTLObXEJfb|JMXTLOTPMRUN|JMXTLPbXGLfb|JMXTLPbXMQTO|JMXTLPbXMQVS|JMXTLPUQGLQJ|JMXTLPUQHLQJ|JMXTLPUQMRVM|JMXTLPVSHLbX|JMXTLPVSMQaV|JNUQEJWSNWbS|JNUQEJWTAETP|JNUQEJWTLPbW|JNUQEJWTNRVM|JNUQEJYUAEVR|JNUQEJYULPVS|JNUQEJZUAEUR|JNUQEJZUAEVR|JNUQEJZUAEWT|JNUQEJZULPUR|JNUQEJZULPVR|JNUQEJZULPWT|JNUQKOWTGKQM|JNUQKOWTNRTK|JNUQKOZUFJUR|JNUQLOWSNWbL|JNUQLOWTEJbW|JNUQLOWTEJZU|JNUQLOWTNRVM|JNUQLOZUEJWT|JNUQLOZUOTXO|JNUQLPVSEJSO|JNUQNRVMIRWS|JNUQNRVMIRWT|JNUQNRVMIRXT|JNUQNRVMIRZU|JNUQNRVMIRZV|JNUQNSWNKRVM|JNURNUYREJRM|JNURNUYREJWS|JNURNUYREJWT|JNURNUYRKNRK|JNURNUZQEJWS|JNURNUZQEJWT|JNURNUZQIMQJ|JNURNUZQKNVR|JNURNUZQLOWS|JNURNUZQLPWS|JNVREJaVAEVS|JNVREJaVBEWT|JNVREJaVBEXT|JNVREJaVJMUQ|JNVREJaVJMWT|JNVREJaVJMXT|JNVREJaVLOWS|JNVREJaVLOWT|JNVREJaVLPea|JNVREJaVLPVS|JNVREJaVLPXT|JNVREJWSNWaT|JNVREJWSNWbS|JNVREJWTBEbW|JNVREJWTBEZV|JNVREJWTJMaV|JNVREJWTJMaW|JNVREJWTJMTP|JNVREJWTJMUQ|JNVREJWTJMZV|JNVREJWTLObW|JNVREJWTLOTP|JNVREJXTBETO|JNVREJXTJMTP|JNVREJXTJMUQ|JNVREJXTLOTP|JNVREJXTLPaV|JNVREJXTLPbX|JNVREJXTLPZV|JNVREJZVAEVS|JNVREJZVBEWT|JNVREJZVJMUQ|JNVREJZVJMWS|JNVREJZVJMWT|JNVREJZVLOUQ|JNVREJZVLOWT|JNVREJZVLPRM|JNVREJZVLPUQ|JNVRFJaVJMUQ|JNVRFJaVJMWS|JNVRFJaVJMWT|JNVRFJaVJMXT|JNVRFJaVLPXT|JNVRFJWSNWbS|JNVRFJWTJMaV|JNVRFJWTJMTP|JNVRFJWTJMUQ|JNVRFJWTJMZV|JNVRFJWTLObW|JNVRFJWTLOTP|JNVRFJWTLOZV|JNVRFJWTLPZV|JNVRFJXTJMaV|JNVRFJXTJMTP|JNVRFJZVBFWS|JNVRFJZVJMUQ|JNVRFJZVJMWT|JNVRLOWTEJbW|JNVRLOWTFJbW|JNVRLOZVEJWT|JNVRLOZVGLUQ|JNVRLPWTPWbJ|JNVRLPXTGLbX|JNVRLPZVEJUQ|JNVRLPZVFJUQ|JNVRLPZVGLRM|JNVRLPZVGLUQ|JNVRLPZVHLcZ|JNVRLPZVHLUQ|JNVRLPZVHLVS|JNVRLPZVHLWT|JNVSEJaVAEVR|JNVSEJaVKOda|JNVSEJaVKOea|JNVSEJaVKOUQ|JNVSEJaVKOUR|JNVSEJaVKOWT|JNVSEJaVLOSL|JNVSEJaVLPUQ|JNVSEJaVLPVR|JNVSEJSOKTWP|JNVSEJSOLSUR|JNVSEJUQAEZV|JNVSEJUQIMZU|JNVSEJUQKOYU|JNVSEJUQLPZU|JNVSEJURNUYR|JNVSEJURNUZQ|JNVSEJZVKOUQ|JNVSEJZVKOUR|JNVSFJaVIMWT|JNVSFJaVKOUQ|JNVSFJaVKOUR|JNVSFJaVLPXT|JNVSFJURNUZQ|JNVSFJZVKOUQ|JNVSFJZVKOUR|JNVSFJZVLPUR|JNVSLOSJENaV|JNVSLOSJENUQ|JNVSLOSJENWS|JNVSLOSJENWT|JNVSLOSJFMWT|JNVSLOSLHOUQ|JNVSLOSLHOUR|JNVSLOSLHOWT|JNVSLPSJFMWS|JNVSLPSJFMWT|JNWSNWaTEJda|JNWSNWaTEJea|JNWSNWaTEJTP|JNWSNWaTEJUQ|JNWSNWaTEJUR|JNWSNWaTEJVS|JNWSNWaTIMea|JNWSNWaTIMTP|JNWSNWaTIMUR|JNWSNWaTKNbW|JNWSNWaTKNTP|JNWSNWaTLOda|JNWSNWaTLOea|JNWSNWaTLPTO|JNWSNWbSEJaW|JNWSNWbSEJfb|JNWSNWbSEJUQ|JNWSNWbSEJXT|JNWSNWbSIMaW|JNWSNWbSIMeb|JNWSNWbSIMfb|JNWSNWbSIMUQ|JNWSNWbSKNSJ|JNWSNWbSKOfb|JNWSNWbSLOSL|JNWSNWbSLPfb|JNWTEJaWAEea|JNWTEJaWBETP|JNWTEJaWLOda|JNWTEJaWLOVR|JNWTEJaWLPea|JNWTEJbWAETP|JNWTEJbWAEUQ|JNWTEJbWAEVR|JNWTEJbWAEVS|JNWTEJbWJMeb|JNWTEJbWJMfb|JNWTEJbWJMTP|JNWTEJbWJMUQ|JNWTEJbWJMUR|JNWTEJbWJMVS|JNWTEJbWLOfb|JNWTEJbWLPTO|JNWTEJTOKTXO|JNWTEJTOLSVO|JNWTEJTPBEbW|JNWTEJTPJMbW|JNWTEJTPJMUQ|JNWTEJTPJMVR|JNWTEJTPJMVS|JNWTEJTPJMXT|JNWTEJTPLObW|JNWTEJTPLOUQ|JNWTEJTPLOUR|JNWTEJTPLOVR|JNWTEJUQAETP|JNWTEJUQNRVM|JNWTEJURNUZQ|JNWTEJVRBEbW|JNWTEJVRJMaW|JNWTEJVRJMbW|JNWTEJVRJMTP|JNWTEJVRJMUQ|JNWTEJVRLObW|JNWTEJVRLOTP|JNWTEJVRLOZV|JNWTFJaWJMVS|JNWTFJaWLPea|JNWTFJbWBFTP|JNWTFJbWJMTP|JNWTFJbWLOVS|JNWTFJTPBFbW|JNWTFJTPBFVR|JNWTFJTPJMbW|JNWTFJTPJMXT|JNWTFJUQBFTP|JNWTFJURNUYR|JNWTFJVRJMaV|JNWTFJVRJMTP|JNWTFJVRJMUQ|JNWTFJVRJMZV|JNWTLOaWGLTP|JNWTLOaWNRVM|JNWTLObWEJfb|JNWTLObWEJTP|JNWTLObWGLTP|JNWTLObWHLTP|JNWTLObWHLUQ|JNWTLObWNRUN|JNWTLObWNRVM|JNWTLOUQNRVM|JNWTLOVREJaV|JNWTLOVREJbW|JNWTLOVREJTP|JNWTLOVREJZV|JNWTLOVRFJbW|JNWTLPaWNRVM|JNWTLPbWGLVS|JNWTLPbWNRVM|JNWTLPUQPWbJ|JNWTLPURNUYR|JNWTNRUNKRVM|JNWTNRVMIRUN|JNWTNSVOLSaV|JNWTNSVOLSaW|JNWTNSVOLSTP|JNXTEJbXJMVS|JNXTEJTOLSVO|JNXTEJTPJMVS|JNXTEJTPJMWS|JNXTEJTPLOUQ|JNXTIMbXEJUQ|JNXTLObXEJTP|JNXTLObXHLfb|JNXTLObXHLTP|JNXTLObXHLUQ|JNXTLObXNRUN|JNXTLObXNRVM|JNXTLOTPNRUN|JNXTLOTPNRVM|JNXTLOTPOTVS|JNXTLPbXGLeb|JNXTLPbXGLVR|JNXTLPbXGLVS|JNXTLPbXHLVS|JNXTLPbXNRUN|JNXTLPbXNRVM|JNXTLPUQEJVS|JNXTLPUQEJZU|JNXTLPUQFJVS|JNXTLPUQGLbX|JNXTLPUQGLYU|JNXTLPUQGLZU|JNXTLPUQHLVS|JNXTLPUQHLZU|JNXTLPUQNRVM|JNXTLPURNUYR|JNXTLPVREJaV|JNXTLPVREJbX|JNXTLPVRFJbX|JNXTLPVRGLaV|JNXTLPVRGLbX|JNXTLPVRHLaV|JNXTLPVSEJUQ|JNXTLPVSGLSJ|JNXTLPVSHLSJ|KNVRFKaVJMUQ|KNVRFKaVJMXT|KNVRFKWSNWbS|KNVRFKWTJMaV|KNVRFKWTJMTP|KNVRFKZVLOUQ|KNVRGKWTLPbW|KNVRGKZVJMUQ|KNVRGKZVJMWT|KNVRGKZVLPUQ|KNVSFKaVLPXT|KNVSIMUQEIXT|KNVSIMUQMRXT|KNVSIMXTEITP|KNVSIMXTFKTO|KNVSIMXTMQTO|KNVSIMXTMQTP|KNVSIMXTMRTO|KNWSNWaTJMVS|KNWSNWbSIMXT|KNWSNWbSJMXT|KNWSNWbSLPeb|KNWSNWbSLPfb|KNWTFKbWJMTP|KNWTFKbWLPVS|KNWTFKTPBFbW|KNWTFKTPBFUQ|KNWTFKTPBFVR|KNWTFKTPJMXT|KNWTFKUQBFTP|KNWTGKbWDGVS|KNWTGKbWJMVR|KNWTGKTPLOVR|KNWTJMTPMRVM|KNWTJMVRMVaK|KNWTLPbWNRUN|KNWTLPURNUYR|KNWTLPVRPWaT|KNWTLPVRPWRK|KNXTJMTOLSVO|KNXTLPVSGKbX|KNXTLPVSGKZV|KNXTLPVSIMbX|KNXTLPVSIMUQ|KOUQGKWSJNSJ|KOUQGKWTLPYU|KOUQGKYULPWS|KOUQJNVSOVaK|KOUQJNWSNWaK|KOURFKYUJNWT|KOURGKYUJNWS|KOURGKZUJNWS|KOWSGKaWJMUR|KOWSGKbWLPSL|KOWTFKTPBFUQ|KOWTFKTPBFUR|KOWTFKTPBFVR|KOWTGKTPCGUR|KOWTGKTPDGbW|KOWTGKTPDGUQ|KOWTGKTPKNPG|KOWTJMTKFOaW|KOWTJMTKFObW|KOWTJMTKFOUQ|KOWTJMTKFOUR|KOWTJMTKFOVR|KOWTJMTKGNVR|KOWTLPTKFObW|KOWTLPTKGNUR|KOWTOSVOLSTP|KOWTOSVOLSUR|LOUQHLWTJNQM|LOUQHLYULPVS|LOUQJMQJFMVS|LOUQJMQJFMWS|LOUQJMQJFMWT|LOUQJNWSNWbL|LOUQJNWTNRVM|LOURJMWSEJSL|LOURJNYUNSWN|LOVRJMaVHLWT|LOVRJMaVMQea|LOVRJNWTFJTP|LOVSOVZSJNSJ|LOVSOVZSKOSL|LOWSGLbWKNUQ|LOWSGLbWKNUR|LOWSGLbWLPSL|LOWSGLUQLPSL|LOWSHLaWKNUQ|LOWSHLbWJMUQ|LOWSHLbWJMWT|LOWSHLbWKNUR|LOWSHLSNJSXT|LOWSHLSNKRUN|LOWSHLUQKNZU|LOWSHLURJNSJ|LOWSHLXTOXSN|LOWSJNSJFMbW|LOWTHLTPJNVR|LOWTJMaWMRVM|LOWTJMbWEJTP|LOWTJMbWEJWS|LOWTJMbWHLTP|LOWTJMbWMRUN|LOWTJMbWMRVM|LOWTJMTPMRUN|LOWTJMUREJbW|LOWTJNbWHLTP|LOWTJNbWNRUN|LOWTJNbWNRVM|LOWTJNVRFJTP|LPUQGLYUDGcY|LPUQGLYUDGVR|LPUQHLWSKNbW|LPUQHLYUKOVR|LPUQHLYUKOWT|LPUQJNWTPWbJ|LPURJNWSNWaT|LPVRHLZVLOWT|LPVRJMaVMQWS|LPVRJMUQMVaR|LPVSHLXTKOTK|LPWSGLaWLOSL|LPWSGLbWKOfb|LPWSGLbWLOSL|LPWSGLSOKTXO|LPWSGLSOLSVO|LPWSGLUQLOSL|LPWSIMSOKTXO|LPWSIMUREISO|LPWSJMSOKTXO|LPWSJMUQEJZU|LPWSJNSJFMaW|LPWSJNSJFMXT|LPWSKNaWFKXT|LPWSKNURNUYR|LPWSKOSLHObW|LPWSKOSLHOUR|LPWTPWbSGLSO|LPWTPWbSIMfb|LPWTPWbSIMUQ|LPWTPWbSIMUR|LPWTPWbSIMXT|LPWTPWbSJMfb|LPWTPWbSJMUR|LPWTPWbSJMXT|LPWTPWbSJNSJ|LPWTPWbSKNaW|LPWTPWbSKOSL|LPXTKOTKGNVS|IMUQEIYUKNWSNW|IMUQEIZUAEURKN|IMUREIWTJNbWNU|IMXTMRUNKRVMJQ|JMUQEJZUKOURFK|JMUREJWTJNbWNU|JMURLOWTEJbWAE|JMURLOWTEJbWMQ|JMVSMQURKOaVEJ|JMWSEJSOKTXOLS|JMWSKOaWEJURFK|JMWSKOaWFKWTEJ|JMWSKObWFKUREJ|JMWTEJTOLSVOKT|JMWTLPUQPWQJEN|JMXTLPbXMQVSKN|JMXTLPVSHLbXDH|JNUQEJWSNWbSKO|JNUQLOWTEJZUNS|JNUQLOZUOTXOKT|JNUQNRVMIRWTKN|JNUQNRVMIRWTLO|JNUQNRVMIRZVEI|JNURNUYREJWTJM|JNURNUYREJWTJN|JNURNUYREJWTLO|JNURNUYREJWTLP|JNURNUZQEJWSKO|JNVREJWTJMaWMV|JNVREJWTJMUQMV|JNVREJZVJMUQNU|JNVREJZVLOUQNU|JNVREJZVLOWTNS|JNVREJZVLPUQNU|JNVRFJaVJMWTMQ|JNVRFJWTJMTPMV|JNVRFJWTLOZVNS|JNVRFJZVJMUQNU|JNVRLPZVGLRMIR|JNVRLPZVHLUQNU|JNVSEJaVKOdaOT|JNVSEJaVKOeaFK|JNVSEJaVKOUQGK|JNVSEJaVKOURNU|JNVSEJaVLPUQGL|JNVSEJUQAEZVIM|JNVSEJUQIMZUAE|JNVSEJUQIMZUMR|JNVSEJUQKOYUOV|JNVSEJZVKOUQGK|JNVSEJZVKOURNU|JNVSFJaVKOURNU|JNVSFJaVLPXTCF|JNVSFJZVKOURNU|JNVSFJZVLPURNU|JNVSNRUNKRSOLS|JNWSNWaTEJVSJM|JNWSNWbSEJSOKT|JNWSNWbSIMSOKT|JNWTEJbWJMTPMR|JNWTEJbWJMURNU|JNWTEJTPJMbWMR|JNWTEJVRJMTPMV|JNWTEJVRJMUQMV|JNWTLObWEJTPOS|JNWTNRUNKRVMIR|JNWTNRVMIRUNKR|JNXTLObXHLTPNR|JNXTLPbXGLVSLO|JNXTLPbXNRUNKR|JNXTLPUQGLZUDG|JNXTLPUQGLZULO|JNXTLPUQNRVMIR|JNXTLPVSGLSJFM|JNXTLPVSHLSJEN|JNXTLPVSHLSJFM|KNVRFKWTJMaWMV|KNVSFKaVLPXTCF|KOWSFKSNJSURCF|LPVRHLWTPWaTJM|LPWSGLUQLOSLPG|LPWSKNaWFKXTHL|IMUQEIVSKOaVFKZU|IMUQEIVSKOYUOVZS|IMUQEIWSMRVMIRbW|IMUQEIWTLPbWMRVM|IMUQEIWTMRVMIRZV|IMUQEIYUAEVSKNaV|IMUQEIYUKNcYFKWT|IMUQEIYUKNVRMVaK|IMUQEIYUKNWSNWaT|IMUQEIYUKNWSNWbS|IMUQEIYULOURGLZU|IMUQEIYULPURHLZU|IMUQEIZUAEURKNRK|IMUQEIZUAEVRMVaR|IMUQEIZUAEVSLOSL|IMUQEIZUKNURNUYR|IMUQKNVRMVaKFOWT|IMUQKNVRMVaKGNZU|IMUQKNWSNWaTEIZU|IMUQKNWSNWaTLOTK|IMUQKNWSNWbSFKYU|IMUQKNWTEIbWLPTO|IMUQKNWTLPYUPWbS|IMUQKNWTNSVOLSaV|IMUQKNXTLPbXEITO|IMUQKNXTLPVSMRTO|IMUQKNXTNSVOLSWN|IMUQKNXTNSWNJSVO|IMUQKNYUNSWNJSQJ|IMUQLPWTPWaTEIZU|IMUQLPWTPWaTKOTK|IMUREIWSKObWFKWT|IMUREIWTJNbWNUZJ|IMUREIWTLObWJNTP|IMUREIWTLOTPAEbW|IMURMQRMJNMIEJWT|IMURMQRMJNMINRVM|IMURMQRMLPWSEISO|IMURMQRMLPWSHLSO|IMURMQRMLPWTPWbS|IMVRMVaRLPZVGLWT|IMVSEIWTKOTKFVZS|IMVSKNXTMQaVEITP|IMVSKNXTMQbXFKaV|IMVSKNXTMQTPFKaV|IMVSKNXTMQTPFKbX|IMVSKNXTMRbXLPUQ|IMVSMQWTKNTPNWbS|IMWSLPbWGLUQKNVR|IMWSMQUREIbWAEZU|IMWTMQTPJNbWEJWT|IMWTMQTPJNbWNRUN|IMWTMRUNKRVMJQTP|IMXTLOUROXRIHLYU|IMXTLOUROXRIJNYU|IMXTMQTPJNWSNWbS|IMXTMQTPKNVSFKbX|IMXTMRUNKRVMJQTP|IMXTMRUNKRVMJQWS|IMXTMRVMJQTPEJbX|JMUQEJWTAETOKTXO|JMUQEJWTLPTOKTXO|JMUQEJZUKOURFKWS|JMUQFJWSLPZUJNSJ|JMUQFJYULPURHLZU|JMUQLOQJFMWTEJbW|JMUQLOQJFMWTMRVM|JMUQLOQJFMYUMRUN|JMUQMRVMIRWSEJbW|JMUQMRVMIRWSEJSO|JMUQMRVMIRWSLOSL|JMUQMRVMIRWTEJbW|JMUQMRVMIRWTEJZV|JMUQMRVMIRWTKNbW|JMUQMRVMIRWTLObW|JMUQMRVMIRWTLOTP|JMUREJWSKObWAEWT|JMUREJWSKObWFKYU|JMUREJWSKObWGKWT|JMUREJWSKORNAEbW|JMUREJWSMQSNJSVO|JMUREJWTJNbWNUZJ|JMUREJWTLObWJNfb|JMUREJWTLObWJNTP|JMUREJWTLObWMQTP|JMUREJWTLObWMQWS|JMUREJWTLOTPJNbW|JMUREJWTLPTOKTXO|JMURFJWSKOaWMQWT|JMURFJWSKObWMQeb|JMURFJWSLOSLHObW|JMURKNRKGNVSEJSO|JMURKNRKGNWTMRVM|JMURKOWSEJbWFKeb|JMURKOWTLPTKGUZJ|JMURLOWTEJbWAEfb|JMURLOWTEJbWJNTP|JMURLOWTEJbWMQRM|JMURLOWTEJbWMQTP|JMURLOWTEJbWMQWS|JMURLOWTGLTPCGbW|JMURLPWSKOSLHOaW|JMURMQVSKOaVEJWT|JMVSEJSOLSWEAJaV|JMVSEJWTLPTOKTXO|JMVSEJZVMQURJMSN|JMVSFJaVMQeaJNSJ|JMVSFJWTMQSNKRUN|JMVSFJWTMQTOKTXO|JMVSKOaVFKUREJWT|JMVSKOaVMQeaEJWT|JMVSKOUQOVQJENaK|JMVSKOWTOVaRMVZS|JMVSKOWTOVZSMQdZ|JMVSLPSOKTXOMQUR|JMVSMQaVIMUREIWT|JMVSMQaVIMWTMRUN|JMVSMQUREJRNKRSO|JMVSMQURFJRMIRZU|JMVSMQURKNRKFVaR|JMVSMQURKOaVEJWT|JMVSMQURKOaVFKWT|JMVSMQURKOaVGKWT|JMVSMQURKOSNOSNK|JMVSMQURLPSOKTXO|JMVSMQWTEJTOKTXO|JMVSMQWTKOTKFVaR|JMVSMQWTKOTKFVZS|JMWSEJaWKNeaMQSO|JMWSEJaWKNXTMRVM|JMWSEJaWMQeaJMWT|JMWSEJbWAEfbMRUN|JMWSEJbWAEWTMRUN|JMWSEJbWKNebMQSO|JMWSEJbWKOUQFKZU|JMWSEJbWKOUQGKZU|JMWSEJSOKTXOLSVO|JMWSEJSOLSVOKTXO|JMWSEJURKOaWFKWT|JMWSEJURKOYUMQcY|JMWSFJbWMQWTJNSJ|JMWSFJUQJNSJMFbW|JMWSKOaWEJWTFKbW|JMWSKOaWFKUQMRVM|JMWSKOaWFKWTEJbW|JMWSKOaWFKWTMRUN|JMWSKOaWGKUQEJZU|JMWSKOaWGKWTEJTP|JMWSKOaWGKWTLPSL|JMWSKOaWMQeaEJWT|JMWSKOaWMQUREJWT|JMWSKOaWMQWTEJTK|JMWSKOaWMQWTFKTP|JMWSKOaWMQWTGKTP|JMWSKOaWMQWTGKUR|JMWSKOaWMQWTLPTK|JMWSKObWEJUQFKZU|JMWSKObWEJUQGKZU|JMWSKObWEJUQMRVM|JMWSKObWEJURFKWT|JMWSKObWEJURFKYU|JMWSKObWEJURFKZU|JMWSKObWFKUQBFQJ|JMWSKObWFKUQEJZU|JMWSKObWFKUQMRVM|JMWSKObWFKUREJWT|JMWSKObWFKUREJYU|JMWSKObWFKUREJZU|JMWSKObWFKWTLPSL|JMWSKObWGKUQLPSL|JMWSKObWMQWTEJTK|JMWSKObWMQWTLPTK|JMWSKOUQGKQJEWaT|JMWSKOUQGKQJEWbS|JMWSKOUQMRVMIRZU|JMWSKOUREJaWFKWT|JMWSLOSLHOUREJaW|JMWSLOSLHOVRMVZL|JMWSLPSOKTXOEJUR|JMWSLPSOKTXOMQaW|JMWSLPSOKTXOMQbW|JMWSLPSOKTXOMQUR|JMWSMRUNKRVMIRbW|JMWSMRUNKRVMIRZU|JMWTEJbWAETPMQWS|JMWTEJbWJNfbMRVM|JMWTEJbWJNURNUZJ|JMWTEJbWLOfbMQTP|JMWTEJbWMQURLOTP|JMWTEJbWMQWSAESO|JMWTEJbWMQWSLPSO|JMWTEJTOKTXOLSVO|JMWTEJTOLSVOKTXO|JMWTEJTPAEURKOaW|JMWTEJTPLObWOTXO|JMWTEJTPMQbWJNVS|JMWTEJTPMQbWLOWS|JMWTEJTPMQXTLObX|JMWTEJUQMRVMIRTP|JMWTFJUQLPZUPWaT|JMWTKNaWNSWNMRVM|JMWTKNTOLSVOEJbW|JMWTKNTOLSVOEJUR|JMWTKNTPMQXTEJaW|JMWTKNVRMVaKGNbW|JMWTLObWEJfbAETP|JMWTLObWEJTPMQUR|JMWTLObWEJTPMQWS|JMWTLObWEJWSAESL|JMWTLObWEJWSMQSL|JMWTLObWHLTPMRUN|JMWTLObWMQWSEJSL|JMWTLObWMRUNKRVM|JMWTLObWMRVMIRUN|JMWTLOUREJbWJNTP|JMWTLPTOKTXOMQbW|JMWTLPTOKTXOMQUR|JMWTLPUQPWQJENbJ|JMWTMQTPEJXTJMTO|JMWTMRUNKRVMIRTO|JMWTMRUNKRVMIRZU|JMWTMRVMIRUNKRaW|JMWTMRVMIRUNKRTO|JMWTMRVMIRUNKRTP|JMXTLObXEJfbMQTP|JMXTLPbXMQTOKTXO|JMXTLPbXMQVSKNSJ|JMXTLPUQGLQJFMbX|JMXTLPUQHLQJFMVS|JMXTLPUQMRVMIRZU|JMXTLPVSHLbXDHeb|JMXTLPVSMQaVEJea|JNUQEJWSNWbSKOZU|JNUQEJWTAETPLObW|JNUQEJWTAETPLOVR|JNUQEJWTLPbWGLZU|JNUQEJWTNRVMIRbW|JNUQEJYUAEVRIMRI|JNUQEJZUAEURNUYR|JNUQEJZUAEWTLOVR|JNUQEJZUAEWTLPQM|JNUQEJZULOURNUQZ|JNUQEJZULPURNUQZ|JNUQEJZULPVRGLRM|JNUQEJZULPWTPWaT|JNUQKOWTGKQMIRVM|JNUQKOWTNRTKGNVM|JNUQLOWSNWbLHOYU|JNUQLOWTEJbWAETP|JNUQLOWTEJZUHLUR|JNUQLOWTEJZUNScZ|JNUQLOWTEJZUNSdZ|JNUQLOWTEJZUNSVR|JNUQLOZUEJWTNSVR|JNUQLPVSEJSOKTXO|JNUQLPZUEJURNUQZ|JNUQNRVMIRWSEJbW|JNUQNRVMIRWSEJSN|JNUQNRVMIRWSEJSO|JNUQNRVMIRWSLOSL|JNUQNRVMIRWTEJbW|JNUQNRVMIRWTEJTP|JNUQNRVMIRWTEJZV|JNUQNRVMIRWTKNTP|JNUQNRVMIRWTKNZU|JNUQNRVMIRWTLObW|JNUQNRVMIRWTLOTP|JNUQNRVMIRWTLOZU|JNUQNRVMIRZUKNdZ|JNUQNRVMIRZUKNWT|JNUQNRVMIRZULOUN|JNUQNRVMIRZVEIVM|JNUQNSWNKRVMIRZV|JNURNUYREJRMIRVM|JNURNUYREJWSKObW|JNURNUYREJWSLOSL|JNURNUYREJWTAETP|JNURNUYREJWTJMTO|JNURNUYREJWTJMTP|JNURNUYREJWTJNRM|JNURNUYREJWTLObW|JNURNUYREJWTLOTP|JNURNUYREJWTLPTO|JNURNUYRFJZULPUQ|JNURNUYRKNRKGNVS|JNURNUZQEJWSKObW|JNURNUZQEJWSKOYU|JNURNUZQKNVRNUQZ|JNURNUZQLOWSGLYU|JNURNUZQLPWSPTXO|JNVREJaVAEVSLPRM|JNVREJaVBEWTJMTP|JNVREJaVJMUQNUQJ|JNVREJaVJMXTLObX|JNVREJaVJMXTLPUQ|JNVREJaVJMXTMQbX|JNVREJaVJMXTMQTP|JNVREJaVLOWTBEbW|JNVREJaVLOWTBETP|JNVREJaVLOWTBEUQ|JNVREJaVLOWTHLTP|JNVREJaVLOWTJMbW|JNVREJaVLOWTJMUQ|JNVREJaVLPeaGLUQ|JNVREJaVLPeaGLVS|JNVREJaVLPeaGLWT|JNVREJaVLPVSGLZV|JNVREJaVLPVSHLZV|JNVREJaVLPXTGLWS|JNVREJaVLPXTHLbX|JNVREJWSNWaTJMda|JNVREJWSNWbSJMZV|JNVREJWTBEbWJMTP|JNVREJWTBEZVJMbW|JNVREJWTBEZVJMUQ|JNVREJWTJMaVMQea|JNVREJWTJMaWMVZJ|JNVREJWTJMTPMVZJ|JNVREJWTJMUQMVZJ|JNVREJWTJMUQNUQJ|JNVREJWTJMZVLOTP|JNVREJWTJMZVMQdZ|JNVREJWTLObWBETP|JNVREJWTLObWJMUQ|JNVREJWTLObWOSaV|JNVREJWTLObWOSTP|JNVREJXTBETOLSaV|JNVREJXTJMTPMVZJ|JNVREJXTJMUQNUQJ|JNVREJXTLOTPBEaV|JNVREJXTLOTPJMWS|JNVREJXTLOTPOTbX|JNVREJXTLOTPOTZV|JNVREJXTLPaVHLbX|JNVREJXTLPbXGLZV|JNVREJXTLPbXHLaV|JNVREJXTLPbXHLZV|JNVREJXTLPZVGLbX|JNVREJXTLPZVJMUQ|JNVREJZVAEVSLPaV|JNVREJZVJMUQNUQJ|JNVREJZVJMUQNUQZ|JNVREJZVJMWTLObW|JNVREJZVJMWTMQcZ|JNVREJZVLOUQNUQZ|JNVREJZVLOWTNScZ|JNVREJZVLOWTNSUQ|JNVREJZVLPUQNUQZ|JNVRFJaVJMUQNUQJ|JNVRFJaVJMWSNWbS|JNVRFJaVJMWTEJbW|JNVRFJaVJMWTMQTO|JNVRFJaVJMWTMQTP|JNVRFJaVLPXTGLbX|JNVRFJWSNWbSJMRN|JNVRFJWSNWbSJMSN|JNVRFJWTJMaVLOUQ|JNVRFJWTJMaVMQTO|JNVRFJWTJMTPMVZJ|JNVRFJWTJMUQMVZJ|JNVRFJWTJMZVMQcZ|JNVRFJWTLObWJMTP|JNVRFJWTLOTPJMbW|JNVRFJWTLOZVNScZ|JNVRFJWTLOZVNSdZ|JNVRFJWTLOZVNSUQ|JNVRFJZVBFWSNWbS|JNVRFJZVJMUQNUQZ|JNVRFJZVJMWTMQcZ|JNVRLOWTEJbWHLTP|JNVRLOWTEJbWJMTP|JNVRLOWTFJbWJMTP|JNVRLOZVEJWTNSUQ|JNVRLOZVGLUQNUQZ|JNVRLPWTPWbJFVaR|JNVRLPXTGLbXEJaV|JNVRLPZVGLRMIRVM|JNVRLPZVGLUQNUQZ|JNVRLPZVHLcZEJVS|JNVRLPZVHLUQNUQZ|JNVRLPZVHLUQNUYR|JNVRLPZVHLVSDHSJ|JNVRLPZVHLWTPWbJ|JNVSEJaVAEVRLPRM|JNVSEJaVKOdaOTXO|JNVSEJaVKOeaFKUR|JNVSEJaVKOeaGKUR|JNVSEJaVKOUQFKZU|JNVSEJaVKOUQGKZU|JNVSEJaVKOURNUYR|JNVSEJaVKOURNUZQ|JNVSEJaVLOSLHOWT|JNVSEJaVLPUQGLZU|JNVSEJaVLPVRGLZV|JNVSEJSOKTWPLObW|JNVSEJSOLSURNUWE|JNVSEJUQAEZVIMcZ|JNVSEJUQAEZVIMdZ|JNVSEJUQAEZVIMYU|JNVSEJUQIMZUAEcZ|JNVSEJUQIMZUMRcZ|JNVSEJUQIMZUMRdZ|JNVSEJUQIMZUMRXT|JNVSEJUQIMZVNRWT|JNVSEJUQKOYUOVaK|JNVSEJUQLPZUGLaV|JNVSEJURNUYRJNSJ|JNVSEJURNUYRKORN|JNVSEJZVKOUQGKYU|JNVSEJZVKOUQNRVM|JNVSEJZVKOURNUYR|JNVSFJaVKOUQGKZU|JNVSFJaVKOURNUYR|JNVSFJaVLPXTCFUQ|JNVSFJURNUZQBFYU|JNVSFJZVKOUQGKYU|JNVSFJZVKOURNUYR|JNVSLOSJENaVOSVO|JNVSLOSJENUQAEWS|JNVSLOSJENUQFJWT|JNVSLOSJENUQHLWT|JNVSLOSJENUQHLZU|JNVSLOSJENWSOVZJ|JNVSLOSJENWTAEUQ|JNVSLOSJENWTHLUQ|JNVSLOSJFMWTMQbW|JNVSLOSJFMWTMRUN|JNVSLOSLHOUQNRWT|JNVSLOSLHOURNUYR|JNVSLOSLHOWTIMaV|JNVSLPSJFMWSGLaV|JNVSLPSJFMWSHLaV|JNVSLPSJFMWSHLUQ|JNVSLPSJFMWTPWbS|JNWSNWaTEJeaJNUQ|JNWSNWaTEJeaLPUR|JNWSNWaTEJUQAEZU|JNWSNWaTIMTPLOUQ|JNWSNWaTIMUREITP|JNWSNWaTKNbWFKTP|JNWSNWaTKNbWFKVR|JNWSNWaTKNbWLPWS|JNWSNWaTKNTPLOVR|JNWSNWaTLObWGLWS|JNWSNWaTLOdaEJbW|JNWSNWaTLOeaFJbW|JNWSNWbSEJaWKOUQ|JNWSNWbSEJfbKObW|JNWSNWbSEJUQKOZU|JNWSNWbSEJXTLPSO|JNWSNWbSIMaWMQUR|JNWSNWbSIMaWMQWT|JNWSNWbSIMebMQSO|JNWSNWbSIMfbKObW|JNWSNWbSIMfbMQbW|JNWSNWbSIMUQLPQJ|JNWSNWbSKNSJENfb|JNWSNWbSLOSLHOfb|JNWSNWbSLPfbEJbW|JNWSNWbSLPfbEJUQ|JNWSNWbSLPfbFJbW|JNWSNWbSLPfbGLUR|JNWTEJaWAEeaLPVR|JNWTEJaWBETPNRVM|JNWTEJaWLOdaGLTP|JNWTEJaWLPeaAEVR|JNWTEJaWLPeaAEVS|JNWTEJbWAETPLOVS|JNWTEJbWAEUQNSVO|JNWTEJbWAEVRLPaV|JNWTEJbWAEVSIMTO|JNWTEJbWJMebMQTO|JNWTEJbWJMebMRVM|JNWTEJbWJMfbMQTO|JNWTEJbWJMfbMRVM|JNWTEJbWJMTPMQfb|JNWTEJbWJMTPMQUR|JNWTEJbWJMTPMQWT|JNWTEJbWJMTPMRVM|JNWTEJbWJMTPNRUN|JNWTEJbWJMUQMRVM|JNWTEJbWJMUQNRQJ|JNWTEJbWJMURNUZJ|JNWTEJbWJMVSFJTP|JNWTEJbWJMVSMQSJ|JNWTEJbWLOfbAEVR|JNWTEJbWLPTOKTXO|JNWTEJTOKTXOLSVO|JNWTEJTOLSVOKTXO|JNWTEJTPBEbWJMUQ|JNWTEJTPJMbWBEUQ|JNWTEJTPJMbWMQUR|JNWTEJTPJMbWMQWS|JNWTEJTPJMbWMQWT|JNWTEJTPJMbWMRVM|JNWTEJTPJMbWNRUN|JNWTEJTPJMUQNRQJ|JNWTEJTPJMVRMVZJ|JNWTEJTPJMVSNWbS|JNWTEJTPJMXTMQTO|JNWTEJTPJMXTMRVM|JNWTEJTPJMXTNRUN|JNWTEJTPLObWOTXO|JNWTEJTPLOUQNRVM|JNWTEJTPLOURNUYR|JNWTEJTPLOVRBEbW|JNWTEJTPLOVRJMUQ|JNWTEJUQAETPLObW|JNWTEJUQNRVMIRTP|JNWTEJUQNRVMIRZV|JNWTEJURNUZQAEYU|JNWTEJVRBEbWJMTP|JNWTEJVRJMaWMVZJ|JNWTEJVRJMbWMVZJ|JNWTEJVRJMUQMVZJ|JNWTEJVRJMUQNUQJ|JNWTEJVRLObWBEaV|JNWTEJVRLOZVNSUQ|JNWTFJaWJMVSMQSJ|JNWTFJaWLPeaGLUQ|JNWTFJbWBFTPNRUN|JNWTFJTPBFbWJMWT|JNWTFJTPBFVRJMZV|JNWTFJTPJMbWMRVM|JNWTFJTPJMXTMRVM|JNWTFJUQBFTPLObW|JNWTFJURNUYRJNRM|JNWTFJURNUYRKOTK|JNWTFJVRJMaVMQTP|JNWTFJVRJMZVMQcZ|JNWTLOaWHLTPNRVM|JNWTLObWHLTPNRUN|JNWTLObWHLUQNRVM|JNWTLObWHLUQNSWN|JNWTLObWNRUNKRVM|JNWTLOUQNRVMIRbW|JNWTLOVREJaVBEbW|JNWTLOVREJbWJMUQ|JNWTLOVREJTPJMUQ|JNWTLOVREJZVAEUQ|JNWTLOVRFJbWJMfb|JNWTLOVRFJbWJMTP|JNWTLOVRFJTPJMUQ|JNWTLPUQPWbJENXT|JNWTLPUQPWbJFMQJ|JNWTNRUNKRVMIRaW|JNWTNRUNKRVMIRbW|JNWTNRUNKRVMIRTO|JNWTNRUNKRVMIRTP|JNWTNRUNKRVMIRZU|JNWTNRVMIRUNKRaW|JNWTNRVMIRUNKRTO|JNWTNRVMIRUNKRTP|JNWTNRVMIRUNKRZU|JNWTNSVOLSaVKOTK|JNXTEJbXJMVSMQSJ|JNXTEJTOLSVOKTWP|JNXTEJTPJMWSNWbS|JNXTEJTPLOUQOTZU|JNXTLObXFJVRJMTP|JNXTLObXHLfbLPVS|JNXTLObXHLTPNRUN|JNXTLObXHLTPNRVM|JNXTLObXHLUQNRVM|JNXTLObXHLUQNSWN|JNXTLObXNRUNKRVM|JNXTLObXNRVMIRUN|JNXTLOTPNRVMIRUN|JNXTLOTPOTVSTXSJ|JNXTLPbXGLVRLOaV|JNXTLPbXGLVSDGSJ|JNXTLPbXGLVSLOSL|JNXTLPbXHLVSDHSJ|JNXTLPbXNRUNKRVM|JNXTLPbXNRVMIRUN|JNXTLPUQEJVSAEbX|JNXTLPUQEJZUGLbX|JNXTLPUQEJZUGLVR|JNXTLPUQEJZUHLVS|JNXTLPUQFJVSGLbX|JNXTLPUQGLbXLOZU|JNXTLPUQGLYULObX|JNXTLPUQGLZUDGbX|JNXTLPUQGLZULObX|JNXTLPUQHLVSDHSJ|JNXTLPUQHLVSEJbX|JNXTLPUQHLZULObX|JNXTLPUQNRVMIRZU|JNXTLPVREJaVHLbX|JNXTLPVREJbXGLZV|JNXTLPVREJbXHLaV|JNXTLPVREJbXJMTO|JNXTLPVRFJbXJMTO|JNXTLPVRGLaVLObX|JNXTLPVRGLbXEJaV|JNXTLPVRHLaVEJbX|JNXTLPVSEJUQGLbX|JNXTLPVSGLSJFMbX|JNXTLPVSHLSJENZV|JNXTNRUNKRVMIRZU|KNVRFKWSNWbSJMRN|KNVRFKWTJMaVEJTO|KNVRFKWTJMTPMVZJ|KNVRGKZVJMUQNUQZ|KNVRGKZVJMWTDGTP|KNVRGKZVJMWTDGUQ|KNVRLPRKFOURGKZV|KNVSFKaVLPXTCFUQ|KNVSIMUQEIXTLPbX|KNVSIMXTEITPMRWT|KNVSIMXTFKTOKTWP|KNWSNWbSIMXTLPTO|KNWSNWbSLPebGLSO|KNWSNWbSLPebGLUQ|KNWSNWbSLPebJMbW|KNWSNWbSLPebJMUQ|KNWSNWbSLPfbJMbW|KNWTFKbWJMTPMRVM|KNWTFKbWLPVSGLTO|KNWTFKTPBFbWJMfb|KNWTFKTPBFbWJMUQ|KNWTFKTPBFbWNRUN|KNWTFKTPBFUQNRVM|KNWTFKTPBFVRJMbW|KNWTFKTPJMXTMRVM|KNWTGKbWDGVSLOSL|KNWTGKbWJMVRMVZJ|KNWTGKTPLOVRJMPL|KNWTJMTPMRVMIRXT|KNWTJMVRMVaKGNbW|KNWTJMVRMVaKGNea|KNWTJMVRMVaKGNTP|KNWTLPbWNRUNJbfW|KNWTLPURNUYRPWbS|KNWTLPVRPWRKGNaT|KNWTLPVRPWRKGNbS|KNXTLPVSGKbXDGTO|KNXTLPVSGKbXDGUQ|KNXTLPVSGKZVHLcZ|KNXTLPVSIMbXMQTO|KNXTLPVSIMbXMRTO|KOUQGKWSJNSJENZU|KOUQGKWTLPYUPWbL|KOUQGKYULPWSJMQJ|KOUQJNVSOVaKFOWT|KOUQJNVSOVaKGNYU|KOUQJNWSNWaKFObW|KOURFKYUJNWTLPVS|KOURGKYUDGUQOTXO|KOURGKYUJNWSNWaT|KOURGKZUJNWSNWaT|KOURGKZUJNWSNWbS|KOWSFKSNJSURCFYU|KOWTFKTPBFUQJNbW|KOWTFKTPBFURJMYU|KOWTGKTPDGbWOTXO|KOWTGKTPDGUQJNYU|KOWTGKTPKNPGCLbW|KOWTJMTKFOaWBFWT|KOWTJMTKFOaWGKWT|KOWTJMTKFOaWLPea|KOWTJMTKFObWGKWT|KOWTJMTKFObWMRUN|KOWTJMTKFObWMRVM|KOWTJMTKFObWOSVO|KOWTJMTKFOUQMRVM|KOWTJMTKFOUREJbW|KOWTJMTKFOURGKbW|KOWTJMTKFOURMQbW|KOWTJMTKFOVRMVaR|KOWTJMTKGNVRMVaK|KOWTOSVOLSTPFKXT|KOWTOSVOLSTPHLaV|KOWTOSVOLSURJMYU|LOUQHLYULPVSOVZS|LOUQJMQJFMWSHLbW|LOUQJMQJFMWSHLYU|LOUQJMQJFMWTMRVM|LOUQJNWSNWbLGPfb|LOUQJNWSNWbLHOfb|LOURJMWSEJSLHObW|LOVRJMaVHLWTLPUQ|LOVRJNWTFJTPJMZV|LOWSGLbWKNUQFKZU|LOWSGLbWKNURNUYR|LOWSGLbWLPSLPGWS|LOWSGLbWLPSLPGXT|LOWSHLbWJMUQMRVM|LOWSHLSNJSXTOXVH|LOWSHLUQKNZUNWaK|LOWSHLURJMbWMQeb|LOWSHLURJMYUMQcY|LOWSHLURJNSJEUYR|LOWSHLXTOXSNJSVH|LOWTJMbWEJWSAESL|LOWTJMbWEJWSBESL|LOWTJMbWHLTPMRUN|LOWTJMbWMRUNKRVM|LOWTJMbWMRVMIRUN|LOWTJMUREJbWJNfb|LOWTJMUREJbWMQTP|LOWTJNbWNRUNKRVM|LOWTJNbWNRVMIRUN|LOWTJNVRFJTPJMUQ|LPUQGLYUDGcYJMQJ|LPUQGLYUDGURJMQJ|LPUQGLYUDGVRJNZV|LPUQHLWSKNbWFKZU|LPUQHLYUKOVRJMQJ|LPUQHLYUKOWTPWaK|LPUQHLZUKNURNUQZ|LPUQJNQMIRVMEIZV|LPUQJNVSEJSOKTXO|LPUQJNWTPWbJENXT|LPUQJNZUEJURNUQZ|LPURJMXTGLbXEJTO|LPURJNWSNWaTPWbS|LPVRHLZVLOcZGLRM|LPVRHLZVLOWTPWbL|LPVRJMUQMVaREJZU|LPVRJMZVMQcZEJRM|LPVRJMZVMQVSQZdU|LPVSHLaVKOXTOXSN|LPVSHLXTKOTKFVaR|LPVSHLXTKOTKFVZS|LPVSIMXTMQbXEIeb|LPWSGLbWJMURMQfb|LPWSGLSOKTXOLSVO|LPWSGLSOLSVOKTXO|LPWSIMUREISOKTXO|LPWSJMbWFJURJNSQ|LPWSJMSOKTXOMQbW|LPWSJMSOKTXOMQUR|LPWSJMUQEJZUKNcZ|LPWSJNSJFMaWMQWT|LPWSJNSJFMXTPWbS|LPWTPWaTJNTPEJUQ|LPWTPWbSGLSOKTXO|LPWTPWbSIMfbKNbW|LPWTPWbSIMfbMQSO|LPWTPWbSIMUQEIZU|LPWTPWbSIMUREISO|LPWTPWbSIMXTKNTP|LPWTPWbSJMXTMQTP|LPWTPWbSJNSJENXT|LPWTPWbSKNaWGLXT|LPXTKNURNUYRGKTO|LPXTKOTKGNVSFKaV|LPXTKOTKGNVSHLaV";

    // ── [BOOK-V15-1] Parser PDN para novas linhas ────────────────────────────
    // Converte notação algébrica ('c3-d4 d6-e5 ...') para índices [from,to]
    // Todas as linhas são validadas pelo motor antes de entrarem no livro.
    const PDN_EXTRA_LINES = [
        "a3-b4 b6-a5 b2-a3 a7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 d6-c5 d4xb6 e7-d6 b6-a7 d6-e5 g3-f4 e5xg3",
        "a3-b4 b6-a5 b2-a3 a7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 d6-e5 d2-e3 c7-b6 g1-f2 b8-a7 c1-d2 d8-c7",
        "a3-b4 b6-a5 b2-a3 a7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 d6-e5 d2-e3 c7-b6 g1-f2 d8-c7 g3-f4 e5xg3",
        "a3-b4 b6-a5 b2-a3 a7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 d6-e5 d2-e3 e7-d6 g1-f2 b8-a7 c1-d2 d8-e7",
        "a3-b4 b6-a5 b2-a3 a7-b6 a1-b2 d6-e5 e3-d4 h6-g5 g3-f4 g5xe3xc5 b4xd6xf4 b6-c5 f2-e3 g7-h6 c3-d4",
        "a3-b4 b6-a5 b2-a3 c7-b6",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 d6-c5 d4xb6 a5xc7 c3-d4 f6-g5 b2-c3 g5-h4",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 d6-c5 d4xb6 a5xc7 c3-d4 h6-g5 b2-c3 g5-h4",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 f6-e5 d4xf6 g7xe5 b4-c5 d6xb4 a3xc5 b8-c7",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 h6-g5 b4-c5 d6xb4 a3xc5 g7-h6 g1-f2 g5-h4",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 d6-c5 b4xd6 e7xc5 g3-f4 f6-g5 c3-d4 d8-e7",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 d8-c7 g3-f4 e5xg3 h2xf4 e7-f6",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 f6-e5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 d8-c7 g3-f4 e5xg3 h2xf4 g7-f6",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 f6-e5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 g3-f4 e5xg3 h2xf4 f6-g5",
        "a3-b4 b6-a5 b2-a3 c7-b6 c1-b2 b6-c5 g3-f4 f6-e5 c3-d4 e5xc3 b2xd4xb6 a7xc5 h2-g3 a5xc3 d2xb4 g7-f6",
        "a3-b4 b6-a5 b2-a3 c7-b6 e3-d4 b6-c5 d4xb6 a7xc5 d2-e3",
        "a3-b4 b6-a5 b2-a3 f6-e5 e3-f4 g7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 h8-g7 c3-d4 a5xc3xe5 e3-f4 g5xe3",
        "a3-b4 b6-a5 b2-a3 f6-g5 b4-c5 d6xb4 a3xc5 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 c3-b4 a5xc3",
        "a3-b4 b6-a5 b2-a3 f6-g5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "a3-b4 b6-a5 b2-a3 f6-g5 e3-d4 g5-h4 g3-f4 g7-f6 f2-e3 f6-g5 e1-f2 d6-c5 b4xd6",
        "a3-b4 b6-a5 b2-a3 h6-g5 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 g7-h6 g3-f4 f6-g5 b2-a3 h8-g7 c3-d4 c7-d6",
        "a3-b4 b6-a5 e3-d4 a7-b6 d2-e3 d6-c5 b4xd6 e7xc5 d4-e5 f6xd4 c3xe5 c5-b4 e3-f4 f8-e7 e1-d2 e7-d6",
        "a3-b4 b6-a5 e3-d4 a7-b6 d4-e5 f6xd4 c3xe5 a5xc3 b2xd4 d6xf4 g3xe5 g7-f6 e5xg7 h8xf6 a1-b2 c7-d6",
        "a3-b4 b6-a5 e3-d4 d6-c5 b4xd6",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 g7-f6 h2-g3 f6-g5 d4-c5 g5-h4 c5xe7 h4xf2",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 g7-f6 h2-g3 h6-g5 b2-a3 d6-e5 d2-e3 h8-g7",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 g7-f6 h2-g3 h6-g5 g3-h4 f6-e5 h4xf6 e5xg7",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 g7xe5 d2-e3 a7-b6 c3-d4 a5xc3 d4xf6 e7xg5 b2xd4 g5-h4 a1-b2 h6-g5",
        "a3-b4 b6-a5 e3-d4 f6-g5 f2-e3 g5-h4 g1-f2 g7-f6 b2-a3 d6-e5 b4-c5 c7-b6 c1-b2 h8-g7 a3-b4 d8-c7",
        "a3-b4 b6-a5 e3-d4 f6-g5 g3-h4 a7-b6 h4xf6 g7xe5 d4xf6 e7xg5 d2-e3 g5-f4 e3xg5 h6xf4 b2-a3 h8-g7",
        "a3-b4 b6-a5 e3-d4 h6-g5 d4-e5 f6xd4 c3xe5 d6xf4 g3xe5 a5xc3 b2xd4 g7-h6 a1-b2 g5-h4 b2-c3 a7-b6",
        "a3-b4 b6-c5 b2-a3 c5-d4 e3xc5",
        "a3-b4 b6-c5 b2-a3 f6-e5 g3-h4 a7-b6",
        "a3-b4 b6-c5 b2-a3 f6-g5 c3-d4 g7-f6 d4xb6",
        "a3-b4 b6-c5 b2-a3 f6-g5 g3-f4 g7-f6 a1-b2 c7-b6 b4-a5 f6-e5 a5xc7 d8xb6",
        "a3-b4 b6-c5 b2-a3 f6-g5 g3-f4 g7-f6 a1-b2 c7-b6 b4-a5 f6-e5 a5xc7 d8xb6 c3-b4 e5xg3 f2xh4xf6xd8",
        "a3-b4 b6-c5 b4-a5 c5-b4 b2-a3 f6-g5 a3xc5 d6xb4 c3-d4 b4-a3 g3-f4 e7-d6 d4-c5 d6xb4 a5xc3 g7-f6",
        "a3-b4 b6-c5 b4-a5 c5-b4 c3-d4 b4-a3 d4-c5 d6xb4 a5xc3",
        "a3-b4 b6-c5 b4-a5 c5-b4 c3-d4 b4-a3 d4-c5 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 b2-c3 c7-d6 g3-f4 f6-g5",
        "a3-b4 b6-c5 b4-a5 c5-b4 c3-d4 b4-a3 d4-c5 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 g3-f4 f6-g5 b2-c3 e7-d6",
        "a3-b4 b6-c5 b4-a5 c5-b4 c3-d4 b4-a3 d4-c5 d6xb4 a5xc3 a7-b6 g3-f4 b6-c5 c3-b4 f6-g5 b4xd6",
        "a3-b4 b6-c5 b4-a5 f6-g5 g3-f4 g7-f6 c3-d4 g5-h4 d4xb6 a7xc5 b2-c3 c5-b4 c3-d4 b4-a3 d4-e5 f6xd4",
        "a3-b4 b6-c5 b4-a5 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b2-a3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 f2-g3 e7-f6",
        "a3-b4 f6-e5 b4-a5 b6-c5 b2-a3 g7-f6 a1-b2 c7-b6 a5xc7 d8xb6 e3-f4 b6-a5 f4-g5",
        "a3-b4 f6-e5 b4-a5 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b2-a3 e7-d6 c3-b4 g7-h6 d2-c3 h8-g7 e1-d2 h6-g5",
        "a3-b4 f6-e5 b4-c5 b6xd4 e3xc5",
        "a3-b4 f6-e5 b4-c5 d6xb4 c3xa5 b6-c5 e3-f4 e7-d6 b2-a3 g7-f6 d2-c3 d8-e7 c3-b4 c5-d4 c1-b2 f6-g5",
        "a3-b4 f6-g5 b4-a5 e7-f6 g3-h4 f8-e7 b2-a3 g5-f4 e3xg5 h6xf4 c3-b4 f6-g5 h4xf6 g7xe5 a1-b2 h8-g7",
        "a3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 g5-h4 b2-c3 g7-f6 g3-f4 f6-g5 a1-b2 g5xe3 d2xf4 h8-g7",
        "a3-b4 f6-g5 b4-c5 d6xb4 c3xa5 g5-h4 b2-c3 g7-f6 c3-d4 f6-g5 a1-b2 e7-f6 b2-c3 f6-e5 d4xf6 g5xe7",
        "a3-b4 h6-g5 b4-a5 g5-f4 e3xg5 f6xh4 c3-d4 g7-f6 b2-c3 h8-g7 a1-b2 f6-g5 f2-e3 h4xf2 e1xg3 g5-h4",
        "a3-b4 h6-g5 b4-a5 g5-h4 c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 h8-g7 a1-b2 g7-f6 b2-a3 b6-c5 c3-d4 e5xc3",
        "a3-b4 h6-g5 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 f6-e5 g3-h4 g5-f4 b2-c3 a7-b6 a1-b2 b6-c5 b2-a3 c7-d6",
        "a3-b4 h6-g5 b4-c5 d6xb4 c3xa5 g5-h4 b2-c3 f6-e5 a1-b2 g7-f6 e3-f4 e7-d6 f4-g5 d8-e7 c3-b4 h8-g7",
        "a3-b4 h6-g5 b4-c5 d6xb4 c3xa5 g5-h4 b2-c3 g7-h6 c3-d4 f6-g5 a1-b2 e7-d6 d4-c5 d6xb4 a5xc3 b6-a5",
        "a3-b4 h6-g5 b4-c5 d6xb4 c3xa5 g5-h4 b2-c3 g7-h6 g3-f4 f6-g5 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7",
        "a3-b4 h6-g5 g3-f4 b6-c5 f4xh6 c5xa3 c3-d4 a7-b6 h2-g3 b6-a5 g3-h4 f6-e5 d4xf6 g7xe5 b2-c3 h8-g7",
        "a3-b4 h6-g5 g3-f4 b6-c5 f4xh6 c5xa3 h2-g3 f6-e5 c3-d4 e5xc3 b2xd4 g7-f6 a1-b2 a7-b6 g3-h4 b6-a5",
        "c3-b4 b6-a5 b2-c3 a7-b6 c3-d4",
        "c3-b4 b6-a5 b2-c3 c7-b6",
        "c3-b4 b6-a5 b2-c3 c7-b6 c3-d4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 f6-g5 d2-e3 d8-c7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 f6-g5 d2-e3 g7-f6 b2-c3 d8-c7 a1-b2 f6-e5",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 d8-c7 a1-b2 c7-b6 g3-f4 b6xd4 e3xc5 f6-g5",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 f6-e5 f4xd6 c7xe5 e3-f4 e5xg3",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 f6-g5 g1-h2 g5-h4 c3-b4 a5xc3",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 e3-d4 h8-g7 f2-g3 f6-g5 g3-h4 g5xe3",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 b2-a3 c7-b6 c3-d4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 g3-f4 f6-g5 c3-d4 c7-b6 b2-c3 h8-g7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 c7-b6 c3-b4 a5xc3 d2xb4 b6xd4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 f6-g5 c3-b4 a5xc3 d2xb4 c7-b6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 c7-b6 c3-d4 d8-c7 a1-b2 e7-d6 c5xe7 f6xd8",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g7-f6 d2-e3 g5-h4 g3-f4 c7-b6 b2-c3 f6-g5 a1-b2 e7-d6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g7-f6 d2-e3 g5-h4 g3-f4 f6-g5 c1-d2 h8-g7 h2-g3 c7-b6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 e7-d6 c5xe7 f8xd6 b2-c3 a7-b6 c3-d4 d6-c5 a1-b2 d8-e7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 f4-g5 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 c7-d6 a1-b2 d6xb4 f4-e5 f6xd4 e3xc5xa3 a7-b6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 c3-d4 c7-b6 f4-e5 h8-g7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 c7-b6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 h8-g7 a1-b2 c7-b6 c3-d4 d8-c7 d4-e5 f6xd4",
        "c3-b4 b6-a5 d2-c3 c7-b6 c1-d2 b6-c5 e3-f4 f6-e5 f2-e3 g7-f6 g3-h4 e5xg3 h4xf2 f6-g5 h2-g3 g5-h4",
        "c3-b4 b6-a5 d2-c3 f6-g5 c1-d2 g5-h4 b4-c5 d6xb4 a3xc5 g7-f6 c3-b4 a5xc3 d2xb4 f6-g5 b2-a3 e7-f6",
        "c3-b4 b6-a5 d2-c3 f6-g5 c1-d2 g5-h4 b4-c5 d6xb4 a3xc5 g7-f6 g3-f4 f6-g5 c3-d4 h8-g7 b2-a3 c7-b6",
        "c3-b4 b6-a5 g3-f4 a5xc3 b2xd4",
        "c3-b4 b6-a5 g3-f4 a5xc3 d2xb4 f6-g5 b2-c3 g7-f6 c1-d2 g5-h4 b4-a5 f6-e5 a1-b2 e5xg3 h2xf4 h8-g7",
        "c3-b4 b6-a5 g3-f4 a5xc3 d2xb4 f6-g5 b4-c5 d6xb4 a3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 b2-a3 e7-f6",
        "c3-b4 b6-a5 g3-f4 a5xc3 d2xb4 f6-g5 b4-c5 d6xb4 a3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 b2-a3 h8-g7",
        "c3-b4 b6-a5 g3-h4 a5xc3",
        "c3-b4 b6-a5 g3-h4 a5xc3 d2xb4 d6-e5 b4-a5 e5-f4 e3xg5 h6xf4 b2-c3 f6-e5 c3-b4 a7-b6 c1-b2 e7-d6",
        "c3-b4 b6-c5 b2-c3 a7-b6 b4-a5 b8-a7 c3-b4 c5-d4 e3xc5 b6xd4 d2-e3 f6-e5 e3xc5 c7-b6 a5xc7 d8xb6xd4",
        "c3-b4 b6-c5 b2-c3 f6-e5 a1-b2 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4xd6 c7xe5 a3-b4 f4-g3 h2xf4xd6 e7xc5xa3",
        "c3-b4 b6-c5 b2-c3 f6-e5 a1-b2 e7-f6 g3-h4 f8-e7 f2-g3 e5-d4 c3xe5 f6xd4xf2 g1xe3 e7-f6 e3-f4 f6-e5",
        "c3-b4 b6-c5 b2-c3 f6-e5 a1-b2 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 g3-f4 e5xg3 h2xf4 c7-d6 c3-d4 b4-a3",
        "c3-b4 b6-c5 b2-c3 f6-e5 b4-a5 c5-b4 a3xc5 d6xb4 e3-f4 b4-a3 f4xd6 e7xc5 a1-b2 c5-b4 f2-e3 h6-g5",
        "c3-b4 b6-c5 b2-c3 f6-e5 b4-a5 e5-d4 c3xe5 d6xf4 e3xg5",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 c3-b4 g5xe3 f2xd4xf6 g7xe5 g3-h4 f8-g7 h2-g3 e5-d4",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 g7-f6 d2-e3 f6-g5 a1-b2 g5-h4 c1-d2 c7-b6 b4-a5 f8-g7 a5xc7 d8xb6",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 g7-f6 d2-e3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 g7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 h2xf4 h8-g7 a1-b2 d8-e7",
        "c3-b4 b6-c5 b2-c3 f6-g5 c3-d4 g7-f6 d4xb6",
        "c3-b4 b6-c5 b2-c3 f6-g5 c3-d4 g7-f6 d4xb6 c7xa5xc3 d2xb4 h8-g7 g3-f4 d8-c7 a1-b2 g5-h4 b4-c5 d6xb4",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 a1-b2 g5-h4 b4-a5 f6-e5 c3-b4 e5xg3 h2xf4 h8-g7 d2-c3 g7-f6",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 a1-b2 f8-g7 d2-c3 g5-h4",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 f2-g3 b4-a3 g3-h4 c7-b6 a5xc7 b8xd6",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 h8-g7 a1-b2 g5-h4 h2-g3 f6-e5 f4-g5 h6xf4xh2 e3-d4 c5xe3",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 c3-d4 h8-g7 d4xb6 c7xa5xc3 d2xb4 g5-h4 b4-a5 f6-g5 a1-b2 d8-c7",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 f2-g3 e7-d6",
        "c3-b4 b6-c5 d2-c3 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 c3-d4",
        "c3-b4 b6-c5 e3-f4 f6-e5",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 c3-d4 f6-g5 d4xb6 a7xc5 b2-c3 c5-b4",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 f6-e5 a1-b2 e5xg3",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 c3-d4 g5-h4 d4xb6 c7xa5xc3 d2xb4 f6-g5 b4-a5 h8-g7 a1-b2 d6-c5",
        "c3-b4 b6-c5 g3-h4 f6-e5 b4-a5 e5-f4 e3xg5 h6xf4 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 d6-e5 b4xd6 e7xc5",
        "c3-b4 b6-c5 g3-h4 f6-e5 e3-f4 e5xg3 h2xf4 e7-f6 f2-g3",
        "c3-b4 b6-c5 g3-h4 f6-e5 h2-g3 e5-f4 g3xe5 d6xf4 b4xd6 c7xe5 e3xg5 h6xf4 b2-c3 e7-d6 a3-b4 a7-b6",
        "c3-b4 b6-c5 g3-h4 f6-e5 h4-g5 h6xf4 e3xg5 g7-f6 g5-h6 c7-b6 b4-a5 b8-c7 h2-g3 c5-d4 d2-c3 h8-g7",
        "c3-b4 b6-c5 g3-h4 f6-e5 h4-g5 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 c7-b6 h2-g3 h8-g7 g5-h6 d8-c7",
        "c3-b4 b6-c5 g3-h4 f6-e5 h4-g5 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h8-g7 g5-h6 e5-f4 e1-f2 f4-e3",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 b6-a5",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 b6-a5 c3-d4 c7-d6 d4xb6 a5xc7 d2-c3 a7-b6 c3-b4 b6-c5 a1-b2 h6-g5",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 b6-a5 g3-f4 f6-g5 c3-d4 c7-d6 d4xb6 a7xc5 d2-c3 d8-e7",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 b6-a5 g3-f4 f6-g5 c3-d4 c7-d6 d4xb6 a7xc5 d2-c3 d8-e7 c3-b4 a5xc3",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 c7-d6 c3-b4 b6-a5 c1-b2 a5xc3 b2xd4xb6 a7xc5 a1-b2 d8-c7 b2-c3 c7-b6",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 f6-g5 c3-b4 d8-e7 b4xd6 e7xc5 g3-f4 f8-e7 d2-c3 b6-a5 c3-b4 a5xc3",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 f6-g5 c3-d4 g5-h4 d2-c3 g7-f6 c1-b2 h8-g7 c3-b4 d8-e7 b4xd6 c7xe5xc3",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 f8-e7 c3-b4 e7-d6 b4-a5 d8-e7 g3-h4 f6-e5 h4-g5 h6xf4 e3xg5 g7-h6",
        "c3-b4 d6-e5 b2-c3 b6-a5 e3-d4 c7-b6 b4-c5 h6-g5 g3-f4 g5xe3 d2xf4xd6",
        "c3-b4 d6-e5 b2-c3 e5-f4 g3xe5",
        "c3-b4 d6-e5 b2-c3 f6-g5",
        "c3-b4 d6-e5 b4-a5 b6-c5 b2-c3 c5-d4 e3xc5 e5-f4 g3xe5",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 a1-b2 g5xe3 f2xd4xf6 g7xe5 g3-f4 e5xg3 h2xf4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xd4xf6 g7xe5 g3-h4 d8-e7 e1-f2",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xd4xf6 g7xe5 g3-h4 f8-g7 e1-f2",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xd4xf6 g7xe5 g3-h4 h8-g7 h2-g3 g7-f6",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 d2-e3 g5-h4 a1-b2 g7-f6 c3-b4 h8-g7 b2-c3 d8-e7",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 d6-e5 b2-c3 e5-f4 c3-b4 d8-e7",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b2-c3 g7-f6",
        "c3-b4 d6-e5 b4-a5 b6-c5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 e7-d6 c3-b4 f6-e5 f2-g3 d8-e7 e1-f2 a7-b6",
        "c3-b4 d6-e5 b4-a5 b6-c5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 g7-h6 c3-b4 e7-d6 f2-g3 f8-g7 g3xe5 f6xd4",
        "c3-b4 d6-e5 b4-a5 e7-d6 g3-h4 f8-e7 b2-c3 e5-f4 e3xg5 h6xf4 c3-b4 f6-g5 h4xf6 e7xg5 a1-b2 g7-h6",
        "c3-b4 d6-e5 b4-a5 f6-g5 b2-c3 g5-f4 e3xg5 h6xf4 c3-b4 b6-c5 b4xd6 e7xc5 a1-b2 f8-e7 b2-c3 e5-d4",
        "c3-b4 d6-e5 b4-a5 f6-g5 e3-f4 g5xe3",
        "c3-b4 d6-e5 b4-a5 f6-g5 e3-f4 g5xe3 d2xf4xd6 c7xe5 a5xc7 b8xd6 a3-b4",
        "c3-b4 d6-e5 b4-a5 f6-g5 e3-f4 g5xe3 d2xf4xd6 e7xc5 c1-d2 g7-f6 d2-c3",
        "c3-b4 d6-e5 b4-a5 f6-g5 e3-f4 g5xe3 d2xf4xd6 e7xc5 g3-f4 g7-f6 h2-g3",
        "c3-b4 d6-e5 b4-a5 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b2-c3 b6-c5 c3-b4 c7-d6",
        "c3-b4 d6-e5 d2-c3 b6-a5 c1-d2 c7-b6 e3-f4 d8-c7 f4xd6 c7xe5 g3-f4 e5xg3 h2xf4 f6-g5",
        "c3-b4 d6-e5 d2-c3 f6-g5 b4-a5 g5-f4 e3xg5 h6xf4 g3-h4 b6-c5 c3-b4 e7-d6 f2-g3 g7-f6 e1-f2 h8-g7",
        "c3-b4 d6-e5 d2-c3 f6-g5 e3-d4 g7-f6 b4-a5 c7-d6 a5xc7 d8xb6 g3-h4 b6-c5 d4xb6 a7xc5 f2-g3 b8-c7",
        "c3-b4 d6-e5 e3-f4 e7-d6 d2-e3 f6-g5 b4-c5 b6xd4 e3xc5xe7 g5xe3 f2xd4xf6 g7xe5 b2-c3 f8xd6 g3-h4 a7-b6",
        "c3-b4 d6-e5 e3-f4 e7-d6 d2-e3 f6-g5 b4-c5 b6xd4 e3xc5xe7 g5xe3 f2xd4xf6 g7xe5 g3-h4 f8xd6 h2-g3 a7-b6",
        "c3-b4 d6-e5 e3-f4 e7-d6 f2-e3 b6-c5 g3-h4 e5xg3 h4xf2 f6-e5 h2-g3 g7-f6 g3-f4 e5xg3 f2xh4 f6-e5",
        "c3-b4 d6-e5 e3-f4 f6-g5 f4xd6 c7xe5 b4-a5 d8-c7",
        "c3-b4 d6-e5 e3-f4 f6-g5 f4xd6 c7xe5 b4-a5 d8-c7 g3-f4 g5xe3 f2xd4xf6xd8",
        "c3-b4 d6-e5 e3-f4 f6-g5 f4xd6 e7xc5 b4xd6 c7xe5",
        "c3-b4 d6-e5 g3-f4 e5xg3 h2xf4 b6-a5 b4-c5 f6-g5 a3-b4 a5xc3 b2xd4 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7",
        "c3-b4 f6-e5 b2-c3 b6-c5 e3-f4 c5-d4 a1-b2 g7-f6 d2-e3 c7-b6 e3xc5 b6xd4 g3-h4 e5xg3 c3xe5xc7 b8xd6",
        "c3-b4 f6-e5 b2-c3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5",
        "c3-b4 f6-e5 b2-c3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5 b6-c5 c3-b4 e7-d6 a1-b2 g7-f6 f2-e3 f6-g5",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 b6-c5 c3-b4 e7-d6 a1-b2 g7-f6 f2-e3 f6-g5",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 g7-f6 a1-b2 h8-g7 c3-b4 b6-c5 b4xd6 e7xc5",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 f2-e3 g7-h6 e3xg5 h6xf4 e1-f2 h8-g7 f2-g3 e7-d6",
        "c3-b4 f6-e5 b2-c3 g7-f6 a1-b2 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 g5-h4 a3-b4 h8-g7 d2-e3 g7-f6",
        "c3-b4 f6-e5 b2-c3 g7-f6 a1-b2 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 b6-c5 c3-b4 f4-g3 h2xf4 e5xg3",
        "c3-b4 f6-e5 b2-c3 g7-f6 a1-b2 f8-g7 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 e7-d6 a3-b4 a7-b6 d2-e3 f6-g5",
        "c3-b4 f6-e5 b2-c3 g7-f6 e3-d4 b6-c5 d4xb6 a7xc5 d2-e3 h8-g7 e3-f4 c5-d4 a1-b2 f6-g5",
        "c3-b4 f6-e5 b2-c3 g7-f6 e3-d4 f8-g7 b4-a5 e5-f4 g3xe5 d6xf4 c3-b4 f6-e5 d4xf6 g7xe5 f2-g3 h8-g7",
        "c3-b4 f6-e5 b2-c3 g7-f6 e3-f4",
        "c3-b4 f6-e5 b2-c3 g7-f6 g3-f4 e5xg3 h2xf4 f6-g5 a1-b2 b6-a5 b4-c5 d6xb4 a3xc5 c7-b6 c3-d4 d8-c7",
        "c3-b4 f6-e5 b4-a5 b6-c5",
        "c3-b4 f6-e5 b4-a5 e5-f4 e3xg5",
        "c3-b4 f6-e5 b4-a5 g7-f6 a3-b4 b6-c5 b2-a3 e5-d4 g3-h4 f6-e5 h2-g3 h8-g7 g1-h2 a7-b6 c1-b2 e7-f6",
        "c3-b4 f6-e5 b4-a5 g7-f6 b2-c3",
        "c3-b4 f6-e5 b4-a5 g7-f6 b2-c3 f6-g5 c3-b4 e5-f4 g3xe5 d6xf4 f2-g3 e7-d6 g3xe5 d6xf4 a1-b2 h8-g7",
        "c3-b4 f6-e5 b4-a5 g7-f6 e3-f4 f6-g5 b2-c3 g5xe3 f2xd4xf6 e7xg5 g3-f4 g5xe3 d2xf4 h8-g7 c1-d2 g7-f6",
        "c3-b4 f6-e5 b4-a5 g7-f6 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 h8-g7 c3-b4 d6-c5 b4xd6 c7xe5 a5xc7 b8xd6",
        "c3-b4 f6-e5 b4-a5 g7-f6 g3-h4 e5-f4 e3xg5 h6xf4 f2-g3 h8-g7 g3xe5 d6xf4 b2-c3 b6-c5 c3-b4 e7-d6",
        "c3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4",
        "c3-b4 f6-e5 b4-c5 d6xb4",
        "c3-b4 f6-e5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-d6 c5xe7 f8xd6 d2-e3 a7-b6 e3-f4 b6-c5 b2-c3 d8-e7",
        "c3-b4 f6-e5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 g3-f4 e5xg3 h2xf4 f6-g5 d2-e3 g7-f6 b2-c3 d8-e7",
        "c3-b4 f6-e5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g7-f6 b2-a3 h8-g7 g3-f4 e5xg3 h2xf4 c7-d6 a1-b2 d6xb4",
        "c3-b4 f6-e5 d2-c3 b6-a5 c3-d4 e5xc3 b4xd2 g7-f6 a3-b4 a5xc3 d2xb4 f6-e5",
        "c3-b4 f6-e5 d2-c3 b6-c5 g3-f4 e5xg3 h2xf4 g7-f6 c3-d4 f6-e5 d4xb6 c7xa5xc3 b2xd4xf6 e7xg5 a1-b2 a7-b6",
        "c3-b4 f6-e5 d2-c3 g7-f6 b4-a5 f6-g5 c3-d4 e5xc3 b2xd4 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a5xc3 h8-g7",
        "c3-b4 f6-e5 d2-c3 g7-f6 b4-a5 f6-g5 e3-d4 g5-h4 d4xf6 e7xg5 a3-b4 b6-c5 b2-a3 a7-b6 e1-d2 h8-g7",
        "c3-b4 f6-e5 d2-c3 g7-f6 e3-d4 h6-g5 b4-a5 g5-h4 c3-b4 e5xc3 b4xd2 h8-g7 a3-b4 f6-g5 d2-e3 b6-c5",
        "c3-b4 f6-e5 e3-f4 b6-a5 b2-c3 c7-b6 d2-e3 b6-c5 c3-d4 e5xc3 b4xd2 g7-f6 g3-h4 f6-g5 h4xf6 e7xg5",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xd4xf6 e7xg5 a3-b4 g5-h4 e3-d4 h4xf2 e1xg3",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 a3-b4 g5xe3 f2xd4xf6 g7xe5 g3-h4 h8-g7 h2-g3 g7-f6 d2-e3 b6-c5",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xd4xf6 g7xe5 g3-h4",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 g3-h4 e5xg3 h4xf6 g7xe5 f2xh4 h8-g7 a3-b4 g7-f6 h2-g3 b6-c5",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 g3-h4 g5xe3",
        "c3-b4 f6-e5 e3-f4 e7-f6 d2-e3 f6-g5 b2-c3 g5-h4 c1-d2 b6-c5 a1-b2 c7-b6 b4-a5 d8-c7 c3-b4 f8-e7",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b2-c3 g7-f6 b4-a5 b6-c5",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b2-c3 g7-h6 a1-b2 d6-e5",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 d2-c3 b6-c5 e1-d2 g7-f6",
        "c3-b4 f6-e5 e3-f4 g7-f6 b4-a5 f6-g5 b2-c3 g5xe3",
        "c3-b4 f6-e5 e3-f4 g7-f6 b4-a5 f6-g5 d2-e3 g5-h4 b2-c3 b6-c5 c3-b4 a7-b6 c1-d2 h8-g7 a1-b2 e5-d4",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 c5-d6 e7xc5 f4-e5 c7-b6 e5xc3 c5-b4",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 c5-d6 e7xc5 f4-e5 h6-g5 e5xc3 g5-h4",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 a7-b6 b4-a5 h8-g7 b2-c3 b6-c5 c3-b4 e5-d4",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 h8-g7 b2-c3 a7-b6 b4-a5 b6-c5 c3-b4 e5-d4",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-c5 b2-c3 a7-b6 b4-a5 b8-a7 c3-d4 e5xc3 c1-d2 f6-g5 d2xb4 c5-d4",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 f2xh4xf6 f8-e7 e3-d4 e7xg5 b4-c5 d6xb4",
        "c3-b4 f6-e5 g3-f4 e5xg3 h2xf4 b6-c5 b2-c3 e7-f6 c3-d4 f6-e5 d4xf6 g7xe5xg3 f2xh4 h8-g7 e1-f2 g7-f6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 b6-c5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 b6-c5 a1-b2 a7-b6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 b6-c5 a1-b2 g7-f6 b4-a5 f6-e5 c3-b4 f4-g3 h2xf4 e5xg3",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 f2-g3 e7-d6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 e7-f6 c3-b4 g7-h6 d2-c3 f8-g7 f2-e3 f4xd2",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 e7-f6 c3-b4 g7-h6 f2-g3 h8-g7 g3xe5 f6xd4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 d2-c3 d6-e5 c3-b4 e7-d6 b2-c3 g7-f6 f2-g3 h8-g7",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 e7-f6 b2-c3 f6-e5 f2-g3 b6-c5 c3-b4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 e7-f6 b2-c3 f6-e5 f2-g3 b6-c5 c3-b4 f8-e7 e1-f2 a7-b6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 b6-c5 c3-b4 h8-g7 a1-b2 f6-e5 f2-g3 e7-f6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 f6-g5 h4xf6 e7xg5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 f6-g5 h4xf6 e7xg5 a1-b2 d6-e5 a3-b4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 f6-g5 h4xf6 e7xg5 a1-b2 h8-g7 f2-g3 g7-h6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 a1-b2 b6-c5 f2-g3 a7-b6 g3xe5 d6xf4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 a1-b2 g7-h6 c3-b4 f4-e3 d2xf4 f6-g5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 a1-b2 g7-h6 f2-g3 d6-e5 c3-b4 e7-d6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-b4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-b4 d6-c5 b4xd6 c7xe5 a5xc7 b8xd6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-b4 g7-h6 a1-b2",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 f6-e5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 f2-g3 d6-e5 b4-a5 b6-c5 b2-c3 c5-d4 a1-b2 e7-f6 e1-f2 f8-e7",
        "c3-b4 f6-e5 g3-h4 g7-f6 b4-a5 e5-f4 e3xg5 h6xf4 b2-c3 h8-g7 a1-b2 f6-e5 f2-g3 g7-h6 e1-f2 e7-f6",
        "c3-b4 f6-g5 b2-c3 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 e7-f6 h2-g3 c7-b6 c3-d4 d8-c7 c1-b2 f6-g5",
        "c3-b4 f6-g5 b2-c3 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-b4 f6-g5 b2-c3 d6-e5 b4-a5 e5-d4 e3xc5 b6xd4xb2 a1xc3 g5-h4 c3-d4",
        "c3-b4 f6-g5 b2-c3 d6-e5 e3-f4 g5xe3 d2xf4xd6 c7xe5 b4-a5 g7-f6 a5xc7 b8xd6 a3-b4 a7-b6 a1-b2 b6-c5",
        "c3-b4 f6-g5 b2-c3 d6-e5 e3-f4 g5xe3 d2xf4xd6 c7xe5 b4-a5 g7-f6 a5xc7 d8xb6 a3-b4 h8-g7 b4-a5 b6-c5",
        "c3-b4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 e7-d6 c3-b4 d6-e5 d2-c3 d8-e7 c3-d4 e5xc3",
        "c3-b4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c1-b2 b6-c5 b4xd6 e7xc5 c3-b4 c7-d6 f2-g3 d8-c7",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 g7-f6 c3-d4 b6-c5 d4xb6 a7xc5 g3-f4 h8-g7 a1-b2 f6-g5 b2-c3 c5-b4",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 g7-f6 c3-d4 d6-e5 d2-c3 e7-d6 c3-b4 e5xc3 b4xd2 h8-g7 a3-b4 f8-e7",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 g7-f6 g3-f4 f6-e5 a1-b2 e5xg3 h2xf4 d6-e5 f4xd6 c7xe5 a5xc7 b8xd6",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 g7-f6 g3-f4 f6-e5 a1-b2 e5xg3 h2xf4 h8-g7 c3-d4 b6-c5 d4xb6 a7xc5",
        "c3-b4 f6-g5 b2-c3 g5-h4 c3-d4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 b4-a5 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5",
        "c3-b4 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 b6-c5 a1-b2 h8-g7 b4-a5 c5-b4",
        "c3-b4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 g5-f4 g3xe5 f6xd4 h2-g3 g7-f6",
        "c3-b4 f6-g5 b2-c3 g7-f6 b4-a5 f6-e5 a1-b2 e5-f4 g3xe5 d6xf4 f2-g3 e7-d6 g3xe5 d6xf4 a3-b4 h8-g7",
        "c3-b4 f6-g5 b2-c3 g7-f6 b4-a5 f6-e5 g3-h4 e5-f4 h4xf6 e7xg5 a1-b2 g5-h4 e3xg5 h4xf6 h2-g3 f6-e5",
        "c3-b4 f6-g5 b2-c3 g7-f6 c3-d4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-b4 f6-g5 b2-c3 g7-f6 c3-d4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 g3-f4 f6-g5 c5-b6 a7xc5",
        "c3-b4 f6-g5 b4-a5 b6-c5 g3-f4 g7-f6 b2-c3 c5-b4 a3xc5 d6xb4 f2-g3 b4-a3 g3-h4 c7-b6 a5xc7 b8xd6",
        "c3-b4 f6-g5 b4-a5 b6-c5 g3-h4 g5-f4 e3xg5 h6xf4 f2-g3 e7-f6 g3xe5 d6xf4 b2-c3 d8-e7 g1-f2 c7-d6",
        "c3-b4 f6-g5 b4-a5 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b2-c3 g7-f6 a1-b2 h8-g7 c3-d4 b6-c5 d4xb6 a7xc5",
        "c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b2-c3 b6-c5 c3-d4 c5xe3 f2xd4 g7-h6 a1-b2",
        "c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b2-c3 e7-d6 a1-b2 g7-h6 a3-b4 h8-g7 b2-a3 g7-f6",
        "c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b2-c3 g7-f6 a1-b2 h8-g7 c3-b4 f6-e5 d2-c3 g7-h6",
        "c3-b4 f6-g5 b4-a5 g5-h4 b2-c3 b6-c5 c3-b4 g7-f6 a1-b2 a7-b6 b2-c3 f6-g5 e3-f4 g5xe3 d2xf4 c5-d4",
        "c3-b4 f6-g5 b4-a5 g5-h4 b2-c3 g7-f6 c3-b4 b6-c5 e3-d4 c5xe3 f2xd4 h4xf2 g1xe3 d6-e5 d2-c3 e5-f4",
        "c3-b4 f6-g5 b4-a5 g5-h4 b2-c3 h6-g5 c3-b4 g5-f4 g3xe5 d6xf4 e3xg5 h4xf6 h2-g3 f6-e5 d2-e3 g7-f6",
        "c3-b4 f6-g5 b4-a5 g5-h4 g3-f4 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 a1-b2 a7-b6 h2-g3 g7-f6",
        "c3-b4 f6-g5 b4-a5 g7-f6 g3-h4 g5-f4 e3xg5 h6xf4 b2-c3 h8-g7 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 d6-e5",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 d8-c7 c5-d6 c7xe5 g3-f4 g5xe3",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 b2-a3 a7-b6",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 b2-c3 b4-a3",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 c3-d4 e7-f6 b2-c3 d8-e7",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 g5-h4 b2-c3 g7-f6 c3-d4 f6-g5",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-d6 c5xe7 f8xd6 b2-a3 g5-f4 g3xe5 d6xf4 f2-g3 h6-g5",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 d2-e3 f6-e5 c5-d6 e5-d4 e3xc5 c7xe5 b2-c3 f8-e7",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 d2-e3 f6-e5 c5-d6 e5-f4 g3xe5 c7-b6 b2-c3 d8-e7",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 d2-e3 g5-h4 c1-d2 f6-g5 b2-c3 g7-f6 a1-b2 d8-e7",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 b6-a5",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 c3-b4 h8-g7 d2-e3 g7-f6",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 g3-f4 g5xe3 f2xd4 h8-g7",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 b2-c3 h6-g5 a1-b2 c7-d6 c3-b4 d8-c7 b2-c3 c7-b6",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 c3-b4 h8-g7 b2-c3 e7-f6",
        "c3-b4 f6-g5 d2-c3 b6-a5 c1-d2 d6-e5 g3-f4 e5xg3 f2xh4xf6 g7xe5 g1-f2",
        "c3-b4 f6-g5 d2-c3 b6-a5 c1-d2 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 a7-b6 b4-c5 b6xd4",
        "c3-b4 f6-g5 e3-d4 d6-c5 b4xd6",
        "c3-b4 f6-g5 e3-d4 g7-f6 b4-c5 d6xb4 a3xc5 g5-h4 d4-e5 f6xd4 c5xe3 b6-c5 b2-c3 a7-b6 a1-b2 h8-g7",
        "c3-b4 f6-g5 e3-f4 g5xe3 d2xf4 e7-f6 b4-a5 f6-e5 b2-c3 d8-e7 c1-d2 e7-f6 c3-b4 b6-c5 d2-e3 e5-d4",
        "c3-b4 f6-g5 e3-f4 g5xe3 d2xf4 g7-f6 b4-a5 f6-e5 b2-c3 h8-g7 c3-b4 g7-f6 g3-h4 e5xg3 h2xf4 b6-c5",
        "c3-b4 f6-g5 g3-f4 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 g7-f6 d2-c3 d8-c7 c3-d4 e7-d6",
        "c3-b4 f6-g5 g3-f4 b6-a5 b4-c5 d6xb4 a3xc5 g7-f6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3",
        "c3-b4 f6-g5 g3-f4 b6-c5 b2-c3 g7-f6 a1-b2 g5-h4 b4-a5 f6-e5 c3-b4 e5xg3 h2xf4 h8-g7 b2-c3 g7-f6",
        "c3-b4 f6-g5 g3-f4 b6-c5 b2-c3 g7-f6 a1-b2 g5-h4 b4-a5 f6-g5 c3-d4 h8-g7 d4xb6 a7xc5 b2-c3 c5-b4",
        "c3-b4 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 b4-a5 f6-g5 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 c5-b4",
        "c3-b4 f6-g5 g3-f4 g5-h4 b4-a5 g7-f6 f4-g5 h6xf4 e3xg5 b6-c5 g5-h6 f6-e5 d2-e3 h8-g7 c1-d2 e5-f4",
        "c3-b4 f6-g5 g3-f4 g5-h4 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g7-f6 b2-c3 f6-g5 f2-e3 h8-g7 a1-b2 e7-d6",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 b6-c5 b4-a5 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 c5-b4 a3xc5 d6xb4",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 d6-e5 f4xd6 c7xe5 e3-d4 g5-h4 b4-a5 e7-d6 a5xc7 d8xb6 a1-b2 h6-g5",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 d6-e5 f4xd6 c7xe5 e3-d4 g5-h4 d2-e3 h8-g7 c1-b2 h6-g5 d4-c5 b6xd4",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 a1-b2 e5xg3 f2xh4xf6 e7xg5 e1-f2 g5-h4 b4-a5 b6-c5 c3-b4 a7-b6",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 a1-b2 e5xg3 f2xh4xf6 e7xg5 h2-g3 g5-h4 e1-f2 d6-e5 b4-a5 f8-e7",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 b4-a5 e5xg3",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 b6-c5 b4-a5 c5-b4 a3xc5 d6xb4",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 h8-g7 b4-a5 b6-c5 c3-d4 g5-h4 d4xb6 a7xc5 a1-b2 f6-g5 d2-c3 c5-b4",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 h8-g7 b4-a5 g5-h4 c3-b4 f6-g5 d2-c3 g7-f6 c3-d4 b6-c5 d4xb6 a7xc5",
        "c3-b4 f6-g5 g3-f4 g7-f6 b4-a5 f6-e5 h2-g3 g5-h4 b2-c3 h8-g7 c3-b4 g7-f6 b4-c5 b6xd4 e3xc5 d6xb4",
        "c3-b4 f6-g5 g3-f4 g7-f6 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 h8-g7 d2-e3 h6-g5 h2-g3 g7-h6",
        "c3-b4 f6-g5 g3-f4 g7-f6 h2-g3 b6-a5 g3-h4 a5xc3 b2xd4 d6-e5 f4xd6 c7xe5xc3 d2xb4 g5-f4 e3xg5 h6xf4",
        "c3-b4 f6-g5 g3-h4 b6-a5 h4xf6 a5xc3 b2xd4",
        "c3-b4 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 f2-g3 e7-d6",
        "c3-b4 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 b6-c5 f2-e3 g7-h6 e3xg5 h6xf4 e1-f2 h8-g7 f2-g3 e7-f6",
        "c3-b4 h6-g5 b4-a5 f6-e5",
        "c3-b4 h6-g5 d2-c3 g5-h4 b4-a5 f6-e5 c3-d4 e5xc3 b2xd4 g7-f6 c1-b2 d6-e5 b2-c3 e7-d6 c3-b4 e5xc3",
        "c3-b4 h6-g5 e3-f4 g5xe3 d2xf4 f6-e5 f2-e3 g7-f6 g3-h4 e5xg3 h4xf2 f6-g5 b4-a5 h8-g7 a3-b4 b6-c5",
        "c3-b4 h6-g5 g3-f4 g5-h4 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g7-h6 b2-c3 h8-g7 a1-b2 f6-g5 c3-b4 g5xe3",
        "c3-b4 h6-g5 g3-h4 b6-a5 b4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3",
        "c3-b4 h6-g5 g3-h4 b6-a5 f2-g3 a5xc3 d2xb4 g7-h6 b2-c3 d6-e5 b4-a5 f8-g7 c3-d4 e5xc3 g3-f4 a7-b6",
        "c3-b4 h6-g5 g3-h4 d6-e5 b4-a5 e7-d6 b2-c3 f8-e7 c3-d4 e5xc3 d2xb4 d6-e5 e3-f4 g5xe3 f2xd4 e5xc3",
        "c3-b4 h6-g5 g3-h4 g5-f4",
        "c3-b4 h6-g5 g3-h4 g7-h6 f2-g3 h8-g7 g3-f4 d6-e5 f4xd6 c7xe5 e3-f4 e5xg3 h4xf2 f6-e5 b4-a5 b8-c7",
        "c3-d4 b6-a5 b2-c3 a7-b6 g3-h4 d6-e5",
        "c3-d4 b6-a5 b2-c3 c7-b6 a1-b2 d6-c5 g3-f4 f6-g5 f4-e5 e7-f6 f2-g3 g5-h4 g3-f4 f6-g5 e1-f2 d8-c7",
        "c3-d4 b6-a5 b2-c3 c7-b6 g3-f4 b6-c5 d4xb6 a5xc7 c3-b4",
        "c3-d4 b6-a5 b2-c3 c7-b6 g3-h4 b6-c5 d4xb6 a5xc7 a3-b4 a7-b6 b4-a5 f6-e5 e3-d4 g7-f6 f2-g3 f8-g7",
        "c3-d4 b6-a5 b2-c3 c7-b6 g3-h4 f6-g5 h4xf6 e7xg5 d4-e5 d6xf4 f2-g3 f8-e7 g3xe5 b8-c7 c1-b2 g5-h4",
        "c3-d4 b6-a5 b2-c3 f6-g5 a1-b2 g5-h4 d4-c5 d6xb4 a3xc5 g7-f6 g3-f4 f6-g5 b2-a3 h8-g7 e3-d4 g5xe3",
        "c3-d4 b6-a5 b2-c3 f6-g5 a1-b2 g5-h4 g3-f4 d6-c5 d4xb6 a7xc5 c3-d4 c7-d6 d4xb6 a5xc7 d2-c3 g7-f6",
        "c3-d4 b6-a5 b2-c3 f6-g5 a1-b2 g5-h4 g3-f4 g7-f6 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 e7-f6 f2-e3 h8-g7",
        "c3-d4 b6-a5 b2-c3 f6-g5 d4-c5 d6xb4 a3xc5 g7-f6 g3-f4 h8-g7 a1-b2 g5-h4 f4-g5 h6xf4 e3xg5 h4-g3",
        "c3-d4 b6-a5 d4-c5 d6xb4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 f6-g5 h2-g3 g5xe3 f2xd4 e7-d6 c5xe7 f8xd6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 c7-b6 g3-f4 b6xd4 e3xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f6-g5 a1-b2 g7-f6 g3-f4 g5-h4 f4-g5 h6xf4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 e5-d4 c3xe5 c7-d6 e5xc7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 g3-f4 e5xg3 f2xh4 f6-e5 e3-f4 e5xg3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 g3-f4 e5xg3 h2xf4 f6-e5 f4xd6 c7xe5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 c7-b6 g3-f4 e5xg3 h2xf4 b6xd4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 c7-d6 b2-a3 d6xb4 a3xc5 h8-g7 g3-f4 e5xg3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 h8-g7 c3-d4 e5xc3 b2xd4 f6-g5 c5-d6 c7xe5xc3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 h8-g7 g3-f4 e5xg3 h2xf4 c7-b6 c3-b4 a5xc3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 e3-d4 f6-g5 f2-g3 g5xe3 d4xf2 h8-g7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-a3 g7-f6 a1-b2 g5-h4 g3-f4 f6-g5 b2-c3 c7-b6 e3-d4 g5xe3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 c3-b4 a5xc3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 e7-f6 b2-a3 f6-g5 c3-d4 c7-b6 d2-c3 d8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 g3-f4 f6-g5 c3-d4 h8-g7 c5-b6 a7xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 c3-d4 c7-b6 f4-g5 h6xf4 e3xg5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 c3-d4 f6-e5 d4xf6 e7xg5 a1-b2 h8-g7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 f6-g5 c3-b4 a5xc3 d2xb4 e7-f6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 h8-g7 a3-b4 f6-e5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 h8-g7 c3-b4 a5xc3 d2xb4 h6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 c3-d4 c7-b6 g3-f4 f6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 c3-d4 h8-g7 g3-f4 f6-g5 c5-b6 a7xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 c1-b2 g5-h4 b2-a3 h8-g7 c3-d4 c7-b6 e3-f4 h6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 c3-d4 g5-h4 g3-f4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 c7-d6 c1-b2 d6xb4 f4-e5 f6xd4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 c7-d6 c3-b4 a5xc3 d2xb4 g5-h4 a1-b2 f6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 e7-d6 c5xe7 f8xd6 a1-b2 d6-c5 c3-d4 c7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 c3-d4 f6-g5 a1-b2 c7-b6 f4-e5 h8-g7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 e7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 f4-g5 h6xf4 e3xg5 c7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 f4-g5 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 h8-g7 a1-b2 e7-d6 c5xe7 f8xd6 f2-g3 a5-b4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 h8-g7 a1-b2 g5-h4 f4-g5 h6xf4 e3xg5 h4-g3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 e7-f6 d2-e3 c7-b6 g3-f4 d8-c7 h2-g3 g5-h4 f4-e5 f6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 e7-f6 b2-c3 g5-h4 h2-g3 f6-g5 c5-d6 c7xe5 f4xd6 a7-b6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 c3-d4 c7-b6 f4-e5 d8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 e3-d4 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 c7-b6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 e3-d4 e7-f6 d2-e3 c7-b6 c1-d2 f6-g5 h2-g3 d8-e7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 c3-d4 c7-b6 f4-e5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 c3-d4 c7-b6 f4-e5 d8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 c3-d4 c7-b6 f4-e5 h8-g7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 c7-b6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 h6-g5 g3-f4 g7-h6 b2-c3 h8-g7 a1-b2 c7-d6 b2-a3 d6xb4 a3xc5 g5-h4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 h6-g5 g3-f4 g7-h6 e3-d4 g5xe3 d2xf4 h8-g7 h2-g3 c7-b6 d4-e5 f6xd4",
        "c3-d4 b6-a5 e3-f4 f6-g5 d4-c5 g5xe3 f2xd4 d6xb4 a3xc5 g7-f6 d2-e3 f6-g5 g3-f4 h8-g7 h2-g3 g5-h4",
        "c3-d4 b6-a5 g3-f4 c7-b6 f4-g5 h6xf4 e3xg5",
        "c3-d4 b6-a5 g3-f4 f6-g5 d4-c5 d6xb4 a3xc5 g7-f6 b2-c3 g5-h4 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-d4 b6-a5 g3-h4 f6-g5 h4xf6 g7xe5xc3 b2xd4 h6-g5 f2-g3 g5-h4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5 e3-f4 g7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 h8-g7 h2-g3 g5-f4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 c3-d4 h8-g7 d4xb6 c7xa5 c1-b2 f6-e5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 a1-b2 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-d4 c5xe3 f2xd4 g7-f6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 a1-b2 g5-h4 c3-d4 c5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 b8-a7 g3-f4 g7-f6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 g5-h4 b2-c3 g7-f6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 g3-f4 g5-h4 d4-c5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 g3-f4 g5-h4 d4-c5 b8-a7",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g7-f6 c3-d4 c7-b6 d4-e5 f6xd4 a3-b4 c5xa3 e3xc5xa7 g5xe3",
        "c3-d4 b6-c5 d4xb6 a7xc5 d2-c3 c7-b6 g3-h4 b6-a5 c3-b4 a5xc3",
        "c3-d4 b6-c5 d4xb6 c7xa5 a3-b4 a5xc3 b2xd4 b8-c7 a1-b2 c7-b6 d2-c3 b6-a5 e1-d2 d6-c5 d4xb6 a5xc7",
        "c3-d4 b6-c5 d4xb6 c7xa5 b2-c3 f6-g5 c3-d4 a5-b4 a3xc5 d6xb4 a1-b2 b4-a3 b2-c3 a7-b6 g3-h4 b8-a7",
        "c3-d4 d6-c5 b2-c3 c7-d6 a1-b2 d6-e5 g3-f4 e5xg3 h2xf4 f6-g5 f4-e5 b6-a5 d4xb6 a5xc7 e3-f4 g5xe3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c1-b2 f6-g5 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 b4-a5 g7-f6 g3-f4 e5xg3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 c1-d2 g7-f6 d2-c3 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 e1-d2 b8-a7 g3-h4 a7-b6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 b4-a5 b6-c5 e3-f4 f6-e5 b2-c3 c5-d4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 b4-a5 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 d6-e5 g3-f4 e5xg3 h2xf4 f6-e5 f4xd6 c7xe5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 b2-c3 a7-b6 b4-a5 e7-f6 c3-b4 f6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 b2-c3 a7-b6 e3-d4 b6-a5 d4xf6 g7xe5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 d2-c3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 e3-f4 a7-b6 b2-c3 b6-c5 b4-a5 c5-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 b2-c3 g5-h4 b4-c5 d6xb4 c3xa5 g7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 b2-c3 g5-h4 c3-d4 d6-e5 d4xf6 g7xe5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 b2-c3 g7-f6 b4-a5 g5-h4 c3-b4 f6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 b4-c5 d6xb4 a3xc5 g7-f6 b2-c3 g5-h4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 b4-a5 g5-f4 g3xe5 d6xf4 e3xg5 f6xh4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 b4-c5 d6xb4 a3xc5 g5-h4 b2-a3 g7-h6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g5-h4 b2-c3 a7-b6 f4-g5 b6-c5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 a7-b6 b4-a5 f6-e5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 a7-b6 b4-a5 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 f6-e5 h2-g3 g5-h4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 h8-g7 b4-c5 d6xb4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b4-c5 d6xb4 a3xc5 g5-h4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-h4 f6-e5 h4xf6xd4 d6-c5 b4xd6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5 d6-c5 g3-f4 e7-d6 a1-b2 f6-e5 b2-c3 e5xg3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5 d6-c5 g3-h4 e7-d6 f2-g3 f8-e7 a1-b2 f6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5 f6-g5 d2-c3 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-e5 d2-c3 c7-b6 c1-b2 b6xd4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-e5 d2-c3 g7-f6 g3-f4 e5xg3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 a1-b2 g7-f6 g3-f4 g5-h4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-e5 a1-b2 a7-b6 b4-a5 e5-f4 e3xg5 h6xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-e5 c1-d2 a7-b6 b4-a5 b6-c5 c3-b4 e5-f4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-e5 c1-d2 a7-b6 e3-d4 b6-a5 d4xf6 g7xe5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-e5 c1-d2 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5 c3-d4 g5-f4 g3xe5 d6xf4xd2 c1xe3 g7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5 c3-d4 g5-h4 d4-c5 c7-b6 b4-a5 b6xd4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 d6-e5 d2-c3 h6-g5 b4-a5 g5-h4 a3-b4 e7-d6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 h6-g5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 g7-h6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-f4 f6-g5 d2-e3 g5-h4 c1-d2 d6-c5 b4xd6 e7xc5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 g3-f4 f6-g5 a1-b2 g7-f6 b4-c5 d6xb4 a3xc5 g5-h4",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 c3-b4 a7-b6 b4-a5 b6-c5 h2-g3 f6-e5 d2-c3 h6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 c3-b4 f6-e5 f2-g3 g7-f6 a1-b2 f6-g5 g3-h4 e5xg3",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 c3-b4 f6-g5 a1-b2 g5-h4 b2-c3 a7-b6 b4-a5 g7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 a1-b2 g5-h4 c3-d4 g7-f6 b2-c3 f6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-h4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 c3-b4 b6-c5 e3-d4 c5xe3 d2xf4 f6-g5",
        "c3-d4 d6-c5 b2-c3 e7-d6",
        "c3-d4 d6-c5 b2-c3 e7-d6 a1-b2 d6-e5 g3-f4 e5xg3 h2xf4 f6-g5 f2-g3 g5-h4 g1-h2 h4xf2 e1xg3 b6-a5",
        "c3-d4 d6-c5 b2-c3 e7-d6 a1-b2 d6-e5 g3-h4 c5-b4 a3xc5 e5-f4",
        "c3-d4 d6-c5 b2-c3 e7-d6 c1-b2 h6-g5 g3-f4 g7-h6 c3-b4 g5-h4 b4-a5 h8-g7 f2-g3 h4xf2 e1xg3 h6-g5",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xa5xc3 c1-d2",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 f6-g5 g3-f4 g7-f6 b4-a5 h8-g7 d2-c3 d8-e7 h2-g3 c5-b4 a3xc5 d6xb4xd2",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 a1-b2 g7-h6 g3-f4 f6-g5 b2-c3 d8-e7 c3-b4 e7-f6",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 d2-c3 f6-g5 g3-f4 d8-e7 f4xh6 c5-b4 a3xc5 d6xb4xd2xf4",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g7-h6 g3-f4 h8-g7 f2-g3 g5-h4",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g7-h6 g3-f4 h8-g7 f2-g3 g5-h4 a1-b2 h4xf2 e1xg3 f8-e7",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 g3-f4 g7-h6 b4-a5 h8-g7 d2-c3 g5-h4 c3-b4 f6-g5 a1-b2 g7-f6",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 g3-f4 g7-h6 b4-a5 h8-g7 f2-g3 g5-h4 f4-g5 h4xf2 g5xe7 d8xf6",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-e5 d4xf6 g7xe5xg3 h2xf4 h8-g7 f2-g3 g7-f6 g3-h4 f8-e7 g1-h2 f6-g5",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-g5 c1-b2 f8-e7 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xa5xc3 b2xd4 d8-c7",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 d6-e5 f2-g3 c7-d6 g3-f4 e5xg3 h4xf2 b6-a5 d4xb6 a5xc7 c3-d4 f6-e5",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 f8-e7 f2-g3 d6-e5 g3-f4 e5xg3 h2xf4 f6-g5 h4xf6 g7xe5xg3 g1-h2 e7-f6",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 f8-e7 f2-g3 d6-e5 g3-f4 e5xg3 h4xf2 h6-g5 c3-b4 c7-d6 b4-a5 b8-c7",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 f8-e7 h2-g3 d6-e5 g3-f4 e5xg3 c3-b4 e7-d6 b4-a5 h6-g5 a1-b2 g3-h2",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 h6-g5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xa5xc3 h2-g3 c3-b2 a1xc3 d6-e5",
        "c3-d4 d6-c5 b2-c3 f6-g5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xe5xc3 d2xb4 a5xc3 c1-b2",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xa5xc3 c1-b2",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 c7-d6 b4-a5 d8-c7 a1-b2 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 f2-e3 g7-h6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 e7-d6 b4-a5 f8-e7 g3-f4 g5-h4 h2-g3 g7-f6 a1-b2 f6-g5 b2-c3 c5-b4",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 e7-d6 b4-a5 g7-f6 g3-f4 d8-e7 d2-c3 c5-b4 a3xc5 d6xb4xd2 e1xc3 e7-d6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 e7-f6 b4xd6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xe5xc3 d2xb4 b6-a5 c1-b2 a5xc3 b2xd4 a7-b6 a1-b2 b6-a5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xe5xc3 d2xb4 b6-a5 c1-b2 a5xc3 b2xd4 g7-f6 a1-b2 f8-g7",
        "c3-d4 d6-c5 b2-c3 f6-g5 g3-f4 g5-h4 c1-b2 g7-f6 c3-b4 f6-g5 b4xd6 c7xe5xc3 d2xb4 b6-a5 h2-g3 a5xc3",
        "c3-d4 d6-c5 b2-c3 f6-g5 g3-f4 g5-h4 c3-b4 b6-a5 b4xd6 c7xe5xc3 d2xb4 a5xc3 c1-b2 g7-f6 b2xd4 d8-c7",
        "c3-d4 d6-c5 b2-c3 f6-g5 g3-f4 g5-h4 h2-g3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 g7-f6 d4-c5 f6-g5",
        "c3-d4 d6-c5 b2-c3 f6-g5 g3-f4 g7-f6 f4-e5 e7-d6 e5xg7 h8xf6 f2-g3 g5-h4 g1-f2 f8-g7 a1-b2 b6-a5",
        "c3-d4 d6-c5 b2-c3 f6-g5 g3-f4 g7-f6 f4-e5 h8-g7 c3-b4 e7-d6 f2-g3 d6xf4 g3xe5 g5-f4 e3xg5xe7 f8xd6xf4",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-h4 c7-d6 f2-g3 g7-h6 g3-f4 b6-a5 d4xb6 a5xc7 c3-b4 a7-b6 b4-a5 b6-c5",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b2-c3 f6-e5 c1-d2 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b2-c3 f6-g5 c3-d4 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 d8-c7",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 b2-a3",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 b2-a3 g7-f6 a1-b2 g5-h4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 e7-d6 c5xe7 f8xd6",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 e1-d2 g7-f6",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 h6-g5 g3-f4 g7-h6 b2-c3 g5-h4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 f6-g5 b4-a5 b8-c7 g3-f4 g5-h4 c1-d2 g7-f6 h2-g3 h8-g7 d4-e5 f6xd4",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-e5 d4xf6 g7xe5 b4-a5 f8-g7 e3-f4 d8-e7 b2-c3 e7-f6 c3-b4 f6-g5",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-e5 d4xf6 g7xe5 e3-f4 f8-g7 b4-a5 d8-e7",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 b4-a5 f8-g7 f2-g3 h4xf2 e1xg3 f6-e5",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-f4 g3xe5",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xf4xd2 c1xe3",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 g3-f4 g7-f6 b4-a5 g5-h4 b2-c3 f6-g5 c1-b2 d8-e7 c3-b4 e7-f6",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 b2-c3 f6-g5 g3-f4 d8-e7 f4xh6 c5-b4 a3xc5 d6xb4xd2xf4",
        "c3-d4 d6-c5 d2-c3 f6-e5 d4xf6 g7xe5 c3-b4 c7-d6 b4-a5 b8-c7 e3-f4 h8-g7 f4-g5 h6xf4 a3-b4 c5xa3",
        "c3-d4 d6-c5 d2-c3 f6-e5 d4xf6 g7xe5 c3-b4 e5-d4 b4xd6 e7xc5 c1-d2 h6-g5 g3-h4 f8-e7 h4xf6 e7xg5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xe5xc3 b2xd4 g5-h4 a1-b2 g7-f6 c1-d2 f6-g5 d4-c5 d8-c7",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 c5-b4 a3xc5 d6xb4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 f8-g7 f4-g5 h6xf4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xe5xc3 b2xd4 b6-a5 a1-b2 g7-f6 b2-c3 a7-b6 e3-f4 f6-g5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xe5xc3 b2xd4 b6-a5 a1-b2 g7-f6 b2-c3 e7-d6 e3-f4 d6-c5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xe5xc3 b2xd4 b6-a5 a1-b2 g7-f6 b2-c3 f6-g5 g3-f4 a7-b6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xe5xc3 b2xd4 b6-a5 g3-f4 g7-f6 a1-b2 f6-g5 b2-c3 a7-b6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xe5xc3 b2xd4 b6-a5 g3-f4 g7-f6 a1-b2 f6-g5 d4-c5 b8-c7",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 b8xd6 c3-b4 a5xc3",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 d8xb6 c3-d4 b8-c7 a3-b4",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b8-c7 a3-b4 c5xa3 e3-d4",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 b4xd6",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g5-h4 e1-d2 e7-d6 h2-g3 g7-f6 g1-h2 f6-g5 f4-e5 d6xf4 g3xe5 f8-g7",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g7-f6 c3-b4 g5-h4 b4xd6",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-h4 c7-d6 h4xf6 e7xg5 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 c7-b6 h2-g3 g5-h4",
        "c3-d4 d6-c5 d2-c3 h6-g5 c3-b4 e7-d6 g3-f4 g5-h4 f4-g5 f6-e5 d4xf6 g7xe5 g5-h6 e5-f4 e3xg5 h4xf6",
        "c3-d4 d6-c5 d2-c3 h6-g5 c3-b4 g5-h4 b4xd6 c7xe5xc3 b2xd4 b6-a5 g3-f4 g7-h6 a1-b2 f6-g5 b2-c3 a7-b6",
        "c3-d4 d6-c5 d4-e5 f6xd4",
        "c3-d4 d6-c5 g3-f4 c7-d6 f2-g3 b6-a5 d4xb6 a5xc7 b2-c3 f6-e5 a1-b2 g7-f6 a3-b4 f6-g5 g3-h4 e5xg3",
        "c3-d4 d6-c5 g3-f4 c7-d6 f2-g3 b6-a5 d4xb6 a5xc7 b2-c3 f6-e5 a1-b2 g7-f6 c3-b4 a7-b6 d2-c3 b6-a5",
        "c3-d4 d6-c5 g3-f4 f6-g5",
        "c3-d4 d6-c5 g3-f4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 b4xd6 c7xe5xc3 d2xb4 f6-g5 b4-a5 d8-c7 a1-b2 e7-d6",
        "c3-d4 d6-c5 g3-f4 f6-g5 b2-c3 g7-f6 h2-g3 g5-h4 f4-e5 h8-g7 g3-f4 f6-g5 c3-b4 b6-a5 b4xd6 e7xc5",
        "c3-d4 d6-c5 g3-h4 c7-d6 d2-c3 b6-a5 d4xb6 a5xc7 a3-b4 f6-e5 e3-d4 e5-f4 f2-g3 d6-c5 b4xd6 e7xc5xe3",
        "c3-d4 d6-c5 g3-h4 c7-d6 f2-g3",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-g5 h4xf6 e7xg5 g3-f4 g7-f6 b2-c3 d8-e7",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-g5 h4xf6 g7xe5 e3-f4 a7-b6 b2-a3 e7-f6",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-g5 h4xf6 g7xe5 e3-f4 h8-g7 b2-a3 g7-f6",
        "c3-d4 d6-e5 b2-c3 b6-a5 a1-b2 c7-d6 a3-b4 a7-b6 b2-a3 b6-c5 d4xb6 a5xc7 e3-f4 f6-g5 f2-e3 g5-h4",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 a1-b2 b8-c7 e3-f4",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 a1-b2 d8-c7 b2-a3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 f2-e3 b8-a7",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5 b8-c7 a1-b2 c7-d6 b2-a3 d6xb4 a3xc5 d8-c7 c1-b2 c7-d6",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5 d8-c7 a1-b2 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 c1-b2 c7-d6",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5 h6-g5 g3-f4 e5xg3",
        "c3-d4 d6-e5 b2-c3 b6-a5 e3-f4 a7-b6 f4xd6",
        "c3-d4 d6-e5 b2-c3 b6-a5 g3-h4 c7-b6 f2-g3 e7-d6 g3-f4 e5xg3 h4xf2 d6-c5 h2-g3 f6-g5 g3-f4 g5-h4",
        "c3-d4 d6-e5 b2-c3 b6-c5 d4xb6 a7xc5 e3-f4 c5-d4 f4xd6 e7xc5 c3xe5 f6xd4 c1-b2 h6-g5 b2-c3 d4xb2",
        "c3-d4 d6-e5 b2-c3 b6-c5 d4xb6 c7xa5 e3-d4 h6-g5 g3-h4 g5-f4 d4-c5 d8-c7 c1-b2 c7-b6 c3-d4 e5xc3",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-c5 d4xb6",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 a1-b2 b8-c7 c3-b4 c7-b6 b4-a5 c5-d4 a5xc7 d6xb8",
        "c3-d4 d6-e5 b2-c3 e5-f4 g3xe5 b6-c5 d4xb6 f6xd4xb2 a1xc3 a7xc5 h2-g3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 d2-e3 c7-b6 c3-b4 a5xc3 d4xb2 f6-g5 g3-h4 e5xg3 h4xf6 g7xe5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 a3-b4 f6-g5 b4-a5 a7-b6",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 d2-e3 b6-a5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 g3-h4 e5xg3 h4xf2 a7-b6",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 e1-f2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 a3-b4 d6-c5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 c3-b4 f6-g5 g3-h4 e5xg3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 c3-d4 e5xc3 d2xb4 f6-g5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 d2-e3 b6-c5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a7xc5 c1-b2 b8-a7 c3-b4 a5xc3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g3-h4 e5xg3 h4xf2 d6-c5 h2-g3 f6-g5 g3-f4 g7-f6",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 b4-a5 b8-a7 a5xc7 d8xb6 a1-b2 c5-d4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 b4-a5 f6-g5 a5xc7 d8xb6 f2-e3 e5-d4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f6-g5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 c3-b4 f6-g5 b4-a5 g5-h4 e1-d2 b8-a7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 f2-e3 b6-c5 d4xb6 a7xc5 g3-h4 e5xg3 h4xf2 f6-e5 a1-b2 e5-f4",
        "c3-d4 d6-e5 b2-c3 e7-d6 g3-f4 e5xg3 h2xf4 f6-e5 d4xf6 g7xe5xg3 f2xh4",
        "c3-d4 d6-e5 b2-c3 e7-d6 g3-f4 e5xg3 h2xf4 f6-g5 d4-e5",
        "c3-d4 d6-e5 b2-c3 e7-d6 g3-h4 d6-c5 f2-g3 c7-d6 g3-f4 e5xg3 h4xf2 b6-a5 d4xb6 a5xc7 a3-b4 a7-b6",
        "c3-d4 d6-e5 b2-c3 e7-d6 g3-h4 d6-c5 f2-g3 c7-d6 g3-f4 e5xg3 h4xf2 d6-e5",
        "c3-d4 d6-e5 d2-c3 c7-d6 g3-h4 b6-c5 d4xb6",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-d2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 e1-f2 d8-c7",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 e1-f2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 a3-b4",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 f2-e3 b8-c7",
        "c3-d4 d6-e5 d4-c5 b6xd4 e3xc5 e5-f4 g3xe5",
        "c3-d4 d6-e5 g3-f4 e5xc3 b2xd4 b6-a5 h2-g3 f6-g5 d2-c3 g5-h4 g1-h2 c7-b6 c1-d2 b6-c5 d4xb6 a5xc7",
        "c3-d4 d6-e5 g3-f4 e5xc3 b2xd4 f6-e5 f4xd6 c7xe5xc3 d2xb4 g7-f6 b4-a5",
        "c3-d4 d6-e5 g3-f4 e5xc3 d2xb4 f6-g5 b4-a5 g7-f6 b2-c3 g5-h4 c3-b4 f6-g5 a1-b2 h8-g7 h2-g3 g7-f6",
        "c3-d4 f6-e5 d4xf6 e7xg5 a3-b4 b6-c5 b2-a3 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4",
        "c3-d4 f6-e5 d4xf6 e7xg5 a3-b4 b6-c5 b4-a5 g5-h4 g3-f4 d8-e7 b2-a3 g7-f6 a1-b2 h8-g7 h2-g3 f6-g5",
        "c3-d4 f6-e5 d4xf6 e7xg5 a3-b4 f8-e7 b4-a5 b6-c5 g3-f4 g7-f6 b2-c3 f6-e5 h2-g3 g5-h4 a1-b2 c7-b6",
        "c3-d4 f6-e5 d4xf6 e7xg5 a3-b4 g5-h4 b2-a3 b6-c5 g3-f4 g7-f6 b4-a5 f6-g5 a1-b2 h8-g7 b2-c3 d8-e7",
        "c3-d4 f6-e5 d4xf6 e7xg5 a3-b4 g5-h4 b4-a5 b6-c5 b2-c3 c5-b4 c3-d4 b4-a3 d4-c5 d6xb4 a5xc3 g7-f6",
        "c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 b6-c5 g3-h4 f8-e7 h4xf6 e7xg5 c3-b4 g5-h4 b4-a5 g7-f6 e3-f4 f6-g5",
        "c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 d8-e7 c3-d4 g7-f6 a3-b4 d6-e5 d2-c3 b6-a5 g3-f4 e5xg3 h2xf4 e7-d6",
        "c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 f8-e7 c3-d4 b6-a5 a1-b2 a5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4",
        "c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 f8-e7 c3-d4 b6-a5 a1-b2 a7-b6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4",
        "c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 f8-e7 c3-d4 b6-a5 a1-b2 g5-h4 g3-f4 a5-b4 a3xc5 d6xb4 b2-c3 b4-a3",
        "c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 g5-h4 c3-b4 g7-f6 g3-f4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3",
        "c3-d4 f6-e5 d4xf6 e7xg5 g3-f4 d8-e7 b2-c3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 e7-d6 c5xe7 f6xd8",
        "c3-d4 f6-e5 d4xf6 e7xg5 g3-f4 f8-e7 b2-c3 b6-a5 c3-d4 a5-b4 a3xc5 d6xb4 d2-c3 b4xd2 e1xc3 e7-d6",
        "c3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g7-f6 f2-g3 f6-e5 g3-h4 e5xg3 h4xf2 h8-g7 e3-d4 g7-f6 h2-g3 g5-h4",
        "c3-d4 f6-e5 d4xf6 e7xg5 g3-h4 g5-f4 e3xg5 h6xf4 f2-e3 g7-h6 e3xg5 h6xf4 b2-c3 h8-g7 c3-d4 g7-f6",
        "c3-d4 f6-e5 d4xf6 g7xe5",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 b6-a5 g3-h4 a5xc3",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 e5-f4 e3xg5",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 f8-g7 e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 b6-c5 b2-a3 g7-f6",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 h8-g7 b4-a5 g7-f6 e3-f4 b6-c5 b2-a3 a7-b6 f2-e3 f6-g5 g3-h4 e5xg3",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 h8-g7 b4-a5 g7-f6 e3-f4 b6-c5 b2-a3 c5-d4 d2-e3 c7-b6 a5xc7 d8xb6",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 h8-g7 e3-f4 g7-f6 b4-a5 b6-c5 d2-e3 c7-b6 a5xc7 d8xb6 b2-a3 c5-d4",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 h8-g7 e3-f4 g7-f6 b4-a5 b6-c5 f2-e3 c7-b6 a5xc7 d8xb6 b2-c3 b6-a5",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 h8-g7 e3-f4 g7-f6 f2-e3 b6-a5 b2-c3 c7-b6 c1-b2 b6-c5 b2-a3 a7-b6",
        "c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 e5-f4 e3xg5",
        "c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 e7-f6 e3-f4 b6-a5 a1-b2 c7-b6 f2-e3 b6-c5 g3-h4 e5xg3 h2xf4 f8-g7",
        "c3-d4 f6-e5 d4xf6 g7xe5 e3-f4 h8-g7 f2-e3 g7-f6 b2-c3 f6-g5 g3-h4 e5xg3 h4xf2 g5-h4 c3-d4 d6-c5",
        "c3-d4 f6-e5 d4xf6 g7xe5 g3-h4 h8-g7 b2-c3 b6-a5",
        "c3-d4 f6-e5 d4xf6 g7xe5 g3-h4 h8-g7 d2-c3 g7-f6",
        "c3-d4 f6-g5 b2-c3 b6-a5 a1-b2 g5-h4 g3-f4 g7-f6 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 h8-g7 c3-d4 g7-f6",
        "c3-d4 f6-g5 b2-c3 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 c3-b4 a5xc3",
        "c3-d4 f6-g5 b2-c3 b6-a5 d4-c5 d6xb4 a3xc5 g7-f6 a1-b2 g5-h4 c3-d4 h8-g7 b2-a3 c7-b6 e3-f4 d8-c7",
        "c3-d4 f6-g5 b2-c3 d6-c5",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 b4xd6",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xa5xc3 c1-b2",
        "c3-d4 f6-g5 b2-c3 d6-c5 g3-f4 g5-h4 f2-g3 h4xf2 e1xg3 b6-a5 d4xb6 a7xc5 c3-d4 c7-d6 d4xb6 a5xc7",
        "c3-d4 f6-g5 b2-c3 e7-f6",
        "c3-d4 f6-g5 b2-c3 e7-f6 c1-b2 g5-h4 d4-c5 d6xb4 c3xa5 b6-c5 b2-c3 h6-g5 g3-f4 g7-h6 c3-d4 c7-b6",
        "c3-d4 f6-g5 b2-c3 e7-f6 g3-f4 d6-c5 a1-b2 f8-e7 f4-e5 e7-d6 f2-g3 d6xf4 g3xe5 d8-e7 g1-f2 e7-d6",
        "c3-d4 f6-g5 b2-c3 e7-f6 g3-h4 f8-e7 a1-b2 d6-c5 c3-b4 c7-d6 b2-c3 b6-a5 d4xb6 a5xc7 c3-d4 g5-f4",
        "c3-d4 f6-g5 b2-c3 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 a1-b2 b6-c5 d4xb6 a7xc5 c3-d4 c5xe3 f2xd4 g7-f6",
        "c3-d4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 a1-b2 b6-a5 a3-b4 e7-f6 f2-g3 a7-b6 g3xe5 b6-c5",
        "c3-d4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 a1-b2 b6-a5 a3-b4 g7-f6 f2-g3 h8-g7 g3xe5 e7-d6",
        "c3-d4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 a1-b2 b6-c5 d4xb6 a7xc5 c3-d4 c5xe3 f2xd4 g7-f6",
        "c3-d4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 a1-b2 b6-c5 d4xb6 a7xc5 f2-g3 e7-d6 g3xe5 d6xf4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c1-b2 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 f6-g5 e3-d4 g5-f4 g3xe5 d6xf4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 g7-f6 g3-f4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 a1-b2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 a1-b2 f6-g5 b4-a5 d6xb4 a5xc3 a7-b6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 a1-b2 h8-g7 b4-a5 d6xb4 a5xc3 a7-b6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 b4-a5 d6xb4 a5xc3 a7-b6 a3-b4 b6-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 c1-d2 f6-g5 b4-a5 d6xb4 a5xc3 a7-b6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 g3-f4 f6-g5 a1-b2 h8-g7 h2-g3 e7-f6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h6-g5 b4-a5 d6xb4 a5xc3 g7-h6 c3-b4 e7-d6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 b4-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 b4-a5 b6-c5 a1-b2 h8-g7 g3-f4 e5xg3 h2xf4 g7-f6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 b4-a5 e7-d6 a1-b2 e5-f4 e3xg5 h4xf6 b2-c3 f6-g5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 b4-a5 h8-g7 d2-c3 g7-f6 a3-b4 f6-g5 c3-d4 e5xc3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 b4-c5 b6xd4 e3xc5 h6-g5 a1-b2 g5-f4 b2-c3 h8-g7",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 e3-f4 f6-e5 d2-c3 c5-b4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 g3-f4 b8-a7 f4-g5 h6xf4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 g3-f4 f6-g5 b2-c3 e7-f6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 g3-f4 f6-g5 d2-c3 c5-b4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 g3-f4 h8-g7 f4-g5 h6xf4 e3xg5 g7-h6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 b6-a5 g3-f4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 f6-g5 c1-b2 h8-g7 b2-a3 b6-a5 c5-b6 a7xc5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 c1-b2 b6-a5 d4-c5 a5xc3 d2xb4 f6-g5 b4-a5 d6xb4 a5xc3 e7-d6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 d8-c7 c1-d2 f6-g5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 f6-e5 a1-b2 h8-g7 b4-a5 d6xb4 a5xc3 e7-d6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 h8-g7 a1-b2 f6-g5 b2-c3 g7-f6 d2-e3 f6-e5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-a5 g5-f4 e3xg5 h4xf6 f2-e3 g7-h6 a1-b2 h6-g5 b2-c3 g5-h4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-a5 g5-f4 g3xe5 d6xf4 e3xg5 h4xf6 a1-b2 e7-d6 d2-e3 b6-c5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 c7-d6 a1-b2 d6xb4 b2-a3 e7-f6 a3xc5 f6-e5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 c7-d6 g3-f4 d6xb4 f4xh6 b6-a5 h2-g3 b8-c7",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 e7-f6 g3-f4 g7-h6 c1-b2 b6-a5 h2-g3 c7-b6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 g7-h6 c1-b2 h8-g7 b2-a3 b6-a5 c5-b6 a7xc5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 g7-f6 b4-a5 d6xb4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 g5-f4 g3xe5 d6xf4 a1-b2 g7-h6 b2-c3 h6-g5",
        "c3-d4 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 h8-g7 g5-h6 d6-c5 d2-e3 c7-d6 c3-b4 b6-a5",
        "c3-d4 f6-g5 b2-c3 g7-f6 a1-b2 b6-a5 d4-e5 d6xf4",
        "c3-d4 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 g3-f4 d6-e5 f4xd6 e7xc5 h2-g3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 b2-a3 c7-b6 d2-c3 d8-c7",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 f6-e5 d4xf6 e7xg5 a1-b2 f8-e7",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 f6-g5 a1-b2 e7-d6 c5xe7 f8xd6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g5-h4 b4-a5 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g5-h4 c1-b2 h8-g7 e3-d4 d6-e5 b4-a5 e5xc3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 b4-a5 d6xb4 a5xc3 c7-d6 a3-b4 d8-c7",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 b4-a5 d6xb4 a5xc3 g5-f4 g3xe5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 g3-f4 c7-b6 b4-a5 b6xd4 e3xc5 g5xe3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xa5xc3 d2xb4 d6-e5 g3-f4 e5xg3 h2xf4 h8-g7 a1-b2 d8-c7",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xa5xc3 d2xb4 h8-g7 b4-a5 d8-c7 e3-d4 g5-h4 d4-c5 d6xb4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xa5xc3 d2xb4 h8-g7 g3-f4 d8-c7 a1-b2 g5-h4 b4-a5 f6-g5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 d6-e5 b4-a5 e5xc3 d2xb4 g5-h4 e3-d4 f6-g5 c1-d2 e7-f6 d2-e3 f6-e5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 f8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 b2-c3 f6-e5 d4xf6 e7xg5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 b4-a5 d6xb4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 c1-d2 f6-e5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 f6-e5 b4-a5 d6xb4 a5xc3 h8-g7 g3-f4 e5xg3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 f6-g5 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 b6-a5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 h8-g7 b4-a5 d6xb4 a5xc3 e7-d6 a3-b4 f6-e5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 h8-g7 b4-a5 d6xb4 a5xc3 f6-e5 a3-b4 a7-b6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 h8-g7 b4-a5 d6xb4 a5xc3 f6-g5 c3-d4 a7-b6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 h8-g7 d2-e3 f6-g5 a1-b2 g5-f4 g3xe5 d6xf4xd2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-a5 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 f2-g3 e7-d6 g3xe5 d6xf4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 b2-a3 c7-b6 d2-c3 f6-g5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 b2-a3 c7-b6 e3-f4 d8-c7",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 e3-f4 f6-g5 f2-e3 h4xf2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 g3-f4 f6-g5 b2-a3 c7-b6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 g3-f4 f6-g5 c5-b6 a7xc5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 g3-f4 f6-g5 f4-e5 g7-f6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 b2-a3 c7-d6 a3-b4 b6-a5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 b2-a3 e7-f6 d4-e5 f6xd4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 g3-f4 e7-d6 c5xe7 f8xd6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 c1-b2 f6-g5 b2-a3 g7-f6 a1-b2 b6-a5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 f6-g5 a1-b2 c7-d6 b2-a3 d6xb4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 d2-c3 b6-a5 d4-c5 g5-h4 c1-b2 f6-e5",
        "c3-d4 f6-g5 d2-c3 b6-c5 d4xb6 a7xc5 c3-b4 g5-h4 b2-c3 g7-f6 g3-f4 f6-g5 c1-b2 h8-g7 h2-g3 g7-f6",
        "c3-d4 f6-g5 d2-c3 d6-c5 c3-b4 b6-a5 b4xd6 c7xe5xc3 b2xd4 g5-h4 g3-f4 g7-f6 a1-b2 f6-g5 d4-e5 a7-b6",
        "c3-d4 f6-g5 d2-c3 d6-c5 c3-b4 g5-h4 b4xd6 c7xe5xc3 b2xd4 b6-a5 a1-b2 a7-b6 c1-d2 b6-c5 d4xb6 a5xc7",
        "c3-d4 f6-g5 d2-c3 g5-h4 c3-b4 h6-g5 c1-d2 g5-f4 g3xe5 d6xf4 e3xg5 h4xf6 h2-g3 f6-g5 f2-e3 g5-h4",
        "c3-d4 f6-g5 d2-c3 g7-f6 c3-b4 g5-h4 b4-a5 h8-g7 d4-c5 b6xd4 e3xc5 d6xb4 a5xc3 f6-g5 a3-b4 e7-d6",
        "c3-d4 f6-g5 d2-c3 g7-f6 c3-b4 g5-h4 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 e7-f6 a1-b2 d8-e7 c3-b4 b6-a5",
        "c3-d4 f6-g5 d2-c3 g7-f6 g3-f4 d6-e5 f4xd6 e7xc5 h2-g3 c7-d6 c3-b4 g5-h4 b4-a5 d6-e5 a5xc7 b8xd6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 d8-c7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 e3-d4 b4-a3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-a3 h6-g5 a1-b2 e7-f6 d2-e3 g7-h6 a3-b4 h8-g7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 c7-b6 c3-d4 d8-c7 a1-b2 h6-g5 b2-a3 g7-h6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 c7-b6 c3-d4 d8-c7 a1-b2 h6-g5 b2-c3 g7-h6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 c7-b6 c3-d4 d8-c7 a1-b2 h6-g5 d2-e3 g7-f6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 c3-b4 h8-g7 b2-c3 e7-f6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 g7-f6 a1-b2 h8-g7 c3-b4 f6-g5 b2-c3 c7-b6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 h6-g5 a1-b2 g7-h6 c3-b4 e7-f6 d2-e3 d8-e7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 d2-e3 g7-f6 e3-d4 f6-g5 c1-d2 e7-f6 b2-c3 c7-b6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 b2-a3 f6-g5 d2-e3 c7-d6 c1-b2 d6xb4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 b2-c3 h8-g7 h2-g3 f6-g5 a1-b2 g5xe3",
        "c3-d4 f6-g5 d4-c5 d6xb4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 d2-e3 d8-e7 g3-f4 e7-d6 c5xe7 f6xd8 b2-c3 a7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 f2-e3 d8-e7 e3-d4 e7-d6 c5xe7 f6xd8 b2-c3 g5-h4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 f2-e3 g5-h4 g3-f4 h4-g3 f4-g5 h6xf4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 b2-a3 a7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 h2-g3 a7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 h2-g3 d8-e7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 b6-a5",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 f8-e7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 b2-c3 e7-d6 c5xe7 d8xf6 a1-b2 c7-b6 c3-b4 b6-a5",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 c3-b4 e7-f6 b2-c3 f6-e5",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 c3-b4 h8-g7 b2-c3 c7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 d2-e3 g7-f6 b2-a3 f6-e5 g3-f4 e5xg3 h2xf4 h8-g7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 d2-e3 g7-f6 g3-f4 f6-g5 h2-g3 f8-g7 e1-d2 c7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 c3-b4 e7-f6 b2-c3 d8-e7",
        "c3-d4 f6-g5 d4-e5 d6xf4 g3xe5 e7-f6 d2-c3 f6xd4 c3xe5 d8-e7",
        "c3-d4 f6-g5 d4-e5 d6xf4 g3xe5 g5-h4 a3-b4 h6-g5 e3-d4 g7-h6 b4-a5 b6-c5 d4xb6 a7xc5 e5-f6 e7-d6",
        "c3-d4 f6-g5 g3-f4 b6-a5 d4-c5 d6xb4 a3xc5 g5-h4 b2-c3 c7-d6 c3-b4 a5xc3 d2xb4 d6-e5 f4xd6 a7-b6",
        "c3-d4 f6-g5 g3-f4 d6-c5 b2-c3 c7-d6 a1-b2 b6-a5 d4xb6 a7xc5 f2-g3 g7-f6 g3-h4 b8-a7 h2-g3 f8-g7",
        "c3-d4 f6-g5 g3-f4 d6-c5 d2-c3 g7-f6 c3-b4 g5-h4 b4xd6 c7xe5xc3 b2xd4 b6-a5 a1-b2 f6-g5",
        "c3-d4 f6-g5 g3-f4 d6-c5 d2-c3 g7-f6 c3-b4 h8-g7 b4xd6 c7xe5xc3 b2xd4",
        "c3-d4 f6-g5 g3-f4 d6-c5 d2-c3 g7-f6 c3-b4 h8-g7 b4xd6 c7xe5xg3 h2xf4 g5-h4 a3-b4 f6-g5",
        "c3-d4 f6-g5 g3-f4 e7-f6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 d2xf4 f6-g5 h2-g3 g5xe3 f2xd4 h6-g5",
        "c3-d4 f6-g5 g3-f4 e7-f6 f2-g3 g5-h4 f4-g5 h4xf2 g5xe7xc5 g7-f6 e1xg3 f6-e5 d4xf6 b6xd4xf2xh4 b2-c3 h6-g5",
        "c3-d4 f6-g5 g3-f4 g7-f6 b2-c3 h8-g7 f2-g3 g5-h4 a1-b2 h4xf2 e1xg3 d6-c5 g1-f2 b6-a5 d4xb6 a7xc5",
        "c3-d4 f6-g5 g3-f4 g7-f6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 f6-g5 h2-g3 h8-g7 b2-c3 g5-f4",
        "c3-d4 f6-g5 g3-f4 g7-f6 f2-g3 g5-h4 b2-c3 h4xf2 e1xg3 f6-g5 g3-h4 d6-c5 h4xf6 e7xg5 f4-e5 g5-h4",
        "c3-d4 f6-g5 g3-f4 g7-f6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 h8-g7 b2-c3 c7-d6 c3-b4 d8-c7",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xe5xc3 b2xd4 h6-g5 h2-g3 g5-h4",
        "c3-d4 f6-g5 g3-h4 b6-c5 d4xb6 a7xc5 h4xf6 g7xe5 b2-c3 e7-f6 h2-g3 f8-e7 e3-f4 c7-b6 c3-b4 h8-g7",
        "c3-d4 f6-g5 g3-h4 d6-c5 h4xf6",
        "c3-d4 h6-g5 b2-c3 g5-h4 c3-b4 d6-e5 b4-a5 e5xc3 d2xb4 f6-g5 a1-b2 g7-h6 e3-d4 e7-f6 d4-e5 f6xd4",
        "c3-d4 h6-g5 b2-c3 g5-h4 c3-b4 f6-e5 d4xf6 g7xe5 b4-a5 e5-f4 e3xg5 h4xf6 g3-h4 h8-g7 f2-e3 b6-c5",
        "c3-d4 h6-g5 b2-c3 g5-h4 c3-b4 f6-e5 d4xf6 g7xe5 b4-a5 h8-g7 a1-b2 e7-f6 a3-b4 b6-c5 b2-a3 d8-e7",
        "c3-d4 h6-g5 b2-c3 g7-h6 c3-b4 d6-e5 b4-a5 e5xc3 d2xb4 g5-h4 a1-b2 h8-g7 g3-f4 f6-g5 b2-c3 g7-f6",
        "c3-d4 h6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-b6 g3-f4 g5xe3 f2xd4 e7-d6",
        "c3-d4 h6-g5 g3-f4 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-e5 f4xd6 c7xe5 b2-c3 g7-f6 f2-e3 h8-g7",
        "c3-d4 h6-g5 g3-f4 g5-h4 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 f6-e5 f4xd6 c7xe5 b2-c3 g7-f6 a1-b2 h8-g7",
        "c3-d4 h6-g5 g3-f4 g7-h6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 h8-g7 g5-h6 d6-c5 d2-e3 c7-d6 h2-g3 d6-e5",
        "c3-d4 h6-g5 g3-f4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h6-g5 h2-g3 h8-g7 d2-e3 g7-h6",
        "c3-d4 h6-g5 g3-f4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 d2xf4 f6-e5 f4xd6 c7xe5 b2-c3 h8-g7",
        "c3-d4 h6-g5 g3-f4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 h6-g5 d2-e3 g5-f4 e3xg5 f6xh4",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-e5 f6xd4 e3xc5 g5xe3 f2xd4 d6xb4 a3xc5 h8-g7 d2-e3 g7-f6",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 c7-b6 f2-g3 g7-h6 g3-f4 b6-c5 d4xb6 a5xc7 a1-b2 a7-b6 h2-g3 d6-c5",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 c7-b6 f2-g3 g7-h6 g3-f4 b6-c5 d4xb6 a5xc7 c3-b4 d6-e5 f4xd6 c7xe5",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 c7-b6 h2-g3 d6-e5 c1-b2 e7-d6 g1-h2 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 d6-e5 a1-b2 g7-h6 a3-b4 c7-b6 b2-a3 e7-d6 f2-g3 f8-g7 b4-c5 d6xb4",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 d6-e5 f2-g3 g7-h6 g3-f4 e5xg3 h4xf2 h8-g7 h2-g3 g5-h4 a1-b2 f6-g5",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xf4xh6 b6-c5 b2-c3 c5-d4",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 f2-g3 f6-e5 d4xf6 g7xe5 e1-f2 b6xd4",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 a7-b6 g3-f4 g7-h6 h2-g3 d6-e5 f4xd6",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 b2-c3 g7-h6 g3-f4 b6-c5 d4xb6 a5xc7 c3-b4 d6-e5 f4xd6 c7xe5",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 g7-h6 h2-g3 b6-c5 d4xb6 a5xc7 b2-c3 a7-b6 c3-b4 b6-a5",
        "c3-d4 h6-g5 g3-h4 b6-a5 h2-g3 c7-b6 g3-f4 g7-h6 b2-c3 b6-c5 d4xb6 a5xc7 a1-b2 a7-b6 f2-g3 d6-c5",
        "c3-d4 h6-g5 g3-h4 b6-a5 h2-g3 d6-e5 g1-h2 e5xc3 d2xb4 a5xc3 b2xd4 c7-b6 a3-b4 b6-c5 b4xd6 e7xc5",
        "c3-d4 h6-g5 g3-h4 b6-a5 h2-g3 d6-e5 g1-h2 e5xc3 d2xb4 a5xc3 b2xd4 c7-b6 a3-b4 g7-h6 b4-a5 b6-c5",
        "c3-d4 h6-g5 g3-h4 b6-c5 d4xb6 a7xc5",
        "c3-d4 h6-g5 g3-h4 d6-c5",
        "c3-d4 h6-g5 g3-h4 d6-c5 b2-c3 g7-h6 h2-g3 e7-d6 g3-f4 f6-e5 d4xf6 g5xe7 c3-b4 b6-a5 d2-c3 e7-f6",
        "c3-d4 h6-g5 g3-h4 d6-e5 f2-g3 e5xc3 d2xb4 g7-h6 g3-f4 b6-a5 c1-d2 a5xc3 d2xb4 e7-d6 b4-c5 d6xb4",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 d2xb4 g7-h6 b4-a5 e7-d6 g3-f4 d6-e5 f4xd6 c7xe5 a5xc7 b8xd6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-c3 d6xb4 c3xa5 g5-f4 a1-b2 h8-g7",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 b2-c3 c7-b6 c3-d4 b8-c7 d4-e5 b6xd4",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 b2-c3 g5-f4 a1-b2 c7-d6 c3-b4 b8-c7",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f8-g7 a1-b2 d8-c7",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 c7-d6 b2-c3 d6xb4 c3xa5 g5-f4 a1-b2 b8-c7",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 f8-g7 b2-c3 c7-b6 c3-d4 b8-c7 h2-g3",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g1-f2 e5xc3 b2xd4 f8-g7 a1-b2 e7-d6 d4-c5 d6xb4",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g1-f2 e5xc3 d2xb4 b6-a5 c1-d2 a5xc3 b2xd4 a7-b6 d4-e5",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g3-f4 e5xc3 b2xd4 e7-d6 h2-g3 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g3-f4 e5xg3 h4xf2 b6-a5 h2-g3 g5-h4 b2-c3 f6-g5 d4-c5 h8-g7",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 f8-g7 g3-f4 f6-e5 d4xf6 g7xe5xg3 h4xf2",
        "e3-d4 b6-c5 d4xb6 a7xc5 c3-b4",
        "e3-d4 d6-c5 d2-e3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 c3-d4 f6-g5 b2-c3 g5-h4 a3-b4 d6-c5 b4xd6 c7xe5xg3",
        "e3-d4 d6-c5 d2-e3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 b2xd4 a7xc5 d4xb6 c7xa5 a1-b2 f6-g5 g3-f4 g5-h4",
        "e3-d4 d6-c5 d2-e3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 b2-c3 g7-h6 g3-f4 d8-e7 c3-b4 f6-g5 c1-b2 e7-f6",
        "e3-d4 d6-c5 d2-e3 e7-d6 g3-h4 d6-e5 f2-g3 b6-a5 d4xb6 a7xc5 c3-d4 e5xc3 b2xd4xb6 b8-a7 c1-b2 a7xc5",
        "e3-d4 d6-c5 d2-e3 f6-g5 c3-b4 e7-f6 b4xd6",
        "e3-d4 d6-c5 f2-e3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g1-f2 h6-g5",
        "e3-d4 d6-c5 f2-e3 c7-d6 g3-h4 b6-a5 d4xb6 a5xc7 a3-b4 a7-b6 b4-a5 f6-e5 e3-d4 g7-f6 d2-e3 h8-g7",
        "e3-d4 d6-c5 f2-e3 f6-g5 g3-h4 g7-f6 h2-g3 e7-d6 c3-b4 f6-e5 d4xf6 g5xe7 b4-a5 h8-g7 g3-f4 g7-f6",
        "e3-d4 d6-e5 a3-b4 b6-a5 b4-c5 h6-g5 c5-d6 e7xc5xe3 d2xf4xh6 c7-d6 g3-f4 e5xg3 h2xf4 f6-g5 f2-e3 g7-f6",
        "e3-d4 d6-e5 a3-b4 h6-g5 b4-a5 g5-f4 c3-b4 e5xc3 g3xe5 f6xd4 b4-c5 d4-e3 b2xd4 e7-f6 d2xf4 f6-e5",
        "e3-d4 d6-e5 a3-b4 h6-g5 b4-a5 g5-h4 d2-e3 e7-d6 c3-b4 e5xc3 b4xd2 b6-c5 b2-c3 c5-b4 c3-d4 b4-a3",
        "e3-d4 f6-e5 d4xf6 e7xg5 c3-b4 d6-e5 b4-a5 g5-h4 a3-b4 g7-f6 d2-c3 f8-e7 c3-d4 e5xc3 b2xd4 e7-d6",
        "e3-d4 f6-e5 d4xf6 g7xe5 c3-b4 h6-g5 b4-a5 g5-h4 b2-c3 h8-g7 c3-b4 b6-c5 d2-e3 e7-f6 a1-b2 e5-d4",
        "e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 h8-g7 c3-b4 b6-c5 b4-a5 a7-b6 b2-c3 c5-d4 c3-b4 b6-c5 d2-e3 g7-f6",
        "e3-d4 f6-g5 c3-b4 g5-h4 b4-c5 d6xb4 a3xc5 h6-g5 d2-e3 g7-h6 g3-f4 e7-f6 h2-g3 d8-e7 b2-c3 e7-d6",
        "e3-d4 f6-g5 d2-e3 b6-a5 c1-d2 g5-h4 g3-f4 g7-f6 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 h8-g7 f2-e3 g7-f6",
        "e3-d4 f6-g5 d2-e3 g5-h4 c1-d2 b6-a5 d4-c5 d6xb4 a3xc5 g7-f6 b2-a3 f6-g5 c3-b4 a5xc3 d2xb4 c7-b6",
        "e3-d4 f6-g5 d2-e3 g5-h4 c1-d2 g7-f6 c3-b4 h8-g7 d4-c5 b6xd4 e3xc5 f6-g5 b4-a5 d6xb4 a5xc3 e7-d6",
        "e3-d4 f6-g5 g3-h4 d6-c5 h4xf6 c5xe3 f2xd4 e7xg5 a3-b4 g7-f6 e1-f2 g5-h4 d2-e3 f8-e7 c1-d2",
        "e3-d4 f6-g5 g3-h4 d6-c5 h4xf6 c5xe3 f2xd4 g7xe5 d4xf6 e7xg5 h2-g3 g5-h4 g3-f4 b6-c5 d2-e3 a7-b6",
        "e3-d4 f6-g5 g3-h4 d6-c5 h4xf6 e7xg5 d2-e3 g7-f6 c3-b4 h8-g7 b4xd6 c7xe5xc3 b2xd4 b6-a5 h2-g3 g5-h4",
        "e3-d4 h6-g5 c3-b4 g5-f4 g3xe5 d6xf4 b4-a5 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5 a1-b2 g7-f6 f2-g3 h8-g7",
        "e3-d4 h6-g5 g3-h4 d6-e5 a3-b4 b6-a5 b4-c5 g5-f4 f2-e3 c7-d6 e3xg5 d6xb4 b2-a3 g7-h6 a3xc5 h6xf4",
        "e3-f4 b6-a5 f2-e3 c7-b6 g3-h4",
        "e3-f4 b6-c5 f2-e3 a7-b6 g1-f2 b6-a5 f4-g5 h6xf4 e3xg5",
        "e3-f4 f6-e5 f2-e3 e7-f6 a3-b4 b6-c5 g3-h4 c5xa3 f4-g5 h6xf4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 b6-c5 b4-a5 g7-f6 b2-c3 f6-e5 c3-b4 h8-g7 c1-d2 c7-b6 a5xc7 d8xb6",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 f4-e5 d6xf4 g3xe5 f6xd4 b4-c5 d4-e3 f2xd4 b6-a5 b2-c3 f8-e7",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 b4-c5 b6xd4 f4-e5 d6xf4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 b4-c5 b6xd4 f4-e5 d6xf4 g3xe5xc3 e7-d6 h2-g3 a7-b6 c1-d2 f6-g5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 c1-d2 f6-g5 f2-e3 g5-h4 g1-f2 d6-c5 b4xd6 e7xc5 b2-c3 h8-g7",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 f2-e3 f6-g5 c1-d2 g5-h4 g1-f2 b6-a5 b2-c3 a7-b6 a1-b2 b6-c5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 f2-e3 f6-g5 c1-d2 g5-h4 g1-f2 d6-c5 b4xd6 e7xc5 b2-c3 h8-g7",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 f4-e5 d6xf4 g3xe5xg7 h8xf6 h2-g3 h6-g5 b4-a5 f6-e5 g3-h4 g5-f4",
        "e3-f4 f6-g5 d2-e3 g5-h4 c1-d2 d6-c5 c3-d4 e7-f6 f4-e5 f6-g5 g3-f4 f8-e7",
        "e3-f4 f6-g5 f2-e3 g5-h4 e1-f2 b6-c5 c3-b4 g7-f6 b2-c3 f6-e5 b4-a5 h8-g7 c3-b4 g7-f6 d2-c3 f8-g7",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-a5 e5-f6 g7xe5 c3-b4 a5xc3",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-c5 c3-b4 a7-b6 b4xd6 e7xc5 d2-c3 d8-e7 e5-d6 c7xe5 a3-b4 c5xa3",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-c5 c3-b4 e7-d6 f2-g3 d6xf4 g3xe5 d8-e7 b4xd6 e7xc5 e1-f2 f8-e7",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 g5-h4 c3-d4 h6-g5 a3-b4 g7-h6 b2-c3 b6-a5 a1-b2 e7-d6 b2-a3 d6xf4",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 g5-h4 d2-e3 b6-a5 c1-d2 e7-d6 e3-f4 a7-b6 c3-b4 a5xc3 b2xd4 d6-c5",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 g5-h4 f2-e3 b6-c5 e1-f2 a7-b6 c3-b4 e7-d6 e3-f4 c5-d4 e5xc3 d6-c5",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 g5-h4 f2-e3 h6-g5 a3-b4 b6-a5 c3-d4 a5xc3 d2xb4 e7-d6 c1-d2 d6xf4",
        "e3-f4 f6-g5 g3-h4 g5xe3 d2xf4 g7-f6 f2-e3 b6-c5 c3-b4 f6-e5 b2-c3 e5xg3 h2xf4 e7-f6 g1-h2 f8-g7",
        "e3-f4 f6-g5 g3-h4 g5xe3 f2xd4 b6-c5 d4xb6 a7xc5 c3-b4 g7-f6 h2-g3 f6-e5 g3-f4 e5xg3 h4xf2 h8-g7",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 d6-e5 f4xd6 c7xe5 e3-f4 e5xg3 h2xf4 d8-c7 b2-c3 e7-d6 b4-a5 f6-e5",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 f6-e5 h2-g3 a7-b6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g7-f6 f4xd6 c7xe5",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 f6-g5 b2-c3 g7-f6 b4-a5 g5-h4 c3-b4 a7-b6 b4-c5 b6xd4 e3xc5 d6xb4",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 f6-g5 b4-a5 g7-f6 b2-c3 d6-c5 e3-d4 c5xe3 f4xd2 f6-e5 c1-b2 h8-g7",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 f6-g5 b4-c5 d6xb4 a3xc5 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 b2-a3 c7-b6",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xe5xg3 h2xf4 h8-g7 a3-b4 a5xc3 b2xd4 a7-b6 a1-b2 d6-c5 f2-g3 g7-f6",
        "g3-f4 b6-a5 c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 g7-f6 a1-b2 d8-c7 b2-c3 e7-d6",
        "g3-f4 b6-a5 f4-g5 h6xf4 e3xg5",
        "g3-f4 b6-a5 h2-g3 f6-g5 c3-d4 a5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 b8-c7",
        "g3-f4 b6-a5 h2-g3 f6-g5 c3-d4 a5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 g5-h4",
        "g3-f4 b6-c5 c3-d4 a7-b6 d4-e5 f6xd4 a3-b4 c5xa3 e3xc5xa7 g7-f6 b2-c3 f6-e5 h2-g3 h6-g5 f4xh6 e5-d4",
        "g3-f4 d6-c5 c3-b4 e7-d6 b4-a5 f8-e7 b2-c3 c5-b4 a3xc5 b6xd4xb2 a1xc3 f6-g5 c3-b4 a7-b6 h2-g3 g5-h4",
        "g3-f4 d6-c5 c3-d4 f6-g5 h2-g3 g5-h4 b2-c3 g7-f6 c3-b4 f6-e5 d4xf6 e7xg5 b4xd6 c7xe5 f4xd6 d8-e7",
        "g3-f4 d6-c5 h2-g3 c7-d6 c3-b4 f6-e5 b4-a5 d8-c7 b2-c3 e5-d4 c3xe5 h6-g5 f4xh6 d6xf4xh2 a1-b2 g7-f6",
        "g3-f4 d6-c5 h2-g3 c7-d6 c3-b4 f6-e5 b4-a5 d8-c7 b2-c3 e5-d4 c3xe5 h6-g5 f4xh6 d6xf4xh2 e3-f4 g7-f6",
        "g3-f4 d6-e5 f4xd6 c7xe5 c3-d4 e5xc3 b2xd4 b6-a5 h2-g3 f6-g5 c1-b2 g7-f6 d2-c3 e7-d6 g3-f4 d6-c5",
        "g3-f4 f6-e5 c3-d4 e5xc3 d2xb4 g7-f6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-e5 f4xd6 c7xe5 c1-d2 h6-g5",
        "g3-f4 f6-e5 f2-g3 b6-a5 g3-h4 e5xg3 h4xf2 c7-b6 c3-b4 a5xc3 d2xb4 h6-g5 h2-g3 g5-h4 b4-c5 d6xb4",
        "g3-f4 f6-e5 f2-g3 g7-f6",
        "g3-f4 f6-e5 f2-g3 g7-f6 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 f6-g5 b2-c3 g5xe3 d2xf4 h8-g7 g3-h4 e5xg3",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xf4xh2 a3-b4 c7-d6 b4-a5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xf4xh2 a3-b4 e7-d6 b4-a5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xf4xh2 a3-b4 g7-f6 b2-c3",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xf4xh2 a3-b4 g7-f6 b4-a5",
        "g3-f4 f6-e5 h2-g3 e5-d4 e3xc5 b6xd4 c3xe5 h6-g5 f4xh6 d6xf4xh2 b2-c3",
        "g3-f4 f6-e5 h2-g3 e5-d4 e3xc5 b6xd4 c3xe5 h6-g5 f4xh6 d6xf4xh2 d2-e3",
        "g3-f4 f6-e5 h2-g3 e7-f6 e3-d4 b6-a5 d2-e3 c7-b6 e1-d2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 a3-b4",
        "g3-f4 f6-e5 h2-g3 e7-f6 e3-d4 b6-a5 d4-c5 d6xb4 a3xc5 h6-g5 f4xd6 c7xe5 g3-h4 e5-f4 c3-d4 f4-g3",
        "g3-f4 f6-e5 h2-g3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 c5-b6 a7xc5 f4-e5 h6-g5 e5xc3 g5-h4",
        "g3-f4 f6-e5 h2-g3 g7-f6 c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 d2xf4xd6 c7xe5 b2-a3 h8-g7",
        "g3-f4 f6-e5 h2-g3 g7-f6 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 e5-d4 b4-a5 f6-g5 d2-e3 g5-h4 a3-b4 c5xa3",
        "g3-f4 f6-e5 h2-g3 h6-g5 f4xh6 e5-d4 c3xe5 d6xf4xh2 b2-c3 g7-f6 a1-b2",
        "g3-f4 f6-g5 c3-b4 b6-c5 b2-c3 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 f2-g3 b4-a3 g3-h4 e7-d6 h2-g3 f8-g7",
        "g3-f4 f6-g5 c3-b4 b6-c5 b2-c3 g7-f6 c3-d4 h8-g7 d4xb6 c7xa5xc3 d2xb4 g5-h4 b4-a5 f6-g5 a1-b2 d8-c7",
        "g3-f4 f6-g5 c3-b4 e7-f6 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 d2xf4 f6-e5 f4xd6 c7xe5 b2-a3 d8-c7",
        "g3-f4 f6-g5 c3-b4 g5-h4 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g7-f6 b2-c3 f6-g5 d2-e3 h8-g7 a1-b2 e7-f6",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 a1-b2 e5xg3 f2xh4xf6 e7xg5 e1-f2 g5-h4 b4-c5 d6xb4 a3xc5 b6xd4",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 b4-a5 e5xg3 f2xh4xf6 e7xg5 e1-f2 h8-g7 a1-b2 g5-f4 e3xg5 h6xf4",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 g5-h4 b4-a5 f6-g5 c3-d4 h8-g7 d4-e5 b6-c5 a1-b2 e7-f6 d2-c3 f6xd4",
        "g3-f4 f6-g5 c3-b4 g7-f6 b4-a5",
        "g3-f4 f6-g5 c3-b4 g7-f6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 f8-g7 h2-g3 f6-e5 d4xf6 g7xe5",
        "g3-f4 f6-g5 c3-b4 g7-f6 b4-c5 b6xd4 e3xc5 g5xe3 f2xd4 d6xb4 a3xc5 h8-g7 d2-e3 f6-g5 h2-g3 g7-f6",
        "g3-f4 f6-g5 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 h8-g7 d2-e3 h6-g5 h2-g3 g7-h6",
        "g3-f4 f6-g5 c3-d4 g5-h4",
        "g3-f4 f6-g5 c3-d4 g7-f6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 f8-g7 d2-e3 f6-e5 d4xf6 g7xe5",
        "g3-f4 f6-g5 c3-d4 g7-f6 h2-g3 g5-h4 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 h8-g7 b2-c3 c7-d6 c3-b4 d8-c7",
        "g3-f4 f6-g5 h2-g3 g5-h4",
        "g3-f4 f6-g5 h2-g3 g5-h4 c3-d4 d6-c5 d2-c3 e7-d6 g1-h2 f8-e7 c3-b4 b6-a5 d4xb6 a5xc3 b2xd4 a7xc5",
        "g3-h4 b6-a5 c3-d4 a5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 b8-c7 b2-c3",
        "g3-h4 b6-a5 c3-d4 c7-b6 b2-c3 b6-c5 d4xb6 a5xc7 f2-g3",
        "g3-h4 b6-a5 c3-d4 d6-e5 b2-c3 e5-f4 e3xg5 h6xf4 d4-c5 f6-e5 c5-d6 e7xc5 h4-g5 f4xh6 c3-b4 a5xc3",
        "g3-h4 b6-a5 e3-d4 d6-e5",
        "g3-h4 b6-a5 f2-g3 a7-b6 g1-f2 b6-c5 c3-b4 a5xc3",
        "g3-h4 b6-a5 f2-g3 c7-b6",
        "g3-h4 b6-a5 h2-g3 c7-b6 e3-d4 b6-c5 d4xb6 a5xc7 g3-f4",
        "g3-h4 b6-a5 h2-g3 h6-g5 g3-f4",
        "g3-h4 d6-c5 c3-b4 e7-d6 b4-a5 f6-e5 h2-g3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 d2-c3 f4-g3 c3-b4 g3-h2",
        "g3-h4 d6-c5 h2-g3 c7-d6 g3-f4 b8-c7 f2-g3 c5-b4",
        "g3-h4 d6-c5 h2-g3 f6-g5 h4xf6 e7xg5 c3-b4",
        "g3-h4 d6-e5 a3-b4 b6-a5 b2-a3",
        "g3-h4 f6-e5 a3-b4 e5-f4 e3xg5 h6xf4 b2-a3 g7-f6 b4-a5 h8-g7 c3-b4 b6-c5 a1-b2 d6-e5 b4xd6 e7xc5",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b2-c3 g7-f6 b4-a5 h8-g7 c3-b4 d6-c5 b4xd6 c7xe5 a5xc7 b8xd6",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 f2-g3 e7-d6 g3xe5 d6xf4",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 e7-f6 c3-b4 g7-h6 a1-b2",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-b4 b6-c5 d2-c3 a7-b6 e1-d2 g7-h6",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 d2-c3 b6-c5 c3-b4 h8-g7 b2-c3 g7-h6",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 d2-c3 f6-g5 h4xf6 e7xg5 c3-b4 h8-g7 b2-c3 g7-h6",
        "g3-h4 f6-e5 c3-b4 g7-f6 b4-a5 e5-f4 e3xg5 h6xf4 b2-c3 b6-c5 c3-b4 h8-g7 a1-b2 g7-h6 b2-c3 f6-g5",
        "g3-h4 f6-e5 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 g7-f6 b2-c3 h8-g7 a1-b2 h6-g5 d2-e3 g5-f4 e3xg5 g7-h6",
        "g3-h4 f6-e5 e3-d4 b6-c5 d4xb6 a7xc5 f2-g3 e5-f4 g3xe5 d6xf4 c3-b4 g7-f6 b4xd6 e7xc5 b2-c3 f8-e7",
        "g3-h4 f6-e5 e3-d4 g7-f6 f2-g3 f8-g7 d2-e3 d6-c5 g3-f4 e5xg3 h4xf2 c7-d6 f2-g3 f6-g5 g3-h4 g5-f4",
        "g3-h4 f6-e5 e3-f4 e5xg3",
        "g3-h4 f6-e5 e3-f4 e5xg3 h2xf4 b6-c5 c3-b4 g7-f6 d2-e3 f6-e5 f2-g3 e5-d4 e1-f2 h8-g7 c1-d2",
        "g3-h4 f6-e5 e3-f4 e5xg3 h2xf4 g7-f6 f2-g3 b6-c5 g1-h2 f6-e5 d2-e3 a7-b6 c3-d4 e5xc3 b2xd4 e7-f6",
        "g3-h4 f6-e5 f2-g3 b6-a5 g3-f4 e5xg3 h4xf2",
        "g3-h4 f6-e5 f2-g3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 a3-b4 e7-d6 b4-a5 g7-f6 b2-a3 f6-e5 c3-b4 h8-g7",
        "g3-h4 f6-e5 f2-g3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 c3-b4 e7-d6 b4-c5 b6xd4 d2-c3 d6-e5 c3-b4 c7-d6",
        "g3-h4 f6-e5 f2-g3 g7-f6 e3-f4 h8-g7",
        "g3-h4 f6-e5 f2-g3 g7-f6 e3-f4 h8-g7 c3-b4 b6-a5 g1-f2 a5xc3 b2xd4 e5xc3 d2xb4 f6-e5 f2-e3 g7-f6",
        "g3-h4 f6-e5 f2-g3 g7-f6 g3-f4 e5xg3 h4xf2 h6-g5 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4",
        "g3-h4 f6-g5 h4xf6 e7xg5",
        "g3-h4 f6-g5 h4xf6 e7xg5 c3-d4 g5-h4 b2-c3 b6-a5 f2-g3 h4xf2 e1xg3",
        "g3-h4 f6-g5 h4xf6 g7xe5",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 b6-c5 b2-a3 e5-f4 e3xg5 h6xf4 b4-a5 h8-g7 c3-b4 e7-f6 a1-b2 g7-h6",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 h8-g7 b4-a5 e5-f4 e3xg5 h6xf4 c3-b4 b6-c5 b2-a3 g7-f6 a1-b2 d6-e5",
        "g3-h4 f6-g5 h4xf6 g7xe5 c3-b4",
        "g3-h4 f6-g5 h4xf6 g7xe5 c3-b4 b6-c5 b4-a5 e7-f6 b2-c3 h8-g7 a1-b2 f8-e7 c3-b4 c7-b6 a5xc7 d8xb6",
        "g3-h4 f6-g5 h4xf6 g7xe5 c3-b4 h6-g5 b4-a5 g5-h4 a3-b4 e5-f4 e3xg5 h4xf6 d2-e3 b6-c5 b2-a3 f6-g5",
        "g3-h4 f6-g5 h4xf6 g7xe5 c3-b4 h8-g7 b4-a5 e5-f4 e3xg5 h6xf4 b2-c3 g7-h6 c3-b4 h6-g5 d2-c3 e7-f6",
        "g3-h4 f6-g5 h4xf6 g7xe5 e3-d4 e7-f6 f2-g3 h6-g5 d2-e3 g5-h4 e3-f4 h4xf2 e1xg3 b6-c5 d4xb6 a7xc5",
        "g3-h4 f6-g5 h4xf6 g7xe5 e3-f4 e5xg3 f2xh4 h6-g5 h4xf6 e7xg5 d2-e3 g5-h4 e1-f2 h8-g7 c1-d2 b6-c5",
        "g3-h4 h6-g5 e3-d4 b6-c5 d4xb6 a7xc5 f2-e3 g5-f4 e3xg5 g7-h6 e1-f2 h6xf4 f2-e3",
        "g3-h4 h6-g5 f2-g3 g5-f4"
    ];

    const BOOK_DATA_EXT =
        "IMUQEIVSKOaVFKZUJN|IMUQEIVSKOaVFKZUKN|IMUQEIVSKOYUOVZSBE|IMUQEIWSMRVMIRbWAE|IMUQEIYUKNcYFKWTBE|IMUQEIYUKNVRMVaKFO|IMUQEIYUKNWSNWaTBE|IMUQEIYUKNWSNWaTLO|IMUQEIYULOURGLZUDG|IMUQEIZUAEURKNRKGN|IMUQEIZUAEVRMVaRLO|IMUQEIZUAEVSLOSLHO|IMUQEIZUKNURNUYRFK|IMUQKNWSNWaTEIZUBE|IMUQKNWSNWaTEIZUFK|IMUQKNWSNWaTLOTKGN|IMUQKNWSNWbSLPfbGL|IMUQKNWSNWbSLPYUGL|IMUQKNXTLPbXEITOGK|IMUQKNXTLPbXEITOMR|IMUQKNXTLPVSMRbXEI|IMUQKNXTNSVOLSWNJS|IMUQLPYUEIWSAEbWMR|IMURMQRMJNMINRVMQJ|IMURMQWTLObWJNTPNU|IMXTMRUNKRVMJQTPEJ|IMXTMRUNKRVMJQWSFK|JMUQEJWTLPTOKTXOMR|JMUQFJYULPURHLZUDH|JMUQLOQJFMVRMVZLHO|JMUQLOQJFMWTMRVMIR|JMUQMRVMIRWSEJbWAE|JMUQMRVMIRWSEJbWBE|JMUQMRVMIRWSEJZUBE|JMUREJWSKOaWFKWTKN|JMUREJWSKObWFKWTAE|JMUREJWSLOSLHOaWOT|JMUREJWSMQSNJSVOKT|JMUREJWTLObWAETPMQ|JMUREJWTLObWJNfbNU|JMURFJWSLOSLHObWJN|JMURLPWSKOSLHOaWGL|JMVSKOUQOVQJFMZSLO|JMVSMQaVIMWTMRUNKa|JMVSMQUREJRNKRSOLS|JMVSMQURKNRKFVaREJ|JMVSMQURKOaVEJWTJM|JMVSMQURLPSOKTXOEJ|JMWSEJaWKNXTMRVMIR|JMWSEJSNKRUEAJbWMQ|JMWSEJSOKTXOLSVOMQ|JMWSEJSOLSVOKTXOGL|JMWSFJbWMQWTJNSJEN|JMWSKOaWEJWTFKbWMQ|JMWSKOaWMQWTEJTKGW|JMWSKOaWMQWTGKTPDG|JMWSKOaWMQWTLPTKGW|JMWSKObWEJURFKWTLP|JMWSKObWFKSNKRUNMQ|JMWSKObWFKUQBFQJFM|JMWSKObWFKUREJYUMQ|JMWSKObWMQWTFKTPEJ|JMWSKOUQGKQJEWaTAE|JMWSKOUQGKQJEWaTIM|JMWSKOUQGKQJEWaTLP|JMWSKOUQMRVMIRZUOV|JMWSKOUREJaWFKWTKN|JMWSLOSLHOVRMVZLGP|JMWSLPSOKTXOMQaWEJ|JMWSMQbWKOWTEJTKGW|JMWSMQUREJRMIRVMLO|JMWSMRUNKRVMIRbWEI|JMWSMRUNKRVMIRZUFK|JMWSMRVMIRUNKRXTRV|JMWSMRVMIRUNKRZUFK|JMWTEJbWJNURNUZJFM|JMWTEJTPMQbWLOWSAE|JMWTFJUQLPZUPWaTCF|JMWTLObWMRVMIRUNKR|JMWTMRUNKRVMIRTOLS|JMWTMRVMIRUNKRaVRa|JMWTMRVMIRUNKRTOLS|JNUQEJVSLOSLHOZVDH|JNUQEJVSLOSLHOZVOT|JNUQEJZULOURNUQZGL|JNUQEJZULOURNUQZJM|JNUQEJZULPURNUQZGL|JNUQLOZUFJURNUQZJN|JNUQNRVMIRWSEJSOKT|JNUQNRVMIRWTLObWEJ|JNUQNRVMIRWTLOTPKN|JNURNUYREJWSLOSLHO|JNURNUYREJWSLPaWKN|JNURNUYREJWSLPbWGL|JNURNUYREJWTAETPJN|JNURNUYRLOWSGLbWLP|JNVREJWTJMaVMQeaLO|JNVREJWTJMZVMQdZAE|JNVREJWTLObWOSaVSb|JNVREJZVJMUQNUQZAE|JNVREJZVJMUQNUQZFJ|JNVREJZVJMUQNUQZKN|JNVREJZVJMUQNUQZLO|JNVREJZVJMUQNUQZMQ|JNVREJZVJMUQNUQZMR|JNVREJZVLOWTNSUQSZ|JNVRFJaVJMWSNWbSMQ|JNVRFJaVJMWTMQTOLS|JNVRFJaVJMXTLOTPOT|JNVRFJWSNWbSJMRNKR|JNVRFJWTJMTPMVZJEN|JNVRFJWTLObWJMTPMV|JNVRFJWTLOTPJMbWMV|JNVRFJZVJMUQNUQZEJ|JNVRFJZVJMUQNUQZMR|JNVRLOWTEJbWHLTPOS|JNVRLOZVGLUQNUQZEJ|JNVRLPWTPWbJFVaREJ|JNVRLPZVGLWSNWbSLO|JNVSEJaVKOeaGKURNU|JNVSEJaVKOUQGKZUBE|JNVSEJaVKOUQGKZUDG|JNVSEJaVKOUQGKZULP|JNVSEJaVKOURNUYRJM|JNVSEJaVLOSLHOWTNS|JNVSEJSOKTWPLOZVGK|JNVSEJUQAEZVIMcZEI|JNVSEJUQAEZVIMYUEI|JNVSEJUQIMZUAEcZKO|JNVSEJUQLPZUGLaVLO|JNVSFJaVLOSLHOWTNS|JNVSLOSLHOURNUYREJ|JNVSLOSLHOWTNRUNKR|JNWSNWbSEJaWKOUQAE|JNWSNWbSIMfbMQSOKT|JNWSNWbSKOURGKfbLP|JNWSNWbSLPUREJRMIR|JNWTEJbWAETPLOVSOV|JNWTEJbWJMfbMRVMIR|JNWTEJTOKTXOLSVOAE|JNWTEJTPJMbWMQURNU|JNWTEJTPJMbWNRUNKR|JNWTEJTPJMUQNRQJFM|JNWTEJTPJMVSNWbSMQ|JNWTEJTPJMXTNRUNKR|JNWTLObWHLTPNRUNKR|JNWTLObWNRUNKRVMIR|JNWTLOVREJZVAEUQNU|JNWTLPUQPWbJFMQJEN|JNWTLPURPWbJEUYRKO|JNWTNRUNKRVMIRaVRa|JNWTNRUNKRVMIRTOLS|JNWTNRVMIRUNKRTOLS|JNWTNSVOLSaVGLVOLS|JNWTNSVOLSaVKOTKFO|JNXTLOTPNRUNKRVMIR|JNXTLPbXGLVSLOSLPG|JNXTLPUQHLZULObXNS|JNXTLPVREJbXHLaVLO|JNXTLPVSHLSJENUQDH|JNXTLPVSHLSJFMURMV|KNUQNRVMIRZVJMQJFM|KNVRFKWSNWbSJMRNKR|KNVRFKWTJMaVEJTOLS|KNVRFKWTJMTPMVZJEN|KNVRGKZVJMUQNUQZMR|KNVRGKZVJMWTDGUQNU|KNVSIMXTFKTOKTWPNW|KNWSNWbSLPfbJMbWMQ|KNWTFKbWLPVSGLTOKT|KNWTFKTPBFbWJMfbNR|KNWTFKTPBFbWLOURNU|KNWTFKTPBFbWNRUNJb|KNWTFKTPBFUQNRVMIR|KNWTFKTPBFVRJMbWMV|KNWTFKTPJMXTMRVMIR|KNWTJMTPMRVMIRXTEI|KNWTJMTPMRVMIRXTLO|KNWTJMVRMVaKGNbWEJ|KNWTJMVRMVaKGNeaIM|KNWTLPURNUYRPWbSJN|KNXTLPVSGKbXDGTOKT|KNXTLPVSGKbXDGUQNR|KNXTLPVSGKZVHLcZLO|KNXTLPVSIMbXMQTOEI|KNXTLPVSIMbXMRTOGK|KOUQJNVSOVaKFOWTEJ|KOUQJNVSOVaKGNYUEJ|KOUQJNVSOVaKGNYUFK|KOUQJNWSNWaKFObWEJ|KOURGKYUDGUQOTXOKT|KOWSJNSJFMbWOSVOLb|KOWTFKTPBFURJMYUMQ|KOWTGKTPDGbWOTXOLb|KOWTGKTPDGUQJNYUEJ|KOWTJMTKFOaWBFWTGK|KOWTJMTKFOaWGKWTBF|KOWTJMTKFOaWLPeaHL|KOWTJMTKFObWMRUNOS|KOWTJMTKFObWMRVMIR|KOWTJMTKFObWOSVOLb|KOWTJMTKFOUQMRVMIR|KOWTJMTKFOUREJbWGK|KOWTJMTKFOURGKbWMQ|KOWTJMTKFOURMQbWGK|KOWTJMTKFOVRMVaREJ|KOWTJMTKGNVRMVaKFO|KOWTOSVOLSURJMYUMV|LOUQGLWSJNSJENbWOS|LOUQJMQJFMWTMRVMIR|LOUQJNWSNWbLGPfbEJ|LOUQJNWSNWbLHOfbKN|LOVRHLZVJMWSMQdZEJ|LOVRJNWTHLTPEJbWJM|LOWSGLbWKNURNUYRJM|LOWSGLbWLPSLPGUQKO|LOWSGLbWLPSLPGWSJM|LOWSGLUQDGYUJNSJEN|LOWSHLbWJMUQMRVMIR|LOWSHLSNJSXTOXVHIM|LOWSHLURJNSJEUYRLP|LOWSHLXTOXSNJSVHIM|LOWSJNSJENbWOSVOKT|LOWTJMbWEJWSAESLGW|LOWTJMbWMQfbEJTPAE|LOWTJMbWMRUNKRVMIR|LPUQGLYUDGVRJNZVEJ|LPUQHLYUKOVRJMQJFV|LPUQHLYUKOWTPWaKFO|LPUQHLZUKNURNUQZLO|LPUQJNVRNUYREJZUBE|LPUQJNVSEJZVIMYUAE|LPUQJNWTPWbJENXTHL|LPUQJNZUEJURNUQZGL|LPURJNVSNUYREJRMIR|LPVSIMSOKTXOFKOFBK|LPWSGLbWLOSLPGURJM|LPWSGLSOLSVOKTXOIM|LPWSIMUREISOKTXOGL|LPWSJMbWGLfbLOSLPG|LPWSJMSOKTXOMQbWEJ|LPWSJMSOKTXOMQUREJ|LPWSJMSOKTXOMQURFJ|LPWSJNSJENURNUYRAE|LPWSJNSJENURNUYRKO|LPWSKNaWIMSOFKOFBK|LPWSKNbWGKVRPTWPNW|LPWSKOSLHObWFKebGL|LPWTPWbSGLSOKTXOLS|LPWTPWbSIMfbMQSOKT|LPWTPWbSIMUQEIZUBE|LPWTPWbSIMUQEIZUHL|LPWTPWbSIMUREISOKT|LPWTPWbSIMXTKNTPNW|LPWTPWbSJNSJENfbIM|LPWTPWbSJNSJENURNU|LPWTPWbSJNSJENVRNS|LPWTPWbSJNSJENVSNW|LPWTPWbSJNSJENXTAE|LPWTPWbSJNSJFMVSKN|IMUQEIVSKOaVFKZUJNQJ|IMUQEIVSKOaVFKZUKNUR|IMUQEIVSKOaVFKZUKNVR|IMUQEIVSKOYUOVZSBEXT|IMUQEIWSMRVMIRbWAEfb|IMUQEIWTLPbWMRVMIRTO|IMUQEIWTMRVMIRZVAEVM|IMUQEIXTLPbXGLfbAEVR|IMUQEIYUAEVSKNaVGKea|IMUQEIYUKNcYFKWTBEaW|IMUQEIYUKNVRMVaKFOWT|IMUQEIYUKNWSNWaTBEUR|IMUQEIYUKNWSNWaTLOTK|IMUQEIYULOURGLZUDGcY|IMUQEIYULPWSKNcYNWaT|IMUQEIYULPWSKNcYNWbS|IMUQEIZUAEURKNRKGNVR|IMUQEIZUAEVRMVaRLOWT|IMUQEIZUAEVSLOSLHOUR|IMUQKNVRMVaKGNZUDGUR|IMUQKNWSNWaTEIZUBEUR|IMUQKNWSNWaTEIZUFKTP|IMUQKNWSNWaTFKZUEITP|IMUQKNWSNWaTLOTKGNbW|IMUQKNWSNWbSFKYUJNQJ|IMUQKNWSNWbSLPYUGLUR|IMUQKNWTLPYUPWbSNWaT|IMUQKNWTNSVOLSaVGLVO|IMUQKNXTLPbXEITOGKZU|IMUQKNXTLPbXEITOMRVM|IMUQKNXTLPVSGLbXEITO|IMUQKNXTLPVSMRTOGKbX|IMUQKNXTNSVOLSWNJSQJ|IMUQKNXTNSWNJSVOLSQJ|IMUQKNYUGKcYEIWSNWaT|IMUQKNYUGKcYEIWSNWbS|IMUQKNYUNSWNJSQJENVO|IMUQLPWTPWaTEIZUHLTP|IMUQLPWTPWaTKOTKGNbW|IMUREIWSKObWFKWTLPSL|IMUREIWTJNbWNUZJFMfb|IMUREIWTLOTPAEbWOTXO|IMURMQRMJNMIEJWTLPbW|IMURMQRMJNMIEJWTLPYU|IMURMQRMJNMINRVMQJYU|IMURMQRMLPMIHLWSKOYU|IMURMQRMLPWSEISOIRVM|IMURMQRMLPWSHLSOLSVO|IMURMQRMLPWTPWbSHLMI|IMURMQRMLPWTPWbSJNSJ|IMVRMVaRLPZVGLWTPWbS|IMVSEIWTKOTKFVZSMQXT|IMVSKNXTMQaVEITPFKWT|IMVSKNXTMQbXFKaVJMSJ|IMVSKNXTMQTPFKaVKObX|IMVSKNXTMQTPFKbXJMSJ|IMVSMQWTKNTPNWbSJMfb|IMWSLPbWGLUQKNVRMOWT|IMWSMRUNKRVMJQYUEJaV|IMWTMQTPJNbWEJWTAETO|IMWTMQTPJNbWEJWTLOaW|IMWTMQTPJNbWNRUNKRVM|IMWTMQTPJNbWNRVMQJUQ|IMWTMRUNKRVMJQTPEJbW|IMWTMRVMJQTPEJbWAEaV|IMXTLOUROXRIHLYULPUQ|IMXTLOUROXRIJNYUHLUQ|IMXTMQTPJNWSNWbSEJfb|IMXTMQTPKNVSFKbXEIfb|IMXTMQTPKNVSFKbXJMSJ|IMXTMRUNKRVMJQTPEJWT|IMXTMRUNKRVMJQWSLPTO|IMXTMRVMJQTPEJbXJNWT|IMXTMRVMJQTPEJbXLOWT|JMUQEJWSLOSLGPaWHLWS|JMUQEJWTAETOKTXOLSVO|JMUQEJWTLPTOKTXOMRVM|JMUQEJWTMRVMIRTPAEbW|JMUQEJZUKNURNUQZMRVM|JMUQEJZUKOURFKWSLPSL|JMUQFJWSLPZUJNSJMFUR|JMUQFJYULPURHLZUDHWS|JMUQLOQJENWSNWbLHOfb|JMUQLOQJFMWTEJbWAETP|JMUQLOQJFMWTEJbWBFTP|JMUQLOQJFMWTEJbWMQTP|JMUQLOQJFMWTMRVMIRbW|JMUQLOQJFMYUMRUNKRVM|JMUQLPQJFMWTPWbSHLfb|JMUQMRVMIRWSEJbWAEfb|JMUQMRVMIRWSEJbWBEfb|JMUQMRVMIRWSEJSOKTXO|JMUQMRVMIRWSEJSOLSZV|JMUQMRVMIRWSLOSLHObW|JMUQMRVMIRWTEJbWAETP|JMUQMRVMIRWTEJbWLOZU|JMUQMRVMIRWTEJTPLObW|JMUQMRVMIRWTEJZVAEVM|JMUQMRVMIRWTFJaVRaeV|JMUQMRVMIRWTKNbWFKTP|JMUQMRVMIRWTLOTPEJbW|JMUQMRVMIRZVEIVMIRcZ|JMUREJWSKOaWMQeaJMWT|JMUREJWSKObWAEWTLPTK|JMUREJWSKObWFKWTAETP|JMUREJWSKObWFKWTLPSL|JMUREJWSKObWFKYUMQeb|JMUREJWSKObWGKWTLPSL|JMUREJWSKORNAEbWFKZU|JMUREJWSKORNAEbWLPSL|JMUREJWSLOSLHObWMQWT|JMUREJWTJNbWNUZJFMfb|JMUREJWTLObWJNfbNUZJ|JMUREJWTLObWJNTPNUZJ|JMUREJWTLObWMQRMIRVM|JMUREJWTLObWMQTPJMWS|JMUREJWTLObWMQTPJNWT|JMUREJWTLObWMQWSJMSL|JMUREJWTLOTPJNbWNUZJ|JMUREJWTLPTOKTXOMQRM|JMURFJWSCFaWMQeaKOWT|JMURFJWSKOaWMQWTJMTK|JMURFJWSKObWMQebJMYU|JMURFJWSLOSLHOaWJNWS|JMURFJWSLOSLHOaWJNYU|JMURKNRKGNVSEJSOLSaV|JMURKNRKGNWTMRVMIRZU|JMURKOWTLPTKGUZJENXT|JMURLOWTEJbWAEfbMQTP|JMURLOWTEJbWAEfbMQYU|JMURLOWTEJbWJNTPNUZJ|JMURLOWTEJbWMQRMIRVM|JMURLOWTEJbWMQTPOTXO|JMURLOWTEJbWMQWSAESL|JMURLOWTEJbWMQWSJMSL|JMURLOWTGLTPCGbWOTXO|JMURLPWTPWbSGLfbKObW|JMURLPWTPWbSHLfbLPbW|JMURMQVSKOaVEJWTLPTK|JMVRMVaREJWTJMdaMVaR|JMVRMVaRFJXTJMbXMVZS|JMVSEJWTLPTOKTXOGKUQ|JMVSFJaVMQeaJNSJENUR|JMVSFJWTMQSNKRUNJSTO|JMVSFJWTMQTOKTXOIMSN|JMVSKOaVFKUREJWTKNTK|JMVSKOaVFKWTMRUNKaeV|JMVSKOaVMQeaEJWTJMTK|JMVSKOaVMRUNOTXOGKNP|JMVSKOUQOVQJENaKFOYU|JMVSLPSOKTXOMQUREJaV|JMVSMQaVIMUREIWTLPSN|JMVSMQaVIMWTMRUNKaeV|JMVSMQUREJRNKRSOLSWE|JMVSMQURFJRMIRZUQZcO|JMVSMQURKNRKFVaREJea|JMVSMQURKNSJEUYRFJWS|JMVSMQURKNSJFVaREJea|JMVSMQURKNSJFVaREJXT|JMVSMQURKOaVEJWTGKSN|JMVSMQURKOaVEJWTJMTK|JMVSMQURKOaVFKeaEJYU|JMVSMQURKOaVFKWTKNTK|JMVSMQURKOaVGKWTLPSL|JMVSMQURKOSNOSNKGUWN|JMVSMQURLPSOKTXOEJZU|JMVSMQURLPSOKTXOEJZV|JMVSMQURLPSOKTXOFJaV|JMVSMQWTEJTOKTXOJMUR|JMVSMQWTKOTKFVaRLObW|JMVSMQWTKOTKFVZSQZdU|JMWSEJaWKNeaMQSOLSVO|JMWSEJaWKNXTMRVMIRbX|JMWSEJaWMQeaJMWTMRUN|JMWSEJbWAEfbMRUNKRVM|JMWSEJbWAEUQMRVMIRfb|JMWSEJbWAEWTMRUNKRVM|JMWSEJbWKOUQFKZUJNSJ|JMWSEJbWKOUQGKZULPSL|JMWSEJSOKTXOLSVOMQbW|JMWSEJSOKTXOLSVOMQUR|JMWSEJSOLSVOKTXOAEUR|JMWSEJSOLSVOKTXOBEUQ|JMWSEJSOLSVOKTXOBEZV|JMWSEJSOLSVOKTXOGLaW|JMWSEJSOLSVOKTXOMQUR|JMWSEJURKOaWFKWTKNTK|JMWSEJURKOYUMQcYJMbW|JMWSEJURMQRMIRVMAEMI|JMWSEJURMQRMIRVMKOaV|JMWSFJbWMQWTJNSJENTO|JMWSFJbWMQWTJNSJENTP|JMWSKOaWEJWTFKTPBFUR|JMWSKOaWEJWTGKTPDGUR|JMWSKOaWFKUQMRVMIRWT|JMWSKOaWFKWTEJbWBFUQ|JMWSKOaWFKWTEJTPBFUR|JMWSKOaWFKWTMRUNKaTK|JMWSKOaWGKWTEJTPDGUR|JMWSKOaWGKWTEJURKNRK|JMWSKOaWGKWTLPSLPGTO|JMWSKOaWMQeaEJWTJMTK|JMWSKOaWMQUREJWTJMTK|JMWSKOaWMQWTEJTKGWbS|JMWSKOaWMQWTFKTPEJUR|JMWSKOaWMQWTGKTPDGUR|JMWSKOaWMQWTGKURLPSL|JMWSKOaWMQWTLPTKGWbS|JMWSKObWEJUQFKZUJNSJ|JMWSKObWEJUQGKZULPSL|JMWSKObWEJUQMRVMOVaR|JMWSKObWEJURFKWTLPSL|JMWSKObWEJURFKYUMQcY|JMWSKObWFKUQBFQJFMfb|JMWSKObWFKUQBFQJFMYU|JMWSKObWFKUQEJZUJNSJ|JMWSKObWFKUQMRVMIRSN|JMWSKObWFKUREJWTLPSL|JMWSKObWFKUREJYUMQcY|JMWSKObWFKUREJZUMQRM|JMWSKObWFKWTLPSLPWaT|JMWSKObWGKUQLPSLPGQJ|JMWSKObWGKWTLPSLPGfb|JMWSKObWMQWTEJTKGWaT|JMWSKObWMQWTFKTPEJUR|JMWSKObWMQWTLPTKGWaT|JMWSKOUQEJZUGKaWKNVR|JMWSKOUQGKQJEWaTAETP|JMWSKOUQGKQJEWaTAEYU|JMWSKOUQGKQJEWaTIMea|JMWSKOUQGKQJEWaTIMTP|JMWSKOUQGKQJEWaTIMZU|JMWSKOUQGKQJEWaTLPYU|JMWSKOUQGKQJEWbSIMaW|JMWSKOUQGKQJEWbSIMYU|JMWSKOUREJaWFKWTKNTK|JMWSKOURFKbWEJZUMQRM|JMWSLOSLHOUREJaWAEWS|JMWSLOSLHOUREJaWJNWS|JMWSLOSLHOVRMVZLGPXT|JMWSLPSOKTXOEJbWMQUR|JMWSLPSOKTXOEJURAEYU|JMWSLPSOKTXOMQaWEJWT|JMWSLPSOKTXOMQbWEJfb|JMWSLPSOKTXOMQbWEJWT|JMWSLPSOKTXOMQUREJaW|JMWSLPSOKTXOMQUREJbW|JMWSLPSOKTXOMQUREJRM|JMWSLPUQGLQJEWbSKOfb|JMWSLPUQPTXOKTQJEWbS|JMWSMQbWIMUREISNLPWS|JMWSMQSOKTXOLSVOEJbW|JMWSMQSOLSVOKTXOEJbW|JMWSMQURLPSOKTXOEJbW|JMWSMQURLPSOKTXOEJZU|JMWSMRUNKRVMIRbWLOSL|JMWSMRUNKRVMIRSOLSZU|JMWSMRUNKRVMIRZUFKUN|JMWSMRVMIRUNKRZUFKUN|JMWSMRVMIRUNKRZULOUN|JMWTEJbWAETPMQWSLOSL|JMWTEJbWJNfbMRVMIRTP|JMWTEJbWJNURNUZJFMVS|JMWTEJbWLOfbMQTPOTXO|JMWTEJbWMQURLOTPJNWT|JMWTEJbWMQWSAESOLSVO|JMWTEJbWMQWSLPSOPWaT|JMWTEJTOKTXOLSVOMQbW|JMWTEJTOLSVOKTXOBEUR|JMWTEJTOLSVOKTXOBEZV|JMWTEJTOLSVOKTXOMQbW|JMWTEJTPAEURKOaWOTXO|JMWTEJTPJNbWNRUNKRZU|JMWTEJTPJNUQNRQJFMbW|JMWTEJTPLObWOTXOKTWS|JMWTEJTPMQbWJMURLOfb|JMWTEJTPMQbWJNVSFJaV|JMWTEJTPMQbWLOWSAESL|JMWTEJTPMQXTLObXJNUR|JMWTEJUQMRVMIRTPLObW|JMWTFJbWBFVSLPTOKTXO|JMWTFJUQLPZUPWaTCFUR|JMWTFJUQLPZUPWaTCFVS|JMWTFJUQLPZUPWaTKNUR|JMWTKNaWNSWNMRVMIKea|JMWTKNaWNSWNMRVMIKTP|JMWTKNTOLSVOEJbWGLfb|JMWTKNTOLSVOEJURNUYR|JMWTKNTOLSVOGLaVLSVO|JMWTKNTPMQXTEJaWAEWS|JMWTKNTPMQXTEJbXAEfb|JMWTKNTPMRVMIRbWFKUQ|JMWTKNVRMVaKGNbWEJTP|JMWTLObWEJfbAETPMRVM|JMWTLObWEJTPMQURJNfb|JMWTLObWEJTPMQWSAESL|JMWTLObWEJWSAESLGWaT|JMWTLObWEJWSMQSLGWaT|JMWTLObWMQWSEJSLGWaT|JMWTLObWMRUNKRVMIRTK|JMWTLObWMRVMIRUNKRTK|JMWTLOUQMRVMIRbWEJfb|JMWTLOUREJbWJNTPNUZJ|JMWTLOUREJbWMQTPJMWT|JMWTLOVRMVZLGWbSHLfb|JMWTLPTOKTXOMQbWFJWT|JMWTLPTOKTXOMQUREJbW|JMWTLPTOKTXOMQUREJRM|JMWTLPUQPWQJENbJFMfb|JMWTLPUQPWQJENbJFMXT|JMWTMQbWEJWSLPSOPWaT|JMWTMQTPEJXTJMTOKTPW|JMWTMQTPEJXTJMTOLSVO|JMWTMRUNKRVMIRTOLSZU|JMWTMRUNKRVMIRTPEJXT|JMWTMRUNKRVMIRTPLOZU|JMWTMRUNKRVMIRZUFKUN|JMWTMRVMIRUNKRaWFKWS|JMWTMRVMIRUNKRTOLSZU|JMWTMRVMIRUNKRTPEJbW|JMWTMRVMIRUNKRTPLObW|JMXTEJTPMQWSJMSOKTPW|JMXTLObXEJfbMQTPJNUR|JMXTLPbXGLUQMRVMIRZV|JMXTLPbXMQTOKTXOEJfb|JMXTLPbXMQTOKTXOGKWT|JMXTLPbXMQVSKNSJENUR|JMXTLPUQGLQJFMbXEJVS|JMXTLPUQHLQJFMVSMQSN|JMXTLPUQMRVMIRZUKNTO|JMXTLPUQMRVMIRZURVaR|JMXTLPVSHLbXDHebKOTD|JMXTLPVSMQaVEJeaJNSJ|JMXTMQbXIMVSEITOKTXO|JNUQEJVSLOSLHOZUAEUR|JNUQEJWSNWbSKOZUJNSJ|JNUQEJWTAETPLObWNSWN|JNUQEJWTAETPLOVRNUYR|JNUQEJWTLPbWGLZULOUR|JNUQEJWTNRVMIRbWLOfb|JNUQEJYUAEVRIMRINSWN|JNUQEJZUAEWTLOVROSaW|JNUQEJZUAEWTLPQMJSaV|JNUQEJZULOdZGLVSOVaR|JNUQEJZULPURNUQZIMYU|JNUQEJZULPVRGLRMIRWT|JNUQEJZULPWTPWaTNSVO|JNUQKOWTGKQMIRVMEIZV|JNUQKOWTNRTKGNVMIRbW|JNUQKOYUNSWNOTXOLJbW|JNUQKOZUFJURNUQZJNVS|JNUQKOZUGKVRIMQSOMaV|JNUQKOZUGKVRIMQSOMWT|JNUQLOWSNWbLHOYUOTXO|JNUQLOWTEJbWAETPNRVM|JNUQLOWTEJZUNScZKNTR|JNUQLOWTEJZUNSdZSWbL|JNUQLOWTEJZUNSVRJNcZ|JNUQLOZUEJWTNSVRJNTP|JNUQLPVSEJSOKTXOAEWS|JNUQLPWTPWbJENXTGLTP|JNUQNRVMIRWSEJbWAEfb|JNUQNRVMIRWSEJbWBEfb|JNUQNRVMIRWSEJbWBEZU|JNUQNRVMIRWSEJbWLOSL|JNUQNRVMIRWSEJSNJSZV|JNUQNRVMIRWSEJSOLSaV|JNUQNRVMIRWSLOSLHObW|JNUQNRVMIRWTEJbWAETP|JNUQNRVMIRWTEJbWJNTP|JNUQNRVMIRWTEJbWLOaV|JNUQNRVMIRWTEJbWLOfb|JNUQNRVMIRWTEJbWLOTP|JNUQNRVMIRWTEJbWLOZV|JNUQNRVMIRWTEJTPAEbW|JNUQNRVMIRWTEJTPAEXT|JNUQNRVMIRWTEJTPLObW|JNUQNRVMIRWTEJZVAEVM|JNUQNRVMIRWTEJZVJMQJ|JNUQNRVMIRWTKNbWFKTP|JNUQNRVMIRWTKNTPFKXT|JNUQNRVMIRWTKNTPLObW|JNUQNRVMIRWTKNZUFKcZ|JNUQNRVMIRWTLObWEJfb|JNUQNRVMIRWTLObWEJTP|JNUQNRVMIRWTLObWEJZV|JNUQNRVMIRWTLObWKNTK|JNUQNRVMIRWTLOTPEJbW|JNUQNRVMIRWTLOTPHLbW|JNUQNRVMIRWTLOZUHLUN|JNUQNRVMIRZUKNdZLOWT|JNUQNRVMIRZUKNdZLOZV|JNUQNRVMIRZUKNWTFKTP|JNUQNRVMIRZULOUNKRdZ|JNUQNRVMIRZULOUNKRWT|JNUQNRVMIRZVEIVMIRWT|JNUQNSWNKRVMIRZVEIVM|JNURNUYREJWSKOaWJMZU|JNURNUYREJWSKObWJMWT|JNURNUYREJWTAETPJNRM|JNURNUYREJWTJMTOLSVO|JNURNUYREJWTJMTPLObW|JNURNUYREJWTJNRMIRVM|JNURNUYREJWTLObWJMfb|JNURNUYREJWTLObWJMTP|JNURNUYREJWTLOTPAEbW|JNURNUYREJWTLOTPJMbW|JNURNUYREJWTLOTPJNbW|JNURNUYREJWTLPTOKTXO|JNURNUYRFJZULPUQJMQJ|JNURNUYRLPVSKNRKFVaR|JNURNUZQEJWSKObWGKYU|JNURNUZQEJWSKOYUJNSJ|JNURNUZQKNVRNUQZEJaV|JNURNUZQKNVRNUQZFKaV|JNURNUZQLOWSGLYUOTXO|JNURNUZQLPWSPTXOKTYU|JNVREJaVAEVSLPRMIRSO|JNVREJaVBEWTJMTPLOUQ|JNVREJaVJMUQNUQJFMZJ|JNVREJaVJMXTLObXMQfb|JNVREJaVJMXTMQbXLOfb|JNVREJaVJMXTMQTPAEWT|JNVREJaVJMXTMQTPFJda|JNVREJaVJMXTMQTPFJWT|JNVREJaVJMXTMQTPLOWS|JNVREJaVLOWTBEbWJMTP|JNVREJaVLOWTBETPJMUQ|JNVREJaVLOWTBEUQNUYR|JNVREJaVLOWTHLTPDHea|JNVREJaVLOWTHLTPDHUQ|JNVREJaVLOWTJMbWMQfb|JNVREJaVLOWTJMUQNUQJ|JNVREJaVLPeaGLVSLOSL|JNVREJaVLPeaGLWTPWaT|JNVREJaVLPVSGLZVLOSL|JNVREJaVLPVSHLZVPTXH|JNVREJaVLPXTHLbXLOWS|JNVREJWTBEbWJMTPMVZJ|JNVREJWTBEZVJMbWMQcZ|JNVREJWTJMaWMVZJFMWS|JNVREJWTJMTPMVZJFMUQ|JNVREJWTJMUQMVZJFMQJ|JNVREJWTJMUQNUQJFMZJ|JNVREJWTJMZVLOTPMQdZ|JNVREJWTLObWBETPJMWT|JNVREJWTLObWJMUQMVZJ|JNVREJXTBETOLSaVJMVO|JNVREJXTJMTPMVZJFMWS|JNVREJXTJMUQNUQJFMZJ|JNVREJXTLOTPBEaVHLWS|JNVREJXTLOTPBEaVJMVS|JNVREJXTLOTPJMWSNWbL|JNVREJXTLOTPOTbXJMXO|JNVREJXTLOTPOTZVJMUQ|JNVREJXTLPaVHLbXLOWS|JNVREJXTLPbXGLZVLOUQ|JNVREJXTLPbXHLaVJMWS|JNVREJXTLPbXHLaVLOda|JNVREJXTLPbXHLZVJMUQ|JNVREJXTLPZVGLbXJMUQ|JNVREJXTLPZVJMUQNUQZ|JNVREJZVJMUQNUQJFMYR|JNVREJZVJMUQNUQZAEVS|JNVREJZVJMUQNUQZAEWS|JNVREJZVJMUQNUQZAEWT|JNVREJZVJMUQNUQZAEXT|JNVREJZVJMUQNUQZAEYU|JNVREJZVJMUQNUQZAEZU|JNVREJZVJMUQNUQZFJWS|JNVREJZVJMUQNUQZFJWT|JNVREJZVJMUQNUQZFJXT|JNVREJZVJMUQNUQZKNVR|JNVREJZVJMUQNUQZKNVS|JNVREJZVJMUQNUQZKNWS|JNVREJZVJMUQNUQZKNXT|JNVREJZVJMUQNUQZLOWS|JNVREJZVJMUQNUQZLOWT|JNVREJZVJMUQNUQZLOYU|JNVREJZVJMUQNUQZMQWS|JNVREJZVJMUQNUQZMQWT|JNVREJZVJMUQNUQZMRVM|JNVREJZVJMUQNUYRLOQJ|JNVREJZVJMWSNWbSBEfb|JNVREJZVJMWTLObWMQcZ|JNVREJZVJMWTMQcZLOTP|JNVREJZVLOUQNUQZAEWS|JNVREJZVLOUQNUQZAEYU|JNVREJZVLOUQNUQZJMWT|JNVREJZVLOWTNScZIMRI|JNVREJZVLOWTNSUQSZdU|JNVREJZVLPUQNUQZHLWS|JNVRFJaVJMUQNUQJENYR|JNVRFJaVJMWTEJbWLOTP|JNVRFJaVJMWTMQTOLSVF|JNVRFJaVJMWTMQTPLObW|JNVRFJaVLPXTGLbXLOWS|JNVRFJWSNWbSJMRNKRUN|JNVRFJWSNWbSJMSNMVaR|JNVRFJWTJMaVLOUQNUYR|JNVRFJWTJMaVMQTOLSVF|JNVRFJWTJMTPMVZJENUQ|JNVRFJWTJMUQMVZJENTP|JNVRFJWTJMZVMQcZCFTP|JNVRFJWTJMZVMQcZLOTP|JNVRFJWTLObWJMTPMVZJ|JNVRFJWTLOTPJMbWMVZJ|JNVRFJWTLOZVNScZIMRI|JNVRFJWTLOZVNSdZSWbL|JNVRFJWTLOZVNSUQSZcV|JNVRFJWTLOZVNSUQSZdU|JNVRFJZVBFWSNWbSJMfb|JNVRFJZVJMUQNUQZEJWT|JNVRFJZVJMUQNUQZMQWS|JNVRFJZVJMUQNUQZMRVM|JNVRFJZVJMWTMQcZLObW|JNVRFJZVJMWTMQcZLOTP|JNVRLOWTEJbWJMTPMVZJ|JNVRLOWTFJbWJMTPMVZJ|JNVRLOZVEJWTNSUQSZdU|JNVRLPWTPWbJFVaREJfb|JNVRLPWTPWbJFVaREJZV|JNVRLPXTGLbXEJaVLOWS|JNVRLPZVGLRMIRVMEIcZ|JNVRLPZVGLUQNUQZIMYU|JNVRLPZVHLUQNUQZIMWS|JNVRLPZVHLUQNUQZIMWT|JNVRLPZVHLUQNUQZIMYU|JNVRLPZVHLVSDHSJFVaR|JNVSEJaVAEVRLPRMIRSO|JNVSEJaVKOdaOTXOGKbX|JNVSEJaVKOeaFKURNUYR|JNVSEJaVKOeaGKURNUYR|JNVSEJaVKOUQFKZUJMQJ|JNVSEJaVKOUQGKZUBEUR|JNVSEJaVKOUQGKZUDGea|JNVSEJaVKOUQGKZUDGUR|JNVSEJaVKOUQGKZULPSL|JNVSEJaVKOURNUYRJMea|JNVSEJaVKOURNUYRJMZU|JNVSEJaVKOURNUZQGKYU|JNVSEJaVLOSLHOWTDHUR|JNVSEJaVLPUQGLZUKOUR|JNVSEJaVLPVRGLZVLOSL|JNVSEJSOLSURNUWEAJZQ|JNVSEJUQAEZVIMdZKOZU|JNVSEJUQAEZVIMYUEIUR|JNVSEJUQIMZUMRcZAEZV|JNVSEJUQIMZUMRdZAEZV|JNVSEJUQIMZUMRXTLOSL|JNVSEJUQKOYUOVaKFOWT|JNVSEJUQLOSLHOQMJQWT|JNVSEJURNUYRKORNOVaR|JNVSEJZVKOUQGKYUBEcY|JNVSEJZVKOUQGKYUBEUR|JNVSEJZVKOUQGKYUDGUR|JNVSEJZVKOUQNRVMIRXT|JNVSEJZVKOURNUYRJMcZ|JNVSFJaVKOUQGKZUDGUR|JNVSFJaVKOURNUYRBFWT|JNVSFJaVKOURNUYRJMRN|JNVSFJaVKOURNUYRJMZU|JNVSFJaVLPXTCFUQGLZU|JNVSFJZVKOUQGKYULPSL|JNVSFJZVKOURNUYRJMRN|JNVSLOSJENaVOSVOKadW|JNVSLOSJENUQAEWSNWbL|JNVSLOSJENUQFJWTBEaV|JNVSLOSJENUQHLWTAETP|JNVSLOSJENUQHLZUAEWT|JNVSLOSJFMWTMQbWEJTP|JNVSLOSJFMWTMRUNKRTK|JNVSLOSLHOUQNRWTIMQJ|JNVSLOSLHOURNUYREJaV|JNVSLOSLHOWTIMaVMQbW|JNVSLPSJFMWSGLaVLOSL|JNVSLPSJFMWSHLaVKObW|JNVSLPSJFMWSHLUQEJaV|JNVSLPSJFMWTPWbSEJfb|JNVSLPSJFMWTPWbSEJXT|JNWSNWaTEJUQAEZUJNUR|JNWSNWaTIMTPLOUQEIQJ|JNWSNWaTIMUREITPLObW|JNWSNWaTKNbWFKTPNRVM|JNWSNWaTKNbWFKVREJTP|JNWSNWaTKNbWLPWSNWTa|JNWSNWaTKNTPLOVRFKbW|JNWSNWaTLOdaEJbWJMUQ|JNWSNWaTLOeaFJbWJNUR|JNWSNWbSEJebKOaWGKWT|JNWSNWbSEJfbKObWGKUR|JNWSNWbSEJfbKObWGKWT|JNWSNWbSEJUQKOZUJNSJ|JNWSNWbSEJXTLPSOPWaT|JNWSNWbSFJSNJSVFCJfb|JNWSNWbSIMaWMQURKOWT|JNWSNWbSIMaWMQWTKNSJ|JNWSNWbSIMebMQSOLSVO|JNWSNWbSIMfbKObWMQUR|JNWSNWbSIMfbMQbWEIUR|JNWSNWbSIMUQLPQJEWaT|JNWSNWbSKOfbEJbWGKUR|JNWSNWbSLOSLHOfbEJVR|JNWSNWbSLPfbEJbWGLUQ|JNWTEJaWAEeaLPVRJMZV|JNWTEJaWBETPNRVMJQUR|JNWTEJaWLOdaGLTPAEPG|JNWTEJaWLPeaAEVRJMUQ|JNWTEJaWLPeaAEVRJMZV|JNWTEJbWAEUQNSVOLbfW|JNWTEJbWAEVRLPaVGLWS|JNWTEJbWJMebMRVMIRTP|JNWTEJbWJMfbMQTOKTXO|JNWTEJbWJMfbMRVMIRTP|JNWTEJbWJMTPMQURNUYR|JNWTEJbWJMTPMRVMIRfb|JNWTEJbWJMTPMRVMIRUQ|JNWTEJbWJMTPNRUNKRWS|JNWTEJbWJMTPNRUNKRZU|JNWTEJbWJMUQMRVMIRTP|JNWTEJbWJMUQNRQJFMfb|JNWTEJbWJMUQNRQJFMTP|JNWTEJbWJMURNUZJFMfb|JNWTEJbWJMURNUZJFMVS|JNWTEJbWJMURNUZJFMYU|JNWTEJbWJMVSFJTPMQaV|JNWTEJbWJMVSMQSJFMTP|JNWTEJbWLOfbAEVRGLTP|JNWTEJTOKTXOLSVOAEUR|JNWTEJTOKTXOLSVOIMOK|JNWTEJTOLSVOKTXOAEUR|JNWTEJTOLSVOKTXOJMbW|JNWTEJTPBEbWJMUQNRQJ|JNWTEJTPJMbWBEUQNRQJ|JNWTEJTPJMbWMQURNUYR|JNWTEJTPJMbWMQWTLOUR|JNWTEJTPJMbWMRVMIRfb|JNWTEJTPJMbWMRVMIRUQ|JNWTEJTPJMbWMRVMIRWT|JNWTEJTPJMbWNRUNKRfb|JNWTEJTPJMbWNRUNKRWS|JNWTEJTPJMbWNRUNKRWT|JNWTEJTPJMbWNRUNKRZU|JNWTEJTPJMUQNRQJFMbW|JNWTEJTPJMVRMVZJFMdZ|JNWTEJTPJMVRMVZJFMUQ|JNWTEJTPJMVSNWbSFJaV|JNWTEJTPJMVSNWbSFJfb|JNWTEJTPJMVSNWbSMQfb|JNWTEJTPJMXTMQTOKTPW|JNWTEJTPJMXTMQTOLSVO|JNWTEJTPJMXTMRVMIRaW|JNWTEJTPJMXTMRVMIRbX|JNWTEJTPJMXTMRVMIRZV|JNWTEJTPJMXTNRUNKRbW|JNWTEJTPJMXTNRUNKRTO|JNWTEJTPJMXTNRUNKRZU|JNWTEJTPLObWOTXOKTVR|JNWTEJTPLOUQNRVMIRaW|JNWTEJTPLOURNUYRAEbW|JNWTEJTPLOVRBEbWJMWT|JNWTEJTPLOVRJMUQMVZJ|JNWTEJUQAETPLObWNSWN|JNWTEJUQNRVMIRTPAEbW|JNWTEJUQNRVMIRTPLObW|JNWTEJURNUZQAEYUJNVR|JNWTEJVRBEbWJMTPMVZJ|JNWTEJVRJMaWMVZJFMWS|JNWTEJVRJMbWMVZJFMfb|JNWTEJVRJMbWMVZJFMWS|JNWTEJVRJMUQMVZJFMQJ|JNWTEJVRJMUQNUQJFMZJ|JNWTEJVRLObWBEaVJMVS|JNWTEJVRLOZVNSUQSZcV|JNWTFJbWBFTPNRUNJbfW|JNWTFJTPBFbWJMWTNRUN|JNWTFJTPBFVRJMZVMQcZ|JNWTFJTPJMbWMRVMIRUQ|JNWTFJTPJMXTMRVMIRbX|JNWTFJUQBFTPLObWOTXO|JNWTFJVRJMaVMQTPEJda|JNWTFJVRJMZVMQcZLOTP|JNWTLObWHLTPNRUNKRVM|JNWTLObWHLUQNRVMIRTP|JNWTLObWHLUQNSWNKRVM|JNWTLObWNRUNKRVMIRTK|JNWTLOUQNRVMIRbWEJTP|JNWTLOVREJaVBEbWJMUQ|JNWTLOVREJbWJMUQNUQJ|JNWTLOVREJTPJMUQMVZJ|JNWTLOVREJTPJMUQNUQJ|JNWTLOVRFJbWJMfbMVZJ|JNWTLOVRFJbWJMTPMVZJ|JNWTLPUQPWbJENXTAEfb|JNWTLPUQPWbJENXTAETP|JNWTLPUQPWbJENXTAEYU|JNWTLPUQPWbJENXTHLTP|JNWTLPUQPWbJFMQJENfb|JNWTLPUQPWbJFMQJENYU|JNWTLPURPWbJEUYRAEVS|JNWTNRUNKRVMIRaWFKda|JNWTNRUNKRVMIRaWGKda|JNWTNRUNKRVMIRaWGKTP|JNWTNRUNKRVMIRaWLOTK|JNWTNRUNKRVMIRbWLPeb|JNWTNRUNKRVMIRTOLSaW|JNWTNRUNKRVMIRTOLSZU|JNWTNRUNKRVMIRTPEJbW|JNWTNRUNKRVMIRTPEJZU|JNWTNRUNKRVMIRTPFKbW|JNWTNRUNKRVMIRTPLObW|JNWTNRVMIRUNKRaWFKWS|JNWTNRVMIRUNKRTOLSZU|JNWTNRVMIRUNKRTPEJbW|JNWTNRVMIRUNKRTPFKbW|JNWTNRVMIRUNKRZUFKUN|JNWTNSVOLSaVKOTKFObW|JNWTNSVOLSaWFJWNJSda|JNXTEJbXJMVSMQSJFMTP|JNXTEJTOKTWPFKUQLOZU|JNXTEJTOKTWPLOVRFKZV|JNXTEJTOLSVOKTWPAEaV|JNXTEJTOLSVOKTWPAEbW|JNXTEJTOLSVOKTWPAEbX|JNXTEJTPJMWSNWbSMQfb|JNXTEJTPJMWSNWbSMQSO|JNXTEJTPJMWSNWbSMQUR|JNXTEJTPLOUQOTZUTXVR|JNXTEJVRJMUQNUQJFMZJ|JNXTLObXHLfbLPVSOVZJ|JNXTLObXHLTPNRUNKRVM|JNXTLObXHLUQNRVMIRTP|JNXTLObXHLUQNSWNKRTK|JNXTLObXHLUQNSWNKRVM|JNXTLObXNRUNKRVMIRTK|JNXTLObXNRVMIRUNKRTK|JNXTLOTPOTVSTXSJENWS|JNXTLPbXGLVRLOaVHLWS|JNXTLPbXGLVSDGSJENUQ|JNXTLPbXGLVSDGSJENUR|JNXTLPbXGLVSDGSJFMUQ|JNXTLPbXGLVSLOSJFMaV|JNXTLPbXGLVSLOSLPGTO|JNXTLPbXHLVSDHSJENUQ|JNXTLPbXHLVSDHSJENUR|JNXTLPbXHLVSDHSJFMUR|JNXTLPbXNRUNKRVMIReb|JNXTLPbXNRUNKRVMIRTO|JNXTLPbXNRUNKRVMIRZV|JNXTLPbXNRVMIRUNKRZV|JNXTLPUQEJVSAEbXIMZU|JNXTLPUQEJZUGLbXLOUR|JNXTLPUQEJZUGLVRLObX|JNXTLPUQEJZUHLVSBEaV|JNXTLPUQFJVSGLbXLOSL|JNXTLPUQGLbXLOZUHLVR|JNXTLPUQGLYULObXHLVS|JNXTLPUQGLZUDGbXEJUR|JNXTLPUQGLZUDGURNUQZ|JNXTLPUQGLZUDGURNUYR|JNXTLPUQGLZUEJbXLOVR|JNXTLPUQGLZUFJbXDGVR|JNXTLPUQGLZULObXEJUR|JNXTLPUQGLZULObXHLUR|JNXTLPUQGLZULObXHLVR|JNXTLPUQHLVSDHSJFMQJ|JNXTLPUQHLVSEJbXDHYU|JNXTLPUQHLZULObXNSWN|JNXTLPUQNRVMIRaVRaeV|JNXTLPUQNRVMIRZUEIUN|JNXTLPUQNRVMIRZUKNTO|JNXTLPUQNRVMIRZURVaR|JNXTLPVREJaVHLbXLOWS|JNXTLPVREJbXGLZVLOUQ|JNXTLPVREJbXHLaVLOWS|JNXTLPVREJbXJMTOMVZJ|JNXTLPVRFJbXJMTOMVZJ|JNXTLPVRGLaVLObXEJWS|JNXTLPVRGLaVLObXHLWS|JNXTLPVRGLbXEJaVAEWS|JNXTLPVRHLaVEJbXJMWS|JNXTLPVSEJUQGLbXLOSL|JNXTLPVSGLSJFMbXLOUQ|JNXTLPVSHLSJENUQLObX|JNXTLPVSHLSJENZVAETO|JNXTLPVSHLSJENZVLObX|JNXTLPVSHLSJFMbXDHUQ|KNUQNRVMIRWTJNTPLObW|KNURNUYRFKRNKRVFBKaV|KNVRFKaVLPVSGLUQNUYR|KNVRFKaVLPXTGLUQNUYR|KNVRFKWSNWbSJMRNKRUN|KNVRFKWTJMaVEJTOLSVF|KNVRFKWTJMTPMVZJENUQ|KNVRFKZVJMUQNUQZEJWT|KNVRGKWTLPZVPWbSNWaT|KNVRGKXTKOTKNGZVJMWS|KNVRGKZVJMUQNUQZMRVM|KNVRGKZVJMWTDGTPMQdZ|KNVRGKZVJMWTDGUQNUQZ|KNVSIMUQEIXTLPbXMRTO|KNVSIMXTEITPMRWTNWUE|KNVSIMXTFKTOKTWPNWbS|KNWSNWbSIMXTLPTOMQUR|KNWSNWbSLPebGLSOLSVO|KNWSNWbSLPebGLUQIMYU|KNWSNWbSLPebJMbWEJfb|KNWSNWbSLPebJMbWHLfb|KNWSNWbSLPebJMUQMRVM|KNWSNWbSLPfbJMbWMQSO|KNWTFKbWIMTPLOWSNWaT|KNWTFKbWJMTPMRVMIRWS|KNWTFKbWLPVSGLTOKTXO|KNWTFKTPBFbWJMfbNRUN|KNWTFKTPBFbWJMUQNRQJ|KNWTFKTPBFbWNRUNJbfW|KNWTFKTPBFUQNRVMIRXT|KNWTFKTPBFVRJMbWMVZJ|KNWTFKTPJMXTMRVMIRbX|KNWTFKUQBFTPNRVMIRbW|KNWTGKbWDGVSLOSLHOTP|KNWTGKbWJMVRMVZJENeb|KNWTGKTPLOVRJMPLMVZJ|KNWTJMTPMRVMIRXTEIUQ|KNWTJMTPMRVMIRXTFKbX|KNWTJMTPMRVMIRXTLOTK|KNWTJMVRMVaKGNbWEJTP|KNWTJMVRMVaKGNbWEJZV|KNWTJMVRMVaKGNeaIMZV|KNWTJMVRMVaKGNTPDGUR|KNWTLPbWNRUNJbfWEJVS|KNWTLPURNUYRPWbSJNRK|KNWTLPVRPWRKGNaTIMTP|KNWTLPVRPWRKGNbSNWaT|KNXTLPVSGKbXDGTOKTXO|KNXTLPVSGKbXDGUQNRSO|KNXTLPVSGKZVHLcZLOSL|KNXTLPVSIMbXEIUQGLTO|KNXTLPVSIMbXMQTOEIUR|KNXTLPVSIMbXMQTOGLUR|KNXTLPVSIMbXMRTOGKeb|KOUQFKZUBFURJMQJEUYR|KOUQGKWSJNSJENZUDGVR|KOUQGKWSJNSJENZUOTXO|KOUQGKWTLPYUPWbLHOfb|KOUQGKYULPWSJMQJEWbL|KOUQGKZULPWSHLbWDHUR|KOUQJNVSOVaKFOWTEJTK|KOUQJNVSOVaKGNYUEJZV|KOUQJNVSOVaKGNYUFKZV|KOUQJNWSNWaKFObWEJWT|KOURFKYUJNWTLPVSOMZV|KOURGKYUJNWSNWaTEJUQ|KOURGKYUJNWSNWaTLPUQ|KOURGKZUJNWSNWaTEJea|KOURGKZUJNWSNWbSOTXO|KOVRLPaVHLWSGKSNJSea|KOVRLPaVHLWSJNRTPNbW|KOWSGKaWIMURLPRIOTXO|KOWSJNSJFMUQMRVMIRZU|KOWSJNSJFMURMQbWGKWT|KOWTFKTPBFUQJNbWOSVO|KOWTFKTPBFURJMYUMQcY|KOWTGKTPDGbWOTXOLbfW|KOWTGKTPDGUQJNYUEJVR|KOWTGKTPKNPGCLbWFKWS|KOWTJMTKFOaWBFWTGKTP|KOWTJMTKFOaWGKWTBFTP|KOWTJMTKFOaWGKWTBFUQ|KOWTJMTKFOaWGKWTBFUR|KOWTJMTKFOaWLPeaHLWT|KOWTJMTKFOaWMRVMIRUN|KOWTJMTKFObWGKWTBFTP|KOWTJMTKFObWMRUNOSVO|KOWTJMTKFObWMRVMIRUN|KOWTJMTKFObWOSVOLbfW|KOWTJMTKFOUQMRVMIRZV|KOWTJMTKFOUREJbWGKZU|KOWTJMTKFOURGKbWMQWS|KOWTJMTKFOURGKbWMQWT|KOWTJMTKFOURMQbWGKWS|KOWTJMTKFOURMQbWGKWT|KOWTJMTKFOVRMVaREJUQ|KOWTJMTKGNVRMVaKFObW|KOWTOSVOLSTPGKXTKNbX|KOWTOSVOLSTPHLaVLOea|KOWTOSVOLSUQSWbSJMQJ|KOWTOSVOLSURJMaVGLVO|KOWTOSVOLSURJMYUMVaR|LOUQHLYULPVSOVZSIMaV|LOUQHLYULPVSOVZSJMQJ|LOUQJMQJFMWSHLYUMRUN|LOUQJMQJFMWTMRVMIRbW|LOUQJNWSNWbLGPfbEJbW|LOUQJNWSNWbLHOfbKNVR|LOUQJNWSNWbLHOfbKNZU|LOUQKNVSOVaKGNZVHLYU|LOURJMWSEJSLHObWJNfb|LOVRHLaVLPWSGLSNJSea|LOVRJMaVHLWTLPUQPWbL|LOVRJNWTFJTPJMZVMQcZ|LOWSGLbWKNUQFKZUBFUR|LOWSGLbWKNURNUYRJMRN|LOWSGLbWKNURNUYRJMWT|LOWSGLbWLPSLPGWSJMfb|LOWSGLbWLPSLPGXTHLTP|LOWSHLbWJMUQMRVMIRSN|LOWSHLSNJSXTOXVHIMbW|LOWSHLSNJSXTOXVHIMUR|LOWSHLSNJSXTOXVHIMZV|LOWSHLUQKNZUNWaKFObW|LOWSHLURJNSJEUYRLPbW|LOWSHLXTOXSNJSVHIMbW|LOWSJNSLHOUQEJbWOSVO|LOWSJNSLHOUQEJbWOTXO|LOWSJNSLHOUQOTXOKTbW|LOWTJMbWEJWSAESLGWaT|LOWTJMbWEJWSBESLGWaT|LOWTJMbWEJWSMQSLGWaT|LOWTJMbWHLTPMRUNKRVM|LOWTJMbWHLUQMRVMIRTP|LOWTJMbWMRUNKRTKGNVM|LOWTJMbWMRUNKRVMIRTK|LOWTJMbWMRVMIRUNKRTK|LOWTJMUQHLQJFMTPMQVR|LOWTJMUREJbWJNfbNUZJ|LOWTJMUREJbWMQTPOTXO|LOWTJNbWNRUNKRVMIRTK|LOWTJNbWNRVMIRUNKRTK|LOWTJNVRFJbWGLTPCFPG|LOWTJNVRFJTPJMUQNUQJ|LPUQGLYUDGcYJMQJFMWT|LPUQGLYUDGVRJNZVEJcY|LPUQHLWSKNbWFKZUKOUR|LPUQHLYUKOVRJMQJFVaR|LPUQHLYUKOWTPWaKFObW|LPUQIMWTPWaTEIbWAEZU|LPUQJNWTPWbJENXTHLTP|LPUQJNWTPWbJFMQJENYU|LPURHLZUKOWTPWaKFObW|LPURJNWSNWaTPWbSEJeb|LPURJNWSNWaTPWbSKNRK|LPURJNWSNWbSEJSOKTXO|LPVRHLZVLOWTPWbLGPfb|LPVRJMUQMVaREJZUJMQJ|LPVRJMZVMQVSQZdUEJSO|LPVSHLXTKOTKFVaRJMZV|LPVSHLXTKOTKFVZSGKSN|LPVSHLXTKOTKFVZSGKUR|LPVSIMSOKTXOJNbXGLOK|LPVSJMSOKTXOMQUREJbX|LPVSJNSJENURNUYRFJaV|LPVSJNSJENWTPWbJFMfb|LPVSKOSLHOWSOVZSGLaV|LPWSGLbWLOSLPGWSJNSJ|LPWSGLSOKTXOLSVOIMaV|LPWSGLSOKTXOLSVOJMbW|LPWSGLSOLSVOKTXOIMaV|LPWSGLSOLSVOKTXOIMZV|LPWSIMUQKNYUNWbSGLUR|LPWSIMUREISOKTXOGLYU|LPWSJMSOKTXOGKbXKTXO|LPWSJMSOKTXOMQbWEJfb|LPWSJMSOKTXOMQbWEJWT|LPWSJMSOKTXOMQUREJbW|LPWSJMSOKTXOMQUREJRM|LPWSJMSOKTXOMQURFJbW|LPWSJMUQEJZUKNbWFKUR|LPWSJMUQEJZUKNbWPTWP|LPWSJMUQEJZUKNcZNWbS|LPWSJNSJFMaWMQWTPWbS|LPWSJNSJFMXTPWbSHLfb|LPWSJNSJFMXTPWbSMQUR|LPWSKNbWGKURNUYRJNSJ|LPWSKNbWGLebFKVRLOSL|LPWSKNURNWbSGKfbDGbW|LPWSKOSLHObWFKebGLWT|LPWTPWaTJMTPEJXTJNbW|LPWTPWbSGLfbKOURJMZU|LPWTPWbSGLSOKTXOLSVO|LPWTPWbSIMfbEIbWHLWT|LPWTPWbSIMfbKNbWMRVM|LPWTPWbSIMfbMQSOKTXO|LPWTPWbSIMUQEIZUBEUR|LPWTPWbSIMUQEIZUHLeb|LPWTPWbSIMUREISOKTXO|LPWTPWbSIMXTKNTPNWaT|LPWTPWbSJMXTMQTPIMSO|LPWTPWbSJNSJENXTAEVR|LPWTPWbSKNaWGLXTFKTP|LPXTGLbXLOURHLZUDHcZ|LPXTKOTKGNVSFKaVHLbX|LPXTKOTKGNVSHLaVFKbX|LPXTKOTKGNVSHLaVFKUQ|LPXTKOTKGNVSHLaVLOSL|LPXTKOTKGNVSHLbXIMaV|JMVSEJUQKNZUMRXTLOTKFV|JMVSKOWTOVZSMQdZLOTKGd|JMVSMQWTKOTKFVaRBFbWFJ|JMVSMQWTKOTKFVaRLObWHL|JMVSMQWTKOTKFVZSQZcVIM|JMWSKOaWMQWTEJTKGWbSLP|JMWSLPSOKTXOMQbWEJfbJM|JMWTEJVSMQSNKRUEAJTPJN|JMWTFJUQBFVSLOSLGWbSDG|JNUQLOWTEJZUNSdZSWbLGd|JNUQNRVMIRWSEJSNJSZVSZ|JNVREJaVJMUQNUQJFMZJBF|JNVREJWTJMUQMVZJFMQJBE|JNVREJWTJMUQNUQJFMZJBE|JNVRFJaVJMWTMQTOLSVFBK|JNVRFJWTLOZVNScZIMRIKN|JNVRFJWTLOZVNSdZSWbLGd|JNVSEJaVLOSLHOWSNWbLGP|JNVSEJSOLSURNUWEAJYRHL|JNVSLOSJENWSOVZJFMbWMQ|JNWTEJbWAETPLOVSOVaRHL|JNWTEJTPJMUQNRQJFMbWAE|JNWTEJVRJMUQNUQJFMZJBE|JNWTLOVRFJbWJMfbMVZJEN|JNWTNRVMIRUNKRTOLSZURV|JNXTLPbXGLebLOWSNWbLPG|JNXTLPUQGLYULObXHLVSOV|LOWSHLSNJSXTOXVHIMaVMQ|LOWSHLSNJSXTOXVHIMbWEJ|LOWSHLSNJSXTOXVHIMbWMQ|LOWSHLSNJSXTOXVHIMZVMQ|LOWSHLSNKRUNJSXTOXVHEJ|LOWSHLSNKRUNJSXTOXVHFK|LOWSHLXTOXSNJSVHEJbWAE|LPWTPWaTJNTPEJUQGLPGCL|IMUQEIVSKOaVFKZUJNQJNEWT|IMUQEIVSKOaVFKZUKNURNUQZ|IMUQEIVSKOaVFKZUKNVROVRa|IMUQEIVSKOYUOVZSBEXTFKTP|IMUQEIWSMRVMIRbWAEfbLOSL|IMUQEIWTLPbWMRVMIRTOKTXO|IMUQEIWTMRVMIRZVAEVMEIcZ|IMUQEIYUAEVSKNaVGKeaLPXT|IMUQEIYUKNcYFKWTBEaWLPea|IMUQEIYUKNVRMVaKFOWTGKTP|IMUQEIYUKNVRMVaKFOWTGKZV|IMUQEIYUKNWSNWaTBEURFKZU|IMUQEIYUKNWSNWaTLOTKGNVS|IMUQEIYULOURGLZUDGcYLPWT|IMUQEIZUAEURKNRKGNVRMVaK|IMUQEIZUAEURKNRKGNVRNUQZ|IMUQEIZUAEVRMVaRLOWTJNcZ|IMUQEIZUAEVRMVaRLOWTJNda|IMUQEIZUAEVSLOSLHOURMVaR|IMUQKNVRMVaKGNZUDGURNUQZ|IMUQKNWSNWaTEIZUBEURFKYU|IMUQKNWSNWaTLOTKGNbWHLeb|IMUQKNWSNWaTLOTKGNbWHLWT|IMUQKNWSNWaTLOTKGNbWHLXT|IMUQKNWSNWbSFKYUJNQJNWaT|IMUQKNWTLPYUPWbSNWaTFKTO|IMUQKNWTNSVOLSaVGLVOLSea|IMUQKNXTLPbXEITOGKZUKTXO|IMUQKNXTLPbXEITOMRVMIROK|IMUQKNXTLPVSMRTOGKbXKTXO|IMUQKNXTNSVOLSWNJSQJENYU|IMUQKNXTNSWNJSVOLSQJENbX|IMUQKNYUNSWNJSQJENVOLSbW|IMUQLPWTPWaTEIZUHLTPKNbW|IMUQLPWTPWaTKOTKGNbWHLWT|IMUREIWSKObWFKWTLPSLPWaT|IMUREIWTJNbWNUZJFMfbAEdZ|IMUREIWTLObWAEZUMQWSQZdU|IMUREIWTLOTPAEbWOTXOKTZU|IMURMQRMJNMIEJWTLPYUPWaT|IMURMQRMJNMINRVMQJYUJNUQ|IMURMQRMJNMINRVMQJYULOUR|IMURMQRMLPWSEISOIRVMKTXO|IMURMQRMLPWSHLSOLSVOKTXO|IMURMQRMLPWTPWbSHLMIJNSJ|IMURMQRMLPWTPWbSJNSJENMI|IMVRMVaRLPZVGLWTPWbSKNRK|IMVSEIWTKOTKFVZSMQXTQZcV|IMVSKNXTMQaVEITPFKWTNWTa|IMVSKNXTMQbXFKaVJMSJMFTP|IMVSKNXTMQTPFKaVKObXGKPG|IMVSKNXTMQTPFKbXJMSJMFUR|IMVSMQWTKNTPNWbSJMfbFKbW|IMWSLPbWGLUQKNVRMOWTPWaR|IMWTMQTPJNbWEJWTAETOLSVO|IMWTMQTPJNbWNRUNKRVMQJaV|IMWTMRUNKRVMJQTPEJbWLOWT|IMXTLOUROXRIHLYULPUQGLZU|IMXTLOUROXRIJNYUHLUQLPcY|IMXTLOUROXRIJNYUHLUQLPWS|IMXTMQTPJNWSNWbSEJfbAEaW|IMXTMQTPKNVSFKbXJMSJMFUR|IMXTMRUNKRVMJQTPEJWTLOTK|IMXTMRUNKRVMJQWSLPTOEJYU|IMXTMRVMJQTPEJbXJNWTAEaV|JMUQEJWTAETOKTXOLSVOGLaW|JMUQEJWTLPTOKTXOMRVMIRbW|JMUQEJZUKOURFKWSLPSLHObW|JMUQFJWSLPZUJNSJMFURHLbW|JMUQFJWSLPZUJNSJMFURHLYU|JMUQFJYULPURHLZUDHWSJNSJ|JMUQLOQJFMWTEJbWBFTPMQWS|JMUQLOQJFMWTMRVMIRbWEJTP|JMUQLOQJFMYUMRUNKRVMIRWT|JMUQMRVMIRWSEJbWAEfbLOSL|JMUQMRVMIRWSEJbWBEfbLOSL|JMUQMRVMIRWSEJSOLSZVSZdE|JMUQMRVMIRWSLOSLHObWEJWT|JMUQMRVMIRWTEJbWAETPEIWT|JMUQMRVMIRWTEJbWLOZUJNdZ|JMUQMRVMIRWTEJZVAEVMEIcZ|JMUQMRVMIRWTKNbWFKTPLOZU|JMUQMRVMIRWTLOTPEJbWOTXO|JMUQMRVMIRZULOUNKRWTFKdZ|JMUREJWSKObWAEWTLPTKGWaT|JMUREJWSKObWFKWTLPSLPWaT|JMUREJWSKObWFKYUMQebJMWT|JMUREJWSKObWGKWTLPSLPWaT|JMUREJWSKORNAEbWFKZUKRUN|JMUREJWSKORNAEbWLPSLJbfW|JMUREJWTJNbWNUZJFMfbMQdZ|JMUREJWTLObWJNfbNUZJFMdZ|JMUREJWTLObWJNTPNUZJFMWT|JMUREJWTLObWMQTPJNWTNUYR|JMUREJWTLObWMQWSJMSLGWaT|JMUREJWTLPTOKTXOMQRMIRVM|JMURFJWSKOaWMQWTJMTKGWbS|JMURFJWSKObWMQebJMYUGKWT|JMURKNRKGNVSEJSOLSaVCGVO|JMURKNRKGNVSEJSOLSaVDGVO|JMURKNRKGNWTMRVMIRZUEJbW|JMURKOWTLPTKGUZJENXTPWbJ|JMURLOWTEJbWAEfbMQTPHLWS|JMURLOWTEJbWAEfbMQTPJNWT|JMURLOWTEJbWAEfbMQTPJNYU|JMURLOWTEJbWAEfbMQYUJNRM|JMURLOWTEJbWJNTPNUZJFMWT|JMURLOWTEJbWMQRMIRVMGLMI|JMURLOWTEJbWMQRMIRVMGLTP|JMURLOWTEJbWMQTPOTXOKTRM|JMURLOWTGLTPCGbWOTXOLbfW|JMURMQVSKOaVEJWTLPTKGWbS|JMVSEJWTLPTOKTXOGKUQKTbX|JMVSFJaVMQeaJNSJENURNUYR|JMVSFJWTMQSNKRUNJSTOSVZS|JMVSFJWTMQTOKTXOIMSNLSNW|JMVSKOaVFKUREJWTKNTKNWbS|JMVSKOaVMQeaEJWTJMTKGWaT|JMVSKOUQOVQJENaKFOYUGKWT|JMVSLPSOKTXOMQUREJaVGKea|JMVSMQaVIMUREIWTLPSNPWbS|JMVSMQaVIMWTMRUNKaeVEJYU|JMVSMQUREJRNKRSOLSWEAJZU|JMVSMQURKNRKFVaREJeaLOaV|JMVSMQURKOaVEJWTGKSNJSRM|JMVSMQURKOaVEJWTJMTKGWbS|JMVSMQURKOaVFKWTKNTKNWbS|JMVSMQURKOaVGKWTLPSLPGTO|JMVSMQURKOSNOSNKGUWNCGYR|JMVSMQURLPSOKTXOEJZUQZcV|JMVSMQWTEJTOKTXOJMURMVaR|JMVSMQWTKOTKFVaRLObWHLea|JMVSMQWTKOTKFVZSQZdUIMbW|JMVSMQWTLPTOKTXOEJURJMZV|JMWSEJaWKNeaMQSOLSVOJMWS|JMWSEJaWKNXTMRVMIRbXGKZV|JMWSEJaWMQeaJMWTMRUNKRVM|JMWSEJbWAEfbMRUNKRVMJQXT|JMWSEJbWAEWTMRUNKRVMJQTP|JMWSEJbWKOUQFKZUJNSJMFWS|JMWSEJbWKOUQGKZULPSLPGXT|JMWSEJSOKTXOLSVOMQbWAEfb|JMWSEJSOKTXOLSVOMQURGLRN|JMWSEJSOLSVOKTXOAEURMVaR|JMWSEJSOLSVOKTXOBEUQGLaV|JMWSEJSOLSVOKTXOBEZVMRVM|JMWSEJSOLSVOKTXOGLaWLSWE|JMWSEJSOLSVOKTXOMQURJMaV|JMWSEJURKOaWFKWTKNTKNWbS|JMWSEJURKOYUMQcYJMbWFKRN|JMWSFJbWMQWTJNSJENTOLSVF|JMWSFJbWMQWTJNSJENTPNRUN|JMWSFJUQJNSJMFbWIMQJFMWS|JMWSKOaWFKUQMRVMIRWTOVZS|JMWSKOaWFKWTEJbWBFUQMRVM|JMWSKOaWFKWTMRUNKaTKGWbS|JMWSKOaWGKWTEJTPDGURMQZU|JMWSKOaWGKWTLPSLPGTOKTXO|JMWSKOaWMQeaEJWTJMTKGWaT|JMWSKOaWMQUREJWTJMTKGWbS|JMWSKOaWMQWTEJTKGWbSLPfb|JMWSKOaWMQWTEJTKGWbSLPUR|JMWSKOaWMQWTEJTKGWbSLPVR|JMWSKOaWMQWTFKTPEJURJMbW|JMWSKOaWMQWTGKTPDGUREJYU|JMWSKOaWMQWTGKURLPSLPGTO|JMWSKOaWMQWTLPTKGWbSEJfb|JMWSKOaWMQWTLPTKGWbSEJUR|JMWSKObWEJUQFKZUJNSJMFUR|JMWSKObWEJUQGKZULPSLPGXT|JMWSKObWEJUQMRVMOVaRJNRK|JMWSKObWEJURFKWTLPSLPWaT|JMWSKObWEJURFKYUMQcYJMRN|JMWSKObWFKUQBFQJFMfbMQYU|JMWSKObWFKUQBFQJFMYUMQfb|JMWSKObWFKUQBFQJFMYUMRUN|JMWSKObWFKUQEJZUJNSJMFUR|JMWSKObWFKUQMRVMIRSNRUYR|JMWSKObWFKUQMRVMIRSNRVaR|JMWSKObWFKUREJWTLPSLPWaT|JMWSKObWFKUREJYUMQcYJMRN|JMWSKObWFKUREJYUMQcYJNSJ|JMWSKObWFKUREJZUMQRMIRVF|JMWSKObWFKWTLPSLPWaTGWea|JMWSKObWGKUQLPSLPGQJFMWS|JMWSKObWMQWTEJTKGWaTLPea|JMWSKObWMQWTLPTKGWaTPWeb|JMWSKOUQEJZUGKaWKNVRMVSZ|JMWSKOUQGKQJEWaTAETPDGYU|JMWSKOUQGKQJEWaTAEYUEJUR|JMWSKOUQGKQJEWaTIMTPCGVS|JMWSKOUQGKQJEWaTIMTPDGda|JMWSKOUQGKQJEWaTIMZUOSVO|JMWSKOUQGKQJEWaTLPYUPWbL|JMWSKOUQGKQJEWbSIMaWAEWT|JMWSKOUQGKQJEWbSIMaWAEYU|JMWSKOUQGKQJEWbSIMaWMQWT|JMWSKOUQGKQJEWbSIMYUMQaW|JMWSKOUREJaWFKWTKNTKNWbS|JMWSLOSLHOUREJaWAEWSGLbW|JMWSLOSLHOUREJaWJNWSNWbL|JMWSLOSLHOVRMVZLGPXTPWbS|JMWSLPSOKTXOMQaWEJWTPWbS|JMWSLPSOKTXOMQbWEJfbJMbX|JMWSLPSOKTXOMQbWEJfbJMVR|JMWSLPSOKTXOMQbWEJWTPWaT|JMWSLPSOKTXOMQUREJaWJMbX|JMWSLPSOKTXOMQUREJbWJMfb|JMWSLPSOKTXOMQUREJbWJMYU|JMWSLPSOKTXOMQUREJRMIRVM|JMWSMRUNKRVMIRbWLOSLHOfb|JMWSMRUNKRVMIRbWLOSLHOWT|JMWSMRUNKRVMIRZUFKUNKRXT|JMWTEJbWAETPMQWSLOSLHOfb|JMWTEJbWJNfbMRVMIRTPAEUQ|JMWTEJbWJNURNUZJFMVSLOSL|JMWTEJbWLOfbMQTPOTXOKTUR|JMWTEJbWMQURLOTPJNWTNUYR|JMWTEJbWMQWSAESOLSVOGLaV|JMWTEJbWMQWSLPSOPWaTAETP|JMWTEJTOKTXOLSVOMQbWGLWS|JMWTEJTOKTXOLSVOMQbWJMfb|JMWTEJTOKTXOLSVOMQbWJNUR|JMWTEJTOLSVOKTXOBEURMVaR|JMWTEJTOLSVOKTXOBEZVMRVM|JMWTEJTOLSVOKTXOMQbWAEfb|JMWTEJTPAEURKOaWOTXOLSWN|JMWTEJTPLObWOTXOKTWSTXUR|JMWTEJTPMQbWJNVSFJaVJMSJ|JMWTEJTPMQbWLOWSAESLHOfb|JMWTEJTPMQXTLObXJNURNUYR|JMWTEJUQMRVMIRTPLObWJNWT|JMWTFJUQLPZUPWaTCFURKNRK|JMWTFJUQLPZUPWaTCFVSMRUN|JMWTFJUQLPZUPWaTKNURNUYR|JMWTKNaWNSWNMRVMIKeaEJTP|JMWTKNaWNSWNMRVMIKTPEJUQ|JMWTKNTOLSVOEJbWGLfbLSUR|JMWTKNTOLSVOEJURNUYRMVZS|JMWTKNTPMQXTEJaWAEWSNWTa|JMWTKNVRMVaKGNbWEJTPIMPG|JMWTLObWEJfbAETPMRVMJQWT|JMWTLObWEJTPMQURJNfbNUYR|JMWTLObWEJTPMQWSAESLHOfb|JMWTLObWEJWSAESLGWaTHLTP|JMWTLObWEJWSAESLGWaTHLUR|JMWTLObWEJWSMQSLGWaTJNUR|JMWTLObWMQWSEJSLGWaTHLUR|JMWTLObWMRUNKRVMIRTKGNZU|JMWTLObWMRVMIRUNKRTKGNeb|JMWTLOUREJbWJNTPNUZJFMWT|JMWTLPTOKTXOMQbWFJWTPWaT|JMWTLPTOKTXOMQUREJRMIRVM|JMWTLPUQPWQJENbJFMfbHLYU|JMWTLPUQPWQJENbJFMXTAEfb|JMWTMQTPEJXTJMTOLSVOKTPW|JMWTMRUNKRVMIRTOLSZURVaR|JMWTMRUNKRVMIRZUFKUNKRTP|JMWTMRVMIRUNKRaWFKWSRVSN|JMWTMRVMIRUNKRTOLSZURVaR|JMWTMRVMIRUNKRTPEJbWAEWT|JMXTLObXEJfbMQTPJNURNUYR|JMXTLPbXMQTOKTXOGKWTPWaT|JMXTLPbXMQVSKNSJENURNUYR|JMXTLPUQGLQJFMbXEJVSMQeb|JMXTLPUQHLQJFMVSMQSNKRTO|JMXTLPUQMRVMIRZURVaRKNRK|JMXTLPVSHLbXDHebKOTDMRUN|JMXTLPVSMQaVEJeaJNSJFMVS|JNUQEJWSNWbSKOZUJNSJFMQJ|JNUQEJWTAETPLObWNSWNKRVM|JNUQEJWTAETPLOVRNUYRJNZV|JNUQEJWTLPbWGLZULOURNUQZ|JNUQEJWTNRVMIRbWLOfbAETP|JNUQEJYUAEVRIMRINSWNKYbW|JNUQEJZUAEWTLOVROSaWGLTP|JNUQEJZUAEWTLPQMJSaVPWVO|JNUQEJZULPURNUQZIMYUMQWS|JNUQEJZULPVRGLRMIRWTPWbS|JNUQKOWTGKQMIRVMEIZVIRVM|JNUQKOWTNRTKGNVMIRbWFKWT|JNUQLOWSNWbLHOYUOTXOKTUR|JNUQLOWTEJbWAETPNRVMIRWT|JNUQLOWTEJZUNScZKNTRBEVO|JNUQLOWTEJZUNSVRJNcZSWbL|JNUQLOZUEJWTNSVRJNTPAEcZ|JNUQLPVSEJSOKTXOAEWSNWbS|JNUQNRVMIRWSEJbWAEfbLOSL|JNUQNRVMIRWSEJbWBEfbLOSL|JNUQNRVMIRWSEJbWBEZULOSL|JNUQNRVMIRWSEJbWLOSLHOWS|JNUQNRVMIRWSEJSNJSZVSZcM|JNUQNRVMIRWSEJSOLSaVRadE|JNUQNRVMIRWSLOSLHObWGLWT|JNUQNRVMIRWSLOSLHObWGLZU|JNUQNRVMIRWSLOSLHObWKNfb|JNUQNRVMIRWSLOSLHObWKNWT|JNUQNRVMIRWTEJbWLOaVRaeV|JNUQNRVMIRWTEJbWLOfbAEaV|JNUQNRVMIRWTEJbWLOTPAEWT|JNUQNRVMIRWTEJbWLOTPJNWT|JNUQNRVMIRWTEJbWLOTPOTXO|JNUQNRVMIRWTEJbWLOZVBEVM|JNUQNRVMIRWTEJTPAEbWEIfb|JNUQNRVMIRWTEJTPAEbWJNZU|JNUQNRVMIRWTEJTPLObWJNZU|JNUQNRVMIRWTEJZVAEVMEIcZ|JNUQNRVMIRWTEJZVJMQJFMVS|JNUQNRVMIRWTKNTPFKXTLObX|JNUQNRVMIRWTKNZUFKcZLObW|JNUQNRVMIRWTLObWEJfbJNTP|JNUQNRVMIRWTLObWEJTPJNWS|JNUQNRVMIRWTLObWEJTPJNWT|JNUQNRVMIRWTLObWEJTPOTXO|JNUQNRVMIRWTLObWEJZVJMQJ|JNUQNRVMIRWTLObWKNTKFOWT|JNUQNRVMIRWTLOTPEJbWJNWT|JNUQNRVMIRWTLOTPHLbWEJfb|JNUQNRVMIRWTLOTPHLbWEJWT|JNUQNRVMIRWTLOZUHLUNKRTK|JNUQNRVMIRZUKNdZLOWTFJTK|JNUQNRVMIRZUKNdZLOZVEIVM|JNUQNRVMIRZUKNWTFKTPLObW|JNUQNRVMIRZULOUNKRdZFKZU|JNUQNRVMIRZULOUNKRWTHLTK|JNUQNRVMIRZVEIVMIRWTKNbW|JNUQNRVMIRZVEIVMIRWTKNdZ|JNUQNSWNKRVMIRZVEIVMIRcZ|JNURNUYREJWSKObWJMWTMQTK|JNURNUYREJWTAETPJNRMIRVM|JNURNUYREJWTJMTOLSVOKTXO|JNURNUYREJWTJMTPLObWOTXO|JNURNUYREJWTJNRMIRVMAEMI|JNURNUYREJWTJNRMIRVMAETP|JNURNUYREJWTLObWJMfbMQTP|JNURNUYREJWTLObWJMTPAEfb|JNURNUYREJWTLOTPAEbWJNWT|JNURNUYREJWTLOTPJMbWOTXO|JNURNUYREJWTLOTPJNbWNUZQ|JNURNUYREJWTLPTOKTXOJMVS|JNURNUZQEJWSKObWGKYUBEeb|JNURNUZQEJWSKOYUJNSJFMQJ|JNURNUZQKNVRNUQZEJaVIMYU|JNURNUZQKNVRNUQZFKaVEJWS|JNURNUZQLOWSGLYUOTXOKTbX|JNURNUZQLPWSPTXOKTYUTWaT|JNVREJaVBEWTJMTPLOUQNUYR|JNVREJaVJMUQNUQJFMZJBFVS|JNVREJaVJMXTMQbXLOfbGLTP|JNVREJaVJMXTMQTPFJWTJMbX|JNVREJaVJMXTMQTPFJWTLOda|JNVREJaVJMXTMQTPLOWSNWbL|JNVREJaVLOWTBETPJMUQNUYR|JNVREJaVLOWTBEUQNUYRJMQJ|JNVREJaVLOWTHLTPDHUQNUYR|JNVREJaVLOWTJMUQNUQJFMZJ|JNVREJaVLPeaGLVSLOSLPGXT|JNVREJaVLPVSGLZVLOSLPGea|JNVREJaVLPVSGLZVLOSLPGUQ|JNVREJaVLPVSGLZVLOSLPGVS|JNVREJaVLPXTHLbXLOWSNWTa|JNVREJWTBEbWJMTPMVZJFMWT|JNVREJWTBEZVJMbWMQcZLOTP|JNVREJWTJMaWMVZJFMWSLOSL|JNVREJWTJMaWMVZJFMWSMQTO|JNVREJWTJMaWMVZJFMWSMRUN|JNVREJWTJMUQMVZJFMQJBEYU|JNVREJWTJMUQMVZJFMQJBFYU|JNVREJWTJMUQNUQJFMZJBEJF|JNVREJWTJMUQNUQJFMZJBFYU|JNVREJWTLObWBETPJMWTMVZL|JNVREJWTLObWJMUQMVZJFMQJ|JNVREJXTBETOLSaVJMVOKaRB|JNVREJXTJMUQNUQJFMZJBEaV|JNVREJXTLOTPBEaVHLWSNWbS|JNVREJXTLOTPBEaVJMVSMVSL|JNVREJXTLOTPJMWSNWbLMVaR|JNVREJXTLOTPOTbXJMXOMVZJ|JNVREJXTLOTPOTZVJMUQNUQZ|JNVREJXTLPaVHLbXLOWSNWTa|JNVREJXTLPaVHLbXLOWSPWSb|JNVREJXTLPbXGLZVLOUQNUQZ|JNVREJXTLPbXHLaVJMWSNWTa|JNVREJXTLPbXHLZVJMUQNUQZ|JNVREJXTLPZVGLbXJMUQNUQZ|JNVREJXTLPZVJMUQNUQZMRVM|JNVREJZVJMUQNUQJFMYRAEWS|JNVREJZVJMUQNUQZAEVSLOSL|JNVREJZVJMUQNUQZAEWSEJaW|JNVREJZVJMUQNUQZAEWSEJSO|JNVREJZVJMUQNUQZAEWSEJYU|JNVREJZVJMUQNUQZAEWTEJbW|JNVREJZVJMUQNUQZAEWTEJTP|JNVREJZVJMUQNUQZAEWTMRVM|JNVREJZVJMUQNUQZAEXTLObX|JNVREJZVJMUQNUQZAEXTMQTO|JNVREJZVJMUQNUQZAEYUMQWS|JNVREJZVJMUQNUQZAEYUMRUN|JNVREJZVJMUQNUQZFJWSAEYU|JNVREJZVJMUQNUQZFJWSBFYU|JNVREJZVJMUQNUQZKNVRNUZJ|JNVREJZVJMUQNUQZKNVSFJXT|JNVREJZVJMUQNUQZKNWSNWbS|JNVREJZVJMUQNUQZKNXTMQTO|JNVREJZVJMUQNUQZKNXTMRVM|JNVREJZVJMUQNUQZLOWSGLbW|JNVREJZVJMUQNUQZLOWSGLYU|JNVREJZVJMUQNUQZLOWSHLYU|JNVREJZVJMUQNUQZLOWTAEbW|JNVREJZVJMUQNUQZMQWSAEYU|JNVREJZVJMUQNUQZMQWTFJTO|JNVREJZVJMUQNUQZMQWTKNTO|JNVREJZVJMUQNUQZMRVMIRWS|JNVREJZVJMUQNUQZMRVMIRXT|JNVREJZVLOUQNUQZAEWSGLYU|JNVREJZVLOWTNScZIMRIKNTR|JNVREJZVLOWTNSUQSZdUAEcZ|JNVREJZVLOWTNSUQSZdUAETP|JNVREJZVLOWTNSUQSZdUIMRI|JNVREJZVLPUQNUQZHLWSKOYU|JNVRFJaVJMUQNUQJENYRNUZQ|JNVRFJaVJMWSNWbSKOebMQda|JNVRFJaVJMWTMQTOLSVFBKbW|JNVRFJaVJMWTMQTOLSVFBKXT|JNVRFJaVLPXTGLbXLOWSNWTa|JNVRFJWSNWbSJMRNKRUNBFXT|JNVRFJWSNWbSJMSNMVaRBFXT|JNVRFJWTJMaVMQTOLSVFBKbW|JNVRFJWTJMaVMQTOLSVFBKXT|JNVRFJWTJMTPMVZJENUQAEbW|JNVRFJWTJMTPMVZJENUQLObW|JNVRFJWTJMZVMQcZLOTPBFbW|JNVRFJWTJMZVMQcZLOTPCFbW|JNVRFJWTJMZVMQcZLOTPGLPG|JNVRFJWTJMZVMQcZLOTPHLbW|JNVRFJWTLObWJMTPMVZJENUQ|JNVRFJWTLOTPJMbWMVZJENWT|JNVRFJWTLOZVNScZIMRIKNTR|JNVRFJWTLOZVNSUQSZcVJMQJ|JNVRFJWTLOZVNSUQSZdUIMRI|JNVRFJWTLOZVNSUQSZdUJNcZ|JNVRFJWTLOZVNSUQSZdUKNTK|JNVRFJZVJMUQNUQZEJWTLObW|JNVRFJZVJMUQNUQZMQWSKOaW|JNVRFJZVJMUQNUQZMRVMIRWS|JNVRFJZVJMUQNUQZMRVMIRWT|JNVRFJZVJMUQNUQZMRVMIRXT|JNVRFJZVJMUQNUQZMRVMIRZU|JNVRFJZVJMWTMQcZLObWHLTP|JNVRFJZVJMWTMQcZLOTPBFbW|JNVRFJZVJMWTMQcZLOTPGLPG|JNVRLOWTFJbWJMTPMVZJENUQ|JNVRLOZVEJWTNSUQSZdUAETP|JNVRLPWTPWbJFVaREJZVHLfb|JNVRLPXTGLbXEJaVLOWSPWSb|JNVRLPZVGLRMIRVMEIcZIRWT|JNVRLPZVHLUQNUQZIMWSKOSN|JNVRLPZVHLUQNUQZIMWSMQYU|JNVRLPZVHLUQNUQZIMWTPWbS|JNVRLPZVHLUQNUQZIMYUMQWS|JNVRLPZVHLVSDHSJFVaREJea|JNVRLPZVHLVSDHSJFVaREJUQ|JNVSEJaVAEVRLPRMIRSOKaeM|JNVSEJaVKOdaOTXOGKbXKTWG|JNVSEJaVKOeaFKURNUYRIMRI|JNVSEJaVKOeaGKURNUYRLPSL|JNVSEJaVKOUQFKZUJMQJNEUR|JNVSEJaVKOUQFKZUJMQJNEWT|JNVSEJaVKOUQGKZUBEURNUQZ|JNVSEJaVKOUQGKZUBEURNUYR|JNVSEJaVKOUQGKZUDGURNUQZ|JNVSEJaVKOUQGKZUDGURNUYR|JNVSEJaVKOUQGKZULPSLPGVR|JNVSEJaVKOURNUYRJMeaAEWT|JNVSEJaVKOURNUYRJMZUGKSN|JNVSEJaVKOURNUYRJMZUMQWT|JNVSEJaVKOURNUZQGKYUBEea|JNVSEJaVKOURNUZQGKYULPSL|JNVSEJaVLPUQGLZUKOURNUQZ|JNVSEJaVLPVRGLZVLOSLPGUQ|JNVSEJaVLPVRGLZVLOSLPGVS|JNVSEJUQAEZVIMdZKOZUOTXO|JNVSEJUQAEZVIMYUEIURNUQZ|JNVSEJUQKOYUOVaKFOWTGKZV|JNVSEJURNUYRKORNOVaRJSWN|JNVSEJZVKOUQGKYUBEcYDGUR|JNVSEJZVKOUQGKYUBEURNUQZ|JNVSEJZVKOUQGKYUDGURNUQZ|JNVSEJZVKOUQNRVMIRXTOXSO|JNVSEJZVKOURNUYRJMcZGKWT|JNVSEJZVKOURNUYRJMcZMQZU|JNVSFJaVKOUQGKZUDGURNUQZ|JNVSFJaVKOURNUYRBFWTFKSN|JNVSFJaVKOURNUYRJMRNMQWT|JNVSFJaVKOURNUYRJMZUEJWT|JNVSFJaVKOURNUYRJMZUGKWT|JNVSFJaVLPXTCFUQGLZULOSL|JNVSFJZVKOUQGKYULPSLPGXT|JNVSFJZVKOURNUYRJMRNEJNE|JNVSFJZVKOURNUYRJMRNMQcZ|JNVSLOSJENUQAEWSNWbLHOfb|JNVSLOSJFMWTMQbWEJTPJMWT|JNVSLOSJFMWTMRUNKRTKGNXT|JNVSLOSLHOUQNRWTIMQJFMbW|JNVSLOSLHOURNUYREJaVJNWS|JNVSLPSJFMWSGLaVLOSLPGXT|JNVSLPSJFMWSHLaVKObWMQUR|JNVSLPSJFMWSHLUQEJaVKObW|JNVSLPSJFMWSHLUQEJaVKOZU|JNVSLPSJFMWTPWbSEJfbMQSO|JNVSLPSJFMWTPWbSEJXTMQSO|JNWSNWaTEJUQAEZUJNURNUQZ|JNWSNWaTIMUREITPLObWOTXO|JNWSNWaTKNbWFKTPNRVMIRUN|JNWSNWaTKNbWFKVREJTPLOZV|JNWSNWaTLOdaEJbWJMUQMRVM|JNWSNWaTLOeaFJbWJNURNUYR|JNWSNWbSEJfbKObWGKURLPSL|JNWSNWbSEJUQKOZUJNSJFMQJ|JNWSNWbSIMaWMQWTKNSJENfb|JNWSNWbSIMebMQSOLSVOKTXO|JNWSNWbSIMfbMQbWEIURAEZU|JNWSNWbSLOSLHOfbEJVRJNUQ|JNWTEJaWBETPNRVMJQUREJXT|JNWTEJaWLOdaGLTPAEPGCLVS|JNWTEJaWLPeaAEVRJMUQMeQM|JNWTEJaWLPeaAEVRJMZVEJUQ|JNWTEJbWAEUQNSVOLbfWHLTP|JNWTEJbWAEVRLPaVGLWSPWSb|JNWTEJbWJMebMRVMIRTPAEUQ|JNWTEJbWJMfbFJUQNRTPBEWS|JNWTEJbWJMfbMQTOKTXOLSVO|JNWTEJbWJMfbMRVMIRTPAEUQ|JNWTEJbWJMfbMRVMIRTPAEWT|JNWTEJbWJMfbMRVMIRTPLOWT|JNWTEJbWJMTPMQURNUYRAEfb|JNWTEJbWJMTPNRUNKRWSMQVM|JNWTEJbWJMTPNRUNKRZUFKUN|JNWTEJbWJMUQNRQJFMfbLOZU|JNWTEJbWJMUQNRQJFMfbMQVM|JNWTEJbWJMURNUZJFMfbAEdZ|JNWTEJTOKTXOLSVOAEURNUYR|JNWTEJTOKTXOLSVOIMOKFOUR|JNWTEJTOLSVOKTXOAEURNUYR|JNWTEJTPBEbWJMUQNRQJFMWT|JNWTEJTPJMbWBEUQNRQJFMWT|JNWTEJTPJMbWMQURNUYRAEfb|JNWTEJTPJMbWMQURNUYRLOfb|JNWTEJTPJMbWMQWTLOURNUYR|JNWTEJTPJMbWMRVMIRfbLOWT|JNWTEJTPJMbWNRUNKRWSAEfb|JNWTEJTPJMbWNRUNKRWSMQVM|JNWTEJTPJMbWNRUNKRZUFKUN|JNWTEJTPJMbWNRUNKRZULOUN|JNWTEJTPJMUQNRQJFMbWAEWT|JNWTEJTPJMUQNRQJFMbWBFWT|JNWTEJTPJMUQNRQJFMbWMQVM|JNWTEJTPJMVSNWbSMQfbFJbW|JNWTEJTPJMXTMQTOKTPWGKbX|JNWTEJTPJMXTMQTOLSVOKTPW|JNWTEJTPJMXTMRVMIRZVAEVM|JNWTEJTPJMXTNRUNKRTOLSVO|JNWTEJTPJMXTNRUNKRZUFKUN|JNWTEJTPLOVRBEbWJMWTMVZJ|JNWTEJTPLOVRBEbWJMWTMVZL|JNWTEJTPLOVRJMUQMVZJFMQJ|JNWTEJUQAETPLObWNSWNKRVM|JNWTEJURNUZQAEYUJNVREJTP|JNWTEJVRBEbWJMTPMVZJFMUQ|JNWTEJVRJMUQMVZJFMQJBEYU|JNWTEJVRJMUQMVZJFMQJKOTK|JNWTEJVRJMUQNUQJFMZJBEYU|JNWTEJVRLObWBEaVJMVSMVSL|JNWTFJTPBFbWJMWTNRUNKRVS|JNWTFJTPBFVRJMZVMQcZLObW|JNWTFJTPJMXTMRVMIRbXLOZV|JNWTFJUQBFTPLObWOTXOKTfb|JNWTFJVRJMZVMQcZLOTPCFbW|JNWTLObWHLTPNRUNKRVMIRfb|JNWTLObWHLTPNRUNKRVMIRWT|JNWTLObWHLUQNRVMIRTPEJWT|JNWTLObWHLUQNSWNKRVMIRTK|JNWTLObWNRUNKRVMIRTKGNfb|JNWTLObWNRUNKRVMIRTKGNXT|JNWTLOVREJaVBEbWJMUQNUQJ|JNWTLOVREJbWJMUQNUQJFMZJ|JNWTLOVREJTPJMUQMVZJFMQJ|JNWTLOVREJTPJMUQNUQJFMZJ|JNWTLOVRFJbWJMfbMVZJENUR|JNWTLOVRFJbWJMTPMVZJENUQ|JNWTLPUQPWbJENXTAEfbHLTP|JNWTLPUQPWbJENXTAETPHLYU|JNWTLPUQPWbJENXTAETPKOfb|JNWTLPUQPWbJENXTAEYUHLTP|JNWTLPUQPWbJENXTHLTPAEfb|JNWTLPUQPWbJENXTHLTPAEYU|JNWTLPUQPWbJENXTHLTPFJfb|JNWTLPUQPWbJENXTHLTPLOfb|JNWTLPUQPWbJENXTHLTPLOYU|JNWTLPUQPWbJFMQJENYUAEVR|JNWTLPUQPWbJFMQJENYUHLfb|JNWTNRUNKRVMIRaWFKdaLOaV|JNWTNRUNKRVMIRaWGKTPLOPL|JNWTNRUNKRVMIRaWLOTKFOWT|JNWTNRUNKRVMIRTOLSZURVaR|JNWTNRUNKRVMIRTPEJbWAEfb|JNWTNRUNKRVMIRTPEJbWAEWT|JNWTNRUNKRVMIRTPEJZUJNdZ|JNWTNRUNKRVMIRTPLObWEJWT|JNWTNRUNKRVMIRTPLObWHLWT|JNWTNRUNKRVMIRZVEIVMIRdZ|JNWTNRVMIRUNKRTOLSZURVaR|JNWTNRVMIRUNKRTPFKbWEIWS|JNWTNRVMIRUNKRZUFKUNKRaW|JNWTNSVOLSaVKOTKFObWSbfW|JNXTEJbXJMVSMQSJFMTPAEfb|JNXTEJTOLSVOKTWPAEaVHLbX|JNXTEJTPJMWSNWbSMQfbAEaW|JNXTEJTPJMWSNWbSMQSOKTPW|JNXTEJTPLOUQOTZUTXVRHLaV|JNXTLObXHLfbLPVSOVZJENTO|JNXTLObXHLTPNRUNKRVMIRfb|JNXTLObXHLTPNRUNKRVMIRWS|JNXTLObXHLTPNRUNKRVMIRWT|JNXTLObXHLUQNRVMIRTPEJWT|JNXTLObXHLUQNSWNKRTKGNVM|JNXTLObXHLUQNSWNKRVMIRTK|JNXTLObXNRUNKRVMIRTKFOWS|JNXTLObXNRUNKRVMIRTKGNfb|JNXTLObXNRUNKRVMIRTKGNXT|JNXTLObXNRVMIRUNKRTKGNfb|JNXTLOTPOTVSTXSJENWSNWbS|JNXTLPbXGLVRLOaVHLWSNWTa|JNXTLPbXGLVRLOaVHLWSPWSb|JNXTLPbXGLVSDGSJENURNUYR|JNXTLPbXGLVSDGSJFMUQBFQJ|JNXTLPbXGLVSLOSLPGTOKTXO|JNXTLPbXHLVSDHSJENUQAEZU|JNXTLPbXHLVSDHSJENURNUYR|JNXTLPbXHLVSDHSJFMURMVaR|JNXTLPbXNRUNKRVMIRebEJZU|JNXTLPbXNRUNKRVMIRTOEJeb|JNXTLPbXNRUNKRVMIRZVEIVM|JNXTLPbXNRUNKRVMIRZVEJVM|JNXTLPbXNRVMIRUNKRZVEIVM|JNXTLPUQEJVSAEbXIMZUEIaV|JNXTLPUQEJZUGLbXLOURNUQZ|JNXTLPUQEJZUGLVRLObXHLaV|JNXTLPUQEJZUHLVSBEaVDHbX|JNXTLPUQFJVSGLbXLOSLPGTO|JNXTLPUQGLbXLOZUHLVRIMQS|JNXTLPUQGLYULObXHLVSOVZJ|JNXTLPUQGLZUDGbXEJURNUQZ|JNXTLPUQGLZULObXEJURNUQZ|JNXTLPUQGLZULObXHLURNUQZ|JNXTLPUQGLZULObXHLURNUYR|JNXTLPUQGLZULObXHLVRIMQS|JNXTLPUQHLVSDHSJFMQJENZU|JNXTLPUQHLVSEJbXDHYUIMZV|JNXTLPUQHLZULObXNSWNPWaT|JNXTLPUQNRVMIRaVRaeVKNVS|JNXTLPUQNRVMIRZUEIUNKRQM|JNXTLPUQNRVMIRZUKNTOGKbX|JNXTLPUQNRVMIRZUKNTOGLWS|JNXTLPUQNRVMIRZURVaRKNRK|JNXTLPVREJaVHLbXLOWSPWSb|JNXTLPVREJbXGLZVLOUQNUQZ|JNXTLPVREJbXHLaVLOWSPWSL|JNXTLPVREJbXJMTOMVZJKTXO|JNXTLPVRFJbXJMTOMVZJENOF|JNXTLPVRGLaVLObXEJWSPWSb|JNXTLPVRGLaVLObXHLWSPWSb|JNXTLPVRGLbXEJaVAEWSNWTa|JNXTLPVRHLaVEJbXJMWSNWTa|JNXTLPVSEJUQGLbXLOSLPGTP|JNXTLPVSGLSJFMbXLOUQBFQJ|JNXTLPVSHLSJENZVAETOLQWT|JNXTLPVSHLSJENZVLObXFJUQ|JNXTNRUNKRVMIRZULOTKGNaV|KNVRFKWSNWbSJMRNKRUNLOSL|KNVRFKWTJMaVEJTOLSVFBKda|KNVRFKWTJMTPMVZJENUQLObW|KNVRGKZVJMUQNUQZMRVMIRWS|KNVRGKZVJMUQNUQZMRVMIRWT|KNVRGKZVJMWTDGTPMQdZLObW|KNVRGKZVJMWTDGUQNUQZMRVM|KNVSIMUQEIXTLPbXMRTOGKeb|KNVSIMXTEITPMRWTNWUEAJbS|KNVSIMXTFKTOKTWPNWbSMQUR|KNWSNWbSIMXTLPTOMQUREIRM|KNWSNWbSIMXTLPTOMQUREIRN|KNWSNWbSLPebGLSOLSVOPTOK|KNWSNWbSLPebGLUQIMYUFKUR|KNWSNWbSLPebJMbWEJfbMQXT|KNWSNWbSLPebJMbWHLfbMQSO|KNWSNWbSLPebJMUQMRVMIRbW|KNWSNWbSLPfbJMbWMQSOEJWT|KNWTFKbWJMTPMRVMIRWSNWUN|KNWTFKbWLPVSGLTOKTXOPTWG|KNWTFKTPBFbWJMfbNRUNKRWT|KNWTFKTPBFbWJMUQNRQJENVM|KNWTFKTPBFbWNRUNJbfWIMYU|KNWTFKTPBFUQNRVMIRXTJMQJ|KNWTFKTPBFVRJMbWMVZJENUQ|KNWTFKTPJMXTMRVMIRbXEIaW|KNWTGKbWDGVSLOSLHOTPNRUN|KNWTGKbWJMVRMVZJENebAEUQ|KNWTGKTPLOVRJMPLMVZJFMLS|KNWTJMTPMRVMIRXTEIUQAEZU|KNWTJMTPMRVMIRXTFKbXLOZV|KNWTJMTPMRVMIRXTLOTKFObX|KNWTJMVRMVaKGNbWEJTPAEPG|KNWTJMVRMVaKGNbWEJZVAETP|KNWTJMVRMVaKGNeaIMZVEIUR|KNWTJMVRMVaKGNTPDGURNUYR|KNWTLPURNUYRPWbSJNRKGWaT|KNWTLPVRPWRKGNaTIMTPFKXT|KNWTLPVRPWRKGNbSNWaTJNTO|KNXTLPVSGKbXDGTOKTXOGKfb|KNXTLPVSGKbXDGUQNRSOJNZU|KNXTLPVSGKZVHLcZLOSLPGTO|KNXTLPVSIMbXMQTOEIURNUYR|KNXTLPVSIMbXMRTOGKebKTXO|KOUQGKWSJNSJENZUDGVRIMQS|KOUQGKWSJNSJENZUOTXOLZcV|KOUQGKWTLPYUPWbLHOfbDGbW|KOUQGKYULPWSJMQJEWbLPGfb|KOUQJNVSOVaKFOWTEJTKGNbW|KOUQJNVSOVaKGNYUEJZVBEVR|KOUQJNVSOVaKGNYUFKZVDGVR|KOUQJNWSNWaKFObWEJWTOSVO|KOURFKYUJNWTLPVSOMZVPWbQ|KOURGKYUJNWSNWaTEJUQLPea|KOURGKYUJNWSNWaTLPUQPWbL|KOURGKZUJNWSNWaTEJeaJMbW|KOURGKZUJNWSNWbSOTXOKTfb|KOWTFKTPBFUQJNbWOSVOLbfW|KOWTFKTPBFURJMYUMQcYEJRM|KOWTFKTPBFVRJNaWOSWTLOea|KOWTGKTPDGbWOTXOLbfWJNWS|KOWTGKTPDGUQJNYUEJVRNSaV|KOWTGKTPKNPGCLbWFKWSNWaT|KOWTJMTKFOaWBFWTGKTPDGda|KOWTJMTKFOaWGKWTBFTPDGda|KOWTJMTKFOaWGKWTBFTPDGea|KOWTJMTKFOaWGKWTBFTPDGUQ|KOWTJMTKFOaWGKWTBFUQOSQJ|KOWTJMTKFOaWGKWTBFUROSVO|KOWTJMTKFOaWLPeaHLWTPWaK|KOWTJMTKFObWGKWTBFTPDGUQ|KOWTJMTKFObWMRUNOSVOLJWS|KOWTJMTKFObWMRUNOSVOLJXT|KOWTJMTKFObWMRVMIRUNOSNK|KOWTJMTKFObWOSVOLbfWMQUR|KOWTJMTKFObWOSVOLbfWMQXT|KOWTJMTKFOUQMRVMIRZVEIVM|KOWTJMTKFOUREJbWGKZUJNUQ|KOWTJMTKFOURGKbWMQWSLPSL|KOWTJMTKFOURGKbWMQWTLPeb|KOWTJMTKFOURMQbWGKWSLPSL|KOWTJMTKFOURMQbWGKWTLPeb|KOWTJMTKFOVRMVaREJUQBFZU|KOWTJMTKGNVRMVaKFObWEJUQ|KOWTOSVOLSTPHLaVLOeaFKUQ|KOWTOSVOLSURJMYUMVaRFJea|LOUQHLYULPVSOVZSIMaVKNcY|LOUQHLYULPVSOVZSJMQJENSJ|LOUQJMQJFMWSHLYUMRUNKRVM|LOUQJMQJFMWTMRVMIRbWEJTP|LOUQJNWSNWbLGPfbEJbWHLYU|LOUQJNWSNWbLHOfbKNVRNUYR|LOUQJNWSNWbLHOfbKNZUNScZ|LOUQJNWSNWbLHOfbKNZUNSVR|LOURJMWSEJSLHObWJNfbNUZJ|LOVRJMaVHLWTLPUQPWbLGPQJ|LOVRJMaVMQeaEJRMIRUEAJVR|LOVRJNWTFJTPJMZVMQcZGLPG|LOWSGLbWKNUQFKZUBFURNUQZ|LOWSGLbWKNURNUYRJMRNLPSL|LOWSGLbWKNURNUYRJMWTEJTK|LOWSGLbWLPSLPGWSJMfbMQSO|LOWSGLbWLPSLPGXTHLTPJNVR|LOWSHLbWJMUQMRVMIRSNRUYR|LOWSHLbWJMUQMRVMIRSNRVaR|LOWSHLSNJSXTOXVHIMbWEJfb|LOWSHLSNJSXTOXVHIMbWEJWS|LOWSHLSNJSXTOXVHIMbWMRUN|LOWSHLSNJSXTOXVHIMURMVaR|LOWSHLSNJSXTOXVHIMZVEIUR|LOWSHLSNJSXTOXVHIMZVMQVS|LOWSHLUQKNZUNWaKFObWLPea|LOWSHLURJNSJEUYRLPbWOTXO|LOWSHLXTOXSNJSVHIMbWEJUQ|LOWTJMbWEJWSAESLGWaTCGTP|LOWTJMbWEJWSBESLGWaTJNfb|LOWTJMbWEJWSBESLGWaTJNTP|LOWTJMbWHLTPMRUNKRVMIRWT|LOWTJMbWMRUNKRVMIRTKGNeb|LOWTJMbWMRUNKRVMIRTKGNfb|LOWTJMbWMRVMIRUNKRTKGNfb|LOWTJMUREJbWJNfbNUZJFMTP|LOWTJMUREJbWMQTPOTXOKTWS|LOWTJNbWNRUNKRVMIRTKGNXT|LOWTJNbWNRVMIRUNKRTKGNeb|LOWTJNVRFJTPJMUQNUQJENZQ|LPUQGLYUDGcYJMQJFMWTPWbS|LPUQGLYUDGVRJNZVEJcYLORM|LPUQHLWSKNbWFKZUKOURNUQZ|LPUQHLYUKOVRJMQJFVaRDHea|LPUQHLYUKOWTPWaKFObWLPea|LPUQJNWTPWbJENXTHLTPAEfb|LPURJNWSNWaTPWbSKNRKGWeb|LPVRHLZVLOWTPWbLGPfbKObW|LPVRJMUQMVaREJZUJMQJFVWT|LPVSHLXTKOTKFVaRJMZVMQcZ|LPVSHLXTKOTKFVZSGKSNKRUN|LPVSHLXTKOTKFVZSGKURKOSN|LPVSHLXTKOTKFVZSGKURLOSL|LPWSGLSOKTXOLSVOJMbWMQUR|LPWSGLSOLSVOKTXOIMZVMRVM|LPWSIMUREISOKTXOGLYULSVO|LPWSJMSOKTXOMQbWEJfbJMVR|LPWSJMSOKTXOMQbWEJWTPWaT|LPWSJMSOKTXOMQUREJbWJMfb|LPWSJMSOKTXOMQUREJRMIRVM|LPWSJMSOKTXOMQURFJbWJMWS|LPWSJMUQEJZUKNcZNWbSBEfb|LPWSJNSJFMaWMQWTPWbSEJfb|LPWSJNSJFMaWMQWTPWbSIMSO|LPWSJNSJFMXTPWbSHLfbBFbX|LPWSJNSJFMXTPWbSMQURHLfb|LPWTPWbSGLSOKTXOLSVOIMZV|LPWTPWbSIMfbKNbWMRVMJQSJ|LPWTPWbSIMfbMQSOKTXOEIbW|LPWTPWbSIMUQEIZUBEURJNSJ|LPWTPWbSIMUQEIZUHLebKNcZ|LPWTPWbSIMUREISOKTXOGLYU|LPWTPWbSIMUREISOKTXOMQfb|LPWTPWbSIMXTKNTPNWaTMQfb|LPWTPWbSJMXTMQTPIMSOKTPW|LPWTPWbSJNSJENXTAEVREJTP|LPWTPWbSKNaWGLXTFKTPKOPG|LPXTKOTKGNVSFKaVHLbXLOSL|LPXTKOTKGNVSHLaVLOSLPGbX|LPXTKOTKGNVSHLaVLOSLPGea|IMUQEIWTKNTPLObWGKWTCGVRMV|IMWSMQUREIbWAEZUQZdUKOUQOT|JMUQMRVMIRWTEJTPAEbWEIZUJN|JMWSKOUQGKQJEWaTIMTPKNPGCL|JMWSLPSOKTXOMQaWEJWSGLURJM|JMWSLPSOKTXOMQbWEJfbJMbXAE|JNVRFJWTLOZVNSUQSZdUJNcZIM|JNVRFJZVJMUQNUQZMRVMIRWTEI|JNVSEJaVKOUQGKZUDGURNUQZKN|JNWTEJTPJMbWNRUNKRZUFKUNKR|LPWSJMSOKTXOMQUREJaWJMbXAE|LPXTKNURNUYRGKTOKTbXCGXOGK|IMUQEIVSKOaVFKZUJNQJNEWTIMTP|IMUQEIVSKOaVFKZUKNURNUQZMQYU|IMUQEIVSKOaVFKZUKNVROVRaBEXT|IMUQEIVSKOYUOVZSBEXTFKTPKNaV|IMUQEIWSMRVMIRbWAEfbLOSLGPWS|IMUQEIWTLPbWMRVMIRTOKTXOAEfb|IMUQEIWTMRVMIRZVAEVMEIcZIRZV|IMUQEIYUAEVSKNaVGKeaLPXTHLUR|IMUQEIYUKNcYFKWTBEaWLPeaGLTO|IMUQEIYUKNVRMVaKFOWTGKTPDGZV|IMUQEIYUKNVRMVaKFOWTGKZVBFdZ|IMUQEIYUKNWSNWaTBEURFKZUKNRK|IMUQEIYUKNWSNWaTLOTKGNVSNWbS|IMUQEIYULOURGLZUDGcYLPWTPWbL|IMUQEIZUAEURKNRKGNVRMVaKFOea|IMUQEIZUAEURKNRKGNVRNUQZJNXT|IMUQEIZUAEVRMVaRLOWTJNcZOSbW|IMUQEIZUAEVSLOSLHOURMVaROSWN|IMUQKNVRMVaKGNZUDGURNUQZFKWT|IMUQKNWSNWaTEIZUBEURFKYUKNRK|IMUQKNWSNWaTLOTKGNbWHLebDHYU|IMUQKNWSNWaTLOTKGNbWHLWTMRVM|IMUQKNWSNWaTLOTKGNbWHLXTLPWS|IMUQKNWSNWbSFKYUJNQJNWaTENTP|IMUQKNWTLPYUPWbSNWaTFKTOKTXO|IMUQKNWTNSVOLSaVGLVOLSeaDGaV|IMUQKNXTLPbXEITOGKZUKTXOMRVM|IMUQKNXTLPbXEITOMRVMIROKFOZV|IMUQKNXTLPVSMRTOGKbXKTXORVaK|IMUQKNXTNSVOLSWNJSQJENYUAETP|IMUQKNXTNSWNJSVOLSQJENbXAETP|IMUQKNYUNSWNJSQJENVOLSbWSbfW|IMUQLPWTPWaTKOTKGNbWHLWTCGTO|IMUREIWSKObWFKWTLPSLPWaTGWea|IMUREIWTJNbWNUZJFMfbAEdZMQTP|IMUREIWTLOTPAEbWOTXOKTZUFKUQ|IMURMQRMJNMIEJWTLPYUPWaTHLbW|IMURMQRMJNMINRVMQJYUJNUQLOWT|IMURMQRMJNMINRVMQJYULOURJMWT|IMURMQRMLPWSEISOIRVMKTXOJNMI|IMURMQRMLPWSHLSOLSVOKTXOEIZV|IMURMQRMLPWTPWbSHLMIJNSJENfb|IMURMQRMLPWTPWbSJNSJENMIHLfb|IMVRMVaRLPZVGLWTPWbSKNRKFOUR|IMVSEIWTKOTKFVZSMQXTQZcVIMbW|IMVSEIWTKOTKFVZSMQXTQZcVIMTO|IMVSKNXTMQaVEITPFKWTNWTaAEbW|IMVSKNXTMQbXFKaVJMSJMFTPEJfb|IMVSKNXTMQTPFKaVKObXGKPGCLeb|IMVSKNXTMQTPFKbXJMSJMFUREJRM|IMVSMQWTKNTPNWbSJMfbFKbWEJaV|IMWSLPbWGLUQKNVRMOWTPWaREIZV|IMWTMQTPJNbWEJWTAETOLSVOKTPW|IMWTMQTPJNbWNRUNKRVMQJaVJMWS|IMWTMRUNKRVMJQTPEJbWLOWTAETK|IMXTLOUROXRIHLYULPUQGLZUJNcY|IMXTLOUROXRIJNYUHLUQLPcYEJZU|IMXTLOUROXRIJNYUHLUQLPWSNWbS|IMXTMQTPJNWSNWbSEJfbAEaWEIUR|IMXTMQTPJNWSNWbSEJfbAEaWKObX|IMXTMQTPKNVSFKbXJMSJMFUREIfb|IMXTMRUNKRVMJQTPEJWTLOTKFObW|IMXTMRVMJQTPEJbXJNWTAEaVNRVM|JMUQEJWTAETOKTXOLSVOGLaWLSWN|JMUQEJWTLPTOKTXOMRVMIRbWAEfb|JMUQEJZUKOURFKWSLPSLHObWBEWS|JMUQFJWSLPZUJNSJMFURHLbWLOYU|JMUQFJWSLPZUJNSJMFURHLYUEJcY|JMUQFJYULPURHLZUDHWSJNSJMFbW|JMUQLOQJFMWTEJbWBFTPMQWSAESL|JMUQLOQJFMWTMRVMIRbWEJTPAEWT|JMUQLOQJFMYUMRUNKRVMIRWTEJTK|JMUQMRVMIRWSEJbWAEfbLOSLGPWS|JMUQMRVMIRWSEJbWBEfbLOSLHOZU|JMUQMRVMIRWSEJSOLSZVSZdEAJXT|JMUQMRVMIRWSLOSLHObWEJWTDHTP|JMUQMRVMIRWTEJbWAETPEIWTJMQJ|JMUQMRVMIRWTEJbWLOZUJNdZAEaV|JMUQMRVMIRWTEJZVAEVMEIcZIRZV|JMUQMRVMIRWTKNbWFKTPLOZUEJWT|JMUQMRVMIRWTLOTPEJbWOTXOKTZV|JMUREJWSKObWAEWTLPTKGWaTPWeb|JMUREJWSKObWFKYUMQebJMWTLPSL|JMUREJWSKObWGKWTLPSLPWaTHOfb|JMUREJWSKORNAEbWFKZUKRUNLPSL|JMUREJWSKORNAEbWLPSLJbfWHOVR|JMUREJWTJNbWNUZJFMfbMQdZIMTO|JMUREJWTJNbWNUZJFMfbMQdZKNTP|JMUREJWTLObWJNfbNUZJFMdZMQYU|JMUREJWTLObWJNTPNUZJFMWTMQfb|JMUREJWTLObWMQTPJNWTNUYRAEcY|JMUREJWTLObWMQTPJNWTNUYRAEfb|JMUREJWTLObWMQWSJMSLGWaTAETP|JMUREJWTLPTOKTXOMQRMIRVMJNMI|JMURFJWSKOaWMQWTJMTKGWbSLPeb|JMURFJWSKOaWMQWTJMTKGWbSLPRN|JMURFJWSKOaWMQWTJMTKGWbSLPYU|JMURFJWSKObWMQebJMYUGKWTLPSL|JMURKNRKGNVSEJSOLSaVCGVOFKOF|JMURKNRKGNVSEJSOLSaVDGVOGLea|JMURKNRKGNWTMRVMIRZUEJbWAEdZ|JMURKOWTLPTKGUZJENXTPWbJFMYU|JMURLOWTEJbWAEfbMQTPHLWSOTXH|JMURLOWTEJbWAEfbMQTPJNWTNUYR|JMURLOWTEJbWAEfbMQTPJNYUGLPG|JMURLOWTEJbWAEfbMQYUJNRMIYVS|JMURLOWTEJbWJNTPNUZJFMWTMQfb|JMURLOWTEJbWMQRMIRVMGLMILPYU|JMURLOWTEJbWMQRMIRVMGLTPJNPG|JMURLOWTEJbWMQTPOTXOKTRMIRVM|JMURLOWTEJbWMQWSJMSLGWaTAETP|JMURLOWTEJbWMQWSJMSLGWaTHLZU|JMURLOWTGLTPCGbWOTXOLbfWKOWS|JMURMQVSKOaVEJWTLPTKGWbSCGYU|JMVRMVaREJUQLOWTJNZVNUYRFJda|JMVSEJWTLPTOKTXOGKUQKTbXBEXO|JMVSFJaVMQeaJNSJENURNUYRKOWS|JMVSFJUQBFZUKOdZOVZSLOSLHOWT|JMVSFJWTMQSNKRUNJSTOSVZSLPbW|JMVSFJWTMQTOKTXOIMSNLSNWJNUR|JMVSKOaVFKUREJWTKNTKNWbSGWeb|JMVSKOaVMQeaEJWTJMTKGWaTLPTO|JMVSKOUQOVQJENaKFOYUGKWTLPea|JMVSLPSOKTXOMQUREJaVGKeaKTRN|JMVSMQaVIMUREIWTLPSNPWbSKOSL|JMVSMQaVIMWTMRUNKaeVEJYUAETO|JMVSMQUREJRNKRSOLSWEAJZUQZdE|JMVSMQURKNRKFVaREJeaLOaVBFWT|JMVSMQURKOaVEJWTGKSNJSRMIadP|JMVSMQURKOaVEJWTJMTKGWbSLPda|JMVSMQURKOaVEJWTJMTKGWbSLPeb|JMVSMQURKOaVEJWTJMTKGWbSLPfb|JMVSMQURKOaVEJWTJMTKGWbSLPSO|JMVSMQURKOaVFKWTKNTKNWbSGWeb|JMVSMQURKOaVGKWTLPSLPGTOKTXO|JMVSMQURKOSNOSNKGUWNCGYRLOcY|JMVSMQURLPSOKTXOEJZUQZcVGLdZ|JMVSMQWTEJTOKTXOJMURMVaRAEea|JMVSMQWTKOTKFVaRLObWHLeaCFWT|JMVSMQWTKOTKFVZSQZdUIMbWMQXT|JMWSEJaWKNeaMQSOLSVOJMWSNWbS|JMWSEJaWKNXTMRVMIRbXGKZVRaeV|JMWSEJaWMQeaJMWTMRUNKRVMQJaV|JMWSEJbWAEfbMRUNKRVMJQXTIMYU|JMWSEJbWAEfbMRUNKRVMJQXTLPZV|JMWSEJbWAEWTMRUNKRVMJQTPIMfb|JMWSEJbWKNURNUYRFKfbKORNAEWT|JMWSEJbWKOUQFKZUJNSJMFWSKNSJ|JMWSEJbWKOUQGKZULPSLPGXTAETO|JMWSEJSOKTXOLSVOMQbWAEfbJMUR|JMWSEJSOKTXOLSVOMQURGLRNJSOV|JMWSEJSOLSVOKTXOAEURMVaRJMOK|JMWSEJSOLSVOKTXOAEURMVaRJNRK|JMWSEJSOLSVOKTXOBEUQGLaVLSVO|JMWSEJSOLSVOKTXOBEZVMRVMJZcV|JMWSEJSOLSVOKTXOGLaWLSWEAJbW|JMWSEJSOLSVOKTXOGLaWLSWEAJUQ|JMWSEJSOLSVOKTXOMQURJMaVAEbW|JMWSEJURKOaWFKWTKNTKNWbSGWeb|JMWSEJURKOYUMQcYJMbWFKRNKRUN|JMWSFJbWMQWTJNSJENTOLSVFBKUR|JMWSFJbWMQWTJNSJENTPNRUNKRVM|JMWSKOaWFKUQMRVMIRWTOVZSBFSN|JMWSKOaWFKWTEJbWBFUQMRVMOVZS|JMWSKOaWFKWTMRUNKaTKGWbSLPeV|JMWSKOaWGKWTEJTPDGURMQZUQZdU|JMWSKOaWGKWTLPSLPGTOKTXOEJbW|JMWSKOaWMQeaEJWTJMTKGWaTLPTO|JMWSKOaWMQUREJWTJMTKGWbSLPeb|JMWSKOaWMQWTEJTKGWbSLPfbCGbW|JMWSKOaWMQWTEJTKGWbSLPfbJMbW|JMWSKOaWMQWTEJTKGWbSLPURCGea|JMWSKOaWMQWTEJTKGWbSLPURJMfb|JMWSKOaWMQWTEJTKGWbSLPVRJMSN|JMWSKOaWMQWTFKTPEJURJMbWCFfb|JMWSKOaWMQWTGKTPDGUREJYUBEbW|JMWSKOaWMQWTGKURLPSLPGTOKTXO|JMWSKOaWMQWTLPTKGWbSEJfbJMSO|JMWSKOaWMQWTLPTKGWbSEJURCGSO|JMWSKObWEJUQFKZUJNSJMFURLPWT|JMWSKObWEJUQGKZULPSLPGXTAEUR|JMWSKObWEJUQMRVMOVaRJNRKIRea|JMWSKObWEJURFKWTLPSLPWaTGWea|JMWSKObWEJURFKYUMQcYJMRNKRUN|JMWSKObWFKUQBFQJFMfbMQYUEJUR|JMWSKObWFKUQBFQJFMfbMQYUIMSN|JMWSKObWFKUQBFQJFMYUMQfbEJUR|JMWSKObWFKUQBFQJFMYUMRUNKRVM|JMWSKObWFKUQEJZUJNSJMFURLPWT|JMWSKObWFKUQMRVMIRSNRUYROSNJ|JMWSKObWFKUQMRVMIRSNRVaROSXT|JMWSKObWFKUREJWTLPSLPWaTGWeb|JMWSKObWFKUREJYUMQcYJMRNKRUN|JMWSKObWFKUREJYUMQcYJNSJBFRM|JMWSKObWFKUREJYUMQcYJNSJBFWT|JMWSKObWFKUREJZUMQRMIRVFCJaV|JMWSKObWFKWTLPSLPWaTGWeaKNaT|JMWSKObWGKUQLPSLPGQJFMWSEJYU|JMWSKObWMQWTEJTKGWaTLPeaPWaT|JMWSKObWMQWTLPTKGWaTPWebHLbS|JMWSKOUQEJZUGKaWKNVRMVSZBEWT|JMWSKOUQGKQJEWaTAETPDGYUEJea|JMWSKOUQGKQJEWaTAEYUEJURLPea|JMWSKOUQGKQJEWaTIMTPCGVSOVZS|JMWSKOUQGKQJEWaTIMTPDGdaKNbW|JMWSKOUQGKQJEWaTIMTPDGdaMQbW|JMWSKOUQGKQJEWaTIMZUOSVOLSda|JMWSKOUQGKQJEWaTIMZUOSVOLSea|JMWSKOUQGKQJEWaTLPYUPWbLHOfb|JMWSKOUQGKQJEWbSIMaWAEWTLPSL|JMWSKOUQGKQJEWbSIMaWAEYUMQUR|JMWSKOUQGKQJEWbSIMaWMQWTLPSL|JMWSKOUQGKQJEWbSIMYUMQaWAEWT|JMWSLOSLHOUREJaWAEWSGLbWLPSL|JMWSLOSLHOUREJaWJNWSNWbLGPfb|JMWSLOSLHOVRMVZLGPXTPWbSCGfb|JMWSLPSOKTXOMQaWEJWTPWbSJMfb|JMWSLPSOKTXOMQbWEJfbJMbXMRUN|JMWSLPSOKTXOMQbWEJfbJMbXMRVM|JMWSLPSOKTXOMQbWEJfbJMVRMVZS|JMWSLPSOKTXOMQbWEJWTPWaTJMfb|JMWSLPSOKTXOMQUREJaWJMbXFJeb|JMWSLPSOKTXOMQUREJbWJMfbGLWS|JMWSLPSOKTXOMQUREJbWJMYUAEWS|JMWSLPSOKTXOMQUREJbWJMYUGLWS|JMWSLPSOKTXOMQUREJRMIRVMJNMI|JMWSMRUNKRVMIRbWLOSLHOfbEJWS|JMWSMRUNKRVMIRbWLOSLHOWTFKfb|JMWSMRUNKRVMIRZUFKUNKRXTEJTO|JMWSMRUNKRVMIRZUFKUNKRXTGKbX|JMWSMRUNKRVMIRZUFKUNKRXTGKSN|JMWTEJbWAETPMQWSLOSLHOfbJNUR|JMWTEJbWJNfbMRVMIRTPAEUQLOWT|JMWTEJbWJNURNUZJFMVSLOSLHOdZ|JMWTEJbWLOfbMQTPOTXOKTURTXRM|JMWTEJbWMQURLOTPJNWTNUYRAEfb|JMWTEJbWMQWSLPSOPWaTAETPKTPW|JMWTEJTOKTXOLSVOMQbWGLWSBEUR|JMWTEJTOKTXOLSVOMQbWJMfbAEWS|JMWTEJTOKTXOLSVOMQbWJNURNUYR|JMWTEJTOLSVOKTXOBEURMVaRJMZV|JMWTEJTOLSVOKTXOBEZVMRVMJZcV|JMWTEJTOLSVOKTXOMQbWAEfbJMUR|JMWTEJTPAEURKOaWOTXOLSWNJSVO|JMWTEJTPLObWOTXOKTWSTXURAEfb|JMWTEJTPMQbWJNVSFJaVJMSJMFfb|JMWTEJTPMQbWLOWSAESLHOfbJNbW|JMWTEJTPMQXTLObXJNURNUYRAEfb|JMWTEJUQMRVMIRTPLObWJNWTRUYR|JMWTFJUQLPZUPWaTCFURKNRKGNbW|JMWTFJUQLPZUPWaTCFVSMRUNKRTO|JMWTFJUQLPZUPWaTKNURNUYRHLbW|JMWTKNaWNSWNMRVMIKeaEJTPLOUR|JMWTKNaWNSWNMRVMIKTPEJUQJNZU|JMWTKNTOLSVOEJbWGLfbLSURNUWE|JMWTKNTOLSVOEJURNUYRMVZSJMbW|JMWTKNTPMQXTEJaWAEWSNWTaJNbW|JMWTKNVRMVaKGNbWEJTPIMPGDKXT|JMWTLObWEJfbAETPMRVMJQWTEJUR|JMWTLObWEJTPMQURJNfbNUYRAEcY|JMWTLObWEJTPMQWSAESLHOfbKNaW|JMWTLObWEJWSAESLGWaTHLTPKOPG|JMWTLObWEJWSAESLGWaTHLURMQfb|JMWTLObWEJWSMQSLGWaTJNURNUYR|JMWTLObWMQWSEJSLGWaTHLURLOfb|JMWTLObWMRUNKRVMIRTKGNZUNSUN|JMWTLObWMRVMIRUNKRTKGNebFKWS|JMWTLOUREJbWJNTPNUZJFMWTMQfb|JMWTLPTOKTXOMQbWFJWTPWaTJMfb|JMWTLPTOKTXOMQUREJRMIRVMJNMI|JMWTLPUQPWQJENbJFMfbHLYUMQbW|JMWTLPUQPWQJENbJFMXTAEfbMQVR|JMWTMQTPEJXTJMTOLSVOKTPWHLWS|JMWTMRUNKRVMIRTOLSZURVaRGKRM|JMWTMRUNKRVMIRTOLSZURVaRGLRM|JMWTMRUNKRVMIRTOLSZURVaRHLRM|JMWTMRUNKRVMIRTOLSZURVaRHLUQ|JMWTMRUNKRVMIRZUFKUNKRTPLObW|JMWTMRVMIRUNKRaWFKWSRVSNKRZS|JMWTMRVMIRUNKRTOLSZURVaRGKRM|JMWTMRVMIRUNKRTPEJbWAEWTLOTK|JMXTLObXEJfbMQTPJNURNUYRAEWS|JMXTLPbXMQTOKTXOGKWTPWaTEJfb|JMXTLPbXMQVSKNSJENURNUYRHLaV|JMXTLPUQGLQJFMbXEJVSMQebJNSJ|JMXTLPUQHLQJFMVSMQSNKRTOLSWU|JMXTLPUQMRVMIRZURVaRKNRKFXUR|JMXTLPVSHLbXDHebKOTDMRUNCGDK|JMXTLPVSMQaVEJeaJNSJFMVSKOTK|JNUQEJWSNWbSKOZUJNSJFMQJOTXO|JNUQEJWTAETPLObWNSWNKRVMIRaW|JNUQEJWTAETPLOVRNUYRJNZVNUQZ|JNUQEJWTLPbWGLZULOURNUQZJMYU|JNUQEJWTNRVMIRbWLOfbAETPOTXO|JNUQEJYUAEVRIMRINSWNKYbWJNZV|JNUQEJZUAEWTLOVROSaWGLTPDGQM|JNUQEJZUAEWTLPQMJSaVPWVOKTbA|JNUQEJZULPURNUQZIMYUMQWSKNbW|JNUQEJZULPVRGLRMIRWTPWbSNWUP|JNUQKOWTGKQMIRVMEIZVIRVMAEMI|JNUQKOWTNRTKGNVMIRbWFKWTLOfb|JNUQLOWSNWbLHOYUOTXOKTURTXfb|JNUQLOWTEJbWAETPNRVMIRWTJNZU|JNUQLOWTEJZUNScZKNTRBEVOJMQJ|JNUQLOWTEJZUNSVRJNcZSWbLGWaT|JNUQLOZUEJWTNSVRJNTPAEcZEJaV|JNUQLOZUEJWTNSVRJNTPAEcZIMQA|JNUQLPVSEJSOKTXOAEWSNWbSGKaV|JNUQNRVMIRWSEJbWAEfbLOSLHOWS|JNUQNRVMIRWSEJbWBEfbLOSLHOZU|JNUQNRVMIRWSEJbWBEZULOSLHOUN|JNUQNRVMIRWSEJbWLOSLHOWSOVZS|JNUQNRVMIRWSEJSNJSZVSZcMAEMI|JNUQNRVMIRWSEJSOLSaVRadEAJea|JNUQNRVMIRWSLOSLHObWGLWTKNTK|JNUQNRVMIRWSLOSLHObWGLZUKNWT|JNUQNRVMIRWSLOSLHObWKNfbGLWT|JNUQNRVMIRWSLOSLHObWKNWTGLTK|JNUQNRVMIRWTEJbWAETPEIfbIMWS|JNUQNRVMIRWTEJbWAETPJNZULOWT|JNUQNRVMIRWTEJbWLOaVRaeVAEVR|JNUQNRVMIRWTEJbWLOfbAEaVRaeV|JNUQNRVMIRWTEJbWLOTPAEWTJNZU|JNUQNRVMIRWTEJbWLOTPJNWTAEZU|JNUQNRVMIRWTEJbWLOTPOTXOKTZV|JNUQNRVMIRWTEJbWLOZVBEVMOSWN|JNUQNRVMIRWTEJTPAEbWEIfbJMQJ|JNUQNRVMIRWTEJTPAEbWJNZULOWT|JNUQNRVMIRWTEJTPLObWJNZUOTXO|JNUQNRVMIRWTEJZVAEVMEIcZIRZV|JNUQNRVMIRWTEJZVJMQJFMVSLOSL|JNUQNRVMIRWTKNTPFKXTLObXCFZU|JNUQNRVMIRWTKNTPFKXTLObXHLZU|JNUQNRVMIRWTKNZUFKcZLObWBFfb|JNUQNRVMIRWTLObWEJfbJNTPAEWT|JNUQNRVMIRWTLObWEJTPAEWTJNZU|JNUQNRVMIRWTLObWEJTPJNWSNWaT|JNUQNRVMIRWTLObWEJTPJNWTAEZU|JNUQNRVMIRWTLObWEJTPJNWTRUYR|JNUQNRVMIRWTLObWEJTPOTXOKTWS|JNUQNRVMIRWTLObWEJZVJMQJFMTP|JNUQNRVMIRWTLObWKNTKFOWTGKfb|JNUQNRVMIRWTLOTPEJbWJNWTRUYR|JNUQNRVMIRWTLOTPHLbWEJfbJMQJ|JNUQNRVMIRWTLOTPHLbWEJWTJMQJ|JNUQNRVMIRWTLOZUHLUNKRTKGNaV|JNUQNRVMIRWTLOZUHLUNKRTKGNbW|JNUQNRVMIRZUKNdZLOWTFJTKJMQS|JNUQNRVMIRZUKNdZLOZVEIVMIRcZ|JNUQNRVMIRZUKNWTFKTPLObWHLWT|JNUQNRVMIRZULOUNKRdZFKZUKNcZ|JNUQNRVMIRZULOUNKRdZFKZUKNWT|JNUQNRVMIRZULOUNKRWTHLTKGNaV|JNUQNRVMIRZVEIVMIRWTKNbWAEdZ|JNUQNRVMIRZVEIVMIRWTKNdZAEbW|JNUQNSWNKRVMIRZVEIVMIRcZAEZV|JNURNUYREJWSKObWJMWTMQTKGUcY|JNURNUYREJWTAETPJNRMIRVMLOMI|JNURNUYREJWTJMTOLSVOKTXOMVZS|JNURNUYREJWTJMTPLObWOTXOKTcY|JNURNUYREJWTJNRMIRVMAEMILOTP|JNURNUYREJWTJNRMIRVMAEMINRcY|JNURNUYREJWTJNRMIRVMAEMINRTP|JNURNUYREJWTJNRMIRVMAETPEIZV|JNURNUYREJWTLObWJMfbMQTPAEWS|JNURNUYREJWTLObWJMTPAEfbOTXO|JNURNUYREJWTLOTPAEbWJNWTNUZQ|JNURNUYREJWTLOTPJMbWOTXOKTWS|JNURNUYREJWTLOTPJNbWNUZQAEWT|JNURNUYREJWTLPTOKTXOJMVSMVaR|JNURNUZQEJWSKObWGKYUBEebDGcZ|JNURNUZQEJWSKOYUJNSJFMQJOTXO|JNURNUZQKNVRNUQZEJaVIMYUMQWS|JNURNUZQKNVRNUQZFKaVEJWSLOSL|JNURNUZQLOWSGLYUOTXOKTbXDGXO|JNURNUZQLPWSPTXOKTYUTWaTIMQJ|JNVREJaVBEWTJMTPLOUQNUYRHLQJ|JNVREJaVJMUQNUQJFMZJBFVSFMWT|JNVREJaVJMXTMQbXLOfbGLTPAEPG|JNVREJaVJMXTMQbXLOfbGLTPBEPG|JNVREJaVJMXTMQbXLOfbGLTPOTPG|JNVREJaVJMXTMQTPFJWTJMbXLOda|JNVREJaVJMXTMQTPFJWTLOdaOXRM|JNVREJaVJMXTMQTPLOWSNWbLHOea|JNVREJaVLOWTBETPJMUQNUYRHLQJ|JNVREJaVLOWTBEUQNUYRJMQJEUZQ|JNVREJaVLOWTHLTPDHUQNUYRBEbW|JNVREJaVLOWTJMUQNUQJFMZJBEbW|JNVREJaVLPeaGLVSLOSLPGXTJMZV|JNVREJaVLPVSGLZVLOSLPGeaJMUQ|JNVREJaVLPVSGLZVLOSLPGUQNUQZ|JNVREJaVLPVSGLZVLOSLPGVSGLUQ|JNVREJaVLPXTHLbXLOWSNWTaGLaW|JNVREJWTBEbWJMTPMVZJFMWTMQTO|JNVREJWTBEZVJMbWMQcZLOTPHLWS|JNVREJWTJMaWMVZJFMWSLOSLGWbS|JNVREJWTJMaWMVZJFMWSMQTOKTXO|JNVREJWTJMaWMVZJFMWSMRUNKRea|JNVREJWTJMUQMVZJFMQJBEYUENUQ|JNVREJWTJMUQMVZJFMQJBFYUFMUQ|JNVREJWTJMUQNUQJFMZJBEJFKBTP|JNVREJWTJMUQNUQJFMZJBFYUFMUQ|JNVREJWTLObWBETPJMWTMVZLHOaV|JNVREJWTLObWJMUQMVZJFMQJBEYU|JNVREJXTBETOLSaVJMVOKaRBEJeV|JNVREJXTJMUQNUQJFMZJBEaVENVS|JNVREJXTLOTPBEaVHLWSNWbSJMfb|JNVREJXTLOTPBEaVJMVSMVSLHOZL|JNVREJXTLOTPJMWSNWbLMVaRHOZV|JNVREJXTLOTPOTZVJMUQNUQZAEWS|JNVREJXTLPaVHLbXLOWSNWTaDHUQ|JNVREJXTLPaVHLbXLOWSPWSbGLUQ|JNVREJXTLPbXGLZVLOUQNUQZJMVS|JNVREJXTLPbXHLaVJMWSNWTaMQfb|JNVREJXTLPbXHLZVJMUQNUQZMQVS|JNVREJXTLPZVGLbXJMUQNUQZMQVR|JNVREJXTLPZVJMUQNUQZMRVMIRZU|JNVREJZVJMUQNUQJFMYRAEWSBFbW|JNVREJZVJMUQNUQJFMYRAEWSCFbW|JNVREJZVJMUQNUQJFMYRAEWSCFcY|JNVREJZVJMUQNUQJFMYRAEWSCFdZ|JNVREJZVJMUQNUQJFMYRAEWSKORN|JNVREJZVJMUQNUQJFMYRAEWSLOSL|JNVREJZVJMUQNUQZAEVSLOSLHOWS|JNVREJZVJMUQNUQZAEWSEJaWKOXT|JNVREJZVJMUQNUQZAEWSEJSOLSVO|JNVREJZVJMUQNUQZAEWSEJYUKOaW|JNVREJZVJMUQNUQZAEWTEJbWMQTP|JNVREJZVJMUQNUQZAEWTEJTPJNVS|JNVREJZVJMUQNUQZAEWTEJTPMRVM|JNVREJZVJMUQNUQZAEWTMRVMIRbW|JNVREJZVJMUQNUQZAEXTLObXEJfb|JNVREJZVJMUQNUQZAEXTLObXEJTP|JNVREJZVJMUQNUQZAEXTLObXEJWS|JNVREJZVJMUQNUQZAEXTLObXEJYU|JNVREJZVJMUQNUQZAEXTLObXMRVM|JNVREJZVJMUQNUQZAEXTMQTOLSVO|JNVREJZVJMUQNUQZAEYUMQWSEJSO|JNVREJZVJMUQNUQZAEYUMRUNKRVM|JNVREJZVJMUQNUQZFJWSAEYUMQSO|JNVREJZVJMUQNUQZFJWSBFYUKNUQ|JNVREJZVJMUQNUQZKNVRNUZJFMYU|JNVREJZVJMUQNUQZKNVSFJXTMQTP|JNVREJZVJMUQNUQZKNWSNWbSLPfb|JNVREJZVJMUQNUQZKNWSNWbSLPYU|JNVREJZVJMUQNUQZKNXTMQTOLSVO|JNVREJZVJMUQNUQZKNXTMRVMIRTP|JNVREJZVJMUQNUQZLOWSGLbWLPSL|JNVREJZVJMUQNUQZLOWSGLYUMQbW|JNVREJZVJMUQNUQZLOWSHLYUAEUR|JNVREJZVJMUQNUQZLOWTAEbWMRVM|JNVREJZVJMUQNUQZMQWSAEYUEJSO|JNVREJZVJMUQNUQZMQWTFJTOKTXO|JNVREJZVJMUQNUQZMQWTKNTOLSVO|JNVREJZVJMUQNUQZMRVMIRWSFJbW|JNVREJZVJMUQNUQZMRVMIRWSFJZU|JNVREJZVJMUQNUQZMRVMIRWSLOSL|JNVREJZVJMUQNUQZMRVMIRXTAETO|JNVREJZVLOUQNUQZAEWSGLYULPSL|JNVREJZVLOWTNScZIMRIKNTRJMVO|JNVREJZVLOWTNSUQSZdUAEcZJMQA|JNVREJZVLOWTNSUQSZdUAETPJNbW|JNVREJZVLOWTNSUQSZdUIMRIBEIB|JNVREJZVLPUQNUQZHLWSKOYUBEXT|JNVREJZVLPUQNUQZHLWSKOYUDHXT|JNVREJZVLPUQNUQZHLWSKOYUJMbW|JNVRFJaVJMUQNUQJENYRNUZQAEdZ|JNVRFJaVJMWTMQTOLSVFBKbWHLWT|JNVRFJaVJMWTMQTOLSVFBKXTGLZV|JNVRFJaVJMWTMQTOLSVFBKXTHLbX|JNVRFJaVLPXTGLbXLOWSNWTaJNfb|JNVRFJWSNWbSJMRNKRUNBFXTLPeb|JNVRFJWSNWbSJMSNMVaRBFXTLPea|JNVRFJWTJMaVMQTOLSVFBKbWHLfb|JNVRFJWTJMaVMQTOLSVFBKXTHLbX|JNVRFJWTJMTPMVZJENUQAEbWBFcZ|JNVRFJWTJMTPMVZJENUQAEbWBFfb|JNVRFJWTJMTPMVZJENUQAEbWEJYU|JNVRFJWTJMTPMVZJENUQAEbWLOWT|JNVRFJWTJMTPMVZJENUQLObWAEWT|JNVRFJWTJMTPMVZJENUQLObWOSWT|JNVRFJWTJMZVMQcZLOTPBFbWHLfb|JNVRFJWTJMZVMQcZLOTPCFbWEJeb|JNVRFJWTJMZVMQcZLOTPCFbWHLeb|JNVRFJWTJMZVMQcZLOTPCFbWNSWN|JNVRFJWTJMZVMQcZLOTPGLPGCLbW|JNVRFJWTJMZVMQcZLOTPHLbWBFWS|JNVRFJWTLObWJMTPMVZJENUQAEWT|JNVRFJWTLOTPJMbWMVZJENWTAEUQ|JNVRFJWTLOZVNScZIMRIKNTRJMVO|JNVRFJWTLOZVNSUQSZcVJMQJEUYR|JNVRFJWTLOZVNSUQSZdUIMRIBFIB|JNVRFJWTLOZVNSUQSZdUJNcZIMQL|JNVRFJWTLOZVNSUQSZdUKNTKJMQS|JNVRFJZVJMUQNUQZEJWTLObWAETP|JNVRFJZVJMUQNUQZMQWSKOaWGKWT|JNVRFJZVJMUQNUQZMRVMIRWSLOSL|JNVRFJZVJMUQNUQZMRVMIRWTKNTP|JNVRFJZVJMUQNUQZMRVMIRWTLObW|JNVRFJZVJMUQNUQZMRVMIRXTKNTP|JNVRFJZVJMUQNUQZMRVMIRXTLObX|JNVRFJZVJMUQNUQZMRVMIRZULOUN|JNVRFJZVJMWTMQcZLObWHLTPNSWN|JNVRFJZVJMWTMQcZLOTPBFbWHLeb|JNVRFJZVJMWTMQcZLOTPBFbWHLfb|JNVRFJZVJMWTMQcZLOTPGLPGCLbW|JNVRLOWTFJbWJMTPMVZJENUQOScZ|JNVRLOZVEJWTNSUQSZdUAETPJNbW|JNVRLPWTPWbJFVaREJZVHLfbJNbW|JNVRLPXTGLbXEJaVLOWSPWSbHLUQ|JNVRLPZVGLRMIRVMEIcZIRWTPWbJ|JNVRLPZVHLUQNUQZIMWSKOSNMQYU|JNVRLPZVHLUQNUQZIMWSMQYUKOSN|JNVRLPZVHLUQNUQZIMWTPWbSKOfb|JNVRLPZVHLUQNUQZIMWTPWbSKOYU|JNVRLPZVHLUQNUQZIMYUMQWSKOUR|JNVRLPZVHLVSDHSJFVaREJeaJMRN|JNVRLPZVHLVSDHSJFVaREJUQBFda|JNVSEJaVAEVRLPRMIRSOKaeMJQXT|JNVSEJaVKOeaFKURNUYRIMRIKNZU|JNVSEJaVKOeaGKURNUYRLPSLPGWS|JNVSEJaVKOUQFKZUJMQJNEURBFYU|JNVSEJaVKOUQFKZUJMQJNEWTIMTP|JNVSEJaVKOUQFKZUJMQJNEWTLPSL|JNVSEJaVKOUQGKZUBEURNUQZIMYU|JNVSEJaVKOUQGKZUBEURNUQZJNSJ|JNVSEJaVKOUQGKZUBEURNUQZKNYU|JNVSEJaVKOUQGKZUBEURNUQZKNZU|JNVSEJaVKOUQGKZUBEURNUYRJMQJ|JNVSEJaVKOUQGKZUDGURNUQZIMYU|JNVSEJaVKOUQGKZUDGURNUQZJMWT|JNVSEJaVKOUQGKZUDGURNUQZJNSJ|JNVSEJaVKOUQGKZUDGURNUQZKNYU|JNVSEJaVKOUQGKZUDGURNUQZKNZU|JNVSEJaVKOUQGKZUDGURNUYRBEcY|JNVSEJaVKOUQGKZUDGURNUYRJNSJ|JNVSEJaVKOUQGKZULPSLPGVRAEXT|JNVSEJaVKOUQGKZULPSLPGVRGLRM|JNVSEJaVKOUQGKZULPSLPGVRHLea|JNVSEJaVKOURNUYRJMeaAEWTGKSN|JNVSEJaVKOURNUYRJMeaAEWTGKTP|JNVSEJaVKOURNUYRJMZUGKSNDGNJ|JNVSEJaVKOURNUYRJMZUGKSNOSNP|JNVSEJaVKOURNUYRJMZUMQWTQZdU|JNVSEJaVKOURNUZQGKYUBEeaDGcZ|JNVSEJaVKOURNUZQGKYULPSLPGXT|JNVSEJaVLPUQGLZUKOURNUQZJMYU|JNVSEJaVLPVRGLZVLOSLPGUQNUQZ|JNVSEJUQAEZVIMdZKOZUOTXOMRVM|JNVSEJUQAEZVIMYUEIURNUQZKNXT|JNVSEJUQKOYUOVaKFOWTGKZVBFTP|JNVSEJURNUYRKORNOVaRJSWNBEXT|JNVSEJZVKOUQGKYUBEcYDGURNUQZ|JNVSEJZVKOUQGKYUBEURNUQZKNZU|JNVSEJZVKOUQGKYUDGURNUQZKNZU|JNVSEJZVKOUQNRVMIRXTOXSOLSWU|JNVSEJZVKOURNUYRJMcZGKWTAESN|JNVSEJZVKOURNUYRJMcZGKWTAETP|JNVSEJZVKOURNUYRJMcZMQZUQZdU|JNVSFJaVKOUQGKZUDGURNUQZKNZU|JNVSFJaVKOURNUYRBFWTFKSNJSTP|JNVSFJaVKOURNUYRJMRNMQWTIMTK|JNVSFJaVKOURNUYRJMZUEJWTGKTP|JNVSFJaVKOURNUYRJMZUGKWTCFTP|JNVSFJaVLPXTCFUQGLZULOSLHXVR|JNVSFJZVKOUQGKYULPSLPGXTIMUR|JNVSFJZVKOURNUYRJMRNEJNEAJWT|JNVSFJZVKOURNUYRJMRNMQcZBFXT|JNVSFJZVKOURNUYRJMRNMQcZIMZU|JNVSLOSJFMWTMQbWEJTPJMWTAEfb|JNVSLOSJFMWTMRUNKRTKGNXTHLbX|JNVSLOSLHOUQNRWTIMQJFMbWEJTP|JNVSLOSLHOURNUYREJaVJNWSNUSL|JNVSLPSJFMWSGLaVLOSLPGXTHLVS|JNVSLPSJFMWSHLaVKObWMQUREJYU|JNVSLPSJFMWSHLUQEJaVKObWGKZU|JNVSLPSJFMWSHLUQEJaVKOZUJNSJ|JNVSLPSJFMWTPWbSEJfbMQSOKTXO|JNVSLPSJFMWTPWbSEJXTMQSOJNOF|JNWSNWaTEJUQAEZUJNURNUQZEJea|JNWSNWaTIMTPLOUQEIQJFMbWAEfb|JNWSNWaTKNbWFKTPNRVMIRUNKRWT|JNWSNWaTKNbWFKVREJTPLOZVJMUQ|JNWSNWaTLOdaEJbWJMUQMRVMIRaV|JNWSNWaTLOeaFJbWJNURNUYRKNRK|JNWSNWbSEJfbKObWGKURLPSLPGWS|JNWSNWbSEJUQKOZUJNSJFMQJOTXO|JNWSNWbSIMaWMQWTKNSJENfbAEbW|JNWSNWbSIMebMQSOLSVOKTXOEJbW|JNWSNWbSIMfbMQbWEIURAEZUQZdU|JNWSNWbSLOSLHOfbEJVRJNUQNUYR|JNWTEJaWBETPNRVMJQUREJXTLObX|JNWTEJaWLOdaGLTPAEPGCLVSOVaR|JNWTEJaWLPeaAEVRJMUQMeQMIRda|JNWTEJaWLPeaAEVRJMZVEJUQNUQZ|JNWTEJbWAEUQNSVOLbfWHLTPLOWT|JNWTEJbWAEVRLPaVGLWSPWSbLOUQ|JNWTEJbWJMebMRVMIRTPAEUQEJWS|JNWTEJbWJMfbMQTOKTXOLSVOIMUR|JNWTEJbWJMfbMRVMIRTPAEUQEIZU|JNWTEJbWJMfbMRVMIRTPAEUQLOWT|JNWTEJbWJMfbMRVMIRTPAEWTEIbW|JNWTEJbWJMfbMRVMIRTPAEWTEJbW|JNWTEJbWJMfbMRVMIRTPAEWTEJUQ|JNWTEJbWJMfbMRVMIRTPAEWTEJZV|JNWTEJbWJMfbMRVMIRTPAEWTLOaV|JNWTEJbWJMfbMRVMIRTPLOWTAEZV|JNWTEJbWJMTPMQURNUYRAEfbLOcY|JNWTEJbWJMTPNRUNKRWSMQVMQJfb|JNWTEJbWJMTPNRUNKRZUFKUNKRXT|JNWTEJbWJMUQNRQJFMfbLOZUMQUN|JNWTEJbWJMUQNRQJFMfbMQVMQJTO|JNWTEJbWJMURNUZJFMfbAEdZKOTK|JNWTEJTOKTXOLSVOAEURNUYRJNRK|JNWTEJTOKTXOLSVOIMOKFOURNUYI|JNWTEJTOLSVOKTXOAEURNUYRJNRK|JNWTEJTPBEbWJMUQNRQJFMWTKNTO|JNWTEJTPJMbWBEUQNRQJFMWTMQVM|JNWTEJTPJMbWMQURNUYRAEfbKOWS|JNWTEJTPJMbWMQURNUYRAEfbLOcY|JNWTEJTPJMbWMQURNUYRAEfbLOWT|JNWTEJTPJMbWMQURNUYRLOfbOTXO|JNWTEJTPJMbWMQWTLOURNUYRAEaW|JNWTEJTPJMbWMRVMIRfbLOWTAEaV|JNWTEJTPJMbWNRUNKRWSAEfbMQVM|JNWTEJTPJMbWNRUNKRWSMQVMQJfb|JNWTEJTPJMbWNRUNKRZUFKUNKRdZ|JNWTEJTPJMbWNRUNKRZUFKUNKRXT|JNWTEJTPJMbWNRUNKRZULOUNFKPL|JNWTEJTPJMUQNRQJFMbWAEWTMQVM|JNWTEJTPJMUQNRQJFMbWBFWTMQVM|JNWTEJTPJMUQNRQJFMbWMQVMQJYU|JNWTEJTPJMVSNWbSMQfbFJbWIMWT|JNWTEJTPJMXTMQTOKTPWGKbXAEXT|JNWTEJTPJMXTMQTOLSVOKTPWAEWT|JNWTEJTPJMXTMRVMIRZVAEVMEIaW|JNWTEJTPJMXTMRVMIRZVAEVMEIcZ|JNWTEJTPJMXTNRUNKRTOLSVOAEbX|JNWTEJTPJMXTNRUNKRTOLSVOFKOF|JNWTEJTPJMXTNRUNKRZUFKUNKRbW|JNWTEJTPLOVRBEbWJMWTMVZJENUQ|JNWTEJTPLOVRBEbWJMWTMVZLHOaV|JNWTEJTPLOVRJMUQMVZJFMQJBFYU|JNWTEJUQAETPLObWNSWNKRVMIRfb|JNWTEJURNUZQAEYUJNVREJTPLOcY|JNWTEJVRBEbWJMTPMVZJFMUQLOQJ|JNWTEJVRJMUQMVZJFMQJBEYUENUQ|JNWTEJVRJMUQMVZJFMQJKOTKGEXT|JNWTEJVRJMUQNUQJFMZJBEYUENUQ|JNWTEJVRLObWBEaVJMVSMVSLHOZJ|JNWTFJTPBFbWJMWTNRUNKRVSMQSO|JNWTFJTPBFVRJMZVMQcZLObWHLeb|JNWTFJTPJMXTMRVMIRbXLOZVEIVM|JNWTFJUQBFTPLObWOTXOKTfbTXZU|JNWTFJVRJMZVMQcZLOTPCFbWEJeb|JNWTLObWHLTPNRUNKRVMIRfbEJZV|JNWTLObWHLTPNRUNKRVMIRWTEJTK|JNWTLObWHLUQNRVMIRTPEJWTJMQJ|JNWTLObWHLUQNSWNKRVMIRTKGNfb|JNWTLObWNRUNKRVMIRTKGNfbFKXT|JNWTLObWNRUNKRVMIRTKGNXTHLfb|JNWTLOVREJaVBEbWJMUQNUQJENZQ|JNWTLOVREJbWJMUQNUQJFMZJBEJF|JNWTLOVREJTPJMUQMVZJFMQJBEYU|JNWTLOVREJTPJMUQNUQJFMZJBFYU|JNWTLOVRFJbWJMfbMVZJENURNUYR|JNWTLOVRFJbWJMfbMVZLHOTPIMWT|JNWTLOVRFJbWJMTPMVZJENUQAEWT|JNWTLOVRFJbWJMTPMVZJENUQOSWT|JNWTLPUQPWbJENXTAEfbHLTPEJYU|JNWTLPUQPWbJENXTAETPHLYULOVS|JNWTLPUQPWbJENXTAETPKOfbFKbX|JNWTLPUQPWbJENXTAEYUHLTPLOVS|JNWTLPUQPWbJENXTHLTPAEfbEJYU|JNWTLPUQPWbJENXTHLTPAEfbLObX|JNWTLPUQPWbJENXTHLTPAEYULOVS|JNWTLPUQPWbJENXTHLTPFJfbKOZU|JNWTLPUQPWbJENXTHLTPLOfbAEbX|JNWTLPUQPWbJENXTHLTPLOfbAEYU|JNWTLPUQPWbJFMQJENYUAEVRHLXT|JNWTLPUQPWbJFMQJENYUHLfbAEbW|JNWTNRUNKRVMIRaWFKdaLOaVRaWd|JNWTNRUNKRVMIRaWGKTPLOPLOTXO|JNWTNRUNKRVMIRaWLOTKFOWTHLTK|JNWTNRUNKRVMIRTOLSZURVaRFKRM|JNWTNRUNKRVMIRTOLSZURVaRGKcZ|JNWTNRUNKRVMIRTOLSZURVaRGKRM|JNWTNRUNKRVMIRTOLSZURVaRGKUQ|JNWTNRUNKRVMIRTOLSZURVaRHLRM|JNWTNRUNKRVMIRTOLSZURVaRHLUQ|JNWTNRUNKRVMIRTPEJbWAEfbJNWT|JNWTNRUNKRVMIRTPEJbWAEWTJNaW|JNWTNRUNKRVMIRTPEJZUJNdZAEXT|JNWTNRUNKRVMIRTPLObWEJWTHLTK|JNWTNRUNKRVMIRTPLObWHLWTEJTK|JNWTNRVMIRUNKRaWGKTPLOPLOTXO|JNWTNRVMIRUNKRTOLSZURVaRGKRM|JNWTNRVMIRUNKRTOLSZURVaRGKUQ|JNWTNRVMIRUNKRTOLSZURVaRHLRM|JNWTNRVMIRUNKRTOLSZURVaRHLUQ|JNWTNRVMIRUNKRTPFKbWEIWSLOSL|JNWTNRVMIRUNKRZUFKUNKRaWGKdZ|JNWTNSVOLSaVKOTKFObWSbfWEJWT|JNXTEJbXJMVSMQSJFMTPAEfbLOWT|JNXTEJTOLSVOKTWPAEaVHLbXLOfb|JNXTEJTPJMWSNWbSMQfbAEaWIMUR|JNXTEJTPJMWSNWbSMQSOKTPWLPfb|JNXTEJTPLOUQOTZUTXVRHLaVLOWS|JNXTLObXHLfbLPVSOVZJENTOKTXO|JNXTLObXHLTPNRUNKRVMIRfbEJWS|JNXTLObXHLTPNRUNKRVMIRfbEJWT|JNXTLObXHLTPNRUNKRVMIRfbEJZV|JNXTLObXHLTPNRUNKRVMIRWSOVZS|JNXTLObXHLTPNRUNKRVMIRWTEITK|JNXTLObXHLTPNRUNKRVMIRWTEJTK|JNXTLObXHLUQNRVMIRTPEJWTJMQJ|JNXTLObXHLUQNSWNKRTKGNVMIRfb|JNXTLObXHLUQNSWNKRVMIRTKGNfb|JNXTLObXHLUQNSWNKRVMIRTKGNXT|JNXTLObXNRUNKRVMIRTKFOWSOVZS|JNXTLObXNRUNKRVMIRTKGNfbHLXT|JNXTLObXNRUNKRVMIRTKGNXTHLfb|JNXTLObXNRVMIRUNKRTKGNfbFKXT|JNXTLOTPOTVSTXSJENWSNWbSIMfb|JNXTLOTPOTVSTXSJENWSNWbSIMSO|JNXTLPbXGLVRLOaVHLWSNWTaEJUQ|JNXTLPbXGLVRLOaVHLWSPWSbLPUQ|JNXTLPbXGLVSDGSJENebAEaVNRVM|JNXTLPbXGLVSDGSJENURNUYRAEeb|JNXTLPbXGLVSDGSJFMUQBFQJENaV|JNXTLPbXGLVSLOSLPGTOKTXOGKWT|JNXTLPbXHLVSDHSJENUQAEZUEJaV|JNXTLPbXHLVSDHSJENURNUYRAEeb|JNXTLPbXHLVSDHSJFMURMVaREJeb|JNXTLPbXNRUNKRVMIRebEJZUJNcZ|JNXTLPbXNRUNKRVMIRTOEJebJMZV|JNXTLPbXNRUNKRVMIRZVEIVMIReb|JNXTLPbXNRUNKRVMIRZVEJVMJQTO|JNXTLPbXNRVMIRUNKRZVEIVMIReb|JNXTLPUQEJVSAEbXIMZUEIaVGLeb|JNXTLPUQEJZUGLbXLOURNUQZJMVS|JNXTLPUQEJZUGLVRLObXHLaVDHeb|JNXTLPUQEJZUHLVSBEaVDHbXNRVM|JNXTLPUQFJVSGLbXLOSLPGTOKTWP|JNXTLPUQGLbXLOZUHLVRIMQSOMaV|JNXTLPUQGLYULObXHLVSOVZJFMQJ|JNXTLPUQGLZUDGbXEJURNUQZJNYU|JNXTLPUQGLZULObXEJURNUQZJMVS|JNXTLPUQGLZULObXHLURNUQZEJYU|JNXTLPUQGLZULObXHLURNUYREJRM|JNXTLPUQGLZULObXHLURNUYRKNRK|JNXTLPUQGLZULObXHLURNUYRKNTK|JNXTLPUQGLZULObXHLVRIMQSOMeb|JNXTLPUQHLVSDHSJFMQJENZUIMbX|JNXTLPUQHLVSDHSJFMQJENZUIMUR|JNXTLPUQHLVSEJbXDHYUIMZVAETO|JNXTLPUQNRVMIRaVRaeVKNVSEISJ|JNXTLPUQNRVMIRZUEIUNKRQMRUYR|JNXTLPUQNRVMIRZUKNTOGKbXKTXO|JNXTLPUQNRVMIRZUKNTOGLWSNWbS|JNXTLPUQNRVMIRZURVaRKNRKFXcZ|JNXTLPUQNRVMIRZURVaRKNRKFXUR|JNXTLPUQNRVMIRZURVaRKNRKFXWS|JNXTLPVREJaVHLbXLOWSPWSbGLUQ|JNXTLPVREJbXGLZVLOUQNUQZHLVR|JNXTLPVREJbXHLaVLOWSPWSLGPVS|JNXTLPVREJbXJMTOMVZJKTXOFMeb|JNXTLPVRFJbXJMTOMVZJENOFBKeb|JNXTLPVRGLaVLObXEJWSPWSbHLUQ|JNXTLPVRGLaVLObXHLWSPWSbLPUQ|JNXTLPVRGLbXEJaVAEWSNWTaJNVS|JNXTLPVRHLaVEJbXJMWSNWTaMQfb|JNXTLPVSEJUQGLbXLOSLPGTPAEWT|JNXTLPVSGLSJFMbXLOUQBFQJFMaV|JNXTLPVSHLSJENZVAETOLQWTPWbA|JNXTLPVSHLSJENZVLObXFJUQGLYU|KNVRFKWSNWbSJMRNKRUNLOSLHOaV|KNVRFKWTJMaVEJTOLSVFBKdaMVaR|KNVRFKWTJMTPMVZJENUQLObWAEWT|KNVRFKWTJMTPMVZJENUQLObWBEWT|KNVRFKWTJMTPMVZJENUQLObWOSWT|KNVRGKZVJMUQNUQZMRVMIRWSLOSL|KNVRGKZVJMUQNUQZMRVMIRWTKNTP|KNVRGKZVJMWTDGTPMQdZLObWGLPG|KNVRGKZVJMWTDGUQNUQZMRVMIRTP|KNVSIMUQEIXTLPbXMRTOGKebKTXO|KNVSIMXTEITPMRWTNWUEAJbSIMZV|KNVSIMXTFKTOKTWPNWbSMQUREIaV|KNWSNWbSIMXTLPTOMQUREIRMIRVM|KNWSNWbSIMXTLPTOMQUREIRNJMfb|KNWSNWbSLPebGLSOLSVOPTOKFObW|KNWSNWbSLPebGLUQIMYUFKUREIbW|KNWSNWbSLPebJMbWEJfbMQXTGLbX|KNWSNWbSLPebJMbWHLfbMQSOLSWN|KNWSNWbSLPebJMUQMRVMIRbWFJZV|KNWSNWbSLPfbJMbWMQSOEJWTPWaT|KNWTFKbWJMTPMRVMIRWSNWUNKRaT|KNWTFKbWLPVSGLTOKTXOPTWGDTaW|KNWTFKTPBFbWJMfbNRUNKRWTMQVM|KNWTFKTPBFbWJMUQNRQJENVMIRWT|KNWTFKTPBFbWNRUNJbfWIMYUMQWT|KNWTFKTPBFUQNRVMIRXTJMQJFMTO|KNWTFKTPBFVRJMbWMVZJENUQLOWT|KNWTFKTPJMXTMRVMIRbXEIaWAEWS|KNWTGKbWDGVSLOSLHOTPNRUNJbfW|KNWTGKbWJMVRMVZJENebAEUQIMQA|KNWTGKTPLOVRJMPLMVZJFMLSCFSO|KNWTJMTPMRVMIRXTEIUQAEZUEJaW|KNWTJMTPMRVMIRXTFKbXLOZVEIVM|KNWTJMTPMRVMIRXTLOTKFObXGLPG|KNWTJMVRMVaKGNbWEJTPAEPGCLea|KNWTJMVRMVaKGNbWEJZVAETPNRVM|KNWTJMVRMVaKGNeaIMZVEIURNUYR|KNWTJMVRMVaKGNTPDGURNUYREJbW|KNWTLPbWNRUNJbfWEJVSJMYUMQSN|KNWTLPURNUYRPWbSJNRKGWaTEJfb|KNWTLPVRPWRKGNaTIMTPFKXTHLPG|KNWTLPVRPWRKGNbSNWaTJNTOIMZV|KNXTLPVSGKbXDGTOKTXOGKfbKTbX|KNXTLPVSGKbXDGUQNRSOJNZUEJcZ|KNXTLPVSGKZVHLcZLOSLPGTOKTWP|KNXTLPVSIMbXMQTOEIURNUYRJMaV|KNXTLPVSIMbXMRTOGKebKTXODGbX|KOUQGKWSJNSJENZUDGVRIMQSOMUR|KOUQGKWSJNSJENZUOTXOLZcVAEbW|KOUQGKWTLPYUPWbLHOfbDGbWGLcY|KOUQGKYULPWSJMQJEWbLPGfbAEbW|KOUQJNVSOVaKFOWTEJTKGNbWBEZV|KOUQJNVSOVaKGNYUEJZVBEVRFKdZ|KOUQJNVSOVaKGNYUFKZVDGVRLOWT|KOUQJNWSNWaKFObWEJWTOSVOLSea|KOURFKYUJNWTLPVSOMZVPWbQIMQJ|KOURGKYUJNWSNWaTEJUQLPeaPWbL|KOURGKYUJNWSNWaTLPUQPWbLHOfb|KOURGKZUJNWSNWaTEJeaJMbWFJWS|KOURGKZUJNWSNWbSOTXOKTfbTXcZ|KOWTFKTPBFUQJNbWOSVOLbfWHLWT|KOWTFKTPBFURJMYUMQcYEJRMIRUE|KOWTGKTPDGbWOTXOLbfWJNWSNWaT|KOWTGKTPDGUQJNYUEJVRNSaVJNea|KOWTGKTPKNPGCLbWFKWSNWaTJNTP|KOWTJMTKFOaWBFWTGKTPDGdaMRVM|KOWTJMTKFOaWGKWTBFTPDGdaMRUN|KOWTJMTKFOaWGKWTBFTPDGdaOSVO|KOWTJMTKFOaWGKWTBFTPDGeaEJUQ|KOWTJMTKFOaWGKWTBFTPDGUQMRVM|KOWTJMTKFOaWGKWTBFUQOSQJENVO|KOWTJMTKFOaWGKWTBFUROSVOLSda|KOWTJMTKFOaWLPeaHLWTPWaKGNVS|KOWTJMTKFObWGKWTBFTPDGUQEJYU|KOWTJMTKFObWMRUNOSVOLJWSHLYU|KOWTJMTKFObWMRUNOSVOLJXTIMfb|KOWTJMTKFObWMRVMIRUNOSNKSbfW|KOWTJMTKFObWOSVOLbfWMQUREJWS|KOWTJMTKFObWOSVOLbfWMQXTEJUR|KOWTJMTKFObWOSVOLbfWMQXTIMWS|KOWTJMTKFOUQMRVMIRZVEIVMIRcZ|KOWTJMTKFOUREJbWGKZUJNUQNUQZ|KOWTJMTKFOURGKbWMQWSLPSLHOaW|KOWTJMTKFOURGKbWMQWTLPebPWbL|KOWTJMTKFOURMQbWGKWSLPSLHOeb|KOWTJMTKFOURMQbWGKWTLPebPWbL|KOWTJMTKFOVRMVaREJUQBFZUJMQJ|KOWTJMTKGNVRMVaKFObWEJUQDGZV|KOWTOSVOLSTPHLaVLOeaFKUQJNYU|KOWTOSVOLSURJMYUMVaRFJeaJMaV|LOUQHLYULPVSOVZSIMaVKNcYEISO|LOUQHLYULPVSOVZSJMQJENSJFMWT|LOUQJMQJFMWSHLYUMRUNKRVMIRbW|LOUQJMQJFMWTMRVMIRbWEJTPAEWT|LOUQJNWSNWbLGPfbEJbWHLYUAEUR|LOUQJNWSNWbLHOfbKNVRNUYREJbW|LOUQJNWSNWbLHOfbKNVRNUYREJZV|LOUQJNWSNWbLHOfbKNZUNScZEJaW|LOUQJNWSNWbLHOfbKNZUNScZEJUR|LOUQJNWSNWbLHOfbKNZUNScZOTXO|LOUQJNWSNWbLHOfbKNZUNSVRSVRM|LOUQJNWSNWbLHOfbKNZUNSVRSVRN|LOURJMWSEJSLHObWJNfbNUZJFMWS|LOVRJMaVHLWTLPUQPWbLGPQJEUZQ|LOVRJNWTFJTPJMZVMQcZGLPGCLbW|LOWSGLbWKNUQFKZUBFURNUQZKNZU|LOWSGLbWKNURNUYRJMRNLPSLPGXT|LOWSGLbWKNURNUYRJMWTEJTKFOaW|LOWSGLbWKNURNUYRJMWTEJTKFOfb|LOWSGLbWKNURNUYRJMWTEJTKFORN|LOWSGLbWLPSLPGWSJMfbMQSOKTXO|LOWSGLbWLPSLPGXTHLTPJNVREJZV|LOWSHLbWJMUQMRVMIRSNRUYROSXT|LOWSHLbWJMUQMRVMIRSNRVaROSXT|LOWSHLSNJSXTOXVHIMbWEJfbAEWS|LOWSHLSNJSXTOXVHIMbWEJWSKNaW|LOWSHLSNJSXTOXVHIMbWMRUNKRWS|LOWSHLSNJSXTOXVHIMURMVaREJYU|LOWSHLSNJSXTOXVHIMZVEIURAEbW|LOWSHLSNJSXTOXVHIMZVEIURAEcZ|LOWSHLSNJSXTOXVHIMZVMQVSQZcV|LOWSHLUQKNZUNWaKFObWLPeaGKWT|LOWSHLURJNSJEUYRLPbWOTXOKTZU|LOWSHLXTOXSNJSVHIMbWEJUQMRZV|LOWTJMbWEJWSAESLGWaTCGTPMRUN|LOWTJMbWEJWSBESLGWaTJNfbDGbW|LOWTJMbWEJWSBESLGWaTJNfbDGUR|LOWTJMbWEJWSBESLGWaTJNfbMRVM|LOWTJMbWEJWSBESLGWaTJNTPDGXT|LOWTJMbWEJWSBESLGWaTJNTPMRVM|LOWTJMbWHLTPMRUNKRVMIRWTEJTK|LOWTJMbWMRUNKRVMIRTKGNebHLWS|LOWTJMbWMRUNKRVMIRTKGNfbFKXT|LOWTJMbWMRUNKRVMIRTKGNfbHLWT|LOWTJMbWMRVMIRUNKRTKGNfbFKXT|LOWTJMUREJbWJNfbNUZJFMTPMQWT|LOWTJMUREJbWMQTPOTXOKTWSTXRM|LOWTJNbWNRUNKRVMIRTKGNXTCGfb|LOWTJNbWNRVMIRUNKRTKGNebFKWS|LOWTJNVRFJTPJMUQNUQJENZQAEdZ|LPUQGLYUDGcYJMQJFMWTPWbSBFfb|LPUQGLYUDGVRJNZVEJcYLORMIRVM|LPUQHLWSKNbWFKZUKOURNUQZGKYU|LPUQHLYUKOVRJMQJFVaRDHeaOSWN|LPUQHLYUKOWTPWaKFObWLPeaGKWT|LPUQJNWTPWbJENXTHLTPAEfbLObX|LPURJNWSNWaTPWbSKNRKGWebFKbS|LPVRHLZVLOWTPWbLGPfbKObWFKWS|LPVRJMUQMVaREJZUJMQJFVWTPWbZ|LPVSHLXTKOTKFVaRJMZVMQcZLOea|LPVSHLXTKOTKFVZSGKSNKRUNJSWN|LPVSHLXTKOTKFVZSGKURKOSNJSWN|LPWSGLSOKTXOLSVOJMbWMQUREJfb|LPWSGLSOLSVOKTXOIMZVMRVMJZcV|LPWSIMUREISOKTXOGLYULSVOMVaR|LPWSJMSOKTXOMQbWEJfbJMVRMVZS|LPWSJMSOKTXOMQbWEJWTPWaTJNUR|LPWSJMSOKTXOMQbWFJURJMfbEJbX|LPWSJMSOKTXOMQUREJbWJMfbGLWS|LPWSJMSOKTXOMQUREJbWJMfbGLYU|LPWSJMSOKTXOMQUREJRMIRVMGLaV|LPWSJMSOKTXOMQUREJRMIRVMJNMI|LPWSJMSOKTXOMQURFJbWJMWSGLYU|LPWSJMUQEJZUKNcZNWbSBEfbFKSN|LPWSJNSJFMaWMQWTPWbSEJfbKNbW|LPWSJNSJFMaWMQWTPWbSIMSOKTXO|LPWSJNSJFMXTPWbSHLfbBFbXLPSN|LPWSJNSJFMXTPWbSMQURHLfbBFbW|LPWTPWbSGLSOKTXOLSVOIMZVMRVM|LPWTPWbSIMfbKNbWMRVMJQSJENaV|LPWTPWbSIMfbMQSOKTXOEIbWJMWT|LPWTPWbSIMUQEIZUBEURJNSJEUQZ|LPWTPWbSIMUQEIZUHLebKNcZNWbS|LPWTPWbSIMUREISOKTXOGLYULSVO|LPWTPWbSIMUREISOKTXOMQfbJMaW|LPWTPWbSIMXTKNTPNWaTMQfbJNbW|LPWTPWbSJMXTMQTPIMSOKTPWFKUR|LPWTPWbSJMXTMQTPIMSOKTPWFKVR|LPWTPWbSJNSJENXTAEVREJTPHLfb|LPWTPWbSKNaWGLXTFKTPKOPGCLUR|LPXTKOTKGNVSFKaVHLbXLOSLPGeb|LPXTKOTKGNVSHLaVLOSLPGbXJMWT|LPXTKOTKGNVSHLaVLOSLPGeaJMWS|IMUQEIYUAEVSKNXTLOTRMOURGKbXJN|IMUREIWTLObWAEZUMQWSQZdUJMSLGd|IMURMQRMJNMINRVMQJYULOURJMWTMV|JMUQMRVMIRWTEJbWLOTPOTXOKTWSTX|JMVSMQURKOaVEJWTAETKGWbSLOSLHO|JMVSMQURKOaVEJWTJMTKGWbSLPdaCG|JMVSMQURKOaVEJWTJMTKGWbSLPebCG|JMWSLPSOKTXOMQbWEJWTPWaTAEVSIM|JMWTMQTOLSVOKTXOEJURJNRKGNbXAE|JNUQNRVMIRWTEJTPLObWJNZUOTXOKT|JNUQNRVMIRWTLObWEJTPAEWTJNZUOS|JNUQNRVMIRZVEIVMIRcZAEZULOUNKR|JNURNUYREJWTJNRMIRVMAEMILOTPNR|JNVREJZVJMUQNUQZAEXTLPWSPNVRMV|JNVSFJaVKOUQGKZUCGURNUQZKNYUIM|JNWTEJbWJMUQNRQJFMfbMQVMQJTOLS|JNXTLPbXGLVSDGSJFMUQBFQJENYUNS|JNXTLPbXNRVMIRUNKRebEJZUJNcZHL|KNWTLPVRPWRKGNaTIMbWCGTPFKeaBF|LOWSHLaWKNUQFKZUCFURNUQZKNYUIM|LPUQJNQMIRVMEIZVIRVMAEMINRcZEJ|LPWSKOSLHOURJMbWFKWSGLSNCGfbBF|IMUQEIVSKOaVFKZUJNQJNEWTIMTPEIUR|IMUQEIVSKOaVFKZUKNURNUQZMQYUGKWT|IMUQEIVSKOaVFKZUKNVROVRaBEXTMRTP|IMUQEIVSKOYUOVZSBEXTFKTPKNaVNRUN|IMUQEIWSKObWGKWTLPSLPGfbJNQSKOTK|IMUQEIWSMRVMIRbWAEfbLOSLGPWSKOSL|IMUQEIWTLPbWMRVMIRTOKTXOAEfbGKZV|IMUQEIWTMRVMIRTPLObWJNWTRUYRNUQM|IMUQEIWTMRVMIRZVAEVMEIcZIRZVJMQJ|IMUQEIXTMRVMIRTPAEbXLOWTEIfbJNZV|IMUQEIYUAEURKNRKGNVRNUaVUYVSLOSL|IMUQEIYUAEURKNRKGNVSFKaVDGcYBFda|IMUQEIYUAEURKNRKGNVSFKZUDGcYBFdZ|IMUQEIYUAEURKNRKGNVSFKZUDGdZLOSL|IMUQEIYUAEVSKNaVGKeaLPXTHLURNUTO|IMUQEIYUKNcYFKWTBEaWLPeaGLTOKTXO|IMUQEIYUKNVRMVaKFOWTGKTPDGZVBFea|IMUQEIYUKNVRMVaKFOWTGKZVBFdZLPUR|IMUQEIYUKNWSNWaTBEURFKZUKNRKGNUR|IMUQEIYUKNWSNWaTLOTKGNVSNWbSFKXT|IMUQEIYUKNWSNWaTLOTKGNVSNWbSFKZV|IMUQEIYULOURGLZUDGcYLPWTPWbLGPfb|IMUQEIZUAEURKNRKGNVRMVaKFOeaDGWT|IMUQEIZUAEURKNRKGNVRNUQZJNWTEJTP|IMUQEIZUAEURKNRKGNVRNUQZJNXTEJTP|IMUQEIZUAEURKNRKGNWSNWbSMRVMIRcZ|IMUQEIZUAEURKNRKGNXTMRVMIRbXDGTP|IMUQEIZUAEVRMVaRLOWTJNcZOSbWSbfW|IMUQEIZUAEVSLOSLHOURMVaROSWNJSea|IMUQEIZUAEWSMRUNKRVMIRdZLOSLHOaW|IMUQEIZUAEWSMRVMIRUNKRaWLOSLHOWT|IMUQEIZUAEWSMRVMIRUNKRdZLOSLHObW|IMUQEIZUBEURLOWSJNSJEUYRHLQJFMbW|IMUQKNVRMVaKGNZUDGURNUQZFKWTJNea|IMUQKNWSNWaTEIZUBEURFKYUKNRKGNUR|IMUQKNWSNWaTLOTKGNbWHLebDHYUFKWT|IMUQKNWSNWaTLOTKGNbWHLWTMRVMEIea|IMUQKNWSNWaTLOTKGNbWHLWTNRTPRaPG|IMUQKNWSNWaTLOTKGNbWHLXTEIVSFKfb|IMUQKNWSNWaTLOTKGNbWHLXTLPWSPWSb|IMUQKNWSNWbSFKYUJNQJNWaTENTPAEXT|IMUQKNWTGKTPDGbWEIVSMRZUBEfbIMdZ|IMUQKNWTLPYUPWbSNWaTFKTOKTXOEIfb|IMUQKNWTNSVOLSaVGLVOLSeaDGaVGLVO|IMUQKNXTLPbXEITOGKZUKTXOMRVMIRcZ|IMUQKNXTLPbXEITOMRVMIROKFOZVCFVM|IMUQKNXTLPVSMRTOGKbXKTXORVaKJMQJ|IMUQKNXTNSVOLSWNJSQJENYUAETPEJUQ|IMUQKNXTNSWNJSVOLSQJENbXAETPEJYU|IMUQKNYUFKVRMVaRNSWNJSRMKOeaCFaV|IMUQKNYUNSWNJSQJENVOLSbWSbfWAEZV|IMUQLPWTPWaTKOTKGNbWHLWTCGTOLSVO|IMUREIWSKObWFKWTLPSLPWaTGWeaHLaT|IMUREIWTJNbWNUZJFMfbAEdZMQTPIMWS|IMUREIWTLOTPAEbWOTXOKTZUFKUQKNRK|IMURMQRMEIWTIRVMJNMILOaVNRVMQJbW|IMURMQRMJNMIEJWTLPYUPWaTHLbWAETP|IMURMQRMJNMINRVMQJYUJNUQEJZVLOWT|IMURMQRMJNMINRVMQJYUJNUQLOWTEJaV|IMURMQRMJNMINRVMQJYULOURJMWTMVZL|IMURMQRMLPWSEISOIRVMKTXOJNMIAEbW|IMURMQRMLPWSHLSOLSVOKTXOEIZVIRVM|IMURMQRMLPWTPWbSHLMIJNSJENfbAEbW|IMURMQRMLPWTPWbSJNSJENMIHLfbNRVM|IMURMQWTLObWJNTPNUYREJRMJNMINSWN|IMURMQWTLPTOKTXOEIRMIRVMJNMIGLaW|IMVRMVaRLPZVGLWTPWbSKNRKFOURLPSL|IMVSEIWTKOTKFVZSMQXTQZcVIMbWGKTP|IMVSEIWTKOTKFVZSMQXTQZcVIMTOGKOF|IMVSKNXTMQaVEITPFKWTNWTaAEbWJNUR|IMVSKNXTMQbXFKaVJMSJMFTPEJfbAEea|IMVSKNXTMQTPFKaVKObXGKPGCLebJMSJ|IMVSKNXTMQTPFKbXJMSJMFUREJRMJNMI|IMVSMQWTKNTPNWbSJMfbFKbWEJaVJNSJ|IMWSLPbWGLUQKNVRMOWTPWaREIZVLOfb|IMWSLPbWGLUQKNVRMOWTPWaREIZVLPfb|IMWSMQSOLSVOKTXOEIaVJMbXFJfbCFXT|IMWSMRVMJQURKOaVEIbWFJdaJMRNBEWT|IMWTMQaWLPeaEITOKTXOJMWTPWbSAEfb|IMWTMQTPJNbWEJWTAETOLSVOKTPWFKaV|IMWTMQTPJNbWNRUNKRVMQJaVJMWSEJYU|IMWTMRUNKRVMJQTPEJbWLOWTAETKFOfb|IMWTMRVMJQTPEJbWJNWTAEaWEJWSNWTa|IMXTLOUROXRIHLWSJNSJENbWAEYULPUQ|IMXTLOUROXRIHLYULPUQGLZUJNcYEJUR|IMXTLOUROXRIJNYUHLUQLPcYEJZUGLVR|IMXTLOUROXRIJNYUHLUQLPWSNWbSEJfb|IMXTMQTOKTWPJNbWEJfbAEWTGKPGCLTP|IMXTMQTPJNWSNWbSEJfbAEaWEIURJNSJ|IMXTMQTPJNWSNWbSEJfbAEaWKObXEIUR|IMXTMQTPJNWSNWbSEJfbAEbWEIURJNSJ|IMXTMQTPKNVSFKbXJMSJMFUREIfbLOZV|IMXTMRUNKRVMJQTPEJWTLOTKFObWJNWS|IMXTMRUNKRVMJQWSLPTOEJYUAEUREIZV|IMXTMRVMJQTPEJbXJNWTAEaVNRVMQJUQ|IMXTMRVMJQTPEJbXLOWTJNURNUYRAEfb|IMXTMRVMJQTPEJWSAEbWKOaVOTdaJMfb|JMUQEJWTAETOKTXOLSVOGLaWLSWNJSQA|JMUQEJWTLPTOKTXOMRVMIRbWAEfbJNZV|JMUQEJZUKOURFKWSLPSLHObWBEWSDHSL|JMUQFJWSLPZUJNSJMFURHLbWLOYUEJcY|JMUQFJWSLPZUJNSJMFURHLYUEJcYLORM|JMUQFJWTBFTPMRVMIRbWJMQJFMWTEIaW|JMUQFJWTBFTPMRVMIRbWLOWTJNfbEIZU|JMUQFJYULPURHLZUDHWSJNSJMFbWEJcY|JMUQFJZUBFURKOWSGKbWLPSLPGWTHLTP|JMUQLOQJFMWTEJbWBFTPMQWSAESLHOfb|JMUQLOQJFMWTMRVMIRbWEJTPAEWTEIfb|JMUQLOQJFMWTMRVMIRTPEJbWAEWTEIaW|JMUQLOQJFMWTMRVMIRTPEJbWAEWTEIfb|JMUQLOQJFMYUMRUNKRVMIRWTEJTKGNbW|JMUQLPQJFMVSMQSOKTXOEJWSJMYUBEaV|JMUQMRVMIRWSEJbWAEfbLOSLGPWSKOSL|JMUQMRVMIRWSEJbWBEfbLOSLHOZUJMQJ|JMUQMRVMIRWSEJSOLSZVSZdEAJXTHLTP|JMUQMRVMIRWSLOSLHObWEJWSOVZSKOSL|JMUQMRVMIRWSLOSLHObWEJWTDHTPJMQJ|JMUQMRVMIRWSLOSLHObWKNfbGLWTLPTK|JMUQMRVMIRWTEJbWAETPEIWTJMQJFMZU|JMUQMRVMIRWTEJbWAETPEIZUJMQJFMUN|JMUQMRVMIRWTEJbWLOZUJNdZAEaVRaWd|JMUQMRVMIRWTEJTPAEbWLOWTJNZUEJfb|JMUQMRVMIRWTEJTPLObWJNWTRUYRNUQM|JMUQMRVMIRWTEJZVAEVMEIcZIRZVJMQJ|JMUQMRVMIRWTKNbWFKTPLOWTBFfbHLZU|JMUQMRVMIRWTKNbWFKTPLOZUEJWTAEaV|JMUQMRVMIRWTLOaVRaeVEJYUJNVRAEda|JMUQMRVMIRWTLObWEJfbAEZUJNdZNSWN|JMUQMRVMIRWTLObWEJTPAEWTJNZUOSfb|JMUQMRVMIRWTLObWEJTPOTXOKTWSTXZU|JMUQMRVMIRWTLObWEJZVAEVMOSWNKIYU|JMUQMRVMIRWTLOTPEJbWOTXOKTZVJMQJ|JMUQMRVMIRZULOUNKRWTFKbWEJdZAEWS|JMUQMRVMIRZVEIVMIRdZAEZULOUNKRWT|JMUREJWSAEaWLPeaGLSNJSWGDKaWKOWS|JMUREJWSAEbWMQRMIRVMLOSLHOZVJNMI|JMUREJWSAESOKTXOLSVOMVZSIMOLHVaI|JMUREJWSKOaWMQWTJMTKGWbSLPebHLSN|JMUREJWSKObWAEWTLPTKGWaTPWebFKbS|JMUREJWSKObWFKWTAETPBFZUMQebQZdU|JMUREJWSKObWFKYUMQebJMWTLPSLPWbS|JMUREJWSKObWGKWTLPSLPWaTHOfbAEda|JMUREJWSKORNAEbWFKZUKRUNLPSLJZcV|JMUREJWSKORNAEbWLPSLJbfWHOVRMVZL|JMUREJWSMQRMIRVMKOMIOVaRAERMGKXT|JMUREJWTJNbWNUZJFMfbLOdZAETPMRVM|JMUREJWTJNbWNUZJFMfbMQdZIMTOLSVF|JMUREJWTJNbWNUZJFMfbMQdZKNTPNRVM|JMUREJWTLObWAETPMQWSJMSLHOfbFJbW|JMUREJWTLObWJNfbNUZJFMdZMQYUAEUR|JMUREJWTLObWJNfbNUZJFMTPMQWTAEdZ|JMUREJWTLObWJNTPNUZJFMWTMQfbAEbW|JMUREJWTLObWMQfbAETPHLWSOTXHKNRK|JMUREJWTLObWMQRMIRVMGLMILPZUQZcV|JMUREJWTLObWMQRMIRVMJNMIAEebFJTP|JMUREJWTLObWMQTPJNWTNUYRAEcYFJRM|JMUREJWTLObWMQTPJNWTNUYRAEfbEJRM|JMUREJWTLObWMQWSJMSLGWaTAETPCGfb|JMUREJWTLPTOKTXOMQRMIRVMJNMIGLaV|JMUREJYUMQcYJMRNKRUNFKWSKRZUQZdN|JMURFJWSKOaWMQWTJMTKGWbSLPebHLbW|JMURFJWSKOaWMQWTJMTKGWbSLPRNEJNE|JMURFJWSKOaWMQWTJMTKGWbSLPYUHLfb|JMURFJWSKObWMQebJMYUGKWTLPSLPGTO|JMURKNRKGNVSEJSOLSaVCGVOFKOFJCWS|JMURKNRKGNVSEJSOLSaVDGVOGLeaLSaV|JMURKNRKGNWTMRVMIRZUEJbWAEdZLPaV|JMURKOWTLPTKGUZJENXTPWbJFMYUHLfb|JMURLOWTEJbWAEfbMQTPHLWSOTXHKNRK|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRM|JMURLOWTEJbWAEfbMQTPJNWTNUYRFJaW|JMURLOWTEJbWAEfbMQTPJNYUGLPGCLRM|JMURLOWTEJbWAEfbMQYUJNRMIYVSOVZA|JMURLOWTEJbWJNTPNUZJFMWTMQfbAEbW|JMURLOWTEJbWJNTPNUZJFMWTMQfbAEdZ|JMURLOWTEJbWJNTPNUZJFMWTMQfbAEVR|JMURLOWTEJbWMQRMIRVMGLMILPYUHLaV|JMURLOWTEJbWMQTPOTXOKTRMIRVMGKMI|JMURLOWTEJbWMQWSJMSLGWaTAETPCGfb|JMURLOWTEJbWMQWSJMSLGWaTAETPEJZU|JMURLOWTEJbWMQWSJMSLGWaTHLZUQSTP|JMURLOWTGLTPCGbWOTXOLbfWKOWSGLPG|JMURLPWSHLSOLSVOMVZSKTXOEJaVIMYU|JMURLPWSMQSOKTXOEJbWJMfbGLVSMVaR|JMURLPWSPTXOKTbWTXZUMQcZHLRNFJfb|JMURLPWSPTXOKTbXGKXOKTfbTXSOCGOK|JMURLPWSPTXOKTbXGKXOKTZUHLfbTXdZ|JMURMQVSKOaVEJWTLPTKGWbSCGYUGLRN|JMURMQVSKOaVEJWTLPTKGWbSCGYUJMXT|JMVRMVaREJeaJMaVMQdaLPWSPTXOKTbX|JMVRMVaREJUQJNZVNUQZFJYUJMURAEXT|JMVRMVaREJUQLOWTJNZVNUYRFJdaJMQJ|JMVRMVaREJWTJMdaMVaRLOeaFJUQJMQJ|JMVRMVaREJWTJNTPFJbWBEfbJMdaMVZJ|JMVRMVaREJZVJMUQBEQJEUYRAEdZEJZU|JMVSEJWTLPTOKTXOGKUQKTbXBEXODGeb|JMVSFJaVMQeaJNSJENURNUYRKOWSAERN|JMVSFJWTKNbWMQZVQZdULPURNUYRGLcZ|JMVSFJWTMQSNKRUNJSTOSVZSLPbWEJaV|JMVSFJWTMQTOKTXOLPURJMaVGLbWCGfb|JMVSKOaVFKUREJWTKNTKNWbSGWebBFbS|JMVSKOaVFKWTMRUNKaTKGWbSEJeVLPYU|JMVSKOaVFKWTMRUNKaTKGWbSLPeVHLYU|JMVSKOaVGKURLPSLPGWSHLbWLOSLGPWS|JMVSKOaVMQeaEJWTJMTKGWaTLPTOFKOF|JMVSKOUQOVQJENaKFOYUGKWTLPeaPWbL|JMVSLOSLHOUQMRWTIMQJENZVAEVMEIcZ|JMVSLPSOKTXOMQUREJaVGKeaKTRNJSVX|JMVSMQaVIMUREIWTLPSNPWbSKOSLHOfb|JMVSMQaVIMWTMRUNKaeVEJYUAETOEIUR|JMVSMQaVLPeaEJSOKTXOJMWTPWaTAEbX|JMVSMQUREJRNKRSOLSWEAJZUQZdEFJEN|JMVSMQURKNRKFVaREJeaLOaVBFWTFKTP|JMVSMQURKNRKFVaREJeaLOaVBFWTGKTP|JMVSMQURKOaVEJWTFKTPAEbWJMfbEJda|JMVSMQURKOaVEJWTJMTKGWbSLPdaAEaW|JMVSMQURKOaVEJWTJMTKGWbSLPebHLSN|JMVSMQURKOaVEJWTJMTKGWbSLPfbAEbW|JMVSMQURKOaVEJWTJMTKGWbSLPfbHLbW|JMVSMQURKOaVEJWTJMTKGWbSLPfbHLea|JMVSMQURKOaVEJWTJMTKGWbSLPSOCGVS|JMVSMQURKOaVEJWTJMTKGWbSLPSOPTOL|JMVSMQURKOaVFKWTKNTKNWbSGWebEJbS|JMVSMQURKOaVGKWTLPSLPGTOKTXOEJbW|JMVSMQURKOaVGKWTLPSLPGVSEJSOJMda|JMVSMQURKOSNOSNKGUWNCGYRLOcYEJNE|JMVSMQURLPSOKTXOEJaVJMWSGLdaCGYU|JMVSMQURLPSOKTXOEJbXJMaVGLebLSWN|JMVSMQURLPSOKTXOEJZUQZcVGLdZLSWE|JMVSMQWTEJTOKTXOJMURMVaRAEeaEJSN|JMVSMQWTKOTKFVaRLObWHLeaCFWTLPTK|JMVSMQWTKOTKFVZSQZdUIMbWMQXTQZcV|JMWSEJaWKNeaMQSOLSVOJMWSNWbSGLfb|JMWSEJaWKNXTMRVMIRbXGKZVRaeVLPda|JMWSEJaWMQeaJMWTMRUNKRVMQJaVJMYU|JMWSEJbWAEebMRUNKRVMJQaVIMYUFKWT|JMWSEJbWAEfbMRUNKRVMJQXTIMYUEITO|JMWSEJbWAEfbMRUNKRVMJQXTLPZVGKbX|JMWSEJbWAEWTLPTOKTXOMQURJMOLHOSL|JMWSEJbWAEWTMRUNKRVMJQTPIMfbFKbW|JMWSEJbWKNebMQSOLSVOJMWSNWbSGLfb|JMWSEJbWKOUQFKZUJNSJMFWSKNSJFMQJ|JMWSEJbWKOUQGKZULPSLPGXTAETOKTWP|JMWSEJbWLOSLHOWTAEUQMRVMIRZUJNdZ|JMWSEJSOKTXOLSVOMQbWAEfbJMURMVaR|JMWSEJSOKTXOLSVOMQURGLRNJSOVAEVR|JMWSEJSOKTXOLSVOMQURJMaVAEbWGKWT|JMWSEJSOLSVOKTXOAEURMVaRJMOKGUZA|JMWSEJSOLSVOKTXOAEURMVaRJNRKGNbX|JMWSEJSOLSVOKTXOBEUQGLaVLSVODGbW|JMWSEJSOLSVOKTXOBEZVMRVMJZcVEJVS|JMWSEJSOLSVOKTXOGKbXKTXOCGfbGLaV|JMWSEJSOLSVOKTXOGLaWLSWEAJbWDGZV|JMWSEJSOLSVOKTXOGLaWLSWEAJUQMRZU|JMWSEJSOLSVOKTXOMQbWAEfbJMURMVaR|JMWSEJSOLSVOKTXOMQURJMaVAEbWGKWT|JMWSEJURKOaWFKWTKNTKNWbSGWebBFbS|JMWSEJURKORNAEbWFKZUKRUNLPSLJZcV|JMWSEJURKOYUMQcYJMbWFKRNKRUNBFXT|JMWSFJbWKNXTMQTPJMSJMFfbIMWTFKUR|JMWSFJbWMQWTJNSJENTOLSVFBKURNUYR|JMWSFJbWMQWTJNSJENTPNRUNKRVMQJfb|JMWSFJbWMQWTKNTPNWaTIMUREIYUCFfb|JMWSFJURLOSLHObWJNWSNUZJEWaTAEYU|JMWSKOaWFKUQMRVMIRWTOVZSBFSNRVbW|JMWSKOaWFKWTEJbWBFUQMRVMOVZSIRTO|JMWSKOaWFKWTEJTPBFURAEZUMQdZJMea|JMWSKOaWFKWTMRUNKaTKGWbSLPeVHLYU|JMWSKOaWGKWTEJTPDGURMQZUQZdUJNSJ|JMWSKOaWGKWTLPSLPGTOKTXOEJbWMQUR|JMWSKOaWGKWTLPSLPGTOKTXOEJbXAEVS|JMWSKOaWGKWTLPSLPGTOKTXOFJURCFbW|JMWSKOaWGKWTLPSLPGTOKTXOMQbWEJfb|JMWSKOaWGKWTLPSLPGTOKTXOMQUREJbW|JMWSKOaWMQeaEJWTJMTKGWaTLPTOFKOF|JMWSKOaWMQUREJWTJMTKGWbSLPebHLSN|JMWSKOaWMQWTEJTKGWbSLPfbCGbWHLVR|JMWSKOaWMQWTEJTKGWbSLPfbJMbWFKUR|JMWSKOaWMQWTEJTKGWbSLPURCGeaJMfb|JMWSKOaWMQWTEJTKGWbSLPURJMfbAEbW|JMWSKOaWMQWTEJTKGWbSLPVRJMSNMVZS|JMWSKOaWMQWTFKTPEJURJMbWCFfbOTXO|JMWSKOaWMQWTGKTPDGUREJYUBEbWJNSJ|JMWSKOaWMQWTGKURLPSLPGTOKTXOEJbW|JMWSKOaWMQWTIMTKGWbSLPfbHLbWFKUR|JMWSKOaWMQWTLPSLPWbSGPfbIMbWHLUR|JMWSKOaWMQWTLPTKGWbSEJfbJMSOAEea|JMWSKOaWMQWTLPTKGWbSEJURCGSOGLVS|JMWSKObWEJUQFKZUJNSJMFURLPWTPWaT|JMWSKObWEJUQGKZULPSLPGXTAEURKNRK|JMWSKObWEJUQMRVMOVaRJNRKIReaGNZV|JMWSKObWEJURFKWTLPSLPWaTGWeaHLaT|JMWSKObWEJURFKYUMQcYJMRNKRUNBEWT|JMWSKObWFKUQBFQJFMfbEJYUMQURJMSN|JMWSKObWFKUQBFQJFMfbMQYUEJURJMSN|JMWSKObWFKUQBFQJFMfbMQYUIMSNKYVS|JMWSKObWFKUQBFQJFMYUMQfbEJURJMSN|JMWSKObWFKUQBFQJFMYUMRUNKRVMIRfb|JMWSKObWFKUQEJZUJNSJMFURLPWTPWaT|JMWSKObWFKUQMRVMIRSNRUYROSNJEUWN|JMWSKObWFKUQMRVMIRSNRVaROSXTSJTP|JMWSKObWFKUQMRVMIRSNRVaROSZUSJRM|JMWSKObWFKUREJWTLPSLPWaTGWebBFbS|JMWSKObWFKUREJYUMQcYJMRNKRUNBEWT|JMWSKObWFKUREJYUMQcYJMRNKRUNBFXT|JMWSKObWFKUREJYUMQcYJNSJBFRMIRUN|JMWSKObWFKUREJYUMQcYJNSJBFWTFMRN|JMWSKObWFKUREJZUMQRMIRVFCJaVQZdU|JMWSKObWFKWTLPSLPWaTGWeaKNaTMRVM|JMWSKObWGKUQLPSLPGQJFMWSEJYUMQfb|JMWSKObWMQWTEJTKGWaTLPeaPWaTAEfb|JMWSKObWMQWTFKTPEJURJMYUBFfbAESN|JMWSKObWMQWTLPTKGWaTPWebHLbSLPVR|JMWSKOUQEJZUFKURJNSJMFbWLPWTPWaT|JMWSKOUQEJZUGKaWKNVRMVSZBEWTOSTP|JMWSKOUQGKQJEWaTAETPDGYUEJeaBEUQ|JMWSKOUQGKQJEWaTAEYUEJURLPeaPWbL|JMWSKOUQGKQJEWaTIMTPCGVSOVZSMRda|JMWSKOUQGKQJEWaTIMTPDGdaKNbWOSVO|JMWSKOUQGKQJEWaTIMTPDGdaMQbWOSVO|JMWSKOUQGKQJEWaTIMZUOSVOLSdaAEbW|JMWSKOUQGKQJEWaTIMZUOSVOLSeaKNcZ|JMWSKOUQGKQJEWaTLPYUPWbLHOfbAEbW|JMWSKOUQGKQJEWbSIMaWAEWTLPSLPGYU|JMWSKOUQGKQJEWbSIMaWAEYUMQURLPSL|JMWSKOUQGKQJEWbSIMaWMQWTLPSLPGfb|JMWSKOUQGKQJEWbSIMYUMQaWAEWTLPSL|JMWSLOSLHOUREJaWAEWSGLbWLPSLPGfb|JMWSLOSLHOUREJaWJNWSNWbLGPfbCGbW|JMWSLOSLHOVRMVZLGPXTPWbSCGfbGLbW|JMWSLPbWMQSOKTXOEJfbAEWSGLbXCGaW|JMWSLPSOKTXOEJURAEbWMQWSJMOLHOSL|JMWSLPSOKTXOGLVSMQUREJRNAEaWCGea|JMWSLPSOKTXOMQaWEJWSGLURJMeaCGYU|JMWSLPSOKTXOMQaWEJWTPWbSJMfbAEbX|JMWSLPSOKTXOMQaWEJWTPWbSJMfbFJUR|JMWSLPSOKTXOMQbWEJfbAEbXGLVSJMaV|JMWSLPSOKTXOMQbWEJfbAEbXJMOKFOWT|JMWSLPSOKTXOMQbWEJfbAEURGLYULSVO|JMWSLPSOKTXOMQbWEJfbJMbXMRUNFKOF|JMWSLPSOKTXOMQbWEJfbJMbXMRVMIRUN|JMWSLPSOKTXOMQbWEJfbJMVRMVZSQZcV|JMWSLPSOKTXOMQbWEJfbJNURNUYRAEWS|JMWSLPSOKTXOMQbWEJURJMfbAEWSGLaW|JMWSLPSOKTXOMQbWEJWTPWaTAEfbGLbX|JMWSLPSOKTXOMQbWEJWTPWaTJMfbGLea|JMWSLPSOKTXOMQUREJaWJMbXFJebGKOF|JMWSLPSOKTXOMQUREJaWJMbXGLfbLSWN|JMWSLPSOKTXOMQUREJbWJMfbGLWSCGZU|JMWSLPSOKTXOMQUREJbWJMYUAEWSGLfb|JMWSLPSOKTXOMQUREJbWJMYUGLWSCGeb|JMWSLPSOKTXOMQUREJRMIRVMJNMIGLaV|JMWSLPSOKTXOMQURFJVSJMaVEJbWGLfb|JMWSMQbWEJWTJMSOLSVOGLaVLSVOAEfb|JMWSMQbWIMUREISNLPWSHLfbDHYUBEaW|JMWSMQbWKOWTEJTKGWaTLOTKFOfbBFbW|JMWSMQbWLPSOKTXOEJfbJMVRMVZSQZcV|JMWSMQbWLPSOKTXOGLfbLSVOEJURJMaV|JMWSMRUNKRVMIRbWLOSLHOfbEJWSOVZS|JMWSMRUNKRVMIRbWLOSLHOWTFKfbRVZL|JMWSMRUNKRVMIRZUFKUNKRXTEJTOBEaW|JMWSMRUNKRVMIRZUFKUNKRXTGKbXLOSL|JMWSMRUNKRVMIRZUFKUNKRXTGKSNLONU|JMWSMRVMIRUNKRaVRaeVFKYUKOUREJda|JMWSMRVMIRUNKRaWLOSLHOWTFKbWEJda|JMWSMRVMIRUNKRbWEIfbLOSLHOZVAEVM|JMWTEJbWAEfbMRUNKRVMJQTOLSWNHLbW|JMWTEJbWAETPMQWSLOSLHOfbJNURNUYR|JMWTEJbWJNfbMRVMIRTPAEUQLOWTRUYR|JMWTEJbWJNfbMRVMIRTPAEUQRUYRNUQM|JMWTEJbWJNURNUZJFMVSLOSLHOdZAEfb|JMWTEJbWLOfbMQTPOTXOKTURTXRMIRVM|JMWTEJbWMQURLOTPJNWTNUYRAEfbFJRM|JMWTEJbWMQWSAESOLSVOGLaVLSVOIMfb|JMWTEJbWMQWSLPSOPWaTAETPKTPWHLWS|JMWTEJTOKTXOLSVOMQbWGLWSBEURJMfb|JMWTEJTOKTXOLSVOMQbWJMfbAEWSEJbX|JMWTEJTOKTXOLSVOMQbWJNURNUYRAEfb|JMWTEJTOLSVOKTXOBEURMVaRJMZVGLdZ|JMWTEJTOLSVOKTXOBEZVMRVMJZcVFJVS|JMWTEJTOLSVOKTXOMQaVJMVSFJdaJNSJ|JMWTEJTOLSVOKTXOMQbWAEfbJMURMVZS|JMWTEJTPAEURKOaWOTXOLSWNJSVOMVZS|JMWTEJTPJNUQNRQJFMbWMQVMQJYUJNUQ|JMWTEJTPLObWOTXOKTWSTXURAEfbMQRM|JMWTEJTPMQbWJNURNUYRLOfbAEWTEJRM|JMWTEJTPMQbWJNVSFJaVJMSJMFfbIMea|JMWTEJTPMQbWLOWSAESLHOfbJNbWEJVR|JMWTEJTPMQbWLOWSAESLHOfbJNURNUYR|JMWTEJTPMQbWLOWSAESLHOVSOVZSQZcV|JMWTEJTPMQXTLObXJNURNUYRAEfbEJRM|JMWTEJUQMRVMIRTPLOaWHLZUJNdZBEWT|JMWTEJUQMRVMIRTPLObWJNWTRUYRNUQM|JMWTEJVSKOTKFVZSMQbWQZcVIMYUAEUR|JMWTEJVSKOTKFVZSMQbWQZdUIMfbMQUR|JMWTFJUQBFTPLObWOTXOKTWSTXYUMRUN|JMWTFJUQLPZUPWaTCFURKNRKGNbWMRVM|JMWTFJUQLPZUPWaTCFVSMRUNKRTOGLbW|JMWTFJUQLPZUPWaTKNURNUYRHLbWGKea|JMWTKNaWNSWNMRVMIKeaEJTPLOURBEZU|JMWTKNaWNSWNMRVMIKTPEJUQJNZUNRUN|JMWTKNbWMRVMIRTPNSWNRKUREJYUAEfb|JMWTKNTOLSVOEJbWGLfbLSURNUWEAJYR|JMWTKNTOLSVOEJURNUYRMVZSJMbWAEfb|JMWTKNTPMQXTEJaWAEWSNWTaJNbWEJUR|JMWTKNVRMVaKGNbWEJTPIMPGDKXTMQfb|JMWTKNVRMVaKGNbWEJTPIMPGDKXTMRfb|JMWTKOTKFOaWMQWSEJdaBFaWJMURFKSN|JMWTKOTKFObWMQWSEJfbJMbWLPSLHOUR|JMWTLObWEJfbAETPMRVMJQWTEJURJNYU|JMWTLObWEJfbMQTPJMWTFJbWJNURNUYR|JMWTLObWEJfbMQURJNTPNUYRAEWTFJRM|JMWTLObWEJTPMQURJNfbNUYRAEcYHLWS|JMWTLObWEJTPMQWSAESLHOfbKNaWGLPG|JMWTLObWEJTPOTXOKTWSTXURMQRMIRVM|JMWTLObWEJURMQTPOTXOKTWSTXRMIRVM|JMWTLObWEJVSOVZSKNTPFKfbBEXTNRUN|JMWTLObWEJVSOVZSKNTPMQaVQZdUAEXT|JMWTLObWEJWSAESLGWaTCGTPMQURJMYU|JMWTLObWEJWSAESLGWaTHLTPCGVSMQea|JMWTLObWEJWSAESLGWaTHLTPKOPGCLfb|JMWTLObWEJWSAESLGWaTHLURMQfbLObW|JMWTLObWEJWSMQSLGWaTJNURNUYRHLTO|JMWTLObWHLUQLPQJENVSOVZJFMTOKTXO|JMWTLObWMQWSHLTPEJfbJMbWMRUNKRVM|JMWTLObWMRUNKRVMIRTKGNZUNSUNSJXT|JMWTLObWMRVMIRUNKRTKGNebFKWSNWbS|JMWTLObWMRVMIRUNKRTKGNfbFKXTHLbX|JMWTLOTPEJbWMQWTJNURNUYRAEfbEJRM|JMWTLOTPMQbWOTXOKTURTXWSFKfbBFSO|JMWTLOTPMRVMIRUNKRbWEJWTGKfbAEaV|JMWTLOUQMRVMIRbWEJTPOTXOKTZVJMQJ|JMWTLOUQMRVMIRZVEIVMIRbWFJdZJNaV|JMWTLOUREJbWAETPMQWSJMSLHOfbEJbW|JMWTLOUREJbWAETPMQWTJNfbNUYREJRM|JMWTLOUREJbWJNTPNUZJFMWTMQfbAEdZ|JMWTLPTOKTXOMQbWFJWTPWaTJMfbEJbW|JMWTLPTOKTXOMQUREJRMIRVMJNMIGLaV|JMWTLPTOKTXOMQURGKbXKTXOCGfbGLaW|JMWTLPUQPWQJENbJFMfbHLYUMQbWAEUR|JMWTLPUQPWQJENbJFMXTAEfbMQVRCFTP|JMWTMQbWLPTOKTXOEJfbJNURNUYRAEVS|JMWTMQTOKTXOLSVOEJbWAEfbJNURNUYR|JMWTMQTOLSVOKTXOEJaVAEbXIMfbEIbW|JMWTMQTOLSVOKTXOEJbWAEfbJMWSFJbX|JMWTMQTPEJbWJMURKNRKGNPGDKVSFJSO|JMWTMQTPEJURJMbWAEYUEJWTKOTKFORN|JMWTMQTPEJXTJMTOLSVOKTPWHLWSFKbW|JMWTMQTPLOUREJRMIRVMJNMIAEYUHLbW|JMWTMQURLObWEJRMIRVMGLMILPZUQZcV|JMWTMQURLPTOKTXOGLaWLSVOEJdaDGZV|JMWTMRUNKRVMIRTOLSZURVaRGKRMEJMI|JMWTMRUNKRVMIRTOLSZURVaRGKRMHLea|JMWTMRUNKRVMIRTOLSZURVaRGKRMKOMI|JMWTMRUNKRVMIRTOLSZURVaRGKUQEIYU|JMWTMRUNKRVMIRTOLSZURVaRGLRMFKMI|JMWTMRUNKRVMIRTOLSZURVaRHLRMGKea|JMWTMRUNKRVMIRTOLSZURVaRHLRMLOea|JMWTMRUNKRVMIRTOLSZURVaRHLRMLOMI|JMWTMRUNKRVMIRTOLSZURVaRHLRMSVMI|JMWTMRUNKRVMIRTOLSZURVaRHLUQLOYU|JMWTMRUNKRVMIRTPEJbWAEWTJNaWEJda|JMWTMRUNKRVMIRZUFKUNKRTPLObWEJWT|JMWTMRUNKRVMIRZVEIVMIRdZRVZSLOTK|JMWTMRVMIRUNKRaVRaeVEITOLSVOGLXT|JMWTMRVMIRUNKRaWFKTPBFWTEJbWAEda|JMWTMRVMIRUNKRaWFKWSRVSNKRZSEJea|JMWTMRVMIRUNKRaWFKWSRVSOLSZUEJda|JMWTMRVMIRUNKRbWEJTPAEWTJMfbEJaW|JMWTMRVMIRUNKRTOLSZURVaRGKRMCGea|JMWTMRVMIRUNKRTOLSZURVaRGKRMHLUQ|JMWTMRVMIRUNKRTOLSZURVaRHLRMLOea|JMWTMRVMIRUNKRTOLSZURVaRHLUQLOYU|JMWTMRVMIRUNKRTPEJbWAEWTJMfbFKbW|JMWTMRVMIRUNKRTPEJbWAEWTLOTKGNfb|JMWTMRVMIRUNKRTPEJXTAEZVJMdZEJZU|JMWTMRVMIRUNKRZUFKUNKRTPEJbWJNWT|JMXTFJTPMQWSJNSJENbWBEVSEJaVJMSJ|JMXTKOTKFOWSGKbWLPSLPGWTMQfbIMUR|JMXTLObXEJfbMQTPJNURNUYRAEWSEJSL|JMXTLOTPMRUNKRVMIRbXEJfbAEWTJMTK|JMXTLPbXGLfbLOVSOVZSKOSLPGWSMQcZ|JMXTLPbXMQTOKTXOGKWTPWaTEJfbAEbX|JMXTLPbXMQVSKNSJENURNUYRHLaVFKeb|JMXTLPUQGLQJFMbXEJVSMQebJNSJLOYU|JMXTLPUQHLQJFMVSMQSNKRTOLSWUIMbW|JMXTLPUQMRVMIRZURVaRKNRKFXURGKcZ|JMXTLPVSMQaVEJeaJNSJFMVSKOTKGNSJ|JNUQEJWTAETPLObWNSWNKRVMIRaWGKfb|JNUQEJWTAETPLOVRNUYRJNZVNUQZFJbW|JNUQEJWTAETPNRVMIRbWLOWTEIfbKNTK|JNUQEJWTLPbWGLZULOURNUQZJMYUMQUR|JNUQEJWTNRVMIRbWLOfbAETPOTXOKTPL|JNUQEJYUAEVRIMRINSWNKYbWJNZVEJVR|JNUQEJZUAEVRLOWTOSaWGLTPLOWTCGdZ|JNUQEJZUAEWTLOVROSaWGLTPDGQMJZcO|JNUQEJZULPURNUQZIMYUMQWSKNbWGLeb|JNUQEJZULPVRGLRMIRWTPWbSNWUPJNaT|JNUQEJZULPWTPWaTNSVOGLeaLScZBETP|JNUQKOWTGKQMIRVMEIZVIRVMAEMINRcZ|JNUQKOWTNRTKGNVMIRbWFKWTLOfbHLTP|JNUQLOWSNWbLHOYUOTXOKTURTXfbGLbW|JNUQLOWTEJbWAETPNRVMIRWTJNZUOSfb|JNUQLOWTEJZUNSVRJNcZSWbLGWaTIMQS|JNUQLOWTNRVMIRbWEJTPJNWTRUYRNUQM|JNUQLOZUEJWTNSVRJNTPAEcZEJaVHLXT|JNUQLOZUEJWTNSVRJNTPAEcZIMQABEAJ|JNUQLPVSEJSOKTXOAEWSNWbSGKaVKTSN|JNUQNRVMIRWSEJbWAEfbLOSLGPWSKOSL|JNUQNRVMIRWSEJbWAEfbLOSLHOWSOVZS|JNUQNRVMIRWSEJbWBEfbJNSJENWTRVZJ|JNUQNRVMIRWSEJbWBEfbLOSLHOZUJMQJ|JNUQNRVMIRWSEJbWBEZULOSLHOUNJbfW|JNUQNRVMIRWSEJbWBEZVEIVMIRfbLOSL|JNUQNRVMIRWSEJbWLOSLHOWSOVZSKNSO|JNUQNRVMIRWSEJSNJSZVSZcMAEMIEJXT|JNUQNRVMIRWSEJSOLSaVRadEAJeaHLbW|JNUQNRVMIRWSLOSLHObWGLWTKNTKFOfb|JNUQNRVMIRWSLOSLHObWGLZUKNWTLPTK|JNUQNRVMIRWSLOSLHObWKNfbGLWTLPTK|JNUQNRVMIRWSLOSLHObWKNWTGLTKNGfb|JNUQNRVMIRWTEIbWAETPLOWTEJZUKNTK|JNUQNRVMIRWTEJbWAETPEIfbJMQJFMXT|JNUQNRVMIRWTEJbWAETPEIWTJMQJFMaW|JNUQNRVMIRWTEJbWAETPJNfbLOWTRUYR|JNUQNRVMIRWTEJbWBETPEIfbJNZUKOXT|JNUQNRVMIRWTEJbWJNTPLOWTRUYRNUQM|JNUQNRVMIRWTEJbWLOaVRaeVAEVRJNZV|JNUQNRVMIRWTEJbWLOfbAEaVRaeVGLQM|JNUQNRVMIRWTEJbWLOfbAETPOTXOKTPL|JNUQNRVMIRWTEJbWLOTPAEWTJNZUOSfb|JNUQNRVMIRWTEJbWLOTPJNWTAEZUOSfb|JNUQNRVMIRWTEJbWLOTPJNWTRUYRNUaV|JNUQNRVMIRWTEJbWLOTPJNWTRUYRNUQM|JNUQNRVMIRWTEJbWLOTPOTXOKTZVJMQJ|JNUQNRVMIRWTEJbWLOZVBEVMOSWNKIaV|JNUQNRVMIRWTEJbWLOZVJMQJFMTPAEWT|JNUQNRVMIRWTEJTPAEaWEIWTJNZUFJdZ|JNUQNRVMIRWTEJTPAEbWEIfbJMQJFMXT|JNUQNRVMIRWTEJTPAEbWJNZULOWTOSdZ|JNUQNRVMIRWTEJTPAEbWLOWTJNfbRUYR|JNUQNRVMIRWTEJTPLObWJNWSNWaTAEfb|JNUQNRVMIRWTEJTPLObWJNWTRUYRNUQM|JNUQNRVMIRWTEJTPLObWJNZUOTXOKTcZ|JNUQNRVMIRWTEJZVAEVMEIcZIRZVJMQJ|JNUQNRVMIRWTEJZVJMQJFMVSLOSLGWbS|JNUQNRVMIRWTKNaWFKZULOdZHLTPOSWT|JNUQNRVMIRWTKNTPFKXTLObXCFZUFJaV|JNUQNRVMIRWTKNTPFKXTLObXHLZUEJdZ|JNUQNRVMIRWTKNZUFKcZLObWBFfbNSWN|JNUQNRVMIRWTLOaWEJTPHLWTRVZSOVYU|JNUQNRVMIRWTLObWEJfbJNTPAEWTEIQM|JNUQNRVMIRWTLObWEJTPAEWTJNZUOSdZ|JNUQNRVMIRWTLObWEJTPAEWTJNZUOSfb|JNUQNRVMIRWTLObWEJTPJNWSNWaTAEfb|JNUQNRVMIRWTLObWEJTPJNWTAEZUOSfb|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUaV|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUQM|JNUQNRVMIRWTLObWEJTPOTXOKTWSTXfb|JNUQNRVMIRWTLObWEJTPOTXOKTWSTXZU|JNUQNRVMIRWTLObWEJTPOTXOKTWSTXZV|JNUQNRVMIRWTLObWEJZVJMQJFMTPAEVS|JNUQNRVMIRWTLObWEJZVJMQJFMTPAEWT|JNUQNRVMIRWTLObWKNTKFOWTGKfbDGTP|JNUQNRVMIRWTLOTPEJbWAEWTJNZUOSdZ|JNUQNRVMIRWTLOTPEJbWJNWTRUYRNUQM|JNUQNRVMIRWTLOTPHLbWEJfbJMQJFMWS|JNUQNRVMIRWTLOTPHLbWEJWTJMQJFMZU|JNUQNRVMIRWTLOTPKNaWFKZUBFWTHLda|JNUQNRVMIRWTLOTPKNZVEIVMIRcZAEZU|JNUQNRVMIRWTLOZUHLUNKRTKGNaVRaeV|JNUQNRVMIRWTLOZUHLUNKRTKGNbWLOWT|JNUQNRVMIRXTLObXEJfbAEZVEIVMIRTP|JNUQNRVMIRXTLObXKNTKFOfbHLZUNSWN|JNUQNRVMIRZUKNdZLOWTFJTKJMQSGdUN|JNUQNRVMIRZUKNdZLOZVEIVMIRcZBEWT|JNUQNRVMIRZUKNWTFKTPLObWHLWTCFfb|JNUQNRVMIRZULOUNKRdZFKZUKNcZCFZV|JNUQNRVMIRZULOUNKRdZFKZUKNWTEJTK|JNUQNRVMIRZULOUNKRWTHLTKGNaVRaeV|JNUQNRVMIRZVEIVMIRWTAEbWLOTPOTXO|JNUQNRVMIRZVEIVMIRWTKNbWAEdZFKZU|JNUQNRVMIRZVEIVMIRWTKNdZAEbWFKZU|JNUQNSWNKRVMIRZVEIVMIRcZAEZVEIVM|JNURNUYREJWSKObWGKWTLPSLPGfbHLTO|JNURNUYREJWSKObWJMWTMQTKGUcYLOSL|JNURNUYREJWSLOSLHObWJNfbNUZQBEWS|JNURNUYREJWTAETOLSVOKTXOJNRKGNbW|JNURNUYREJWTAETPJNRMIRVMEIZVIRVM|JNURNUYREJWTAETPJNRMIRVMLOMINRbW|JNURNUYREJWTJMTOLSVOKTXOMVZSFKOF|JNURNUYREJWTJMTPLObWOTXOKTcYAEWS|JNURNUYREJWTJNRMIRVMAEMILOTPNRbW|JNURNUYREJWTJNRMIRVMAEMILOTPNRcY|JNURNUYREJWTJNRMIRVMAEMINRcYEJTP|JNURNUYREJWTJNRMIRVMAEMINRcYLObW|JNURNUYREJWTJNRMIRVMAEMINRTPEJbW|JNURNUYREJWTJNRMIRVMAEMINRTPLObW|JNURNUYREJWTJNRMIRVMAEMINRTPLOcY|JNURNUYREJWTJNRMIRVMAETPEIZVIRVM|JNURNUYREJWTLObWJMfbMQTPAEWSHLcY|JNURNUYREJWTLObWJMTPAEfbOTXOKTWS|JNURNUYREJWTLObWJNZUNSWNIMRIKYTK|JNURNUYREJWTLOTPAEbWJNWTNUZQEJfb|JNURNUYREJWTLOTPJMbWOTXOKTWSTXcY|JNURNUYREJWTLOTPJMbWOTXOKTWSTXfb|JNURNUYREJWTLOTPJNbWNUZQAEWTEJfb|JNURNUYREJWTLPTOKTXOJMVSMVaRAEea|JNURNUZQEJWSKObWGKYUBEebDGcZKNUR|JNURNUZQEJWTJNQMIRVMAEMIEJYULPcY|JNURNUZQIMQJENcZAEZUFJUQCFVRNUQZ|JNURNUZQKNVRNUQZEJaVIMYUMQWSLPUR|JNURNUZQKNVRNUQZFKaVEJWSLOSLHObW|JNURNUZQLOWSGLYUOTXOKTbXDGXOIMQJ|JNVREJaVAEVSLOSLHOWTGLTPDHPGCLUQ|JNVREJaVBEWTJMTPLOUQNUYRHLQJEUZQ|JNVREJaVBEXTLObXJMTPMQfbGLPGCLXT|JNVREJaVJMUQNUQJFMZJBFVSFMWTLOSL|JNVREJaVJMWTLObWMQfbFJdaHLRMIRVF|JNVREJaVJMXTLObXMQfbFJTPJMWTAEbW|JNVREJaVJMXTLObXMQfbGLTPOTPGTadW|JNVREJaVJMXTMQbXLOfbGLTPAEPGCLea|JNVREJaVJMXTMQbXLOfbGLTPAEPGCLXT|JNVREJaVJMXTMQbXLOfbGLTPBEPGCLXT|JNVREJaVJMXTMQbXLOfbGLTPOTPGTadW|JNVREJaVJMXTMQTPAEbXLOWTEJdaJMaW|JNVREJaVJMXTMQTPFJWTJMbXLOdaAEaW|JNVREJaVJMXTMQTPFJWTLOdaOXRMIRVO|JNVREJaVJMXTMQTPLOWSNWbLHOeaAEfb|JNVREJaVLOWSNWbLHOfbGLbWLPeaDHWT|JNVREJaVLOWTBEeaJMUQNUQJFMZJENdZ|JNVREJaVLOWTBETPJMUQNUYRHLQJEUZQ|JNVREJaVLOWTBEUQNUYRJMQJEUZQIMQJ|JNVREJaVLOWTHLTPDHUQNUYRBEbWOTXO|JNVREJaVLOWTJMUQNUQJFMZJBEbWENVR|JNVREJaVLPeaGLVSLOSLHOWTPWbLDHaW|JNVREJaVLPeaGLVSLOSLPGXTJMZVMQcZ|JNVREJaVLPeaHLVSLOSLJMaVMQXTAELH|JNVREJaVLPVSGLZVLOSLPGeaJMUQNUQZ|JNVREJaVLPVSGLZVLOSLPGUQNUQZHLWT|JNVREJaVLPVSGLZVLOSLPGUQNUQZJNWS|JNVREJaVLPVSGLZVLOSLPGVSGLUQNUQZ|JNVREJaVLPXTHLbXLOWSNWTaGLaWJNUQ|JNVREJaVLPXTJMUQNUQJFMZJHLJEAJVS|JNVREJWTBEbWJMTPMVZJFMWTMQTOQZOF|JNVREJWTBEZVJMbWMQcZLOTPHLWSNWaT|JNVREJWTJMaVMQbWLOdaFJRMIRVFCJaV|JNVREJWTJMaVMQeaLOTPHLbWAEWTEJRM|JNVREJWTJMaWMVZJFMWSLOSLGWbSMQSO|JNVREJWTJMaWMVZJFMWSMQTOKTXOQZcV|JNVREJWTJMaWMVZJFMWSMRUNKReaIMcZ|JNVREJWTJMTPMVZJFMUQBEQJENbWAEeb|JNVREJWTJMTPMVZJFMUQBEQJENYUAEUQ|JNVREJWTJMUQMVZJFMQJBEYUENUQAETP|JNVREJWTJMUQMVZJFMQJBEYUENUQLObW|JNVREJWTJMUQMVZJFMQJBFYUFMUQMRTP|JNVREJWTJMUQNUQJFMZJBEJFKBTPLOYU|JNVREJWTJMUQNUQJFMZJBFYUFMUQMRTP|JNVREJWTJMZVMQdZAETOLSVOKTXOGKbX|JNVREJWTLObWBETPJMWTMVZLHOaVEJVR|JNVREJWTLObWJMUQMVZJFMQJBEYUENUQ|JNVREJWTLObWOSaVSbfWGLTPDGebAEUQ|JNVREJWTLObWOSfbJMaVGLVOLSTOKaeO|JNVREJWTLOTPBEbWJMWTMVZJFMUQHLQJ|JNVREJWTLOTPHLZVJMUQNUQZKNbWNRWT|JNVREJWTLOTPJMUQMVZJFMQJBEbWENdZ|JNVREJXTBETOLSaVJMVOKaRBEJeVMQUR|JNVREJXTJMUQNUQJFMZJBEaVENVSLPSJ|JNVREJXTLOTPBEaVHLWSNWbSJMfbMQda|JNVREJXTLOTPBEaVJMVSMVSLHOZLDHbX|JNVREJXTLOTPJMWSNWbLMVaRHOZVAEfb|JNVREJXTLOTPOTbXJMXOMVZJKTUQFMQJ|JNVREJXTLPaVHLbXLOWSNWTaDHUQGLZU|JNVREJXTLPaVHLbXLOWSPWSbGLUQNUYR|JNVREJXTLPbXGLZVLOUQNUQZJMVSOVZS|JNVREJXTLPbXHLaVJMWSNWTaMQfbLObW|JNVREJXTLPbXHLZVJMUQNUQZMQVSKOTK|JNVREJXTLPZVGLbXJMUQNUQZMQVRAEeb|JNVREJXTLPZVGLbXLOUQNUQZJMYUMQUR|JNVREJXTLPZVJMUQNUQZMRVMIRZUAEUN|JNVREJZVAEVSLOSLHOWTOSUQNUQZKOTK|JNVREJZVBEWTJMUQNUQZMRVMIRTPLObW|JNVREJZVJMUQNUQJFMYRAEWSBFbWEJfb|JNVREJZVJMUQNUQJFMYRAEWSBFbWFJfb|JNVREJZVJMUQNUQJFMYRAEWSCFbWEJfb|JNVREJZVJMUQNUQJFMYRAEWSCFcYLPYU|JNVREJZVJMUQNUQJFMYRAEWSCFcYMQYU|JNVREJZVJMUQNUQJFMYRAEWSCFdZKObW|JNVREJZVJMUQNUQJFMYRAEWSKORNBFNJ|JNVREJZVJMUQNUQJFMYRAEWSKORNCFaW|JNVREJZVJMUQNUQJFMYRAEWSKORNLPSL|JNVREJZVJMUQNUQJFMYRAEWSKORNMQaW|JNVREJZVJMUQNUQJFMYRAEWSLOSLHObW|JNVREJZVJMUQNUQJFMYRAEWSMQbWLOSL|JNVREJZVJMUQNUQZAEVSLOSLHOWSOVZS|JNVREJZVJMUQNUQZAEWSEJaWKOXTOXSO|JNVREJZVJMUQNUQZAEWSEJSOLSVOKTXO|JNVREJZVJMUQNUQZAEWSEJYUKNUQNWbS|JNVREJZVJMUQNUQZAEWSEJYUKOaWMQXT|JNVREJZVJMUQNUQZAEWSEJYUMQaWJMWT|JNVREJZVJMUQNUQZAEWSFJSOKTXOLSVO|JNVREJZVJMUQNUQZAEWSKOYUEJURMQRM|JNVREJZVJMUQNUQZAEWTEJbWMQTPJMWT|JNVREJZVJMUQNUQZAEWTEJTPJNVSNWbS|JNVREJZVJMUQNUQZAEWTEJTPMRVMJQbW|JNVREJZVJMUQNUQZAEWTMRVMIRbWEJTP|JNVREJZVJMUQNUQZAEXTLObXEJfbMQZU|JNVREJZVJMUQNUQZAEXTLObXEJfbMRVM|JNVREJZVJMUQNUQZAEXTLObXEJTPOTXO|JNVREJZVJMUQNUQZAEXTLObXEJWSHLTP|JNVREJZVJMUQNUQZAEXTLObXEJYUMQfb|JNVREJZVJMUQNUQZAEXTLObXEJYUMQWS|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfb|JNVREJZVJMUQNUQZAEXTLObXMRVMIRTP|JNVREJZVJMUQNUQZAEXTLOTPEJYUOTUR|JNVREJZVJMUQNUQZAEXTMQTOLSVOKTWP|JNVREJZVJMUQNUQZAEXTMRVMIRTPEIbX|JNVREJZVJMUQNUQZAEYUMQURKOWSEJRN|JNVREJZVJMUQNUQZAEYUMQWSEJSOLSVO|JNVREJZVJMUQNUQZAEYUMRUNKRVMIRWT|JNVREJZVJMUQNUQZAEYUMRUNKRVMIRZV|JNVREJZVJMUQNUQZFJWSAEYUMQSOKTXO|JNVREJZVJMUQNUQZFJWSBFSOKTXOLSVO|JNVREJZVJMUQNUQZFJWSBFYUKNUQNWbS|JNVREJZVJMUQNUQZFJWSBFYUMQURJMSO|JNVREJZVJMUQNUQZFJWTJNTOLSVFBKbW|JNVREJZVJMUQNUQZFJWTJNTPNRZUMQUN|JNVREJZVJMUQNUQZKNVRNUZJFMYUMQUR|JNVREJZVJMUQNUQZKNVSFJXTMQTPIMaV|JNVREJZVJMUQNUQZKNVSFJXTMQTPIMbX|JNVREJZVJMUQNUQZKNWSNWbSLPfbAEbW|JNVREJZVJMUQNUQZKNWSNWbSLPYUAEXT|JNVREJZVJMUQNUQZKNWSNWbSLPYUMQfb|JNVREJZVJMUQNUQZKNWSNWbSLPYUMQUR|JNVREJZVJMUQNUQZKNXTMQTOLSVOIMWS|JNVREJZVJMUQNUQZKNXTMRVMIRTPAEbX|JNVREJZVJMUQNUQZKNXTMRVMIRTPLObX|JNVREJZVJMUQNUQZKOWTFKTPBFVRMVaR|JNVREJZVJMUQNUQZLOWSGLbWLPSLPGfb|JNVREJZVJMUQNUQZLOWSGLYUMQbWAEWT|JNVREJZVJMUQNUQZLOWSHLYUAEURMQaW|JNVREJZVJMUQNUQZLOWTAEbWMRVMIRTP|JNVREJZVJMUQNUQZMQVRLOaVAEWSEJSL|JNVREJZVJMUQNUQZMQVRLPaVGLeaAEWT|JNVREJZVJMUQNUQZMQWSAEYUEJSOLSVO|JNVREJZVJMUQNUQZMQWTFJTOKTXOLSVO|JNVREJZVJMUQNUQZMQWTKNTOLSVOGLaW|JNVREJZVJMUQNUQZMRVMIRWSFJbWLOSL|JNVREJZVJMUQNUQZMRVMIRWSFJZUBEUN|JNVREJZVJMUQNUQZMRVMIRWSLOSLHObW|JNVREJZVJMUQNUQZMRVMIRWSLOSLHOZV|JNVREJZVJMUQNUQZMRVMIRWTAEbWLOTP|JNVREJZVJMUQNUQZMRVMIRXTAETOKTWP|JNVREJZVLOUQNUQZAEWSGLYULPSLPGXT|JNVREJZVLOUQNUQZJMWSGLbWAEWTLPSL|JNVREJZVLOUQNUQZJMWTAETPEJYUMQbW|JNVREJZVLOUQNUQZJMYUMQURHLWSFJXT|JNVREJZVLOWTNScZIMRIKNTRJMVOMcUR|JNVREJZVLOWTNSUQSZdUAEcZJMQAFJAL|JNVREJZVLOWTNSUQSZdUAETPJNbWEJWT|JNVREJZVLOWTNSUQSZdUIMRIBEIBAEBI|JNVREJZVLPUQNUQZAEYUJMURKNRKFOWT|JNVREJZVLPUQNUQZHLWSKOYUBEXTPNVS|JNVREJZVLPUQNUQZHLWSKOYUDHXTPNVS|JNVREJZVLPUQNUQZHLWSKOYUJMbWMQUR|JNVRFJaVJMUQNUQJENYRNUZQAEdZKNWS|JNVRFJaVJMWSNWbSMQebKOdaEJaWJMWT|JNVRFJaVJMWTEJbWLOTPMQebGLPGCLWS|JNVRFJaVJMWTLObWMQTPEJWTBEdaJMaW|JNVRFJaVJMWTMQTOLSVFBKbWHLWTLOfb|JNVRFJaVJMWTMQTOLSVFBKXTGLZVQSTP|JNVRFJaVJMWTMQTOLSVFBKXTHLbXLOfb|JNVRFJaVJMXTMQTPEJWTLOdaOXRMIRVO|JNVRFJaVLPXTGLbXLOWSNWTaJNfbHLbW|JNVRFJWSNWbSJMRNKRUNBFXTLPebPWaT|JNVRFJWSNWbSJMSNMVaRBFXTLPeaPWaT|JNVRFJWSNWbSJMZVMQcZKOfbOTXOIMRI|JNVRFJWTJMaVMQTOLSVFBKbWHLfbLOea|JNVRFJWTJMaVMQTOLSVFBKXTHLbXLOfb|JNVRFJWTJMTPMVZJENUQAEbWBFcZLOZU|JNVRFJWTJMTPMVZJENUQAEbWBFfbNRQM|JNVRFJWTJMTPMVZJENUQAEbWEJaVKOVR|JNVRFJWTJMTPMVZJENUQAEbWEJWTLOYU|JNVRFJWTJMTPMVZJENUQAEbWEJYUKOWT|JNVRFJWTJMTPMVZJENUQAEbWLOWTEJdZ|JNVRFJWTJMTPMVZJENUQLObWAEWTEJYU|JNVRFJWTJMTPMVZJENUQLObWAEWTNRcZ|JNVRFJWTJMTPMVZJENUQLObWOSWTNRfb|JNVRFJWTJMUQMVZJENTPAEbWBFWTNRdZ|JNVRFJWTJMZVMQcZLOTPBFbWHLfbNSWN|JNVRFJWTJMZVMQcZLOTPCFbWEJebHLWS|JNVRFJWTJMZVMQcZLOTPCFbWEJebOTXO|JNVRFJWTJMZVMQcZLOTPCFbWEJRMIRVM|JNVRFJWTJMZVMQcZLOTPCFbWHLebEJWS|JNVRFJWTJMZVMQcZLOTPGLPGCLbWLPeb|JNVRFJWTJMZVMQcZLOTPHLbWBFWSNWaT|JNVRFJWTLObWJMTPMVZJENUQAEWTEJaV|JNVRFJWTLOTPCFaVHLbWDHWTOSVOLSeb|JNVRFJWTLOTPJMbWMVZJENWTAEUQEJdZ|JNVRFJWTLOZVNSUQSZcVJMQJEUYRAEdZ|JNVRFJWTLOZVNSUQSZdUIMRIBFIBAEBI|JNVRFJWTLOZVNSUQSZdUJNcZIMQLGdRM|JNVRFJWTLPZVPWaTJMUQNUQZKNZUHLTP|JNVRFJXTJMaVLOTPOTWSNWbSTXSOKTPW|JNVRFJXTJMTPMVZJENUQLObXAEWTEJYU|JNVRFJZVJMUQNUQZEJWSBFSOLSVOKTXO|JNVRFJZVJMUQNUQZEJWTJNTOKTXOLSVO|JNVRFJZVJMUQNUQZEJWTLObWAETPBFYU|JNVRFJZVJMUQNUQZMQWSKOaWGKWTLPSL|JNVRFJZVJMUQNUQZMRVMIRWSLOSLHObW|JNVRFJZVJMUQNUQZMRVMIRWTEIbWAETP|JNVRFJZVJMUQNUQZMRVMIRWTKNaVRaeV|JNVRFJZVJMUQNUQZMRVMIRWTKNTPLObW|JNVRFJZVJMUQNUQZMRVMIRWTLObWEJfb|JNVRFJZVJMUQNUQZMRVMIRWTLObWEJTP|JNVRFJZVJMUQNUQZMRVMIRWTLOTPCFbW|JNVRFJZVJMUQNUQZMRVMIRXTKNTPLObX|JNVRFJZVJMUQNUQZMRVMIRXTLObXEJTP|JNVRFJZVJMUQNUQZMRVMIRZULOUNKRdZ|JNVRFJZVJMWTMQcZLObWHLTPNSWNDHfb|JNVRFJZVJMWTMQcZLOTPBFbWHLebDHWS|JNVRFJZVJMWTMQcZLOTPBFbWHLebNSWN|JNVRFJZVJMWTMQcZLOTPBFbWHLfbNSWN|JNVRFJZVJMWTMQcZLOTPGLPGCLbWLPeb|JNVRLOWTEJbWHLTPOSfbLOWTJMUQMVaR|JNVRLOWTEJbWJMTPMVZJFMWTMQdZAEaV|JNVRLOWTFJbWJMTPMVZJENUQOScZSbfW|JNVRLOZVEJWTNSUQSZdUAETPJNbWEJWT|JNVRLOZVGLUQNUQZEJWSAEbWIMWTLPSL|JNVRLOZVGLUQNUQZEJWSAEbWJMYUFJUQ|JNVRLPWTPWbJFVaREJZVHLfbJNbWAEVS|JNVRLPXTGLbXEJaVLOWSPWSbHLUQNUYR|JNVRLPZVFJUQNUQZIMWSKNSOGLVRMVaK|JNVRLPZVGLRMIRVMEIcZIRWTPWbJFMUP|JNVRLPZVHLUQNUQZIMWSKOSNMQYUFKUR|JNVRLPZVHLUQNUQZIMWSMQYUKOSNFKUR|JNVRLPZVHLUQNUQZIMWTPWaTLObWEJda|JNVRLPZVHLUQNUQZIMWTPWbSKOfbEIbW|JNVRLPZVHLUQNUQZIMWTPWbSKOfbMQbW|JNVRLPZVHLUQNUQZIMWTPWbSKOYUEIaW|JNVRLPZVHLUQNUQZIMWTPWbSKOYUMQaW|JNVRLPZVHLUQNUQZIMWTPWbSKOYUMQUR|JNVRLPZVHLUQNUQZIMYUMQWSKOUREJbW|JNVRLPZVHLVSDHSJFVaREJeaJMRNKRUN|JNVRLPZVHLVSDHSJFVaREJUQBFdaLOYU|JNVSEJaVAEVRLPRMIRSOKaeMJQXTPWbA|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEcY|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZ|JNVSEJaVKOeaFKURNUYRJMWTMQTPCFcY|JNVSEJaVKOeaGKURNUYRLPSLPGWSAESO|JNVSEJaVKOeaGKURNUYRLPSLPGWSJNSJ|JNVSEJaVKOeaGKURNUYRLPSLPGWSKOSL|JNVSEJaVKOUQFKZUJMQJNEURBFYUFJcY|JNVSEJaVKOUQFKZUJMQJNEWTIMTPEIUR|JNVSEJaVKOUQFKZUJMQJNEWTIMTPMQUR|JNVSEJaVKOUQFKZUJMQJNEWTLPSLPWbS|JNVSEJaVKOUQGKZUBEURNUQZIMWTMQYU|JNVSEJaVKOUQGKZUBEURNUQZIMYUMQWT|JNVSEJaVKOUQGKZUBEURNUQZJNSJENYU|JNVSEJaVKOUQGKZUBEURNUQZKNYUFKUQ|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQ|JNVSEJaVKOUQGKZUBEURNUQZKNZUDGXT|JNVSEJaVKOUQGKZUBEURNUQZKNZUFKUQ|JNVSEJaVKOUQGKZUBEURNUQZKNZULPSL|JNVSEJaVKOUQGKZUBEURNUQZKNZUNRUN|JNVSEJaVKOUQGKZUBEURNUQZLPSLPGYU|JNVSEJaVKOUQGKZUBEURNUYRJMQJEUcY|JNVSEJaVKOUQGKZUCGURNUQZKNYUIMVR|JNVSEJaVKOUQGKZUDGURNUQZIMYUBEVR|JNVSEJaVKOUQGKZUDGURNUQZJMWTLPSL|JNVSEJaVKOUQGKZUDGURNUQZJMWTMRVM|JNVSEJaVKOUQGKZUDGURNUQZJNSJFMWT|JNVSEJaVKOUQGKZUDGURNUQZKNYUFKUQ|JNVSEJaVKOUQGKZUDGURNUQZKNYUIMUQ|JNVSEJaVKOUQGKZUDGURNUQZKNZUBEXT|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKcZ|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKUQ|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKUR|JNVSEJaVKOUQGKZUDGURNUQZKNZUGKcZ|JNVSEJaVKOUQGKZUDGURNUYRBEcYJMQJ|JNVSEJaVKOUQGKZULPSLPGVRAEXTHLcZ|JNVSEJaVKOUQGKZULPSLPGVRAEXTHLea|JNVSEJaVKOUQGKZULPSLPGVRGLRMIRWS|JNVSEJaVKOUQGKZULPSLPGVRHLeaJMQS|JNVSEJaVKOUQGKZULPSLPGVRHLWTLObW|JNVSEJaVKOURNUYRJMeaAEWTGKSNOSNP|JNVSEJaVKOURNUYRJMeaAEWTGKTPFJPN|JNVSEJaVKOURNUYRJMZUGKSNDGNJMQXT|JNVSEJaVKOURNUYRJMZUGKSNOSNPSQda|JNVSEJaVKOURNUYRJMZUMQcYQZdUAERN|JNVSEJaVKOURNUYRJMZUMQWTQZdUGKSN|JNVSEJaVKOURNUYRJMZUMQWTQZdUGKUQ|JNVSEJaVKOURNUZQGKYUBEeaDGcZKNUR|JNVSEJaVKOURNUZQGKYULPSLPGXTJMQJ|JNVSEJaVLPUQGLZUKOURNUQZJMYUMRUN|JNVSEJaVLPVRGLZVLOSLPGUQNUQZIMYU|JNVSEJUQAEZVIMYUEIURNUQZKNXTLPbX|JNVSEJUQAEZVIMYUEIURNUQZKNXTLPSO|JNVSEJUQAEZVIMYUEIURNUQZKNXTMQTO|JNVSEJUQAEZVIMYUEIURNUQZKOWTGKTP|JNVSEJUQIMZUAEdZEIZVKOURNUYRGKcY|JNVSEJUQIMZUMRcZAEZVEIVMIRdZBEZV|JNVSEJUQIMZUMRdZAEZVEIVMIRcZBEZV|JNVSEJUQKOYUOVaKFOWTGKZVBFTPDGea|JNVSEJUQLPZUGLaVLOSLPGVRHLWTLOTP|JNVSEJURNUYRKORNOVaRJSWNBEXTEJNE|JNVSEJURNUZQKNXTLPTONRdZBEZUJNSJ|JNVSEJZVKOUQGKYUBEcYDGURNUQZKNZU|JNVSEJZVKOUQGKYUBEURNUQZKNZUDGUQ|JNVSEJZVKOUQGKYUDGURNUQZKNZUGKUQ|JNVSEJZVKOUQNRVMIRXTOXSOLSWUGKcZ|JNVSEJZVKOURNUYRAEcZJMZUMQRNQZVc|JNVSEJZVKOURNUYRJMcZGKWTAESNOSNP|JNVSEJZVKOURNUYRJMcZGKWTAETPFJPN|JNVSEJZVKOURNUYRJMcZMQZUQZdULPSL|JNVSFJaVKOUQGKZUBFURNUQZKNZUCGdZ|JNVSFJaVKOUQGKZUDGURNUQZKNZUGKcZ|JNVSFJaVKOUQGKZUDGURNUQZKNZUGKUQ|JNVSFJaVKOURNUYRBFWTFKSNJSTPCFcY|JNVSFJaVKOURNUYRJMRNMQWTIMTKEJNE|JNVSFJaVKOURNUYRJMZUEJWTGKTPAEPN|JNVSFJaVKOURNUYRJMZUGKWTCFTPFJPN|JNVSFJZVKOUQGKYULPSLPGXTIMURNUQZ|JNVSFJZVKOURNUYRJMRNEJNEAJWTCFTK|JNVSFJZVKOURNUYRJMRNMQcZBFXTOXWT|JNVSFJZVKOURNUYRJMRNMQcZIMZUQZVc|JNVSLOSJENUQHLWTFJTPDHZUBFURNUQZ|JNVSLOSJFMWTMQbWEJTPJMWTAEfbHLbW|JNVSLOSJFMWTMRUNKRTKGNXTHLbXCGfb|JNVSLOSLHOUQNRWTIMQJFMbWEJTPAEWT|JNVSLOSLHOURNUYREJaVJNWSNUSLGPZQ|JNVSLPSJFMWSGLaVLOSLPGXTHLVSBFTP|JNVSLPSJFMWSHLaVKObWMQUREJYUGKfb|JNVSLPSJFMWSHLUQEJaVKObWGKZUDHXT|JNVSLPSJFMWSHLUQEJaVKOZUJNSJMFVS|JNVSLPSJFMWTPWbSEJfbMQSOKTXOBFUR|JNVSLPSJFMWTPWbSEJXTMQSOJNOFBKfb|JNWSNWaTEJdaJNbWIMVSFJUQLOSLHOaV|JNWSNWaTEJeaJNUQAEQMIRVMEIZVIRVM|JNWSNWaTEJeaJNUQAETPLOQMIRVMEJMI|JNWSNWaTEJeaJNUQAEYUNRUNKRVMIRTP|JNWSNWaTEJTPJMbWLOWTMRVMIRUNKRTK|JNWSNWaTEJUQAEZUJNURNUQZEJeaKNZU|JNWSNWaTEJURLPeaPWaTJMTPMQbWKOWT|JNWSNWaTIMeaMQURLObWEJWSHLTPAEZU|JNWSNWaTIMTPEIURLObWMQWTAEfbEJda|JNWSNWaTIMTPLOUQEIQJFMbWAEfbMRVM|JNWSNWaTIMTPMQUREJRMJNMINRVMQJbW|JNWSNWaTIMUREITPLObWOTXOKadWFKfb|JNWSNWaTIMURMQTPLOdaEIbWAEfbHLWT|JNWSNWaTKNbWFKTPNRVMIRUNKRWTEJZV|JNWSNWaTKNbWFKVREJTPLOZVJMUQNUQZ|JNWSNWaTLObWGLWSLPSLPGfbKNbWHLTP|JNWSNWaTLOdaEJbWJMUQMRVMIRaVRaWd|JNWSNWaTLOeaEJUQJNQMIRVMFJMFCJaV|JNWSNWaTLOeaFJbWJNURNUYRKNRKOFWS|JNWSNWaTLPTOKTXOGKbXKTXOEJfbJNbW|JNWSNWbSEJaWKOUQAEZUGKURLPSLHOeb|JNWSNWbSEJfbKObWGKURLPSLPGWSAEaW|JNWSNWbSIMaWMQWTKNSJENfbAEbWFKTP|JNWSNWbSIMebKOaWGKWTLPSLPGUREIbW|JNWSNWbSIMebMQSOLSVOKTXOEJbWJMfb|JNWSNWbSIMfbKObWGKUQEJZUBEUREIYU|JNWSNWbSIMfbKObWMQURFKZUQZdUEIRN|JNWSNWbSIMfbKObWMQURGKZUQZdUEJUQ|JNWSNWbSIMfbMQbWEIURAEZUQZdUEJUQ|JNWSNWbSIMfbMQbWKOUREIRNFKZUQZdU|JNWSNWbSIMfbMQbWKOUREIYUGKWTLPSL|JNWSNWbSKOfbGKbWEJWTLPSLPGTPJNVR|JNWSNWbSLOSLHOfbEJVRJNUQNUYROSZU|JNWTEJaWBETPNRVMJQUREJXTLObXJNZU|JNWTEJaWLOdaGLTPAEPGCLVSOVaRLPZV|JNWTEJaWLOVRAEeaOSaVGLVOLSdaDGaV|JNWTEJaWLPeaAEVRJMUQMeQMIRdaeVZA|JNWTEJaWLPeaAEVRJMZVEJUQNUQZJNTO|JNWTEJbWAEUQNSVOLbfWHLTPLOWTJNaW|JNWTEJbWAEVRLPaVGLWSPWSbLOUQNUYR|JNWTEJbWJMebMRVMIRTPAEUQEJWSNWaT|JNWTEJbWJMfbMQTOKTXOLSVOIMURMVZJ|JNWTEJbWJMfbMQTOLSVOKTXOGLaVLSVO|JNWTEJbWJMfbMRVMIRTPAEUQEIZUFJWT|JNWTEJbWJMfbMRVMIRTPAEUQEIZUKOdZ|JNWTEJbWJMfbMRVMIRTPAEUQEIZULOWT|JNWTEJbWJMfbMRVMIRTPAEUQKOWTGKPG|JNWTEJbWJMfbMRVMIRTPAEUQLOWTEIZU|JNWTEJbWJMfbMRVMIRTPAEUQLOWTOSbW|JNWTEJbWJMfbMRVMIRTPAEUQLOWTRUYR|JNWTEJbWJMfbMRVMIRTPAEWTEIaWNSWN|JNWTEJbWJMfbMRVMIRTPAEWTEIbWLOUQ|JNWTEJbWJMfbMRVMIRTPAEWTEIZVIMUQ|JNWTEJbWJMfbMRVMIRTPAEWTEJbWLOUQ|JNWTEJbWJMfbMRVMIRTPAEWTEJUQJMQS|JNWTEJbWJMfbMRVMIRTPAEWTEJZVJMUQ|JNWTEJbWJMfbMRVMIRTPAEWTLOaVRaeV|JNWTEJbWJMfbMRVMIRTPBEWTEIbWAEUQ|JNWTEJbWJMfbMRVMIRTPLOWTAEZVEIVM|JNWTEJbWJMfbMRVMIRTPLOWTAEZVEJVM|JNWTEJbWJMTPMQURNUYRAEfbLOcYOTXO|JNWTEJbWJMTPNRUNKRfbFKWTAETOLSVF|JNWTEJbWJMTPNRUNKRfbMQVMQJaVIMWS|JNWTEJbWJMTPNRUNKRfbMQVMQJWSIMYU|JNWTEJbWJMTPNRUNKRfbMQVMQJWTJNYU|JNWTEJbWJMTPNRUNKRWSMQVMQJfbLOSL|JNWTEJbWJMTPNRUNKRWTMQVMQJYUJMUQ|JNWTEJbWJMTPNRUNKRZUFKUNKRXTBFWS|JNWTEJbWJMTPNRUNKRZUFKUNKRXTMQVM|JNWTEJbWJMUQMRVMIRTPAEWTEIZUFJdZ|JNWTEJbWJMUQMRVMIRTPLOWSNWaTAEea|JNWTEJbWJMUQMRVMIRTPLOWTAEaVRaeV|JNWTEJbWJMUQMRVMIRTPLOWTRUYRNUQM|JNWTEJbWJMUQNRQJFMfbLOZUMQUNKRTK|JNWTEJbWJMUQNRQJFMfbMQVMQJTOLSWE|JNWTEJbWJMUQNRQJFMfbMQVMQJZVIMdZ|JNWTEJbWJMUQNRQJFMTPBEfbKNVSMQSJ|JNWTEJbWJMUQNRQJFMTPMQVMQJYUJNUQ|JNWTEJbWJMURNUZJFMfbAEdZKOTKGNXT|JNWTEJbWJMURNUZJFMfbLOdZAETPMQWT|JNWTEJbWJMURNUZJFMfbMQdZKNTPNRVM|JNWTEJbWJMURNUZJFMVSLOSLHOfbAEdZ|JNWTEJbWJMVSMQSJFMTPKNWTBFaWFKWS|JNWTEJTOKTXOLSVOAEURNUYRJNRKGNbW|JNWTEJTOKTXOLSVOIMOKFOURNUYIJNbW|JNWTEJTOLSVOKTXOAEUQIMaWGLYULSUR|JNWTEJTOLSVOKTXOAEUQIMbWGLfbLSaV|JNWTEJTOLSVOKTXOAEURNUYRGLaVLSVO|JNWTEJTOLSVOKTXOAEURNUYRJNRKGNbW|JNWTEJTPBEbWJMUQNRQJFMWTKNTOLSVO|JNWTEJTPJMbWBEUQNRQJFMWTMQVMQJaV|JNWTEJTPJMbWMQURNUYRAEfbKOWSFJRM|JNWTEJTPJMbWMQURNUYRAEfbLOcYHLWS|JNWTEJTPJMbWMQURNUYRAEfbLOcYOTXO|JNWTEJTPJMbWMQURNUYRAEfbLOWTEJaW|JNWTEJTPJMbWMQURNUYRAEfbLOWTFJRM|JNWTEJTPJMbWMQURNUYRLOfbOTXOKTbX|JNWTEJTPJMbWMQWTLOURNUYRAEaWFJWS|JNWTEJTPJMbWMRVMIRfbLOWTAEaVRaeV|JNWTEJTPJMbWMRVMIRUQLOWTRUYRNUQM|JNWTEJTPJMbWMRVMIRWTBEfbEIUQRUYR|JNWTEJTPJMbWNRUNKRfbAEWTEJbWFKWS|JNWTEJTPJMbWNRUNKRWSAEfbMQVMQJaV|JNWTEJTPJMbWNRUNKRWSMQVMQJfbLOSL|JNWTEJTPJMbWNRUNKRZUFKUNKRdZBFWS|JNWTEJTPJMbWNRUNKRZUFKUNKRdZBFWT|JNWTEJTPJMbWNRUNKRZUFKUNKRdZMQVM|JNWTEJTPJMbWNRUNKRZUFKUNKRXTBFWS|JNWTEJTPJMbWNRUNKRZULOUNFKPLGPNG|JNWTEJTPJMUQMRVMIRbWLOWTRUYRNUQM|JNWTEJTPJMUQNRQJFMbWAEfbMQVMQJYU|JNWTEJTPJMUQNRQJFMbWAEWTMQVMQJYU|JNWTEJTPJMUQNRQJFMbWBFWTMQVMQJYU|JNWTEJTPJMUQNRQJFMbWLOWTAEfbHLaW|JNWTEJTPJMUQNRQJFMbWMQVMQJYUIMUQ|JNWTEJTPJMUQNRQJFMbWMQVMQJYUJMfb|JNWTEJTPJMUQNRQJFMbWMQVMQJYUJNUQ|JNWTEJTPJMUQNRQJFMXTMQVMQJbXJMaV|JNWTEJTPJMVSNWbSMQaVAESOKTPWEJWT|JNWTEJTPJMVSNWbSMQfbFJbWIMWTJNSJ|JNWTEJTPJMVSNWbSMQURAEfbLOSLHObW|JNWTEJTPJMVSNWbSMRUNKRXTAETOEJfb|JNWTEJTPJMXTMQTOKTPWGKbXAEXTEJTP|JNWTEJTPJMXTMQTOLSVOKTPWAEaVFKUR|JNWTEJTPJMXTMQTOLSVOKTPWAEWTEJTP|JNWTEJTPJMXTMRVMIRaWLObXBEUQHLZU|JNWTEJTPJMXTMRVMIRbXBEfbEIUQRUYR|JNWTEJTPJMXTMRVMIRZVAEVMEIaWIRWS|JNWTEJTPJMXTMRVMIRZVAEVMEIcZIRZV|JNWTEJTPJMXTMRVMIRZVLOVMOXUQHLcZ|JNWTEJTPJMXTNRUNKRTOLSVOAEbXEJXT|JNWTEJTPJMXTNRUNKRTOLSVOFKOFBKbX|JNWTEJTPJMXTNRUNKRZUFKUNKRbWAEfb|JNWTEJTPJMXTNRUNKRZUFKUNKRbWBFWS|JNWTEJTPJMXTNRUNKRZUFKUNKRbWMQVM|JNWTEJTPJMXTNRUNKRZUFKUNKRdZMQVM|JNWTEJTPLObWOTXOKTfbTXVRFKZVJMUQ|JNWTEJTPLOVRBEbWJMWTMVZJENUQFJaV|JNWTEJTPLOVRBEbWJMWTMVZLHOaVEJVR|JNWTEJTPLOVRJMUQMVZJFMQJBFYUFMUQ|JNWTEJUQAETPLObWNSWNKRVMIRfbJNbW|JNWTEJUQNRVMIRbWAETPJNfbEIZUKOdZ|JNWTEJUQNRVMIRZVAEVMEIcZIRZVJMQJ|JNWTEJURNUZQAEYUJNVREJTPLOcYHLaV|JNWTEJVRBEbWJMTPMVZJFMUQLOQJENWT|JNWTEJVRJMUQMVZJFMQJBEYUENUQAEdZ|JNWTEJVRJMUQMVZJFMQJKOTKGEXTEJaV|JNWTEJVRJMUQNUQJFMZJBEYUENUQLOTP|JNWTEJVRLObWBEaVJMVSMVSLHOZJENUQ|JNWTEJVRLOTPGLPGCLUQNUYRJNZVNUQZ|JNWTFJbWJMTPMQfbNRUNKRVMQJWTIMaV|JNWTFJbWJMTPMRVMIRWTEJaWAEdaJMUQ|JNWTFJbWLOVSOVaRHLZVJMTPMQVSQZcV|JNWTFJTPBFbWJMWTNRUNKRVSMQSOLSZU|JNWTFJTPBFVRJMZVMQcZLObWHLebNSWN|JNWTFJTPJMXTBFTOLSVOKTPWHLWTGKTP|JNWTFJTPJMXTMRVMIRbXLOZVEIVMIRcZ|JNWTFJUQBFTPLObWOTXOKTfbTXZUNRVM|JNWTFJURNUYRJMTPEJbWLOWTBEfbHLbW|JNWTFJVRJMTPMVZJENUQAEYUBFURNUQZ|JNWTFJVRJMUQMVZJENTPLObWAEWTNSYU|JNWTFJVRJMZVMQcZLOTPCFbWEJebOTXO|JNWTLOaWGLTPOTPGTRbWCLWSNWUPEJXT|JNWTLOaWNRVMIRUNKRTKFOWTHLTKGNXT|JNWTLObWEJfbGLTPAEPGCLVRDGUQNUYR|JNWTLObWGLTPEJPGCLWTLPVRPWaTOSTP|JNWTLObWHLTPNRUNKRVMIRfbEJZVJMdZ|JNWTLObWHLTPNRUNKRVMIRWTEJTKGNPG|JNWTLObWHLUQNRVMIRTPEJWTJMQJFMaW|JNWTLObWNRUNKRVMIRTKGNfbFKXTHLbX|JNWTLObWNRUNKRVMIRTKGNXTHLfbFKbX|JNWTLObWNRVMIRUNKRTKGNWTHLfbEJTO|JNWTLOUQNRVMIRTPEJZVJMQJFMVSOVYU|JNWTLOVREJaVBEbWJMUQNUQJENZQNRVM|JNWTLOVREJbWJMUQNUQJFMZJBEJFKBTK|JNWTLOVREJTPJMUQMVZJFMQJBEYUENUQ|JNWTLOVREJTPJMUQNUQJFMZJBFYUFMUQ|JNWTLOVREJZVAEUQNUYRGLbWLPcYHLeb|JNWTLOVRFJbWJMfbMVZJENURNUYRAEaV|JNWTLOVRFJbWJMfbMVZJENURNUYRAETP|JNWTLOVRFJbWJMTPMVZJENUQOSWTNRfb|JNWTLPUQPWbJENXTAEfbHLTPEJYULObX|JNWTLPUQPWbJENXTAETPHLYULOVSNWaT|JNWTLPUQPWbJENXTAETPKOfbFKbXCFVR|JNWTLPUQPWbJENXTAEYUHLTPLOVSNWaT|JNWTLPUQPWbJENXTHLTPAEfbEJYULObX|JNWTLPUQPWbJENXTHLTPAEfbLObXEJYU|JNWTLPUQPWbJENXTHLTPAEfbLObXEJZU|JNWTLPUQPWbJENXTHLTPAEYULOVSNWaT|JNWTLPUQPWbJENXTHLTPFJfbKOZUGKPG|JNWTLPUQPWbJENXTHLTPLOfbAEbXEJYU|JNWTLPUQPWbJFMQJENYUAEVRHLXTEJTP|JNWTLPUQPWbJFMQJENYUHLfbAEbWNRUN|JNWTLPURNUYRPWbSEJaWHLeaKOZUJMfb|JNWTNRUNKRVMIRaWFKdaLOaVRaWdEJYU|JNWTNRUNKRVMIRaWGKTPLOPLOTXOKaeM|JNWTNRUNKRVMIRaWLOTKFOWTHLTKGNXT|JNWTNRUNKRVMIRTOLSZURVaRFKRMKOea|JNWTNRUNKRVMIRTOLSZURVaRGKcZSWbS|JNWTNRUNKRVMIRTOLSZURVaRGKRMEJMI|JNWTNRUNKRVMIRTOLSZURVaRGKRMEJUQ|JNWTNRUNKRVMIRTOLSZURVaRGKRMHLea|JNWTNRUNKRVMIRTOLSZURVaRGKRMHLUQ|JNWTNRUNKRVMIRTOLSZURVaRGKRMKNMI|JNWTNRUNKRVMIRTOLSZURVaRGKUQEJQM|JNWTNRUNKRVMIRTOLSZURVaRGKUQHLda|JNWTNRUNKRVMIRTOLSZURVaRGKUQHLYU|JNWTNRUNKRVMIRTOLSZURVaRHLRMGKea|JNWTNRUNKRVMIRTOLSZURVaRHLRMGKMI|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOea|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOMI|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVMI|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVXT|JNWTNRUNKRVMIRTOLSZURVaRHLUQGKYU|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOda|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOYU|JNWTNRUNKRVMIRTPEIXTAEaWFKbXIMfb|JNWTNRUNKRVMIRTPEJbWAEfbJMWTEJZU|JNWTNRUNKRVMIRTPEJbWAEfbJNWTEIbW|JNWTNRUNKRVMIRTPEJbWAEWTJMfbEJaW|JNWTNRUNKRVMIRTPEJbWAEWTJNaWEJWS|JNWTNRUNKRVMIRTPEJXTAEbXJMaWFKda|JNWTNRUNKRVMIRTPEJZUJNdZAEXTEIbX|JNWTNRUNKRVMIRTPEJZUJNdZAEXTEJbX|JNWTNRUNKRVMIRTPEJZUJNdZAEXTFKbW|JNWTNRUNKRVMIRTPFKbWKNWTBFaWEJZU|JNWTNRUNKRVMIRTPLObWEIWTFKZVBEVM|JNWTNRUNKRVMIRTPLObWEJfbHLWTAETK|JNWTNRUNKRVMIRTPLObWEJWTHLTKGNPG|JNWTNRUNKRVMIRTPLObWHLWTEJTKGNPG|JNWTNRVMIRUNKRaWFKdaLOaVRaWdEJYU|JNWTNRVMIRUNKRaWGKdaKNaVRaWdEJTP|JNWTNRVMIRUNKRbWEJTPAEWTJMaWEJda|JNWTNRVMIRUNKRTOLSZURVaRGKRMHLea|JNWTNRVMIRUNKRTOLSZURVaRGKRMHLUQ|JNWTNRVMIRUNKRTOLSZURVaRGKUQEIYU|JNWTNRVMIRUNKRTOLSZURVaRGKUQHLda|JNWTNRVMIRUNKRTOLSZURVaRGKUQHLYU|JNWTNRVMIRUNKRTOLSZURVaRHLRMGKea|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOea|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOMI|JNWTNRVMIRUNKRTOLSZURVaRHLUQGKYU|JNWTNRVMIRUNKRTOLSZURVaRHLUQLOda|JNWTNRVMIRUNKRTOLSZURVaRHLUQLOYU|JNWTNRVMIRUNKRTPEJaVRadWAEZUJMUQ|JNWTNRVMIRUNKRTPEJbWAEWTJMaWEJWS|JNWTNRVMIRUNKRTPEJbWAEWTJMfbEJZU|JNWTNRVMIRUNKRTPFKbWEIWSLOSLHOfb|JNWTNRVMIRUNKRTPFKbWLOWTHLebCFZU|JNWTNRVMIRUNKRZUFKUNKRaWGKdZKNTP|JNWTNSVOLSaVKOTKFObWSbfWEJWTHLTK|JNWTNSVOLSTPIMXTKNbXMQURNUYRSWaV|JNXTEJbXJMVSMQSJFMTPAEfbLOWTEJbW|JNXTEJTOLSVOKTWPAEaVHLbXLOfbOSVO|JNXTEJTPJMVSMQSJFMWTAEbXKNaWNSWN|JNXTEJTPJMWSNWbSMQfbAEaWIMUREIda|JNXTEJTPJMWSNWbSMQSOKTPWLPfbGKUR|JNXTEJTPLOUQOTZUTXVRHLaVLOWSNWbL|JNXTLObXEJTPOTXOKTfbTXVRFKZVHLVS|JNXTLObXHLfbLPVSOVZJENTOKTXOIMOK|JNXTLObXHLTPNRUNKRVMIRfbEJWSOVZS|JNXTLObXHLTPNRUNKRVMIRfbEJWTFKaV|JNXTLObXHLTPNRUNKRVMIRfbEJWTFKZV|JNXTLObXHLTPNRUNKRVMIRfbEJZVJMdZ|JNXTLObXHLTPNRUNKRVMIRWSOVZSFJaV|JNXTLObXHLTPNRUNKRVMIRWTEITKGNPG|JNXTLObXHLTPNRUNKRVMIRWTEJTKGNPG|JNXTLObXHLUQNRVMIRTPEJWTJMQJFMaV|JNXTLObXHLUQNSWNKRTKGNVMIRfbFKbW|JNXTLObXHLUQNSWNKRVMIRTKGNfbFKaV|JNXTLObXHLUQNSWNKRVMIRTKGNfbLObW|JNXTLObXHLUQNSWNKRVMIRTKGNXTLOTK|JNXTLObXNRUNKRVMIRTKFOWSOVZSEJfb|JNXTLObXNRUNKRVMIRTKGNfbHLXTRUYK|JNXTLObXNRUNKRVMIRTKGNXTHLfbFKbX|JNXTLObXNRUNKRVMIRTKGNXTHLfbLOTK|JNXTLObXNRVMIRUNKRTKFOWSOVZSEJfb|JNXTLObXNRVMIRUNKRTKGNfbFKXTHLbX|JNXTLObXNRVMIRUNKRTKGNXTFKTOKTWP|JNXTLOTPNRUNKRVMIRWSOVZSEJbWGKfb|JNXTLOTPNRVMIRUNKRWSOVZSEJbWAEfb|JNXTLOTPOTVSTXSJENWSNWbSIMfbAEUQ|JNXTLOTPOTVSTXSJENWSNWbSIMSOKTPW|JNXTLPbXGLVRLOaVHLWSNWTaEJUQJMQJ|JNXTLPbXGLVRLOaVHLWSPWSbLPUQNUYR|JNXTLPbXGLVSDGSJENURNUYRAEebFJaV|JNXTLPbXGLVSDGSJFMUQBFQJENaVNSVO|JNXTLPbXGLVSLOSJENaVHLVRFJZVJMUQ|JNXTLPbXGLVSLOSLPGTOKTXOGKWTEJfb|JNXTLPbXGLVSLOSLPGUQHLTPEJWTNRfb|JNXTLPbXHLVSDHSJENUQAEZUEJaVBEVS|JNXTLPbXHLVSDHSJENURNUYRAEebFJcY|JNXTLPbXHLVSDHSJFMURMVaREJebBFYU|JNXTLPbXNRUNKRVMIRebEJTOAEZVJMcZ|JNXTLPbXNRUNKRVMIRebEJZUJNcZAEaV|JNXTLPbXNRUNKRVMIRebEJZUJNcZBETO|JNXTLPbXNRUNKRVMIRebEJZUJNcZGLZV|JNXTLPbXNRUNKRVMIRebEJZUJNcZHLZV|JNXTLPbXNRUNKRVMIRebEJZUJNcZNSUN|JNXTLPbXNRUNKRVMIRTOEJebJMZVAEcZ|JNXTLPbXNRUNKRVMIRZVEIVMIRebAEcZ|JNXTLPbXNRUNKRVMIRZVEIVMIRebAEdZ|JNXTLPbXNRUNKRVMIRZVEJVMJQTOAEcZ|JNXTLPbXNRUNKRVMIRZVEJVMJQTOAEfb|JNXTLPbXNRVMIRUNKRZVEIVMIRebAEdZ|JNXTLPbXNRVMIRUNKRZVEIVMIRebAETO|JNXTLPbXNRVMIRUNKRZVEJVMJQTOAEcZ|JNXTLPUQEJVSAEbXIMZUEIaVGLebMRVM|JNXTLPUQEJVSGLbXLOSLPGfbHLTPAEWT|JNXTLPUQEJZUGLbXLOURNUQZAEYUHLVR|JNXTLPUQEJZUGLbXLOURNUQZJMVSOVZS|JNXTLPUQEJZUGLVRLObXHLaVDHebAEWS|JNXTLPUQEJZUHLVSBEaVDHbXNRVMIRUN|JNXTLPUQFJVSGLbXLOSLPGTOKTWPHLaV|JNXTLPUQGLbXLOZUHLVRIMQSOMaVLOdZ|JNXTLPUQGLYULObXHLVSOVZJFMQJENaV|JNXTLPUQGLZUDGbXEJURNUQZJNYUFJUQ|JNXTLPUQGLZUEJbXLOURNUQZJMVSOVZS|JNXTLPUQGLZULObXEJURNUQZJMVSOVZS|JNXTLPUQGLZULObXHLURNUQZEJYUJMUQ|JNXTLPUQGLZULObXHLURNUYREJRMIRVM|JNXTLPUQGLZULObXHLURNUYRKNRKIMQJ|JNXTLPUQGLZULObXHLURNUYRKNTKNGcZ|JNXTLPUQGLZULObXHLURNUYRKNTKNGeb|JNXTLPUQGLZULObXHLVRIMQSOMebLOaV|JNXTLPUQHLVSDHSJFMQJENZUIMbXMQUR|JNXTLPUQHLVSDHSJFMQJENZUIMURMVaR|JNXTLPUQHLVSEJbXDHYUIMZVAETOKTXO|JNXTLPUQHLZULObXEJURNUQZAEYUGLVR|JNXTLPUQHLZULObXNSWNPWaTKadWFKUR|JNXTLPUQNRVMIRaVRaeVKNVSEISJFMQJ|JNXTLPUQNRVMIRZUEIUNKRQMRUYRAETO|JNXTLPUQNRVMIRZUKNTOGKbXKTXOCGeb|JNXTLPUQNRVMIRZUKNTOGKbXKTXOEIeb|JNXTLPUQNRVMIRZUKNTOGKbXKTXOFKOF|JNXTLPUQNRVMIRZUKNTOGLWSNWbSCGUN|JNXTLPUQNRVMIRZURVaRKNRKFXcZEJUR|JNXTLPUQNRVMIRZURVaRKNRKFXcZGKUR|JNXTLPUQNRVMIRZURVaRKNRKFXUREJcZ|JNXTLPUQNRVMIRZURVaRKNRKFXUREJRM|JNXTLPUQNRVMIRZURVaRKNRKFXUREJRN|JNXTLPUQNRVMIRZURVaRKNRKFXUREJYU|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZ|JNXTLPUQNRVMIRZURVaRKNRKFXURHLcZ|JNXTLPUQNRVMIRZURVaRKNRKFXWSEJbW|JNXTLPUQNRVMIRZURVaRKNRKFXWSHLbW|JNXTLPVREJaVHLbXLOWSPWSbGLUQNUYR|JNXTLPVREJbXGLZVLOUQNUQZHLVRJMZU|JNXTLPVREJbXHLaVLOWSNWTaJMUQFJaW|JNXTLPVREJbXHLaVLOWSPWSLGPVSCGSb|JNXTLPVREJbXJMTOMVZJKTXOFMebMQcZ|JNXTLPVRFJbXJMTOMVZJENOFBKebNRUN|JNXTLPVRGLaVLObXEJWSPWSbHLUQNUYR|JNXTLPVRGLaVLObXHLWSPWSbLPUQNUYR|JNXTLPVRGLbXEJaVAEWSNWTaJNVSNWaT|JNXTLPVRHLaVEJbXJMWSNWTaMQfbLObW|JNXTLPVSEJUQGLbXLOSLPGTPAEWTHLfb|JNXTLPVSGLSJFMbXLOUQBFQJFMaVEJVS|JNXTLPVSGLSJFMbXLOUQBFQJFMaVMRVM|JNXTLPVSHLSJENZVLObXFJUQGLYUCFUR|JNXTLPVSHLSJFMbXMQaVLOVSOVZSQZcV|KNVRFKaVJMUQNUQJENYRNUZQAEWTLOTP|KNVRFKaVJMXTMQTPEJbXLOdaJMWTBEaW|KNVRFKaVLPVSGLUQNUYRJNSJEUcYBEYR|KNVRFKWSNWbSJMRNKRUNLOSLHOaVBFda|KNVRFKWTJMaVEJTOLSVFBKdaMVaRHLZV|KNVRFKWTJMTPMVZJENUQLObWAEWTNRQM|KNVRFKWTJMTPMVZJENUQLObWBEWTCFfb|KNVRFKWTJMTPMVZJENUQLObWOSWTNRfb|KNVRFKZVLOUQNUQZJNWTEJTPIMVRMVZL|KNVRGKWTLPbWHLaVJMWSNWTaMQfbLObW|KNVRGKZVJMUQNUQZMRVMIRWSLOSLHObW|KNVRGKZVJMUQNUQZMRVMIRWTKNTPDGXT|KNVRGKZVJMWTDGTPMQdZLObWGLPGCLfb|KNVRGKZVJMWTDGUQNUQZMRVMIRTPEJbW|KNVRGKZVLPUQNUQZIMYUMQWSKNbWFKfb|KNVSIMUQEIXTLPbXMRTOGKebKTXOHLOH|KNVSIMUQMRXTRVaKFXZVLOSLHOWTGKbW|KNVSIMXTEITPMRWTNWUEAJbSIMZVMQcZ|KNVSIMXTFKTOKTWPNWbSMQUREIaVBFda|KNVSIMXTMQTOJMSJLSWNMRNKENaWFOWS|KNVSIMXTMQTPFKaVJMSJMFUREJRMJNMI|KNWSNWaTJMVSMQTPIMbWFJeaJNSJENaV|KNWSNWbSIMXTLPTOMQUREIRMIRVMGKMI|KNWSNWbSIMXTLPTOMQUREIRNJMfbGKNG|KNWSNWbSJMXTMQTPEJfbJMURFKaWAESN|KNWSNWbSLPebGLSOLSVOPTOKFObWJNWP|KNWSNWbSLPebGLUQIMYUFKUREIbWJNSJ|KNWSNWbSLPebJMbWEJfbMQXTGLbXJMUR|KNWSNWbSLPebJMbWHLfbMQSOLSWNIMNJ|KNWSNWbSLPebJMUQMRVMIRbWFJZVCFVM|KNWSNWbSLPfbJMbWMQSOEJWTPWaTJMda|KNWSNWbSLPfbJMURMQYUEJRNJMURFKbW|KNWTFKbWJMTPMRVMIRWSNWUNKRaTEJfb|KNWTFKbWLPVSGLTOKTXOPTWGDTaWTadW|KNWTFKTPBFbWJMfbNRUNKRWTMQVMQJaV|KNWTFKTPBFbWJMUQNRQJENVMIRWTAEZU|KNWTFKTPBFbWNRUNJbfWIMYUMQWTEJTO|KNWTFKTPBFUQNRVMIRbWEIWTJMQJFMZU|KNWTFKTPBFUQNRVMIRXTJMQJFMTOLSaV|KNWTFKUQBFTPLObWNSWNKRVMIRfbGKbW|KNWTJMTPMRVMIRXTFKbXLOaWHLdaEJaV|KNWTLPVRPWaTFKbWJMfbMVZJENUQHLTP|KNWTLPVRPWRKGNbSNWaTHLTPLOURFKYU|KNXTJMTOLSVOMQURNUYREJWSAEbWGLfb|KNXTLPVSIMUQMRTOGKZVKTVMEIbXIRXO|KOWTGKTPCGURJMbWEJWSMQfbJMbWFJeb|KOWTJMTKFOaWOSVOLSWNMRNKGNUQEJea|KOWTJMTKFObWBFWTGKTPDGVRMVaREJfb|KOWTJMTKFObWGKWTBFTPDGUQEJYUAEUR|KOWTJMTKFObWGKWTBFTPDGVRMVaREJfb|KOWTJMTKFObWMRUNOSVOLJaVHLYUBFWT|KOWTJMTKFObWOSVOLbfWHLXTMQWSLPTO|KOWTJMTKFOURMQbWEJWSJMfbBFZUQZdU|KOWTLPTKFObWGKURJMWSEJSLHOaWDHeb|KOWTLPTKGNURNUYRJMbWHLWSLOSLPGfb|KOWTOSVOLSTPFKUQBFaVKOYUJMQJENVR|KOWTOSVOLSTPGKURCGYUJMaVKORNSJVR|KOWTOSVOLSTPGKXTIMUQJNQJFMaVBFVO|KOWTOSVOLSTPJNXTIMbXEJUQAEaVEIVO|KOWTOSVOLSURJMaVGLVOLSdaMVaRCGea|KOWTOSVOLSURJMYUMVaRFJdaSVZSIMRI|LOUQHLWTJNQMIRVMEIZVIRVMAEMINRcZ|LOUQHLWTJNQMIRVMEIZVIRVMAEMINRTP|LOUQJMQJFMVSOVZSKOSLHOdZEJaVMQWS|LOUQJMQJFMWSHLYUMRUNKRVMIRbWOVZS|LOUQJMQJFMWTEJbWMQTPJMYUMRUNKRVM|LOUQJMQJFMWTMQbWEJVRKNRKOFWSBEfb|LOUQJMQJFMWTMRVMIRbWEJTPAEWTEIZU|LOUQJNWSNWbLHOfbIMQJENYUAEVRGLbW|LOUQJNWTNRVMIRZVEIVMIRbWAEdZEJaV|LOURJNYUNSWNIMRIKYbWEJWSHLXTOXSN|LOVRHLZVJMWSMQdZEJSNJSXTOXVHAEbW|LOVRHLZVJMWSMQdZEJSNJSXTOXVHKObW|LOVRJMaVMQeaEJRMIRUEAJWTJMYUHLTP|LOVRJNWTHLTPEJbWJMWSNWaTMVZSOVda|LOVSOVZSJNSJENUQHLWTBEbWFJaVLOVR|LOWSGLbWKNURNUYRJMWTEJTKFOfbLPSL|LOWSGLUQLPSLPGZUJMQJFMXTHLTPMRVM|LOWSHLaWKNUQNRVMIRXTOVZSLPSOJNOL|LOWSHLbWJMUQMRVMIRSNRUYROSXTSJTP|LOWSHLbWJMWTMRVMIRUNKRTKFVZSEIfb|LOWSHLbWKNURNUYRJMSNMQWTFKTPIMRI|LOWSJNSJFMbWMRUNKRVMIRWSOVZSBFXT|LOWTHLTPJNVRFJaVDHeaJMUQNUQJENYR|LOWTJMaWMRVMIRUNKRTKFOWSOVZSEIdZ|LOWTJMbWEJTPMQWTJNfbNSURAEaWFJWN|LOWTJMbWEJWSAESLGWaTCGTPMRVMIRUN|LOWTJMbWEJWSMQSLGWaTCGfbAETOKTXO|LOWTJMbWMRUNKRTKGNVMIRfbFKWTHLbW|LOWTJMbWMRUNKRVMIRTKGNebHLWSNWbS|LOWTJMbWMRVMIRUNKRTKGNfbFKXTHLbX|LOWTJMTPMRUNKRVMIRbWEJWTFKfbAEaW|LOWTJMUREJbWJNfbNUZJFMTPMQWTAEdZ|LOWTJMUREJbWMQRMIRVMGLMILPaVHLeb|LOWTJNbWHLTPNRVMIRUNKRfbEJZVJMdZ|LOWTJNbWNRVMIRUNKRTKGNebFKWSNWbS|LPUQJNVSEJSOKTXONRWSRVaRPTOXJMQJ|LPVRJMaVMQWSHLSOLSVOKTXOFJOLJMLH|LPWSGLbWKOfbJMUQDGQJENSJFMWSGKbW|LPWSGLbWLOSLPGXTJMUQMRVMIRZVEIVM|LPWSGLSOKTXOLSVOIMaVMQbWEIWSJMfb|LPWSGLSOKTXOLSVOJMaVMRUNFJVSJMZV|LPWSIMSOKTXOEIbWMQfbJMURAEVSMVaR|LPWSJMbWMQSOKTXOEJURJMfbAEbXEJWT|LPWSJMSOKTXOEJbWMQfbJMVRMVZSQZcV|LPWSJMSOKTXOMQbWEJfbJMURFJYUCFbX|LPWSJMSOKTXOMQbWFJWTPWaTJMfbEJbX|LPWSJMSOKTXOMQUREJRMIRVMGLaVLSVO|LPWSKNbWGLebFKVRLOSLPGZVGLWTLPTO|LPWSKNURNUYRGLSOLSVOJMbWMVaREJea|LPWSKNURNUYRJMbWEJfbAEXTFKTOKTbX|LPWSKOSLHObWGLURDHWSFKYUJNSJENaW|LPWTPWbSIMfbMQSOKTXOJMUREIbWAEVS|LPWTPWbSIMUREISOKTXOMQfbJMaWAEbX|LPWTPWbSJMfbMQSOKTXOEJbXJMXTFJaW|LPWTPWbSJMURMQaWEJfbAEeaJMZUQZdU|LPWTPWbSJMXTMQTPIMSOKTPWFKUREIWT|LPWTPWbSKNaWGLXTFKTPKOPGCLURNUYR|LPWTPWbSKOSLGPXTPWaTFKTPCGfbBFUR";

function parsePDNLine(pdnLine) {
    const moves = [];
    const tokens = pdnLine.replace(/\d+\./g, ' ').trim().split(/\s+/);
    for (const tk of tokens) {
        if (!tk || /[{}()\[\]]/.test(tk)) continue;
        const seps = tk.split(/[-x]/);
        if (seps.length < 2) continue;
        const from = algToIdx(seps[0]);
        const to   = algToIdx(seps[seps.length - 1]);
        if (from >= 0 && to >= 0) moves.push({ from, to });
    }
    return moves;
}

// ── Opening book map: hash -> array of encoded moves (from*64 + to) ──────
let bookMap = null;


    function bookAddLine(state, moveIdxs) {
    const s = state.clone();
    for (const mi of moveIdxs) {
        const lm = s.getMoves();
        const found = lm.find(m => m.from === mi.from && m.to === mi.to);
        if (!found) return; // invalid line — stop here
        const h = s.hash;
        if (!bookMap.has(h)) bookMap.set(h, []);
        const arr = bookMap.get(h);
        if (!arr.includes(found.from * 64 + found.to))
            arr.push(found.from * 64 + found.to);
        s.applyMove(found);
    }
}

// ── Build the opening book (progressive async loading) ────────────────────

    function buildOpeningBook() {
        bookMap = new Map();
        const initState = new State();

        // 1) Linhas do BOOK_DATA comprimido (formato char-pair) — síncrono (rápido)
        const lines = BOOK_DATA.split('|');
        for (const line of lines) {
            if (line.length < 2) continue;
            const moveIdxs = [];
            let ok = true;
            for (let i = 0; i < line.length - 1; i += 2) {
                const fsq = charToSq[line[i]];
                const tsq = charToSq[line[i+1]];
                if (fsq === undefined || tsq === undefined) { ok = false; break; }
                moveIdxs.push({ from: fsq, to: tsq });
            }
            if (ok && moveIdxs.length > 0) bookAddLine(initState, moveIdxs);
        }

        // 2) [BOOK-V31-FULL] BOOK_DATA_EXT + PDN_EXTRA_LINES processados em lotes
        // assíncronos para nunca bloquear o thread. Motor joga imediatamente com
        // BOOK_DATA; os 4780+3152 linhas extra carregam em background.
        // Fase A: BOOK_DATA_EXT (comprimido — ultra-rápido por tick)
        const extLines = BOOK_DATA_EXT.split('|').filter(l => l.length >= 2);
        let extIdx = 0, pdnIdx = 0;
        const BATCH_EXT = 200; // linhas comprimidas: ~1-2ms cada batch (muito mais rápido que PDN)
        const BATCH_PDN = 60;  // linhas PDN: mais lento (~5-8ms)

        function processExtBatch() {
            const end = Math.min(extIdx + BATCH_EXT, extLines.length);
            for (; extIdx < end; extIdx++) {
                const line = extLines[extIdx];
                if (line.length < 2) continue;
                const moveIdxs = [];
                let ok = true;
                for (let i = 0; i < line.length - 1; i += 2) {
                    const fsq = charToSq[line[i]], tsq = charToSq[line[i+1]];
                    if (fsq === undefined || tsq === undefined) { ok = false; break; }
                    moveIdxs.push({ from: fsq, to: tsq });
                }
                if (ok && moveIdxs.length > 0) bookAddLine(initState, moveIdxs);
            }
            if (extIdx < extLines.length) { setTimeout(processExtBatch, 0); }
            else                          { setTimeout(processPDNBatch, 0); } // fase B
        }

        function processPDNBatch() {
            const end = Math.min(pdnIdx + BATCH_PDN, PDN_EXTRA_LINES.length);
            for (; pdnIdx < end; pdnIdx++) {
                try {
                    const moveIdxs = parsePDNLine(PDN_EXTRA_LINES[pdnIdx]);
                    if (moveIdxs.length > 0) bookAddLine(initState, moveIdxs);
                } catch(e) { /* linha inválida — ignora */ }
            }
            if (pdnIdx < PDN_EXTRA_LINES.length) setTimeout(processPDNBatch, 0);
        }
        setTimeout(processExtBatch, 50); // inicia 50ms após carregamento
    }

    // [BOOK-V27-EVAL] bookProbe com avaliação de engine: cada candidato do livro
    // é avaliado estaticamente após o lance. O resultado pondera a seleção via
    // softmax com temperatura adaptativa [BOOK-V29-TEMP]: T=14 na abertura,
    // T=10 no meio-jogo, T=8 no final — menos aleatoriedade quando importa mais.
    function bookProbe(state) {
        const h = state.hash;
        const arr = bookMap.get(h);
        if (!arr || arr.length === 0) return null;
        const lm = state.getMoves();
        const candidates = [];
        for (const encoded of arr) {
            const fr = Math.floor(encoded / 64);
            const to = encoded % 64;
            const found = lm.find(m => m.from === fr && m.to === to);
            if (found) candidates.push(found);
        }
        if (candidates.length === 0) return null;
        if (candidates.length === 1) return candidates[0];
        // Avalia cada candidato com eval() estático após o lance
        const scored = candidates.map(m => {
            const s2 = state.clone();
            s2.applyMove(m);
            return { move: m, score: -s2.eval() }; // negado: eval() é relativo ao jogador seguinte
        });
        const maxSc = scored.reduce((mx, e) => Math.max(mx, e.score), -Infinity);
        // [BOOK-V29-TEMP] Temperatura adaptativa: abertura=14, meio-jogo=10, final=8
        const pcCount = state.wP + state.bP + state.wK + state.bK;
        const BOOK_TEMP = pcCount > 18 ? 14 : pcCount > 14 ? 10 : 8;
        const weights = scored.map(e => Math.exp((e.score - maxSc) / BOOK_TEMP));
        const total = weights.reduce((s, w) => s + w, 0);
        let rnd = Math.random() * total;
        for (let i = 0; i < scored.length; i++) {
            rnd -= weights[i];
            if (rnd <= 0) return scored[i].move;
        }
        return scored[scored.length - 1].move;
    }

    // ════════════════════════════════════════════════════════════════════════
    //  BUSCA v2 — PVS + LMR + NMP + IID + Aspiração + Quiescência
    // ════════════════════════════════════════════════════════════════════════
    let nodes = 0, searchStartTime = 0, searchTimeLimitMs = 30000, searchAborted = false;

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
                const tsc = tte.sc * 20;
                if (tte.fl === TE) return tsc;
                if (tte.fl === TL && tsc >= beta) return beta;
                if (tte.fl === TU && tsc <= alpha) return alpha;
            }
        }

        const poolPos = saveMP();
        const moves = state.getMoves();
        if (moves.length === 0) { restoreMP(poolPos); return -9999 + ply; }
        const hasCaptures = moves[0].captured.length > 0;

        // Forced move extension (captures included — single legal move is forced)
        let extension = 0;
        if (moves.length === 1 && ply < 16) extension = 1;

        // Internal Iterative Deepening
        if (hfm < 0 && depth >= 3 && !hasCaptures) {
            search(state, depth - 3, alpha, beta, ply, prevFrom, prevTo);
            if (searchAborted) { restoreMP(poolPos); return alpha; }
            const tte2 = ttProbe(hash);
            if (tte2) { hfm = tte2.mv >> 6; htm = tte2.mv & 0x3F; }
        }

        // Null-move pruning
        let staticEval = null;
        if (!isPV && depth >= 4 && !hasCaptures && beta < 9000 && beta > -9000) {
            const pc = state.wP + state.bP + state.wK + state.bK;
            const sideKings = state.turn === 1 ? state.wK : state.bK;
            const isPureKingEG = (state.wP === 0 && state.bP === 0 && pc <= 6);
            if (!isPureKingEG && (pc >= 10 || sideKings > 0)) {
                staticEval = state.eval();
                if (staticEval >= beta) {
                    const oldTurn = state.turn; state.turn = -state.turn; state.hash ^= zt;
                    const R = depth >= 9 ? 4 : depth >= 6 ? 3 : 2;
                    const nullScore = -search(state, depth - 1 - R, -beta, -beta + 1, ply + 1, -1, -1);
                    state.turn = oldTurn; state.hash ^= zt;
            if (searchAborted) { restoreMP(poolPos); return alpha; }
                    if (nullScore >= beta) { restoreMP(poolPos); return nullScore; }
                }
            }
        }

        // Razoring
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

            // LMP
            if (!isPV && isQuiet && depth <= 5 && quietCount >= LMP_TABLE[Math.min(depth, 5)]) break;
            if (isQuiet) quietCount++;

            // Futility pruning
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
                // LMR
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

    // ── Aprofundamento iterativo + wrapper getBestMove ────────────
    function getBestMove(state, maxDepth, timeLimitMs) {
        const poolPos = saveMP();
        const moves = state.getMoves();
        if (moves.length === 0) { restoreMP(poolPos); return { move: null, score: -10000, depth: 0, nodes: 0, pv: [], isBook: false }; }

        // Book probe
        const bookMove = bookProbe(state);
        if (bookMove) {
            restoreMP(poolPos);
            return { move: cloneMv(bookMove), score: 0, depth: 0, nodes: 0, pv: [cloneMv(bookMove)], isBook: true };
        }

        if (moves.length === 1) {
            const res = { move: cloneMv(moves[0]), score: state.eval(), depth: 1, nodes: 1, pv: [cloneMv(moves[0])], isBook: false };
            restoreMP(poolPos);
            return res;
        }

        // Reset
        for (let ki = 0; ki < killers.length; ki++) killers[ki] = 0;
        for (let hi = 0; hi < histTable.length; hi++) histTable[hi] = 0;
        nodes = 0; searchAborted = false;
        searchStartTime = Date.now(); searchTimeLimitMs = timeLimitMs || 0;

        let bestMove = moves[0], bestScore = -Infinity, reachedDepth = 0;

        for (let depth = 1; depth <= maxDepth; depth++) {
            // History decay
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

        // Root-level variety adaptativa
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

        // Extract PV
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
            move: cloneMv(bestMove),
            score: bestScore,
            depth: reachedDepth,
            nodes,
            pv: pv.map(cloneMv),
            isBook: false,
        };
    }    // ════════════════════════════════════════════════════════════════════════
    //  ESTADO DA UI
    // ════════════════════════════════════════════════════════════════════════
    let gameState = new State(), selIdx=-1, valTgt=[], lastM=null;
    const txtStatus   = document.getElementById('status-text');
    const barStatus   = document.getElementById('status-container');
    const txtAnalysis = document.getElementById('analysis-text');

    // ── Relógio ───────────────────────────────────────────────────────────────
    function startClock() {
        if (clockInterval) return;
        clockLastStamp = Date.now();
        clockInterval  = setInterval(clockTick, 250);
    }
    function stopClock() {
        if (clockInterval) { clearInterval(clockInterval); clockInterval = null; }
        clockLastStamp = 0;
    }
    function clockTick() {
        if (!gameStarted || gameEnded || timeLimit === 0) return;
        const now     = Date.now();
        const elapsed = (now - clockLastStamp) / 1000;
        clockLastStamp = now;
        if (elapsed <= 0) return;
        if (gameState.turn === 1) {
            timeW -= elapsed;
            if (timeW <= 0) { timeW=0; updateClocks(); popModal("Fim de Jogo","Tempo esgotado! Vermelhas vencem."); return; }
        } else {
            timeB -= elapsed;
            if (timeB <= 0) { timeB=0; updateClocks(); popModal("Fim de Jogo","Tempo esgotado! Brancas vencem."); return; }
        }
        updateClocks();
    }
    function fTime(sec) {
        const s = Math.max(0, Math.ceil(sec));
        return `${Math.floor(s/60).toString().padStart(2,'0')}:${(s%60).toString().padStart(2,'0')}`;
    }
    function updateClocks() {
        const cw = document.getElementById('clock-white');
        const cb = document.getElementById('clock-black');
        if (timeLimit > 0) {
            cw.innerText = fTime(timeW); cb.innerText = fTime(timeB);
            const wActive  = gameState.turn===1 && gameStarted && !gameEnded;
            const bActive  = gameState.turn===-1 && gameStarted && !gameEnded;
            cw.className   = wActive ? (timeW<=30?'timer warning':'timer active') : 'timer';
            cb.className   = bActive ? (timeB<=30?'timer warning':'timer active') : 'timer';
        } else { cw.innerText=cb.innerText='--:--'; cw.className=cb.className='timer'; }
    }

    // ── DOM ───────────────────────────────────────────────────────────────────
    function initDOM() {
        const board = document.getElementById('board'); board.innerHTML='';
        // Build the 64 squares
        for (let r=7; r>=0; r--) for (let c=0; c<8; c++) {
            const idx=r*8+c, dark=(r+c)%2===0;
            const sq=document.createElement('div');
            sq.className=`square ${dark?'sq-dark':'sq-light'}`;
            sq.id=`sq-${idx}`; sq.onclick=()=>onSquareClick(idx);
            sq.oncontextmenu=(e)=>{ e.preventDefault(); if(editMode){ gameState.board[idx]=EMPTY; gameState.hashHist=[gameState.hash]; render(); } };
            board.appendChild(sq);
        }
        // Coordinates are in static overlays OUTSIDE .board — see updateCoords()
    }

    // [VIS-V19-COORD] Coordinate labels live in static overlay divs outside .board.
    // They never rotate. Content (order) is updated here whenever the view flips.
    //   White view — numbers left (bottom→top): 1…8  letters bottom (L→R): A…H
    //   Red   view — numbers left (bottom→top): 8…1  letters bottom (L→R): H…A
    function updateCoords() {
        const numDiv = document.getElementById('coord-numbers');
        const letDiv = document.getElementById('coord-letters');
        if (!numDiv || !letDiv) return;
        numDiv.innerHTML = '';
        letDiv.innerHTML = '';
        const flipped = cfgView === 'B';
        // Numbers: overlay is top→bottom, so index 0 = top row visually
        //   White: top = 8, bottom = 1  → array [8,7,6,5,4,3,2,1]
        //   Red:   top = 1, bottom = 8  → array [1,2,3,4,5,6,7,8]
        for (let i = 0; i < 8; i++) {
            const n = flipped ? (i + 1) : (8 - i);
            const el = document.createElement('div');
            el.className = 'coord-label';
            el.textContent = n;
            numDiv.appendChild(el);
        }
        // Letters: overlay is left→right
        //   White: A,B,C,D,E,F,G,H   Red: H,G,F,E,D,C,B,A
        for (let i = 0; i < 8; i++) {
            const c = flipped ? String.fromCharCode(72 - i) : String.fromCharCode(65 + i);
            const el = document.createElement('div');
            el.className = 'coord-label';
            el.textContent = c;
            letDiv.appendChild(el);
        }
    }

    function render() {
        // Collect capture victim squares for the selected piece's moves
        const captureVictimSquares = new Set();
        if (selIdx !== -1 && valTgt.length > 0 && valTgt[0].captured.length > 0) {
            for (const m of valTgt) {
                for (const sq of m.captured) captureVictimSquares.add(sq);
            }
        }

        for (let i=0; i<64; i++) {
            const sq=document.getElementById(`sq-${i}`); if(!sq) continue;
            const isDark = ((i>>3)+(i&7))%2===0;
            let cn=`square ${isDark?'sq-dark':'sq-light'}`;
            if (selIdx===i) cn+=' highlight';
            else if (lastM && (lastM.from===i || lastM.to===i)) cn+=' last-move';
            if (valTgt.find(m=>m.to===i)) cn+=' suggestion';
            else if (isDark && captureVictimSquares.has(i)) cn+=' capture-hint';
            sq.className=cn;
            const p=gameState.board[i];
            sq.innerHTML = p!==EMPTY
                ? `<div class="piece ${Math.sign(p)===1?'white':'red'} ${Math.abs(p)===2?'king':''}"></div>`
                : '';
        }
        const be=document.getElementById('board');
        if (cfgView==='B') be.classList.add('rotated'); else be.classList.remove('rotated');
        updateCoords();

        if (editMode) {
            txtStatus.innerText = "✏ Editando — coloque as peças e pressione ▶";
            barStatus.classList.remove('computing');
        } else if (!gameStarted) {
            txtStatus.innerText = gameEnded ? "Fim de Jogo" : "Pressione ▶ Iniciar / Continuar";
            barStatus.classList.remove('computing');
        } else if (!gameEnded) {
            const moves=gameState.getMoves(), draw=gameState.checkDraw();
            if      (moves.length===0) popModal("Fim de Jogo",`${gameState.turn===1?'Vermelhas':'Brancas'} vencem! (Sem lances legais)`);
            else if (draw)             popModal("Fim de Jogo", draw);
            else {
                txtStatus.innerText=`Vez das ${gameState.turn===1?'Brancas':'Vermelhas'}`;
                barStatus.classList.remove('computing');
            }
        }
        renderHist(); updateClocks(); updatePieceCount();
    }

    function updatePieceCount() {
        let wP=0,wK=0,bP=0,bK=0;
        for (let i=0;i<64;i++) {
            const p=gameState.board[i];
            if(p===W_MAN) wP++; else if(p===W_KING) wK++;
            else if(p===V_MAN) bP++; else if(p===V_KING) bK++;
        }
        const ew=document.getElementById('piece-count-w');
        const eb=document.getElementById('piece-count-b');
        if(ew) ew.textContent=`${wP}P ${wK}D`;
        if(eb) eb.textContent=`${bP}P ${bK}D`;
    }

    function renderHist() {
        const h = document.getElementById('history');
        h.innerHTML = '';
        // Tablita header: show tablita name and sequence
        if (cfgMode === MODE_TABLITA && tablitaManager && tablitaManager.currentTablita) {
            const hdr = document.createElement('div');
            hdr.style.cssText = 'padding:0.3rem 0.4rem;margin-bottom:0.3rem;background:#1a1d24;border-radius:4px;font-size:0.72rem;color:#ffa726;';
            const name = tablitaManager.getTablitaName();
            const display = tablitaManager.getTablitaDisplay();
            const gameNum = tablitaManager.gameNumber;
            hdr.innerHTML = `🏓 <strong>${name}</strong> <span style="color:#888;">(Jogo ${gameNum}/2)</span><br><span style="color:#8591a8;font-family:ui-monospace,monospace;">${display}</span>`;
            h.appendChild(hdr);
        }
        appendSequenceDOM(rootNode, 0, h);
        const a = h.querySelector('.active-move');
        if (a) a.scrollIntoView({ block: 'nearest' });
    }

    function appendSequenceDOM(node, plyCount, container) {
        const mkSpan = (cls, text) => {
            const s = document.createElement('span');
            s.className = cls; s.textContent = text; return s;
        };
        const txt = t => document.createTextNode(t);
        let curr = node, ply = plyCount, prevHadVars = false;
        while (curr.children.length > 0) {
            const main = curr.children[0], isWhite = (ply % 2 === 0);
            const hasVars = curr.children.length > 1;
            const moveNum = Math.floor(ply / 2) + 1;
            if (isWhite) {
                container.appendChild(mkSpan('ply-num', `${moveNum}.`));
                container.appendChild(txt(' '));
            } else if (curr === node || prevHadVars) {
                container.appendChild(mkSpan('ply-num', `${moveNum}...`));
                container.appendChild(txt(' '));
            }
            const ms = mkSpan((main === currentNode) ? 'active-move' : 'move-link', main.moveStr);
            ms.onclick = () => navToId(main.id);
            container.appendChild(ms);
            container.appendChild(txt(' '));
            for (let i = 1; i < curr.children.length; i++) {
                const v = curr.children[i];
                container.appendChild(txt('( '));
                container.appendChild(mkSpan('ply-num', `${moveNum}${isWhite ? '.' : '...'}`));
                container.appendChild(txt(' '));
                const vs = mkSpan((v === currentNode) ? 'active-move' : 'move-link', v.moveStr);
                vs.onclick = () => navToId(v.id);
                container.appendChild(vs);
                container.appendChild(txt(' '));
                appendSequenceDOM(v, ply + 1, container);
                container.appendChild(txt(') '));
            }
            prevHadVars = hasVars; curr = main; ply++;
        }
    }

    function popModal(title, desc) {
        document.getElementById('modal-title').innerText=title;
        document.getElementById('modal-desc').innerText=desc;
        document.getElementById('modal').style.display='flex';
        if (title==="Fim de Jogo") {
            gameEnded=true; stopClock();
            tablitaGameInProgress = false; // Mark Tablita game as ended
            const dl=desc.toLowerCase();
            if (dl.includes('empate')||dl.includes('draw')) gameResultType='draw';
            else if (dl.includes('brancas vencem')) gameResultType='white';
            else gameResultType='red';
            txtStatus.innerText="Fim de Jogo";
            barStatus.classList.remove('computing');
            selIdx=-1; valTgt=[];
            updateClocks();
            // [V21-STATS] Track CPU×CPU game results
            if (cfgMode===MODE_MVM) {
                const d=desc.toLowerCase();
                if      (d.includes('brancas vencem')) updateCpuStats('w');
                else if (d.includes('vermelhas vencem'))  updateCpuStats('b');
                else                                   updateCpuStats('d');
            }
            // Tablita mode: track match score and manage match flow
            if (cfgMode===MODE_TABLITA && tablitaManager) {
                const d = desc.toLowerCase();
                const playerIsWhite = tablitaManager.isPlayerWhite();
                let result;
                if (d.includes('empate') || d.includes('draw')) {
                    result = 'draw';
                    tablitaMatchScore.w++; tablitaMatchScore.b++;
                } else if (d.includes('brancas vencem')) {
                    tablitaMatchScore.w++;
                    result = playerIsWhite ? 'win' : 'loss';
                } else {
                    tablitaMatchScore.b++;
                    result = playerIsWhite ? 'loss' : 'win';
                }
                tablitaManager.recordResult(result);
                updateTablitaUI();

                // If game 1 just ended, advance to game 2
                if (tablitaManager.gameNumber === 1) {
                    tablitaManager.startGame2();
                    tablitaGameNum = 2;
                    updateTablitaUI();
                    // Update modal description to indicate game 2 is next
                    const matchResult = tablitaManager.getMatchResult();
                    document.getElementById('modal-desc').innerText =
                        desc + `\n\nPlacar: ${matchResult.playerWins}-${matchResult.opponentWins}` +
                        `\nPressione ▶ para iniciar o Jogo 2 (cores trocadas)`;
                } else {
                    // Match complete
                    const matchResult = tablitaManager.getMatchResult();
                    const matchDesc = matchResult.matchResult === 'win' ? 'Vitória no Micromatch!' :
                                      matchResult.matchResult === 'loss' ? 'Derrota no Micromatch.' :
                                      'Empate no Micromatch.';
                    document.getElementById('modal-desc').innerText =
                        desc + `\n\n${matchDesc} (${matchResult.playerWins}-${matchResult.opponentWins})` +
                        `\nTablita: ${tablitaManager.getTablitaName()}`;
                    // Clean up match state after showing result
                    tablitaManager.reset();
                    tablitaManager = null;
                    tablitaGameNum = 1;
                    tablitaMatchScore = { w: 0, b: 0 };
                    updateTablitaUI();
                }
            }
        }
    }

    // ── Loop do jogo ──────────────────────────────────────────────────────────
    function loop() {
        if (!gameStarted||gameEnded||isComputing) return;
        let isCPU;
        if (cfgMode === MODE_TABLITA) {
            // Tablita: use tablitaSubMode + game number to determine CPU control
            // Game 2 swaps colors: HVM→CPU plays White, MVH→CPU plays Red
            const swapped = tablitaManager && tablitaManager.gameNumber === 2;
            isCPU = (tablitaSubMode === MODE_HVM && gameState.turn === (swapped ? 1 : -1)) ||
                    (tablitaSubMode === MODE_MVH && gameState.turn === (swapped ? -1 : 1)) ||
                     tablitaSubMode === MODE_MVM;
        } else {
            isCPU = (cfgMode===MODE_HVM && gameState.turn===-1) ||
                    (cfgMode===MODE_MVH && gameState.turn===1)  ||
                     cfgMode===MODE_MVM;
        }
        if (isCPU)           triggerCPU();
        else if (isAnalysisOn) runAna();
    }

    // [FIX-V31-TIME] Orçamento de tempo adaptativo por fase.
    // Abertura: mais rápido (média 1.2s). Meio-jogo: aloca mais (média 2.5s).
    // Final: máximo de precisão (média 3.5s). Complexidade ajusta por número de lances.
    function getTimeBudget() {
        if (timeLimit===0) return 0;
        const rem = gameState.turn===1 ? timeW : timeB;
        const legalMoves = gameState.getMoves().length;
        const totalPieces = gameState.wP + gameState.bP + gameState.wK + gameState.bK;
        // Phase factor: opening=0.7, middlegame=1.0, endgame=1.4
        const phaseFactor = totalPieces > 18 ? 0.7 : totalPieces > 8 ? 1.0 : 1.4;
        // Complexity based on legal moves (log scale, capped)
        const complexity = Math.min(1.0 + Math.log2(Math.max(legalMoves, 1)) * 0.15, 2.0);
        // Base: fraction of remaining time scaled by phase
        const base = Math.max(1200, rem * 1000 / 24 * phaseFactor);
        // Cap at 30% of remaining time, max 20s for critical endgames
        return Math.min(base * complexity, rem * 1000 * 0.3, 20000);
    }

    function triggerCPU() {
        if (isComputing||gameEnded) return;
        isComputing=true;
        txtStatus.innerText="Calculando..."; barStatus.classList.add('computing');
        clockLastStamp = Date.now();
        const t0=Date.now();
        setTimeout(()=>{
            // [ENG-V24-SYNC] Sinergia de Transição Livro→Motor (Overclock):
            // O momento em que a engine sai do livro é o mais crítico — ela precisa de
            // máxima potência para ancorar as posições teóricas. Nos primeiros 2 lances
            // fora da teoria, cfgDepth+1 garante cálculo de elite sem "apagão" tático.
            // getBestMove retorna isBook:true para lances do livro (short-circuit);
            // usamos bookProbe aqui apenas para detectar se ainda estamos na teoria.
            const isInBook = bookProbe(gameState) !== null;
            const effectiveDepth = (!isInBook && nonBookPlyCount < 2) ? cfgDepth + 1 : cfgDepth;
            const res=getBestMove(gameState, effectiveDepth, getTimeBudget());
            // Atualiza contador de transição pós-livro
            if (res.isBook) { nonBookPlyCount = 0; }
            else            { nonBookPlyCount++; }
            const elapsed=((Date.now()-t0)/1000).toFixed(1);
            isComputing=false;
            const sc=res.score;
            const scStr = sc>9000?'Mate': sc<-9000?'-Mate': (sc>=0?'+':'')+(sc/100).toFixed(2);
            const pvStr = res.pv&&res.pv.length>0 ? res.pv.slice(0,3).map(move2Str).join(' ') : '-';
            const bookTag  = res.isBook ? ' <span style="color:#ffa726;">[📖 Livro]</span>' : '';
            const ocTag    = (!res.isBook && nonBookPlyCount <= 2) ? ' <span style="color:#b388ff;">[⚡OC]</span>' : '';
            txtAnalysis.innerHTML=`P:<strong>${res.depth}</strong> Eval:<strong style="color:${sc>=0?'#66bb6a':'#ef5350'}">${scStr}</strong> N:<strong>${res.nodes}</strong> T:<strong>${elapsed}s</strong> PV:<strong style="color:#90caf9">${pvStr}</strong>${bookTag}${ocTag}`;
            // Debita o tempo de pensar ainda não cobrado pelo clockInterval
            if (timeLimit > 0) {
                const now = Date.now();
                const uncharged = (now - clockLastStamp) / 1000;
                if (gameState.turn === 1) { timeW = Math.max(0, timeW - uncharged); }
                else                      { timeB = Math.max(0, timeB - uncharged); }
                clockLastStamp = now;
                if (timeW <= 0) { timeW=0; updateClocks(); popModal("Fim de Jogo","Tempo esgotado! Vermelhas vencem."); return; }
                if (timeB <= 0) { timeB=0; updateClocks(); popModal("Fim de Jogo","Tempo esgotado! Brancas vencem."); return; }
                updateClocks();
            }
            if (res.move) exec(res.move); else render();
        }, 10);
    }

    function runAna() {
        const t0=Date.now();
        txtAnalysis.innerHTML=`<span style="color:#29b6f6;">Avaliando profundidade ${cfgDepth}...</span>`;
        setTimeout(()=>{
            const res=getBestMove(gameState, cfgDepth, 0);
            const elapsed=((Date.now()-t0)/1000).toFixed(1);
            const sc=res.score;
            let scStr, scColor;
            if      (sc>9000)  { scStr='Mate';  scColor='#ffa726'; }
            else if (sc<-9000) { scStr='-Mate'; scColor='#ffa726'; }
            else { scStr=(sc>=0?'+':'')+(sc/100).toFixed(2); scColor=sc>=0?'#66bb6a':'#ef5350'; }
            const pvStr=res.pv&&res.pv.length>0?res.pv.slice(0,5).map(move2Str).join(' '):'-';
            const bookTag=res.isBook?'<span style="color:#ffa726;"> [📖 Livro]</span>':'';
            txtAnalysis.innerHTML=`P:<strong>${res.depth}</strong> Eval:<strong style="color:${scColor}">${scStr}</strong> N:<strong>${res.nodes}</strong> T:<strong>${elapsed}s</strong> PV:<strong style="color:#90caf9">${pvStr}</strong>${bookTag}`;
            if (res.move) { selIdx=res.move.from; valTgt=[res.move]; render(); }
        }, 10);
    }

    // ── Ações do tabuleiro ────────────────────────────────────────────────────
    function enterEditMode() {
        if (isComputing) return;
        if (editMode) { editMode=false; document.getElementById('edit-controls').style.display='none'; resetBoard(); return; }
        editMode=true; editStartTurn=1;
        gameStarted=false; gameEnded=false; isComputing=false; gameResultType=null;
        stopClock();
        const ns=new State();
        for (let i=0;i<64;i++) ns.board[i]=EMPTY;
        ns.turn=1; ns._rehash(); ns.hashHist=[ns.hash];
        rootNode={ id:0, parent:null, moveStr:null, state:ns, children:[] };
        nextNodeId=1; allNodes={ 0:rootNode }; currentNode=rootNode;
        gameState=ns.clone();
        selIdx=-1; valTgt=[]; lastM=null;
        document.getElementById('edit-turn').value='1';
        document.getElementById('edit-controls').style.display='flex';
        document.getElementById('modal').style.display='none';
        render(); txtStatus.innerText='✏ Editando — coloque as peças e pressione ▶';
    }

    function resetBoard() {
        editMode=false; document.getElementById('edit-controls').style.display='none';
        gameStarted=false; gameEnded=false; isComputing=false; gameResultType=null;
        tablitaGameInProgress = false; // Reset Tablita game progress flag
        gameTrajectory = [];
        trajectoryPhase = 'opening';
        nonBookPlyCount = 0; // [ENG-V24-SYNC] Reset do contador de transição Livro→Motor
        stopClock();
        ttGen++;
        // Clean up Tablita match state on reset
        if (tablitaManager) { tablitaManager.reset(); tablitaManager = null; }
        tablitaGameNum = 1; tablitaMatchScore = { w: 0, b: 0 };
        updateTablitaUI();

        const ns=new State();
        timeLimit=parseInt(document.getElementById('cfg-time').value);
        ns.timeW=timeLimit; ns.timeB=timeLimit;
        timeW=timeLimit; timeB=timeLimit;

        rootNode={ id:0, parent:null, moveStr:null, state:ns, children:[] };
        nextNodeId=1; allNodes={ 0:rootNode }; currentNode=rootNode;
        gameState=ns.clone();

        selIdx=-1; valTgt=[]; lastM=null;
        document.getElementById('modal').style.display='none';
        document.getElementById('branch-modal').style.display='none';
        pendingBranchMove=null;
        render(); txtAnalysis.innerText='Modo Análise: Desativado';
    }

    function resumeGame() {
        if (editMode) {
            editMode = false;
            document.getElementById('edit-controls').style.display='none';
            gameStarted = true; gameEnded = false; isComputing = false;
            currentNode.state = gameState.clone();
            currentNode.state.turn = editStartTurn;
            currentNode.state.hashHist = [currentNode.state.hash];
            gameState = currentNode.state.clone();
            cfgView = editStartTurn === 1 ? 'W' : 'B';
            document.getElementById('cfg-view').value = cfgView;
            lastM = null; selIdx = -1; valTgt = [];
            if (timeLimit > 0) {
                timeW = timeLimit; timeB = timeLimit;
                clockLastStamp = Date.now(); startClock();
            }
            document.getElementById('modal').style.display='none';
            render(); loop(); return;
        }

        // ── Tablita mode: initialize match if not already in one ──────────
        // Only initialize if game hasn't started (prevent reset during ongoing game)
        if (cfgMode === MODE_TABLITA && !tablitaManager && !gameStarted) {
            tablitaManager = new TablitaManager();
            tablitaManager.selectTablita();
            tablitaGameNum = 1;
            tablitaMatchScore = { w: 0, b: 0 };
            tablitaSubMode = parseInt(document.getElementById('tablita-submode').value);
            updateTablitaUI();
        }

        // ── Tablita mode: rebuild position from tablita moves ─────────────
        // Only rebuild if game hasn't started OR game has ended (never during ongoing game)
        // Use tablitaGameInProgress to detect ongoing games even when gameStarted is false due to navigation
        if (cfgMode === MODE_TABLITA && tablitaManager && tablitaManager.currentTablita && !tablitaGameInProgress) {
            const notation = tablitaManager.getTablitaNotation();
            const ns = new State();
            timeLimit = parseInt(document.getElementById('cfg-time').value);
            ns.timeW = timeLimit; ns.timeB = timeLimit;
            timeW = timeLimit; timeB = timeLimit;

            // Build rootNode chain by replaying tablita moves
            rootNode = { id: 0, parent: null, moveStr: null, state: ns, children: [] };
            nextNodeId = 1; allNodes = { 0: rootNode };
            let curr = rootNode;

            for (const moveStr of notation) {
                const parts = moveStr.split(/[-x]/);
                const from = algToIdx(parts[0]);
                const to = algToIdx(parts[parts.length - 1]);
                const moves = curr.state.getMoves();
                const found = moves.find(m => m.from === from && m.to === to);
                if (!found) { console.warn(`Tablita move ${moveStr} not legal`); break; }
                const ns2 = curr.state.clone();
                ns2.applyMove(found); ns2.timeW = timeLimit; ns2.timeB = timeLimit;
                const nd = { id: nextNodeId++, parent: curr, moveStr: move2Str(found),
                             state: ns2, children: [], move: cloneMv(found) };
                curr.children.push(nd); allNodes[nd.id] = nd; curr = nd;
            }

            currentNode = curr;
            gameState = currentNode.state.clone();
            lastM = currentNode.move || null;
            selIdx = -1; valTgt = [];
            nonBookPlyCount = 0;

            // Set view: human sees from their color's perspective, accounting for game 2 swap
            // Game 1: HVM→human=White→'W', MVH→human=Red→'B'
            // Game 2: colors swapped, HVM→human=Red→'B', MVH→human=White→'W'
            const humanIsWhite = (tablitaManager.gameNumber === 1)
                ? (tablitaSubMode !== MODE_MVH)
                : (tablitaSubMode === MODE_MVH);
            cfgView = humanIsWhite ? 'W' : 'B';
            document.getElementById('cfg-view').value = cfgView;
            updateCoords();

            gameStarted = true; gameEnded = false; isComputing = false;
            tablitaGameInProgress = true; // Mark Tablita game as in progress
            if (timeLimit > 0) {
                clockLastStamp = Date.now(); startClock();
            }
            document.getElementById('modal').style.display = 'none';
            render(); loop();
            return;
        }

        gameStarted = true; gameEnded = false; isComputing = false;
        gameState = currentNode.state.clone();
        lastM     = currentNode.move || null;
        selIdx    = -1; valTgt = [];
        if (timeLimit > 0) {
            if (currentNode.state.timeW !== undefined) {
                timeW = currentNode.state.timeW; timeB = currentNode.state.timeB;
            }
            clockLastStamp = Date.now(); startClock();
        }
        document.getElementById('modal').style.display = 'none';
        render(); loop();
    }

    function onSquareClick(idx) {
        if (editMode) {
            const p=gameState.board[idx];
            const isDark=((idx>>3)+(idx&7))%2===0;
            if (!isDark) return;
            const r = idx >> 3;
            if (p===EMPTY)       gameState.board[idx]=W_MAN;
            else if (p===W_MAN)  gameState.board[idx]=W_KING;
            else if (p===W_KING) gameState.board[idx]=V_MAN;
            else if (p===V_MAN)  gameState.board[idx]=V_KING;
            else if (p===V_KING) gameState.board[idx]=EMPTY;
            if (gameState.board[idx] === W_MAN && r === 7) gameState.board[idx] = W_KING;
            if (gameState.board[idx] === V_MAN && r === 0) gameState.board[idx] = V_KING;
            gameState._rehash(); gameState.hashHist=[gameState.hash];
            render(); return;
        }
        if (!gameStarted||isComputing||gameEnded) return;
        let isCPU;
        if (cfgMode === MODE_TABLITA) {
            const swapped = tablitaManager && tablitaManager.gameNumber === 2;
            isCPU = (tablitaSubMode === MODE_HVM && gameState.turn === (swapped ? 1 : -1)) ||
                    (tablitaSubMode === MODE_MVH && gameState.turn === (swapped ? -1 : 1)) ||
                     tablitaSubMode === MODE_MVM;
        } else {
            isCPU = (cfgMode===MODE_HVM&&gameState.turn===-1)||(cfgMode===MODE_MVH&&gameState.turn===1)||cfgMode===MODE_MVM;
        }
        // [ENG-V32-FLEX] Allow user to create variations freely even during CPU's turn, overriding it
        // if (isCPU&&cfgMode!==MODE_SAND&&!isAnalysisOn) return;
        const m=valTgt.find(m=>m.to===idx);
        if (m) { exec(m); return; }
        if (gameState.board[idx]!==EMPTY&&Math.sign(gameState.board[idx])===gameState.turn) {
            selIdx=idx; valTgt=gameState.getMoves().filter(m=>m.from===idx);
        } else { selIdx=-1; valTgt=[]; }
        render();
    }

    function exec(m) {
        const mStr=move2Str(m);
        const existing=currentNode.children.find(c=>c.moveStr===mStr);
        if (existing) {
            currentNode=existing; gameState=currentNode.state.clone();
            if (currentNode.state.timeW!==undefined) { timeW=currentNode.state.timeW; timeB=currentNode.state.timeB; }
            selIdx=-1; valTgt=[]; lastM=m;
            if (gameStarted&&timeLimit>0) clockLastStamp=Date.now();
            render(); if (!gameEnded&&gameStarted) setTimeout(loop,50);
        } else if (currentNode.children.length>0) {
            pendingBranchMove=m; document.getElementById('branch-modal').style.display='flex';
        } else { addNodeAndApply(m); }
    }

    function addNodeAndApply(m) {
        const newState=currentNode.state.clone();
        newState.applyMove(m); newState.timeW=timeW; newState.timeB=timeB;
        const n={ id:nextNodeId++, parent:currentNode, moveStr:move2Str(m), state:newState, children:[], move: cloneMv(m) };
        currentNode.children.push(n); allNodes[n.id]=n; currentNode=n;
        gameState=currentNode.state.clone();

        // [ENG-V18-3] Registra estado estratégico da partida após cada lance.
        // Calcula material, mobilidade e fase para alimentar o rastreador de trajetória.
        {
            let wP=0,bP=0,wK=0,bK=0,wMob=0,bMob=0;
            for (let i=0;i<64;i++) {
                const p=newState.board[i]; if(p===EMPTY) continue;
                if(p===W_MAN) wP++; else if(p===V_MAN) bP++;
                else if(p===W_KING) wK++; else bK++;
            }
            const totalPieces=wP+bP+wK+bK;
            const material=(wP-bP)*100+(wK-bK)*285;
            // Detecta e atualiza fase automaticamente
            if (trajectoryPhase==='opening' && totalPieces<=18) trajectoryPhase='middlegame';
            if (trajectoryPhase==='middlegame' && totalPieces<=8) trajectoryPhase='endgame';
            const snap={ plyIndex:n.id, material, totalPieces, phase:trajectoryPhase, mobBalance:0 };
            gameTrajectory.push(snap);
            if (gameTrajectory.length>TRAJ_MAX) gameTrajectory.shift();
        }

        selIdx=-1; valTgt=[]; lastM=m;
        if (gameStarted&&timeLimit>0) clockLastStamp=Date.now();
        if (gameStarted&&!gameEnded&&timeLimit>0&&!clockInterval) startClock();
        render(); if (!gameEnded&&gameStarted) setTimeout(loop,50);
    }

    window.branchReplace = function() {
        document.getElementById('branch-modal').style.display='none';
        currentNode.children=[]; addNodeAndApply(pendingBranchMove);
    };
    window.branchAdd = function() {
        document.getElementById('branch-modal').style.display='none';
        addNodeAndApply(pendingBranchMove);
    };
    window.branchCancel = function() {
        document.getElementById('branch-modal').style.display='none';
        pendingBranchMove=null; selIdx=-1; valTgt=[]; render();
    };

    window.navToId = function(id) {
        if (isComputing) return;
        const n=allNodes[id]; if (!n) return;
        if (editMode) { editMode=false; document.getElementById('edit-controls').style.display='none'; }
        document.getElementById('branch-modal').style.display='none';
        pendingBranchMove=null;
        stopClock();
        gameStarted=false; gameEnded=false;
        currentNode=n; gameState=n.state.clone();
        lastM=n.move||null; selIdx=-1; valTgt=[];
        nonBookPlyCount = 0;
        render();
        txtStatus.innerText="⏸ Pausado — pressione ▶ para continuar";
        txtAnalysis.innerText='';
    };

    window.addEventListener('keydown', e=>{
        if (e.target.tagName==='TEXTAREA'||e.target.tagName==='INPUT') return;
        if (e.key==='ArrowLeft')  { e.preventDefault(); if(currentNode.parent) navToId(currentNode.parent.id); }
        if (e.key==='ArrowRight') { e.preventDefault(); if(currentNode.children.length>0) navToId(currentNode.children[0].id); }
        if (e.key==='ArrowUp')    { e.preventDefault(); navToId(0); }
        if (e.key==='ArrowDown')  { e.preventDefault(); let c=currentNode; while(c.children.length>0) c=c.children[0]; navToId(c.id); }
    });

    document.getElementById('cfg-mode').onchange=e=>{
        cfgMode=parseInt(e.target.value);
        cfgView=(cfgMode===MODE_MVH)?'B':'W'; document.getElementById('cfg-view').value=cfgView;
        // [V21-STATS] Show CPU stats row only in CPU×CPU mode
        const statsRow = document.getElementById('cpu-stats-row');
        if (statsRow) statsRow.style.display = cfgMode===MODE_MVM ? 'flex' : 'none';
        // Tablita mode controls
        const tablitaCtrl = document.getElementById('tablita-controls');
        const tablitaSeq = document.getElementById('tablita-sequence');
        const tablitaSub = document.getElementById('tablita-submode-row');
        if (tablitaCtrl) tablitaCtrl.style.display = cfgMode===MODE_TABLITA ? 'flex' : 'none';
        if (tablitaSeq) tablitaSeq.style.display = cfgMode===MODE_TABLITA ? 'flex' : 'none';
        if (tablitaSub) tablitaSub.style.display = cfgMode===MODE_TABLITA ? 'flex' : 'none';
        // Reset stale Tablita state when switching away
        if (cfgMode !== MODE_TABLITA && tablitaManager) {
            tablitaManager.reset(); tablitaManager = null;
            tablitaGameNum = 1; tablitaMatchScore = { w: 0, b: 0 };
            updateTablitaUI();
        }
        // Auto-select random tablita and reconstruct board on mode selection
        if (cfgMode === MODE_TABLITA) {
            autoSelectTablita();
        }
        render();
    };

    // Tablita sub-mode selector
    document.getElementById('tablita-submode').onchange=e=>{
        tablitaSubMode=parseInt(e.target.value);
    };
    document.getElementById('cfg-view').onchange    =e=>{ cfgView=e.target.value; render(); };
    document.getElementById('cfg-depth').onchange   =e=>{ cfgDepth=parseInt(e.target.value); if(isAnalysisOn&&gameStarted) runAna(); };
    document.getElementById('cfg-time').onchange    =e=>{
        if (!gameStarted) {
            timeLimit=parseInt(e.target.value); timeW=timeB=timeLimit;
            for (const id in allNodes) { allNodes[id].state.timeW=timeLimit; allNodes[id].state.timeB=timeLimit; }
            render();
        }
    };
    document.getElementById('cfg-analysis').onchange=e=>{
        isAnalysisOn=e.target.checked; selIdx=-1; valTgt=[]; render();
        // Run analysis immediately when toggled on, but never trigger CPU execution.
        let isCPU;
        if (cfgMode === MODE_TABLITA) {
            const swapped = tablitaManager && tablitaManager.gameNumber === 2;
            isCPU = (tablitaSubMode === MODE_HVM && gameState.turn === (swapped ? 1 : -1)) ||
                    (tablitaSubMode === MODE_MVH && gameState.turn === (swapped ? -1 : 1)) ||
                     tablitaSubMode === MODE_MVM;
        } else {
            isCPU = (cfgMode===MODE_HVM&&gameState.turn===-1)||(cfgMode===MODE_MVH&&gameState.turn===1)||cfgMode===MODE_MVM;
        }
        if(gameStarted && !gameEnded && isAnalysisOn && !isCPU) runAna();
    };

    document.getElementById('btn-resume').onclick =resumeGame;
    document.getElementById('btn-reset').onclick  =resetBoard;
    document.getElementById('btn-force').onclick  =()=>{ if(gameStarted&&!gameEnded) triggerCPU(); };
    document.getElementById('btn-edit').onclick   =enterEditMode;

    // Desistir (resign) button
    document.getElementById('btn-resign').onclick=()=>{
        if (!gameStarted || gameEnded || isComputing) return;
        const winner = gameState.turn === 1 ? 'Vermelhas' : 'Brancas';
        popModal("Fim de Jogo", `${winner} vencem! (Desistência)`);
    };

    // Tablita mode UI update
    function updateTablitaUI() {
        const gameNumEl = document.getElementById('tablita-game-num');
        const scoreEl = document.getElementById('tablita-match-score');
        const seqEl = document.getElementById('tablita-sequence');
        if (gameNumEl) gameNumEl.textContent = `${tablitaGameNum}/${TABLITA_MAX_GAMES}`;
        if (scoreEl) scoreEl.textContent = `${tablitaMatchScore.w}-${tablitaMatchScore.b}`;
        if (seqEl && tablitaManager) {
            const results = tablitaManager.matchResults;
            if (results.length > 0) {
                const seq = results.map(r =>
                    r.result === 'win' ? '1-0' : r.result === 'loss' ? '0-1' : '½-½'
                );
                seqEl.textContent = 'Seq: ' + seq.join(' ');
            } else {
                seqEl.textContent = '';
            }
        } else if (seqEl) {
            seqEl.textContent = '';
        }
    }
    document.getElementById('edit-turn').onchange =e=>{ editStartTurn=parseInt(e.target.value); };
    document.addEventListener('contextmenu', e=>{ if(editMode) e.preventDefault(); });

    document.getElementById('btn-suggest').onclick=()=>{
        if (gameEnded||isComputing) return;
        // [ENG-V18-1] Sugestão também usa busca real; resultado indica se livro foi confirmado.
        txtAnalysis.innerHTML=`<span style="color:#66bb6a;">Sugerindo profundidade ${cfgDepth}...</span>`;
        const t0=Date.now();
        setTimeout(()=>{
            const res=getBestMove(gameState, cfgDepth, 0);
            const elapsed=((Date.now()-t0)/1000).toFixed(1);
            const sc=res.score;
            const scStr=sc>9000?'Mate':sc<-9000?'-Mate':(sc>=0?'+':'')+(sc/100).toFixed(2);
            const bookTag=res.isBook?'<span style="color:#ffa726;"> [📖 Livro]</span>':'';
            txtAnalysis.innerHTML=`Sugestão: <strong style="color:#66bb6a">${res.move?move2Str(res.move):'-'}</strong> | Eval:<strong style="color:${sc>=0?'#66bb6a':'#ef5350'}">${scStr}</strong> P:<strong>${res.depth}</strong> T:<strong>${elapsed}s</strong>${bookTag}`;
            if (res.move) { selIdx=res.move.from; valTgt=[res.move]; render(); }
        }, 10);
    };

    document.getElementById('btn-nav-start').onclick=()=>navToId(0);
    document.getElementById('btn-nav-prev').onclick =()=>{ if(currentNode.parent) navToId(currentNode.parent.id); };
    document.getElementById('btn-nav-next').onclick =()=>{ if(currentNode.children.length>0) navToId(currentNode.children[0].id); };
    document.getElementById('btn-nav-end').onclick  =()=>{ let c=currentNode; while(c.children.length>0) c=c.children[0]; navToId(c.id); };

    // ── PDN: Formatação de Lance ──────────────────────────────────────────────
    function move2PDN(m) {
        return move2Str(m);
    }

    // ── PDN: Geração do Texto ─────────────────────────────────────────────────
    function generatePDN(node, plyCount) {
        let out = '', curr = node, ply = plyCount, prevHadVars = false;
        while (curr.children.length > 0) {
            const main = curr.children[0], isWhite = (ply % 2 === 0), hasVars = curr.children.length > 1;
            const moveNum = Math.floor(ply / 2) + 1;
            if (isWhite) out += `${moveNum}. `;
            else if (curr === node || prevHadVars) out += `${moveNum}... `;
            out += main.moveStr + ' ';
            for (let i = 1; i < curr.children.length; i++) {
                const v = curr.children[i];
                out += `( ${moveNum}${isWhite ? '.' : '...'} ${v.moveStr} ${generatePDN(v, ply + 1)}) `;
            }
            prevHadVars = hasVars; curr = main; ply++;
        }
        return out;
    }

    // ── PDN: Exportação ───────────────────────────────────────────────────────
    document.getElementById('btn-export').onclick = async () => {
        let result = '*';
        if (gameEnded) {
            if (gameResultType === 'draw') result = '1/2-1/2';
            else if (gameResultType === 'white') result = '2-0';
            else result = '0-2';
        }
        const now = new Date();
        const dateStr = `${now.getFullYear()}.${String(now.getMonth()+1).padStart(2,'0')}.${String(now.getDate()).padStart(2,'0')}`;
        let txt = '';
        txt += `[Event "DraughtsMind Pro Match"]\n`;
        txt += `[Site "DraughtsMind Pro v${ENGINE_VERSION}"]\n`;
        txt += `[Date "${dateStr}"]\n`;
        txt += `[Round "1"]\n`;
        txt += `[White "Human"]\n`;
        txt += `[Black "Engine (ply ${cfgDepth})"]\n`;
        txt += `[Result "${result}"]\n`;
        txt += `[GameType "26"]\n`;
        
        // Write Setup/FEN if custom position
        const defaultState = new State();
        if (rootNode.state.toFEN() !== defaultState.toFEN()) {
            txt += `[SetUp "1"]\n`;
            txt += `[FEN "${rootNode.state.toFEN()}"]\n`;
        }
        
        txt += `\n`;
        txt += `{DraughtsMind Pro v${ENGINE_VERSION} | depth:${cfgDepth} | time:${timeLimit} | hash:${gameState.hash.toString(16).toUpperCase().slice(-8)}}\n\n`;
        txt += generatePDN(rootNode, 0).trim() + `\n${result}\n`;
        const name = `mind_game_${Date.now()}.pdn`;
        if (window.electronAPI?.saveFile) {
            try {
                const r = await window.electronAPI.saveFile({ content: txt, filename: name, filters: [{ name: 'PDN', extensions: ['pdn'] }] });
                if (r) {
                    if (r.success) txtAnalysis.innerHTML = `<span style="color:#66bb6a;">✓ Exportado: ${r.path}</span>`;
                    return;
                }
            } catch(e) { /* fallback below */ }
        } else if (window.showSaveFilePicker) {
            try {
                const h = await window.showSaveFilePicker({ suggestedName: name, types: [{ description: 'PDN', accept: { 'text/plain': ['.pdn'] } }] });
                const w = await h.createWritable(); await w.write(txt); await w.close();
                txtAnalysis.innerHTML = `<span style="color:#66bb6a;">✓ Exportado: ${name}</span>`; return;
            } catch(e) { if (e.name === 'AbortError') return; }
        }
        const blob = new Blob([txt], { type: 'text/plain' }), url = URL.createObjectURL(blob);
        const a = document.createElement('a'); a.href = url; a.download = name; a.style.display = 'none';
        document.body.appendChild(a); a.click(); document.body.removeChild(a);
        setTimeout(() => URL.revokeObjectURL(url), 5000);
        txtAnalysis.innerHTML = `<span style="color:#66bb6a;">✓ Download: ${name}</span>`;
    };

    // ── PDN: Importação ───────────────────────────────────────────────────────
    function algToIdx(sq) {
        if (!sq || sq.length < 2) return -1;
        const charCode = sq.toLowerCase().charCodeAt(0);
        const c = charCode - 97, r = parseInt(sq[1]) - 1;
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
        if (moves.length === 0) return null;

        // Clean token from any trailing annotations like !, ?, etc.
        const cleanTk = tk.replace(/[!?+#]+$/g, '');

        // 1. Try exact string match first
        let found = moves.find(m => move2Str(m).toLowerCase() === cleanTk.toLowerCase());
        if (found) return found;

        // Helper to check if a sequence of squares matches a move
        function matchesMove(m, tkSqs) {
            if (tkSqs.length < 2) return false;
            if (tkSqs[0] !== m.from) return false;
            
            if (m.captured.length > 0) {
                // The notation might specify landing squares OR captured pieces.
                // As long as the last square is either m.to OR the last captured piece,
                // and all intermediate squares are part of the capture path or captured pieces, we consider it a match.
                
                // Also, sometimes notations just use from-to even for captures (e.g. c3-e5 instead of c3xe5)
                if (tkSqs.length === 2 && tkSqs[1] === m.to) return true;
                
                // If it specifies the captured piece instead of landing square (e.g. c5-d4 instead of c5-e3)
                if (tkSqs.length === 2 && m.captured.length === 1 && tkSqs[1] === m.captured[0]) return true;

                // Validate sequence
                const validSqs = [...m.path, ...m.captured, m.to];
                for (let i = 1; i < tkSqs.length; i++) {
                    if (!validSqs.includes(tkSqs[i])) return false;
                }
                return true;
            } else {
                return tkSqs[tkSqs.length - 1] === m.to;
            }
        }

        // 2. Try parsing as algebraic coordinate notation (e.g. c3-d4, c3xe5, f6-d4-b2, c3:e5)
        if (/^[a-h][1-8]([-x:][a-h][1-8])+$/i.test(cleanTk)) {
            const parts = cleanTk.split(/[-x:]/i);
            const tkSqs = parts.map(algToIdx);
            if (tkSqs.every(idx => idx >= 0)) {
                const matches = moves.filter(m => matchesMove(m, tkSqs));
                if (matches.length > 0) {
                    const exactEnd = matches.find(m => tkSqs[tkSqs.length - 1] === m.to);
                    if (exactEnd) return exactEnd;
                    return matches[0];
                }
            }
        }

        // 3. Try parsing as standard numeric notation (e.g. 21-17, 21x17, 21:17)
        if (/^\d+([-x:]\d+)+$/i.test(cleanTk)) {
            const parts = cleanTk.split(/[-x:]/i).map(Number);
            for (const useAlt of [false, true]) {
                const conv = useAlt ? numToIdxAlt : numToIdx;
                const tkSqs = parts.map(conv);
                if (tkSqs.every(idx => idx >= 0)) {
                    const matches = moves.filter(m => matchesMove(m, tkSqs));
                    if (matches.length > 0) {
                        const exactEnd = matches.find(m => tkSqs[tkSqs.length - 1] === m.to);
                        if (exactEnd) return exactEnd;
                        return matches[0];
                    }
                }
            }
        }

        return null;
    }

    function looksLikeMove(tk) {
        const clean = tk.replace(/[!?+#]+$/g, '');
        return /^[a-h][1-8]([-x:][a-h][1-8])+$/i.test(clean) || /^\d+([-x:]\d+)+$/i.test(clean);
    }

    function parsePDNTokens(tokens, startState) {
        const ns = startState ? startState.clone() : new State();
        ns.timeW = timeLimit; ns.timeB = timeLimit;
        const rn = { id: 0, parent: null, moveStr: null, state: ns, children: [] };
        let nid = 1, curr = rn, skipped = [];
        const restoreStack = [];
        let varDepth = 0;
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
                if (!found) {
                    if (looksLikeMove(tk)) {
                        skipped.push(tk);
                    }
                    continue;
                }
                const mStr = move2Str(found);
                const ex = curr.children.find(c => c.moveStr === mStr);
                if (ex) { curr = ex; }
                else {
                    const ns2 = curr.state.clone();
                    ns2.applyMove(found); ns2.timeW = timeLimit; ns2.timeB = timeLimit;
                    const nd = { id: nid++, parent: curr, moveStr: mStr,
                                 state: ns2, children: [], move: cloneMv(found),
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
        return { rootNode: rn, skipped, nodeCount: nid - 1 };
    }

    function loadEBNF(str) {
        const headers = {};
        str.replace(/\[(\w+)\s+"([^"]*)"\]/g, (_, key, val) => { headers[key.toLowerCase()] = val; });

        str = str.replace(/^%[^\r\n]*/gm, ' ');
        str = str.replace(/\[[^\]]*\]/g, ' '); // remove tags globally
        str = str.replace(/;[^\r\n]*/g, ' '); // remove semicolon comments
        let prev;
        do { prev = str; str = str.replace(/\{[^{}]*\}/g, ' '); } while (str !== prev);
        str = str.replace(/\r?\n/g, ' ');
        str = str.replace(/\$\d{1,3}/g, ' ').replace(/[?!]+/g, ' ');
        str = str.replace(/\b(1\/2-1\/2|2-0|0-2|1-1|1-0|0-1)\b/g, ' ').replace(/\*/g, ' ');
        str = str.replace(/\d+\.+/g, ' ');
        str = str.replace(/\(/g, ' ( ').replace(/\)/g, ' ) ');

        const rawTokens = str.split(/\s+/).filter(t => t.length > 0);
        const tokens = [];
        for (const tk of rawTokens) {
            if (tk === '(' || tk === ')') {
                tokens.push(tk);
                continue;
            }
            if (/^\d+$/.test(tk)) continue; // ignore pure numbers
            if (/^\.+$/.test(tk)) continue; // ignore pure dots / ellipsis
            if (/^(1-0|0-1|2-0|0-2|1\/2-1\/2|1-1|\*)$/.test(tk)) continue; // ignore results
            tokens.push(tk);
        }

        allNodes = {};
        const startState = new State();
        if (headers.fen) {
            startState.loadFEN(headers.fen);
        }
        let r = parsePDNTokens(tokens, startState);

        rootNode = r.rootNode;
        nextNodeId = r.nodeCount + 1;
        allNodes = {};
        const collectNodes = (nd) => { allNodes[nd.id] = nd; nd.children.forEach(collectNodes); };
        collectNodes(rootNode);

        currentNode = rootNode; gameState = currentNode.state.clone();
        timeW = timeLimit; timeB = timeLimit;
        editMode = false;
        gameResultType = null;
        if (headers.result) {
            if (headers.result === '1/2-1/2') gameResultType = 'draw';
            else if (headers.result === '2-0') gameResultType = 'white';
            else if (headers.result === '0-2') gameResultType = 'red';
        }
        gameStarted = false; gameEnded = false; isComputing = false;
        selIdx = -1; valTgt = []; lastM = null;
        stopClock();
        document.getElementById('modal').style.display = 'none';
        document.getElementById('edit-controls').style.display = 'none';
        document.getElementById('branch-modal').style.display = 'none';
        render();

        const nodeCount = Object.keys(allNodes).length - 1;
        if (r.skipped.length > 0) {
            const uniq = [...new Set(r.skipped)];
            const safe = uniq.slice(0, 6)
                .map(t => t.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;'))
                .join(', ');
            txtAnalysis.innerHTML =
                `<span style="color:#ffa726;">Importado com ${r.skipped.length} token(s) desconhecido(s): ${safe}${uniq.length > 6 ? '…' : ''}</span>`;
        } else {
            txtAnalysis.innerHTML =
                `<span style="color:#66bb6a;">✓ Importação concluída. ${nodeCount} lance(s)/variação(ões) carregados.</span>`;
        }
    }


    document.getElementById('btn-import').onchange = e => {
        const f = e.target.files[0]; if (!f) return;
        const r = new FileReader(); r.onload = ev => loadEBNF(ev.target.result); r.readAsText(f);
    };
    document.getElementById('btn-apply-paste').onclick = () => loadEBNF(document.getElementById('paste-area').value);

    // ── Inicialização ─────────────────────────────────────────────────────────
    buildOpeningBook();
    initDOM();
    updateCoords();   // populate static coord overlays (outside .board, never rotate)
    resetBoard();
    // Set dynamic version badge
    const _vb = document.getElementById('version-badge');
    if (_vb) _vb.textContent = `Pro`;

