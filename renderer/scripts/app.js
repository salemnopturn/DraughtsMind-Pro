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
                         state: ns2, children: [], move: found };
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
        document.getElementById('modal').style.display = 'none';
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
                if (!this.isEndgame) { this.isEndgame = true; this.endgameClock = 0; this.endgameLimit = endgameLimit; }
                else { this.endgameClock++; this.endgameLimit = endgameLimit; }
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
    const BOOK_DATA=
        // ─ c3-d4 / d6-c5 (Clássica/Pioneiro — JN+VR) ──────────────────────
        "JNVR|JNVRFJaV|JNVRFJaVJMWT|JNVRFJaVJMWTMQTO|JNVRFJWT|JNVRFJWTJMZV|JNVRFJWTJMZVMQcZ|JNVRFJWTLOTP|JNVRFJWTLOTPJMbW|JNVRFJWTJMTP|JNVRFJWTJMTPMVZJ|JNVRFJWTLOZV|JNVRFJWTLOZVNSUQ|JNVRFJWTLOZVNScZ|JNVRFJWTLObW|JNVRFJWTLObWJMTP|JNVREJZV|JNVREJZVJMUQ|JNVREJZVJMUQNUQZ|JNVREJaV|JNVREJaVJMXT|JNVREJaVJMXTMQbX|JNVREJaVJMUQ|JNVREJaVJMUQNUQJ|JNVRFJaVJMUQ|JNVRFJaVJMUQNUQJ|JNVREJXT|JNVREJXTLPbX|JNVREJXTLPbXHLaV|JNVREJWT|JNVREJWTJMUQ|JNVREJWTJMUQMVZJ|JNVRLPZV|JNVRLPZVHLUQ|JNVRLPZVHLUQNUQZ|JNVREJaVJMXTMQTP|JNVREJaVLOWT|JNVREJaVLOWTJMUQ|JNVREJaVAEVS|JNVREJaVAEVSLPRM|JNVREJaVLPVS|JNVREJaVLPVSGLZV|JNVREJWTJMaW|JNVREJWTJMaWMVZJ|JNVREJWTLObW|JNVREJWTLObWBETP|JNVRFJZV|JNVRFJZVJMUQ|JNVRFJZVJMUQNUQZ|JNVREJaVLPea|JNVREJaVLPeaGLWT|JNVRLPWS|JNVREJZVLPRM|JNVRLPZVEJUQ|JNVREJ|JNVREJZVJMWS|JNVREJWTJMUQNUQJ|JNVRLPWT|JNVRLPWTPWbJ|JNVRLPWTPWbJFVaR|JNVREJaVJMXTLObX|JNVREJaVLOWTBEbW|JNVREJWTLObWJMUQ|JNVRLPZVGLUQ|JNVRLPZVGLUQNUQZ|JNVREJXTLPbXHLZV|JNVRLPXT|JNVRLPXTGLbX|JNVRLPXTGLbXEJaV|JNVREJRM|JNVRLOZV|JNVRLOZVNS|JNVRFJZVJMWT|JNVRFJZVJMWTMQcZ|JNVREJZVJMUQNUQJ|JNVREJZVLPUQ|JNVREJZVLPUQNUQZ|JNVRLPZVGLRM|JNVRLPZVGLRMIRVM|JNVREJZVLOWT|JNVREJZVLOWTNScZ|JNVREJZVLOWTNSUQ|JNVRLOZVEJWT|JNVRLOZVEJWTNSUQ|JNVREJZVLOUQ|JNVREJZVLOUQNUQZ|JNVRFJWTLOZVNSdZ|JNVREJaVBEWT|JNVREJaVBEWTJMTP|JNVREJXTLPZV|JNVREJXTLPZVJMUQ|JNVREJaVLOWTBEUQ|JNVREJaVLOWTBETP|JNVREJXTBETO|JNVREJXTBETOLSaV|JNVREJXTLPZVGLbX|JNVREJWTBEbW|JNVREJWTBEbWJMTP|JNVREJXTJMUQ|JNVREJXTJMUQNUQJ|JNVREJXTLOTP|JNVREJXTLOTPBEaV|JNVREJaVLPeaGLVS|JNVRFJWS|JNVRFJWSNWbS|JNVRFJWSNWbSJMSN|JNVRLPZVHLVS|JNVRLPZVHLVSDHSJ|JNVRLO|JNVREJWTLObWOSTP|JNVREJXTLPbXGLZV|JNVREJXTLOTPOTbX|JNVRFJWTJMUQ|JNVRFJWTJMUQMVZJ|JNVREJaVLPXT|JNVREJaVLPXTHLbX|JNVRFJWTJMaV|JNVRFJWTJMaVLOUQ|JNVREJXTLPaV|JNVREJXTLPaVHLbX|JNVREJaVLOWTJMbW|JNVREJaVLPVSHLZV|JNVRFJaVJMWTMQTP|JNVREJaVLOWTHLTP|JNVREJXTJMTP|JNVREJXTJMTPMVZJ|JNVREJXTLOTPOTZV|JNVREJWTJMZV|JNVREJWTJMZVLOTP|JNVRFJWTJMaVMQTO|JNVRLOWT|JNVRLOWTFJbW|JNVRLOWTFJbWJMTP|JNVRFJaVLPXT|JNVRFJaVLPXTGLbX|JNVREJWTJMTP|JNVREJWTJMTPMVZJ|JNVREJZVJMWT|JNVREJZVJMWTLObW|JNVREJZVJMWTMQcZ|JNVRFJZVBFWS|JNVRFJZVBFWSNWbS|JNVREJXTLOTPJMWS|JNVRFJWSNWbSJMRN|JNVREJWTLObWOSaV|JNVREJWTJMZVMQdZ|JNVRLOWTEJbW|JNVRLOWTEJbWHLTP|JNVRLOZVGLUQ|JNVRLOZVGLUQNUQZ|JNVRFJaVJMWS|JNVRFJaVJMWSNWbS|JNVREJWTJMaV|JNVREJWTJMaVMQea|JNVRFJaVJMWTEJbW|JNVRLOWTEJbWJMTP|JNVREJWTBEZV|JNVREJWTBEZVJMUQ|JNVRLPZVHLUQNUYR|JNVRLPZVHLWT|JNVRLPZVHLWTPWbJ|JNVREJWS|JNVREJWSNWaT|JNVREJWSNWaTJMda|JNVREJaVLPeaGLUQ|JNVRLPZVHLcZ|JNVRLPZVHLcZEJVS|JNVREJZVAEVS|JNVREJZVAEVSLPaV|JNVREJWSNWbS|JNVREJWSNWbSJMZV|"+
        // ─ c3-d4 / d6-e5 (Cruz — JN+VS) ────────────────────────────────────
        "JNVS|JNVSEJUQ|JNVSEJUQIMZU|JNVSEJUQIMZUMRcZ|JNVSEJUQIMZUMRdZ|JNVSEJUQIMZUMRXT|JNVSEJaV|JNVSEJaVKOUQ|JNVSEJaVKOUQGKZU|JNVSFJZV|JNVSFJZVKOUQ|JNVSFJZVKOUQGKYU|JNVSLOSJ|JNVSLOSJENUQ|JNVSLOSJENUQHLWT|JNVSEJaVLO|JNVSFJaV|JNVSFJaVIMWT|JNVSEJUQLO|JNVSEJ|JNVSFJZVLPUR|JNVSLOSJENUQAEWS|JNVSLOSJFMWT|JNVSLOSJFMWTMQbW|JNVSKO|JNVSLP|JNVSLOSL|JNVSEJaVKOUR|JNVSLO|JNVSEJZV|JNVSIM|JNVSEJUQIMZUMR|JNVSEJUQIMZUAE|JNVSEJUQAEZV|JNVSEJUQAEZVIMYU|JNVSEJUQAEZVIMdZ|JNVSEJaVKOURNUYR|JNVSEJaVKOURNUZQ|JNVSEJaVLPUQ|JNVSEJaVLPUQGLZU|JNVSEJaVAEVR|JNVSEJaVAEVRLPRM|JNVSEJaVKOea|JNVSEJaVKOeaFKUR|JNVSEJaVKOda|JNVSEJaVKOdaOTXO|JNVSEJZVKOUQ|JNVSEJZVKOUQGKYU|JNVSEJZVKOUR|JNVSEJZVKOURNUYR|JNVSFJaVKOUQ|JNVSFJaVKOUQGKZU|JNVSFJaVKOUR|JNVSFJaVKOURNUYR|JNVSFJZVKOUR|JNVSFJZVKOURNUYR|JNVSFJaVLPXT|JNVSFJaVLPXTCFUQ|JNVSEJUR|JNVSEJURNUYR|JNVSEJURNUYRKORN|JNVSEJaVKOUQFKZU|JNVSEJUQKOYU|JNVSEJUQKOYUOVaK|JNVSEJaVLPVR|JNVSEJaVLPVRGLZV|JNVSEJaVKOeaGKUR|JNVSLOSJENaV|JNVSLOSJENaVOSVO|JNVSLOSJENWS|JNVSLOSJENWSOVZJ|JNVSFJ|JNVSEJSO|JNVSEJSOKTWP|JNVSEJSOKTWPLObW|JNVSEJZVKOUQNRVM|JNVSEJSOLSUR|JNVSEJSOLSURNUWE|JNVSLOSLHOUR|JNVSLOSLHOURNUYR|JNVSLOSLHOWT|JNVSLOSLHOWTIMaV|JNVSLOSJENUQHLZU|JNVSLOSLHOUQ|JNVSLOSLHOUQNRWT|JNVSLOSJENUQFJWT|JNVSLOSJFMWTMRUN|JNVSNR|JNVSEJWT|JNVSLPSJ|JNVSLPSJFMWS|JNVSLPSJFMWSGLaV|JNVSLPSJFMWSHLUQ|JNVSLPSJFMWSHLaV|JNVSLPSJFMWT|JNVSLPSJFMWTPWbS|JNVSEJUQLPZU|JNVSEJUQLPZUGLaV|JNVSEJUQIMZUAEcZ|JNVSLOSJENWT|JNVSLOSJENWTHLUQ|JNVSEJURNUYRJNSJ|JNVSFJUR|JNVSFJURNUZQ|JNVSFJURNUZQBFYU|JNVSLOSJENWTAEUQ|"+
        // ─ c3-d4 / b6-c5 (Pioneiro — JN+UR) ────────────────────────────────
        "JNUR|JNURNUYR|JNURNUYREJWT|JNURNUYREJWTJNRM|JNURNUYREJWS|JNURNUYREJWSKObW|JNURNUYREJWTJMTO|JNURNUYREJWTJMTP|JNURNUYREJWTLObW|JNURNUZQ|JNURNUZQEJWS|JNURNUZQEJWSKObW|JNURNUZQEJWSKOYU|JNURNUZQLPWS|JNURNUZQLPWSPTXO|JNURNUZQLOWS|JNURNUZQLOWSGLYU|JNURNUYREJWTLPTO|JNURNUYREJWTLOTP|JNURNUYREJWSKObW|JNURNUYRFJ|JNURNUYRKNRK|JNURNUYRKNRKGNVS|JNURNUYREJRM|JNURNUYREJRMIRVM|JNURNUYREJWSLOSL|JNURNUZQKNVR|JNURNUZQKNVRNUQZ|JNURNUYREJWTAETP|JNURNUYREKWT|JNURNUYREKWTLObW|JNURNUYREKWS|JNURNUYREKWSIMbW|JNURNUZQEKWT|JNURNUZQEKWTLOcZ|JNURNUZQEKWS|JNURNUZQEKWSIMbW|"+
        // ─ c3-d4 / f6-g5 (Flank — JN+WT) ───────────────────────────────────
        "JNWT|JNWTNRVM|JNWTNRVMIRUN|JNWTNRVMIRUNKRTO|JNWTNRUN|JNWTNRUNKRVM|JNWTNRUNKRVMIRTO|JNWTEJVR|JNWTEJVRJMbW|JNWTEJVRJMbWMVZJ|JNWTEJbW|JNWTEJbWJMTP|JNWTEJbWJMTPMRVM|JNWTFJTP|JNWTFJTPJMbW|JNWTFJTPJMbWMRVM|JNWTEJVRJMUQ|JNWTEJVRJMUQNUQJ|JNWTEJTP|JNWTEJTPJMXT|JNWTEJTPJMXTMQTO|JNWTEJTO|JNWTEJTOLSVO|JNWTEJTOLSVOKTXO|JNWTNRUNKRVMIRTP|JNWTLPUQ|JNWTLPUQPWbJ|JNWTLPUQPWbJFMQJ|JNWTEJTPJMXTNRUN|JNWTEJTPJMbW|JNWTEJTPJMbWNRUN|JNWTEJbWJMUR|JNWTEJbWJMURNUZJ|JNWTEJVRLObW|JNWTEJVRLObWBEaV|JNWTEJTPJMUQ|JNWTEJTPJMUQNRQJ|JNWTEJbWJMfb|JNWTEJbWJMfbMRVM|JNWTEJTPJMVR|JNWTEJTPJMVRMVZJ|JNWTEJTPJMVS|JNWTEJTPJMVSNWbS|JNWTNRVMIRUNKRZU|JNWTEJVRBEbW|JNWTEJVRBEbWJMTP|JNWTEJbWJMTPNRUN|JNWTNRUNKRVMIRbW|JNWTEJTPJMbWMQUR|JNWTEJbWJMUQ|JNWTEJbWJMUQMRVM|JNWTEJbWJMUQNRQJ|JNWTEJTPJMbWMRVM|JNWTEJTPJMXTMRVM|JNWTNR|JNWTLPUR|JNWTLP|JNWTLObW|JNWTLObWEJTP|JNWTLObWEJTPOS|JNWTLPVR|JNWTIMTO|JNWTEJTPJMbWMQWT|JNWTLOVR|JNWTLOVREJbW|JNWTLOVREJbWJMUQ|JNWTEJTPLOUR|JNWTEJTPLOURNUYR|JNWTLOUQ|JNWTLOUQNRVM|JNWTLOUQNRVMIRbW|JNWTLOVREJaV|JNWTLOVREJaVBEbW|JNWTEJTPLOVR|JNWTEJTPLOVRBEbW|JNWTEJVRJMaW|JNWTEJVRJMaWMVZJ|JNWTLOVRFJbW|JNWTLOVRFJbWJMTP|JNWTEJVRLOZV|JNWTEJVRLOZVNSUQ|JNWTEJTPLOUQ|JNWTEJTPLOUQNRVM|JNWTNRUNKRVMIRaW|JNWTEJbWJMVS|JNWTEJbWJMVSMQSJ|JNWTEJbWJMTPMQUR|JNWTEJbWJMfbMQTO|JNWTLPUQPWbJENXT|JNWTEJTPLObW|JNWTEJTPLObWOTXO|JNWTEJaW|JNWTNS|JNWTEJTPJMbWMR|JNWTEJbWJMTPMR|JNWTEJbWLOfb|JNWTEJUQ|JNWTKO|JNWTFJ|JNWTEJ|JNWTLO|JNWTLObWHLTP|JNWTLObWHLTPNRUN|JNWTLObWHLUQ|JNWTLObWHLUQNSWN|JNWTEJTPNS|JNWTLObWHLUQNRVM|JNWTFJVR|JNWTFJVRJMZV|JNWTFJVRJMZVMQcZ|JNWTEJUR|JNWTEJURNUZQ|JNWTEJURNUZQAEYU|JNWTEJaWLPea|JNWTEJaWLPeaAEVR|JNWTFJTPJMXT|JNWTFJTPJMXTMRVM|JNWTEJVRJMUQMVZJ|JNWTLOVRFJbWJMfb|JNWTLObWNRUN|JNWTLObWNRUNKRVM|JNWTEJbWJMeb|JNWTEJbWJMebMRVM|JNWTEJUQAETP|JNWTEJUQAETPLObW|JNWTEJaWBETP|JNWTEJaWBETPNRVM|JNWTEJTPBEbW|JNWTEJTPBEbWJMUQ|JNWTNRVMIRUNKRTP|JNWTEJbWAEUQ|JNWTEJbWAEUQNSVO|JNWTEJTPJMbWBEUQ|JNWTEJbWAEVR|JNWTEJbWAEVRLPaV|JNWTLObWNRVM|JNWTLPbW|JNWTLPbWNRVM|JNWTLPbWGLVS|JNWTNSVO|JNWTNSVOLSaV|JNWTNSVOLSaVKOTK|JNWTNRVMIRUNKRaW|JNWTEJUQNRVM|JNWTEJUQNRVMIRZV|JNWTFJTPBFbW|JNWTFJTPBFbWJMWT|JNWTLOVREJTP|JNWTLOVREJTPJMUQ|JNWTFJVRJMaV|JNWTFJVRJMaVMQTP|JNWTEJaWLOda|JNWTEJaWLOdaGLTP|JNWTEJTOKTXO|JNWTEJTOKTXOLSVO|JNWTFJbW|JNWTFJbWBFTP|JNWTFJbWBFTPNRUN|JNWTEJbWLOfbAEVR|JNWTEJTPLOVRJMUQ|JNWTEJUQNRVMIRTP|JNWTEJbWJMVSFJTP|JNWTFJUQ|JNWTFJUQBFTP|JNWTFJUQBFTPLObW|JNWTEJaWAEea|JNWTEJaWAEeaLPVR|JNWTLOVREJZV|JNWTLOVREJZVAEUQ|JNWTEJbWAETP|JNWTEJbWAETPLOVS|JNWTLPaW|JNWTLPaWNRVM|JNWTLOVS|JNWTEJbWJMTPMQWT|JNWTEJTPJMbWMQWS|JNWTEJbWJMebMQTO|JNWTFJaW|JNWTFJaWJMVS|JNWTFJaWJMVSMQSJ|JNWTFJaWLPea|JNWTFJaWLPeaGLUQ|JNWTEJbWAEVS|JNWTEJbWAEVSIMTO|JNWTFJUR|JNWTFJURNUYR|JNWTFJURNUYRJNRM|JNWTEJbWJMTPMQfb|JNWTEJaWLPeaAEVS|JNWTEJbWLPTO|JNWTEJbWLPTOKTXO|JNWTNRUNKRVMIRZU|JNWTEJVRJMTP|JNWTEJVRJMTPMV|JNWTEJbWJMURNU|JNWTFJURNUYRKOTK|"+
        // ─ c3-d4 / b6-a5 (JN+UQ) ────────────────────────────────────────────
        "JNUQ|JNUQNRVM|JNUQNRVMIRWT|JNUQNRVMIRWTLObW|JNUQNRVMIRWTKNTP|JNUQLPVS|JNUQLPVSEJSO|JNUQLPVSEJSOKTXO|JNUQNRVMIRWS|JNUQNRVMIRWSEJbW|JNUQNRVMIRWTEJTP|JNUQEJZU|JNUQEJZULPWT|JNUQEJZULPWTPWaT|JNUQNRVMIRWTLOTP|JNUQFJ|JNUQEJ|JNUQEJVS|JNUQEJVSLO|JNUQKOYU|JNUQKOYUNS|JNUQKOZU|JNUQKOZUFJUR|JNUQLOWT|JNUQNR|JNUQLP|JNUQNRVMIRWTEJbW|JNUQNRVMIRWTLOZU|JNUQLOWS|JNUQLOWSNWbL|JNUQLOWSNWbLHOYU|JNUQLO|JNUQEJYU|JNUQIM|JNUQKO|JNUQNS|JNUQEJVR|JNUQFJZU|JNUQNRVMIRWSLOSL|JNUQNRVMIRZU|JNUQNRVMIRZULOUN|JNUQNRVMIRZUKNdZ|JNUQNRVMIRZUKNWT|JNUQNRVMIRZV|JNUQNRVMIRZVEIVM|JNUQNRVMIRWSEJSN|JNUQLOWTEJZU|JNUQLOWTEJZUNSdZ|JNUQLOWTEJZUNScZ|JNUQLOWTEJZUNSVR|JNUQLOZU|JNUQLOZUEJWT|JNUQLOZUEJWTNSVR|JNUQEJZUAEWT|JNUQEJZUAEWTLPQM|JNUQEJWT|JNUQEJWTAETP|JNUQEJWTAETPLObW|JNUQEJZUAEWTLOVR|JNUQEJWS|JNUQEJWSNWbS|JNUQEJWSNWbSKOZU|JNUQNRVMIRWSEJSO|JNUQKOWT|JNUQKOWTNRTK|JNUQKOWTNRTKGNVM|JNUQNRVMIRWTKNZU|JNUQNRVMIRWTEJZV|JNUQEJZULPVR|JNUQEJZULPVRGLRM|JNUQEJWTAETPLOVR|JNUQEJWTNRVM|JNUQEJWTNRVMIRbW|JNUQEJZUAEUR|JNUQEJZUAEURNUYR|"+
        // ─ c3-d4 / f6-e5 (JN+WS) ────────────────────────────────────────────
        "JNWS|JNWSNWbS|JNWSNWbSIMUQ|JNWSNWbSIMUQLPQJ|JNWSNWbSIMaW|JNWSNWbSIMaWMQUR|JNWSNWaT|JNWSNWaTIMTP|JNWSNWaTIMTPLOUQ|JNWSNWaTKNTP|JNWSNWaTKNTPLOVR|JNWSNWbSIMeb|JNWSNWbSIMebMQSO|JNWSNWaTIMUR|JNWSNWaTIMUREITP|JNWSNWaTLOea|JNWSNWaTLOeaFJbW|JNWSNWaTLOda|JNWSNWaTLOdaEJbW|JNWSNWbSKNSJ|JNWSNWbSKNSJENfb|JNWSNWaTEJVS|JNWSNWaTEJVSJM|JNWSNWbSLPfb|JNWSNWbSLPfbGLUR|JNWSNWbSEJ|JNWSNWbSIMfb|JNWSNWbSIMfbMQbW|JNWSNWbSEJfb|JNWSNWbSEJfbKObW|JNWSNWbSEJUQ|JNWSNWbSEJUQKOZU|JNWSNWaTEJUQ|JNWSNWaTEJUQAEZU|JNWSNWbSIMfbKObW|JNWSNWbSIMaWMQWT|JNWSNWbSLOSL|JNWSNWbSLOSLHOfb|JNWSNWbSEJXT|JNWSNWbSEJXTLPSO|JNWSNWbSLPfbEJbW|JNWSNWaTKNbW|JNWSNWaTKNbWFKVR|JNWSNWbSEJaW|JNWSNWbSEJaWKOUQ|JNWSNWaTKNbWLPWS|JNWSNWaTKNbWFKTP|JNWSNWaTEJea|JNWSNWaTEJeaJNUQ|JNWSNWaTEJeaLPUR|JNWSNW|"+
        // ─ RUSSA (c3-b4 — JM) — [BOOK-V15-2] ────────────────────────────────
        // c3-b4 / f6-e5
        "JMWS|JMWSMQURLPSOKTXOEJZUQZdU|JMWSMQUR|JMWSMQURLPSOKTXOEJbW|JMWSMQURLPSOKTXOEJbWOSTP|JMWSMQURLPSO|JMWSMQURLPSOFJbW|JMWSMQURLPSOFJbWJNVS|JMWSMQURLPFJ|JMWSMQURLPFJKObW|JMWSKOKTWP|JMWSKOKTWPIMaV|JMWSKOKTIMWS|JMWSFJWTEJbW|JMWSFJWTEJbWNUYR|JMWSFJaV|JMWSFJaVJNVS|JMWSFJaVJNVSFJWT|JMWSEJ|JMWSEJbW|JMWSEJbWJNVS|JMWSIMbW|JMWSIMbWFJaV|JMWSMQURLOTP|JMWSMQURLOTPFJbW|JMWSMQURLOTPFJWT|JMWSMQURLObW|JMWSMQURLObWOSTP|JMWSMQURLPaVFJWT|JMWSKO|JMWSFJ|JMWSIM|JMWSMQ|JMWSEJ|"+
        // c3-b4 / b6-c5
        "JMUR|JMURLObW|JMURLObWEJbW|JMURLObWEJbWNUYR|JMURLOTP|JMURLOTPEJbW|JMURLOTPFJaV|JMURFJWT|JMURFJWTEJbW|JMURFJWTIMaV|JMURFJWS|JMURFJWSEJ|JMURFJWSEJbW|JMUREJ|JMUREJbW|JMUREJbWFJaV|JMUREJWT|JMUREJWTFJaV|JMUREJWTIMaV|JMURIM|JMURIMbW|JMURIMbWFJaV|JMURKO|JMURKObW|JMURKObWFJaV|"+
        // c3-b4 / d6-e5
        "JMVS|JMVSMQURLPSOKTXOEJbW|JMVSMQUR|JMVSMQURLPSOKTXOFJaV|JMVSMQURLPFJaV|JMVSFJWT|JMVSFJWTEJbW|JMVSFJaV|JMVSFJaVJNVS|JMVSEJ|JMVSEJbW|JMVSEJbWFJaV|JMVSIM|JMVSIMaV|JMVSKO|JMVSKOaV|JMVSMQ|"+
        // c3-b4 / h6-g5 (Variante Tanueir)
        "JMXT|JMXTLPbXHLaV|JMXTLPbXHLaVFJWT|JMXTLPbXHLZV|JMXTLPbXGLZV|JMXTGLbX|JMXTGLbXHLaV|JMXTLPbX|JMXTFJbX|JMXTFJbXHLaV|JMXTEJ|JMXTLP|JMXTGL|"+
        // c3-b4 / f6-g5
        "JMWT|JMWTNRVMIRUNKRbW|JMWTNRVMIRbW|JMWTNRVMIRUN|JMWTFJbW|JMWTFJbWJNVS|JMWTEJbW|JMWTEJbWFJaV|JMWTIMbW|JMWTIMaV|JMWTLP|JMWTFJ|JMWTEJ|JMWTKO|JMWTNR|JMWTIM|"+
        // c3-b4 / g7-f6 (incomum)
        "JMbW|JMbWNRVMIRWTLObW|JMbWEJWTLObW|JMbWFJWTIMaV|JMbWMQ|JMbWFJ|"+
        // ─ g3-f4 abertura (LO) — [BOOK-V15-4] ───────────────────────────────
        // [BOOK-V25-FIX] Removidas: "LOVS" duplicada (sem efeito) e "LOVT" (d6→g5
        // não é diagonal válida para pedra: Δrow=1,Δcol=3). Ambas filtradas pela
        // engine mas desperdiçavam tempo de build.
        "LOVS|LOVSEJaV|LOVSEJaVJMWT|LOVSEJaVJMWTMQTO|LOVSEJaVKOUQ|LOVSEJaVFJZV|LOVSIMbW|LOVSIMbWFJWT|LOVSVR|LOVSVREJbW|LOVR|LOVREJbW|LOVREJbWFJaV|LOVREJbWMQUR|"+
        // ─ g3-h4 abertura (LP) ───────────────────────────────────────────────
        "LPVS|LPVSIMbW|LPVSIMbWEJaV|LPVR|LPVREJbW|LPVREJbWFJaV|LPVT|LPVTFJbW|LPVTFJbWEJaV|"+
        // ─ c3-d4 / g7-f6 — variantes adicionais ─────────────────────────────
        "JNbW|JNbWFJaV|JNbWFJaVJMWT|JNbWEJaV|JNbWEJaVJMWT|JNbWIMaV|JNbWIMaVFJWT|JNbWKO|JNbWKOaV|"+
        // ─ Variante Americana (JN+VR troca imediata) ─────────────────────────
        "JNVRNUYR|JNVRNUYREJbW|JNVRNUYREJbWJMTP|JNVRNUYREJWTFJaV|JNVRNUYRFJaV|JNVRNUYREJaV|JNVRNUYREJaVFJWT|JNVRNUYRKOaV|JNVRNUYREJaVKO|JNVRNUYREJaVKOUQ|"+
        // ─ c3-b4 variações extras (Alma) — [BOOK-V25-FIX] ───────────────────
        // Seção anterior "JNMQ..." estava errada: iniciava com JN (c3-d4) em vez de
        // JM (c3-b4) e a segunda jogada MQ (b4-a5) referia-se a uma casa sem peça
        // Vermelha no início. Todas as entradas eram inválidas e filtradas pela engine.
        // Substituído por variações Alma legítimas ainda não cobertas na seção Russa.
        "JMVR|JMVREJbW|JMVREJbWFJaV|JMVRFJbW|JMVRFJbWJNVS|JMVRFJaV|JMVRFJaVJNVS|"+
        "";

    // ── [BOOK-V15-1] Parser PDN para novas linhas ────────────────────────────
    // Converte notação algébrica ('c3-d4 d6-e5 ...') para índices [from,to]
    // Todas as linhas são validadas pelo motor antes de entrarem no livro.
    const PDN_EXTRA_LINES = [

        // Russa — linhas complementares extraídas dos campeonatos
        "c3-b4 f6-e5 b4-a5 b6-c5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 c7-b6 a5xc7 d8xb6",
        "c3-b4 f6-e5 b4-a5 b6-c5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 c7-b6",
        "c3-b4 f6-e5 e3-f4 e5xg3 h2xf4 g7-f6 b4-a5 f6-g5 b2-c3",
        "c3-b4 f6-e5 e3-f4 e5xg3 h2xf4 g7-f6 b4-a5 f6-g5",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 g5-h4 c3-b4 f6-e5",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 g5-h4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e5xg3 h2xf4 c7-b6 b2-c3",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e5xg3 h2xf4",
        // Cruz — extensões profundas
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6",
        "c3-d4 d6-e5 b2-c3 b6-c5 d4xb6 a7xc5 g3-f4 f6-g5",
        "c3-d4 d6-e5 b2-c3 b6-c5 d4xb6 a7xc5 a1-b2 b8-a7",
        "c3-d4 d6-e5 e3-f4 b6-a5 b2-c3 e7-d6 g3-h4 g7-f6",
        "c3-d4 d6-e5 e3-f4 b6-a5 b2-c3 e7-d6",
        "c3-d4 d6-e5 g3-f4 e5xg3 h2xf4 f6-g5 b2-c3 g7-f6",
        "c3-d4 d6-e5 g3-f4 e5xg3 h2xf4 f6-g5 b2-c3",
        // Pioneiro — extensões
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 c7-d6 b4-a5 b8-c7",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 c7-d6",
        // Flank — extensões
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6-a5 g3-f4 g5-h4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6-a5",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 g5-h4",
        // Abertura Turca (c3-d4 d6-e5 b2-c3 b6-a5)
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5 b8-c7",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5 h6-g5",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5",
        // Variante Cruz+WT
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f6-g5 f4xe5 d6xf4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f6-g5",
        // Americana
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5 e3-f4 e7-f6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5",
        // Clássica
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4",
        // g3-f4 abertura
        "g3-f4 d6-e5 f4xe5 f6xe4 d2xe4 c7-d6 e4-f5 g7-f6",
        "g3-f4 d6-e5 f4xe5 f6xe4 d2xe4 c7-d6",
        "g3-f4 f6-g5 b2-c3 d6-e5 c3-d4 g7-f6",
        // === Linhas extraídas dos Campeonatos Brasileiros Absolutos ===
        // Cruz captura (d4xf6 g7xe5) — 1 Cbra 1967 Salim Salum
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 e7-f6 b4-a5 b6-c5 e3-f4",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 e7-f6 b4-a5 b6-c5",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 e7-f6",
        // Americana profunda — 1 Cbra 1967 Rabelo
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5 e3-f4 e7-f6 c3-b4 c7-b6 b4-a5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5 e3-f4 e7-f6 c3-b4 c7-b6",
        // Flank variante simetria — 1 Cbra 1967 Salum vs Oliveira
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5",
        // Clássica VR com b2-c3 direto — 1 Cbra 1967 Rosa vs Bueno
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c1-d2",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3",
        // Cruz com f2-e3 — Oliveira vs Ribeiro
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c3-b4",
        // Russa captura invertida — 1 Cbra 1967 Marra vs Jotta
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 g3-h4",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5",
        // Flank com d2-c3 — Bueno vs Oliveira
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 g7-f6 b4xd6 c7xc3 d2xb4",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 g7-f6 b4xd6 c7xc3",
        // Russa com b6-c5 — Izidoro vs Sodre
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 g5-h4 c3-b4 f6-e5",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 g5-h4 c3-b4",
        // Clássica com d2-c3 e7-d6 — Ribeiro vs Izidoro
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2",
        // Russa com h6-g5 (Tanqueir) — Oliveira vs Ribeiro
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 b2xd4 a7xc5",
        // Flank com g3-h4 — multiplos jogos
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 d2xb4 a5xc3 b2xd4",
        "c3-d4 f6-g5 g3-h4 d6-c5 h4xf6 g7xc3 d2xb4",
        // Russa com b6-a5 (Americana invertida) — Marra vs Silva
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6",
        // Cruz com h2-g3 — Ribeiro vs Izidoro extra
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5 c1-b2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5",
        // Flank com a3-b4 — Rabelo vs Ribeiro
        "c3-d4 f6-g5 d4-c5 b6xd4 a3xc5 b6-a5 g3-f4 g5-h4 c5-b6 a7xc5",
        "c3-d4 f6-g5 d4-c5 b6xd4 a3xc5 b6-a5 g3-f4 g5-h4",
        // Russa com d6-e5 — Jotta vs Friques
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 d2-e3 f8-e7 b2-c3 a7-b6",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 d2-e3 f8-e7",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 d2-e3",
        // h6-g5 rara — multiplos
        "c3-d4 h6-g5 g3-h4 g5-f4 e3xg5 d6xe4 d2xf4",
        "c3-d4 h6-g5 g3-h4 d6-c5 h2-g3 e7-d6 b2-c3 g7-h6",
        // b6-a5 rara — multiplos
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g3-f4",
        "c3-d4 b6-a5 g3-h4 d6-e5 b2-c3 e5-f4 e3xg5 h6xf4",
        
        // ╔══════════════════════════════════════════════════════════════════╗
        // ║  [BOOK-V30-FULL] CAMPEONATOS BRASILEIROS ABSOLUTOS — COMPLETO     ║
        // ║  3152 linhas maximais de 3152 aberturas únicas de campeonato ║
        // ╚══════════════════════════════════════════════════════════════════╝
        // --- c3-d4 (1511 linhas de campeonato) ---
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 a1-b2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d6-e5",
        "c3-d4 c7-b6 b2-c3 d6-c5 a1-b2 f6-g5 g3-h4 c5-b4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 c3-b4 c7-b6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 h8-g7",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 b4-c5 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 f4-e5 h2-g3 f6-g5 a3-b2 g5-f4",
        "c3-d4 d6-c5 g3-f4 c7-d6 d4-e5 h2-g3 b6-a5 g1-h2 d4-c3",
        "c3-d4 d6-e5 b2-c3 e7-d6 g3-f4 f6-g5 g1-h2 b6-c5 a3-b4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 e7-f6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 c3-d4 f6-e5",
        "c3-d4 f6-g5 b2-c3 e7-f6 g3-h4 f8-e7 g3-f4 d8-e7 c3-b4 d6-e5",
        "c3-d4 b4-c5 g7-h6 d2-e3 e7-d6 f2-g3 f8-e7 g3-f4 f6-e5 b2-c3 h8-g7",
        "c3-d4 b6-a5 g3-f4 f6-g5 b2-c3 c7-b6 d4-e5 d8-c7 e5-f6 g7xg3 f2xd8",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 d8-c7 e5-f6 g7xg3 f2xd8",
        "c3-d4 d6-e5 d4-c5 b6xd4 e3xc5 e5-f4 g3xe5 f6xb6 g3-f4 e5xd2 e5xf2",
        "c3-d4 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 g3-f4 d6-e5 f4xd6 e7xc5 h2-g3",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 d4-c5 d6xb4 a3xc5",
        "c3-d4 d6-c5 b2-c3 c7-d6 h2-g3 c5-b4 a1-b2 b4-a3 b8-c7 c3-d4 c7-d6 b2-c3",
        "c3-d4 d6-e5 b2-c3 e7-d6 g3-h4 d6-c5 f2-g3 c7-d6 g3-f4 e5xg3 h4xf2 d6-e5",
        "c3-d4 f6-e5 b2-c3 e5-f4 d2-e3 b6-a5 d6-c5 e3-d4 c7-d6 c1-d2 f6-g5 d6-e5",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 f2-e3 h8-g7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 d8-e7 f4-g5 h6xf4 f2-e3 g7-h6 e3xg5 f6xf2 d4xd8",
        "c3-d4 d6-e5 d2-c3 e7-d6 g3-h4 h6-g5 e1-d2 b6-a5 f2-g3 c7-b6 e5xg3 h2xh6 d6-c5",
        "c3-d4 d6-e5 g3-f4 e5xc3 b2xd4 b6-a5 a1-b2 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 b2-c3",
        "c3-d4 h6-g5 g3-h4 h6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 f6xb6 g3-h4",
        "c3-d4 b6-a5 b2-c3 c7-b6 a1-b2 f6-g5 g3-h4 a5-b4 c3xe5 e7-d6 h4xf6 d6xf4 e3xg5 g7xa1",
        "c3-d4 b6-c5 d4xb6 c7xa5 g3-h4 f6-e5 h4-g5 h6xf4 e3xg5 a7-b6 e7xg5 a3-b4 a5xc3 b2xh4",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-h4 g7-h6 h2-g3 e7-d6 g3-f4 d8-e7 f6xb2 h4xd8 b8-a7 a1xc3",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 d8xb6 g5xe3 c3-b4 a5xe5 f2xd8",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b8-c7 a3-b4 c5xa3 g5xc5 c3-b4 d6xf4 b4xb8",
        "c3-d4 d6-e5 b2-c3 b6-a5 a1-b2 c7-d6 a3-b4 d8-c7 e3-f4 c7-b6 h6xf4 b4-c5 d6xb4 f2-e3",
        "c3-d4 d6-e5 d2-c3 e7-d6 g3-h4 h6-g5 e1-d2 b6-a5 f2-g3 c7-b6 g3-f4 e5xg3 h2xh6 d6-c5",
        "c3-d4 d6-e5 h2-g3 e7-d6 a1-b2 f6-e5 g7-f6 c1-d2 d6-c5 e3-f4 c7-d6 f2-e3 f6-g5 g3-h4",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 b2xd4 c7-d6 a1-b2 g5-f4 g3xa5 f6-g5 h4xf6 g7xa1",
        "c3-d4 b6-a5 b2-c3 f6-e5 d4xf6 g7xe5 e3-f4 c7-b6 c3-d4 e5xc3 d2xb4 a5xc3 f4-g5 h6xf4 g3xa5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 c7-b6 g3-f4 b6xd4 e3xc5",
        "c3-d4 b6-a5 g3-f4 f6-g5 b2-c3 c7-b6 d4-e5 b8-c7 e3-d4 g5xc5 c1-b2 d6xf4 c3-b4 a5xc3 d2xb8",
        "c3-d4 b6-c5 d4xb6 c7xa5 b2-c3 f6-e5 e3-f4 a7-b6 c3-d4 e5xc3 d2xb4 a5xc3 f4-g5 h6xf4 g3xa5",
        "c3-d4 b6-c5 d4xb6 c7xa5 g3-h4 f6-e5 h4-g5 h6xf4 e3xg5 a7-b6 g5-f6 e7xg5 a3-b4 a5xc3 b2xh4",
        "c3-d4 d6-c5 b2-c3 e7-d6 a1-b2 d6-e5 g3-h4 c5-b4 a3xc5 e5-f4 e3xe7 f8xb4 c3xa5 h6-g5 h4xf6",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 d8xb6 e3-d4 g5xe3 c3-b4 a5xe5 f2xd8",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b8-c7 a3-b4 c5xa3 e3-d4 g5xc5 c3-b4 d6xf4 b4xb8",
        "c3-d4 d6-e5 b2-c3 b6-a5 a1-b2 c7-d6 a3-b4 d8-c7 e3-f4 c7-b6 f4-g5 h6xf4 b4-c5 d6xb4 f2-e3",
        "c3-d4 d8-c7 b4-a5 g5-f4 d2-e3 g7-f6 f6-g5 h2-g3 f8-g7 b2-c3 e7-d6 g3-f4 h4-g3 g1-f2 a1-b2",
        "c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 b6-a5 e3-f4 c7-b6 c3-d4 e5xc3 d2xb4 a5xc3 f4-g5 h6xf4 g3xa5",
        "c3-d4 f6-g5 b2-c3 g7-f6 g3-f4 h8-g7 a1-b2 d6-c5 f2-g3 g5-h4 h4xf2 e1xg3 b6-a5 d4xb6 f6xh4",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 f8-g7 b2-c3 c7-b6 c3-d4 b8-c7 h2-g3",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g1-f2 e5xc3 d2xb4 b6-a5 c1-d2 a5xc3 b2xd4 a7-b6 d4-e5",
        "c3-d4 b6-a5 b2-c3 c7-b6 g3-h4 d6-c5 f2-g3 c5-b4 a3xc5 f6-g5 h4xf6 g7xe5 d4xf6 b6xh4 c3-d4 e7xg5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 d8-c7 g3-f4 f6-g5 g5xe3 c3-b4 a5xe5 f2xd8 b6xd4 d8xf2",
        "c3-d4 b6-c5 e3-f4 h8-g7 f2-e3 c5-b4 b2-a3 d6-c5 c7-d6 a1-b2 d6-e5 g5-h6 e5-d4 g3-f4 f6-e5 b4-c3",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 b8-c7 c3-b4 a5xa1 d2-c3 a1xg3 f2xd8",
        "c3-d4 d6-c5 g3-h4 c7-d6 f2-g3 c5-b4 a3xc5 d6xb4 b2-a3 b8-c7 a3xc5 f6-g5 h4xf6 g7xc3 d2xb4 b6xh4",
        "c3-d4 d6-e5 b2-c3 e7-d6 a1-b2 d6-c5 g3-h4 c5-b4 a3xc5 e5-f4 e3xe7 f8xb4 c3xa5 h6-g5 h4xf6 g7xa1",
        "c3-d4 d6-e5 b2-c3 h8-g7 e3-d4 g7-f6 d2-e3 e7-d6 f6-e5 g3-f4 f8-e7 e3-d4 e7-f6 d4-c5 f4-g5 d2-e3",
        "c3-d4 f6-g5 b2-c3 d6-c5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 b8xd6 a5xc3 d2xb4 g7-f6 b4-a5 d8-c7 f2-g3",
        "c3-d4 g3-h4 d4-c5 e3xc5 h6-g5 g7-h6 b6xd4 d6xb4 a3xc5 b2-a3 a3xc5 a1-b2 c7-d6 d6xb4 g5-f4 f8-g7",
        "c3-d4 g7-f6 b2-c3 f6-g5 g3-h4 e7-f6 f2-g3 f6-e5 d6-e5 h2-g3 a7-b6 g1-h2 h8-g7 c3-d4 e3-d4 g3-f4",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 d2xb4 g7-h6 g1-h2 b6-a5 a5xc3 d2xb4 e7-d6 b2-c3 a7-b6 b4-a5",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g1-f2 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 a1-b2 f8-g7 d2-c3 e7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 d8-c7 g3-f4 f6-g5 d2-c3 g5xe3 c3-b4 a5xe5 f2xd8 b6xd4 d8xf2",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 g3-f4 e5xg3 f2xh4 f6-e5 e3-f4 e5xg3 h4xf2",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c7-b6 a3-b4 c5xa3 c1-b2 a3xc1 d2-c3 c1xf4 g3xa5 c3-d4 c3xe5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 e7-f6 e3-f4 h6-g5 f4xh6 e5-f4 g3xe5 f6xb2",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 a1-b2 b8-c7 c3-b4 a5xa1 d2-c3 a1xg3 f2xd8",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-h4 b6-a5 d4xb6 a5xc7 h2-g3 f6-e5 a7-b6 c1-b2 h6-g5 h4xd4 d6-e5 d4xf6 e7xc1",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-h4 b6-a5 d4xb6 a5xc7 h2-g3 f6-e5 a7-b6 g1-h2 h6-g5 h4xd4 d6-e5 d4xf6 e7xg1",
        "c3-d4 d6-e5 d2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 b8-c7 a3-b4 c7-b6 a5xc7 d6xb8 f4xd6 e7xa3",
        "c3-d4 f6-e5 e3-f4 h8-g7 b2-c3 g7-f6 f2-e3 b6-c5 f6-e5 g1-h2 e7-f6 c3-d4 b8-a7 a1-b2 f6-e5 b2-c3 d8-e7",
        "c3-d4 f6-g5 g3-f4 d6-c5 b2-c3 e7-d6 c1-b2 g7-f6 c3-b4 b6-a5 d4xb6 a5xc3 b2xd4 c7xa5 d4-c5 d6xb4 a3xc5",
        "c3-d4 b6-a5 b2-c3 c7-b6 a1-b2 f6-g5 g3-f4 d6-c5 f4-e5 e7-f6 f2-g3 g5-h4 g1-f2 a5-b4 c3xc7 b8xf4 e3xe7 c5xg1",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 e3-f4 c5-d4 c1-d2 d4-c3 b2xf6 e7xc1",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 b2-c3 e7-f6 e3-f4 h6-g5 f4xh6 e5-f4 g3xe5 f6xb2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-f4 e3xg5 f6xh4 c3-d4 c7-b6 b4-c5 d6xb4 a3xc5",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-h4 b6-a5 d4xb6 a5xc7 h2-g3 f6-e5 e3-f4 a7-b6 c1-b2 h6-g5 h4xd4 d6-e5 d4xf6 e7xc1",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-h4 b6-a5 d4xb6 a5xc7 h2-g3 f6-e5 e3-f4 a7-b6 g1-h2 h6-g5 h4xd4 d6-e5 d4xf6 e7xg1",
        "c3-d4 d6-c5 b2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b8-c7 a3-b4 c5xa3 e3-d4 g5xc5 c3-b4 d6xf4 b4xb8 g7-f6 b8xg3 b6-c5",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 h6-g5 f2-g3 c7-d6 a5xe5 g5-h4 d4xb6 h4xf6",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 d8xb6 b8-c7 a3-b4 a5xg3 f2xd8 c5-b4 d8-h4 b4-a3 h4-f2",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 d8xb6 c5xa3 c1-d2 a3xc1 a1-b2 c1xa3 c3-b4 a3xg3 f2xd8",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 b8-c7 f6-g5 a1-b2 e5-d4 f4-e5 d4xh4 e1-f2 d6xf4 b4xb8",
        "c3-d4 d6-e5 d2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 b4-a5 b8-c7 a3-b4 c7-b6 a5xc7 d6xb8 f4xd6 e7xa3",
        "c3-d4 f6-g5 d2-c3 g5-h4 c1-d2 g7-f6 c3-b4 f6-g5 d4-c5 b6xd4 e3xc5 d6-e5 b4-a5 e5-f4 g3xe5 c7-b6 a5xc7 d8xf6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 b8-c7 e5-f6 g7xe5 e3-d4 c5xe3 d2xb8",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 e7-d6 c5xe7 f8xd6 d6-e5 b2-a3 e5xc3 d2xb4 a5xc3 e1-d2 c3xg3 h2xf8",
        "c3-d4 b4-a3 g3-h4 e7-d6 d4-e5 b2-c3 d6-e5 g7-f6 f2-e3 c7-d6 g1-h2 b8-c7 e3-f4 b6-c5 d2-e3 a7-b6 e1-d2 h8-g7 f4-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 d8-c7 c7-b6 e3-d4 f6-g5 b2-c3 g5xe3 c3-b4 a5xe5 f2xd8 b6xd4",
        "c3-d4 b6-a5 g3-f4 f6-g5 b2-c3 c7-b6 d4-e5 d6-c5 c3-d4 b8-c7 e5-f6 g7xg3 f2xf6 e7xg5 a3-b4 a5xe5 e3-d4 c5xe3 d2xb8",
        "c3-d4 b6-c5 d4xb6 c7xa5 g3-f4 f6-e5 f2-g3 a7-b6 f4-g5 h6xf4 e3xg5 g7-h6 g1-f2 h6xf4 a3-b4 a5xc3 b2xf6 e7xg5 g3xa5",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 d6-e5 h2-g3 c7-d6 h4-g5 h6xh2 c5xa3 f2-g3 h2xf4 e3xc5 b8-c7 d4xf6 b6xb2 a1xc3 g7xe5",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 d8xb6 a3-b4 c5xa3 c1-d2 a3xc1 a1-b2 c1xa3 c3-b4 a3xg3 f2xd8",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 d8xb6 c3-d4 b8-c7 a3-b4 a5xg3 f2xd8 c5-b4 d8-h4 b4-a3 h4-f2",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 b8-c7 f2-e3 f6-g5 a1-b2 e5-d4 f4-e5 d4xh4 e1-f2 d6xf4 b4xb8",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g3-h4 e5xg3 h4xf2 d6-c5 h2-g3 f8-e7 c3-b4 a5xe5 e3-d4 c5xe3 d2xf8",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 f8-e7 a1-b2 f6-g5 f2-e3 e5-d4 f4-e5 d4xh4 e1-f2 d6xf4 b4xf8",
        "c3-d4 d6-e5 d2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 b8-c7 b2-c3 d4xb2 a1xc3 h6-g5 f4xh6 e5-f4 g3xe5 f6xb2",
        "c3-d4 d6-e5 d2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 b8-c7 c1-d2 h6-g5 f4xh6 f6-g5 h6xf4 d4-e3 f2xf6 e7xc1",
        "c3-d4 d6-e5 d2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 b8-c7 g3-h4 e5xg3 h2xf4 d4-c3 b2xd4 f6-g5 h4xf6 e7xc5",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b8-c7 e5-f6 g7xe5 e3-d4 c5xe3 d2xb8",
        "c3-d4 g7-f6 d4-c5 b6-a5 c3-d4 f6-g5 b2-c3 c7-b6 b8-c7 g3-f4 h8-g7 a3-b4 e7-d6 b2-a3 f8-e7 h2-g3 g7-f6 b4-c5 c7-d6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 e7-d6 c5xe7 f8xd6 e3-d4 d6-e5 b2-a3 e5xc3 d2xb4 a5xc3 e1-d2 c3xg3 h2xf8",
        "c3-d4 a5-b4 b2-a3 c7-d6 a1-b2 b4-a3 h6-g5 g3-f4 b8-c7 h2-g3 g7-h6 g3-f4 h8-g7 g1-f2 g7-f6 f2-e3 f6-g5 e1-f2 e7-d6 d2-c3",
        "c3-d4 a7-b6 b4-a5 f6-e5 e3-f4 c5-d4 a3-b4 b6-c5 h8-g7 g3-h4 g7-f6 f4-g5 f2-e3 c1-d2 e7-f6 d2-e3 f6-e5 e3-f4 d8-e7 a1-b2",
        "c3-d4 a7-b6 b4-a5 f6-g5 b2-c3 g5-f4 a1-b2 e7-d6 d4-e5 f4-g3 b6-c5 c3-b4 d8-e7 c1-d2 g7-h6 e1-f2 c5-d4 d6-c5 d2-e3 b8-a7",
        "c3-d4 b2-c3 c1-b2 c3-b4 d6-c5 f6-g5 g7-f6 e7-d6 b4-a5 g3-f4 h2-g3 d4-e5 d8-e7 h8-g7 g5-h4 f6xd4 g1-h2 f4xh6 e3-f4 d2-c3",
        "c3-d4 b2-c3 c3-b4 b4-c5 f6-g5 g7-f6 g5-h4 d6xb4 a3xc5 g3-f4 c5-b6 d4xb6 b6-a5 f6-g5 a7xc5 h8-g7 b6-a7 a1-b2 f4-e5 d2-c3",
        "c3-d4 b2-c3 c3-b4 b4-c5 f6-g5 g7-f6 h8-g7 d6xb4 a3xc5 a1-b2 b2-a3 d2-c3 g5-h4 b6-a5 c7-b6 e7-d6 c5xg5 a3xc5 g3-f4 f4-e5",
        "c3-d4 b2-c3 c3-b4 b4-c5 f6-g5 g7-f6 h8-g7 d6xb4 a3xc5 a1-b2 g3-f4 b2-a3 g5-h4 b6-a5 c7-d6 d6xb4 a3xc5 c1-b2 c5xe7 f4-e5",
        "c3-d4 b2-c3 c3-b4 b4-c5 f6-g5 g7-f6 h8-g7 d6xb4 a3xc5 c1-b2 b2-a3 c5-b6 g5-h4 b6-a5 f6-g5 a7xc5 d4xb6 b6-a7 a3xc5 a1-b2",
        "c3-d4 b2-c3 c3-b4 b4xd6 d6-c5 h6-g5 b6-a5 c7xc3 d2xb4 g3-f4 c1-b2 b2xd4 a5xc3 g5-h4 e7-d6 h4-g3 f2xh4 f4xd6 h4xf6 e3-f4",
        "c3-d4 b2-c3 c3-b4 b4xd6 f6-g5 d6-c5 b6-a5 c7xc3 d2xb4 c1-b2 b2xd4 d4-c5 a5xc3 a7-b6 b6-a5 g5-h4 g3-f4 f4-e5 e5xc7 e3xc5",
        "c3-d4 b2-c3 c3-b4 d4-c5 f6-g5 g5-h4 b6-a5 a5xc3 d2xb4 b4-a5 a5xc3 c3-b4 g7-f6 d6xb4 a7-b6 b6-a5 c1-d2 d2xb4 a1-b2 b4-a5",
        "c3-d4 b2-c3 c3-b4 d4-c5 f6-g5 g5-h4 g7-f6 b6xd4 e3xc5 d2-e3 e3xc5 b4-a5 c7-b6 b6xd4 d8-c7 d6xb4 a5xc3 c3-b4 b4-a5 a1-b2",
        "c3-d4 b2-c3 c3-b4 d4-c5 f6-g5 g7-f6 g5-h4 b6xd4 e3xc5 a1-b2 g3-f4 f2xf6 f6-e5 h6-g5 g5xe3 e7xg5 c5xe7 b4-a5 a3-b4 b2-c3",
        "c3-d4 b2-c3 c3-b4 d4-c5 f6-g5 g7-f6 g5-h4 b6xd4 e3xc5 g3-f4 h2xf4 c1-b2 f6-e5 e5xg3 h8-g7 g7-f6 b4-a5 a5xc3 c3-b4 b4-c5",
        "c3-d4 b2-c3 c3-b4 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 a1-b2 b2-c3 b4-c5 a3xc5 a7-b6 b6-a5 d6xb4 f6-g5 c5-b6 g3-f4 b6-a7 c3-b4",
        "c3-d4 b2-c3 c3-b4 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 a1-b2 b2-c3 e3-f4 b4-a5 f6-e5 g7-f6 a7-b6 f8-g7 d2-e3 c3-b4 g3-h4 h2xf4",
        "c3-d4 b2-c3 c3-b4 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 a1-b2 g3-f4 b2-c3 b4-a5 h6-g5 g7-h6 a7-b6 f6-e5 f2-g3 e3-d4 e1xg3 d4xf6",
        "c3-d4 b2-c3 c3-b4 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 a1-b2 g3-f4 b4-c5 a3xc5 h6-g5 g7-h6 d6xb4 h8-g7 b2-c3 c3-b4 f4xd6 e3xg5",
        "c3-d4 b2-c3 c3-b4 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 b4-c5 a3xc5 g3-f4 e3xc5 d6xb4 c7-b6 b6xd4 f6-g5 h2-g3 f2xd4 g3-f4 a1-b2",
        "c3-d4 b2-c3 c3-b4 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 e3-d4 b4-a5 d4-c5 a5xc3 h6-g5 g5-h4 d6xb4 f6-e5 a3-b4 b4-a5 g3-f4 h2xf4",
        "c3-d4 b2-c3 c3-b4 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 e3-d4 d4xf6 g3-h4 b4-a5 f6-e5 g7xe5 a7-b6 h8-g7 a1-b2 h2-g3 g3xe5 a3-b4",
        "c3-d4 b2-c3 c3-b4 d4xb6 f6-g5 d6-c5 b6-a5 a5xc3 d2xb4 c1-b2 b2xd4 g3-f4 c7xc3 a7-b6 b6-a5 g5-h4 h2-g3 a1-b2 e1-d2 f4-e5",
        "c3-d4 b2-c3 c3-b4 d4xf6 f6-g5 g5-h4 d6-e5 g7xe5 d2-c3 b4-a5 e3xg5 g3-h4 e7-d6 e5-f4 h4xf6 b6-c5 f2-e3 e3-f4 h2xf4 e1-d2",
        "c3-d4 b2-c3 d4-c5 a3xc5 f6-g5 b6-a5 d6xb4 g7-f6 g3-f4 c1-b2 f4-e5 e3xa3 c7-d6 d6xb4 f6xd4 a7-b6 h2-g3 c3-b4 b2xd4 d2-e3",
        "c3-d4 b2-c3 e3-f4 d2-e3 d6-e5 e7-d6 f8-e7 b6-c5 a3-b4 e3-d4 a1-b2 c7-b6 d8-c7 e1-d2 d4-c5 b6-a5 c7-d6 g3-f4 f2-e3 g1-f2",
        "c3-d4 b2-c3 e3-f4 d4xb6 d6-e5 e7-d6 b6-c5 a7xc5 c3-b4 f2-e3 f4-e5 e5xa5 c7-b6 e5-d4 d4xh4 d8-e7 b4xd6 a1-b2 b2-c3 c3-d4",
        "c3-d4 b2-c3 e3-f4 d4xb6 d6-e5 e7-d6 b6-c5 c7xa5 f2-e3 c1-b2 g3-h4 h4xf2 a7-b6 f8-e7 e5xg3 h6-g5 c3-b4 d2xb4 e3xg5 b4-c5",
        "c3-d4 b2-c3 g3-f4 c1-b2 f6-g5 g5-h4 d6-c5 g7-f6 c3-b4 b4xd6 d2xb4 h2-g3 f6-g5 c7xc3 b6-a5 a5xc3 b2xd4 a3-b4 d4-c5 c5xe7",
        "c3-d4 b2-c3 g3-h4 d4xb6 b6-a5 c7-b6 b6-c5 a5xc7 h2-g3 e3-f4 d2-e3 c3-b4 f6-e5 a7-b6 g7-f6 b6-c5 b4-a5 e1-d2 a1-b2 a3-b4",
        "c3-d4 b2-c3 g3-h4 h2-g3 d6-c5 h6-g5 g7-h6 e7-d6 g3-f4 d4xf6 c3-b4 f2-g3 f6-e5 g5xe7 b6-a5 a5xc3 d2xb4 b4-a5 a1-b2 c1-d2",
        "c3-d4 b4-a3 d4-c5 b6-a5 c3-d4 a7-b6 g3-f4 c7-d6 b6-c5 g3-h4 c7-b6 b2-c3 b6-a5 a1-b2 g7-f6 c3-d4 d8-c7 b2-c3 h8-g7 g1-h2",
        "c3-d4 b4-a3 d4-c5 h6-g5 c3-d4 g5-h4 g7-f6 a1-b2 a7-b6 d4-c5 g3-f4 c7-d6 f4-g5 b8-c7 b2-c3 f6-e5 g5-h6 c7-b6 f2-g3 b6-a5",
        "c3-d4 b4-a3 g3-h4 f6-e5 d4xf6 g7xe5 b2-c3 e7-d6 e3-d4 h6-g5 d4xf6 g5xe7 h4-g5 d6-e5 f2-g3 h8-g7 g5-h6 e7-f6 g3-h4 e5-d4",
        "c3-d4 b4-a3 g3-h4 f6-e5 d4xf6 g7xe5 h4-g5 h6xf4 e3xg5 h8-g7 e5-f4 b2-c3 b6-c5 c3-b4 c7-d6 f2-e3 b8-c7 e3xg5 c5-d4 a1-b2",
        "c3-d4 b6-a5 b2-c3 a7-b6 a1-b2 d6-c5 a3-b4 c5xa3 d4-e5 f6xd4 e3xa7 g7-f6 c3-d4 c7-d6 b2-c3 d6-c5 d4xb6 a5xc7 g3-h4 h8-g7",
        "c3-d4 b6-a5 b2-c3 c7-b6 a1-b2 b6-c5 d4xb6 a7xc5 c3-d4 g5-h4 d4xb6 a5xc7 b2-c3 f6-g5 a3-b4 e7-d6 b4-a5 g7-f6 c3-b4 f8-g7",
        "c3-d4 b6-a5 b2-c3 c7-b6 g3-f4 d8-c7 f2-g3 d6-e5 f4xd6 e7xc5 f8-e7 h2-g3 c7-d6 g1-h2 c5-b4 f4-g5 h6xf4 g3xc7 b6xd8 e3-f4",
        "c3-d4 b6-a5 b2-c3 c7-b6 g3-h4 b6-c5 d4xb6 a5xc7 a3-b4 a7-b6 b4-a5 f6-e5 e3-d4 g7-f6 f2-g3 f8-g7 g3-f4 e5xg3 h4xf2 f6-e5",
        "c3-d4 b6-a5 b2-c3 c7-b6 g3-h4 f6-g5 h4xf6 e7xg5 d4-e5 d6xf4 f2-g3 f8-e7 g3xe5 b8-c7 c1-b2 g5-h4 g1-f2 h6-g5 e3-d4 g7-h6",
        "c3-d4 b6-a5 b2-c3 c7-b6 g3-h4 f6-g5 h4xf6 e7xg5 d4-e5 d6xf4 f8-e7 g3xe5 b8-c7 e3-d4 g7-f6 e5xg7 h6xf8 h2-g3 e7-d6 g1-h2",
        "c3-d4 b6-a5 b2-c3 d6-e5 g3-f4 c7-b6 a1-b2 b6-c5 f4-g5 a7-b6 g5-h6 b6-a5 c3-d4 c7-d6 b2-c3 b8-a7 f2-g3 a7-b6 g1-h2 d6-c5",
        "c3-d4 b6-a5 b2-c3 f6-g5 a1-b2 g5-h4 g3-f4 d6-c5 d4xb6 a7xc5 c3-d4 c7-d6 d4xb6 a5xc7 d2-c3 g7-f6 c3-b4 f6-g5 b2-c3 e7-f6",
        "c3-d4 b6-a5 b2-c3 f6-g5 a1-b2 g5-h4 g3-f4 g7-f6 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 e7-f6 f2-e3 h8-g7 b2-a3 h4-g3 g1-f2 g3xe5",
        "c3-d4 b6-a5 b2-c3 f6-g5 d4-c5 d6xb4 a3xc5 g7-f6 g3-f4 h8-g7 a1-b2 g5-h4 f4-g5 h6xf4 e3xg5 h4-g3 h2xf4 f6xh4 f2-e3 g7-f6",
        "c3-d4 b6-a5 b2-c3 f6-g5 g3-h4 g7-f6 f2-g3 c7-b6 g3-f4 b6-c5 d4xb6 a5xc7 c3-b4 a7-b6 b4-a5 b6-c5 a1-b2 b8-a7 e1-f2 f8-g7",
        "c3-d4 b6-a5 b2-c3 g7-h6 g3-f4 c7-b6 f4-g5 h8-g7 b6-c5 c3-d4 a7-b6 a1-b2 b6-a5 b2-c3 c7-b6 f2-e3 b6-c5 e3-d4 c7-b6 h2-g3",
        "c3-d4 b6-a5 d2-c3 g5-h4 d4-c5 f6-g5 c3-b4 c7-b6 b6-a5 f4-e5 e7-d6 g5-f4 c5-d6 h6-g5 d4-c5 g5-f4 f2-e3 f6-g5 h2-g3 g7-f6",
        "c3-d4 b6-a5 d2-c3 g5-h4 d4-c5 f6-g5 c3-b4 c7-b6 b6-a5 f4-e5 g7-f6 h2-g3 a5-b4 c5-d6 e3-f4 b8-c7 e3-f4 f8-e7 e1-f2 f6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3-c5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 f4-g5 h6xf4 e3xg5 e3xg5 c7-d6 f6-e5 c3-b4 a5xc3 d2xb4 f6-e5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 d8-c7 g3-f4 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 c1-b2 f6-g5 d2-c3 g5xe3 c3-b4 a5xe5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 d8-c7 g3-f4 c7-d6 d6xb4 a3xc5 b8-c7 c1-b2 f6-g5 d2-c3 g5xe3 c3-b4 a5xe5 f2xd8",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 f6-g5 d2-e3 g5-h4 g3-f4 g7-f6 h2-g3 f6-g5 e1-d2 h8-g7 d2-c3 d8-c7 b2-a3 c7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 f6-g5 d2-e3 g5-h4 g7-f6 h2-g3 f6-g5 e1-d2 h8-g7 d2-c3 d8-c7 b2-a3 c7-d6 c3-b4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 d8-c7 c7-b6 e3-d4 b8-c7 e1-d2 c7-d6 b2-a3 d6xb4 a3xc5 f6-g5 d2-c3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 d8-c7 d2-e3 c7-b6 e3-d4 b8-c7 e1-d2 c7-d6 b2-a3 d6xb4 a3xc5 f6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 d8-c7 d2-e3 c7-b6 e3-d4 f6-g5 b2-c3 g5xe3 c3-b4 a5xe5 f2xd8 b6xd4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 f6-g5 h2-g3 g5xe3 f2xd4 e7-d6 c5xe7 f8xd6 b2-a3 a7-b6 a1-b2 g7-f6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f6-g5 d8-c7 a1-b2 g7-f6 d2-e3 c7-b6 c1-d2 g5-h4 b2-a3 a5-b4 e3-f4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f6-g5 e3-d4 d8-c7 a1-b2 g7-f6 d2-e3 c7-b6 b2-a3 g5-h4 c1-d2 h8-g7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f6-g5 e3-d4 d8-c7 a1-b2 g7-f6 d2-e3 c7-b6 c1-d2 g5-h4 b2-a3 a5-b4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f6-g5 e3-d4 g7-f6 a1-b2 d8-c7 d2-e3 c7-b6 c1-d2 g5-h4 b2-a3 f6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f6-g5 g7-f6 a1-b2 d8-c7 d2-e3 c7-b6 c1-d2 g5-h4 b2-a3 f6-g5 d2-c3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 e5-d4 c3xe5 c7-d6 e5xc7 b8xb4 a1-b2 b4-a3 b2-c3 h6-g5 g3-h4 a7-b6 h4xf6 g7xe5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 e5-f4 g3xe5 e7-d6 c5xe7 d8xb2 a1xc3 f8-e7 h2-g3 g7-f6 g3-h4 c7-d6 f2-g3 a7-b6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 e5xg3 f2xh4 f6-e5 e3-f4 e5xg3 h4xf2 c7-b6 d2-e3 b6xd4 e3xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 e5xg3 f2xh4 f6-e5 e3-f4 e5xg3 h4xf2 c7-d6 b2-a3 d6xb4 a3xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 e5xg3 f2xh4 f6-e5 g1-f2 c7-b6 e3-d4 g7-f6 b2-a3 e5-f4 h4-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 g3-f4 e5xg3 h2xf4 f6-e5 f4xd6 c7xe5 e3-f4 e5xg3 f2xh4 b8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 c7-b6 g3-f4 e5xg3 h2xf4 b6xd4 c3xg7 h8xf6 b2-c3 a7-b6 a1-b2 b6-c5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 h8-g7 e5xg3 h2xf4 c7-b6 c3-b4 a5xc3 b2xd4 f6-g5 f2-g3 g5-h4 a1-b2",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 h8-g7 e5xg3 h2xf4 c7-b6 c3-d4 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 f4-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 h8-g7 g3-f4 e5xg3 h2xf4 c7-b6 c3-b4 a5xc3 b2xd4 f6-g5 a1-b2 b6-a5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 g3-f4 e5xg3 h2xf4 f6-e5 f4xd6 c7xe5 e3-d4 e5-f4 g1-h2 h6-g5 f2-g3 b8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 c7-b6 e3-d4 f6-g5 g3-h4 g5xe3 d2xf4 h8-g7 c5-d6 e7xg5 h4xh8",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 e3-d4 f6-g5 f2-g3 g5xe3 d4xf2 h8-g7 g3-f4 c7-d6 b2-a3 d6xb4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 e3-d4 h8-g7 f2-g3 f6-g5 g3-h4 g5xe3 d4xf2 c7-b6 d2-e3 b6xd4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 f2-g3 c7-b6 e3-d4 f6-g5 g3-h4 g5xe3 d2xf4 h8-g7 c5-d6 e7xg5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 f2-g3 f6-g5 e3-d4 g5xe3 d2xf4 h8-g7 e1-d2 g7-f6 d2-e3 f6-g5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 f6-g5 e3-d4 g5xe3 d2xf4 h8-g7 e1-d2 g7-f6 d2-e3 f6-g5 g3-h4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 h8-g7 f2-g3 f6-g5 g3-h4 g5xe3 d4xf2 c7-b6 d2-e3 b6xd4 e3xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 c3-b4 a5xc3 d2xb4 d6-e5 b4-a5 g5-f4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 c3-b4 a5xc3 d2xb4 d6-e5 e3-f4 g5xe3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 c3-b4 a5xc3 d2xb4 d6-e5 g3-f4 e5xg3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 c7-d6 c3-b4 a5xc3 d2xb4 d6-e5 g3-f4 e5xg3 f2xf6 g7xe5 e3-f4 e5xg3 h2xf4 h8-g7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 b2-a3 h8-g7 c3-b4 a5xc3 d2xb4 h6-g5 g3-f4 g7-h6 c1-b2 c7-b6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 c3-d4 c7-b6 g3-f4 f6-g5 f4-e5 d8-c7 b2-a3 h8-g7 a3-b4 a5xc3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 f6-e5 d4xf6 e7xg5 b2-c3 c7-b6 c3-d4 f8-e7 g3-f4 d8-c7 c1-b2",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 f6-g5 c3-d4 c7-b6 f4-e5 d8-c7 b2-a3 h8-g7 a3-b4 a5xc3 d2xb4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 g3-f4 f6-g5 c3-d4 h8-g7 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 b4-a3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 h8-g7 c3-b4 a5xc3 d2xb4 h6-g5 e1-d2 c7-b6 g3-f4 b6xd4 e3xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 h8-g7 c3-b4 a5xc3 d2xb4 h6-g5 e3-d4 g7-h6 c1-d2 e7-d6 c5xe7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 h6-g5 g7-f6 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 f8-g7 b2-c3 b4-a3 c3-b4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 h6-g5 g7-h6 c3-d4 c7-b6 f4-e5 f8-g7 d2-c3 g7-f6 e5xg7 h6xf8 h2-g3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 c3-d4 c7-b6 f4-g5 h6xf4 e3xg5 b8-c7 a1-b2 c7-d6 b2-a3 d6xb4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 c3-d4 c7-b6 f4-g5 h6xf4 e3xg5 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 b4-a3 f4-e5 e7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 e7-d6 a1-b2 b4-a3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 e7-d6 d2-c3 b4xd2",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 f6-g5 c3-b4 a5xc3 d2xb4 e7-f6 e1-d2 c7-b6 g3-f4 b6xd4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 h8-g7 c3-b4 a5xc3 d2xb4 h6-g5 c1-b2 g7-h6 e3-d4 e7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 h8-g7 c3-b4 a5xc3 d2xb4 h6-g5 e1-d2 c7-b6 g3-f4 b6xd4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 h8-g7 c3-b4 a5xc3 d2xb4 h6-g5 e3-d4 c7-b6 b4-a5 g7-h6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 c3-d4 c7-b6 g3-f4 f6-g5 f4-e5 h8-g7 e5-d6 e7-f6 h2-g3 d8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 c3-d4 h8-g7 g3-f4 f6-g5 c5-b6 a7xc5 d4xb6 e7-d6 b6-a7 f8-e7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 f6-g5 c3-d4 c7-b6 f4-e5 h8-g7 b2-c3 g7-f6 e5xg7 g5-f4 e3xg5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 h8-g7 c3-b4 a5xc3 d2xb4 h6-g5 c5-d6 c7xe5 g3-f4 e5xg3 h2xh6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 c3-d4 g5-h4 c7-b6 g3-f4 f6-g5 f4-e5 h8-g7 b2-c3 g7-f6 e5xg7 g5-f4 e3xg5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 c7-d6 c1-b2 d6xb4 f4-e5 f6xd4 e3xa3 e7-d6 h2-g3 a7-b6 d2-e3 g5-h4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 e7-d6 c5xe7 f8xd6 a1-b2 d6-c5 c3-d4 c7-d6 d4xb6 a7xc5 d2-c3 c5-b4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 e7-d6 c5xe7 f8xd6 a1-b2 d6-c5 c3-d4 c7-d6 d4xb6 a7xc5 d2-c3 g5-h4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 a1-b2 f6-g5 c3-d4 c7-b6 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 c3-d4 f6-g5 a1-b2 c7-b6 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 e7-d6 d2-c3 h8-g7 c1-b2 f8-e7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 f4-g5 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 f6-e5 g5-h6 b8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 f4-g5 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 f6-e5 g5-h6 h8-g7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 f6-g5 c3-d4 c7-b6 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6 d2-c3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 b4-a3 d2-c3 f8-g7 h2-g3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 b8-c7 c1-d2 f6-e5 g5-h6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 d8-c7 c1-d2 h8-g7 g5-h6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 h8-g7 a1-b2 e7-d6 c5xe7 f8xd6 f2-g3 a5-b4 c3xa5 c7-b6 a5xe5 f6xh4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 h8-g7 a1-b2 g5-h4 f4-g5 h6xf4 e3xg5 h4-g3 f2xh4 g7-h6 g1-f2 h6xf4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 c7-b6 d2-e3 b8-c7 g3-f4 g7-f6 c1-d2 h8-g7 d4-e5 f6xd4 c5-d6 c7xg3 f2xh8 d4xf2",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 d2-e3 h6-g5 g3-f4 g7-h6 e1-d2 c7-b6 d2-c3 e7-d6 c5xe7 f8xd6 d4-e5 b8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 d2-e3 h6-g5 g3-f4 g7-h6 h2-g3 c7-b6 b2-c3 d8-c7 c1-b2 c7-d6 c3-b4 a5xe5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 d2-e3 h6-g5 g7-h6 e1-d2 c7-b6 d2-c3 e7-d6 c5xe7 f8xd6 d4-e5 b8-c7 b2-a3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 d2-e3 h6-g5 g7-h6 h2-g3 c7-b6 b2-c3 d8-c7 c1-b2 c7-d6 c3-b4 a5xe5 b2-a3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g3-f4 g7-f6 c7-b6 e1-d2 f6-g5 h2-g3 d8-c7 d2-c3 c7-d6 c3-b4 a5xe5 b2-a3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g3-f4 g7-f6 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 b4-a3 b2-c3 e7-d6 c3-d4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g3-f4 g7-f6 h6xf4 f2-g3 h4xf2 e1xg7 h8xf6 d2-e3 f6-e5 d4xf6 e7xg5 g1-f2",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g7-f6 d2-e3 g5-h4 f6-e5 f4xd6 c7xc3 b2xd4 h8-g7 h2-g3 e7-d6 c5xe7 f8xd6 g3-f4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 c7-b6 h2-g3 b6xd4 e3xc5 g5xe3 f2xd4 e7-d6 c5xe7 f8xd6 b2-c3 g7-f6 a1-b2 a7-b6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 c7-b6 h2-g3 b6xd4 e3xc5 g5xe3 f2xd4 e7-d6 c5xe7 f8xd6 d4-c5 d6xb4 b2-a3 b4-c3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 c7-b6 h2-g3 b6xd4 e3xc5 g5xe3 f2xd4 g7-f6 g3-f4 f6-g5 d2-e3 h8-g7 g1-f2 e7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 e7-d6 d2-c3 b4xd2",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 f6-g5 b2-a3 h8-g7 c3-d4 a5-b4 c5-b6 a7xc5 d4xb6 c7xa5 a3xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 e7-d6 d2-c3 b4xd2 e1xc3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 b8-c7 b4-a5 d6xb4 a5xc3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 f6-e5 g5-h6 b8-c7 b4-a5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 h6xf4 e3xg5 f6-e5 g5-h6 c7-b6 a1-b2 b6xd4 d2-e3 b8-c7 e3xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 e3-d4 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 c7-b6 d2-e3 e7-d6 c5xe7 f8xd6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 e3-d4 e7-f6 d2-e3 c7-b6 c1-d2 f6-g5 h2-g3 d8-e7 d2-c3 e7-d6 c5xe7 f8xd6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 h2-g3 g7-f6 b2-c3 f6-g5 c3-b4 a5xc3 d2xb4 c7-b6 a1-b2 b6xd4 e3xc5 g5xe3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 h2-g3 g7-f6 b2-c3 h8-g7 c3-b4 a5xc3 d2xb4 f6-e5 f4xd6 c7xe5 e3-f4 d8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 h2-g3 g7-f6 b2-c3 h8-g7 c3-b4 a5xc3 d2xb4 f6-e5 f4xd6 c7xe5 e3-f4 e7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 c7-d6 a5xc3 d2xb4 g5-h4 a1-b2 d6-e5 f4xd6 a7-b6 c5xa7 e7xa3 h2-g3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 c7-d6 a5xc3 d2xb4 g5-h4 a1-b2 f6-g5 b2-a3 h8-g7 h2-g3 b8-c7 e3-d4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 c7-d6 a5xc3 d2xb4 g5-h4 a1-b2 f6-g5 b2-c3 d8-c7 h2-g3 h8-g7 e3-d4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 c7-d6 c3-b4 a5xc3 d2xb4 g5-h4 a1-b2 d6-e5 f4xd6 a7-b6 c5xa7 e7xa3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 c7-d6 c3-b4 a5xc3 d2xb4 g5-h4 a1-b2 f6-g5 b2-a3 h8-g7 h2-g3 b8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 c7-d6 c3-b4 a5xc3 d2xb4 g5-h4 a1-b2 f6-g5 b2-c3 d8-c7 h2-g3 h8-g7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 c3-d4 c7-b6 f4-e5 d8-c7 b2-a3 f8-g7 a3-b4 a5xc3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 c3-d4 c7-b6 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 c3-d4 f6-e5 d4xf6 e7xg5 a1-b2 h8-g7 d2-c3 d8-e7 c5-b6 a7xc5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 c3-d4 f6-g5 a1-b2 c7-b6 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 b4-a3 a1-b2 e7-d6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 e7-d6 a1-b2 f8-g7 d2-c3 b8-a7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 c7-b6 a1-b2 b6xd4 d2-e3 b8-c7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 c7-d6 c3-b4 a5xc3 d2xb4 h8-g7",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 h8-g7 c5-d6 e7xc5 c3-b4 c5xa3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f6-e5 d4xf6 e7xg5 a1-b2 h8-g7 d2-c3 d8-e7 c5-b6 a7xc5 c3-b4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f6-g5 a1-b2 c7-b6 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6 d2-c3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f6-g5 c3-d4 c7-b6 f4-e5 d8-c7 b2-a3 f8-g7 a3-b4 a5xc3 d2xb4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f6-g5 c3-d4 c7-b6 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6 d2-c3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 b4-a3 a1-b2 e7-d6 b2-c3",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f6-g5 c5-b6 a7xc5 d4xb6 e7-d6 a1-b2 f8-g7 d2-c3 b8-a7 c3-d4",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 h6xf4 e3xg5 f6-e5 g5-h6 c7-d6 c3-b4 a5xc3 d2xb4 h8-g7 a1-b2",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 h6xf4 e3xg5 f6-e5 g5-h6 h8-g7 c5-d6 e7xc5 c3-b4 c5xa3 c1-b2",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 h8-g7 c3-d4 g5-h4 a1-b2 f6-g5 b2-a3 a5-b4 c5-b6 a7xc5 d4xb6 c7xa5",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 e3-d4 g5xe3 d2xf4 f6-g5 f2-e3 h8-g7 g1-f2 g5-h4 f2-g3 h4xf2 e1xg3 g7-f6",
        "c3-d4 b6-a5 d4-c5 d6xb4 a3xc5 h6-g5 g3-f4 g7-h6 b2-c3 h8-g7 a1-b2 c7-d6 b2-a3 d6xb4 a3xc5 g5-h4 c3-d4 f6-g5 d2-c3 e7-d6",
        "c3-d4 b6-a5 d4-c5 h8-g7 b2-c3 f6-g5 a1-b2 c7-b6 g7-f6 f2-g3 f6-g5 h2-g3 g5-h4 c3-d4 e7-f6 b2-c3 f6-g5 g3-h4 f8-e7 d4-e5",
        "c3-d4 b6-a5 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 c7-d6 b2-a3 d6xb4 a3xc5 d8-c7 c1-b2 c7-d6",
        "c3-d4 b6-a5 e3-f4 a7-b6 d4-e5 f4-g5 g7-f6 d6-e5 b2-c3 c7-d6 f2-e3 d6-c5 c3-b4 a5-b4 d6-e7 a1-b2 b6-a5 e3-f4 d8-c7 b2-c3",
        "c3-d4 b6-a5 e3-f4 c7-b6 d2-c3 b6-c5 c3-d4 d6-e5 d8-e7 g3-f4 f6-g5 h2-g3 g7-f6 b2-c3 f8-e7 e1-f2 f6-e5 a1-b2 e7-f6 f2-e3",
        "c3-d4 b6-a5 e3-f4 c7-b6 f2-e3 d6-c5 a3-b4 a5xe5 f4xb4 e7-d6 b6-a5 b2-a3 a5xc3 d2xb4 f6-g5 b4-c5 d6xb4 a3xc5 g5-h4 e3-d4",
        "c3-d4 b6-a5 e3-f4 c7-b6 f2-e3 d6-c5 a3-b4 a5xe5 f4xb4 f6-g5 g7-f6 b4-a5 g5-h4 a5xc7 b8xd6 b2-c3 f6-g5 c3-d4 e7-f6 g3-f4",
        "c3-d4 b6-a5 e3-f4 e7-f6 d4-e5 f6xd4 f4-g5 h6xf4 g3xc3 g7-f6 h2-g3 h8-g7 g3-f4 c7-b6 f4-g5 d8-e7 g5-h6 b6-c5 c3-b4 a5xc3",
        "c3-d4 b6-a5 e3-f4 f6-g5 d4-c5 g5xe3 f2xd4 d6xb4 a3xc5 g7-f6 d2-e3 f6-g5 g3-f4 h8-g7 h2-g3 g5-h4 g1-h2 h4xf2 e3xg1 g7-f6",
        "c3-d4 b6-a5 e3-f4 f6-g5 f2-e3 a5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 b8-c7 b2-c3 c7-b6 c3-d4 b6-a5",
        "c3-d4 b6-a5 e3-f4 f6-g5 f2-e3 a5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 b8-c7 e3-d4 g5xe3 d4xf2 g7-f6",
        "c3-d4 b6-a5 g3-f4 c7-b6 b2-c3 f6-g5 d4-e5 d6-c5 c3-d4 g5-h4 a1-b2 b8-c7 a3-b4 a5xa1 c1-b2 a1xc3 d2xb8 d8-c7 b8xd6 e7xc5",
        "c3-d4 b6-a5 g3-f4 c7-b6 b2-c3 f6-g5 d4-e5 d6-c5 c3-d4 g5-h4 a1-b2 b8-c7 b2-c3 e7-d6 h2-g3 h6-g5 f4xh6 d6xh2 c3-b4 a5xe5",
        "c3-d4 b6-a5 g3-f4 f6-e5 d4xf6 g7xg3 h2xf4 a7-b6 f4-g5 h6xf4 e3xg5 b6-c5 g5-h6 h8-g7 f2-g3 g7-f6 g3-h4 d6-e5 b2-c3 c7-d6",
        "c3-d4 b6-a5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 d4-c5 d6xb4 a3xc5 f6-g5 c3-d4 c7-b6 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6",
        "c3-d4 b6-a5 g3-f4 f6-g5 h8-g7 d4-e5 e7-d6 d8-e7 f2-g3 c7-b6 e3-d4 g7-f6 d4-e5 f4-g5 b8-c7 h2-g3 c7-d6 d2-e3 e7-f6 g3-h4",
        "c3-d4 b6-a5 g3-f4 f6-g5 h8-g7 h2-g3 g7-f6 a7-b6 a1-b2 b6-c5 g1-h2 b8-a7 c3-d4 c7-b6 b2-c3 b6-a5 g3-f4 a7-b6 e1-f2 b6-c5",
        "c3-d4 b6-a5 g3-h4 d6-c5 d4xb6 a5xc7 f2-g3 a7-b6 b2-c3 b6-a5 f4-g5 h6xf4 e3xg5 g7-h6 a1-b2 h6xf4 g3xg7 h8xf6 c3-d4 c7-d6",
        "c3-d4 b6-a5 g3-h4 d6-e5 b2-c3 e5-f4 e3xg5 h6xf4 a1-b2 f6-e5 d4xf6 g7xe5 f2-e3 e7-d6 e3xg5 e5-d4 c3xe5 d6xh6 b2-c3 h8-g7",
        "c3-d4 b6-a5 g3-h4 f6-g5 h4xf6 g7xg3 h2xf4 d6-c5 d4xb6 a5xc7 b2-c3 a7-b6 f2-g3 h8-g7 g3-h4 g7-f6 g1-h2 c7-d6 e1-f2 b8-c7",
        "c3-d4 b6-a5 g3-h4 g7-f6 f2-g3 h8-g7 g1-f2 d6-c5 c7-d6 f4-g5 c3-b4 g7-h6 a1-b2 f6-e5 b2-c3 e5-f4 h4-g5 f2-e3 e7-f6 b4-a5",
        "c3-d4 b6-c5 b2-c3 a7-b6 g3-h4 f6-g5 h8-g7 c3-d4 d6-c5 d2-c3 g7-f6 c1-b2 f6-g5 d4-e5 g5-h4 c3-d4 e7-d6 e5-f6 d6-e5 b6-c5",
        "c3-d4 b6-c5 b2-c3 c5-b4 c3-d4 f6-g5 g7-h6 d4-e5 g5-h4 a1-b2 c7-b6 d2-c3 b6-c5 c3-d4 b8-a7 b2-c3 d8-c7 c1-b2 e7-d6 c3-d4",
        "c3-d4 b6-c5 b2-c3 c5-b4 e3-d4 b4-a3 c7-d6 c3-b4 d6-e5 g3-f4 f6-g5 b4-a5 e7-f6 e1-d2 f6-e5 a5-b6 b8-a7 g1-h2 e5-f4 d2-c3",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 a1-b2 f6-g5 d4-c5 e7-d6 c5xe7 f8xd6 g3-f4 g5xe3 d2xf4 d6-c5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5 e3-f4 e7-f6 c3-b4 c7-b6 f6-g5 a5xc7 d8xb6 a1-b2 g5xe3 f2xf6 g7xe5 d2-e3 f8-e7 e3-f4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5 e3-f4 e7-f6 c3-b4 c7-b6 f6-g5 a5xc7 d8xb6 f2-e3 e5-d4 f4-e5 d4xh4 e5xa5 f8-e7 a1-b2",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-e5 e3-f4 g7-f6 c3-b4 f6-g5 b4-a5 g5xe3 f2xb6 b8-a7 g3-f4 e5xg3 h2xf4 a7xc5 d2-e3 h8-g7",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 a1-b2 g5-h4 c3-d4 c5-b4 a3xc5 d6xb4 g3-f4 b4-a3 d4-c5 g7-f6 b2-c3 f6-g5 e3-d4 g5xe3",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-b4 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4xd6 c7xe5 d2-e3 f4xd2 c1xe3 d8-c7 a1-b2 e7-d6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-b4 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 b8-a7 a1-b2 f6-e5 g5-h6 f8-g7 h6xf8 h8-g7",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-b4 g5-h4 g3-f4 g7-f6 h6xf4 e3xg5 b8-a7 a1-b2 f6-e5 g5-h6 f8-g7 h6xf8 h8-g7 f8xh6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 b8-a7 b2-c3 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 g5-h4 g3-f4 b8-a7 b2-c3 g7-f6 f4-g5 h6xf4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 d4-c5 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 b8-a7",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 g3-f4 g5-h4 d4-c5 b8-a7 b2-c3 g7-f6 f4-g5 h6xf4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 g3-f4 g5-h4 d4-c5 g7-f6 f4-g5 h6xf4 e3xg5 b8-a7",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 a1-b2 g5-h4 b2-a3 c7-d6 a3xc5 d6xb4 g3-f4 d8-c7 d2-c3 b4xd2",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 b4-a3 d4-c5 b8-a7 b2-c3 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 b4-a3 d4-c5 g5-h4 g3-f4 b8-a7 b2-c3 g7-f6 f4-g5 h6xf4 e3xg5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 b4-a3 d4-c5 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 b8-a7 b2-c3",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 b4-a3 g3-f4 g5-h4 d4-c5 b8-a7 b2-c3 g7-f6 f4-g5 h6xf4 e3xg5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 b4-a3 g3-f4 g5-h4 d4-c5 g7-f6 f4-g5 h6xf4 e3xg5 b8-a7 b2-c3",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 c3-d4 c5-b4 a3xc5 d6xb4 g5-h4 b2-a3 c7-d6 a3xc5 d6xb4 g3-f4 d8-c7 d2-c3 b4xd2 e1xc3",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g5-h4 a1-b2 g7-f6 c3-d4 f6-g5 d4xb6 c7xa5 b2-c3 h8-g7 c3-d4 d8-c7 d2-c3 e7-f6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g5-h4 a1-b2 g7-f6 c3-d4 f6-g5 d4xb6 c7xa5 b2-c3 h8-g7 c3-d4 d8-c7 d4-e5 d6-c5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g5-h4 a1-b2 g7-f6 f6-g5 d4xb6 c7xa5 b2-c3 h8-g7 c3-d4 d8-c7 d2-c3 e7-f6 c1-b2",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g5-h4 a1-b2 g7-f6 f6-g5 d4xb6 c7xa5 b2-c3 h8-g7 c3-d4 d8-c7 d4-e5 d6-c5 a3-b4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 b8-a7 a1-b2 f8-g7 h6xf8 h8-g7",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 h8-g7 b4-a5 g7-f6 a1-b2 b8-a7",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 h6xf4 e3xg5 f6-e5 g5-h6 b8-a7 a1-b2 f8-g7 h6xf8 h8-g7 f8xh6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 h8-g7 b2-c3 f6-g5 b4-a5 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 d4-c5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g5-h4 c3-d4 g7-f6 d4xb6 c7xa5 a1-b2 f6-g5 b2-c3 h8-g7 c3-d4 d8-c7 d2-c3 e7-f6",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g7-f6 c3-b4 g5-h4 a1-b2 h8-g7 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 g7-f6 d2-e3 e5-d4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g7-f6 c3-b4 g5-h4 h8-g7 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 g7-f6 d2-e3 e5-d4 h2-g3",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g7-f6 c3-b4 h8-g7 b4-a5 g5-h4 a1-b2 f6-e5 h2-g3 b8-a7 b2-c3 h6-g5 f4xh6 e5-d4",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-f4 g7-f6 c3-b4 h8-g7 g5-h4 a1-b2 f6-e5 h2-g3 b8-a7 b2-c3 h6-g5 f4xh6 e5-d4 c3xe5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 c3-b4 d6-e5 b4xd6 e7xc5 a1-b2 f8-e7 d2-c3 e7-f6 c3-b4 f6-g5",
        "c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 d6-e5 b4xd6 e7xc5 a1-b2 f8-e7 d2-c3 e7-f6 c3-b4 f6-g5 h4xb6",
        "c3-d4 b6-c5 d4xb6 a7xc5 d2-c3 g5-h4 c3-d4 c7-b6 b2-c3 b6-a5 d4xb6 a5xc7 a3-b4 e7-d6 a1-b2 f6-e5 b2-a3 e5-f4 g3xe5 d6xd2",
        "c3-d4 b6-c5 d4xb6 a7xc5 e3-d4 c5xe3 f2xd4 d6-e5 c1-d2 e5xc3 b2xd4 h6-g5 d2-e3 g5-h4 a3-b4 h4xf2 e1xg3 e7-d6 d4-c5 g7-h6",
        "c3-d4 b6-c5 d4xb6 c7xa5 b2-c3 f6-e5 e3-f4 g7-f6 f2-e3 a7-b6 c1-b2 f8-g7 g1-f2 b8-c7 e3-d4 b6-c5 d4xb6 f6-g5 f2-e3 e5-d4",
        "c3-d4 b6-c5 d4xb6 c7xa5 b2-c3 f6-e5 e3-f4 g7-f6 f2-e3 a7-b6 f8-g7 g1-f2 b8-c7 e3-d4 b6-c5 d4xb6 f6-g5 f2-e3 e5-d4 c3xe5",
        "c3-d4 b6-c5 d4xb6 c7xa5 e3-d4 d6-c5 d4xb6 a5xc7 b2-c3 e7-d6 a3-b4 a7-b6 b4-a5 f6-e5 g3-h4 b6-c5 a1-b2 c5-b4 b2-a3 f8-e7",
        "c3-d4 b6-c5 d4xb6 c7xa5 e3-d4 d6-c5 d4xb6 a5xc7 d2-e3 e7-d6 b2-c3 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 c1-d2 h8-g7 f2-g3 f6-g5",
        "c3-d4 b6-c5 g3-f4 f6-g5 b2-c3 c5-b4 f8-e7 d4-e5 b4-a3 e5-f6 g5-h4 f4-g5 d6-e5 a1-b2 c7-d6 b2-c3 h8-g7 h2-g3 g7-h6 g3-h4",
        "c3-d4 b6-c5 g3-h4 d6-e5 e3-d4 c7-d6 f2-e3 f6-e5 b2-c3 g7-f6 e3-f4 d8-e7 c1-d2 h8-g7 c3-b4 b8-c7 a1-b2 g7-h6 b2-c3 c5-d4",
        "c3-d4 d2-c3 c3-b4 b4-a5 d6-c5 f6-g5 c7-d6 b8-c7 g3-f4 e1-d2 b2-c3 h2-g3 g5-h4 g7-f6 f8-g7 f6-e5 d4xf6 c3-b4 g1-h2 f4-g5",
        "c3-d4 d2-c3 c3-b4 b4xd6 d6-c5 h6-g5 g5-f4 c7xc3 e3xg5 b2xd4 g3-f4 d4xf6 f6xh4 g7-f6 f6-e5 e7xe3 f2xd4 a1-b2 b2-c3 c1-d2",
        "c3-d4 d2-c3 e3-f4 c1-d2 d6-e5 e7-d6 b6-a5 c7-b6 f2-e3 d4xb6 e3-d4 d4-c5 b6-c5 a5xc7 c7-b6 b6xd4 g3-h4 c3xc7 h4xf2 h2-g3",
        "c3-d4 d2-c3 g3-f4 c3-b4 d6-c5 h6-g5 g5-h4 f6-e5 d4xf6 b4xd6 h2xf4 b2-c3 g7xg3 e7xc5 c7-d6 b6-a5 c1-b2 c3-d4 d4xb6 b2-c3",
        "c3-d4 d4-c5 a3xc5 e3xc5 f6-g5 d6xb4 b6xd4 c7-b6 d2-e3 e3xc5 b2-c3 a1-b2 b6xd4 g5-h4 h6-g5 g7-f6 c3-d4 c5xe7 b2-c3 d4xf6",
        "c3-d4 d4-c5 a3xc5 e3xc5 f6-g5 d6xb4 b6xd4 e7-f6 d2-e3 e3-d4 b2xd4 a1-b2 f6-e5 e5xc3 g7-f6 g5-h4 b2-a3 c1-d2 d2-e3 g3-f4",
        "c3-d4 d4-c5 a3xc5 e3xc5 f6-g5 d6xb4 b6xd4 e7-f6 f2-e3 g1-f2 b2-c3 a1-b2 g5-h4 f6-g5 g7-f6 f6-e5 c5-d6 e3xg5 c3-b4 b2-c3",
        "c3-d4 d4-c5 a3xc5 e3xc5 f6-g5 d6xb4 b6xd4 g5-f4 g3xe5 c5-d6 h2-g3 g3-f4 c7-b6 e7xc5 c5-b4 b4-a3 b2-c3 g1-h2 f2-g3 e5xg7",
        "c3-d4 d4-c5 a3xc5 e3xc5 f6-g5 d6xb4 b6xd4 g5-f4 g3xe5 c5-d6 h2-g3 g3-f4 c7-b6 e7xc5 c5-b4 f8-e7 b2-c3 f2-e3 g1-f2 f2-g3",
        "c3-d4 d4-c5 a3xc5 e3xc5 f6-g5 d6xb4 b6xd4 g5-h4 b2-c3 a1-b2 c3-b4 d2-e3 g7-f6 f6-g5 h8-g7 g7-f6 e3-d4 c5xe7 b4-a5 b2-c3",
        "c3-d4 d4-c5 a3xc5 g3-f4 b6-a5 d6xb4 f6-e5 e5xg3 h2xf4 e3-d4 f2-g3 d2xf4 g7-f6 f6-g5 g5xe3 h8-g7 g1-f2 f2-e3 g3-h4 h4xf6",
        "c3-d4 d4-c5 e3xc5 a3xc5 f6-g5 b6xd4 d6xb4 g5-f4 g3xe5 c5-d6 h2-g3 e5-d6 c7-b6 e7xc5 d8-e7 c5-d4 d2-c3 c3xe5 b2-c3 e1xc3",
        "c3-d4 d4-c5 e3xc5 a3xc5 f6-g5 b6xd4 d6xb4 g5-f4 g3xe5 c5-d6 h2-g3 g3-f4 c7-b6 e7xc5 c5-b4 f8-e7 b2-c3 f2-e3 e5xg7 e3-d4",
        "c3-d4 d4-c5 e3xc5 a3xc5 f6-g5 b6xd4 d6xb4 g5-h4 b2-a3 a1-b2 a3-b4 b2-c3 g7-f6 h8-g7 f6-g5 c7-b6 c3-d4 b4-a5 d2-c3 c3-b4",
        "c3-d4 d4-c5 f6-g5 g5-f4 c5-d6 h2-g3 f2-e3 c7-b6 b6-a5 a7-b6 g1-f2 g3-h4 e3-d4 f2-g3 d8-e7 c5-b4 b4-a3 b8-a7 d2-c3 c3-d4",
        "c3-d4 d4xf6 b2-c3 c3-d4 f6-e5 e7xg5 b6-c5 c7-b6 a3-b4 c1-b2 d2-c3 g3xa5 c5xa3 a3xc1 c1xf4 g5-h4 h2-g3 a1-b2 f2-e3 e1xg3",
        "c3-d4 d6-c5 a1-b2 c7-d6 b2-c3 b6-a5 d6-e5 f2-g3 h6-g5 a3-b4 g7-h6 b4-a5 c7-b6 d2-e3 a7-b6 c1-b2 d6-c5 g3-f4 e7-d6 b2-a3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 a1-b2 f6-e5 e5-f4 h2-g3 f6-e5 g3-h4 a7-b6 b2-c3 e5-f4 h4-g5 f4-e3 d6-c5 e1-f2 g7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 c1-d2 g7-f6 b2-c3 h8-g7 b4-a5 d8-c7 e3-f4 f6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 e1-d2 b8-a7 b4-a5 a7-b6 a5xc7 d6xb8 b2-c3 c5-d4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 e1-d2 b8-a7 b4-a5 a7-b6 a5xc7 d6xb8 e3-f4 e7-d6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 e1-d2 d8-c7 e3-f4 g7-f6 f2-e3 e5-d4 g1-f2 h6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 e1-d2 g7-f6 b2-c3 h8-g7 e3-d4 c5xe3 f2xd4 h6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 e3-f4 c5-d4 b4-a5 e7-f6 a3-b4 h6-g5 f4xh6 d4-e3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 e3-f4 c5-d4 e1-d2 e7-f6 d2-e3 h6-g5 e3xe7 g5xe3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 e3-f4 c5-d4 g3-h4 e5xg3 h2xf4 d6-e5 f4xd6 e7xc5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 f6-e5 f2-g3 h6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 a1-b2 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 c1-d2 f6-g5 b2-c3 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 c1-d2 g7-f6 b2-c3 h8-g7 b4-a5 d8-c7 e3-f4 f6-g5 g3-h4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 e1-d2 b8-a7 b4-a5 a7-b6 a5xc7 d6xb8 b2-c3 c5-d4 e3xc5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 e1-d2 b8-a7 b4-a5 a7-b6 a5xc7 d6xb8 e3-f4 e7-d6 f2-e3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 e1-d2 d8-c7 e3-f4 g7-f6 f2-e3 e5-d4 g1-f2 h6-g5 f4xh6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 e1-d2 g7-f6 b2-c3 b8-a7 e3-d4 c5xe3 f2xd4 h6-g5 g3-h4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 e3-f4 c5-d4 b4-a5 e7-f6 a3-b4 h6-g5 f4xh6 d4-e3 f2xd4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 e3-f4 c5-d4 b4-a5 e7-f6 g3-h4 e5xg3 h2xf4 d6-e5 f4xd6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 e3-f4 c5-d4 e1-d2 e7-f6 d2-e3 h6-g5 e3xe7 g5xe3 e7xg5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 e3-f4 c5-d4 g3-h4 e5xg3 h2xf4 d6-e5 f4xd6 e7xc5 b4xd6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 f6-e5 f2-g3 h6-g5 f4xh6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 c1-d2 f6-g5 b2-c3 h8-g7 f2-g3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 a7xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 f2-g3 f6-e5 g3-h4 e5xg3 h4xf2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 b4-a5 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-d4 e7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f6-e5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 b6xd4 e3xc5 d6xb4 a3xc5 h6-g5 f2-e3 g5-f4 e3xg5 f6xf2 g1xe3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 d6-e5 e3-f4 e7-d6 b2-c3 f6-g5 d2-e3 g5-h4 e3-d4 f8-e7 d4xf6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 f6-g5 b2-c3 e7-f6 b4-a5 f6-e5 f2-g3 g5-h4 e3-d4 h4xf2 e1xg3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 c7-b6 f6-g5 c3-d4 d6-c5 b4xd6 e7xc5 d2-c3 g5-h4 c1-d2 g7-f6 c3-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 d6-e5 e5xg3 h2xf4 f6-e5 f4xd6 c7xe5 f2-g3 g7-f6 b2-c3 h8-g7 e3-d4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 d6-e5 e5xg3 h2xf4 f6-e5 f4xd6 c7xe5 f2-g3 g7-f6 b4-a5 h8-g7 e1-f2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 d6-e5 g3-f4 e5xg3 h2xf4 f6-e5 f4xd6 c7xe5 f2-g3 g7-f6 b2-c3 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 a7-b6 b4-a5 e7-f6 c3-b4 f6-g5 b4-c5 b6xd4 e3xe7 f8xd6 a3-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 a7-b6 b4-a5 e7-f6 g3-f4 e5xg3 h2xf4 f8-e7 f2-g3 f6-g5 c3-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 a7-b6 e3-d4 b6-a5 d4xf6 g7xe5 b4-c5 d6xb4 a3xc5 c7-d6 c3-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 a7-b6 f2-e3 b6-c5 g3-h4 e5xg3 h2xf4 g7-f6 f4-g5 h6xf4 e3xg5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 b2-c3 a7-b6 e3-f4 e7-f6 b4-a5 h6-g5 f4xh6 e5-f4 g3xe5 f6xb2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-d4 e7-f6 b4-a5 f8-e7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-d4 g7-h6 f2-g3 e7-d6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 d2-c3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 f2-g3 a7-b6 g3xe5 b6-a5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-d4 a7-b6 b4-a5 e7-f6 a3-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-d4 a7-b6 f2-g3 e7-d6 g3xe5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-d4 g7-h6 f2-g3 e7-d6 g3xe5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 b2-c3 g5-h4 b4-c5 d6xb4 c3xa5 g7-f6 d2-c3 f6-g5 c3-d4 e7-d6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 b2-c3 g5-h4 c3-d4 d6-e5 d4xf6 g7xe5 g3-f4 e5xg3 h2xf4 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 b2-c3 g7-f6 b4-a5 g5-h4 c3-b4 f6-g5 b4-c5 d6xb4 a5xc3 a7-b6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 b4-c5 d6xb4 a3xc5 g7-f6 b2-c3 g5-h4 g3-f4 f6-g5 e3-d4 g5xe3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 d6xb4 a3xc5 g7-f6 g3-f4 f6-e5 f4xd6 c7xe5 e3-f4 e5xg3 f2xf6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 b4-a5 g5-f4 g3xe5 d6xf4 e3xg5 f6xh4 b2-c3 g7-f6 c3-d4 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 a7-b6 b4-a5 f6-e5 f2-g3 g5-h4 e3-d4 h4xf2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 a7-b6 b4-a5 h8-g7 h2-g3 g5-h4 c3-d4 d6-e5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 f6-e5 h2-g3 g5-h4 b4-c5 d6xb4 f4xd6 e7xc5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 a7-b6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 h8-g7 b4-a5 c7-b6 a5xe5 f6xb2 a3-b4 b2-a1",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 h8-g7 b4-c5 d6xb4 a3xc5 c7-d6 c3-d4 d6xb4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 e3-d4 f6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b2-c3 h8-g7 b4-c5 d6xb4 c3xa5 c7-d6 h2-g3 g5-h4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b4-c5 d6xb4 a3xc5 g5-h4 d2-c3 f6-g5 b2-a3 c7-b6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b4-c5 d6xb4 a3xc5 g5-h4 d2-c3 f6-g5 b2-a3 e7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b4-c5 d6xb4 a3xc5 g5-h4 f4-g5 h6xf4 e3xg5 c7-d6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b4-c5 d6xb4 a3xc5 h8-g7 b2-c3 c7-d6 c3-b4 d6-e5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b4-c5 d6xb4 a3xc5 h8-g7 b2-c3 g5-h4 e3-d4 f6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b4-c5 d6xb4 a3xc5 h8-g7 b2-c3 g5-h4 f4-g5 h6xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-f4 g7-h6 b4-c5 d6xb4 a3xc5 h8-g7 d2-c3 g5-h4 b2-a3 f6-g5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g3-h4 g3-f4 f6-e5 h4xd4 d6-c5 d4xb6 c7xa1 a1-b2 f6-e5 e3-f4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-f4 e3xg5 f6xh4 b4-a5 g7-f6 c3-b4 d6-e5 d2-e3 a7-b6 e3-f4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-f4 e3xg5 f6xh4 b4-c5 d6xb4 c3xa5 e7-d6 d2-e3 a7-b6 c1-b2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-f4 e3xg5 f6xh4 c3-d4 g7-f6 d4-c5 h8-g7 b4-a5 d6xb4 a5xc3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-f4 g3xe5 d6xf4 e3xg5 f6xh4 b2-c3 e7-d6 d2-e3 g7-f6 c3-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-f4 g3xe5 d6xf4 e3xg5 f6xh4 b2-c3 g7-f6 c3-d4 f8-g7 d2-c3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-h4 a3-b4 d6-e5 b2-a3 e7-d6 b4-c5 d6xb4 a5xc3 a7-b6 g3-f4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-h4 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 e3-d4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-h4 b4-c5 d6xb4 a3xc5 g7-h6 b2-c3 f6-g5 e3-d4 g5xe3 d2xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-h4 b4-c5 d6xb4 a3xc5 g7-h6 d2-c3 f6-g5 b2-a3 h8-g7 c3-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-h4 b4-c5 d6xb4 c3xa5 g7-h6 a3-b4 h8-g7 e3-d4 f6-g5 d2-e3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g5-h4 g3-f4 g7-h6 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 h8-g7 b4-a5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b2-c3 a7-b6 b4-a5 f6-e5 f2-g3 g5-h4 e3-d4 h4xf2 e1xg3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b2-c3 a7-b6 b4-a5 h8-g7 h2-g3 g5-h4 c3-d4 d6-e5 f4xd6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b2-c3 h8-g7 b4-a5 c7-b6 a5xe5 f6xb2 a3-b4 b2-a1 d2-c3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b4-a5 g5-h4 c3-b4 d6-c5 b4xd6 e7xc5 g3-f4 f8-e7 d2-c3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b4-c5 d6xb4 a3xc5 g5-h4 b2-c3 f6-g5 e3-d4 g5xe3 d2xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b4-c5 d6xb4 a3xc5 g5-h4 b2-c3 h8-g7 e3-d4 f6-g5 f4-e5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b4-c5 d6xb4 a3xc5 g5-h4 d2-c3 f6-g5 b2-a3 c7-b6 c3-d4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b4-c5 d6xb4 a3xc5 h8-g7 b2-c3 c7-d6 c3-d4 d6xb4 d4-e5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b4-c5 d6xb4 a3xc5 h8-g7 b2-c3 g5-h4 c3-d4 f6-g5 d2-c3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b4-c5 d6xb4 a3xc5 h8-g7 d2-c3 g5-h4 b2-a3 f6-g5 c1-b2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b4-c5 d6xb4 a3xc5 h8-g7 d2-c3 g5-h4 b2-a3 f6-g5 e1-d2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 h6-g5 g7-h6 b4-c5 d6xb4 a3xc5 h8-g7 d2-c3 g5-h4 c3-d4 f6-g5 b2-a3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5 f6-e5 a1-b2 a7-b6 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-d4 e7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5 f6-g5 d2-c3 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 c3-d4 e7-f6 f2-g3 f6-e5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5 f6-g5 e3-d4 g5-f4 g3xe5 d6xf4 f2-g3 e7-f6 g3xe5 c7-b6 a5xc7 b8xf4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-e5 d2-c3 c7-b6 c1-b2 b6xd4 e3xc5 h6-g5 c5-b6 a7xc5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-e5 d2-c3 g7-f6 g3-f4 e5xg3 h2xf4 f6-g5 c3-b4 c7-b6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 d2-c3 f6-e5 f4xd6 c7xe5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 h6-g5 a1-b2 g5-f4 e3xg5 f6xh4 g3-f4 g7-f6 b2-c3 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-e5 a1-b2 a7-b6 b4-a5 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 c3-d4 g7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-e5 a7-b6 b4-a5 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 f2-g3 b6-c5 g3xe5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-e5 c1-d2 a7-b6 e3-d4 b6-a5 d4xf6 g7xe5 b4-c5 d6xb4 a3xc5 e5-f4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5 d6-c5 d4xb6 c7xc3 c1-b2 a7-b6 b2xd4 b6-a5 a1-b2 g5-h4 g3-f4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5 g5-h4 d4-c5 g7-f6 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 b6-a5 c1-b2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5 g7-f6 b4-c5 d6xb4 c3xa5 g5-h4 e3-d4 f6-e5 d4xf6 e7xg5 a1-b2",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5 g7-f6 b4-c5 d6xb4 c3xa5 g5-h4 e3-d4 f6-g5 d2-e3 g5-f4 e3xg5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5 g7-f6 c1-d2 a7-b6 b4-a5 f6-e5 a1-b2 e5xg3 f2xf6 e7xg5 c3-d4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 f6-g5 g7-f6 d4-c5 g5-h4 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 h8-g7 b4-c5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 d2-c3 h6-g5 d6-e5 b4-a5 a7-b6 c1-d2 b6-c5 c3-d4 e5xc3 d2xd6 c7xe5 a3-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 d6-c5 d4xb6 c7xc3 d2xb4 a7-b6 b4-a5 b6-c5 g3-f4 e7-d6 a1-b2 f8-e7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 d6-e5 d2-c3 h6-g5 b4-a5 g5-h4 a3-b4 g7-h6 c1-d2 h6-g5 d2-e3 c7-d6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 a7-b6 a1-b2 h6-g5 h4xd4 b6-c5 d4xb6 c7xa1",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 a7-b6 b4-a5 b6-c5 a1-b2 e7-f6 d2-e3 f8-e7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 a7-b6 b4-a5 b6-c5 a1-b2 h8-g7 b2-c3 c5-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 a7-b6 b4-a5 h8-g7 a1-b2 b6-c5 b2-c3 c5-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 a7-b6 b4-a5 h8-g7 a1-b2 b6-c5 f2-g3 g7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 a7-b6 b4-a5 h8-g7 a1-b2 g7-f6 b2-c3 b6-c5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 h8-g7 a1-b2 g7-f6 b4-a5 e5-f4 a3-b4 d6-e5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 h6-g5 b4-a5 g5-f4 g3xe5 d6xf4 a3-b4 f6-e5 d4xf6 g7xe5 f2-e3 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 h6-g5 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 g7-h6 b2-a3 f6-g5 g3-f4 g5xe3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 h6-g5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 g7-h6 f4-e5 e7-d6 c5xg5 h6xd6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 h6-g5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 g7-h6 f4-e5 h8-g7 a1-b2 e7-d6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 e3-d4 h6-g5 d6xb4 a3xc5 g5-h4 a1-b2 g7-h6 b2-a3 f6-g5 d2-e3 c7-b6 g3-f4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 g3-f4 a7-b6 f6-g5 b2-c3 g7-f6 b4-a5 g5-h4 c3-d4 f6-e5 d4xf6 e7xg5 d2-c3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 g3-f4 f6-e5 a7-b6 b4-a5 g7-f6 a1-b2 f6-g5 b2-c3 b6-c5 g3-h4 e5xg3 h4xf6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 g3-f4 f6-e5 f2-g3 a7-b6 b4-a5 g7-f6 a1-b2 f6-g5 b2-c3 b6-c5 g3-h4 e5xg3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 g3-f4 f6-e5 f2-g3 g7-f6 g3-h4 e5xg3 h4xf2 h8-g7 e3-f4 f6-e5 h2-g3 g7-f6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 g3-f4 f6-e5 h2-g3 a7-b6 a1-b2 b6-c5 b4-a5 e7-f6 b2-c3 f6-g5 e3-d4 g5xe3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 g3-f4 f6-g5 a1-b2 g7-f6 b4-c5 d6xb4 a3xc5 g5-h4 d2-c3 f6-g5 b2-a3 c7-b6",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 g3-f4 f6-g5 d6-e5 f4xd6 c7xe5 b2-c3 e5-f4 b4-a5 g5-h4 e3xg5 h4xf6 c3-d4",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 g3-f4 c5-d4 f6-g5 e1-f2 h8-g7 g7-f6 a1-b2 b8-a7 h2-g3 h6-g5 b2-c3 a7-b6 c1-b2 d6-e5",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 f6-e5 c1-b2 h8-g7 g7-f6 e3-d4 b6-c5 g1-f2 d8-c7 a1-b2 c5-d4 g3-h4 c7-b6 b4-a5 b6-c5 h2-g3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 f6-g5 b4-a5 b8-c7 g3-f4 g5-h4 g7-f6 b2-c3 c5-b4 a3xc5 d6xb4 f4-g5 h6xf4 e3xg5 b4-a3 h2-g3",
        "c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 f6-g5 g3-f4 g7-f6 b4-a5 b8-c7 g5-h4 b2-c3 c5-b4 a3xc5 d6xb4 f4-g5 h6xf4 e3xg5 b4-a3 g5-h6",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 f6-e5 f2-g3 g7-f6 g3-h4 e5xg3 h4xf2 f6-e5 b4-a5 h8-g7 b2-c3",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 a7-b6 g3-h4 e5xg3 h4xf2 h6-g5 c3-d4 g7-f6 h2-g3 g5-h4 d2-c3",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 f2-g3 a7-b6 g3-h4 e5xg3 h4xf2 h6-g5 c3-d4 g7-f6 h2-g3 g5-h4",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 c3-b4 f6-g5 d6-c5 b4xd6 c7xg3 f2xf6 g7xe5 b2-c3 h8-g7 a3-b4 h6-g5 e3-d4",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 a1-b2 g5-h4 c3-d4 g7-f6 b2-c3 f6-g5 h2-g3 e7-d6 d4-e5 f8-e7",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 a1-b2 g5-h4 c3-d4 g7-f6 b2-c3 f6-g5 h2-g3 e7-d6 d4-e5 h8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 a3-b4 c5xa3 c1-b2 a3xc1 a1-b2 c1xa3 c3-b4 a3xg3 f2xd8 a5-b4",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 g5-h4 c3-d4 g7-f6 b2-c3 f6-g5 h2-g3 e7-d6 d4-e5 f8-e7 e5xc7",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 g5-h4 c3-d4 g7-f6 b2-c3 f6-g5 h2-g3 e7-d6 d4-e5 h8-g7 e5xc7",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-f4 f6-g5 d4-e5 b8-c7 a3-b4 c5xa3 e3-d4 g5xc5 c3-b4 d6xf4 b4xb8 b6-c5 b8xg3 g7-f6 g3-b8 e7-d6",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-h4 b6-a5 d4xb6 a5xc7 h2-g3 f6-e5 a7-b6 c3-b4 g7-f6 b4-a5 b6-c5 d2-e3 e5-d4 a1-b2 f8-g7 e1-d2",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-h4 b6-a5 d4xb6 a5xc7 h2-g3 f6-e5 e3-f4 a7-b6 c3-b4 g7-f6 b4-a5 b6-c5 d2-e3 e5-d4 a1-b2 f8-g7",
        "c3-d4 d6-c5 b2-c3 c7-d6 g3-h4 c5-b4 h2-g3 b4-a3 f6-g5 b6-c5 e3-f4 a7-b6 f4-g5 h8-g7 d2-e3 g7-f6 e1-f2 b8-a7 e3-d4 c7-d6",
        "c3-d4 d6-c5 b2-c3 e7-d6 c1-b2 f6-g5 c3-b4 g5-h4 g3-f4 b6-a5 d4xb6 a7xc5 h2-g3 a5xc3 b2xb6 c7xa5 d2-c3 g7-f6 c3-d4 f6-g5",
        "c3-d4 d6-c5 b2-c3 e7-d6 c1-d2 d6-e5 g3-f4 e5xg3 h2xf4 c7-d6 b8-c7 g1-h2 f6-e5 d4xf6 g7xe5 g3-h4 e5xg3 h4xf2 d8-e7 h2-g3",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 a7-b6 d2xb4 b6-c5 a1-b2 f6-e5 b2-c3 d8-c7 g3-f4 e5xg3 h2xf4",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 a7-b6 d2xb4 b6-c5 a1-b2 f6-e5 b2-c3 f8-e7 g3-h4 e5-f4 e3xg5",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c1-d2 d6-e5 d2xb4 f6-g5 g3-f4 e5xg3 f2xf6 g7xe5 h2-g3 a7-b6",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c3-b2 a1xc3 f6-g5 c3-b4 a7-b6 b4-a5 d8-c7 e3-d4 g7-f6 d2-c3",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 f6-g5 d2xb4 d6-e5 g3-f4 e5xg3 f2xf6 g7xe5 e3-f4 e5xg3 h2xf4",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 f6-g5 d2xb4 d6-e5 g3-f4 e5xg3 f2xf6 g7xe5 h2-g3 a7-b6 a1-b2",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 a1-b2 f6-g5 d8-e7 g3-f4 g7-h6 c3-b4 e7-f6 d2-c3 f6-e5 d4xf6 g5xe7 e1-d2",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 d2-c3 d8-e7 g7-h6 a1-b2 f6-g5 g3-f4 e7-f6 b2-c3 f6-e5 d4xf6 g5xe7 c3-d4",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 d2-c3 f6-g5 c3-b4 g7-h6 g3-f4 d8-e7 a1-b2 e7-f6 b2-c3 f6-e5 d4xf6 g5xe7",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 d2-c3 f6-g5 d8-e7 f4xh6 c5-b4 a3xc5 d6xf4 d4-c5 b6xd4 f2-g3 h4xf2 e1xc3",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 d2-c3 f6-g5 g3-f4 d8-e7 f4xh6 c5-b4 a3xc5 d6xf4 d4-c5 b6xd4 f2-g3 h4xf2",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 d2-c3 f6-g5 g7-h6 c3-b4 d8-e7 a1-b2 e7-f6 b2-c3 f6-e5 d4xf6 g5xe7 c3-d4",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g5-h4 g3-f4 f6-e5 d4xf6 g7xg3 h2xf4 f8-e7 a1-b2 h8-g7 d2-c3 c5-b4 a3xc5 d6xd2",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g7-h6 g3-f4 h8-g7 f2-g3 g5-h4 a1-b2 h4xf2 e1xg3 f8-e7 d8-e7 g3-h4 h6-g5 f4xh6",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g7-h6 g3-f4 h8-g7 f2-g3 g5-h4 a1-b2 h4xf2 e1xg3 h6-g5 f4xh6 c5-b4 a3xg5 f8-e7",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g7-h6 g3-f4 h8-g7 f2-g3 g5-h4 c1-b2 h4xf2 e1xg3 h6-g5 f4xh6 c5-b4 a3xg5 f8-e7",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g7-h6 g3-f4 h8-g7 f2-g3 g5-h4 f4-g5 h4xf2 g5xe7 d8xf6 e1xg3 h6-g5 g3-h4 d6-e5",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g7-h6 g3-f4 h8-g7 g5-h4 a1-b2 h4xf2 e1xg3 h6-g5 f4xh6 c5-b4 a3xg5 f8-e7 h6xd6",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g7-h6 g3-f4 h8-g7 g5-h4 c1-b2 h4xf2 e1xg3 h6-g5 f4xh6 c5-b4 a3xg5 f8-e7 h6xd6",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 b4-a5 g7-h6 g3-f4 h8-g7 g5-h4 f4-g5 h4xf2 g5xe7 d8xf6 e1xg3 h6-g5 g3-h4 d6-e5 d2-c3",
        "c3-d4 d6-c5 b2-c3 e7-d6 c3-b4 h6-g5 g3-f4 g7-h6 b4-a5 h8-g7 f8-e7 f2-g3 g5-h4 b2-c3 h4xf2 e1xg3 c5-b4 a3xc5 d6xb4 g3-h4",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-g5 c1-b2 b6-a5 d4xb6 a7xc5 c3-b4 a5xc3 b2xb6 c7xa5 a3-b4 a5xc3 d2xb4 d8-e7 b4-a5 d6-c5",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-g5 c1-b2 b6-a5 d4xb6 a7xc5 c3-b4 a5xc3 b2xb6 c7xa5 a3-b4 a5xc3 d2xb4 g7-f6 b4-c5 d6xb4",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-g5 c1-b2 g5-h4 c3-b4 b6-a5 d4xb6 a7xc5 h2-g3 a5xc3 b2xb6 c7xa5 g1-h2 d6-c5 a1-b2 d8-e7",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-g5 c1-b2 g7-f6 c3-b4 g5-h4 d8-e7 d2-c3 f6-g5 c3-b4 e7-f6 b2-c3 f6-e5 d4xf6 g5xe7 c3-d4",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-g5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c1-b2 g7-f6 b2xd4 d6-c5 d4xb6 a7xc5 a1-b2 f8-e7",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-g5 c3-b4 g7-f6 b4-a5 h8-g7 f8-e7 f2-g3 g5-h4 b2-c3 h4xf2 e1xg3 c5-b4 a3xc5 d6xb4 g3-h4",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-g5 h2-g3 g5-h4 g1-h2 b6-a5 d4xb6 a7xc5 c1-b2 g7-f6 f4-g5 h6xf4 e3xe7 d8xf6 c3-b4 a5xc3",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-f4 f6-g5 h2-g3 g5-h4 g1-h2 f8-e7 b6-a5 d4xb6 a7xc5 c3-d4 c5-b4 a3xc5 d6xb4 b2-c3 b4-a3 c3-b4",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 d6-e5 f2-g3 c7-d6 g3-f4 e5xg3 h4xf2 b6-a5 d4xb6 a5xc7 h2-g3 f6-g5 g3-f4 g7-f6 c3-d4 f8-e7",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 d6-e5 f2-g3 c7-d6 g3-f4 e5xg3 h4xf2 d6-e5 f2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f8-e7 e3-d4 a7-b6",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 d6-e5 f2-g3 c7-d6 g3-f4 e5xg3 h4xf2 f8-e7 c3-b4 b6-a5 d4xb6 a5xc7 h2-g3 a7-b6 a1-b2 h6-g5",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 f8-e7 f2-g3 d6-e5 g3-f4 e5xg3 h4xf2 h6-g5 c3-b4 c7-d6 b4-a5 b8-c7 a1-b2 g5-f4 e3xg5 c5xe3",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 f8-e7 f2-g3 f6-g5 h4xf6 e7xg5 g7-f6 h2-g3 g5-h4 e1-f2 b6-a5 d4xb6 a7xc5 a1-b2 c7-b6 g1-h2",
        "c3-d4 d6-c5 b2-c3 e7-d6 g3-h4 h6-g5 h2-g3 g7-h6 g3-f4 f6-e5 d4xf6 g5xe7 f2-g3 e7-f6 c3-d4 b6-a5 d4xb6 a7xc5 g1-h2 f6-e5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c1-b2 c7-d6 c3-b4 g7-f6 b4-a5 b8-c7 g3-f4 g5-h4 h2-g3 f6-e5 d4xf6 e7xg5 d2-c3 f8-e7 c3-d4 e7-f6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c1-b2 g7-f6 c3-b4 g5-h4 b4xd6 c7xc3 d2xb4 f6-g5 b4-a5 g5-f4 a5xc7 f4xd2 e1xc3 d8xb6 g3-f4 e7-d6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 a7-b6 b2xd4 b6-a5 g3-f4 g5-h4 e1-d2 b8-a7 a1-b2 d8-c7 b2-c3",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 a7-b6 b2xd4 b6-a5 g3-f4 g5-h4 h2-g3 d8-c7 f4-e5 a5-b4 a3xc5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-b2 a7-b6 b2xd4 b6-a5 a1-b2 g5-h4 d4-c5 g7-f6 e3-d4 d8-c7",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-b2 a7-b6 b2xd4 b6-a5 g3-f4 g7-f6 e1-d2 h8-g7 a1-b2 b8-a7",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-d2 a7-b6 d2xb4 b6-a5 b4-c5 g5-h4 a1-b2 d8-c7 b2-c3 c7-d6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-d2 a7-b6 d2xb4 b6-a5 b4-c5 g5-h4 a1-b2 d8-c7 c5-b6 g7-f6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-d2 a7-b6 d2xb4 b6-a5 b4-c5 g5-h4 a1-b2 d8-c7 e3-d4 g7-f6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-d2 a7-b6 d2xb4 b6-a5 b4-c5 g5-h4 a1-b2 d8-c7 g3-f4 h6-g5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c3-d2 e3xc1 e7-d6 a3-b4 f8-e7 b2-a3 d6-e5 g3-f4 g5xe3 f2xf6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c3-d2 e3xc1 e7-d6 a3-b4 f8-e7 b4-a5 d6-e5 b2-c3 g7-f6 c3-b4",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c3-d2 e3xc1 g5-h4 a3-b4 h6-g5 b2-c3 e7-d6 b4-a5 g7-f6 a1-b2",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 g7-f6 b2xd4 g5-h4 a3-b4 d8-c7 b4-a5 e7-d6 d4-c5 d6xb4 a5xc3",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 a7-b6 b2xd4 b6-a5 g3-f4 g5-h4 d4-c5 a5-b4 f4-g5 h6xd2 e1xa5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c1-b2 c3-d2 e3xc1 g5-h4 g3-f4 a7-b6 b2-c3 e7-d6 c3-d4 d6-c5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c1-d2 a7-b6 d2xb4 b6-a5 b4-c5 g5-h4 a1-b2 d8-c7 e3-d4 g7-f6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c3-d2 e3xc1 e7-d6 b2-c3 a7-b6 c3-d4 f8-e7 a3-b4 g7-f6 b4-a5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c3-d2 e3xc1 g5-h4 g3-f4 a7-b6 b2-c3 e7-d6 c3-d4 d6-c5 f4-e5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 c7-d6 b4-a5 d8-c7 a1-b2 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 f2-e3 g7-h6 e3xg5 h6xf4 d2-e3 f4xd2",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 c7-d6 g3-f4 g5-h4 b4-a5 d8-c7 g7-f6 b2-c3 f6-g5 c3-b4 e7-f6 d2-c3 f6-e5 d4xf6 g5xe7 c3-d4",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 e7-d6 b4-a5 f8-e7 g3-f4 g5-h4 h2-g3 g7-f6 a1-b2 f6-g5 b2-c3 c5-b4 a3xc5 d6xb4 d4-e5 b4-a3",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 e7-f6 b4xd6 c7xc3 d2xb4 f6-e5 b4-a5 g5-f4 e3xg5 h6xf4 a5xc7 b8xd6 a1-b2 a7-b6 g3-h4 d6-c5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 e7-f6 b4xd6 c7xc3 d2xb4 f6-e5 b4-c5 b6xd4 e3xc5 f8-e7 a3-b4 b8-c7 g3-h4 e5-f4 h4xf6 g7xe5",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 e7-f6 b4xd6 c7xc3 d2xb4 f6-e5 g3-f4 e5xg3 f2xf6 g7xe5 b4-a5 e5-f4 e3xg5 h6xf4 a5xc7 b8xd6",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 e7-f6 b4xd6 c7xc3 d2xb4 f6-e5 g5-f4 e3xg5 h6xf4 a5xc7 b8xd6 f2-e3 f4xd2 c1xe3 a7-b6 a1-b2",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 e7-f6 b4xd6 c7xc3 d2xb4 f6-e5 g5-f4 e3xg5 h6xf4 f2-e3 f4xd2 c1xe3 b6-a5 b2-c3 a7-b6 g3-f4",
        "c3-d4 d6-c5 b2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 d2xb4 b6-a5 a5xc3 b2xd4 a7-b6 g3-f4 b6-a5 a1-b2 b8-a7 e1-d2 a7-b6 d4-c5",
        "c3-d4 d6-c5 b2-c3 f6-g5 g3-f4 g7-f6 c1-b2 g5-h4 c3-b4 f6-g5 b4xd6 c7xg3 h2xf4 e7-d6 b2-c3 d6-c5 f4-e5 b6-a5 d4xb6 a5xc7",
        "c3-d4 d6-c5 b2-c3 f6-g5 g3-f4 g7-f6 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-b2 a7-b6 b2xd4 b6-a5 a1-b2 g5-h4 d4-c5 b8-a7",
        "c3-d4 d6-c5 b2-c3 f6-g5 g3-f4 g7-f6 f4-e5 e7-d6 e5xg7 h8xf6 f2-g3 g5-h4 g1-f2 f8-g7 a1-b2 b6-a5 d4xb6 a7xc5 e3-f4 f6-e5",
        "c3-d4 d6-c5 b2-c3 g7-f6 c1-b2 f6-g5 c3-b4 e7-d6 d4-e5 e3-d4 d8-c7 f8-e7 b4-a5 b6-c5 a5-b6 e5-d6 e7-f6 f6-e5 h2-g3 h8-g7",
        "c3-d4 d6-c5 b2-c3 h6-g5 c1-b2 g5-f4 g3xe5 e7-d6 c3-b4 d6xf4 e3xe7 c5xc1 b2-c3 f8xd6 b4-a5 b6-c5 c3-b4 g7-f6 a1-b2 f6-e5",
        "c3-d4 d6-c5 b2-c3 h6-g5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c1-b2 e7-d6 b2xd4 d6-e5 g3-h4 e5xc3 h2-g3 a7-b6 e3-f4 g5xe3",
        "c3-d4 d6-c5 b2-c3 h6-g5 c3-b4 g5-h4 b4xd6 c7xc3 d2xb4 f6-e5 e5xg3 h2xf4 e7-d6 a1-b2 d8-c7 b4-c5 b6xd4 e3xe7 f8xd6 b2-c3",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-f4 g5-h4 c1-b2 e7-d6 c3-b4 d6-e5 b4xd6 e5xg3 h2xf4 c7xg3 g1-h2 g7-h6 h2xf4 b6-c5 d4xb6 a7xc5",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-f4 g5-h4 c1-b2 e7-d6 h2-g3 f6-e5 d4xf6 g7xe5 c3-b4 h8-g7 b4-a5 d8-e7 d2-c3 c5-d4 e3xc5 d6xd2",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-f4 g5-h4 c3-b4 f6-e5 d4xf6 g7xg3 b4xd6 e7xc5 h2xf4 c7-d6 a1-b2 h8-g7 b2-c3 b6-a5 c3-b4 a5xc3",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-f4 g5-h4 f4-g5 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 g5-h6 e5-f4 e3xg5 h4xf6 h2-g3 f6-e5",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-f4 g5-h4 f4-g5 g7-h6 c3-b4 h6xf4 b4xd6 c7xc3 e3xg5 b6-a5 d2xb4 a5xc3 c1-b2 c3-d2 e1xc3 f6-e5",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-h4 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 c7-b6 a1-b2 b6xd4 e3xc5 g5-f4 f2-e3 g7-h6",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-h4 c7-d6 f2-g3 g7-h6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5 d6-c5 a1-b2 f8-g7 g3-f4 c5-d4 e3xc5 g5xe3",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-h4 e7-d6 h2-g3 g7-h6 g3-f4 f6-e5 d4xf6 g5xe7 g1-h2 b6-a5 f2-g3 c7-b6 c3-d4 c5-b4 a3xc5 d6xb4",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-h4 e7-d6 h2-g3 g7-h6 g3-f4 f6-e5 h4xf6 e5xg7 f2-g3 b6-a5 d4xb6 a7xc5 g3-h4 c7-b6 c1-b2 g7-f6",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-h4 g7-h6 f2-g3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 c3-b4 d6-e5 f4xd6 c7xe5 a1-b2 a7-b6 b2-c3 g5-f4",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-h4 g7-h6 h2-g3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5 d6-e5 e3-f4 g5xe3 d2xd6 e7xc5 a1-b2 f8-g7",
        "c3-d4 d6-c5 b2-c3 h6-g5 g3-h4 g7-h6 h2-g3 e7-d6 c3-b4 f6-e5 d4xf6 g5xe7 b4-a5 h8-g7 g3-f4 g7-f6 a1-b2 f6-e5 g1-h2 e5xg3",
        "c3-d4 d6-c5 d2-c3 c7-d6 c1-d2 f6-e5 d4xf6 g7xe5 c3-b4 h8-g7 g7-f6 a5xc7 d8xb6 e3-f4 b6-a5 f2-e3 a7-b6 g3-h4 e5xg3 h2xf4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b2-c3 f6-g5 g3-f4 g7-f6 a1-b2 g5-h4 c1-d2 a7-b6 f4-e5 d6xf4 e3xg5 h6xf4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-a5 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 c7-b6 g3-f4 b6xd4 e3xc5 d8-c7 b2-c3 f6-e5 f4xd6 c7xe5",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 f6-e5 f4xd6 c7xe5",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g3-f4 g7-f6 b2-c3 c7-d6 c1-d2 d6xb4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g3-f4 g7-f6 b2-c3 c7-d6 c3-b4 a7-b6",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g3-f4 g7-f6 b2-c3 c7-d6 e1-d2 d6xb4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g3-f4 g7-f6 f2-e3 f6-g5 c1-d2 e7-f6",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g3-f4 g7-f6 f2-g3 h4xf2 g1xe3 f6-g5",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 b2-a3 h8-g7",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 h8-g7 a1-b2 g5-h4 b2-a3 f6-g5",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 h6-g5 e3-d4 g5-h4 g3-f4 g7-h6 f2-e3 f6-g5 b2-c3 h8-g7",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 h6-g5 g3-f4 g7-h6 b2-c3 g5-h4 a1-b2 f6-g5 c3-d4 c7-d6",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 f6-g5 b4-a5 b8-c7 g3-f4 g5-h4 c1-d2 g7-f6 h2-g3 f8-g7 d4-e5 f6xd4 g1-h2 d4-c3 b2xd4 g7-f6",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 f6-g5 b4-a5 b8-c7 g3-f4 g5-h4 c1-d2 g7-f6 h2-g3 f8-g7 g1-h2 f6-e5 d4xf6 g7xe5 b2-c3 c5-d4",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 f6-g5 b4-a5 b8-c7 g3-f4 g5-h4 c1-d2 g7-f6 h2-g3 h8-g7 d4-e5 f6xd4 g1-h2 c5-b4 a5xe5 a5xe5",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 f6-g5 b4-a5 b8-c7 g3-f4 g5-h4 c1-d2 g7-f6 h2-g3 h8-g7 d4-e5 f6xd4 g1-h2 c5-b4 a5xe5 b6-c5",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 f6-g5 b4-a5 b8-c7 g3-f4 g5-h4 f2-g3 h4xf2 e1xg3 g7-f6 g3-h4 f8-g7 h2-g3 f6-e5 d4xf6 e7xg5",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 f6-g5 b4-a5 b8-c7 g3-f4 g5-h4 f2-g3 h4xf2 e1xg3 g7-f6 g3-h4 f8-g7 h2-g3 f6-e5 d4xf6 g7xe5",
        "c3-d4 d6-c5 d2-c3 c7-d6 c3-b4 f6-g5 b4-a5 b8-c7 g3-f4 g7-f6 h2-g3 g5-h4 d4-e5 f6xd4 g1-h2 h8-g7 c1-d2 c1-d2 c5-b4 a5xe5",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 b6-a5 d4xb6 a5xc3 b2xd4 a7xc5 d4xb6 c7xa5 a1-b2 d8-c7 e3-d4 f6-e5 d4xf6 g7xe5 b2-c3 h8-g7",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-e5 d4xf6 g7xe5 b4-a5 f8-g7 e3-f4 d8-e7 b2-c3 e7-f6 c3-b4 f6-g5 f2-e3 g5-h4 e1-f2 g7-f6",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 g7-f6 h2-g3 f6-g5 g3-f4 h8-g7 b2-c3 f8-e7 g1-h2 e7-f6",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 h6-g5 h2-g3 g7-h6 g3-f4 h8-g7 b2-c3 f8-e7 a1-b2 e7-f6",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 h6-g5 h2-g3 g7-h6 g3-f4 h8-g7 b2-c3 f8-e7 a1-b2 g5-h4",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 h6-g5 h2-g3 g7-h6 g3-f4 h8-g7 b2-c3 f8-e7 g1-h2 e7-f6",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 h6-g5 h2-g3 g7-h6 g3-f4 h8-g7 b2-c3 g5-h4 a1-b2 f8-e7",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 h6-g5 h2-g3 g7-h6 g3-f4 h8-g7 g1-h2 d8-e7 a3-b4 c5xc1",
        "c3-d4 d6-c5 d2-c3 e7-d6 c3-b4 f6-g5 b4-a5 g5-h4 g3-f4 g7-f6 f6-g5 d2-c3 d8-e7 c3-b4 e7-f6 b2-c3 f6-e5 d4xf6 g5xe7 c1-d2",
        "c3-d4 d6-c5 d2-c3 e7-d6 g3-h4 h6-g5 f2-g3 g7-h6 g3-f4 f6-e5 d4xf6 g5xe7 c3-d4 h8-g7 h2-g3 g7-f6 b2-c3 b6-a5 d4xb6 a7xc5",
        "c3-d4 d6-c5 d2-c3 f6-e5 d4xf6 g7xe5 c3-b4 c5-d4 e3xc5 b6xd4 c1-d2 h6-g5 g3-h4 f8-g7 h4xf6 e7xg5 b2-c3 d4xb2 a3xc1 g7-f6",
        "c3-d4 d6-c5 d2-c3 f6-e5 d4xf6 g7xe5 c3-b4 e5-d4 b4xd6 e7xc5 c1-d2 h6-g5 g3-h4 f8-e7 h4xf6 e7xg5 b2-c3 d4xb2 a3xc1 g5-h4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 b6-a5 b4xd6 c7xc3 b2xd4 g5-h4 g7-f6 c1-d2 h8-g7 d4-c5 a5-b4 c5-b6 a7xc5 b2-c3 e7-d6 c3xa5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 c1-d2 g7-f6 h2-g3 f8-g7 h8-g7 d4-e5 f6xd4 g1-h2 g1-h2 d4-c3",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 c1-d2 g7-f6 h2-g3 h8-g7 d4-e5 f6xd4 g1-h2 g1-h2 c5-b4 a5xe5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 f2-g3 h4xf2",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 f8-g7 f4-g5 h6xf4 e3xg5 c5xe3 d2xf4 d2xf4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 f8-g7 f4-g5 h6xf4 e3xg5 c5xe3 f2xd4 f2xd4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 f8-g7 h2-g3 f6-e5 d4xf6 g7xe5 c3-b4 e7-f6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 f8-g7 h2-g3 f6-e5 d4xf6 g7xe5 c3-b4 h8-g7",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 d4-e5 f6xd4 h2-g3 h2-g3 e1-d2 h8-g7 g1-h2 h6-g5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 f8-g7 h2-g3 f6-e5 d4xf6 g7xe5 h8-g7 d2-c3 c5-d4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 g7-f6 b2-c3 f8-g7 h2-g3 f6-e5 d4xf6 g7xe5 c3-b4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 h2-g3 f8-g7 b2-c3 f6-e5 d4xf6 g7xe5 g7xe5 c3-b4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 f2-g3 h4xf2 e1xg3 g7-f6 g3-h4 f8-g7 f8-g7 h2-g3 f6-e5 d4xf6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 f2-g3 h4xf2 e1xg3 g7-f6 g3-h4 f8-g7 h2-g3 f6-e5 d4xf6 e7xg5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 f2-g3 h4xf2 e1xg3 g7-f6 g3-h4 f8-g7 h2-g3 f6-e5 d4xf6 g7xe5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 g7-f6 b2-c3 f8-g7 f4-g5 h6xf4 e3xg5 c5xe3 f2xd4 f6-e5 d4xf6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 h2-g3 g7-f6 c1-d2 f6-e5 d4xf6 e7xg5 d2-c3 f8-e7 c3-d4 e7-f6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 e7-d6 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 g7-f6 h2-g3 h8-g7 g3-f4 f8-e7 b2-c3 f6-g5 f4-e5 c5-b4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 e7-d6 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 h6-g5 h2-g3 g7-h6 g3-f4 h8-g7 g1-h2 f8-e7 a3-b4 c5xc1",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 e7-d6 b4-a5 g5-f4 g3xe5 d6xd2 c1xe3 h6-g5 h2-g3 g7-h6 g3-f4 h8-g7 g1-h2 f8-e7 b2-c3 e7-f6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 e7-d6 g3-f4 b6-a5 d4xb6 a7xc5 a5xc3 b2xb6 c7xa5 g3-h4 g7-f6 a1-b2 d6-c5 b2-c3 f8-e7 e3-d4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 a1-b2 g7-f6 b2-c3 a7-b6 e3-f4 f6-g5 f4-e5 b6-c5 d4xb6 a5xc7",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 a1-b2 g7-f6 c1-d2 b8-c7 g3-f4 c7-b6 d2-c3 f6-g5 d4-c5 b6xd4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 a1-b2 g7-f6 c1-d2 h8-g7 d4-c5 a5-b4 c5-d6 e7xc5 b2-c3 b8-c7",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 a1-b2 g7-f6 g3-f4 f6-g5 b2-c3 d8-c7 d4-c5 c7-b6 c1-b2 b6xd4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g3-f4 g7-f6 a1-b2 f6-g5 b2-c3 a7-b6 d4-e5 h8-g7 c3-d4 d8-c7",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g3-f4 g7-f6 a1-b2 f6-g5 d4-c5 b8-c7 b2-c3 c7-d6 a3-b4 d8-c7",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g3-f4 g7-f6 f4-e5 f6-g5 d4-c5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g7-f6 a1-b2 f6-g5 b2-c3 a7-b6 d4-e5 h8-g7 c3-d4 d8-c7 a3-b4",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g7-f6 a1-b2 f6-g5 d4-c5 b8-c7 b2-c3 c7-d6 a3-b4 d8-c7 e1-d2",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g7-f6 b2-c3 a7-b6 g3-f4 f6-g5 d4-e5 h8-g7 c3-d4 b6-c5 d4xb6",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g7-f6 b2-c3 e7-d6 e3-f4 d6-c5 d4xb6 a5xc7 f4-g5 h6xf4 g3xg7",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g7-f6 c1-d2 b8-c7 g3-f4 c7-b6 d2-c3 f6-g5 d4-c5 b6xd4 c3xe5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g7-f6 c1-d2 h8-g7 d4-c5 a5-b4 c5-d6 e7xc5 b2-c3 b8-c7 c3xa5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g7-f6 g3-f4 f6-g5 b2-c3 d8-c7 d4-c5 c7-b6 c1-b2 b6xd4 c3xe5",
        "c3-d4 d6-c5 d2-c3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 h6-g5 b2-c3 e7-f6 c1-d2 f6-e5 d4xf6 g5xe7 c3-b4 a5xc3 d2xb4",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 b8xd6 a5xc3 b2xb6 a7xc5 a1-b2 d8-c7 b2-c3 c7-b6 c1-b2 b6-a5 c3-b4",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 b8xd6 a5xc3 b2xb6 a7xc5 a1-b2 d8-c7 b2-c3 c7-b6 c3-b4 b6-a5 e3-d4",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 b8xd6 c3-b4 a5xc3 b2xb6 a7xc5 a1-b2 b2-c3 c7-b6 c3-b4 b6-a5 e3-d4",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 b8xd6 c3-b4 a5xc3 b2xb6 a7xc5 a1-b2 d8-c7 b2-c3 c7-b6 c1-b2 b6-a5",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 c7-d6 d4-e5 b6-a5 e5xc7 b8xd6 c3-b4 a5xc3 b2xb6 a7xc5 a1-b2 d8-c7 b2-c3 c7-b6 c3-b4 b6-a5",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 b4xd6 c7xc3 b2xd4 b6-a5 a1-b2 f6-g5 b2-c3 d8-c7 a7-b6 d4-e5 h8-g7 c3-d4",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 b4xd6 c7xc3 b2xd4 b6-a5 a1-b2 f6-g5 b2-c3 d8-c7 h2-g3 d4-c5 c7-b6 e3-d4",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 b4xd6 c7xc3 b2xd4 b6-a5 a1-b2 f6-g5 b2-c3 d8-c7 h2-g3 h8-g7 c3-b4 a5xe5",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 b4xd6 c7xc3 b2xd4 f6-g5 a1-b2 b6-a5 b2-c3 d8-c7 d4-c5 c7-b6 c1-b2 b6xd4",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g5-h4 c3-b4 g7-f6 b4xd6 c7xc3 b2xd4 f6-g5 a1-b2 b6-a5 b2-c3 d8-c7 h2-g3 h8-g7 c3-b4 a5xe5",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g7-f6 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 a1-b2 f6-g5 b2-c3 e7-d6 d4-e5 b8-c7 c3-b4 a5xc3",
        "c3-d4 d6-c5 d2-c3 f6-g5 g3-f4 g7-f6 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 a1-b2 f6-g5 b2-c3 e7-d6 d4-e5 b8-c7 e3-d4 g5xc5",
        "c3-d4 d6-c5 d2-e3 e7-d6 g3-f4 f6-g5 b2-c3 g7-f6 c1-d2 f6-e5 d4xf6 g5xe7 c3-d4 f8-g7 h2-g3 g7-f6 a1-b2 f6-g5 d4-e5 c5-d4",
        "c3-d4 d6-c5 g3-f4 c7-d6 b2-c3 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 a1-b2 g5-h4 c3-d4 g7-f6 b2-c3 f6-g5 h2-g3 e7-d6 d4-e5 b8-c7",
        "c3-d4 d6-c5 g3-f4 c7-d6 b2-c3 f6-g5 d4-e5 b6-a5 e5xc7 d8xb6 g5-h4 c3-d4 g7-f6 b2-c3 f6-g5 h2-g3 e7-d6 d4-e5 b8-c7 e5-f6",
        "c3-d4 d6-c5 g3-f4 c7-d6 f2-g3 b6-a5 d4xb6 a5xc7 b2-c3 f6-e5 a1-b2 g7-f6 c3-b4 a7-b6 d2-c3 b6-a5 e3-d4 c7-b6 e1-f2 b6-c5",
        "c3-d4 d6-c5 g3-f4 f6-g5 b2-c3 g7-f6 h2-g3 g5-h4 f4-e5 h8-g7 g3-f4 f6-g5 c3-b4 b6-a5 b4xd6 e7xc5 d4xb6 a7xc5 a1-b2 f8-e7",
        "c3-d4 d6-c5 g3-f4 f6-g5 d2-c3 g7-f6 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 f4-e5 b8-c7 e5xg7 h8xf6 h2-g3 c7-b6 a1-b2 b6-c5",
        "c3-d4 d6-c5 g3-f4 g7-f6 f2-g3 f6-g5 g3-h4 f8-g7 h4xf6 g7xg3 h2xf4 h8-g7 g1-h2 g7-f6 h2-g3 f6-g5 g3-h4 e7-f6 e1-f2 d8-e7",
        "c3-d4 d6-c5 g3-f4 g7-f6 f2-g3 f8-g7 b2-c3 e7-d6 f4-e5 d6xf4 e3xe7 d8xf6 d2-e3 h6-g5 g3-f4 g7-h6 f4-e5 h8-g7 c3-b4 c7-d6",
        "c3-d4 d6-c5 g3-h4 c7-d6 f2-g3 b6-a5 d4xb6 a5xc7 a3-b4 a7-b6 b6-c5 e1-f2 f6-g5 h4xf6 g7xe5 e3-f4 e7-f6 b2-a3 f8-g7 a1-b2",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 a7-b6 b4-a5 f6-e5 e3-f4 b6-c5 b2-c3 g7-f6 f2-e3 c5-b4 a1-b2 b4-a3",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 a7-b6 f6-e5 e3-f4 b6-c5 b2-c3 c5-b4 a1-b2 b4-a3 f2-e3 g7-f6 e1-f2",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 a7-b6 f6-g5 h4xf6 g7xe5 e3-f4 h8-g7 f2-e3 g7-f6 b2-c3 f6-g5 g3-h4",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-e5 a7-b6 b4-a5 b6-c5 b2-a3 g7-f6 a1-b2 e5-d4 d2-e3 d4-c3 b2xb6",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-e5 a7-b6 e3-f4 e5-d4 d2-e3 b6-c5 c1-d2 g7-f6 g1-h2 f6-g5 h4xf6",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-e5 b4-a5 a7-b6 e3-f4 e5-d4 d2-e3 b6-c5 c1-d2 g7-f6 g1-h2 f6-g5",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-e5 e3-f4 e5-d4 b4-a5 a7-b6 d2-e3 b6-c5 c1-d2 g7-f6 g1-h2 f6-g5",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-e5 e5-d4 b4-a5 a7-b6 d2-e3 b6-c5 c1-d2 g7-f6 g1-h2 f6-g5 h4xf6",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-g5 h4xf6 g7xe5 e3-f4 a7-b6 b2-a3 e7-f6 b4-a5 f8-g7 d2-c3 b6-c5",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-g5 h4xf6 g7xe5 e3-f4 a7-b6 b4-a5 b6-c5 b2-a3 h8-g7 a1-b2 g7-f6",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-g5 h4xf6 g7xe5 e3-f4 a7-b6 b4-a5 e7-f6 b2-c3 f6-g5 a1-b2 g5xe3",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 b6-a5 d4xb6 a5xc7 a3-b4 f6-g5 h4xf6 g7xe5 e3-f4 h8-g7 b4-a5 g7-f6 b2-c3 a7-b6 a1-b2 f6-g5",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 d6-e5 g1-h2 e5xc3 d2xd6 e7xc5 b2-c3 b6-a5 c1-d2 d8-e7 g3-f4 a7-b6 f2-g3 b8-a7 c3-d4 a5-b4",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 d6-e5 g1-h2 e5xc3 d2xd6 e7xc5 b2-c3 b6-a5 c1-d2 d8-e7 g3-f4 a7-b6 f2-g3 b8-a7 c3-d4 e7-d6",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 d6-e5 g1-h2 e5xc3 d2xd6 e7xc5 b2-c3 f8-e7 c3-b4 c5-d4 e3xc5 b6xd4 b4-a5 a7-b6 a5xc7 b8xd6",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 d6-e5 g1-h2 e5xc3 d2xd6 e7xc5 b2-c3 f8-e7 c3-b4 c5-d4 e3xc5 b6xd4 b4-a5 d8-c7 c1-d2 e7-d6",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 d6-e5 g1-h2 e5xc3 d2xd6 e7xc5 b2-c3 f8-e7 c3-b4 c5-d4 e3xc5 b6xd4 c1-d2 d4-e3 d2xf4 f6-g5",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 d6-e5 g1-h2 e5xc3 d2xd6 e7xc5 b6-a5 c1-d2 d8-e7 g3-f4 a7-b6 f2-g3 b8-a7 c3-d4 a5-b4 d4-e5",
        "c3-d4 d6-c5 g3-h4 c7-d6 h2-g3 d6-e5 g1-h2 e5xc3 d2xd6 e7xc5 f8-e7 c3-b4 c5-d4 e3xc5 b6xd4 b4-a5 d8-c7 c1-d2 e7-d6 a1-b2",
        "c3-d4 d6-c5 g3-h4 f6-e5 b2-c3 g7-f6 b6-a5 c3-b4 a1-b2 b8-c7 b2-c3 c7-d6 e1-d2 a7-b6 g3-f4 f6-e5 e3-d4 b6-a5 d4-c5 d8-e7",
        "c3-d4 d6-c5 g3-h4 f6-g5 h4xf6 g7xc3 d2xd6 e7xc5 b2-c3 c7-d6 h2-g3 h8-g7 c3-d4 g7-f6 a1-b2 d6-e5 b2-c3 f8-e7 g3-f4 e5xg3",
        "c3-d4 d6-c5 g3-h4 f6-g5 h4xf6 g7xc3 d2xd6 e7xc5 b2-c3 h8-g7 c5-d4 e3xc5 b6xd4 h2-g3 g7-f6 c1-d2 f6-e5 d2-c3 d4xb2 a1xc3",
        "c3-d4 d6-c5 g3-h4 h6-g5 f2-g3 g7-h6 b2-c3 e7-d6 g3-f4 f6-e5 h4xf6 e5xg7 h2-g3 b6-a5 d4xb6 a7xc5 g3-h4 c7-b6 c1-b2 g7-f6",
        "c3-d4 d6-c5 h2-g3 e7-d6 b2-c3 d6-e5 g3-h4 c7-d6 h4-g5 f6xh4 d4xf6 g7xe5 e3-d4 c5xe3 f2xf6 b6-c5 c3-d4 c5xe3 d2xf4 a7-b6",
        "c3-d4 d6-e5 b2-c3 b6-a5 a1-b2 c7-d6 a3-b4 a7-b6 b2-a3 b6-c5 d4xb6 a5xc7 e3-d4 h6-g5 b4-a5 g5-f4 a3-b4 b8-a7 g3-h4 g7-h6",
        "c3-d4 d6-e5 b2-c3 b6-a5 a1-b2 c7-d6 a3-b4 a7-b6 b2-a3 b6-c5 d4xb6 a5xc7 e3-d4 h6-g5 b4-a5 g5-f4 a3-b4 g7-h6 g3-h4 f4-e3",
        "c3-d4 d6-e5 b2-c3 b6-a5 a1-b2 c7-d6 a3-b4 a7-b6 b2-a3 b6-c5 d4xb6 a5xc7 e3-d4 h6-g5 g3-h4 e5-f4 b4-c5 d6xb4 a3xc5 e7-d6",
        "c3-d4 d6-e5 b2-c3 b6-a5 a1-b2 c7-d6 a3-b4 a7-b6 b2-a3 b6-c5 d4xb6 a5xc7 e3-d4 h6-g5 g3-h4 g7-h6 f2-e3 g5-f4 e3xg5 h6xf4",
        "c3-d4 d6-e5 b2-c3 b6-a5 a1-b2 c7-d6 a3-b4 a7-b6 b2-a3 b6-c5 d4xb6 a5xc7 e3-f4 f6-g5 f2-e3 g5-h4 g1-f2 c7-b6 b4-a5 b6-c5",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5 b8-c7 a1-b2 c7-d6 b2-a3 d6xb4 a3xc5 d8-c7 c1-b2 c7-d6 b2-a3 d6xb4 a3xc5 h6-g5",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5 d8-c7 a1-b2 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 c1-b2 c7-d6 b2-a3 d6xb4 a3xc5 h6-g5",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5 h6-g5 g3-f4 e5xg3 h2xh6 f6-e5 d4xf6 b6xb2 a1xc3 g7xe5 c1-b2 a7-b6 b2-a3 h8-g7",
        "c3-d4 d6-e5 b2-c3 b6-a5 a3-b4 c7-b6 b4-c5 h6-g5 g3-f4 e5xg3 h2xh6 f6-e5 d4xf6 b6xb2 a1xc3 g7xe5 f2-g3 a7-b6 g3-h4 h8-g7",
        "c3-d4 d6-e5 b2-c3 b6-a5 e3-f4 a7-b6 f4xd6 e7xe3 d2xf4 f6-g5 f2-e3 c7-d6 c1-d2 g5-h4 g1-f2 f8-e7 c3-d4 d8-c7 f4-e5 d6xf4",
        "c3-d4 d6-e5 b2-c3 b6-a5 g3-f4 a5-b4 f6-g5 a1-b2 h8-g7 b2-c3 g7-f6 f2-g3 f6-g5 g3-h4 c5-b4 f8-e7 g1-f2 f2-g3 g5-h4 c3-d4",
        "c3-d4 d6-e5 b2-c3 b6-a5 g3-h4 c7-b6 f2-g3 e7-d6 g3-f4 e5xg3 h4xf2 d6-c5 h2-g3 f6-g5 g3-f4 g5-h4 f2-g3 h4xf2 e1xg3 g7-f6",
        "c3-d4 d6-e5 b2-c3 b6-c5 d4xb6 a7xc5 e3-f4 c5-d4 f4xd6 e7xc5 c3xe5 f6xd4 c1-b2 h6-g5 b2-c3 d4xb2 a3xc1 g5-h4 a1-b2 g7-f6",
        "c3-d4 d6-e5 b2-c3 c7-d6 c1-d2 b6-c5 d4xb6 a7xc5 e3-f4 c5-b4 a3xc5 d6xb4 f4xd6 e7xc5 f2-e3 d8-c7 g3-f4 f6-e5 f4xd6 c7xe5",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-a5 d4-c5 d6xb4 a3xc5 h6-g5 f4xh6 e5-f4 g3xe5 f6xb6 f2-e3 b8-c7 h2-g3 c7-d6 a1-b2 g7-f6",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-a5 f2-e3 a7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 g1-f2 b6-a5 f2-e3 b8-a7 a3-b4 f6-g5",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-a5 f2-e3 a7-b6 c1-b2 b8-a7 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 f2-e3 b6-a5 g3-h4 e5xg3 h4xf2",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-a5 f2-e3 a7-b6 c1-b2 b8-a7 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 f2-e3 b6-a5 g3-h4 e5xg3",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-a5 f2-e3 a7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 f2-e3 b6-a5 a1-b2 h6-g5 f4xh6 a5-b4",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 b8-c7 b4-a5 c7-b6 a5xc7 d8xb6 g3-h4 e5xg3 h2xf4 f6-e5 f4-g5 h6xf4",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 b8-c7 c7-b6 a5xc7 d8xb6 g3-h4 e5xg3 h2xf4 f6-e5 f4-g5 h6xf4 a3-b4",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 b8-c7 f2-e3 f6-g5 a1-b2 g5-h4 d2-c3 h4xd4 g1-f2 e5xg3 c3xe5 d6xf4",
        "c3-d4 d6-e5 b2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 b8-c7 f6-g5 a1-b2 g5-h4 d2-c3 h4xd4 g1-f2 e5xg3 c3xe5 d6xf4 b4xb8",
        "c3-d4 d6-e5 b2-c3 e5-f4 g3xe5 b6-c5 d4xb6 f6xb2 a1xc3 c7xa5 g7-f6 g3-h4 f6-g5 h4xf6 e7xg5 c3-d4 h8-g7 a3-b4 a5xe5 e3-f4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 d2-e3 c7-b6 c3-b4 a5xc3 d4xb2 b6-c5 c1-d2 a7-b6 d2-c3 b8-a7 g3-h4 e5xg3 h2xf4 b6-a5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 d2-e3 c7-b6 c3-b4 a5xc3 d4xb2 f6-g5 a3-b4 g5-h4 b2-a3 b6-c5 b4-a5 a7-b6 a5xc7 d8xb6",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 d2-e3 c7-b6 c3-b4 a5xc3 d4xb2 f6-g5 a3-b4 g5-h4 b2-a3 b6-c5 c1-d2 a7-b6 b4-a5 b8-a7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 d2-e3 c7-b6 c3-b4 a5xc3 d4xb2 f6-g5 a3-b4 g5-h4 b2-a3 b6-c5 c1-d2 a7-b6 b4-a5 f8-e7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 d2-e3 c7-b6 c3-b4 a5xc3 d4xb2 f6-g5 a3-b4 g5-h4 b4-a5 b6-c5 c1-d2 b8-c7 b2-a3 f8-e7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 d2-e3 c7-b6 c3-b4 a5xc3 d4xb2 f6-g5 g3-h4 e5xg3 h4xf6 g7xe5 h2xf4 e5xg3 f2xh4 h8-g7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 a3-b4 a7-b6 b4-a5 f6-g5 c3-d4 e5xc3 b2xd4 g5-h4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 c3-d4 e5xc3 b2xd4 a7-b6 f4-e5 d6xf4 e3xe7 f8xd6",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 d6-c5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 a3-b4 b6-a5 b2-a3 c7-b6 b4-c5 d6xb4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 a3-b4 b6-a5 b2-a3 c7-b6 g1-f2 d6-c5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 a3-b4 b6-a5 b4-c5 d6xb4 f4xd6 c7xe5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 d2-e3 b6-a5 g1-f2 c7-b6 a3-b4 b8-a7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 d2-e3 b6-a5 a3-b4 a7-b6 g1-f2 b8-a7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 d4-c5 b6xd4 g3-h4 e5xg3 c3xc7 b8xd6",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 g1-f2 h6-g5 f4xh6 d6-c5 f2-e3 e5-f4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 g3-h4 e5xg3 h4xf2 d6-c5 d2-e3 f6-g5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a7xc5 c3-b4 a5xc3 b2xb6 b8-a7 g3-h4 a7xc5 a3-b4 e5xg3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 c1-b2 b6-c5 d4xb6 a7xc5 c3-b4 a5xc3 b2xb6 b8-a7 g3-h4 e5xg3 h2xf4 a7xc5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 a3-b4 a7-b6 c1-b2 d6-c5 b4xd6 b6-c5 d6xb4 d8-e7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 c3-b4 f6-g5 b4-c5 d6xb4 f4xd6 c7xe5 a3xc5 e5-d4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 c3-d4 e5xc3 d2xb4 f6-g5 c1-d2 a7-b6 a1-b2 f8-e7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 c3-d4 e5xc3 d2xb4 f6-g5 c1-d2 d6-e5 f4xd6 c7xe5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 a3-b4 b6-a5 a1-b2 d6-c5 d4xb6 e5-d4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 a7-b6 d2-e3 b6-a5 c1-d2 c7-b6 a1-b2 b6-c5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 c1-b2 h6-g5 f4xh6 d6-c5 f2-e3 e5-f4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 d2-e3 b6-a5 c1-d2 a7-b6 a1-b2 b6-c5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 d2-e3 b6-c5 d4xb6 a7xc5 c1-b2 b8-c7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 d2-e3 b8-c7 f4-g5 h6xb4 a3xg5 e5xc3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 f2-e3 b8-c7 c1-b2 f8-e7 g3-h4 e5xg3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a7xc5 c1-b2 b8-a7 c3-b4 a5xc3 b2xb6 a7xc5 a1-b2 d8-c7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a7xc5 c1-b2 b8-a7 c3-b4 a5xc3 b2xb6 a7xc5 d2-c3 d8-c7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a7xc5 c1-b2 b8-a7 c3-b4 a5xc3 b2xb6 a7xc5 d2-c3 f6-g5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a7xc5 c3-d4 e5xc3 d2xb4 a5xc3 c1-b2 b8-a7 b2xb6 a7xc5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 f8-e7 b6-c5 d4xb6 a7xc5 c3-b4 a5xc3 b2xb6 f6-g5 b6-c7 d8xb6 g3-h4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g3-h4 e5xg3 h4xf2 d6-c5 a1-b2 h6-g5 h2-g3 b8-c7 c3-b4 a5xa1 d4-e5 f6xd4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g3-h4 e5xg3 h4xf2 d6-c5 a1-b2 h6-g5 h2-g3 f8-e7 c3-b4 a5xa1 g1-h2 a1xe5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g3-h4 e5xg3 h4xf2 d6-c5 f2-g3 c5-b4 a3xc5 f6-e5 d4xf6 b6xh4 c1-b2 g7xe5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 b4-a5 f6-g5 a5xc7 d8xb6 f2-e3 b6-a5 g3-h4 e5xg3 h4xf2 g5-f4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 e5-d4 g1-f2 d4-c3 b4-a5 h6-g5 a5xe5 f6xd4 d2xd6 g7-h6 e3xc5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 f2-e3 e5-d4 f4-e5 d4xh4 e5xa5 d8-e7 b4xd6 e7xc5 e1-f2 f6-e5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 f2-e3 e5-d4 g1-f2 d4-c3 b4-a5 h6-g5 a5xe5 f6xd4 d2xd6 g7-h6",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 f8-e7 a1-b2 f6-g5 f2-e3 g5-h4 d2-c3 h4xd4 g1-f2 e5xg3 c3xe5 d6xf4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 f8-e7 f6-g5 f2-e3 g5-h4 d2-c3 h4xd4 g1-f2 e5xg3 c3xe5 d6xf4 b4xf8",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 c7xa5 f2-e3 a7-b6 c1-b2 f8-e7 g1-f2 b8-c7 e3-d4 b6-c5 d4xb6 f6-g5 d2-e3 e5-d4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 c7xa5 f2-e3 a7-b6 c1-b2 f8-e7 g1-f2 b8-c7 e3-d4 b6-c5 d4xb6 f6-g5 f2-e3 e5-d4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 c7xa5 f2-e3 a7-b6 e5xg3 h4xf2 h6-g5 c3-b4 a5xc3 d2xb4 d8-c7 b4-a5 f6-e5 a1-b2",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 c7xa5 f2-e3 a7-b6 f8-e7 g1-f2 b8-a7 e3-d4 b6-c5 d4xb6 a5xc7 a3-b4 c7-b6 b4-c5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 c7xa5 f2-e3 a7-b6 f8-e7 g1-f2 b8-c7 e3-d4 b6-c5 d4xb6 f6-g5 d2-e3 e5-d4 c3xe5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 c7xa5 f2-e3 a7-b6 f8-e7 g1-f2 b8-c7 e3-d4 b6-c5 d4xb6 f6-g5 f2-e3 e5-d4 c3xe5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 b6-c5 d4xb6 c7xa5 f2-e3 a7-b6 g3-h4 e5xg3 h4xf2 h6-g5 c3-b4 a5xc3 d2xb4 f6-e5 b4-a5 d8-c7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 a3-b4 c5xa3 e3-d4 c7-b6 a1-b2 b8-a7 d4-c5 d6xd2 f4xf8 b6-c5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 a3-b4 c5xa3 e3-d4 c7-b6 a1-b2 b8-a7 e1-d2 b6-c5 d4xb6 a7xc5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 a3-b4 c5xa3 e3-d4 c7-b6 a1-b2 d8-c7 d4-c5 d6xd2 f4xf8 b6-c5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 a3-b4 c5xa3 e3-d4 c7-b6 a1-b2 d8-c7 d4-c5 d6xd2 f4xf8 b8-a7",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 a3-b4 c5xa3 e3-d4 c7-b6 a1-b2 d8-c7 d4-c5 d6xd2 f4xf8 f6-e5",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 a3-b4 c5xa3 e3-d4 c7-b6 a1-b2 d8-c7 e1-d2 b6-a5 d4-c5 d6xb4",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 c5xa3 e3-d4 c7-b6 a1-b2 b8-a7 d4-c5 d6xd2 f4xf8 b6-c5 c1xe3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 c5xa3 e3-d4 c7-b6 a1-b2 b8-a7 e1-d2 b6-c5 d4xb6 a7xc5 f2-e3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 c5xa3 e3-d4 c7-b6 a1-b2 d8-c7 d4-c5 d6xd2 f4xf8 b6-c5 c1xe3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 c5xa3 e3-d4 c7-b6 a1-b2 d8-c7 d4-c5 d6xd2 f4xf8 b8-a7 c1xe3",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 d2-e3 b6-c5 d4xb6 a7xc5 c5xa3 e3-d4 c7-b6 a1-b2 d8-c7 e1-d2 b6-a5 d4-c5 d6xb4 f4xf8",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 f2-e3 b6-c5 d4xb6 a7xc5 g3-h4 e5xg3 h4xf2 f6-e5 c3-d4 e5xc3 d2xb4 h6-g5 a1-b2 g7-f6",
        "c3-d4 d6-e5 b2-c3 e7-d6 e3-f4 f8-e7 f2-e3 b6-c5 d4xb6 a7xc5 g3-h4 e5xg3 h4xf2 f6-e5 e3-f4 e5xg3 h2xf4 g7-f6 c3-b4 f6-e5",
        "c3-d4 d6-e5 b2-c3 e7-d6 g3-h4 b6-a5 f2-g3 c7-b6 e3-f4 b6-c5 d4xb6 a5xc7 c3-b4 a7-b6 b4-c5 b6xd4 f4-g5 h6xf4 d2-e3 d4xf2",
        "c3-d4 d6-e5 b2-c3 e7-d6 g3-h4 d6-c5 f2-g3 c7-d6 g3-f4 e5xg3 h4xf2 b6-a5 d4xb6 a5xc7 a3-b4 a7-b6 b4-a5 f6-e5 a1-b2 h6-g5",
        "c3-d4 d6-e5 b2-c3 g7-h6 a1-b2 e7-d6 g3-f4 f8-e7 f6-g5 c3-b4 g3-h4 e7-f6 d4-e5 c5-b4 b6-a5 d6-c5 b2-a3 c7-d6 c3-b4 a7-b6",
        "c3-d4 d6-e5 b4-a5 e5xc3 a5xc7 d8xb6 b2xd4 g5-f4 g3xe5 b6-c5 d4xb6 f6xf2 g1xe3 a7xc5 d2-c3 b8-c7 c3-d4 c7-b6 a1-b2 g7-f6",
        "c3-d4 d6-e5 c1-b2 c7-d6 a1-b2 d6-c5 b6-a5 e3-d4 e7-d6 f2-e3 h6-g5 b2-c3 a7-b6 c3-b4 b6-c5 d6-e5 g3-f4 g7-h6 e3-d4 g5-f4",
        "c3-d4 d6-e5 d2-c3 c7-d6 e3-f4 b6-a5 f2-e3 a7-b6 g3-h4 e5xg3 h4xf2 h6-g5 a3-b4 b6-c5 d4xb6 a5xc7 b4-a5 g5-f4 e3xg5 f6xh4",
        "c3-d4 d6-e5 d2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 b2-c3 d4xb2 a1xc3 f6-g5 e1-d2 g5xe3 f2xf6 g7xe5 g3-f4 e5xg3",
        "c3-d4 d6-e5 d2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 b4-a5 b8-c7 c1-d2 h6-g5 f4xh6 f6-g5 h6xf4 d4-e3 f2xf6 e7xc1",
        "c3-d4 d6-e5 d2-c3 e7-d6 a3-b4 f6-g5 e3-d4 e7-f6 h6-g5 d4-e5 g7-f6 d2-e3 f6-e5 e3-f4 b6-c5 b2-c3 g7-f6 c3-d4 f8-e7 g1-f2",
        "c3-d4 d6-e5 d2-c3 e7-d6 a3-b4 f6-g5 e3-d4 h6-g5 e7-f6 c1-d2 f6-e5 g3-f4 g7-h6 f4-e5 c3-d4 h8-g7 d4-c5 f2-g3 g7-f6 c3-d4",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 f2-e3 b6-a5 e1-f2 a7-b6 a3-b4 b6-c5",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-a5 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 f2-e3 b8-c7 c1-d2 f8-e7 g3-h4 e5xg3",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c1-d2 f6-g5 d2-e3 e5-d4 c3xe5 g5-h4 e1-d2 b8-a7 b2-c3 a7-b6 c3-b4 b6-a5",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c1-d2 f6-g5 e5-d4 c3xe5 g5-h4 e1-d2 b8-a7 b2-c3 a7-b6 c3-b4 b6-a5 d2-c3",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 b4-a5 f6-g5 a3-b4 g5xe3 b2-c3 d4xb2 f2xf6 g7xe5 a1xc3 c7-b6",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 b2-c3 f6-g5 f2-e3 g5-h4 a1-b2 h4xd4 g1-f2 e5xg3 c3xa5 d8-e7",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 f2-e3 f6-g5 e1-d2 g5-h4 d2-c3 h4xd4 b4-a5 e5xg3 c3xc7 b8xd6",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 f6-g5 e1-d2 g5-h4 d2-c3 h4xd4 b4-a5 e5xg3 c3xc7 b8xd6 a5xe5",
        "c3-d4 d6-e5 d2-c3 e7-d6 e3-f4 b6-c5 d4xb6 a7xc5 c3-b4 c7-b6 f6-g5 f2-e3 g5-h4 a1-b2 h4xd4 g1-f2 e5xg3 c3xa5 d8-e7 b4xd6",
        "c3-d4 d6-e5 d2-c3 g5-h4 a3-b4 f6-g5 d4xf6 g5xe7 c3-d4 b6-c5 d4xb6 a7xa3 g3-f4 e7-d6 b2-c3 g7-f6 g1-h2 f6-g5 e1-d2 f8-g7",
        "c3-d4 d6-e5 g3-f4 e5xc3 b2xd4 b6-a5 d2-c3 f6-g5 c1-b2 e7-d6 g5-h4 e1-d2 f8-e7 a3-b4 c7-b6 b2-a3 g7-f6 b4-c5 d6xb4 a3xc5",
        "c3-d4 d6-e5 g3-f4 e5xc3 b2xd4 b6-a5 h2-g3 c7-b6 a1-b2 f6-g5 e7-d6 g1-h2 f8-e7 d4-e5 b8-c7 g3-h4 e7-f6 c1-b2 f6xd4 e3xe7",
        "c3-d4 d6-e5 g3-f4 e5xc3 b2xd4 b6-a5 h2-g3 f6-g5 a1-b2 g5-h4 c7-b6 c1-b2 g7-f6 d4-c5 b6xd4 c3xg7 h8xf6 f4-e5 f6xd4 e3xc5",
        "c3-d4 d6-e5 g3-f4 e5xc3 b2xd4 e7-d6 f4-e5 d6xf4 e3xe7 d8xf6 f8-e7 g3-h4 c7-d6 d4-c5 d6xb4 a5xc3 e7-d6 d2-e3 f6-e5 f2-g3",
        "c3-d4 d6-e5 g3-f4 e5xc3 b2xd4 f6-e5 f4xd6 c7xc3 c1-b2 e7-f6 b2xd4 f6-e5 d4xf6 g7xe5 a1-b2 e5-f4 e3xg5 h4xf6 b2-c3 b8-c7",
        "c3-d4 d6-e5 g3-f4 e5xc3 d2xb4 f6-g5 b4-a5 g7-f6 b2-c3 g5-h4 c3-b4 f6-g5 a1-b2 h8-g7 h2-g3 g7-f6 b2-c3 e7-d6 c3-d4 d6-c5",
        "c3-d4 d6-e5 g3-f4 e5xc3 d2xb4 f6-g5 b4-a5 g7-f6 b2-c3 g5-h4 f6-g5 c3-d4 e7-d6 d2-c3 h8-g7 a1-b2 g7-f6 f2-g3 h4xf2 e1xg3",
        "c3-d4 d6-e5 g3-f4 e5xc3 d2xb4 f6-g5 b4-c5 b6xd4 e3xc5 g5xe3 f2xd4 h6-g5 h2-g3 g7-h6 e1-f2 h8-g7 b2-c3 g5-h4 c1-d2 g7-f6",
        "c3-d4 d6-e5 g3-f4 e5xg3 h2xf4 b6-a5 d4-c5 f6-g5 a3-b4 a5xc3 d2xb4 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 b2-a3 f8-g7 c5-b6 c7xa5",
        "c3-d4 d6-e5 g3-f4 e5xg3 h2xf4 b6-c5 d4xb6 a7xc5 b2-c3 e7-d6 c3-d4 f6-e5 d4xb6 e5xg3 f2xh4 c7xa5 a1-b2 g7-f6 b2-c3 d8-c7",
        "c3-d4 d6-e5 g3-f4 e5xg3 h2xf4 b6-c5 d4xb6 a7xc5 b2-c3 e7-d6 f6-e5 f4-g5 h6xf4 e3xg5 g7-f6 g5xe7 d8xf6 d2-e3 c7-b6 b4-a5",
        "c3-d4 d6-e5 g3-f4 e5xg3 h2xf4 f6-g5 a3-b4 e7-d6 b4-a5 g7-f6 f8-e7 a1-b2 h8-g7 b2-a3 g5-h4 c3-b4 b6-c5 d4xb6 a7xc5 f2-g3",
        "c3-d4 d6-e5 g3-h4 e5xc3 d2xb4 f6-e5 f2-g3 e7-d6 g3-f4 e5xg3 h4xf2 h6-g5 h2-g3 d6-e5 c1-d2 g5-h4 d2-c3 f8-e7 b4-a5 e7-d6",
        "c3-d4 d6-e5 g3-h4 e5xc3 d2xb4 f6-e5 h2-g3 b6-a5 b2-c3 e7-d6 e3-f4 c7-b6 c3-d4 e5xc3 b4xd2 d6-e5 f4xd6 h6-g5 h4xf6 g7xc7",
        "c3-d4 d6-e5 g3-h4 e5xc3 d2xb4 f6-e5 h2-g3 b6-a5 b2-c3 e7-d6 e3-f4 g7-f6 f2-e3 c7-b6 g1-h2 h6-g5 f4xh6 f8-g7 h6xf8 b8-c7",
        "c3-d4 d6-e5 g3-h4 e5xc3 d2xb4 f6-e5 h2-g3 e7-d6 e3-f4 g7-f6 b4-a5 b6-c5 b2-c3 a7-b6 f2-e3 h8-g7 c3-d4 e5xc3 c1-b2 h6-g5",
        "c3-d4 d6-e5 g3-h4 e5xc3 d2xb4 f6-g5 h4xf6 g7xe5 b2-c3 h6-g5 b4-a5 e5-f4 c3-d4 f4xd2 c1xe3 h8-g7 a1-b2 g7-h6 h2-g3 b6-c5",
        "c3-d4 d6-e5 g3-h4 e5xc3 d2xb4 f6-g5 h4xf6 g7xe5 b2-c3 h8-g7 b4-a5 e5-f4 e3xg5 h6xf4 c1-d2 b6-c5 a1-b2 g7-f6 c3-b4 a7-b6",
        "c3-d4 d6-e5 h2-g3 e5xc3 b2xd4 f6-e5 d4xf6 g7xe5 d2-c3 e5-d4 e3xc5 b6xb2 a1xc3 a7-b6 c1-d2 c7-d6 f2-e3 h8-g7 g1-f2 g7-f6",
        "c3-d4 d6xb4 b2-c3 f6-g5 c3xa5 g7-f6 g3-f4 h8-g7 a1-b2 g5-h4 f4-g5 h6xf4 e3xg5 h4-g3 h2xf4 f6xh4 b2-c3 g7-h6 g1-h2 f8-g7",
        "c3-d4 d6xf4 g3xe5 c5-b4 h2-g3 b6-a5 e3-f4 e7-d6 g3-h4 b4-c3 d2xb4 a5xc3 b2-a3 c7-b6 e5xa5 c3xg3 a3-b4 f8-e7 b4-c5 g3-h2",
        "c3-d4 d6xf4 g3xe5 h6-g5 b2-c3 g5-h4 h2-g3 e7-d6 g3-f4 f6-g5 f4xh6 d6xf4 e3xg5 c5xe3 d2xf4 h4xf6 a1-b2 c7-d6 c1-d2 f6-g5",
        "c3-d4 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 d2-e3 f6-e5 e3-f4 g7-f6 e5xg3 h2xf4 f6-e5 f2-g3 e7-f6 g1-h2 c7-b6 a5xc7 d8xb6 e1-d2",
        "c3-d4 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 e3-f4 f6-e5 f4-g5 h6xf4 c5xa3 c1-b2 a3xe3 f2xh8 e7-f6 h8xg3 d6-e5 g3xd6 c7xe5 h2-g3",
        "c3-d4 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 g3-f4 b8-a7 a1-b2 f6-g5 g5xe3 f2xb6 a7xc5 c3-b4 g7-f6 d2-e3 f6-e5 e3-f4 e5xg3 h2xf4",
        "c3-d4 e5xc3 b2xd4 d6-c5 a1-b2 c7-d6 b2-c3 b6-a5 d4xb6 a5xc7 f6-g5 b4-c5 d6xb4 c3xa5 g5-h4 g3-f4 h8-g7 e3-d4 g7-f6 f4-g5",
        "c3-d4 e5xc3 b2xd4 d6-c5 d2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 h2-g3 a7-b6 a1-b2 b6-c5 g3-h4 f6-e5 b2-c3 g7-f6 e1-d2 b8-a7",
        "c3-d4 e5xc3 b2xd4 d6-c5 d2-c3 c7-d6 c3-b4 f6-e5 d4xf6 g7xe5 h2-g3 h8-g7 g3-h4 g7-f6 b4-a5 b8-c7 c1-d2 c5-d4 e3xc5 b6xd4",
        "c3-d4 e5xc3 b2xd4 e7-d6 d2-e3 b6-c5 d4xb6 a7xc5 e3-d4 c5xe3 f2xd4 f6-e5 d4xf6 g7xe5 c1-d2 h8-g7 e1-f2 e5-f4 g3xe5 d6xf4",
        "c3-d4 e5xc3 b2xd4 f6-e5 d4xf6 g7xe5 g3-f4 e5xg3 h2xf4 b6-c5 h8-g7 b2-c3 g7-f6 c3-b4 a7-b6 b4xd6 c7xg3 a5xc7 d8xb6 f2xh4",
        "c3-d4 e5xc3 g3-h4 c1-b2 b8-a7 b2xb6 a7xc5 b8-a7 g1-h2 a7-b6 h2-g3 c3-b2 f6-e5 d8-c7 c1-b2 a1xc3 d8-c7 c1-b2 e1-f2 f6-e5",
        "c3-d4 e7-d6 b2-c3 g5-h4 c3-b4 d6-e5 b4-a5 f6-g5 f8-e7 e3-d4 e7-f6 b2-c3 f6-e5 c3-d4 g7-f6 c1-d2 e7-d6 b4-c5 b6-a5 d2-e3",
        "c3-d4 e7-d6 d2-e3 f6-e5 d4xf6 g7xe5 b2-c3 b6-c5 e3-d4 c5xe3 f2xf6 h4xf2 e1xg3 f8-g7 a3-b4 g7xe5 c3-d4 e5xc3 b4xd2 h8-g7",
        "c3-d4 f6-e5 a1-b2 h8-g7 b2-c3 e5-f4 c3-d4 d6-c5 d2-e3 g7-f6 h2-g3 f6-g5 g3-f4 g5-h4 f2-g3 e7-f6 g3-h4 d8-e7 f4-e5 e7-d6",
        "c3-d4 f6-e5 a3-b4 a7-b6 b4-a5 b6-c5 h8-g7 e3-f4 g7-f6 e1-d2 c5-d4 b2-c3 b8-a7 d2-c3 a7-b6 c3-d4 f8-e7 g3-h4 d8-c7 h2-g3",
        "c3-d4 f6-e5 a3-b4 d6-e5 a1-b2 g5-f4 b2-c3 a7-b6 f2-e3 f8-e7 g3-f4 g7-f6 b4-a5 h8-g7 g1-f2 e7-d6 f2-g3 b8-a7 c3-d4 b6-c5",
        "c3-d4 f6-e5 b2-a3 b6-c5 a1-b2 g5-h4 g3-f4 f8-e7 c5-b4 f4-e5 g7-f6 h2-g3 h8-g7 g3-f4 g7-h6 c3-d4 b4-a3 d4-e5 a7-b6 e3-d4",
        "c3-d4 f6-e5 b2-c3 a7-b6 g3-h4 b6-a5 h8-g7 f2-e3 g7-f6 e3-f4 d6-c5 d2-e3 c5-b4 e1-d2 c7-d6 g1-h2 b8-a7 h2-g3 d6-c5 g5-h6",
        "c3-d4 f6-e5 b2-c3 f8-g7 e3-f4 e7-f6 f2-e3 f6-g5 g7-f6 h2-g3 g5-h4 g3-f4 f6-e5 g1-h2 d6-e5 a1-b2 b6-a5 e3-d4 e5-f4 d4-c5",
        "c3-d4 f6-e5 d2-c3 e5-d4 h8-g7 g7-f6 c1-b2 c7-d6 b2-c3 b6-a5 h2-g3 a7-b6 g3-h4 b8-a7 f2-e3 d6-c5 g1-f2 e7-d6 f2-g3 d8-e7",
        "c3-d4 f6-e5 d4xf6 e7xg5 a3-b4 b6-c5 b2-a3 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xe7 d8xf6 d2-e3 h8-g7 e3-f4 f6-e5 a1-b2 e5xg3",
        "c3-d4 f6-e5 d4xf6 e7xg5 a3-b4 b6-c5 b2-a3 g5-h4 g3-f4 g7-f6 h6xf4 e3xe7 d8xf6 d2-e3 h8-g7 b4-a5 f6-e5 e3-f4 e5xg3 h2xf4",
        "c3-d4 f6-e5 d4xf6 e7xg5 a3-b4 g5-h4 g3-f4 b6-a5 b2-a3 a5xc3 d2xb4 g7-f6 a1-b2 h8-g7 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 d8-e7",
        "c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 b6-a5 a1-b2 c7-b6 c3-d4 b6-c5 d4xb6 a5xc7 b2-c3 f8-e7 e3-d4 c7-b6 d2-e3 b6-a5 g3-h4 a7-b6",
        "c3-d4 f6-e5 d4xf6 e7xg5 e3-d4 g5-h4 g3-f4 d6-c5 d2-e3 g7-f6 h8-g7 c1-b2 f6-g5 f4-e5 g7-f6 e5xg7 g5-f4 e3xg5 h4xh8 f2-e3",
        "c3-d4 f6-e5 d4xf6 e7xg5 e3-d4 g7-f6 d2-e3 d6-c5 b2-c3 g5-h4 g3-f4 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-g5 b2-c3 h8-g7",
        "c3-d4 f6-e5 d4xf6 e7xg5 e3-d4 g7-f6 d2-e3 g5-h4 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 f6-g5 b2-c3 c7-d6 c5xe7 f8xd6 a1-b2 h8-g7",
        "c3-d4 f6-e5 d4xf6 e7xg5 e3-d4 g7-f6 g3-h4 f6-e5 d4xf6 g5xe7 h8-g7 b2-c3 g7-f6 f2-e3 b6-a5 e3-f4 a7-b6 g1-h2 f6-e5 d2-e3",
        "c3-d4 f6-e5 d4xf6 e7xg5 g3-f4 d8-e7 b2-c3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 e7-d6 c5xe7 f6xd8 a1-b2 c7-d6 b2-c3 a7-b6",
        "c3-d4 f6-e5 d4xf6 e7xg5 g3-f4 f8-e7 d2-c3 g7-f6 c3-d4 b6-c5 d4xb6 a7xc5 e3-d4 c5xe3 f4xd2 f6-e5 b2-c3 g5-h4 a3-b4 h6-g5",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 b6-a5 g3-h4 a5xc3 b2xf6 e7xg5 h4xf6 f8-g7 h2-g3 g7xe5 g3-h4 a7-b6 h4-g5 h6xf4 e3xg5 h8-g7",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 e7-f6 b4-a5 b6-c5 e3-f4 f6-g5 g5xe3 f2xf6 f8-g7 d2-e3 g7xe5 e3-f4 c5-d4 c1-b2 a7-b6 b2-c3",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 e7-f6 b4-a5 f6-g5 e3-d4 e5xc3 b2xd4 h8-g7 a1-b2 g7-f6 d2-e3 g5-h4 d4-c5 d6xb4 a5xc3 f6-g5",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 f8-g7 b4-a5 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b2-c3 g7-f6 c3-b4 h8-g7 a1-b2 f6-g5 d2-e3 f4xd2",
        "c3-d4 f6-e5 d4xf6 g7xe5 a3-b4 h8-g7 e3-f4 g7-f6 b4-a5 b6-c5 a7-b6 b2-a3 b8-a7 a1-b2 c5-d4 e3xc5 b6xd4 d2-c3 f6-g5 e1-d2",
        "c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 e7-f6 e3-f4 b6-a5 a1-b2 c7-b6 f2-e3 b6-c5 g3-h4 e5xg3 h2xf4 f8-g7 g1-h2 a7-b6 f4-g5 h6xf4",
        "c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 h6-g5 g3-h4 e5-f4 h4xf6 e7xg5 a1-b2 b6-c5 f2-g3 h8-g7 g3xe5 d6xf4 b4xd6 c7xe5 a3-b4 a7-b6",
        "c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 h8-g7 e3-f4 g7-f6 f2-e3 f6-g5 e5xg3 h2xf4 a7-b6 h4xf6 e7xg5 c3-d4 f8-g7 e1-f2 d6-c5 a1-b2",
        "c3-d4 f6-e5 d4xf6 g7xe5 g3-f4 e5xg3 h2xf4 h8-g7 b2-c3 d6-c5 c3-d4 b6-a5 d4xb6 a7xc5 f4-e5 c7-b6 a1-b2 b8-a7 e3-d4 c5xe3",
        "c3-d4 f6-e5 d4xf6 g7xe5 g3-h4 h8-g7 b2-c3 g7-f6 f2-g3 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6 c3-b4 a5xc3 d2xb4 b8-c7 b4-a5 d6xb4",
        "c3-d4 f6-e5 d4xf6 g7xe5 g3-h4 h8-g7 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 f2-g3 g7-f6 e1-f2 f8-g7 f2-e3 e5-f4 g3xe5 f6xb2",
        "c3-d4 f6-e5 h8-g7 b2-c3 g7-f6 c3-d4 d6-c5 f6-g5 a1-b2 e7-d6 g1-h2 f2-g3 f8-e7 e7-d6 e1-f2 f2-g3 d8-e7 e7-d6 e5-f6 h2-g3",
        "c3-d4 f6-g5 b2-c3 b6-a5 a1-b2 g5-h4 g3-f4 g7-f6 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 h8-g7 c3-d4 g7-f6 f4-g5 h6xf4 f2-g3 h4xf2",
        "c3-d4 f6-g5 b2-c3 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 c3-b4 a5xc3 d2xb4 d6-e5 g3-f4 e5xg3",
        "c3-d4 f6-g5 b2-c3 b6-a5 d4-c5 d6xb4 a3xc5 g5-h4 a1-b2 g7-f6 f6-g5 b2-a3 h8-g7 c3-d4 c7-b6 d2-c3 b8-c7 f2-g3 h4xf2 e1xg3",
        "c3-d4 f6-g5 b2-c3 b6-a5 d4-c5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 f6-e5 g5-h6 h8-g7 a1-b2",
        "c3-d4 f6-g5 b2-c3 b6-a5 d4-c5 d6xb4 a3xc5 g7-f6 a1-b2 g5-h4 c3-d4 h8-g7 b2-a3 c7-b6 e3-f4 d8-c7 d2-c3 f6-g5 f2-e3 h4xf2",
        "c3-d4 f6-g5 b2-c3 b6-c5 d4xb6 c7xa5 a1-b2 a7-b6 c3-d4 d6-c5 b2-c3 g5-h4 g3-f4 b8-a7 h2-g3 e7-d6 g1-h2 f8-e7 f4-e5 d6xf4",
        "c3-d4 f6-g5 b2-c3 d6-c5 c1-b2 g7-f6 c3-b4 g5-h4 b4xd6 c7xc3 d2xb4 b6-a5 g3-f4 a5xc3 b2xd4 f6-g5 a3-b4 d8-c7 d4-c5 e7-f6",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 a7-b6 b2xd4 b6-a5 a1-b2 d8-c7 a3-b4 a5xa1 g3-f4 a1xg3 f2xb6",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-b2 a7-b6 b2xd4 b6-a5 a1-b2 d8-c7 a3-b4 a5xa1 g3-f4 a1xg3",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-b2 a7-b6 b2xd4 b6-a5 a1-b2 d8-c7 d4-c5 e7-d6 c5xe7 f8xd6",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c3-d2 e3xc1 g5-h4 g3-f4 g7-f6 b2-c3 a7-b6 a1-b2 b6-c5 f2-g3",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 e3-f4 g5xe3 f2xb2 h6-g5 b2-c3 e7-d6 a3-b4 g7-f6 b4-a5 f6-e5",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 a7-b6 b2xd4 b6-a5 a1-b2 g5-h4 g3-f4 g7-f6 e1-d2 f6-g5 d4-c5",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 a7-b6 b2xd4 b6-a5 g3-f4 g5-h4 e1-d2 d8-c7 a1-b2 b8-a7 b2-c3",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 a7-b6 b2xd4 b6-a5 g3-f4 g7-f6 h2-g3 g5-h4 f4-e5 f6-g5 g3-f4",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c1-b2 a7-b6 b2xd4 b6-a5 g3-f4 g5-h4 e1-d2 d8-c7 a1-b2 b8-a7",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c3-d2 e3xc1 g7-f6 b2-c3 g5-h4 a3-b4 f6-e5 b4-a5 h8-g7 g3-f4",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 e7-f6 b4xd6 c7xc3 d2xb4 f6-e5 g5-f4 a5xc7 b8xd6 e3xg5 h6xf4 f2-e3 f4xd2 c1xe3 a7-b6 a1-b2",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 g7-f6 b4xd6 c7xc3 d2xb4 f6-e5 e5xg3 f2xf6 e7xg5 h2-g3 h8-g7 g3-f4 g7-f6 b4-a5 f8-e7 a5xc7",
        "c3-d4 f6-g5 b2-c3 d6-c5 c3-b4 g7-f6 b4xd6 c7xc3 d2xb4 h8-g7 b6-c5 g3-h4 g5-f4 e3xg5 h6xf4 a5-b6 f4-g3 h2xf4 g7-h6 b6xd4",
        "c3-d4 f6-g5 b2-c3 d6-c5 g3-f4 g7-f6 c1-b2 e7-d6 c3-b4 d6-e5 b4xd6 e5xg3 h2xf4 c7xc3 b2xd4 b6-a5 a1-b2 d8-c7 d2-c3 g5-h4",
        "c3-d4 f6-g5 b2-c3 e7-f6 a1-b2 f8-e7 g3-h4 d6-c5 c3-b4 c7-d6 b6-a5 d4xb6 a5xc7 e3-d4 d6-e5 b4-c5 c7-d6 a3-b4 g5-f4 f2-e3",
        "c3-d4 f6-g5 b2-c3 e7-f6 c1-b2 g5-h4 d4-c5 d6xb4 c3xa5 b6-c5 b2-c3 h6-g5 g3-f4 g7-h6 c3-d4 c7-b6 a5xc7 d8xb6 d2-c3 b6-a5",
        "c3-d4 f6-g5 b2-c3 e7-f6 g3-f4 d8-e7 f2-g3 g5-h4 a1-b2 h4xf2 e1xg3 d6-e5 f4xd6 e7xc5 g3-h4 c7-d6 h4-g5 f6xh4 h2-g3 h4xf2",
        "c3-d4 f6-g5 b2-c3 e7-f6 g3-h4 f8-e7 a1-b2 d6-c5 c3-b4 b6-a5 b4xf8 a5-b4 a3xc5 d8-e7 f8xd6 c7xa1 c5-d6 a7-b6 d6-e7 f6xd8",
        "c3-d4 f6-g5 b2-c3 e7-f6 g3-h4 f8-e7 a1-b2 d6-c5 c3-b4 c7-d6 b2-c3 b6-a5 d4xb6 a5xc7 c3-d4 g5-f4 e3xg5 h6xf4 d4-c5 f6-e5",
        "c3-d4 f6-g5 b2-c3 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 a1-b2 b6-c5 d4xb6 a7xc5 c3-d4 c5xe3 f2xd4 g7-f6 b2-c3 h8-g7 e1-f2 f6-g5",
        "c3-d4 f6-g5 b2-c3 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 a3-b4 f4-e3 d2xf4 b6-c5 d4xb6 a7xa3 c3-d4 g7-f6 f4-e5 f6-g5 a1-b2 h8-g7",
        "c3-d4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 a1-b2 b6-c5 d4xb6 a7xc5 c3-d4 c5xe3 f2xd4 g7-f6 b2-c3 h8-g7 a3-b4 g7-h6",
        "c3-d4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-b4 g7-f6 b6-c5 d4xb6 a7xc5 a1-b2 c7-d6 b2-c3 f6-e5 f2-e3 h8-g7 e3xg5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c1-b2 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 f6-g5 e3-d4 g5-f4 g3xe5 d6xf4 b2-c3 h6-g5 e1-d2 e7-f6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 a1-b2 f6-g5 b4-a5 d6xb4 a5xc3 a7-b6 c3-d4 h8-g7 d4-c5 b6xd4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 h8-g7 g3-f4 f6-e5 f4xd6 c7xe5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 b4-a5 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 a1-b2 h8-g7 g3-f4 f6-g5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 b4-a5 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 g3-f4 f6-g5 a1-b2 c7-b6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 b4-a5 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 g3-f4 h8-g7 a1-b2 f6-g5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 c1-d2 f6-g5 b4-a5 d6xb4 a5xc3 a7-b6 a3-b4 b6-c5 b4xd6 e7xc5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 c7-b6 a1-b2 b6xd4 e3xc5 f6-g5 b4-a5 d6xb4 a5xc3 g5xe3 f2xd4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 a1-b2 b6-a5 c3-d4 f6-g5 b2-c3 c7-b6 g3-f4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 a3-b4 b6-a5 a1-b2 h8-g7 b2-a3 c7-b6 e3-d4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 c3-b4 f6-e5 b4-a5 e7-d6 g3-f4 e5xg3 h2xf4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 c3-b4 f6-g5 b4-a5 h8-g7 a1-b2 e7-d6 g3-f4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 c3-b4 h8-g7 g3-f4 f6-e5 f4xd6 c7xe5 b4-c5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 a1-b2 h8-g7 b2-c3 c7-b6 g3-f4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 a1-b2 h8-g7 g3-f4 f6-g5 b2-c3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 g3-f4 f6-g5 a1-b2 c7-b6 b2-c3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 g3-f4 f6-g5 a1-b2 e7-d6 d4-e5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 g3-f4 h8-g7 a1-b2 f6-g5 b2-c3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 f6-e5 g3-f4 e5xg3 h2xf4 h8-g7 c3-d4 g7-f6 c1-d2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 h8-g7 b4-a5 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 b2-c3 c7-b6 c1-b2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-c5 b4xd6 c7xc3 d2xb4 b6-a5 a5xc3 b2xd4 g7-f6 a1-b2 d8-c7 d4-c5 f6-e5 g3-f4 e5xg3 h2xf4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-c5 b4xd6 c7xc3 d2xb4 d8-c7 b6-c5 a1-b2 g7-f6 g3-f4 h8-g7 c1-d2 f6-g5 d2-c3 a7-b6 c3-d4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 b4-a5 h8-g7 d2-c3 g7-f6 a3-b4 f6-g5 c3-d4 e5xc3 b4xd2 b6-c5 a1-b2 f8-g7",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 b4-a5 h8-g7 e7-d6 b4-c5 b6xd4 e3xe7 f8xd6 a1-b2 g7-f6 d2-e3 a7-b6 b2-c3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 b4-a5 h8-g7 g7-f6 d2-c3 e7-d6 c3-d4 e5xc3 b4xd2 f6-e5 a1-b2 e5-f4 g3xe5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 b4-a5 h8-g7 g7-f6 d2-c3 e7-d6 c3-d4 e5xc3 b4xd2 f6-g5 a1-b2 g5-f4 e3xg5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 d2-c3 e7-d6 e5-f4 e3xg5 h4xf6 a1-b2 h8-g7 g3-h4 f6-e5 a3-b4 e5-f4 f2-e3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 d6-e5 d4xf6 g7xe5 d2-c3 h8-g7 e7-d6 e3-d4 g7-f6 c3-b4 e5xc3 b4xd2 f6-g5 a1-b2 b6-c5 b2-c3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 e3-f4 f6-e5 d2-c3 c5-b4 a3xc5 d6xd2 f4xd6 e7xc5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 g3-f4 b8-a7 f4-g5 h6xf4 e3xg5 g7-h6 b2-c3 h6xf4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 g3-f4 b8-a7 h2-g3 f6-e5 b2-c3 g7-f6 c3-b4 f6-g5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 g3-f4 f6-g5 b2-c3 e7-f6 c3-b4 f6-e5 d2-c3 e5xg3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 g3-f4 f6-g5 d2-c3 c5-b4 a3xc5 d6xd2 e1xc3 e7-d6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 f6-e5 g3-f4 e5xg3 h2xf4 h8-g7 b2-c3 g7-f6 c3-d4 f6-g5 d4xb6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 g3-f4 h8-g7 f4-g5 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h4-g3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 b6-c5 d4xb6 a7xc5 h8-g7 g3-f4 f6-g5 d2-c3 c5-b4 a3xc5 d6xd2 e1xc3 e7-d6 h2-g3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-a5 f6-g5 g3-f4 b6-c5 d4xb6 a7xc5 a1-b2 e7-f6 d2-c3 f6-e5 c3-b4 e5xg3 h2xf4 d6-e5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 b6-a5 c7-b6 e3-f4 f6-g5 b2-c3 g5xe3 d2xf4 d8-c7 f4-e5 c7-d6 e5xc7",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 b6-a5 g3-f4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 e7-d6 a1-b2 b4-a3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 f6-g5 e7-f6 d2-c3 d8-e7 g3-f4 h8-g7 e1-d2 e7-d6 c5xe7 f6xd8 f4-e5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 f6-g5 e7-f6 d2-c3 f6-e5 d4xf6 g5xe7 e1-d2 b6xd4 e3xc5 c7-b6 c3-d4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 f6-g5 e7-f6 d2-c3 f6-e5 d4xf6 g5xe7 g3-f4 b6xd4 e3xc5 c7-b6 c3-d4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 h8-g7 f6-g5 a1-b2 e7-d6 c5xe7 f8xd6 b2-a3 b6-a5 d2-c3 a7-b6 d4-e5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 h8-g7 g3-f4 f6-g5 a1-b2 e7-d6 c5xe7 f8xd6 b2-a3 b6-a5 d2-c3 a7-b6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 c1-b2 b6-a5 d4-c5 a5xc3 d2xb4 f6-g5 b4-a5 d6xb4 a5xc3 e7-d6 a3-b4 g5-f4 g3xe5 d6xd2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4 a5xc3 a7-b6 c1-d2 e7-d6 d2-e3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 f6-e5 a1-b2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 f6-e5 b4-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 h8-g7 b4-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 h6-g5 b4-a5 d6xb4 a5xc3 a7-b6 a3-b4 e7-d6 b4-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 h6-g5 b4-a5 d6xb4 a5xc3 e7-d6 c1-d2 f6-e5 d2-e3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 h6-g5 b4-a5 d6xb4 a5xc3 h8-g7 a3-b4 e7-d6 a1-b2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4 a5xc3 a7-b6 a1-b2 h8-g7",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 h8-g7",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4 a5xc3 a7-b6 g3-f4 f6-e5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 d8-c7 c1-d2 f6-e5 g3-f4 e5xg3 h2xf4 h8-g7",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 d8-c7 c1-d2 f6-g5 a1-b2 d6-e5 d2-e3 g5-f4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 c1-d2 f6-e5 d2-e3 g5-f4 e3xg5 h4xf6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 g3-f4 b6xd4 d2-e3 h4-g3 f2xh4 d4xf2 g1xe3 a7-b6 a1-b2 f6-g5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 f6-e5 a1-b2 h8-g7 b4-a5 d6xb4 a5xc3 e7-d6 a3-b4 a7-b6 b2-a3 g7-f6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 f6-e5 b4-a5 d6xb4 a5xc3 h8-g7 g3-f4 e5xg3 h2xf4 g7-f6 c3-d4 e7-d6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 f6-g5 d6xb4 a5xc3 a7-b6 c3-b4 e7-d6 b4-a5 d6-e5 a3-b4 g5-f4 d2-e3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 h8-g7 d6xb4 a5xc3 a7-b6 c3-d4 e7-d6 a3-b4 b6-c5 d4xb6 c7xc3 d2xb4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 h8-g7 d6xb4 a5xc3 f6-e5 c3-b4 g7-f6 d2-e3 f6-g5 g3-f4 e5xg3 h2xf4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d4-c5 b6xd4 e3xc5 h8-g7 f6-g5 b4-a5 d6xb4 a5xc3 g7-f6 c3-d4 e7-d6 d4-c5 d6xb4 a3xc5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-a5 g5-f4 e3xg5 h4xf6 b6-c5 d4xb6 a7xc5 e3-f4 f6-e5 f2-e3 g7-f6 g3-h4 e5xg3 h4xf2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-a5 g5-f4 e3xg5 h4xf6 f2-e3 g7-h6 a1-b2 h6-g5 b2-c3 g5-h4 e3-f4 h4xf2 g1xe3 h8-g7",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-a5 g5-f4 g3xe5 d6xf4 e3xg5 h4xf6 a1-b2 f6-g5 b2-c3 g5-h4 c3-b4 g7-f6 d2-e3 b6-c5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 g3-f4 d6xb4 f4xh6 b6-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 c7-d6 a1-b2 d6xb4 b2-a3 e7-f6 a3xc5 f6-e5 d4xf6 g5xe7 g3-f4 b6xd4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 c7-d6 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 g3-f4 d6xb4 f4xh6 b6-a5 e3-f4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 c7-d6 d6xb4 f4xh6 b6-a5 d4-e5 g7-f6 e5xg7 h8xf6 d2-c3 b4xf4 f2-g3",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 c7-d6 d6xb4 f4xh6 b6-a5 h2-g3 a7-b6 g3-f4 b6-c5 d4xb6 a5xc7 a1-b2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 c7-d6 d6xb4 f4xh6 b6-a5 h2-g3 a7-b6 g3-f4 b8-a7 g1-h2 b4-a3 a1-b2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 c7-d6 d6xb4 f4xh6 b6-a5 h2-g3 b8-c7 g3-f4 c7-d6 d4-e5 d6-c5 e5-d6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 e7-f6 g7-h6 f4-e5 f8-e7 e5xg7 h6xf8 h2-g3 h8-g7 g3-f4 g7-h6 a1-b2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 g7-h6 e7-f6 d2-c3 f6-e5 d4xf6 b6xd4 e3xc5 g5xe7 g3-f4 c7-b6 c3-d4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4 a5xc3 e7-d6 a3-b4 a7-b6 b4-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 a1-b2 h8-g7 b4-a5 d6xb4 a5xc3 a7-b6 g3-f4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 a1-b2 h8-g7 b4-a5 d6xb4 a5xc3 e7-d6 a3-b4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 a1-b2 h8-g7 g3-f4 g5xe3 f2xd4 g7-h6 b4-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 b4-a5 d6xb4 a5xc3 a7-b6 a3-b4 e7-d6 b4-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 b4-a5 d6xb4 a5xc3 a7-b6 c1-d2 f6-e5 c3-d4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 b4-a5 d6xb4 a5xc3 e7-d6 a3-b4 d8-e7 b4-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 b4-a5 d6xb4 a5xc3 h8-g7 a3-b4 e7-d6 a1-b2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 b4-a5 d6xb4 a5xc3 h8-g7 a3-b4 e7-d6 b4-a5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 b4-a5 d6xb4 a5xc3 h8-g7 c3-d4 e7-d6 a1-b2",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 g7-f6 b4-a5 d6xb4 a5xc3 h8-g7 g3-f4 g5xe3 f2xd4",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 g7-f6 a1-b2 h8-g7 b4-a5 d6xb4 a5xc3 a7-b6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 g7-f6 b4-a5 d6xb4 a5xc3 h8-g7 a3-b4 e7-d6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 g7-f6 c1-d2 f6-e5 d2-e3 g5-f4 e3xg5 h4xf6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 g5-f4 g3xe5 d6xf4 a1-b2 g7-h6 b2-c3 h6-g5 c3-d4 h8-g7 f2-e3 e7-d6",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 g5-f4 g3xe5 d6xf4 d2-e3 f4xd2 c1xe3 g7-h6 h2-g3 e7-f6 a1-b2 f6-g5",
        "c3-d4 f6-g5 b2-c3 g5-h4 c3-b4 h6-g5 d4-c5 b6xd4 e3xc5 g7-f6 h8-g7 g3-f4 g7-h6 c1-b2 c7-b6 f4-e5 d6xd2 e1xc3 b6xd4 c3xg7",
        "c3-d4 f6-g5 b2-c3 g5-h4 g3-f4 b6-a5 d4-c5 d6xb4 a3xc5 e7-f6 f6-g5 f4-e5 c7-b6 c5-d6 d8-c7 b2-a3 g5-f4 e5xg3 c7xe5 g3-f4",
        "c3-d4 f6-g5 b2-c3 g5-h4 g3-f4 b6-c5 d4xb6 a7xc5 a1-b2 g7-f6 h8-g7 b4-a5 f6-g5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 d4-e5",
        "c3-d4 f6-g5 b2-c3 g5-h4 g3-f4 d6-c5 c1-b2 g7-f6 c3-b4 f6-g5 b4xd6 c7xc3 b2xd4 b6-a5 d2-c3 e7-d6 d4-e5 d6-c5 c3-d4 a7-b6",
        "c3-d4 f6-g5 b2-c3 g5-h4 g3-f4 d6-c5 c1-b2 g7-f6 c3-b4 f6-g5 b4xd6 c7xg3 h2xf4 e7-d6 b2-c3 d6-c5 f4-e5 b6-a5 d4xb6 a5xc7",
        "c3-d4 f6-g5 b2-c3 g5-h4 g3-f4 d6-c5 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-d2 a7-b6 d2xb4 b6-a5 b4-c5 g7-f6 a1-b2 b8-a7",
        "c3-d4 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 d6-c5 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5 g5-h6 e5-f4 e3xg5",
        "c3-d4 f6-g5 b2-c3 g7-f6 a1-b2 b6-a5 d4-e5 d6xf4 g3xg7 h8xf6 h2-g3 g5-h4 g3-f4 f6-g5 c3-d4 e7-f6 d2-c3 c7-d6 d4-e5 f6xd4",
        "c3-d4 f6-g5 b2-c3 g7-f6 a1-b2 d6-c5 g3-h4 e7-d6 f2-g3 f6-e5 h4xf6 e5xg7 g3-f4 b6-a5 d4xb6 a7xc5 h2-g3 g7-f6 g3-h4 f6-g5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 f6-e5 d4xf6 e7xg5 e3-d4 g5xe3 d2xf4 f8-e7 c1-b2 c7-d6 b2-a3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 e7-d6 a1-b2 b4-a3 b2-c3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g5-h4 d6xb4 a5xc3 a7-b6 c1-d2 h8-g7 a3-b4 f6-e5 e3-d4 g7-f6 b4-a5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 g5-h4 h8-g7 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 b6-a5 b4-c5 f6-e5 g3-f4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 b4-a5 d6xb4 a5xc3 g5-f4 g3xe5 f6xb2 a1xc3 a7-b6 c3-d4 b6-a5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 b4-a5 d6xb4 a5xc3 g5-f4 g3xe5 f6xb2 a1xc3 a7-b6 h2-g3 g7-f6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 c7-b6 b4-a5 b6xd4 e3xc5 d6xb4 a5xc3 g5xe3 f2xd4 a7-b6 a3-b4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 c7-b6 b4-a5 b6xd4 e3xc5 d6xb4 a5xc3 g5xe3 f2xd4 a7-b6 h2-g3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 c7-b6 b4-a5 d6xb4 a5xc3 b6-c5 e3-d4 c5xe3 f4xd2 f6-e5 f2-g3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 d6xb4 a5xc3 g5-f4 g3xe5 f6xb2 a1xc3 a7-b6 c3-d4 b6-a5 h2-g3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 d6xb4 a5xc3 g5-f4 g3xe5 f6xb2 a1xc3 a7-b6 h2-g3 g7-f6 g3-f4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 d6xb4 a5xc3 g5-f4 g3xe5 f6xb2 a1xc3 a7-b6 h2-g3 g7-f6 g3-h4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 d2xb4 h8-g7 g3-f4 c7-b6 b4-a5 b6xd4 e3xc5 g5xe3 f2xd4 d6xb4 a5xc3 a7-b6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xc3 d2xb4 d6-e5 e5xg3 h2xf4 d8-c7 a1-b2 h8-g7 b4-c5 c7-b6 e1-d2 b6xd4 e3xc5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xc3 d2xb4 h8-g7 a1-b2 d8-c7 e3-f4 g5xe3 f2xd4 h6-g5 g3-h4 d6-e5 b2-c3 c7-b6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xc3 d2xb4 h8-g7 b4-a5 d6-e5 d8-c7 e3-d4 g5-h4 d4-c5 a3-b4 h6-g5 b4-c5 d6xb4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xc3 d2xb4 h8-g7 d8-c7 a1-b2 g5-h4 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 c1-b2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xc3 d2xb4 h8-g7 d8-c7 b2-c3 e3-d4 e3-f4 g5xe3 f2xd4 c7-b6 d6-e5 b2-c3 h6-g5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xc3 d2xb4 h8-g7 d8-c7 b4-a5 d6-e5 a3-b4 a7-b6 b2-a3 g5-f4 e3xg5 h6xf4 g3-h4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xc3 d2xb4 h8-g7 e3-d4 d6-e5 b4-c5 e5xc3 g3-h4 d8-c7 e7-d6 c5xe7 f8xd6 c1-d2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 b6-c5 d4xb6 c7xc3 d2xb4 h8-g7 g3-f4 d8-c7 g5-h4 a1-b2 c1-d2 d8-c7 d2-c3 f6-g5 c3-d4 f6-g5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 d6-e5 b4-a5 e5xc3 d2xb4 g5-h4 f6-g5 c1-d2 e7-f6 d2-e3 f6-e5 d4xf6 g5xe7 a1-b2 h8-g7 e3-d4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 d6-e5 b4-a5 e5xc3 d2xb4 g5-h4 f6-g5 e3-d4 e7-f6 c1-d2 f6-e5 d4xf6 g5xe7 b2-c3 h8-g7 c3-d4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 d6-e5 b4-a5 e5xc3 d2xb4 g5-h4 h8-g7 g3-f4 f6-g5 a1-b2 e7-d6 b2-c3 g7-f6 c3-d4 d6-e5 f4xd6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 d6-e5 d2-c3 g5-h4 b4-a5 e7-d6 e5xc3 b4xd2 h8-g7 a1-b2 f6-g5 g3-f4 b6-c5 b2-c3 g7-f6 h2-g3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 f8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 b2-c3 f6-e5 d4xf6 e7xg5 c5-d6 c7xe5 e3-f4 g5xe3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 g3-f4 b8-a7 f4-g5 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 b4-a5 b6-c5 d4xb6 a7xc5 h8-g7 g3-f4 b8-a7 h2-g3 f6-e5 b2-c3 g7-f6 c3-b4 f6-g5 d2-c3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 b4-c5 d6xb4 a3xc5 b6-a5 c7-b6 g3-f4 f6-g5 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6 f2-g3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 b4-c5 d6xb4 a3xc5 h8-g7 f6-g5 a1-b2 b6-a5 c5-b6 a7xc5 d4xb6 e7-d6 d2-c3 f8-e7 c3-d4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 d8-c7 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 h8-g7 b4-a5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 h6-g5 b4-a5 d6xb4 a5xc3 a7-b6 a1-b2 h8-g7 g3-f4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 h6-g5 b4-a5 d6xb4 a5xc3 a7-b6 a3-b4 b6-a5 b4-c5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 h6-g5 b4-a5 d6xb4 a5xc3 h8-g7 a3-b4 e7-d6 b4-a5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 c1-d2 f6-e5 b4-a5 d6xb4 a5xc3 a7-b6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 g5-h4 d4-c5 b6xd4 e3xc5 f6-e5 b4-a5 d6xb4 a5xc3 h8-g7 g3-f4 e5xg3 h2xf4 g7-f6 c3-d4 e7-d6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-a5 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 a3-b4 b6-c5 b4xd6 c7xc3 d2xb4 d8-c7 f2-e3 f4xd2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 b2-a3 c7-b6 d2-c3 f6-g5 g3-f4 d8-c7 f2-g3 h4xf2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 b2-a3 c7-b6 e3-f4 d8-c7 d2-c3 f6-g5 f2-e3 h4xf2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 b2-a3 c7-b6 e3-f4 d8-c7 f4-g5 h6xf4 g3xe5 f6-g5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 b2-a3 c7-b6 g3-f4 f6-g5 d2-c3 d8-c7 f2-g3 h4xf2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 g3-f4 f6-g5 b2-a3 c7-b6 d2-c3 e7-d6 c5xe7 f8xd6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 g3-f4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 b4-a3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 g3-f4 f6-g5 f4-e5 g7-f6 e5xg7 g5-f4 e3xg5 h4xh8",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 b2-a3 g7-f6 g3-f4 b6-a5 f4-e5 c7-b6 e5xg7 g5-f4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 b2-c3 b6-a5 c3-b4 a5xe5 e3-f4 g5xe3 f2xh8 h4xf2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 b2-c3 c7-d6 c3-b4 b6-a5 e3-f4 a5xe5 c5-b6 a7xc5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 b2-c3 g7-f6 g3-f4 b6-a5 f2-g3 h4xf2 e1xg3 g5-h4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 g3-f4 e7-d6 c5xe7 f8xd6 d2-c3 b6-a5 d4-e5 a7-b6",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 f6-g5 g3-f4 e7-d6 c5xe7 f8xd6 f2-g3 h4xf2 e1xg3 b6-c5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 b6-a5 a1-b2 f6-g5 f2-g3 h4xf2 e1xg3 g5-h4 g1-f2 c7-b6 b2-c3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 b6-a5 g3-f4 c7-d6 b2-a3 d6xb4 a3xc5 f6-g5 f2-g3 h4xf2 e1xg3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 b2-a3 g7-f6 g3-f4 b6-a5 f4-e5 c7-b6 e5xg7 g5-f4 e3xg5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 b2-c3 b6-a5 c3-b4 a5xe5 e3-f4 g5xe3 f2xh8 h4xf2 g1xe3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 b2-c3 c7-d6 c3-b4 b6-a5 e3-f4 a5xe5 c5-b6 a7xc5 d2-c3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 b2-c3 e7-d6 c5xe7 f8xd6 d4-e5 d6xf4 g3xe5 b6-c5 e3-d4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 b2-c3 e7-f6 c1-b2 d8-e7 g3-f4 e7-d6 c5xe7 f8xd6 f4-e5",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 b2-c3 g7-f6 g3-f4 b6-a5 f2-g3 h4xf2 e1xg3 c7-b6 g3-h4",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 b2-c3 g7-f6 g3-f4 b6-a5 f2-g3 h4xf2 e1xg3 g5-h4 c1-b2",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 g3-f4 b6-a5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 b4-a3 d2-c3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 g3-f4 e7-d6 c5xe7 f8xd6 d2-c3 b6-a5 d4-e5 a7-b6 b2-a3",
        "c3-d4 f6-g5 b2-c3 g7-f6 c3-b4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 f6-g5 a1-b2 c7-d6 b2-c3 d6xb4 c3xc7 b8xd6 d2-c3 a7-b6",
        "c3-d4 f6-g5 b6-c5 a1-b2 h8-g7 g7-f6 c3-b4 c7-b6 d2-c3 b6-a5 g3-h4 d8-e7 e3-f4 e7-d6 f2-e3 f6-e5 h2-g3 b8-a7 g1-h2 a7-b6",
        "c3-d4 f6-g5 d2-c3 b6-a5 c1-d2 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 h8-g7 g5-h6 c7-b6 d4-c5 d6xb4 a3xc5 b6xd4 c3xe5 f6xd4",
        "c3-d4 f6-g5 d2-c3 d6-c5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 f8-g7 f4-g5 h6xf4 e3xg5 c5xe3 d2xf4 g7-h6",
        "c3-d4 f6-g5 d2-c3 d6-c5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 f8-g7 f4-g5 h6xf4 e3xg5 c5xe3 f2xd4 f2xd4",
        "c3-d4 f6-g5 d2-c3 d6-c5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 f8-g7 f4-g5 h6xf4 e3xg5 c5xe3 f2xd4 f6-e5",
        "c3-d4 f6-g5 d2-c3 d6-c5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 b2-c3 f8-g7 f4-g5 h6xf4 e3xg5 c5xe3 f2xd4 g7-h6",
        "c3-d4 f6-g5 d2-c3 d6-c5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5-h4 e1-d2 g7-f6 h2-g3 f8-g7 f8-g7 d4-e5 f6xd4 g1-h2 g7-f6 f4-e5",
        "c3-d4 f6-g5 d2-c3 d6-c5 c3-b4 e7-d6 b4-a5 g5-h4 b2-c3 d8-e7 h6-g5 g3-f4 g7-h6 c1-b2 e7-f6 b2-c3 f6-e5 d4xf6 g5xe7 e1-d2",
        "c3-d4 f6-g5 d2-c3 g5-h4 c1-d2 d6-c5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g7-f6 h2-g3 f8-g7 d4-e5 f6xd4 g1-h2 g1-h2 d4-c3 b2xd4",
        "c3-d4 f6-g5 d2-c3 g5-h4 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 b6-a5 f6-g5 c1-d2 c7-b6 b2-c3 d8-c7 a1-b2 c7-d6 b2-a3 d6xb4 a3xc5",
        "c3-d4 f6-g5 d2-c3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 g7-h6 g3-f4 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 c7-d6 b2-a3 d6xb4",
        "c3-d4 f6-g5 d2-c3 g7-f6 c1-d2 g5-h4 d4-c5 b6xd4 c3xg7 h8xf6 f6-g5 d2-c3 g5-f4 e3xg5 h4xf6 g3-h4 f6-e5 b4-a5 a7-b6 c3-d4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 e7-f6 d2-e3 d8-e7 g3-f4 e7-d6 c5xe7 f6xd8 b2-c3 a7-b6 a1-b2 f8-e7 c3-b4 e7-d6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 e7-f6 d2-e3 d8-e7 g5xe3 f2xd4 h6-g5 b2-c3 e7-d6 c5xe7 f6xd8 a1-b2 c7-d6 c1-d2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 e7-f6 f2-e3 d8-e7 e7-d6 c5xe7 f6xd8 b2-c3 g5-h4 a1-b2 h4xf2 g1xe3 h6-g5 h2-g3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 e7-f6 f2-e3 g5-h4 g3-f4 h4-g3 f4-g5 h6xf4 e3xe7 f8xb4 h2xf4 b4-a3 d2-e3 g7-f6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 e7-f6 g3-f4 g5xe3 d2xf4 f6-g5 h2-g3 g5xe3 f2xd4 h6-g5 b2-c3 g7-f6 a1-b2 h8-g7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 d2-e3 c5-b4 e3-f4 f8-e7 f2-g3 b4-a3 e1-d2 b6-a5",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 b2-c3 a5-b4 c3xa5 a7-b6 a5xc7 b8xf4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 h2-g3 a7-b6 g3-f4 d8-e7 g1-f2 e7-d6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 h2-g3 d8-e7 e5-d6 c5-b4 b2-a3 e7xc5",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 b2-c3 b4-a3 h2-g3 b8-c7 e5-f6 g7xe5",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 b2-c3 b6-a5 h2-g3 f8-e7 a1-b2 b8-c7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 b2-c3 b6-a5 h2-g3 f8-e7 e3-f4 b8-c7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 b6-a5 b2-a3 f8-e7 a3xc5 e7-d6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 f8-e7 g3-f4 b6-a5 b2-c3 g7-f6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 f8-e7 g3-f4 b6-a5 g1-f2 a7-b6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 f2-e3 a7-b6 e3-f4 c5-b4 g1-f2 f8-e7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 f2-e3 a7-b6 g3-f4 c5-b4 b2-c3 f8-e7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 c5-b4 b2-c3 f8-e7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 d8-e7 g1-f2 e7-d6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 d2-c3 a7-b6 f2-e3 b8-a7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-e3 a7-b6 g1-f2 c5-b4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-e3 a7-b6 g1-f2 e7-d6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 a7-b6 g1-f2 c5-b4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 a7-b6 g3-h4 c5-b4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 e5-d6 b4-a3 b2-c3 b6-a5 f2-e3 a7-b6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 e5-d6 b4-a3 b2-c3 b6-a5 f2-e3 g7-f6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 e5-d6 h6-g5 b2-c3 b4-a3 f2-e3 b6-a5",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 f2-e3 b4-a3 b2-c3 b6-a5 e3-f4 d8-e7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 f2-e3 f8-e7 e3-f4 b6-a5 b2-c3 a7-b6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 f2-e3 f8-e7 g1-f2 b4-a3 g3-f4 g7-f6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 f2-e3 f8-e7 g3-f4 b6-a5 b2-c3 b8-c7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 b2-c3 b6-a5 f2-g3 d8-e7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 b2-c3 f8-e7 c3-b4 a3xc5",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 f2-e3 b6-a5 g1-f2 d8-c7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 a7-b6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 b8-c7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 g7-f6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-g3 a7-b6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 g1-h2 b8-c7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 d2-c3 b4xd2 e1xc3 g7-f6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 f2-e3 b4-a3 g1-f2 b8-c7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 f2-e3 b6-a5 b2-c3 a7-b6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 b6-a5 h2-g3 a7-b6 e3-f4 c5-b4 g1-h2 f8-e7 b2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 c5-b4 b2-c3 b4-a3 h2-g3 b8-c7 e5-f6 g7xe5 c3-b4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 c5-b4 b2-c3 b6-a5 h2-g3 f8-e7 e3-f4 b8-c7 g1-f2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 c5-b4 h2-g3 b6-a5 b2-a3 f8-e7 a3xc5 e7-d6 c5xe7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 f2-e3 a7-b6 e3-f4 c5-b4 g1-f2 f8-e7 b2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 c5-b4 b2-c3 b4-a3 g1-f2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 c5-b4 b2-c3 f8-e7 g1-f2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 d8-e7 g1-f2 c5-b4 b2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-g3 c5-b4 d2-c3 b4xd2 e1xc3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 d2-c3 a7-b6 f2-e3 b8-a7 e3-d4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-e3 a7-b6 g1-f2 c5-b4 b2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-e3 e7-f6 g1-f2 f6xd4 d2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 a7-b6 g1-f2 c5-b4 b2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 a7-b6 g1-h2 c5-b4 b2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 a7-b6 g3-h4 c5-b4 g1-f2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 a7-b6 g3-h4 e7-f6 d2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 c5-b4 b2-c3 b4-a3 a1-b2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 e5-d6 b4-a3 b2-c3 b6-a5 f2-e3 a7-b6 e3-d4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 e5-d6 b4-a3 b2-c3 b6-a5 f2-e3 g7-f6 e3-d4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 e5-d6 h6-g5 b2-c3 b4-a3 f2-e3 b6-a5 g1-h2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 b2-c3 b6-a5 f2-e3 b8-c7 g1-h2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 f2-e3 b6-a5 g1-f2 d8-c7 f2-g3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 f2-g3 b6-a5 b2-c3 d8-c7 g1-f2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 a7-b6 g1-f2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 b8-c7 a1-b2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 b8-c7 g1-f2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 g7-f6 e5xg7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-g3 a7-b6 g1-f2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 f2-e3 b4-a3 g1-f2 b8-c7 b2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 f2-g3 b4-a3 b2-c3 g7-f6 e5xg7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 e7-f6 c7xe5 b2-c3 h6-g5 a1-b2 d8-c7 c3-b4 f8-e7 b2-a3 e7-d6 c5xe7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 c7-b6 c3-d4 d8-c7 a1-b2 h6-g5 b2-a3 g7-h6 a3-b4 h8-g7 b4-a5 e7-f6",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 c7-b6 d8-c7 a1-b2 h6-g5 b2-a3 g7-h6 a3-b4 h8-g7 b4-a5 e7-f6 d2-c3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 c3-d4 e7-f6 b2-c3 f6-e5 d4xf6 g5xe7 g3-f4 h8-g7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 g7-f6 a1-b2 h8-g7 c3-d4 f6-g5 b2-a3 g7-f6 a3-b4 c7-b6 d4-e5 f6xd4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 g7-f6 f6-g5 c3-d4 e7-f6 b2-c3 f6-e5 d4xf6 g5xe7 g3-f4 h8-g7 f2-g3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 d2-e3 g7-f6 f6-e5 g3-f4 e5xg3 h2xf4 e7-d6 c5xe7 f8xd6 a1-b2 a7-b6 e3-d4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 b2-c3 f6-g5 h2-g3 g5xe3 f2xd4 h4xf2 e1xg3 h6-g5 g3-f4 g5xe3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 f6-g5 a1-b2 g5xe3 d2xf4 h8-g7 c3-d4 c7-b6 b2-c3 e7-d6 c5xe7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 h2-g3 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 e1xg3 h6-g5 a1-b2 h8-g7",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 h8-g7 c3-b4 f6-g5 a1-b2 g5xe3 d2xf4 c7-b6 c1-d2 b6xd4 d2-e3",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g7-f6 g3-h4 f8-g7 g5-f4 a1-b2 f6-g5 h4xf6 g7xe5 f2-g3 h8-g7 b2-a3 c7-d6 c1-b2",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a5xc3 c7-b6 a3-b4 b8-a7 d8-c7 d2-e3 e7-d6 g3-f4 f8-e7 c3-d4 b6-c5 d4xf6 g7xg3 h2xf4",
        "c3-d4 f6-g5 d4-c5 b6xd4 e3xc5 d6xb4 a5xc3 g5-h4 c3-b4 a7-b6 g7-f6 g3-f4 f6-g5 b2-c3 g5xe3 d2xf4 b6-c5 a1-b2 c5-b4 b2-a3",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 e7-f6 f2-e3 d8-c7 e3-d4 g5-h4 c1-d2 h4xf2 g1xe3 h6-g5",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 d2-e3 d8-e7 g3-f4 e7-d6 c5xe7 f6xd8 b2-c3 a7-b6 a1-b2 f8-e7 c3-b4 e7-d6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 d2-e3 f6-e5 e5-d4 c5-d6 c7xe5 e3xc5 f8-e7 g3-h4 g7-f6 b2-a3 b8-c7 a1-b2",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 f2-e3 g5-h4 g3-f4 h4-g3 f4-g5 h6xf4 e3xe7 f8xb4 h2xf4 b4-a3 d2-e3 g7-f6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 c5-b4 b6-a5 g3-f4 d8-c7 f2-e3 c5-b4 b2-c3 b4-a3 g1-f2",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 c5-b4 c5-b4 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 g7-f6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 c5-b4 f2-e3 b6-a5 b2-a3 a7-b6 d2-c3 b8-a7 c3-d4 h6-g5",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 c5-b4 g3-f4 b4-a3 f2-e3 b6-a5 g1-f2 d8-c7 b2-c3 c7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 c5-b4 g3-f4 b8-c7 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 b8-c7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 c5-b4 g3-f4 g3-f4 f8-e7 b2-c3 b6-a5 a1-b2 b8-c7 f2-e3",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 d8-e7 d8-e7 g3-f4 b6-a5 f2-g3 c5-b4 b2-c3 a7-b6 a1-b2",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 d8-e7 d8-e7 g3-f4 b6-a5 f2-g3 c5-b4 b2-c3 a7-b6 g1-f2",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 b2-a3 a7-b6 h2-g3 g3-f4 d2-c3 b8-a7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 h2-g3 a7-b6 g3-f4 d8-e7 g1-f2 e7-d6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 b6-a5 h2-g3 d8-e7 g3-f4 e7-f6 g1-f2 f6xd4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 b6-a5 h2-g3 b6-a5 b2-a3 f8-e7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 f8-e7 g3-f4 b6-a5 b2-c3 g7-f6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 f8-e7 g3-f4 b6-a5 g1-f2 a7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 f2-e3 a7-b6 e3-f4 c5-b4 g1-f2 f8-e7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 c5-b4 b2-c3 b4-a3",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 c5-b4 g1-f2 f8-e7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 d8-e7 g1-f2 e7-d6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 a7-b6 g3-h4 c5-b4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 c5-b4 b2-c3 a7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 f2-e3 f8-e7 g1-f2 b4-a3 g3-f4 g7-f6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 b2-c3 b6-a5 f2-g3 d8-e7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 f2-e3 b6-a5 g1-f2 b8-c7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 f2-e3 b6-a5 g1-f2 d8-c7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 a7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 g7-f6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-g3 a7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 g1-h2 b8-c7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 d2-c3 b4xd2 e1xc3 g7-f6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 f2-e3 b4-a3 g1-f2 b8-c7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 f2-e3 b6-a5 g1-f2 a7-b6",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 g1-h2 b6-a5 h2-g3 b4-a3",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 h2-g3 d8-e7 g3-f4 b6-a5 f2-e3 b8-c7 g1-f2 c5-b4 e3-d4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7-f6 e5-d6 c7xe5 b2-c3 h6-g5 a1-b2 d8-c7 c3-b4 f8-e7 b2-a3",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 c5-b4 e3-f4 f8-e7 b2-c3 b6-a5 g1-f2 a7-b6 a1-b2",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 a7-b6 g3-h4 c5-b4 b2-c3",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 c5-b4 b2-c3 a7-b6 g3-h4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 f2-e3 f8-e7 g1-f2 b4-a3 g3-f4 g7-f6 e5xg7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 f2-e3 b6-a5 g1-f2 f8-e7 b2-c3",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 a7-b6 g1-f2",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 g7-f6 e5xg7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-g3 g7-f6 e5xg7",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 f2-e3 b4-a3 g1-f2 b8-c7 b2-c3",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 b2-c3 g7-f6 h8-g7 g3-f4 f6-g5 d2-e3 c7-b6 e1-d2 b6xd4 e3xc5 g5xe3 d2xf4",
        "c3-d4 f6-g5 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 d2-e3 g7-f6 b2-a3 f6-e5 g3-f4 e5xg3 h2xf4 h8-g7 a1-b2 g7-f6 b2-c3 f6-g5",
        "c3-d4 f6-g5 d4-c5 g5-f4 c5-d6 h2-g3 b6-a5 g3-f4 d8-e7 d2-c3 a7-b6 f2-g3 e7-d6 b2-a3 f8-e7 c1-b2 b8-c7 c3-b4 a1-b2 g7-f6",
        "c3-d4 f6-g5 d4-c5 g5-f4 c5-d6 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 c5-b4 b2-c3 b4-a3 a1-b2 c3-d4 b6-c5 b2-c3 e7-d6 g3-h4 g7-f6",
        "c3-d4 f6-g5 d4-c5 g5-f4 c5-d6 h2-g3 b6-a5 g3-f4 d8-e7 f2-g3 c5-b4 b2-c3 b4-a3 g3-h4 a1-b2 e7-f6 g1-f2 f8-e7 b2-c3 a7-b6",
        "c3-d4 f6-g5 d4-c5 g5-f4 c5-d6 h2-g3 c5-b4 b2-c3 g7-f6 a1-b2 f8-e7 f2-e3 d2-c3 a7-b6 e3-d4 d6-c5 d4-e5 h6-g5 e1-f2 g5-f4",
        "c3-d4 f6-g5 d4-c5 g5-f4 c5-d6 h2-g3 c5-b4 g3-f4 f8-e7 f2-e3 b4-a3 e3-d4 g7-f6 b2-c3 h8-g7 a1-b2 b6-c5 d2-e3 g7-f6 g1-f2",
        "c3-d4 f6-g5 d4-c5 g5-f4 c7-b6 c5-d6 h2-g3 c5-b4 d2-c3 b6-c5 e3-d4 g3-h4 g7-f6 b2-c3 b8-c7 a1-b2 c7-d6 e1-d2 a7-b6 d4-c5",
        "c3-d4 f6-g5 d4-c5 g5-h4 c3-b4 b6-a5 b4-c5 g7-f6 h8-g7 g3-f4 f6-g5 a1-b2 c7-d6 b2-a3 d8-c7 c3-b4 g7-f6 e1-d2 e7-d6 d2-c3",
        "c3-d4 f6-g5 d4-c5 g5-h4 c3-d4 b6-a5 b2-c3 a7-b6 c7-d6 g3-f4 d6-c5 f2-g3 g7-f6 g3-h4 f8-g7 h2-g3 a5-b4 d6-c5 f6-g5 g1-f2",
        "c3-d4 f6-g5 d4xb6 c7xc3 b2xd4 g7-f6 a1-b2 h8-g7 b2-c3 a7-b6 g3-f4 g5-h4 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 e1-d2 e7-d6",
        "c3-d4 f6-g5 d4xb6 c7xc3 b2xd4 g7-f6 a1-b2 h8-g7 c1-d2 d8-c7 d4-e5 d6xf4 g3xe5 f6xd4 e3xc5 e7-d6 c5xe7 f8xd6 d2-e3 a7-b6",
        "c3-d4 f6-g5 d6-e5 a1-b2 g5-f4 a7-b6 b2-c3 d8-c7 g1-f2 b6-a5 b4-c5 e5-f4 e7-f6 g7-f6 f2-e3 c7-d6 g3-h4 h8-g7 c3-d4 d6-c5",
        "c3-d4 f6-g5 d6-e5 a1-b2 g5-f4 e5-d4 b4-a5 g7-f6 f2-e3 h8-g7 g3-f4 d8-c7 e1-d2 d6-e5 e3-f4 g7-h6 d2-e3 a7-b6 c1-d2 d6-e5",
        "c3-d4 f6-g5 g3-f4 b6-a5 d4-c5 d6xb4 a3xc5 g5-h4 b2-c3 c7-d6 c3-b4 a5xc3 d2xb4 d6-e5 f4xd6 a7-b6 c5xa7 e7xa3 a1-b2 g7-f6",
        "c3-d4 f6-g5 g3-f4 b6-a5 d4-c5 d6xb4 a3xc5 g7-f6 b2-c3 g5-h4 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 f6-e5 g5-h6 h8-g7 a1-b2",
        "c3-d4 f6-g5 g3-f4 d6-c5 b2-c3 c7-d6 a1-b2 b6-a5 d4xb6 a7xc5 f2-g3 g7-f6 g3-h4 b8-a7 h2-g3 f8-g7 g1-h2 a7-b6 a3-b4 c5xa3",
        "c3-d4 f6-g5 g3-f4 d6-c5 b2-c3 g5-h4 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3 c1-b2 a7-b6 b2xd4 b6-a5 d4-c5 b8-a7 a1-b2 h6-g5",
        "c3-d4 f6-g5 g3-f4 d6-c5 b2-c3 g5-h4 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c1-d2 a7-b6 d2xb4 b6-a5 b4-c5 g7-f6 a1-b2 f6-g5",
        "c3-d4 f6-g5 g3-f4 d6-c5 b2-c3 g7-f6 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 c1-b2 c3-d2 e3xc1 g5xe3 f2xd4 f8-g7 c1-d2 f6-e5",
        "c3-d4 f6-g5 g3-f4 d6-c5 d2-c3 g7-f6 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 f4-e5 f6-g5 d4-c5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6",
        "c3-d4 f6-g5 g3-f4 d6-c5 d2-c3 g7-f6 c3-b4 h8-g7 b4xd6 c7xc3 b2xd4 b6-c5 d4xb6 a7xc5 a1-b2 e7-d6 b2-c3 d8-e7 c3-d4 b8-a7",
        "c3-d4 f6-g5 g3-f4 d6-c5 d2-c3 g7-f6 c3-b4 h8-g7 b4xd6 c7xc3 b2xd4 b6-c5 d4xb6 a7xc5 a1-b2 g5-h4 b2-c3 f6-g5 c1-b2 e7-d6",
        "c3-d4 f6-g5 g3-f4 d6-c5 d2-c3 g7-f6 f2-g3 g5-h4 e1-d2 h4xf2 a3-b4 c5xa3 d4-c5 f2xd4 c3xg7 h8xf6 d2-c3 b6xd4 c3xg7 e7-f6",
        "c3-d4 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f4-e5 f6-g5 a1-b2 e7-f6 h2-g3 d8-e7 g3-f4 e7-d6 d4-c5 c7-b6 c3-d4 f8-e7 f2-e3 b8-c7",
        "c3-d4 f6-g5 g3-f4 g7-f6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h6-g5 h2-g3 h8-g7 d2-e3 g7-h6 b2-c3 c7-b6 a1-b2 e7-d6",
        "c3-d4 f6-g5 g3-f4 g7-f6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 d2-e3 h6-g5 h2-g3 g7-h6 e1-f2 c7-d6 b2-a3 d6xb4",
        "c3-d4 f6-g5 g3-f4 g7-f6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 d2-e3 h6-g5 h2-g3 g7-h6 g3-f4 c7-d6 b2-a3 d6xb4",
        "c3-d4 f6-g5 g3-f4 g7-f6 d4-c5 d6xb4 a5xc3 h8-g7 c3-d4 c7-d6 d6xb4 b2-c3 g5-h4 c3xa5 f6-g5 a1-b2 e7-d6 b2-c3 g7-f6 c3-d4",
        "c3-d4 f6-g5 g3-f4 g7-f6 h2-g3 b6-a5 d4-c5 d6xb4 a3xc5 g5-h4 b2-c3 f6-g5 c3-b4 a5xc3 d2xb4 e7-f6 c5-d6 c7xe5 f4xd6 a7-b6",
        "c3-d4 f6-g5 g3-f4 g7-f6 h2-g3 b6-a5 d4-c5 d6xb4 a3xc5 g5-h4 b2-c3 f6-g5 c3-b4 a5xc3 d2xb4 e7-f6 c5-d6 c7xe5 f4xd6 d8-e7",
        "c3-d4 f6-g5 g3-f4 g7-f6 h2-g3 b6-a5 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 g3-f4 g7-f6 d2-e3 c7-b6 e1-f2 d8-c7",
        "c3-d4 f6-g5 g3-f4 g7-f6 h2-g3 g5-h4 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 h8-g7 b2-c3 c7-d6 c3-b4 d8-c7 d2-e3 d6-e5 f4xd6 c7xe5",
        "c3-d4 f6-g5 g3-f4 g7-f6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-e5 f4xd6 c7xe5 d2-c3 b8-c7 c3-d4 e5xc3 b2xd4 c7-d6",
        "c3-d4 f6-g5 g3-f4 g7-f6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 g1xe3 e7-d6 c5xe7 f8xd6",
        "c3-d4 f6-g5 g3-f4 g7-f6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 h8-g7 b2-c3 c7-d6 c3-b4 d8-c7 d2-e3 d6-e5 f4xd6 c7xe5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 a1-b2 a7-b6 h2-g3 g5-h4 g3-f4 d6-e5 d4xf6 e7xg5 f4xh6 f8-g7 h6xf8 b6-c5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 a1-b2 g5-h4 e3-f4 h8-g7 d2-e3 g7-h6 c1-d2 d6-c5 d4xb6 a7xc5 f4-e5 b8-a7",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 a1-b2 g5-h4 e3-f4 h8-g7 d2-e3 g7-h6 e1-d2 d6-c5 d4xb6 a7xc5 f4-e5 b8-a7",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 a1-b2 g5-h4 h2-g3 a7-b6 g3-f4 d6-e5 d4xf6 e7xg5 f4xh6 f8-g7 h6xf8 b6-c5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 a1-b2 g5-h4 h8-g7 d2-e3 g7-h6 e1-d2 d6-c5 d4xb6 a7xc5 f4-e5 b8-a7 d2-c3",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 a1-b2 h8-g7 h2-g3 g5-h4 b2-c3 a7-b6 g3-f4 g7-h6 f2-g3 h4xf2 e1xg3 b8-a7",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 a7-b6 g3-f4 d6-e5 d4xf6 e7xg5 f4xh6 f8-g7 h6xf8 b6-c5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 h8-g7 b2-c3 a7-b6 g3-f4 g7-h6 f2-g3 h4xf2 e1xg3 d6-c5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 h8-g7 b2-c3 a7-b6 g3-f4 g7-h6 f2-g3 h4xf2 e1xg3 e7-f6",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 h8-g7 b2-c3 a7-b6 g3-f4 g7-h6 g1-h2 d6-c5 f4-e5 e7-d6",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 h8-g7 g3-f4 g7-h6 b2-c3 a7-b6 d4-e5 d6-c5 c3-b4 a5xc3",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 h8-g7 g3-f4 g7-h6 b2-c3 a7-b6 d4-e5 d6-c5 c3-d4 e7-d6",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 h8-g7 g3-f4 g7-h6 b2-c3 a7-b6 g1-h2 b8-a7 d4-e5 f8-g7",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 h8-g7 g3-f4 g7-h6 b2-c3 a7-b6 g1-h2 d6-c5 f4-e5 e7-d6",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 h8-g7 g3-f4 g7-h6 b2-c3 c7-b6 d4-e5 d6-c5 c3-d4 d8-c7",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a7-b6 a1-b2 d6-e5 d4xf6 e7xg5 f4xh6 f8-g7 h6xf8 b6-c5 f8xb4",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a7-b6 c1-b2 d6-c5 d4-e5 e7-d6 b2-c3 h8-g7 c3-d4 g7-h6 e5-f6",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a7-b6 d4-e5 h8-g7 a1-b2 d6-c5 b2-c3 e7-d6 c3-d4 g7-h6 e5-f6",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a7-b6 g1-h2 d6-c5 a1-b2 h8-g7 b2-c3 b8-a7 f4-e5 c5-b4 a3xc5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 d2-c3 h8-g7 e3-f4 c7-b6 f2-e3 h4xf2 e1xg3 g7-f6 g3-h4 d6-e5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 g3-f4 h8-g7 a1-b2 a7-b6 b2-c3 g7-h6 f2-g3 h4xf2 e1xg3 d6-c5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 g3-f4 h8-g7 a1-b2 g7-h6 b2-c3 a7-b6 f2-g3 h4xf2 e1xg3 b8-a7",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 g3-f4 h8-g7 a1-b2 g7-h6 b2-c3 a7-b6 f2-g3 h4xf2 e1xg3 e7-f6",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 h8-g7 b2-c3 a7-b6 g3-f4 g7-h6 f2-g3 h4xf2 e1xg3 e7-f6 g3-h4",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 h8-g7 g3-f4 g7-h6 b2-c3 a7-b6 d4-e5 d6-c5 c3-d4 e7-d6 d2-c3",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 h8-g7 g3-f4 g7-h6 b2-c3 c7-b6 d4-e5 d6-c5 c3-d4 d8-c7 c1-b2",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 d2xb4 a5xc3 b2xd4 a7-b6 a1-b2 d6-c5 h2-g3 h6-g5 b2-c3 g5-h4 c1-d2 e7-f6 g3-f4 h8-g7",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 d2xb4 a5xc3 b2xd4 a7-b6 a1-b2 d6-c5 h2-g3 h6-g5 b2-c3 g5-h4 d4-e5 c5-d4 e3xa7 c7-b6",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 d2xb4 a5xc3 b2xd4 a7-b6 a1-b2 d6-c5 h2-g3 h6-g5 b2-c3 g5-h4 g3-f4 e7-f6 f4-e5 d8-e7",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 d2xb4 a5xc3 b2xd4 a7-b6 b6-a5 a1-b2 a5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 g3-f4",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 d2xb4 a5xc3 b2xd4 a7-b6 d6-c5 h2-g3 h6-g5 b2-c3 g5-h4 d4-e5 c5-d4 e3xa7 c7-b6 a7xc5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 d2xb4 a5xc3 b2xd4 a7-b6 h2-g3 h8-g7 a1-b2 g7-f6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-e5",
        "c3-d4 f6-g5 g3-h4 b6-a5 h4xf6 g7xc3 d2xb4 a5xc3 b2xd4 h8-g7 g7-f6 b2-c3 a7-b6 h2-g3 b6-a5 g3-f4 f6-g5 c1-d2 c7-b6 d4-e5",
        "c3-d4 f6-g5 g3-h4 b6-c5 a1-b2 d6-e5 e5-f4 f2-e3 e7-d6 c5-d4 d2-e3 h8-g7 h2-g3 g7-f6 e3-d4 f8-e7 c1-d2 e7-d6 d4-c5 c7-d6",
        "c3-d4 f6-g5 g3-h4 c7-d6 b6-c5 h8-g7 h2-g3 g7-f6 b4-a5 f6-g5 g3-h4 d6-c5 a1-b2 f8-e7 b2-c3 g5-f4 a5-b6 f2-e3 f4-g3 e3-f4",
        "c3-d4 f6-g5 g3-h4 c7-d6 d6-c5 h8-g7 b2-c3 g7-f6 h2-g3 b6-a5 e1-d2 a7-b6 c3-d4 b6-a5 d4-c5 b8-a7 g1-h2 a5-b4 c5-b6 d2-c3",
        "c3-d4 f6-g5 g3-h4 d6-c5 d2-c3 c7-d6 d4-e5 d8-c7 g5-h4 e5-f6 f8-g7 f4-e5 c7-d6 c3-d4 h8-g7 d4-e5 b8-c7 b2-c3 b6-a5 f2-g3",
        "c3-d4 f6-g5 g3-h4 e7-d6 d6-c5 a1-b2 h8-g7 g7-f6 h2-g3 c7-d6 g3-h4 d6-e5 f2-g3 d8-c7 g1-h2 f6-g5 g3-f4 g7-f6 h2-g3 c5-b4",
        "c3-d4 f6-g5 g3-h4 e7-f6 d4-c5 d6xb4 a5xc3 a7-b6 h2-g3 f8-e7 e7-d6 c3-d4 b6-a5 d2-c3 d6-e5 f4xd6 c7xe5 f2-g3 d8-c7 g1-h2",
        "c3-d4 f6-g5 g3-h4 g7-f6 d4-c5 d6xb4 a5xc3 a7-b6 h2-g3 e7-d6 b6-a5 c3-d4 d6-e5 f4xd6 c7xc3 b2xd4 f6-e5 d4xf6 g5xe7 a1-b2",
        "c3-d4 f6-g5 h8-g7 e3-f4 b6-c5 g7-f6 f2-e3 c7-b6 a1-b2 f6-e5 b2-c3 b6-a5 f4-g5 b8-c7 g5-f6 c5-b4 h4-g5 d6-c5 g5-h6 c5-d4",
        "c3-d4 f8-e7 d4-c5 b6-a5 c3-d4 f6-g5 g3-f4 c7-b6 g7-f6 f2-g3 e7-d6 f4-e5 h2-g3 g5-h4 e3-f4 b6-c5 a1-b2 h8-g7 c3-d4 c7-d6",
        "c3-d4 f8-e7 d4-c5 e7-d6 c3-d4 f6-e5 b2-c3 d6-c5 c1-b2 c7-d6 g1-f2 a7-b6 f2-e3 b6-a5 a1-b2 c5-b4 g3-f4 d8-c7 b2-c3 c7-b6",
        "c3-d4 g3-f4 d4-c5 a3xc5 f6-g5 b6-a5 d6xb4 g7-f6 b2-c3 c3-d4 f2-g3 e1xg3 h8-g7 g5-h4 h4xf2 c7-d6 g1-f2 d4-e5 e3xa3 d2-c3",
        "c3-d4 g3-f4 d4-c5 a3xc5 h6-g5 g7-h6 d6xb4 b6xd4 e3xc5 f2xd4 d2-e3 h2-g3 g5xe3 h8-g7 h6-g5 g7-h6 g3-f4 c5xe7 e1-f2 f2-g3",
        "c3-d4 g3-f4 d4-c5 e3xc5 h6-g5 g7-h6 b6xd4 d6xb4 a3xc5 f2xd4 d2-e3 h2-g3 g5xe3 h8-g7 h6-g5 g7-h6 e1-f2 b2-a3 a1-b2 c1-d2",
        "c3-d4 g3-f4 d4-c5 e3xc5 h6-g5 g7-h6 b6xd4 g5xe3 f2xd4 a3xc5 d2-e3 h2-g3 d6xb4 h8-g7 h6-g5 g7-h6 e1-f2 b2-a3 a1-b2 c1-d2",
        "c3-d4 g3-f4 d4-c5 h6-g5 g5-h4 b2-c3 f6-e5 e7-d6 a1-b2 d2-e3 c3-d4 a7-b6 e5-f4 f6-e5 f2-e3 b2-c3 e1-d2 d8-e7 h8-g7 e7-f6",
        "c3-d4 g3-f4 d4xf6 h2xf4 b6-a5 f6-e5 g7xg3 h8-g7 e3-d4 d4-c5 a3xc5 f2-e3 g7-f6 d6xb4 f6-g5 c7-b6 e3-d4 d2xf4 c5xe7 d4-e5",
        "c3-d4 g3-f4 h2-g3 d4-c5 f6-g5 g7-f6 g5-h4 b2-c3 c3-b4 h8-g7 c7-d6 d8-c7 d2-e3 e3-f4 d6-e5 h6-g5 e5-f4 a1-b2 b4-a5 c1-d2",
        "c3-d4 g3-f4 h2-g3 d4-c5 h6-g5 g7-h6 g5-h4 b6xd4 e3xc5 a3xc5 b2-c3 c3-b4 d6xb4 h8-g7 c7-d6 d8-c7 d2-e3 f4xd6 e3-f4 f4xh6",
        "c3-d4 g3-f4 h2-g3 g3-h4 h6-g5 g7-h6 h8-g7 d6-e5 f4xd6 b2xd4 e3xg5 a3-b4 c7xc3 g5-f4 h6xf4 f4-e3 d2xf4 d4xb6 a1-b2 b2-c3",
        "c3-d4 g3-f4 h2xf4 d4xb6 d6-e5 e5xg3 b6-c5 a7xc5 b2-c3 c3-b4 f4-g5 e3xg5 e7-d6 f6-e5 h6xf4 g7-f6 g5xe7 d2-e3 b4-a5 a5xc7",
        "c3-d4 g3-h4 f2-g3 g3-f4 h6-g5 b6-a5 a7-b6 g7-h6 h2-g3 f4xd6 d2xb4 b2xd4 d6-e5 c7xc3 a5xc3 e7-d6 a1-b2 d4xf6 b2-c3 g3-f4",
        "c3-d4 g3-h4 f2-g3 g3-f4 h6-g5 g7-h6 d6-e5 e5xc3 b2xd4 h2-g3 d4xf6 a1-b2 e7-d6 f6-e5 g5xe7 b6-a5 b2-c3 g1-h2 f4-g5 g3xc7",
        "c3-d4 g3-h4 f2-g3 g3-f4 h6-g5 g7-h6 d6-e5 e5xg3 h2xf4 b2-c3 d4xf6 f4-g5 e7-d6 f6-e5 g5xe7 h6xf4 e3xg5 g5-h6 c1-b2 c3-b4",
        "c3-d4 g3-h4 h2-g3 b2-c3 d6-c5 c7-d6 b8-c7 d6-e5 g3-f4 c3-b4 b4-a5 a5xc7 e5xg3 c7-d6 f6-e5 e5xc3 d2xb4 b4xd6 g1-h2 h2xf4",
        "c3-d4 g3-h4 h2-g3 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 b2-c3 c3-b4 a1-b2 g3-f4 a7-b6 b6-c5 f6-e5 e5xg3 e3-d4 d2xh2 f2-e3 h4xf6",
        "c3-d4 g3-h4 h2-g3 d6-c5 c7-d6 b6-a5 a3-b4 e3-f4 b4-a5 g1-h2 f6-e5 a7-b6 e5-d4 d4-c3 g3-f4 f2-g3 d6-e5 g7-f6 f8-e7 e1-d2",
        "c3-d4 g3-h4 h4xf6 d2xb4 f6-g5 b6-a5 g7xc3 a5xc3 b2xd4 a1-b2 c1-d2 d4xf6 h6-g5 g5-h4 d6-e5 e7xg5 h2-g3 a3-b4 d2-c3 e3-d4",
        "c3-d4 g5-f4 g3-f4 d6-c5 d2-e3 c7-d6 b2-c3 g7-f6 b6-a5 b4-c5 c7-d6 h2-g3 f4-e5 h8-g7 a1-b2 g7-f6 b2-c3 f6-e5 g3-f4 g1-h2",
        "c3-d4 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 d4-c5 b6xd4 f2-g3 f4-e3 d2xf4 c7-b6 a5xc7 b8xd6 f4-g5 a7-b6 g3-h4 d6-c5 e1-d2 e7-f6",
        "c3-d4 g5-h4 b2-c3 f6-e5 a1-b2 e5-f4 a3-b4 h8-g7 d2-e3 h6-g5 e3-d4 f8-e7 b2-a3 e7-d6 c1-d2 d6-e5 f2-g3 g7-h6 d2-e3 g5-h4",
        "c3-d4 g5-h4 b2-c3 f6-g5 c3-b4 b6-a5 d4-c5 g7-f6 c7-d6 b4-a5 e7-d6 a3-b4 f6-e5 b4-a5 h8-g7 c3-b4 d6-e5 a1-b2 g7-f6 b2-a3",
        "c3-d4 g5-h4 b2-c3 f6-g5 d4-e5 b6-c5 c3-b4 c7-b6 b4xd6 e7xc5 c5-b4 a3xc5 b6xf6 d2-c3 d8-c7 c3-b4 f6-e5 f4xd6 c7xe5 e3-f4",
        "c3-d4 g5-h4 b4-a5 a7-b6 b6-c5 g7-f6 b2-c3 f6-e5 c3-b4 h8-g7 a1-b2 h6-g5 b2-c3 d8-c7 b4-a5 g7-h6 c3-b4 e5-f4 b4-c5 e7-d6",
        "c3-d4 g5-h4 d4-c5 b6-a5 c3-d4 h8-g7 b2-c3 a7-b6 c7-d6 f4-g5 b6-c5 g5-h6 f6-e5 a3-b4 g7-f6 b4-a5 d6-c5 d2-e3 e7-d6 e3-d4",
        "c3-d4 g5-h4 d4-c5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 g5xe3 f2xd4 g7-h6 c1-d2 h4-g3 h2xf4 a7-b6 c5xa7 f6-e5 f4xd6",
        "c3-d4 g5-h4 g3-f4 b6-c5 b2-a3 g7-f6 a1-b2 h8-g7 f6-e5 g5-h6 g7-f6 b2-c3 c5-b4 f2-g3 e7-d6 g1-f2 b4-a3 f2-e3 d6-c5 g3-h4",
        "c3-d4 g7-f6 c3-b4 b6-a5 h8-g7 c1-d2 f6-g5 h2-g3 g7-h6 d2-c3 e7-d6 c3-d4 d6-c5 g3-f4 h6-g5 b2-c3 g5-f4 a3-b4 f4-g3 c3-d4",
        "c3-d4 g7-f6 d4-c5 d6xb4 a5xc3 b6-a5 c3-d4 h8-g7 d4-c5 f6-e5 b2-c3 e5-f4 g3xe5 e7-d6 c5xe7 d8xb2 a3-b4 a5xc3 c1xa3 c7-b6",
        "c3-d4 g7-f6 d4-c5 d6xb4 a5xc3 e7-d6 g3-f4 f6-g5 c3-d4 d8-e7 e7-f6 e5xg7 h8xf6 b2-c3 d6-e5 f4xd6 c7xe5 c3-b4 a3xc5 e3-d4",
        "c3-d4 g7-f6 d4-c5 d6xb4 a5xc3 f6-e5 a3-b4 e7-d6 b4-c5 b6xd4 e3xe7 f8xd6 c3-b4 h6-g5 b4-c5 d6xb4 g3-f4 e5xg3 h2xh6 d8-e7",
        "c3-d4 g7-f6 g3-f4 b6-a5 f4-g5 h6xf4 e3xg5 c7-b6 h2-g3 b6-c5 d4xb6 a5xc7 f2-e3 a7-b6 b2-c3 b6-a5 g3-f4 d6-c5 g5-h6 a3-b2",
        "c3-d4 g7-f6 g3-h4 d6-e5 b2-c3 e7-d6 f2-g3 f8-g7 e3-f4 b6-c5 d4xb6 a7xc5 d2-e3 e5-d4 c3xe5 f6xf2 g1xe3 g7-f6 a1-b2 f6-e5",
        "c3-d4 g7-f6 g3-h4 d6-e5 f2-g3 e5xc3 b2xd4 f6-g5 h4xf6 e7xg5 h8-g7 b2-c3 g7-f6 g3-h4 f6-e5 d4xf6 g5xe7 h2-g3 e7-d6 c3-d4",
        "c3-d4 g7-h6 b2-c3 b6-c5 d4xb6 a7xc5 c3-d4 a5-b4 d4xb6 c7xa5 a3xc5 d6xb4 g3-f4 f6-g5 a1-b2 b4-a3 b2-c3 d8-c7 c3-d4 f8-g7",
        "c3-d4 h6-g5 b2-c3 d6-c5 c3-b4 b6-a5 d4xb6 a5xc3 d2xb4 c7xc3 e7-d6 b2xd4 d6-e5 g3-h4 e5xc3 e3-f4 g5xe3 f2xb2 a7-b6 b2-c3",
        "c3-d4 h6-g5 b2-c3 g5-f4 e3xg5 f6xh4 d2-e3 b6-a5 g3-f4 c7-b6 g7-h6 f2-g3 h4xf2 e1xg3 e7-f6 f4-g5 h6xb4 a3xg5 b6-c5 d4xb6",
        "c3-d4 h6-g5 b2-c3 g5-f4 e3xg5 f6xh4 g3-f4 d6-c5 d2-e3 c7-d6 b6-a5 d4xb6 a5xc7 a1-b2 a7-b6 b4-a5 g7-f6 f4-g5 f6-e5 g5-h6",
        "c3-d4 h6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 f6xh4 a1-b2 e7-d6 h2-g3 g7-h6 g3-f4 h8-g7 f4-e5 d6xf4 d4-c5 b6xd4 c3xg3 g7-f6",
        "c3-d4 h6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 f6xh4 a1-b2 g7-f6 b6xd4 c3xg7 h8xf6 b2-c3 a7-b6 c3-d4 b6-a5 h2-g3 c7-b6 g3-f4",
        "c3-d4 h6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 f6xh4 a1-b2 g7-h6 e7-d6 g3-f4 d6-c5 f4-e5 c5xe3 d2xf4 f8-e7 c3-d4 b6-c5 d4xb6",
        "c3-d4 h6-g5 b2-c3 g5-h4 c3-b4 f6-e5 d4xf6 g7xe5 b4-a5 b6-c5 h8-g7 g3-f4 e5xg3 h2xf4 g7-f6 f4-g5 f6-e5 g5-h6 c7-b6 a5xc7",
        "c3-d4 h6-g5 b2-c3 g5-h4 c3-b4 f6-e5 d4xf6 g7xe5 b4-a5 e5-f4 e3xg5 h4xf6 g3-h4 h8-g7 f2-e3 b6-c5 h2-g3 f6-e5 a1-b2 g7-h6",
        "c3-d4 h6-g5 b2-c3 g5-h4 c3-b4 f6-e5 d4xf6 g7xe5 b4-a5 h8-g7 a1-b2 e7-f6 a3-b4 b6-c5 b2-a3 d8-e7 g3-f4 e5xg3 h2xf4 f6-e5",
        "c3-d4 h6-g5 b2-c3 g5-h4 d2-e3 f6-e5 c3-b4 e5-f4 g3-f4 h8-g7 a1-b2 f6-e5 f2-g3 e7-f6 g3-h4 f6-g5 h2-g3 g7-f6 f2-e3 g5-h4",
        "c3-d4 h6-g5 b2-c3 g5-h4 g3-f4 b6-a5 f4-g5 c7-b6 g5-h6 d6-c5 h2-g3 e7-d6 g3-f4 f6-e5 d4xf6 g7xg3 g1-h2 f8-e7 h2xf4 c5-b4",
        "c3-d4 h6-g5 b2-c3 g7-h6 c3-b4 d6-e5 b4-a5 e5xc3 d2xb4 g5-h4 a1-b2 h8-g7 g3-f4 f6-g5 b2-c3 g7-f6 c3-d4 f6-e5 f4xd6 c7xc3",
        "c3-d4 h6-g5 g3-f4 g5-h4 f4-g5 d6-e5 g5-h6 e5xc3 b2xd4 f6-e5 d4xf6 g7xe5 a3-b4 e5-f4 e3xg5 h4xf6 b4-a5 f6-e5 h2-g3 b6-c5",
        "c3-d4 h6-g5 g3-f4 g5-h4 f4-g5 d6-e5 g5-h6 e5xc3 b2xd4 f6-e5 d4xf6 g7xe5 a3-b4 h8-g7 a1-b2 b6-a5 b2-c3 c7-b6 e3-d4 g7-f6",
        "c3-d4 h6-g5 g3-f4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 d2xf4 f6-e5 f4xd6 c7xe5 b2-c3 h8-g7 h2-g3 b8-c7 g3-f4 e5xg3",
        "c3-d4 h6-g5 g3-f4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h6-g5 h2-g3 h8-g7 g3-f4 g5xe3 d2xf4 g7-h6 e1-f2 f6-g5",
        "c3-d4 h6-g5 g3-f4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 h2-g3 h6-g5 c5-b6 a7xe3 d2xh6 f6-e5 b2-c3 e7-d6",
        "c3-d4 h6-g5 g3-f4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 d2xf4 f6-e5 f4xd6 c7xe5 b2-c3 h8-g7 h2-g3 b8-c7 g3-f4 e5xg3",
        "c3-d4 h6-g5 g3-f4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 h8-g7 d2-e3 h6-g5 h2-g3 g7-h6 c1-d2 c7-b6 g1-f2 e7-d6",
        "c3-d4 h6-g5 g3-f4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 h8-g7 d2-e3 h6-g5 h2-g3 g7-h6 g3-f4 e7-d6 c5xe7 f8xd6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-c5 d6xb4 a3xc5 g5-h4 b2-c3 f6-g5 c3-b4 a5xc3 d2xb4 e7-d6 c5xe7 f8xd6 a1-b2 a7-b6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-c5 d6xb4 a3xc5 g5-h4 b2-c3 f6-g5 c3-b4 a5xc3 d2xb4 e7-d6 c5xe7 f8xd6 a1-b2 h8-g7",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h6-g5 g3-f4 g5xe3 d2xf4 h8-g7 g1-f2 g7-f6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h6-g5 g3-f4 g5xe3 h8-g7 g1-h2 g7-f6 h2-g3",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 d2-e3 e7-d6 c5xe7 f8xd6 g1-h2 g7-f6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 d2-e3 g3-h4 c7-d6 b2-a3 d6xb4 a3xc5",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 g3-f4 g7-f6 d2-e3 c7-b6 g1-f2 b8-c7",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-e5 f6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 g3-f4 g7-f6 g1-h2 f6-g5 h2-g3 g5xe3",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 b6-a5 d4-e5 f6xd4 e3xc5 g5xe3 f2xd4 d6xb4 a3xc5 h8-g7 d2-e3 g7-f6 g3-h4 c7-b6 e1-f2 b8-c7",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-e5 f4xd6 c7xe5 d2-c3 e7-d6 c5xe7 f8xd6 c3-d4 e5xc3",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-a3 g5xe3 f2xd4 h4xf2 e1xg3 c7-b6 d2-e3 e7-d6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-a3 g5xe3 f2xd4 h4xf2 e1xg3 h6-g5 d2-e3 h8-g7",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 e1xg3 e7-d6 c5xe7 f8xd6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 e1xg3 h6-g5 a1-b2 f8-g7",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 e1xg3 h6-g5 a1-b2 h8-g7",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 e1xg3 h6-g5 g1-f2 h8-g7",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 e1xg3 h6-g5 g3-f4 g5xe3",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 e1xg3 h8-g7 a1-b2 g7-f6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 e1xg3 h8-g7 d2-e3 g7-f6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 e1xg3 h8-g7 g3-f4 g7-f6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 h8-g7 b2-c3 c7-d6 c3-b4 d8-c7 d2-e3 d6-e5 f4xd6 c7xe5",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 h8-g7 b2-c3 f6-e5 f4xd6 c7xe5 c5-b6 a7xc5 c3-b4 c5xa3",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 h8-g7 b2-c3 f6-g5 d2-e3 c7-d6 c3-b4 d8-c7 e3-d4 g5xe3",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 h8-g7 b2-c3 f6-g5 d2-e3 e7-d6 c5xe7 f8xd6 c3-d4 a7-b6",
        "c3-d4 h6-g5 g3-f4 g7-h6 h2-g3 h8-g7 g3-h4 d6-e5 f4xd6 c7xc3 b2xd4 g5-f4 e3xg5 h6xf4 a3-b4 f4-e3 d2xf4 b6-c5 d4xb6 a7xa3",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 c7-b6 f2-g3 d6-c5 g3-f4 g7-h6 h2-g3 e7-d6 g1-h2 f8-g7 a1-b2 f6-e5 d4xf6 g5xe7 f4-g5 h6xf4",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 c7-b6 f2-g3 g7-h6 g3-f4 b6-c5 d4xb6 a5xc7 c3-b4 d6-e5 f4xd6 c7xe5 e3-f4 e5xg3 h4xf2 h8-g7",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 c7-b6 h2-g3 d6-e5 c1-b2 e7-d6 g1-h2 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 d8-c7 c3-d4 e5xc3",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 c7-b6 h2-g3 d6-e5 c1-b2 e7-d6 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 d8-c7 c3-d4 e5xc3 b2xd4",
        "c3-d4 h6-g5 g3-h4 b6-a5 b2-c3 d6-e5 a1-b2 g7-h6 a3-b4 c7-b6 b2-a3 e7-d6 f2-g3 f8-g7 b4-c5 d6xb4 a3xc5 a5-b4 c3xc7 b8xb4",
        "c3-d4 h6-g5 g3-h4 b6-a5 d2-c3 d6-e5 f2-g3 g7-h6 g3-f4 e5xg3 h4xf2 g5-f4 e3xg5 f6xh4 h2-g3 e7-d6 g3-f4 h8-g7 c1-d2 g7-f6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 b2-a3 b6xd4 e3xc5 a5-b4 c5-b6 a7xc5 a1-b2 g5-f4 b2-c3 f6-e5 c3xa5 e7-d6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 b2-c3 a7-b6 a1-b2 c5-d4 c3xe5 f6xd4 e1-d2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 b2-c3 b8-c7 e1-d2 c5-b4 h2-g3 c7-d6 f2-e3",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 b2-c3 b8-c7 f2-e3 c5-b4 e1-d2 c7-d6 a1-b2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 b2-c3 c5-d4 c3xe5 f6xd4 f2-e3 d4xf2 g1xe3",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 a7-b6 a1-b2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 a7-b6 g1-f2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 b4-a3 a1-b2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 c7-b6 g1-f2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 d8-e7 e3-f4",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 f6-e5 d4xf6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 e1-d2 c7-d6 h2-g3",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c7-d6 h2-g3 c5-b4 e1-d2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 g1-f2 f6-e5 f2-g3 g7-f6 b2-c3",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 h2-g3 c7-d6 b2-a3 f6-e5 c1-b2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 h2-g3 c7-d6 b2-a3 f6-e5 e1-d2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 h2-g3 c7-d6 b2-a3 f6-e5 g3-f4",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 h2-g3 c7-d6 e3-f4 f6-g5 h4xf6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 h2-g3 f6-e5 b2-c3 g7-f6 e1-d2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 h2-g3 b8-c7 f2-e3 c7-d6 b2-c3 c5-b4 e1-d2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 f6-e5 b2-c3 g7-f6 f2-e3 h8-g7 a1-b2 b6-c5 e3-f4",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 f6-e5 b2-c3 g7-f6 f2-e3 h8-g7 e3-f4 e5xg3 h4xf2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 f6-e5 f2-e3 g7-f6 h2-g3 h8-g7 b2-c3 b8-c7 g3-f4",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 b2-c3 a7-b6 h2-g3 c5-d4 c3xe5 f6xd4",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 b2-c3 b8-c7 a1-b2 c7-d6 h2-g3 d6-e5",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 b2-c3 c5-b4 a1-b2 b4xd2 e1xc3 b8-c7",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 a7-b6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 b4-a3",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 c7-b6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 d8-e7",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 c3-d4 f6-e5",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 e1-d2 c7-d6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 h2-g3 c7-d6 b2-a3 f6-e5",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 h2-g3 c7-d6 e3-f4 f6-g5",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 h2-g3 b8-c7 b2-c3 c5-d4 c3xe5 f6xd4",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 h2-g3 b8-c7 f2-e3 c7-d6 b2-c3 c5-b4",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 h2-g3 b8-c7 f2-e3 c7-d6 e3-f4 f6-e5",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b8-c7 b2-c3 b6-c5 a1-b2 c5-b4 c3-d4 b4-c3",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b8-c7 f2-e3 b6-c5 h2-g3 c7-d6 e3-f4 f6-g5",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 f6-e5 b2-c3 g7-f6 f2-e3 h8-g7 a1-b2 b6-c5",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 f6-e5 h2-g3 g7-f6 f2-e3 h8-g7 b2-c3 b8-c7",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 f2-e3 g7-h6 e3xg5 h6xf4 b2-a3 f8-g7 c1-b2 b8-c7 d2-e3 f4xd2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 f2-e3 g7-h6 e3xg5 h6xf4 d2-e3 f4xd2 e1xc3 b8-c7 b2-a3 c7-d6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 f2-e3 g7-h6 e3xg5 h6xf4 d2-e3 f4xd2 e1xc3 f8-g7 h2-g3 g7-h6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 f2-e3 g7-h6 e3xg5 h6xf4 e1-f2 f8-g7 f2-g3 a5-b4 c5xa3 f6-g5",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 f2-g3 f6-e5 d4xf6 g7xe5 e1-f2 b6xd4 f2-e3 d4xf2 g1xg5 a7-b6",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 g7-h6 e3xg5 h6xf4 d2-e3 f4xd2 e1xc3 f8-g7 h2-g3 g7-h6 b2-a3",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 g7-h6 e3xg5 h6xf4 e1-f2 f8-g7 d2-c3 b8-c7 f2-g3 f4-e3 d4xf2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 g7-h6 e3xg5 h6xf4 e1-f2 f8-g7 d2-c3 f4-e3 f2-g3 b8-c7 d4xf2",
        "c3-d4 h6-g5 g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 g7-h6 e3xg5 h6xf4 e1-f2 f8-g7 f2-g3 a5-b4 c5xa3 f6-g5 g3xe5",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 a7-b6 g3-f4 g7-h6 h2-g3 d6-e5 f4xd6 c7xc3 d2xb4 a5xc3 b2xd4 e7-d6 a1-b2 f6-e5 d4xf6 g5xe7",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 b2-c3 g7-h6 g3-f4 d6-c5 e7-d6 g1-h2 f6-e5 d4xf6 g5xe7 c3-d4 c5-b4 a3xc5 d6xb4 d2-c3",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 d2-c3 g7-h6 g1-f2 d6-c5 b8-c7 f4-e5 c7-d6 e5xg7 h8xf6 f2-g3 c5-b4 a3xc5 d6xf4 g3xg7",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 d2-c3 g7-h6 g1-f2 d6-c5 e7-d6 d4-e5 f6xd4 c3xc7 b8xd6 h4xf6 f8-g7 f2-g3 g7xe5 g3-h4",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 g7-h6 b2-c3 c7-b6 b4-a5 b6-c5 g3-f4 c5-b4 c3-d4 b4-a3 a1-b2",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 g7-h6 b2-c3 d6-e5 b4-a5 f8-g7 c3-d4 e5xc3 d2xb4 g5-f4 g3xe5",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g1-f2 b6-c5 d4xb6 a7xc5 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 g3-f4 g7-h6 f4-e5 f6xd4 e3xc5",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g1-f2 g7-h6 b2-c3 b6-c5 d4xb6 a5xc7 c3-d4 a7-b6 d2-c3 b6-a5 c1-d2 c7-b6 g3-f4 b6-c5",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 g7-h6 b2-c3 b6-c5 d4xb6 a5xc7 c3-b4 d6-e5 f4xd6 c7xe5 e1-f2 a7-b6 b4-a5 b6-c5",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 g7-h6 h2-g3 b6-c5 d4xb6 a5xc7 b2-c3 a7-b6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 g7-h6 h2-g3 b6-c5 d4xb6 a7xc5 b2-c3 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 e1-f2 e7-d6",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 g7-h6 h2-g3 b6-c5 d4xb6 a7xc5 e3-d4 c5xe3 a3-b4 a5xc3 b2xf2 g5xe3 d2xf4 f6-g5",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 g7-h6 h2-g3 b6-c5 d4xb6 a7xc5 e3-d4 g5xe3 d4xf2 b8-c7 b2-c3 c5-b4 a3xc5 d6xb4",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 g7-h6 h2-g3 b6-c5 d4xb6 a7xc5 e3-d4 g5xe3 d4xf2 f8-g7 b2-c3 c5-b4 a3xc5 d6xb4",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 g7-h6 h2-g3 d6-c5 a3-b4 a5xe5 f4xb4 f8-g7 g3-f4 e7-d6 b2-a3 d8-c7 g1-h2 d6-c5",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 g7-h6 h2-g3 d6-c5 a5xe5 f4xb4 e7-d6 b4-a5 d8-c7 b2-c3 b6-c5 c3-d4 a7-b6 g3-f4",
        "c3-d4 h6-g5 g3-h4 b6-a5 f2-g3 g7-h6 g3-f4 c7-b6 h2-g3 d6-c5 a3-b4 a5xe5 f4xb4 e7-d6 g3-f4 d8-c7 g1-h2 d6-c5 b4xd6 c7xg3",
        "c3-d4 h6-g5 g3-h4 b6-a5 h2-g3 c7-b6 g3-f4 g7-h6 d4-e5 f6xd4 h4xf6 e7xg5 e3xe7 d8xf6 d2-e3 b6-c5 b2-c3 f8-e7 f2-g3 e7-d6",
        "c3-d4 h6-g5 g3-h4 b6-a5 h2-g3 d6-e5 b2-c3 g7-h6 g1-h2 a7-b6 a3-b4 c7-d6 a1-b2 g5-f4 e3xg5 h6xf4 d2-e3 f4xd2 c1xe3 b8-a7",
        "c3-d4 h6-g5 g3-h4 b6-a5 h2-g3 d6-e5 b2-c3 g7-h6 g1-h2 a7-b6 a3-b4 c7-d6 a1-b2 g5-f4 e3xg5 h6xf4 f2-e3 b8-a7 e3xg5 b6-c5",
        "c3-d4 h6-g5 g3-h4 b6-a5 h2-g3 d6-e5 b2-c3 g7-h6 g1-h2 a7-b6 c7-d6 a1-b2 g5-f4 e3xg5 h6xf4 d2-e3 f4xd2 c1xe3 b8-a7 b2-a3",
        "c3-d4 h6-g5 g3-h4 b6-a5 h2-g3 d6-e5 g1-h2 e5xc3 d2xb4 a5xc3 b2xd4 c7-b6 a3-b4 b6-c5 b4xd6 e7xc5 d4xb6 a7xc5 a1-b2 c5-d4",
        "c3-d4 h6-g5 g3-h4 b6-a5 h2-g3 d6-e5 g1-h2 e5xc3 d2xb4 a5xc3 b2xd4 c7-b6 a3-b4 g7-h6 b4-a5 b6-c5 d4xb6 a7xc5 a1-b2 f8-g7",
        "c3-d4 h6-g5 g3-h4 d6-c5 b2-c3 e7-d6 h2-g3 g7-h6 g3-f4 f6-e5 h4xf6 e5xg7 f2-g3 b6-a5 d4xb6 a7xc5 c3-d4 c7-b6 d4-e5 d8-e7",
        "c3-d4 h6-g5 g3-h4 d6-c5 b2-c3 e7-d6 h2-g3 g7-h6 g3-f4 f6-e5 h4xf6 e5xg7 f2-g3 b6-a5 d4xb6 a7xc5 g3-h4 c7-b6 c3-b4 a5xc3",
        "c3-d4 h6-g5 g3-h4 d6-c5 b2-c3 e7-d6 h2-g3 g7-h6 g3-f4 f6-e5 h4xf6 e5xg7 f2-g3 b6-a5 d4xb6 a7xc5 g3-h4 c7-b6 g1-f2 b8-a7",
        "c3-d4 h6-g5 g3-h4 d6-c5 b2-c3 g7-h6 c3-b4 g5-f4 b4xd6 c7xc3 e3xg5 h6xf4 d2xb4 f8-g7 b4-a5 b8-c7 f2-e3 f4xd2 c1xe3 b6-c5",
        "c3-d4 h6-g5 g3-h4 d6-c5 b2-c3 g7-h6 f2-g3 c7-d6 g3-f4 b6-a5 d4xb6 a5xc7 h2-g3 d6-c5 c3-b4 c7-b6 b4xd6 e7xc5 a1-b2 d8-c7",
        "c3-d4 h6-g5 g3-h4 d6-c5 b2-c3 g7-h6 h2-g3 e7-d6 g3-f4 f6-e5 d4xf6 g5xe7 c3-b4 b6-a5 d2-c3 e7-f6 c1-b2 a7-b6 f2-g3 f8-g7",
        "c3-d4 h6-g5 g3-h4 d6-c5 b2-c3 g7-h6 h2-g3 e7-d6 g3-f4 f6-e5 h4xf6 e5xg3 f2xh4 d6-e5 e1-f2 e5xg7 g1-h2 f8-e7 a1-b2 e7-f6",
        "c3-d4 h6-g5 g3-h4 d6-c5 d2-c3 g7-h6 c3-b4 g5-f4 b4xd6 c7xc3 b2xd4 f4xd2 c1xe3 f8-g7 d4-c5 b6xd4 e3xc5 b8-c7 f2-e3 f6-e5",
        "c3-d4 h6-g5 g3-h4 d6-c5 f2-g3 e7-d6 g3-f4 g7-h6 b2-c3 f6-e5 h4xf6 e5xg7 h2-g3 b6-a5 d4xb6 a7xc5 g3-h4 c7-b6 c1-b2 b8-a7",
        "c3-d4 h6-g5 g3-h4 d6-c5 f2-g3 e7-d6 g3-f4 g7-h6 b2-c3 f6-e5 h4xf6 e5xg7 h2-g3 b6-a5 d4xb6 a7xc5 g3-h4 c7-b6 c1-b2 f8-e7",
        "c3-d4 h6-g5 g3-h4 d6-c5 f2-g3 e7-d6 g3-f4 g7-h6 h2-g3 f6-e5 h4xf6 e5xg7 g3-h4 b6-a5 d4xb6 a7xc5 b2-c3 c7-b6 c1-b2 b8-a7",
        "c3-d4 h6-g5 g3-h4 d6-c5 f2-g3 g7-h6 b2-c3 e7-d6 a1-b2 f6-e5 d4xf6 g5xe7 c3-d4 d6-e5 d4xf6 e7xg5 h4xf6 c5-b4 a3xc5 b6xh4",
        "c3-d4 h6-g5 g3-h4 d6-c5 h2-g3 e7-d6 b2-c3 g7-h6 c3-b4 f6-e5 d4xf6 g5xe7 b4-a5 h8-g7 g3-f4 g7-f6 a1-b2 f6-e5 g1-h2 e5xg3",
        "c3-d4 h6-g5 g3-h4 d6-c5 h4xf6 g7xc3 d2xd6 c7xe5 a5xc7 b8xd6 b2-c3 h8-g7 h2-g3 a7-b6 g3-h4 g7-h6 f2-g3 d8-c7 e3-f4 e7-f6",
        "c3-d4 h6-g5 g3-h4 d6-c5 h4xf6 g7xc3 d2xd6 c7xe5 a5xc7 b8xd6 e3-d4 e5xc3 b2xd4 h8-g7 a1-b2 g7-f6 b2-c3 a7-b6 h2-g3 f8-g7",
        "c3-d4 h6-g5 g3-h4 d6-e5 b2-c3 b6-a5 f2-g3 g7-h6 g3-f4 e5xg3 h4xf2 g5-h4 a1-b2 f6-g5 h2-g3 h8-g7 g3-f4 c7-b6 d4-c5 b6xd4",
        "c3-d4 h6-g5 g3-h4 d6-e5 f2-g3 e5xc3 d2xb4 g7-h6 g3-f4 b6-a5 a5xc3 d2xb4 e7-d6 h2-g3 d6-e5 f4xd6 c7xe5 b4-a5 f8-g7 g3-f4",
        "c3-d4 h6-g5 g3-h4 d6-e5 f2-g3 e5xc3 d2xb4 g7-h6 g3-f4 b6-a5 c1-d2 a5xc3 d2xb4 e7-d6 b2-c3 d6-e5 f4xd6 c7xe5 e3-d4 g5-f4",
        "c3-d4 h6-g5 g3-h4 d6-e5 f2-g3 e5xc3 d2xb4 g7-h6 g3-f4 b6-c5 b4xd6 c7xg3 h2xf4 a7-b6 a3-b4 b2-a3 f8-g7 a1-b2 d8-c7 b4-a5",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 b2xd4 b6-a5 g3-f4 g7-h6 c7-b6 b2-c3 e7-d6 f2-g3 f8-e7 f4-e5 d6xh2 e3-f4 g5xc5 c3-b4",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 b2xd4 c7-d6 g3-f4 g7-h6 b6-a5 f2-g3 a7-b6 e1-d2 b6-c5 d4xb6 a5xc7 a1-b2 d6-c5 c3-b4",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 b2xd4 c7-d6 g3-f4 g7-h6 b6-a5 f2-g3 a7-b6 e1-d2 b6-c5 d4xb6 a5xc7 a1-b2 d6-c5 g1-h2",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 b2xd4 c7-d6 g3-f4 g7-h6 b6-a5 f2-g3 a7-b6 e1-d2 b6-c5 d4xb6 a5xc7 c3-b4 f6-e5 h4xd4",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 b2xd4 c7-d6 g3-f4 g7-h6 b6-a5 f2-g3 a7-b6 e1-d2 b6-c5 d4xb6 a5xc7 g1-h2 c7-b6 c3-d4",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 b2xd4 c7-d6 g3-f4 g7-h6 d2-c3 b6-a5 f2-g3 a7-b6 e1-d2 b6-c5 d4xb6 a5xc7 a1-b2 d6-c5",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 b2xd4 c7-d6 g3-f4 g7-h6 d2-c3 b6-a5 f2-g3 a7-b6 e1-d2 b6-c5 d4xb6 a5xc7 c3-b4 f6-e5",
        "c3-d4 h6-g5 g3-h4 d6-e5 h2-g3 e5xc3 b2xd4 c7-d6 g3-f4 g7-h6 d2-c3 b6-a5 f2-g3 a7-b6 e1-d2 b6-c5 d4xb6 a5xc7 g1-h2 c7-b6",
        "c3-d4 h6-g5 g3-h4 e7-f6 d4-c5 g7-h6 h2-g3 c7-d6 b6-a5 c3-d4 f6-e5 f2-g3 a7-b6 d4-e5 d8-e7 b2-c3 g7-f6 c3-d4 f6-g5 a1-b2",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f8-g7 a1-b2 b8-c7 d2-c3 g5-f4 b2-a3 c7-d6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f8-g7 a1-b2 d8-c7 b2-c3 e7-d6 c5xe7 f6xd8",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-c3 d6xb4 c3xa5 g5-f4 a1-b2 b8-c7 b2-c3 f8-g7 c3-b4 e7-d6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-c3 d6xb4 c3xa5 g5-f4 a1-b2 h8-g7 b2-a3 b8-c7 a3-b4 e7-d6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 d6xb4 a3xc5 b8-c7 a1-b2 f8-g7 b2-a3 c7-b6 d2-e3 b6xd4 e3xc5",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 d6xb4 a3xc5 f8-g7 a1-b2 b8-c7 d2-c3 g5-f4 b2-a3 c7-d6 c3-b4",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 d6xb4 a3xc5 f8-g7 a1-b2 b8-c7 d2-c3 g5-f4 b2-a3 c7-d6 c5-b6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 d6xb4 c3xa5 g5-f4 a1-b2 h8-g7 b2-a3 b8-c7 a3-b4 e7-d6 b4-c5",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 b2-c3 c7-b6 c3-d4 b8-c7 a1-b2 e7-d6 c5xe7 g5-f4 e7xe3 h6-g5",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 b2-c3 c7-b6 c3-d4 b8-c7 c1-b2 g5-f4 f2-g3 h6-g5 g3xe5 e7-d6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 b2-c3 c7-b6 c3-d4 b8-c7 d4-e5 b6xd4 e5xc3 g5-f4 f2-g3 h6-g5",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 b2-c3 c7-b6 c3-d4 b8-c7 f2-g3 c7-d6 d4-e5 d6xb4 d2-c3 f6xb2",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 b2-c3 c7-b6 c3-d4 b8-c7 h2-g3 c7-d6 d2-e3 d6xb4 d4-e5 f6xd4",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 c7-b6 c3-d4 b8-c7 a1-b2 e7-d6 c5xe7 g5-f4 e7xe3 h6-g5 h4xf6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 c7-b6 c3-d4 b8-c7 c1-b2 g5-f4 f2-g3 h6-g5 g3xe5 e7-d6 c5xe7",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 c7-b6 c3-d4 b8-c7 d4-e5 b6xd4 e5xc3 g5-f4 a1-b2 f6-g5 h4xf6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 c7-b6 c3-d4 b8-c7 f2-g3 c7-d6 d4-e5 d6xb4 d2-c3 f6xb2 a1xc7",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 c7-b6 c3-d4 b8-c7 h2-g3 c7-d6 d2-e3 d6xb4 d4-e5 f6xd4 e3xa3",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 c7-b6 d2-e3 b6xd4 e3xc5 b8-c7 c1-d2 g5-f4 d2-c3 f6-g5 h4xf6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f8-g7 g5-f4 c3-b4 f6-g5 h4xf6 g7xe5 a1-b2 h8-g7 b2-a3 c7-d6 f2-g3",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 b2-c3 f8-g7 c3-b4 c7-d6 a1-b2 b8-c7 b2-a3 f6-g5 h4xf6 g7xe5",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 f8-g7 a1-b2 f6-g5 h4xf6 g7xe5 f2-g3 h8-g7 b2-c3 e7-f6 c5-d6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f8-g7 a1-b2 d8-c7 b2-c3 e7-d6 c5xe7 f6xd8",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 c7-d6 b2-a3 d6xb4 a3xc5 f8-g7 a1-b2 g5-f4 b2-a3 b8-c7 d2-c3 c7-d6",
        "c3-d4 h6-g5 g3-h4 g7-h6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 c7-d6 b2-c3 d6xb4 c3xa5 g5-f4 a1-b2 b8-c7 b2-c3 f8-g7 c3-b4 e7-d6",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-c5 g3-f4 e7-d6 h2-g3 f6-e5 d4xf6 g5xe7 b2-c3 b6-a5 c3-b4 a5xc3 d2xb4 e7-f6 a1-b2 f6-g5",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-c5 g3-f4 e7-d6 h2-g3 f6-e5 h4xf6 e5xg7 g3-h4 b6-a5 d4xb6 a7xc5 b2-c3 c7-b6 g1-h2 b8-a7",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g1-f2 e5xc3 b2xd4 b6-a5 c7-b6 b2-c3 e7-d6 c1-b2 d6-e5 a3-b4 g5-f4 e3xe7 f8xd6 d4xf6",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g1-f2 e5xc3 d2xb4 b6-a5 c1-d2 a5xc3 b2xd4 e7-d6 d4-e5 d6xf4 g3xg7 h8xf6 h2-g3 a7-b6",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g3-f4 e5xc3 d2xb4 e7-d6 d6-e5 f4xd6 c7xe5 a5xc7 b8xd6 e1-f2 f8-e7 e3-d4 e5xc3 b2xd4",
        "c3-d4 h6-g5 g3-h4 g7-h6 f2-g3 d6-e5 g3-f4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 f2-e3 f6-g5 b2-c3 h8-g7 c3-b4 g7-h6 b4-a5 e7-d6",
        "c3-d4 h6-g5 g3-h4 g7-h6 h2-g3 d6-e5 g1-h2 e5xc3 b2xd4 b6-a5 a1-b2 c7-b6 b2-c3 e7-d6 c1-b2 d6-e5 g3-f4 e5xg3 h2xf4 b6-c5",
        "c3-d4 h6-g5 g3-h4 g7-h6 h2-g3 d6-e5 g1-h2 e5xc3 b2xd4 b6-a5 c7-b6 b2-c3 e7-d6 c1-b2 d6-e5 a3-b4 b8-c7 b4-c5 g5-f4 e3xe7",
        "c3-d4 h6-g5 g3-h4 g7-h6 h2-g3 d6-e5 g1-h2 e5xc3 b2xd4 b6-a5 c7-b6 b2-c3 e7-d6 c1-b2 d6-e5 a3-b4 g5-f4 e3xe7 f8xd6 d4xf6",
        "c3-d4 h6-g5 g3-h4 g7-h6 h2-g3 d6-e5 g1-h2 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 a1-b2 f8-g7 d2-c3 b8-a7 c3-b4 f6-e5 h4xb6 c7xa1",
        "c3-d4 h6-g5 g3-h4 g7-h6 h2-g3 d6-e5 g1-h2 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 a1-b2 f8-g7 d2-c3 b8-a7 c3-d4 g5-f4 d4xb6 f4xd2",
        "c3-d4 h6-g5 g3-h4 g7-h6 h2-g3 d6-e5 g1-h2 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 a1-b2 f8-g7 d2-c3 b8-a7 g3-f4 c7-b6 c1-d2 e7-d6",
        "c3-d4 h6-g5 g3-h4 g7-h6 h2-g3 d6-e5 g1-h2 e5xc3 d2xb4 b6-c5 b4xd6 e7xc5 b2-c3 f8-g7 c1-d2 a7-b6 c3-b4 c7-d6 b4-a5 d6-e5",
        "c3-d4 h6-g5 g3-h4 g7-h6 h4xf6 e7xg5 h2-g3 h8-g7 g3-h4 g7-f6 d4-c5 d6xb4 a5xc3 c7-d6 f2-g3 b6-a5 g3-f4 a7-b6 c3-d4 f6-e5",
        "c3-d4 h8-g7 b2-c3 g5-f4 a1-b2 b6-a5 e7-d6 f2-g3 f8-e7 e1-f2 c7-d6 b2-a3 d8-c7 f2-g3 f6-g5 g1-f2 g5-h4 d2-e3 c7-d6 d4-c5",
        // --- c3-b4 (624 linhas de campeonato) ---
        "c3-b4 f6-e5 e3-f4 e7-f6 b2-c3 b6-c5 d2-e3 f8-e7",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g3-h4",
        "c3-b4 f6-e5 f6-g5 g3-h4 e5-f4 g5-f4 e3xg5 h6xf4",
        "c3-b4 d6-e5 b4-a5 b6-c5 d2-c3 c5-b4 a3xc5 c7-b6 a5xc7 b8xf4",
        "c3-b4 f6-g5 f4-e5 g5-h4 b2-c3 h6-g5 c3-d4 g7-h6 g5-f4 b6-c5",
        "c3-b4 a3xc5 e3-d4 c5xe3 g3-f4 e3xg5 h4xh8 g5-f6 e5xg7 e7xg5 h4xb6",
        "c3-b4 d6-e5 f4xd6 h2xf4 e3xg5 f6xh4 b4-c5 b6xd4 d2-c3 e7xc5 c3xe5",
        "c3-b4 h2xf4 e3xg5 f6xh4 b4-a5 g7-f6 d2-c3 f6-g5 a3-b4 b6-c5 d4xb6 a7xa3",
        "c3-b4 b6-a5 d2-c3 c7-b6 c3-d4 a5-b4 b4-a3 b2-c3 b8-c7 g3-f4 f8-g7 f4-g5 e7-d6",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 g5-h4 c3-d4 h4xf2 a5xc3",
        "c3-b4 b6-c5 g3-h4 f6-g5 h2-g3 h8-g7 g3-h4 g7-f6 e5-d4 e1-f2 a7-b6 g3-f4 d4-c3 d6-e5",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 f2-e3 e5-d4 c3xe5 c5-b4 a3xe7 d8xh4",
        "c3-b4 f6-e5 b4-c5 b2-c3 g7-f6 h8-g7 g3-f4 a7-b6 a1-b2 f6-e5 d2-e3 e3-f4 a3-b4 c1-d2",
        "c3-b4 h6-g5 g3-h4 d6-e5 h2-g3 g7-h6 g1-h2 f8-g7 e3-f4 g5xg1 b6xd4 e1-f2 g1xe3 d2xf8",
        "c3-b4 b6-a5 b2-c3 f6-g5 a1-b2 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 e7-f6 g3xe5 f6xd4 c3xe5 a5xa1",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 a7-b6 c5-b4 a3xa7 d6-e5 f4xd6 c7xa1",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 f2-g3 g5-h4 c3-d4 h4xf2 a5xc3",
        "c3-b4 h6-g5 g3-h4 d6-e5 h2-g3 g7-h6 g1-h2 f8-g7 e3-f4 g5xg1 b4-c5 b6xd4 e1-f2 g1xe3 d2xf8",
        "c3-b4 b6-a5 b2-c3 f6-g5 a1-b2 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 f2-g3 e7-f6 g3xe5 f6xd4 c3xe5 a5xa1",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 a7-b6 c3-d4 c5-b4 a3xa7 d6-e5 f4xd6 c7xa1",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 f6-e5 f4-g5 h6xh2 e3-d4 c5xe3 f2xh8",
        "c3-b4 d6-c5 b4xd6 e7xc5 g3-h4 f6-e5 f2-g3 c5-b4 a5xc3 b6-a5 d8-e7 f4xd6 e7xc5 c3-b4 a5xc3 b2xd8",
        "c3-b4 d6-e5 b4-a5 b6-c5 b2-c3 c5-d4 e3xc5 e5-f4 g3xe5 f6xb2 a1xc3 c7-b6 a5xc7 d8xb2 d2-c3 b2xd4",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 a1-b2 b6-c5 b4xd6 e7xc5 c3-b4 f4-e3 f2xb6 c7xa1",
        "c3-b4 f6-g5 f4-e5 g5-f4 c7-d6 a1-b2 d6-e5 b4-a5 b8-c7 c3-b4 g7-f6 b2-c3 h8-g7 d2-e3 e5-d4 f2-e3",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 c5-d4 a1-b2 g7-f6 d2-e3 c7-b6 e3xc5 b6xd4 g3-h4 e5xg3 c3xc7 b8xd6 h2xf4",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 a1-b2 g5-h4 b4-a5 f6-e5 c3-b4 e5xg3 h2xf4 h8-g7 d2-c3 g7-f6 f2-g3",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 h2-g3 f6-e5 f4-g5 h6xh2 e3-d4 c5xe3 f2xh8",
        "c3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g7-f6 g3-f4 e5xg3 h2xf4 f6-g5 d2-e3 h8-g7 c5-d6 c7xg3 f2xh8",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 h8-g7 a7-b6 a3-b4 e5-d4 e3xa7 d6-e5 f4xd6 e7xc1",
        "c3-b4 f6-g5 d4-c5 c7-b6 d2-e3 d8-c7 e7-d6 a3-b4 g7-f6 b4-a5 f6-e5 a1-b2 a7-b6 b2-a3 f8-e7 a3-b4 e7-f6",
        "c3-b4 h6-g5 b4-a5 g5-h4 c3-d4 g7-h6 f6-g5 b2-c3 c7-b6 a1-b2 f8-g7 g3-f4 b8-c7 h2-g3 a7-b6 g1-f2 g7-f6",
        "c3-b4 b6-c5 b2-c3 f6-e5 a1-b2 g7-f6 e1-d2 h8-g7 d8-c7 b4-a5 e5-d4 c1-d2 d6-c5 b2-c3 e7-d6 c1-b2 f8-e7 b2-a3",
        "c3-b4 b6-c5 b4-a5 f6-g5 b2-c3 g7-f6 c3-b4 f6-e5 d2-c3 b8-c7 e7-f6 c3-d4 f4-e5 d2-c1 a5-b6 f8-e7 b6-a7 f6-e5",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 f6-e5 c3-b4 e5xg3 f2xf6 e7xg5 h2-g3 c7-b6 a5xe5 g5-h4 b4xd6 h4xf6",
        "c3-b4 d6-c5 b4xd6 e7xc5 d2-c3 h6-g5 c3-b4 g7-h6 b4xd6 c7xe5 a5xc7 d8xb6 c1-d2 g5-f4 e3xe7 f8xd6 b2-c3 b6-c5",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 h8-g7 b4-a5 a7-b6 a3-b4 e5-d4 e3xa7 d6-e5 f4xd6 e7xc1",
        "c3-b4 b6-c5 b2-c3 f6-e5 g3-f4 h8-g7 c3-d4 e7-f6 f4-g5 d2-e3 g7-h6 e3-d4 h6-g5 b4-c5 b8-a7 c1-d2 c7-d6 d4-c5 f6-e5",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 a7-b6 f2-g3 h4xf2 e1xg3 c5-b4 a3xa7 d6-e5 f4xd6 c7xa1",
        "c3-b4 f6-e5 b2-c3 g7-f6 e3-f4 b6-a5 d2-e3 c7-b6 c3-d4 e5xc3 b4xd2 f6-e5 e3-d4 e5xc3 d2xb4 a5xc3 f4-g5 h6xf4 g3xa5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 f6-g5 h4xf6 e7xg5 a1-b2 d6-e5 b4xd6 f4-g3 f2xd4 c7xa1",
        "c3-b4 f6-g5 e3-d4 g5-h4 b4-c5 d6xb4 a3xc5 g7-f6 d2-e3 b6-a5 c7-b6 a1-b2 d8-c7 b2-c3 f6-e5 d4xd8 b6xb2 d8xb6 a7xc5",
        "c3-b4 a3xc5 c1-d2 c5-b4 a5xc3 d6-c5 c3-b4 c5xa3 d2-c3 c7-d6 e3-f4 b6-c5 d4xb6 a7xc5 f4-g5 d6-e5 g5-h6 c5-d4 c3-b4 a3xc5",
        "c3-b4 a5xc3 d2xb4 f6-e5 e3-f4 e5xg3 h2xf4 g7-f6 b2-c3 b6-a5 f6-g5 g3-h4 g5xe3 e1-d2 h8-g7 d2xf4 g7-f6 f4-g5 a7-b6 g1-f2",
        "c3-b4 a7-b6 b2-c3 f6-g5 a1-b2 g7-f6 b2-a3 g5-h4 f6-e5 g3-f4 h8-g7 b4-a5 g7-f6 f4-g5 d6-e5 g5-h6 e5-f4 d2-c3 f4-g3 g1-h2",
        "c3-b4 b2-c3 g3xe5 e3xg5 f6-g5 g5-f4 d6xf4 h6xf4 b4-a5 a1-b2 c3-b4 b2-c3 g7-f6 h8-g7 f6-e5 e7-d6 d2-e3 c1xe3 c3-d4 b4xd2",
        "c3-b4 b4-a5 e3-d4 b2xd4 d6-e5 f6-g5 e5xc3 g5-h4 g3-f4 f4-g5 f2-g3 e1xg7 g7-f6 h6xf4 h4xf2 h8xf6 a1-b2 b2-c3 h2-g3 d2xf4",
        "c3-b4 b4-a5 g3-h4 h4xf6 d6-e5 f6-g5 e5-f4 e7xg5 f2-g3 g3xe5 a5xc7 b2-c3 b6-c5 c7-b6 b8xf4 g7-f6 c3-b4 b4xd6 a1-b2 b2-c3",
        "c3-b4 b4-c5 a3xc5 e3xc5 f6-g5 d6xb4 b6xd4 e7-f6 d2-e3 b2-a3 a1-b2 b2-c3 g5-h4 f6-g5 g7-f6 d8-e7 a3-b4 c5xe7 c3-d4 g3-f4",
        "c3-b4 b4-c5 a3xc5 e3xc5 f6-g5 d6xb4 b6xd4 g5-f4 g3xe5 c5-d6 f2-e3 h2-g3 c7-b6 e7xc5 c5-b4 b4-a3 b2-c3 e3-f4 a1-b2 c3-d4",
        "c3-b4 b4-c5 a3xc5 e3xc5 f6-g5 d6xb4 b6xd4 g5-h4 b2-c3 a1-b2 c3-b4 b2-a3 h6-g5 g7-h6 h8-g7 g7-f6 d2-e3 e1-d2 e3xc5 d2-e3",
        "c3-b4 b4-c5 e3xc5 a3xc5 f6-g5 b6xd4 d6xb4 g7-f6 b2-c3 g3-f4 d2-e3 a1-b2 g5-h4 f6-g5 h8-g7 c7-b6 c3-b4 e3xc5 f2xd4 e1-f2",
        "c3-b4 b4-c5 g7-f6 b2-c3 e7-d6 h6-g5 d4-c5 f6-e5 b2-c3 h8-g7 c3-b4 g7-h6 d2-c3 f8-e7 c3-d4 e7-d6 d2-c3 g5-f4 c3-d4 f4-g3",
        "c3-b4 b6-a5 b2-c3 c7-b6 c3-d4 g7-h6 g3-f4 b6-c5 c5-b4 a1-b2 b8-c7 b2-c3 c7-d6 f2-e3 b4-a3 h2-g3 a7-b6 g5-h6 h8-g7 g1-h2",
        "c3-b4 b6-a5 b2-c3 c7-b6 e3-d4 b6-c5 d4xb6 a5xc7 b4-c5 d6xb4 c3xa5 e7-d6 a1-b2 f8-g7 a3-b4 a7-b6 b2-a3 f6-g5 d2-c3 g5-h4",
        "c3-b4 b6-a5 b2-c3 c7-b6 e3-f4 b6-c5 d2-e3 f6-e5 g3-h4 e5xg3 h2xf4 g7-f6 c1-b2 f6-e5 g1-h2 e5xg3 h2xf4 d8-c7 e1-d2 h8-g7",
        "c3-b4 b6-a5 b2-c3 c7-b6 g3-h4 b6-c5 f2-g3 a7-b6 g3-f4 e5xg3 h4xf2 f6-g5 h2-g3 g5-h4 g3-f4 e7-f6 f4-g5 h6xf4 e3xe7 d8xf6",
        "c3-b4 b6-a5 b2-c3 e5-f4 e3xg5 f6xh4 b4-c5 d6xb4 a3xc5 g7-f6 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 c7-d6 b2-a3 d6xb4 a3xc5",
        "c3-b4 b6-a5 b2-c3 f6-e5 e3-d4 d2-e3 e5-d4 c7-b6 c1-d2 a7-b6 b4-a5 b6-c5 e1-d2 h8-g7 g1-f2 d6-e5 g3-h4 g7-f6 h2-g3 e7-d6",
        "c3-b4 b6-a5 b2-c3 f6-e5 g3-f4 e7-f6 h2-g3 f6-e5 g7-f6 e3-d4 c7-b6 b4-c5 f8-e7 c3-b4 h6-g7 g7-f8 d4-c3 d8-c7 c7-d6 c1-d2",
        "c3-b4 b6-a5 b2-c3 f6-g5 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 g7-f6 f6-g5 c5-b6 a7xc5 d4xb6 h8-g7 g3-f4 c7-d6 b6-a7 a5-b4 b2-c3",
        "c3-b4 b6-a5 b2-c3 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-c5 d6xb4 a3xc5 g7-f6 a1-b2 h8-g7 c3-d4 c7-d6 b2-a3 d6xb4 a3xc5 d8-c7",
        "c3-b4 b6-a5 b2-c3 h6-g5 g3-f4 g7-h6 f2-g3 f8-g7 c1-b2 c5-d4 e3xe7 g5xe3 e7xg5 h6xf4 g3xe5 e3-d2 e5-f6 g7xe5 b4-c5 d2xd6",
        "c3-b4 b6-a5 b4-a5 h6-g5 a3-b4 d6-e5 b2-a3 g5-f4 d2-c3 g7-f6 c3-d4 h8-g7 a3-b4 f6-e5 d2-c3 g7-f6 c3-d4 f6-e5 a1-b2 a7-b6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 f6-g5 f2-e3 g7-f6 e3-d4 g5xe3 d2xf4 f6-g5 e1-d2 g5xe3",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 b2-c3 e5-f4 e3xg5 h6xf4 c7-b6 c3-d4 e7-f6 d2-c3 f4-e3 e1-d2 a5-b4 c3xc7 b8xb4 d2xf4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 b2-c3 e5-f4 e3xg5 h6xf4 g7-f6 f2-e3 h8-g7 e3xg5 g7-h6 g1-f2 h6xf4 f2-e3 f6-e5 e3xg5",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 b2-c3 e5-f4 g3xe5 c7-d6 e5xc7 d8xb2 a1xc3 h6-g5 h2-g3 g5-h4 g3-f4 a7-b6 e3-d4 e7-d6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 g3-f4 e5xg3 f2xh4 f6-e5 e3-f4 e5xg3 h4xf2 h6-g5 h2-g3 g5-h4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 h8-g7 e5xg3 h2xf4 c7-b6 c3-b4 a5xc3 b2xd4 f6-g5 f2-g3 g5-h4 a1-b2",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 b2-c3 g7-f6 c1-b2 h8-g7 g3-f4 e5xg3 h2xf4 c7-b6 c3-b4 a5xc3 b2xd4 f6-g5 a1-b2 e7-d6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 f6-g5 g1-h2 g5-h4 c3-b4 a5xc3 d2xb4 h8-g7 a1-b2 g7-f6",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 e3-d4 h8-g7 f2-g3 f6-g5 g3-h4 g5xe3 d4xf2 c7-b6 d2-e3 b6xd4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 f6-g5 b2-a3 g5-h4 c1-b2 h8-g7 c5-d6 c7xg3 e3-f4 g3xe5 c3-b4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 f6-g5 d2-e3 g5-h4 c1-d2 c7-b6 g1-h2 d8-c7 f2-g3 h4xf2 e3xg1",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 c3-b4 a5xc3 d2xb4 d6-e5 b4-a5 g5-f4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 b2-a3 c7-b6 c3-d4 d8-c7 g3-f4 a5-b4 c5-d6 c7xg3 a3xc5 f6-g5",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 g3-f4 f6-g5 c3-d4 c7-b6 b2-c3 h8-g7 c1-b2 e7-f6 f4-e5 d8-c7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 h8-g7 g5-h6 f6-e5 a1-b2",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b2-a3 f6-g5 c3-b4 a5xc3 d2xb4 c7-b6 c1-d2 b6xd4 e3xc5 h8-g7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 c7-b6 g3-f4 f6-g5 f4-e5 h8-g7 e5-d6 g5-f4 e3xg5 h4xf6 b2-c3",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 c7-b6 c3-d4 d8-c7 a1-b2 e7-d6 c5xe7 f6xd8 b2-c3 c7-d6 f2-g3 g5-h4",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 b2-c3 g7-f6 g3-f4 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 c7-b6 c1-b2 b6xd4 d2-e3 b8-c7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 d2-c3 e7-d6 c5xe7 f8xd6 c3-d4 a7-b6 e1-d2 b6-c5 d4xb6 a5xc7 d2-c3 c7-b6 c3-d4 b8-c7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g7-f6 d2-e3 g5-h4 g3-f4 c7-b6 b2-c3 f6-g5 a1-b2 e7-d6 c5xe7 f8xd6 d4-e5 d8-e7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g5-h4 b2-c3 g7-f6 f4-g5 h6xf4 e3xg5 c7-d6 c3-b4 a5xc3 d2xb4 h8-g7 g5-h6 d8-c7",
        "c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 c7-b6 a1-b2 b6xd4 d2-e3 b8-c7",
        "c3-b4 b6-a5 b4-c5 f6-e5 e3-f4 g7-f6 b2-c3 f6-e5 c3-b4 b8-c7 a1-b2 h6-g5 b2-a3 e5-f4 d2-e3 f8-g7 g1-h2 g5-f4 g7-h6 g5-f6",
        "c3-b4 b6-a5 b4-c5 f6-e5 e3-f4 g7-f6 b2-c3 f6-e5 d2-e3 b8-c7 a1-b2 c7-b6 e1-d2 h8-g7 b2-a3 e7-d6 d2-e3 a7-b6 e3-d4 g7-f6",
        "c3-b4 b6-a5 b4-c5 f6-g5 e3-d4 g7-f6 f6-g5 g1-h2 g5-h4 c1-d2 e7-d6 b2-c3 h8-g7 a1-b2 d6-c5 h2-g3 d8-e7 g1-f2 b8-c7 f2-e3",
        "c3-b4 b6-a5 b4-c5 g5-h4 g3-f4 f6-g5 c5-b6 e7-d6 f8-e7 d4-e5 d6-c5 b2-c3 c5-b4 a1-b2 e7-d6 c3-d4 a5-b4 b2-a3 d8-e7 c1-d2",
        "c3-b4 b6-a5 b4-c5 g7-f6 c3-b4 f6-e5 g3-f4 e7-d6 c1-d2 h8-g7 e3-d4 g7-f6 d2-c3 f6-g5 f2-e3 c7-b6 b4-a5 d8-c7 g1-f2 d6-c5",
        "c3-b4 b6-a5 c1-b2 a7-b6 e3-f4 f6-g5 d6-c5 b2-c3 g5-h4 g3-f4 h8-g7 a1-b2 g7-f6 f4-g5 f2-g3 g1-f2 c7-d6 f2-e3 d8-e7 h2-g3",
        "c3-b4 b6-a5 c1-b2 a7-b6 g3-f4 b6-a5 c7-d6 h2-g3 f4-e5 h8-g7 f2-e3 g7-f6 a1-b2 e7-d6 e1-d2 d6-c5 d2-c3 b8-a7 c3-d4 f8-e7",
        "c3-b4 b6-a5 c1-d2 g3-f4 d6-e5 f6-g5 a1-b2 h8-g7 b2-c3 g7-f6 h2-g3 c7-d6 c3-b4 f6-e5 e1-d2 b8-c7 b4-c5 d8-e7 c5-d6 d2-c3",
        "c3-b4 b6-a5 d2-c3 a7-b6 g3-h4 b6-c5 h2-g3 c7-b6 g1-h2 f6-e5 c3-d4 e5xc3 b4xd2 g7-f6 b2-c3 b8-a7 a1-b2 f8-g7 g3-f4 f6-e5",
        "c3-b4 b6-a5 d2-c3 c7-b6 c3-d4 b6-c5 a1-b2 b8-c7 f6-g5 g3-h4 h8-g7 b2-c3 g7-f6 h2-g3 f6-e5 g3-f4 d8-e7 g1-h2 h6-g5 f2-e3",
        "c3-b4 b6-a5 d2-c3 f6-e5 g3-h4 c7-b6 c3-d4 e5xc3 b4xd2 b6-c5 h2-g3 a7-b6 b2-c3 b8-a7 g3-f4 c5-b4 a3xc5 b6xb2 a1xc3 d6-c5",
        "c3-b4 b6-a5 d2-c3 f6-e5 g3-h4 c7-b6 c3-d4 e5xc3 b4xd2 b6-c5 h2-g3 g7-f6 g3-f4 a7-b6 b2-c3 b8-a7 c3-b4 a5xc3 d2xb4 b6-a5",
        "c3-b4 b6-a5 d4xb6 a5xc7 b2-c3 d6-e5 h2-g3 f6-g5 e3-f4 g5xe3 d2xd6 c7xe5 c1-d2 h6-g5 d2-e3 g7-f6 g3-f4 e5xg3 f2xh4 h8-g7",
        "c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 h6-g5 b2-c3 g5-h4 f6-e5 e3-f4 e5xg3 h2xf4 g7-h6 f2-e3 h8-g7 e3-d4 g7-f6 e1-f2",
        "c3-b4 b6-a5 e3-f4 a5xc3 b2xb6 c7xa5 a3-b4 a5xc3 d2xb4 d6-e5 f4xd6 e7xa3 g3-h4 f6-e5 h2-g3 g7-f6 g3-f4 e5xg3 h4xf2 f6-e5",
        "c3-b4 b6-a5 g3-f4 a1-b2 f6-e5 b2-c3 g7-f6 c3-d4 d6-c5 d2-c3 f6-e5 e3-d4 h6-g5 e1-f2 g5-f4 a3-b4 h8-g7 f2-e3 c7-d6 g1-f2",
        "c3-b4 b6-a5 g3-f4 a5xc3 b2xd4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 g7-f6 b2-c3 a7-b6 f2-g3 f6-e5 c3-b4 e7-f6 b4-a5 b6-c5 d2-c3",
        "c3-b4 b6-a5 g3-f4 a5xc3 d2xb4 a7-b6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 f2xd4 g7-f6 h2-g3 e7-d6 c5xg5 h6xh2",
        "c3-b4 b6-a5 g3-f4 a5xc3 d2xb4 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 f6-g5 b4-c5 d6xb4 c3xa5 e7-d6 b2-c3 d6-c5 c3-d4 h8-g7 d4xb6",
        "c3-b4 b6-a5 g3-f4 a5xc3 d2xb4 f6-g5 b2-c3 g7-f6 b4-a5 g5-h4 d6-c5 b4xd6 c7xg3 h2xf4 f6-g5 a1-b2 h8-g7 b2-c3 e7-d6 c3-b4",
        "c3-b4 b6-a5 g3-f4 a5xc3 d2xb4 f6-g5 b2-c3 g7-f6 c1-d2 g5-h4 b4-a5 f6-e5 a1-b2 e5xg3 h2xf4 h8-g7 g1-h2 d6-c5 c3-b4 g7-f6",
        "c3-b4 b6-a5 g3-f4 a5xc3 d2xb4 f6-g5 b2-c3 g7-f6 c1-d2 g5-h4 f6-g5 c3-d4 a7-b6 a1-b2 e7-f6 f4-e5 d6xf4 f2-g3 h4xf2 e1xg7",
        "c3-b4 b6-a5 g3-f4 a5xc3 d2xb4 f6-g5 b4-c5 d6xb4 a3xc5 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 b2-a3 h8-g7 c3-d4 c7-b6 e1-d2 b8-c7",
        "c3-b4 b6-a5 g3-f4 g5-h4 d4-c5 f6-g5 a1-b2 g7-f6 c7-b6 c1-b2 d2-c3 f6-e5 c3-b4 g5-f4 d8-c7 f2-e3 e3-f4 a7-b6 a3-b4 f8-e7",
        "c3-b4 b6-a5 g3-h4 a1-b2 c5-b4 b4-a3 h2-g3 c7-b6 e3-d4 b8-c7 d2-e3 c7-d6 e1-d2 b6-a5 g1-h2 d6-c5 e3-d4 c7-b6 d2-e3 e7-d6",
        "c3-b4 b6-a5 g3-h4 a1-b2 d6-e5 b2-c3 e5-f4 a3-b4 e7-d6 f2-e3 f6-e5 g7-h6 g1-f2 f2-e3 b8-c7 e5-d4 b4-c5 c7-d6 e1-f2 h8-g7",
        "c3-b4 b6-a5 g3-h4 a5xc3 b2xb6 c7xa5 a1-b2 a5-b4 a3xc5 d6xb4 b4-a3 g1-h2 e7-d6 b2-c3 a7-b6 e3-f4 f6-e5 f4-g5 d6-c5 d2-e3",
        "c3-b4 b6-a5 g3-h4 a5xc3 b2xb6 c7xa5 h2-g3 a5-b4 a3xc5 d6xb4 b4-a3 b2-c3 b8-a7 g3-f4 f6-g5 h4xf6 g7xg3 f2xh4 e7-f6 c3-d4",
        "c3-b4 b6-a5 g3-h4 a5xc3 b2xb6 c7xa5 h2-g3 a5-b4 a3xc5 d6xb4 b4-a3 b2-c3 b8-c7 g3-f4 f6-g5 h4xf6 g7xg3 f2xh4 f8-g7 e1-f2",
        "c3-b4 b6-a5 g3-h4 a5xc3 d2xb4 f6-g5 h4xf6 g7xe5 h2-g3 h8-g7 e5-f4 g3xe5 d6xd2 c1xe3 g7-f6 c3-d4 f6-g5 f2-g3 g5-h4 g1-f2",
        "c3-b4 b6-a5 h2-g3 a7-b6 b4-a5 f6-e5 b6-c5 e1-d2 g7-f6 g3-h4 h8-g7 f2-g3 c7-b6 b2-c3 b8-c7 g3-f4 b6-a5 c3-d4 c7-b6 d2-c3",
        "c3-b4 b6-a5 h2-g3 f6-e5 e3-f4 a7-b6 f2-e3 g7-f6 h6-g5 b4-c5 f6-e5 b2-c3 g5-h4 a1-b2 h8-g7 b2-a3 e7-d6 a3-b4 g7-h6 b4-a5",
        "c3-b4 b6-a5 h2-g3 g5-h4 a1-b2 f6-g5 a3-b4 e7-d6 d8-e7 b4-a5 a7-b6 b2-a3 e7-d6 c3-d4 b6-a5 d4-e5 g7-f6 a3-b4 c7-b6 b4-c5",
        "c3-b4 b6-c5 b2-c3 f6-e5 a1-b2 g7-h6 b4-a5 e5-f4 f6-e5 f2-g3 h8-g7 c3-b4 g7-f6 b2-c3 c5-d4 g3-f4 b4-c5 h6-g5 a1-b2 f6-e5",
        "c3-b4 b6-c5 b2-c3 f6-e5 a1-b2 g7-h6 g3-f4 h8-g7 c5-b4 b2-a3 g7-f6 c7-b6 f6-g5 d2-c3 a7-b6 c3-d4 e7-d6 d4-c5 e1-f2 b8-c7",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 c5-d4 a1-b2 g7-f6 g3-h4 e5xg3 c3xg7 h8xf6 h2xf4 d6-c5 b4xd6 c7xg3 g1-h2 a7-b6 h2xf4 f6-g5",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 e7-f6 b4-a5 f8-e7 c3-b4 f6-g5 e7-f6 g3-h4 e5xg3 h2xf4 d6-e5 b4xd6 e5xg3 h4xf2 c7xe5 a1-b2",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 g7-f6 a1-b2 f6-g5 g3-h4 g5xe3 f2xf6 e7xg5 h4xf6 f8-g7 d2-e3 g7xe5 e3-f4 e5xg3 h2xf4 h8-g7",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 g7-f6 d2-e3 a7-b6 b4-a5 f8-g7 c3-b4 f6-g5 g3-h4 e5xg3 h4xf6 g7xe5 h2xf4 e5xg3 f2xh4 h8-g7",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 g7-f6 d2-e3 f6-g5 a1-b2 g5-h4 c1-d2 c7-b6 b4-a5 f8-g7 a5xc7 d8xb6 c3-b4 b6-a5 b2-c3 a7-b6",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 g7-f6 d2-e3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 f2xf6 f8-e7 h2-g3 e7xg5 g3-f4 a7-b6 b4-a5 d8-e7",
        "c3-b4 b6-c5 b2-c3 f6-e5 e3-f4 g7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 h2xf4 h8-g7 a1-b2 d8-e7 e3-d4 c5xe3 c3-d4 e3xc5",
        "c3-b4 b6-c5 b2-c3 f6-e5 f2-g3 g7-f6 a1-b2 f6-g5 e3-d4 h8-g7 g3-h4 e5-f4 b4-a5 g7-f6 c3-b4 d6-e5 f2-g3 c7-d6 b2-c3 b8-c7",
        "c3-b4 b6-c5 b2-c3 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 b4-a5 f6-g5 g5-h4 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 g7-f6 c3-d4 b8-a7 d4xb6",
        "c3-b4 b6-c5 b2-c3 f6-e5 g3-f4 g7-f6 f4-g5 c7-b6 b6-a5 a1-b2 f6-e5 g5-h6 h8-g7 b2-c3 g7-f6 e3-d4 e5-f4 b4-c5 f4-g3 a3-b4",
        "c3-b4 b6-c5 b2-c3 f6-g5 c3-d4 g7-f6 d4xb6 c7xc3 d2xb4 h8-g7 b4-a5 d8-c7 a3-b4 g5-f4 g3xe5 d6xd2 c1xe3 f6-e5 e3-d4 e5xc3",
        "c3-b4 b6-c5 b2-c3 f6-g5 c3-d4 g7-f6 d4xb6 c7xc3 d2xb4 h8-g7 b4-a5 d8-c7 e3-d4 g5-h4 d4-c5 d6xb4 a5xc3 h6-g5 a3-b4 g5-f4",
        "c3-b4 b6-c5 b2-c3 f6-g5 c3-d4 g7-f6 d4xb6 c7xc3 d2xb4 h8-g7 d8-c7 e3-d4 g5-h4 d4-c5 d6xb4 a5xc3 h6-g5 a3-b4 g5-f4 g3xe5",
        "c3-b4 b6-c5 b2-c3 f6-g5 c3-d4 g7-f6 d4xb6 c7xc3 d2xb4 h8-g7 g5-h4 a1-b2 h6-g5 g3-f4 g7-h6 f2-g3 h4xd4 a3-b4 g5xe3 b4-c5",
        "c3-b4 b6-c5 b2-c3 f6-g5 e1-f2 g5-h4 a1-b2 g7-f6 f8-e7 c3-d4 h8-g7 e3-d4 d6-e5 b2-c3 h6-g5 a3-b4 g7-h6 b4-c5 g5-f4 c1-b2",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g5-h4 c3-d4 g7-f6 d4xb6 c7xc3 d2xb4 d8-c7 c1-d2 f6-g5 h8-g7 d2-c3 f6-e5 h2-g3 c7-b6 b4-a5",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 f6-e5 f4xd6 c7xe5 g3-f4 e5xg3 h2xf4 b4-a3 c3-d4 b8-c7 a1-b2",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 f6-e5 c3-b4 e5xg3 f2xf6 e7xg5 a1-b2 g5-h4 e1-f2 h8-g7 b2-c3 h6-g5 c3-d4 a7-b6",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 g5-h4 c3-b4 f6-e5 e5xg3 h2xf4 h8-g7 b2-c3 g7-f6 c3-d4 f6-e5 d4xf6 e7xg5 d2-c3",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 g5-h4 c3-b4 f6-e5 e5xg3 h2xf4 h8-g7 b2-c3 g7-f6 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 g5-h4 c3-d4 f6-g5 d4xb6 a7xc5 a1-b2 b8-a7 d2-c3 c5-b4 a3xc5 d6xd2 e1xc3 e7-d6",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 b4-a5 g5-h4 c3-d4 f6-g5 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 c3-d4 g5-h4 d4xb6 c7xc3 d2xb4 f6-g5 b4-a5 h8-g7 a1-b2 g7-f6 f2-g3 h4xd4 a3-b4 g5xe3",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-f4 g7-f6 c3-d4 h8-g7 d4xb6 c7xc3 d2xb4 d8-c7 b4-a5 a7-b6 a1-b2 b6-c5 a3-b4 c5xa3 e3-d4 g5xc5",
        "c3-b4 b6-c5 b2-c3 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 f2-g3 e7-d6 g3xe5 d6xf4 g1-f2 d8-e7",
        "c3-b4 b6-c5 b4-a5 d6-e5 e3-f4 e7-d6 b2-c3 f6-g5 g3-h4 g5xe3 f2xf6 g7xe5 e1-f2 a7-b6 c3-b4 h6-g5 h4xd4 c5xe3 d2xf4 d6-c5",
        "c3-b4 b6-c5 b4-a5 d6-e5 e3-f4 e7-d6 b2-c3 f6-g5 g3-h4 g5xe3 f2xf6 g7xe5 e1-f2 a7-b6 f2-g3 c5-d4 a1-b2 h8-g7 c3-b4 b6-c5",
        "c3-b4 b6-c5 b4-a5 d8-c7 b2-c3 f6-e5 a3-b4 e3-d4 g7-f6 h8-g7 g1-h2 h6-g5 e5-f4 a1-b2 e7-d6 d2-e3 a7-b6 c3-b4 b2-a3 g7-f6",
        "c3-b4 b6-c5 b4-a5 d8-c7 b2-c3 f6-e5 c1-b2 a7-b6 g1-h2 e5-d4 b8-a7 b2-c3 c5-d4 c3-b4 f6-g5 f4-e5 g7-f6 d2-e3 f6-e5 a1-b2",
        "c3-b4 b6-c5 b4-a5 d8-c7 b2-c3 f6-e5 c3-b4 e7-f6 c1-b2 a7-b6 d2-c3 f6-g5 c3-d4 e5xc3 b2xd4 g7-f6 g1-h2 f8-g7 d4-e5 f6xd4",
        "c3-b4 b6-c5 b4xd6 a7-b6 d6-e7 b6-c5 e7-f8 c5-d4 f8-b4 d4-e3 b4-e1 b4-c5 a7-b6 c5xa7 a5-b4 a7-b8 b4-c3 b8-f4 h6xf8 c3-b2",
        "c3-b4 b6-c5 d2-c3 f6-e5 e1-d2 e7-f6 b4-a5 f8-e7 e3-f4 f6-g5 e5-d4 c3xe5 e7-f6 g3-h4 f6xf2 g1xe3 a7-b6 h4xf6 g7xg3 h2xf4",
        "c3-b4 b6-c5 d2-c3 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 a7-b6 h2-g3 h8-g7 c1-d2 g7-f6 d2-e3 e5-d4",
        "c3-b4 b6-c5 d2-c3 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 c5-d4 b2-c3 d4xb2 a1xc3 h8-g7 c3-d4 e5xc3",
        "c3-b4 b6-c5 d2-c3 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 f8-g7 h2-g3 g7-f6 c1-d2 e5-d4 b2-c3 d4xb2",
        "c3-b4 b6-c5 d2-c3 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 f8-g7 h2-g3 g7-f6 c1-d2 h8-g7 d2-e3 e5-d4",
        "c3-b4 b6-c5 d2-c3 f6-e5 e3-f4 g7-f6 b4-a5 f8-g7 c3-b4 a7-b6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 e1-d2 e7-f6",
        "c3-b4 b6-c5 d2-c3 f6-e5 g3-f4 e5xg3 h2xf4 e7-f6 c3-d4 a7-b6 f6-e5 d4xf6 g7xg3 f2xh4 d6-e5 e3-f4 e5xg3 h4xf2 h8-g7 c1-d2",
        "c3-b4 b6-c5 d2-c3 f6-e5 g3-f4 e7-f6 c3-d4 f6-e5 b6-a7 g3-h2 b4-c5 h6-g5 a3-b4 g5-f4 b4-a5 f6-e5 c3-b4 g7-h6 b2-c3 h8-g7",
        "c3-b4 b6-c5 d4xb6 c7xc3 b2xd4 a7-b6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 b8-a7 g3-f4 f6-g5 h2-g3 g5xe3 f2xd4 e7-d6 c5xe7 f8xd6",
        "c3-b4 b6-c5 e3-d4 c5xe3 f2xd4 d6-e5 b2-c3 e5-f4 g3xe5 e7-d6 e1-f2 d6xf4 d2-e3 f4xd2 c3xe1 f6-e5 d4xf6 g7xe5 h2-g3 a7-b6",
        "c3-b4 b6-c5 e3-d4 c5xe3 f2xd4 d6-e5 b2-c3 e5-f4 g3xe5 e7-d6 g1-f2 d6xf4 f2-g3 f8-e7 g3xe5 e7-d6 e1-f2 d6xf4 d2-e3 f4xd2",
        "c3-b4 b6-c5 e3-d4 c5xe3 f2xd4 f6-g5 b4-c5 d6xb4 a3xc5 c7-b6 b2-c3 g7-f6 a1-b2 d8-c7 g3-h4 e7-d6 c5xe7 f6xd8 h4xf6 f8-e7",
        "c3-b4 b6-c5 e3-f4 f6-g5 g3-h4 g5xe3 f2xb6 c7xc3 b2xd4 h6-g5 h4xf6 g7xc3 d2xb4 a7-b6 h2-g3 h8-g7 c1-d2 g7-f6 a1-b2 b6-c5",
        "c3-b4 b6-c5 f2-g3 f6-e5 e3-f4 c5-d4 b2-c3 d4xb2 a1xc3 a7-b6 g7-f6 g1-f2 f6-g5 h4xd4 d6-e5 f4xd6 e7xg1 a3-b4 b6-c5 b4xd6",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 c3-d4 a7-b6 f2-g3 h4xf2 e1xg3 c5-b4 a3xa7 d6-e5 f4xd6 c7xa1",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 c3-d4 f6-g5 d4xb6 a7xc5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 c3-d4 f6-g5 d4xb6 a7xc5 b2-c3 c5-b4 a3xc5 d6xb4 f4-e5 b4-a3",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 c3-d4 f6-g5 d4xb6 a7xc5 d2-c3 e7-f6 c3-d4 b8-a7 d4xb6 a7xc5",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 f6-g5 d4xb6 a7xc5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 d2-c3",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 f6-g5 d4xb6 a7xc5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 d4-e5",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 f6-g5 d4xb6 a7xc5 b2-c3 c5-b4 a3xc5 d6xb4 f4-e5 b4-a3 e3-d4",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 b4-a5 g5-h4 f6-g5 d4xb6 a7xc5 d2-c3 e7-f6 c3-d4 b8-a7 d4xb6 a7xc5 e3-d4",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 b4-a3 g3-h4 a7-b6 h2-g3 e7-d6 a1-b2 f8-g7 c3-b4 a3xc5 b2-a3",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 b4-a3 g3-h4 a7-b6 h2-g3 e7-d6 a1-b2 f8-g7 e1-f2 d6-c5 c3-b4",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 b4-a3 g3-h4 a7-b6 h2-g3 e7-d6 a1-b2 f8-g7 e1-f2 d6-c5 c3-d4",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 f2-g3 b4-a3 g3-h4 a7-b6 h2-g3 e7-d6 a1-b2 f8-g7 c3-b4 a3xc5",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 c5-b4 a3xc5 d6xb4 f2-g3 b4-a3 g3-h4 a7-b6 h2-g3 e7-d6 a1-b2 f8-g7 e1-f2 d6-c5",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 f6-e5 c3-b4 e5xg3 f2xf6 e7xg5 a1-b2 g5-h4 b2-c3 c7-b6 a5xe5 h6-g5 b4xd6 g5-f4",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 f6-e5 c3-b4 e5xg3 f2xf6 e7xg5 a1-b2 g5-h4 e1-f2 h8-g7 b2-c3 h6-g5 e3-d4 c5xe3",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 f6-e5 c3-b4 e5xg3 f2xf6 e7xg5 a1-b2 g5-h4 e1-f2 h8-g7 e3-f4 c7-b6 a5xe5 d8-c7",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 b4-a5 g5-h4 f4-g5 h6xf4 e3xg5 c5-b4 a3xc5 d6xb4 f2-e3 b4-a3 c3-d4 f6-e5 d4xf6 f8-g7",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 c3-d4 g5-h4 d4xb6 c7xc3 d2xb4 f6-g5 b4-a5 h8-g7 a1-b2 d6-c5 a5-b6 c5-b4 a3xc5 b8-c7",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 c3-d4 g5-h4 d4xb6 c7xc3 d2xb4 f6-g5 b4-a5 h8-g7 a1-b2 d8-c7 b2-c3 d6-c5 f2-g3 h4xb2",
        "c3-b4 b6-c5 g3-f4 f6-g5 b2-c3 g7-f6 c3-d4 g5-h4 d4xb6 c7xc3 d2xb4 f6-g5 b4-a5 h8-g7 a1-b2 g7-f6 f2-g3 h4xd4 a3-b4 g5xe3",
        "c3-b4 b6-c5 g3-f4 f6-g5 f2-g3 g5-h4 e1-f2 g7-f6 f4-g5 h6xf4 g3xg7 h8xf6 e3-f4 f6-e5 f2-g3 h4xf2 g1xe3 e5xg3 h2xf4 e7-f6",
        "c3-b4 b6-c5 g3-f4 g7-f6 f4-g5 h8-g7 g5-h6 f6-e5 e5-f4 c1-d2 f6-e5 d2-e3 c7-b6 b2-c3 c5-d4 a7-b6 b4-a5 b6-c5 h2-g3 b8-c7",
        "c3-b4 b6-c5 g3-h4 e5-f4 f2-g3 a7-b6 g3xe5 d6xf4 b4xd6 c7xe5 a5xc7 d8xb6 g1-f2 e7-d6 f2-g3 d6-c5 b2-c3 e5-d4 c3xe5 f4xd6",
        "c3-b4 b6-c5 g3-h4 f6-e5 b4-a5 e5-f4 e3xg5 h6xf4 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 d6-e5 b4xd6 e7xc5 e1-f2 g7-h6 f2-e3 h6-g5",
        "c3-b4 b6-c5 g3-h4 f6-g5 f2-g3 h8-g7 e3-f4 g7-f6 c5-d4 g1-f2 b4-c5 e7-d6 f2-e3 a7-b6 a1-b2 b6-c5 b2-c3 c7-b6 g3-h4 f6-g5",
        "c3-b4 c5xa3 a5-b6 f8-e7 b6-a7 e7-d6 d8-c7 d6-c5 b8-a7 c5-d4 a7-d4 b8-a7 d6-e5 a7-e3 c7-d6 e3-a7 e5-f4 a7-b8 d6-e5 b8-c7",
        "c3-b4 d6-c5 b2-c3 f6-g5 c3-b4 d8-e7 f8-e7 b2-c3 e7-d6 c3-d4 b6-a5 d2-c3 g7-f6 e3-d4 c7-b6 c1-d2 b8-a7 d2-e3 b6-a5 g3-f4",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 b6-a5 d4xb6 a5xc7 a3-b4 f8-e7 e7-d6 c3-b4 a7-b6 b4-c5 d6xb4 a5xc3 b6-a5 a1-b2 c7-d6 c1-d2",
        "c3-b4 d6-c5 b4xd6 e7xc5 b2-c3 b6-a5 d4xb6 a5xc7 c3-b4 f6-e5 g7-f6 a3-b4 c7-d6 b4-c5 d6xb4 a5xc3 d8-c7 c1-b2 c7-d6 b2-a3",
        "c3-b4 d6-c5 b4xd6 e7xc5 e3-f4 c7-d6 b2-c3 f6-g5 h4xf6 g7xg3 h2xf4 f8-e7 f2-g3 e7-f6 g3-h4 h8-g7 d2-e3 d8-c7 c3-d4 d6-e5",
        "c3-b4 d6-c5 g3-h4 f8-e7 h2-g3 g5-f4 b6-a5 b2-c3 a7-b6 d2-e3 b6-c5 c3-b4 c7-d6 a1-b2 e7-f6 b2-c3 f6-g5 e3-f4 b8-c7 g3-h4",
        "c3-b4 d6-c5 g3-h4 f8-e7 h2-g3 g5-f4 b6-a5 b2-c3 h6-g5 d2-e3 a7-b6 c1-b2 c7-d6 c3-d4 b8-a7 a1-b2 h8-g7 g1-f2 b6-c5 g3-f4",
        "c3-b4 d6-e5 b2-c3 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 f2-e3 b6-a5 e3xg5 g7-h6 c1-b2 h6xf4 g1-f2 f8-g7 b4-c5 c7-b6 a3-b4 b6xd4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 c5xe3 d2xd6 e7xc5 b2-c3 f8-e7 c3-b4 c5-d4 g3-h4 f6-g5 h4xf6 g7xe5 c1-d2 h8-g7 h2-g3 g7-f6",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 c5xe3 d2xd6 e7xc5 b2-c3 f8-e7 e7-d6 c1-d2 f6-g5 d2-e3 g5-h4 e1-d2 d8-e7 a1-b2 a7-b6 c3-b4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 c5xe3 d2xd6 e7xc5 b2-c3 f8-e7 e7-d6 c1-d2 f6-g5 d2-e3 g5-h4 e1-d2 d8-e7 a1-b2 a7-b6 c3-d4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 c5xe3 d2xd6 e7xc5 b2-c3 f8-e7 e7-d6 c1-d2 f6-g5 d2-e3 g5-h4 e1-d2 g7-f6 c3-d4 f6-g5 d4xb6",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 c5xe3 d2xd6 e7xc5 b2-c3 f8-e7 e7-d6 c1-d2 f6-g5 f2-e3 g5-h4 e1-f2 g7-f6 c3-d4 f6-g5 d4xb6",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 c5xe3 d2xd6 e7xc5 b2-c3 f8-e7 e7-d6 f2-g3 f6-g5 e1-d2 g5xe3 d2xf4 d8-e7 c3-b4 e7-f6 a1-b2",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 c5xe3 d2xd6 e7xc5 b2-c3 f8-e7 g3-f4 e7-d6 c1-d2 f6-g5 d2-e3 g5-h4 e1-d2 d8-e7 a1-b2 a7-b6",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 c5xe3 d2xd6 e7xc5 b2-c3 f8-e7 g3-f4 e7-d6 c1-d2 f6-g5 d2-e3 g5-h4 e1-d2 g7-f6 c3-d4 f6-g5",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 c5xe3 d2xd6 e7xc5 b2-c3 f8-e7 g3-f4 e7-d6 c1-d2 f6-g5 f2-e3 g5-h4 e1-f2 g7-f6 c3-d4 f6-g5",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 e5xc3 b2xb6 a7xc5 d2-c3 f6-e5 e7-f6 c3-b4 c7-d6 c1-d2 e5-d4 d2-e3 f6-g5 h4xf6 g7xe5 h2-g3",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 e5xc3 d2xd6 e7xc5 b2-c3 f8-e7 e7-d6 c1-d2 f6-e5 g3-h4 g7-f6 d2-e3 h8-g7 f2-g3 e5-d4 e3-f4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-d4 e5xc3 d2xd6 e7xc5 b2-c3 h6-g5 c5-d4 c1-d2 f8-e7 g3-h4 f6-e5 h4xf6 e7xg5 h2-g3 g5-h4 d2-e3",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 b2-c3 c5-d4 e3xc5 e5-f4 g3xe5 f6xb2 a1xc3 c7-b6 a5xc7 d8xb2 d2-c3 c5-b4 a3xc5 c7-b6 a5xc7",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e5-d4 f4-e5 d4-e3 f2xb6 f6xd4 a7xc5 d2-e3 g7-f6 c1-d2 f6-e5 g3-h4 h8-g7 d2-c3 c5-b4 e3xc5",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e5-d4 f4-e5 d4-e3 f2xb6 f6xd4 a7xc5 g3-f4 b8-a7 b2-c3 d4xb2 a1xc3 c5-b4 a3xc5 c7-b6 a5xc7",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e5-d4 f4-e5 d4-e3 f2xb6 f6xd4 e1-f2 a7xc5 g3-f4 b8-a7 b2-c3 d4xb2 a1xc3 c5-b4 a3xc5 c7-b6",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 d8-e7 a1-b2 e7-f6 h2-g3 f8-g7 d2-e3 e5-d4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 e5-f4 e1-f2 d6-e5 b4xd6 h6-g5 h4xd4 c7xg3",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 e5-f4 h4-g5 f4-g3 h2xf4 d6-e5 b4xd6 e5xg3",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 f8-g7 h2-g3 e5-d4 a1-b2 h6-g5 h4xf6 g7xe5",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 f8-g7 h2-g3 e5-d4 g1-h2 g7-f6 e1-f2 d4-c3",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 h8-g7 a1-b2 g7-f6 d2-e3 f8-e7 h2-g3 e5-d4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 h8-g7 h2-g3 f8-e7 g1-h2 g7-f6 d2-e3 c5-d4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 h8-g7 h2-g3 g7-f6 a1-b2 f8-g7 d2-e3 e5-d4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 h8-g7 h2-g3 g7-f6 d2-e3 e5-d4 c1-d2 d4xf2",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 h8-g7 h2-g3 g7-f6 d2-e3 e5-d4 e3-f4 f6-e5",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 h8-g7 h2-g3 g7-f6 d2-e3 e5-d4 g1-f2 f6-g5",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 d2-e3 f6-g5 e3-d4 g5xe3 d4xf6 g7xe5 f2xf6 f8-g7 b2-c3 g7xe5 g3-f4 e5xg3 h2xf4 d8-e7",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 d2-e3 f8-e7 b2-c3 a7-b6 b8-a7 a1-b2 f6-g5 g3-h4 e5xg3 h2xf4 c5-d4 h4xf6 g7xg3 f2xh4",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b2-c3 g7-f6 c3-b4 f6-g5 d2-e3 f4xd2",
        "c3-b4 d6-e5 b4-a5 b6-c5 e3-f4 e7-d6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b2-c3 g7-f6 c3-b4 f6-g5 f2-g3 a7-b6",
        "c3-b4 d6-e5 b4-a5 b6-c5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 c7-b6 a5xc7 b8xd6 f2-g3 d8-c7 g3xe5 f6xb2 a1xc3 g7-f6 h2-g3 f6-e5",
        "c3-b4 d6-e5 b4-a5 b6-c5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 c7-d6 c3-b4 d6-e5 b4xd6 e5xc7 a1-b2 b2-c3 b6-c5 c3-b4 f6-e5 b4xd6",
        "c3-b4 d6-e5 b4-a5 b6-c5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 c7-d6 c5-b4 c3xa5 a7xc5 a1-b2 f4-e3 f2xb6 d6-c5 b6xd4 f6-g5 h4xf6",
        "c3-b4 d6-e5 b4-a5 b6-c5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 e7-d6 c3-b4 f6-e5 f2-g3 d8-e7 e1-f2 a7-b6 a1-b2 e7-f6 b2-c3 g7-h6",
        "c3-b4 d6-e5 b4-a5 b6-c5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 e7-d6 c3-b4 f6-e5 f2-g3 d8-e7 e1-f2 a7-b6 f2-e3 g7-h6 e3xg5 h6xf4",
        "c3-b4 d6-e5 b4-a5 e5xc3 b2xd4 h6-g5 a1-b2 f6-e5 d4xf6 g5xe7 e7-d6 a3-b4 b6-c5 b2-a3 g7-f6 f4-g5 f6-e5 g5-h6 h8-g7 h2-g3",
        "c3-b4 d6-e5 b4-a5 e7-d6 a3-b4 b6-c5 b2-a3 f6-g5 g3-h4 e5-d4 h4xf6 g7xe5 e3-f4 e5xg3 h2xf4 h8-g7 f2-g3 g7-f6 g1-h2 d4-c3",
        "c3-b4 d6-e5 b4-a5 e7-d6 a3-b4 f6-g5 b4-c5 b6xd4 e3xe7 f8xd6 b2-c3 a7-b6 a1-b2 g5-f4 b2-a3 b6-c5 g3-h4 g7-f6 f2-g3 d8-e7",
        "c3-b4 d6-e5 b4-a5 f6-g5 b2-c3 g5-f4 e3xg5 h6xf4 c3-b4 b6-c5 b4xd6 e7xc5 a1-b2 f8-e7 b2-c3 e5-d4 c3xe5 f4xd6 g3-f4 e7-f6",
        "c3-b4 d6-e5 b4-a5 f6-g5 e3-f4 g5xe3 d2xd6 c7xe5 a5xc7 d8xb6 a3-b4 g7-f6 b4-a5 h6-g5 a5xc7 b8xd6 b2-c3 h8-g7 f2-e3 g7-h6",
        "c3-b4 d6-e5 b4-a5 f6-g5 e3-f4 g5xe3 d2xd6 e7xc5 g3-f4 g7-f6 h2-g3 f8-e7 e1-d2 f6-g5 g3-h4 g5xe3 d2xf4 h8-g7 c1-d2 g7-f6",
        "c3-b4 d6-e5 b4-a5 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b2-c3 b6-c5 c3-b4 c7-d6 a7-b6 f2-g3 b8-c7 d2-e3 f4xd2 c1xe3 c7-b6 a5xc7",
        "c3-b4 d6-e5 b4-a5 h6-g5 d2-e3 f6-e5 g7-f6 a1-b2 h8-g7 b2-a3 g7-h6 c1-b2 f6-e5 b2-c3 e7-d6 c3-d4 d6-c5 g3-f4 f8-e7 f4-e5",
        "c3-b4 d6-e5 d2-c3 e7-d6 b4-a5 f8-e7 c3-d4 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 e3-f4 f6-e5 a1-b2 c5-d4 a3-b4 e7-f6 b2-c3 d4xb2",
        "c3-b4 d6-e5 d2-c3 e7-d6 e3-d4 f6-g5 d4xf6 g5xe7 g3-f4 g7-f6 h6xf4 f2-g3 h4xf2 e1xg7 h8xf6 c1-d2 f6-g5 d2-e3 g5-h4 e3-f4",
        "c3-b4 d6-e5 d2-c3 f6-g5 b4-a5 e5-d4 e3xc5 b6xd4 c3xe5 g5-f4 e5-d6 c7xe5 g3-h4 g7-f6 b2-c3 e7-d6 f2-g3 d6-c5 a5-b6 c5-b4",
        "c3-b4 d6-e5 d2-c3 f6-g5 b4-a5 g5-f4 e3xg5 h6xf4 a3-b4 e5-d4 g3xe5 d4xf6 c3-d4 b6-c5 b4xd6 e7xe3 f2xd4 a7-b6 b2-c3 f6-e5",
        "c3-b4 d6-e5 e3-f4 b6-a5 f4xd6 a5xc3 b2xd4 e7xe3 d2xf4 a7-b6 f2-e3 f6-g5 g3-h4 f8-e7 h4xf6 g7xg3 h2xf4 h8-g7 a1-b2 e7-d6",
        "c3-b4 d6-e5 e3-f4 e7-d6 b4-a5 f8-e7 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 e7xg5 g3-h4 g5-f4 d2-e3 f4xd2 c1xe3 d6-e5 h2-g3 e5-d4",
        "c3-b4 d6-e5 e3-f4 e7-d6 b4-c5 b6xd4 f4-g5 h6xf4 f2-e3 d4xf2 g1xc5 h4xf2 e1xg3 c7-b6 a5xc7 d8xd4 a3-b4 b8-c7 b2-c3 d4xb2",
        "c3-b4 d6-e5 e3-f4 e7-d6 b4-c5 b6xd4 f4-g5 h6xf4 f2-e3 d4xf2 g1xc5 h4xf2 e1xg3 c7-b6 a5xc7 d8xd4 a3-b4 h8-g7 b2-c3 d4xb2",
        "c3-b4 d6-e5 e3-f4 e7-d6 d2-e3 b6-c5 b2-c3 f6-g5 e3-d4 g5xe3 d4xf6 g7xe5 f2xf6 f8-g7 c1-d2 g7xe5 g3-f4 e5xg3 h2xf4 c7-b6",
        "c3-b4 d6-e5 e3-f4 e7-d6 d2-e3 f6-g5 b4-c5 b6xd4 e3xe7 f8xd6 g5xe3 f2xf6 g7xe5 g3-f4 e5xg3 h2xf4 h8-g7 c1-d2 g7-f6 d2-e3",
        "c3-b4 d6-e5 g3-f4 e5xg3 h2xf4 b6-c5 b4xd6 c7xg3 g1-h2 e7-d6 h2xf4 f6-e5 d2-c3 e5xg3 e3-d4 d6-e5 d4xf6 g7xe5 a3-b4 g3-h2",
        "c3-b4 d6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 e7-d6 f2-e3 f8-e7 e3xg5 c5-d4 c3xe5 d6xh6 a1-b2 a7-b6 b2-c3 b6-c5",
        "c3-b4 e3-f4 b4-a5 g3-h4 f6-e5 g7-f6 f6-g5 h2-g3 g3-h4 f8-g7 h8-g7 e1-f2 b2-c3 c3-b4 c1-b2 e5-f4 d6-e5 d8-e7 e7-d6 b2-c3",
        "c3-b4 e3-f4 d2-e3 b2-c3 f6-e5 e7-f6 f6-g5 g5-h4 c1-d2 a1-b2 b4-a5 a5xc7 b6-c5 c7-b6 f8-e7 d8xb6 c3-b4 f4-g5 b4-a5 g3-f4",
        "c3-b4 e3-f4 f2-e3 g1-f2 f6-e5 e7-f6 b6-a5 a5xc3 b2xd4 d2xb4 a1-b2 b4-c5 e5xc3 f8-e7 f6-g5 d6xb4 a3xc5 g3-h4 h4xf6 h2xf4",
        "c3-b4 e3-f4 f2-e3 g3-h4 f6-e5 e7-f6 b6-a5 a5xc3 d2xb4 h4xf2 b2-c3 e3xg5 e5xg3 f6-e5 e5-f4 h6xf4 e1-d2 d2-e3 c3xe1 a1-b2",
        "c3-b4 e5-d4 e3xc5 b6xd4 d2-e3 c7-b6 e3xc5 b6xd4 c1-d2 f8-g7 b8-c7 a1-b2 d6-e5 b2-c3 d4xb2 a3xc1 e5-d4 c1-b2 a7-b6 b2-a3",
        "c3-b4 e5-f4 b4-a5 b6-c5 b2-c3 e7-d6 f6-e5 d2-c3 g7-f6 c3-d4 d6-c5 a1-b2 c7-d6 b2-c3 f6-e5 c3-b4 h8-g7 d2-e3 g7-f6 h2-g3",
        "c3-b4 f6-e5 b2-c3 b6-a5 d2-e3 e5-f4 g3-h4 a7-b6 b6-c5 h2-g3 c7-b6 e1-f2 b8-a7 c1-b2 f6-e5 e3-f4 g7-f6 f2-e3 h8-g7 f4-g5",
        "c3-b4 f6-e5 b2-c3 b6-c5 b4-a5 c5-b4 a1-b2 b4-a3 e7-d6 g3-f4 g7-f6 e3-d4 d6-c5 f4-g5 f8-e7 c3-b4 e7-d6 c1-d2 h4-g3 h6-g7",
        "c3-b4 f6-e5 b2-c3 b6-c5 b4-a5 c5-b4 a3xc5 d6xb4 e3-f4 e7-d6 b4-a3 g3-h4 e5xg3 h4xf2 g7-f6 h2-g3 h8-g7 g3-h4 d6-e5 f2-g3",
        "c3-b4 f6-e5 b2-c3 b6-c5 e3-f4 a7-b6 b4-a5 b8-a7 c3-b4 g7-f6 c5-d4 e3xc5 b6xd4 c1-d2 h6-g5 f4xh6 f6-g5 h6xf4 d4-e3 f2xf6",
        "c3-b4 f6-e5 b2-c3 b6-c5 e3-f4 a7-b6 b4-a5 b8-a7 c3-b4 g7-f6 d2-e3 c5-d4 e3xc5 b6xd4 c1-d2 h6-g5 f4xh6 f6-g5 h6xf4 d4-e3",
        "c3-b4 f6-e5 b2-c3 b6-c5 e3-f4 e7-f6 d2-e3 f6-g5 e3-d4 g5xe3 d4xf6 g7xe5 f2xf6 f8-g7 c1-d2 g7xe5 g3-f4 e5xg3 h2xf4 c7-b6",
        "c3-b4 f6-e5 b2-c3 e5-f4 b4-a5 f6-g5 a1-b2 b6-c5 g5-h4 b2-c3 f8-e7 c3-d4 d6-e5 h2-g3 h8-g7 g3-h4 g7-f6 e3-f4 f6-e5 d2-e3",
        "c3-b4 f6-e5 b2-c3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5 a1-b2 b6-c5 b4xd6 e7xc5 c3-d4 c5xe3 f2xd4 g7-h6 a3-b4 f8-e7 g1-f2",
        "c3-b4 f6-e5 b2-c3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5 b6-c5 c3-b4 e7-d6 a1-b2 g7-f6 f2-e3 f6-g5 b2-c3 c7-b6 a5xg3 g5-h4",
        "c3-b4 f6-e5 b2-c3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5 b6-c5 c5-d4 c3xe5 f4xd6 a1-b2 d6-c5 b2-c3 g7-f6 c3-b4 e7-d6 g3-f4",
        "c3-b4 f6-e5 b2-c3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5 b6-c5 f2-g3 c5-d4 c3xe5 f4xd6 a1-b2 d6-c5 b2-c3 g7-f6 c3-b4 e7-d6",
        "c3-b4 f6-e5 b2-c3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5 g7-f6 a1-b2 h8-g7 c3-b4 b6-c5 b4xd6 e7xc5 b2-c3 c5-b4 a3xc5 c7-b6",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 a1-b2 b6-c5 b4xd6 e7xc5 c3-d4 c5xe3 f2xd4 g7-h6 a3-b4 f8-e7 g1-f2 f4-e3",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 b6-c5 c3-b4 e7-d6 a1-b2 g7-f6 f2-e3 f6-g5 b2-c3 c7-b6 a5xg3 g5-h4",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 b6-c5 c3-b4 e7-d6 a1-b2 g7-f6 f2-e3 f6-g5 e3-d4 c5xe3 h2-g3 f4xh2",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 b6-c5 c5xe3 f2xd4 g7-f6 d2-e3 f4xd2 c1xe3 h8-g7 h2-g3 g7-h6 a1-b2",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 b6-c5 e7-d6 a1-b2 g7-f6 f2-e3 f6-g5 b2-c3 c7-b6 a5xg3 g5-h4 b4xd6",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 b6-c5 e7-d6 a1-b2 g7-f6 f2-e3 f6-g5 e1-f2 d6-e5 b4xd6 f4-g3 f2xd4",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 b6-c5 e7-d6 a1-b2 g7-f6 f2-e3 f6-g5 e3-d4 c5xe3 h2-g3 f4xh2 d2xh6",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 g7-f6 a1-b2 h8-g7 c3-b4 b6-c5 b4xd6 e7xc5 b2-c3 c5-b4 a3xc5 c7-b6",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c1-b2 b6-a5 e7-d6 g3xe5 d6xf4 g1-f2 g7-f6 b4-c5 h8-g7 f2-e3 f6-e5 e3xg5",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c1-b2 b6-a5 f2-g3 e7-d6 g3xe5 d6xf4 g1-f2 g7-f6 b4-c5 h8-g7 f2-e3 f6-e5",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c1-b2 c7-d6 b4-c5 d6xb4 c3xc7 b8xd6 b2-c3 d6-e5 f2-g3 d8-c7 c3-b4 a7-b6",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 f2-g3 e7-f6 g3xe5 f6xb2 a1xc3 b6-a5 b4-c5 c7-b6 c1-b2 b6xd4 c3xe5 a7-b6",
        "c3-b4 f6-e5 b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 f2-g3 e7-f6 g3xe5 f6xb2 a1xc3 g7-f6 g1-f2 c7-d6 d2-e3 b6-a5 e3-d4 a7-b6",
        "c3-b4 f6-e5 b2-c3 e7-f6 b4-a5 f8-e7 c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a5xc3 e7-d6 c3-b4 a7-b6 a1-b2 g5-h4 b4-a5 d8-e7",
        "c3-b4 f6-e5 b2-c3 e7-f6 e3-d4 f8-e7 b4-a5 e5-f4 g3xe5 d6xf4 c3-b4 f6-e5 d4xf6 g7xe5 f2-g3 h8-g7 g1-f2 e7-d6 f2-e3 b6-c5",
        "c3-b4 f6-e5 b2-c3 e7-f6 e3-d4 h6-g5 b4-c5 d6xb4 a3xc5 g7-h6 f2-e3 c7-d6 c5xe7 f8xd6 g3-h4 d8-e7 h2-g3 b8-c7 g3-f4 e5xg3",
        "c3-b4 f6-e5 b2-c3 g7-f6 a1-b2 b6-a5 b4-c5 d6xb4 a3xc5 h8-g7 c7-b6 f4xd6 b6xd4 c3xe5 f6xd4 d2-c3 e7xc5 c3xe5 f8-e7 f2-e3",
        "c3-b4 f6-e5 b2-c3 g7-f6 a1-b2 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 g5-h4 a3-b4 h8-g7 d2-e3 g7-f6 b2-c3 e7-d6 c3-d4 e5xc3",
        "c3-b4 f6-e5 b2-c3 g7-f6 a1-b2 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 b6-c5 c3-b4 f4-g3 h2xf4 e5xg3 h4-g5 g3-h2 g5-h6 h8-g7",
        "c3-b4 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 h6-g5 a3-b4 a7-b6 b2-a3 g5-f4 d2-e3 f4xd2 c1xe3 g7-h6",
        "c3-b4 f6-e5 b2-c3 g7-f6 a1-b2 h8-g7 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 h6-g5 g3-h4 c7-d6 f2-e3 g7-h6 g1-f2 d6-c5 b2-c3 a7-b6",
        "c3-b4 f6-e5 b2-c3 g7-f6 e3-d4 f8-g7 b4-a5 e5-f4 g3xe5 d6xf4 c3-b4 f6-e5 d4xf6 g7xe5 f2-g3 h8-g7 g1-f2 e7-d6 f2-e3 b6-c5",
        "c3-b4 f6-e5 b2-c3 g7-f6 e3-f4 b6-a5 f2-e3 c7-b6 g3-h4 e5xg3 h4xf2 h6-g5 a1-b2 g5-f4 e3xg5 f6xh4 b4-c5 d6xb4 a3xc5 b6xd4",
        "c3-b4 f6-e5 b4-a5 b6-c5 a1-b2 c7-b6 a5xc7 d8xb6 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 b6-a5 h6-g7 f8xh6 f4-g5 h6xf4 e3xg5 f6-e5",
        "c3-b4 f6-e5 b4-a5 b6-c5 a1-b2 g7-f6 b2-c3 c5-d4 e3xc5 d6xb4 a3xc5 c7-b6 a5xc7 d8xb2 c1xa3 e7-d6 d2-e3 a7-b6 e1-d2 d6-c5",
        "c3-b4 f6-e5 b4-a5 b6-c5 d2-c3 g7-f6 c3-b4 c5-d4 b2-c3 d4xb2 a1xc3 h8-g7 c3-d4 e5xc3 b4xd2 f6-e5 a3-b4 a7-b6 d2-e3 g7-f6",
        "c3-b4 f6-e5 b4-a5 b6-c5 d2-c3 g7-f6 c3-b4 c5-d4 b2-c3 d4xb2 a1xc3 h8-g7 c3-d4 e5xc3 b4xd2 f6-e5 d2-c3 a7-b6 a3-b4 g7-f6",
        "c3-b4 f6-e5 b4-a5 b6-c5 e3-d4 c1-d2 h8-g7 e1-f2 a7-b6 h2-g3 b6-c5 g3-h4 g7-f6 f2-g3 e5-d4 b2-c3 c5-b4 e1-f2 e7-d6 f2-e3",
        "c3-b4 f6-e5 b4-a5 b6-c5 g3-f4 e3-d4 g7-f6 f6-e5 a3-b4 a7-b6 a1-b2 b6-c5 b2-a3 h8-g7 c3-d4 g7-f6 c1-b2 f6-e5 f2-g3 b8-a7",
        "c3-b4 f6-e5 b4-a5 b6-c5 g3-f4 e5xg3 e3-d4 c5xe3 d2xh2 g7-f6 a3-b4 a7-b6 b4-c5 b6xd4 f2-g3 h4xf2 g1xc5 d6xb4 a5xc3 f6-e5",
        "c3-b4 f6-e5 b4-a5 b6-c5 g3-f4 e5xg3 e3-d4 c5xe3 d2xh2 g7-f6 a3-b4 a7-b6 b4-c5 d6xb4 a5xc3 f6-e5 c3-d4 e5xc3 b2xd4 b6-a5",
        "c3-b4 f6-e5 b4-a5 e5-f4 b2-c3 f6-e5 g3-h4 g7-f6 b6-c5 a1-b2 h8-g7 d2-e3 c5-d4 c7-b6 f2-e3 a7-b6 b2-c3 b6-c5 e1-f2 b8-c7",
        "c3-b4 f6-e5 b4-a5 e5-f4 b2-c3 g7-f6 h8-g7 c3-b4 g7-h6 a3-b4 e7-d6 f2-g3 f8-e7 g1-f2 b6-c5 b2-a3 b8-a7 d2-c3 a7-b6 b4-a5",
        "c3-b4 f6-e5 b4-a5 e5-f4 e3xg5 h4xf6 b2-c3 f6-g5 c3-d4 g5-h4 f8-e7 d2-e3 g7-f6 c1-d2 f6-g5 d2-c3 e7-f6 a1-b2 f6-e5 d4xf6",
        "c3-b4 f6-e5 b4-a5 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 f2-e3 f4xd2 c1xe3 g7-f6 e1-f2 h8-g7 e3-f4 g7-h6 f2-g3 f6-g5 h4xf6 e7xe3",
        "c3-b4 f6-e5 b4-a5 e5-f4 g3-h4 f8-g7 b2-c3 f6-g5 c3-b4 h8-g7 d2-c3 e7-f6 c3-d4 f6-g5 a1-b2 g7-f6 b2-c3 f6-e5 f2-g3 g5-h4",
        "c3-b4 f6-e5 b4-a5 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b2-c3 g7-f6 f6-g5 c3-b4 h8-g7 b2-c3 g7-h6 f2-g3 b6-c5 b4xd6 e7xc5 g3xe5",
        "c3-b4 f6-e5 b4-a5 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b2-c3 g7-f6 h8-g7 a1-b2 b6-c5 b4xd6 e7xc5 b2-c3 c5-b4 a3xc5 c7-b6 a5xc7",
        "c3-b4 f6-e5 b4-a5 g7-f6 e3-f4 f6-g5 b2-c3 g5xe3 e7xg5 g3-f4 g5xe3 d2xf4 h8-g7 c1-d2 g7-f6 d2-e3 b6-c5 a1-b2 a7-b6 h2-g3",
        "c3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 b2-c3 g5-f4 c1-b2 e7-f6 g3-h4 f8-e7 e1-d2 b8-c7",
        "c3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 f2-e3 e5-d4 g3-f4 d4xb6 f4xh6 g7-f6 b2-c3 h8-g7",
        "c3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 f2-e3 e5-d4 g3-f4 d4xb6 f4xh6 g7-f6 h2-g3 f6-e5",
        "c3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 f2-e3 g7-h6 g3-f4 e5xg3 h2xf4 e7-d6 c5xe7 f8xd6",
        "c3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 e5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 b2-c3 b6-a5 f2-e3 d8-c7 g1-f2",
        "c3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 e5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 f2-g3 f8-e7 b2-c3 g7-f6 e5xg7",
        "c3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g7-f6 g3-f4 e5xg3 h2xf4 h8-g7 b2-c3 f6-e5 f4xd6 c7xe5 c5-b6 a7xc5 c3-b4 c5xa3",
        "c3-b4 f6-e5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 h6-g5 b2-c3 f8-e7 c3-d4 e5xc3 g3-f4 g5xe3 f2xb2 g7-f6",
        "c3-b4 f6-e5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 c7-b6 g3-f4 b6xd4 f4xd6 d8-e7 d2-c3 e7xc5 c3xe5 a7-b6 b2-c3 g7-f6 e5xg7 h8xf6",
        "c3-b4 f6-e5 b4-c5 e5-f4 c7-b6 h2-g3 b8-c7 g3-f4 d8-e7 g1-h2 e7-f6 d2-c3 f8-e7 b2-c3 e7-d6 a1-b2 b6-a5 f2-g3 a7-b6 g3-h4",
        "c3-b4 f6-e5 b4-c5 e7-d6 a3-b4 e5-f4 b4-c5 h6-g5 d2-e3 g5-f4 c7-d6 h2-g3 g7-f6 f2-e3 a7-b6 g3-h4 b6-c5 e3-f4 b8-c7 g1-f2",
        "c3-b4 f6-e5 b4-c5 e7-d6 a3-b4 e5-f4 f6-e5 g3-h4 f8-e7 f2-g3 e5-f4 h4-g5 f4-e3 g7-f6 c3-d4 b2-a3 h8-g7 g1-f2 e7-d6 d4-c5",
        "c3-b4 f6-e5 b4-c5 e7-d6 c3-b4 a7-b6 b4-c5 b2-c3 h6-g5 c3-b4 c7-b6 b4-c5 d2-e3 g5-f4 e1-d2 b8-c7 a3-b4 g7-h6 b4-a5 c7-d6",
        "c3-b4 f6-e5 b4-c5 g3-f4 g7-f6 f6-e5 g1-h2 d6-c5 b2-c3 c7-d6 a1-b2 h8-g7 c1-d2 g7-f6 f4-e5 e3-f4 d8-e7 f2-e3 e7-f6 f4-g5",
        "c3-b4 f6-e5 c1-d2 e5-f4 g3xe5 d6xf4 b4xd6 c7xe5 e3xg5 h6xf4 f2-g3 a7-b6 d2-e3 f4xd2 e1xc3 g7-f6 g3-f4 e5xg3 h4xf2 e7-d6",
        "c3-b4 f6-e5 d2-c3 b6-c5 a1-b2 g7-f6 e3-d4 c7-b6 h2-g3 b6-c5 g3-h4 h8-g7 e1-f2 d8-c7 c1-d2 b8-a7 b4-a5 c7-b6 c3-b4 e7-d6",
        "c3-b4 f6-e5 d2-c3 g7-f6 b4-a5 f6-g5 c3-d4 e5xc3 b2xd4 g5-f4 g3xe5 d6xd2 c1xe3 b6-c5 d4xb6 a7xc5 a1-b2 c7-d6 e3-d4 c5xe3",
        "c3-b4 f6-e5 d2-c3 g7-f6 b4-a5 f6-g5 c3-d4 e5xc3 b2xd4 g5-h4 d4-c5 b6xd4 e3xc5 d6xb4 a5xc3 h8-g7 a1-b2 h6-g5 a3-b4 e7-d6",
        "c3-b4 f6-e5 e3-f4 b6-a5 b2-c3 c7-b6 f2-e3 e7-f6 e3-d4 d6-c5 b4xd6 e5xc7 c1-b2 f6-g5 f4-e5 g5-h4 e5-f6 h4xf2 e1xg3 g7xe5",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a1-b2 d6-c5 b2-c3 e3-d4 d2-c3 e3-d2 a7-b6 g5-h4 a7-b6 g3-h4 c7-d6 g1-f2 c3-d4 h4xf2 e1xg3",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 a1-b2 a7-b6 b2-c3 b6-c5 g3-h4 f8-e7 h4xf6 g7xg3 h2xf4 h8-g7 c3-d4 c7-b6",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 a1-b2 d8-e7 c1-d2 e7xc5 c3-b4 a5xc3 d2xd6 h6-g5 g3-f4 g7-h6 f4-e5 h8-g7",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 a1-b2 g5-h4 g1-f2 a7-b6 b2-c3 f8-e7 c1-b2 b6-a5 a3-b4 g7-f6 b4-c5 d6xb4",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 a3-b4 c7-b6 f4-e5 d6xf4 g3xe5 d8-e7 a1-b2 g7-f6 e5xg7 h8xf6 d2-c3 e7-d6",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 a3-b4 c7-b6 f4-e5 d6xf4 g3xe5 f8-e7 e3-d4 b8-c7 b4-c5 g5-h4 a1-b2 g7-f6",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 a3-b4 f8-e7 e7-f6 b2-a3 f6-e5 g3-h4 e5xg3 h4xf2 d6-e5 b4-c5 e5-f4 e3-d4",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 a3-b4 g5-h4 e1-f2 d6-e5 f4xd6 c7xe5 b4-c5 d8-e7 a1-b2 e5-d4 c5-b6 a7xc5",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 a3-b4 g5-h4 g1-f2 d8-e7 b4-a5 g7-f6 f4-e5 d6xf4 g3xg7 h8xf6 a1-b2 f6-e5",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 a3-b4 g5-h4 g1-f2 d8-e7 e3-d4 g7-f6 f4-e5 d6xf4 g3xg7 h8xf6 d2-e3 e7-d6",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 g3-h4 a7-b6 h4xf6 g7xg3 h2xf4 h8-g7 a1-b2 g7-f6 b2-c3 b6-a5 e3-d4 c7-b6",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 e7xg5 g3-h4 a7-b6 h4xf6 g7xg3 h2xf4 h8-g7 a1-b2 g7-f6 b2-c3 f8-g7 c3-d4 d6-e5",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 g7xe5 a3-b4 a7-b6 b4-a5 e7-f6 a1-b2 f6-g5 g3-h4 e5xg3 h4xf2 h8-g7 h2-g3 g5-h4",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 g7xe5 a3-b4 e7-f6 a1-b2 a7-b6 b4-a5 b6-c5 g3-h4 e5xg3 h4xf2 f6-e5 e3-f4 e5xg3",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 g7xe5 a3-b4 e7-f6 a1-b2 f6-g5 g3-h4 e5xg3 h4xf2 a7-b6 b4-a5 d6-e5 b2-c3 g5-f4",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 g7xe5 a3-b4 e7-f6 b4-a5 f6-g5 g3-h4 e5xg3 h4xf2 h8-g7 a1-b2 g7-f6 b2-c3 f8-e7",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 a5xc3 b2xf6 g7xe5 a3-b4 e7-f6 e5xg3 h4xf2 h6-g5 a1-b2 h8-g7 b2-c3 a7-b6 b4-a5 g5-h4 c3-d4",
        "c3-b4 f6-e5 e3-f4 b6-a5 f2-e3 g3-h4 h6-g5 a1-b2 g7-f6 h2-g3 g5-h4 b2-c3 h8-g7 e3-d4 d6-c5 c3-d4 f6-g5 d2-e3 g7-h6 a3-b4",
        "c3-b4 f6-e5 e3-f4 b6-c5 b2-c3 e7-f6 d2-e3 f6-g5 e3-d4 g5xe3 d4xf6 g7xe5 f2xf6 f8-g7 c1-d2 g7xe5 g3-f4 e5xg3 h2xf4 c7-b6",
        "c3-b4 f6-e5 e3-f4 e7-f6 b2-c3 f6-g5 d2-e3 g5-h4 c1-d2 a1-b2 b4-a5 d4-c3 a5xe5 c3xa1 e5-d6 e7-f6 d6xb4 f6-g5 f4-e5 a1xf6",
        "c3-b4 f6-e5 e3-f4 e7-f6 b2-c3 f6-g5 d2-e3 g5-h4 c1-d2 b6-c5 c7-b6 b4-a5 f8-e7 a5xc7 d8xb6 c3-b4 b6-a5 b2-c3 g7-f6 f4-g5",
        "c3-b4 f6-e5 e3-f4 e7-f6 b2-c3 f6-g5 d2-e3 g7-f6 b4-a5 g1xe3 h6-g5 b2-c3 g7-h6 c3-d4 c5-b4 a3xc5 e3-f4 g5xe3 h6-g5 d2-c3",
        "c3-b4 f6-e5 e3-f4 e7-f6 b2-c3 f6-g5 f2-e3 g5-h4 g1-f2 b6-c5 f8-e7 a1-b2 c7-b6 a5xc7 d8xb6 c3-b4 g7-f6 b4-a5 f6-g5 a5xc7",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 b6-c5 b2-c3 c5-d4 a1-b2 f6-g5 a3-b4 g5xe3 d2xf4 g7-f6 e1-d2 f6-g5 d2-e3 g5-h4 e3xe7 f8xd6",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 b6-c5 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 g7xe5 g3-h4 f8-g7 h2-g3 e5-d4 a1-b2 h6-g5 h4xf6 g7xe5",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 b6-c5 c3-b4 e5-d4 d2-e3 d4xf2 g1xe3 h8-g7 e1-f2 g7-f6 c1-d2",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 g3-h4 b6-c5 c3-b4 h8-g7 a1-b2 g7-f6 h2-g3 f8-e7 d2-c3 h6-g5",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 g3-h4 b6-c5 e1-f2 f8-e7 c3-b4 h8-g7 d2-e3 c5-d4 e3xc5 c7-b6",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 g3-h4 d6-c5 c3-b4 e5-d4 b4xd6 c7xe5 a5xc7 b8xd6 g1-f2 d6-c5",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 g3-h4 d6-c5 c3-b4 e5-d4 b4xd6 c7xe5 a5xc7 b8xd6 h2-g3 h8-g7",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 g3-h4 h8-g7 c3-b4 g7-f6 d2-e3 b6-c5 a1-b2 e5-d4 e1-f2 f8-e7",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 g3-h4 h8-g7 e1-f2 g7-f6 h2-g3 d6-c5 c3-b4 c5-d4 d2-c3 d4xb2",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 h8-g7 a1-b2 b6-c5 c3-b4 g7-f6 h2-g3 e5-d4 g3-f4 d4-e3 f4-e5",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 h8-g7 c3-b4 g7-f6 d2-e3 b6-c5 h2-g3 e5-d4 e3-f4 f6-e5 e1-f2",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 h8-g7 c3-b4 g7-f6 h2-g3 b6-c5 a1-b2 f8-g7 d2-e3 e5-d4 e1-f2",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 h8-g7 c3-b4 g7-f6 h2-g3 b6-c5 d2-e3 f8-e7 a1-b2 e5-d4 g1-f2",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 g7xe5 h8-g7 g1-f2 g7-f6 d2-e3 b6-c5 g3-h4 f8-e7 c1-d2 e5-d4 a1-b2",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 d2-e3 g5-h4 b2-c3 b6-c5 c3-b4 g7-f6 e1-d2 h8-g7 f4-g5 h6xf4 e3xe7 d8xf6 d2-e3 e5-d4",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 f2-e3 b6-c5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b2-c3 g7-f6 c3-b4 h8-g7 d2-c3 g7-h6",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 f2-e3 g5-h4 g1-f2 b2-c3 f8-e7 c1-b2 c7-b6 a5xc7 d8xb6 c3-b4 b6-a5 b2-c3 f4-g5 h6xf4",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 f2-e3 g5-h4 g1-f2 b6-c5 b2-c3 a7-b6 c1-b2 g7-f6 c3-d4 e5xc3 b2xd4 f6-g5 a1-b2 h8-g7",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 g3-h4 g5xe3 f2xf6 g7xe5 b2-c3 b6-c5 e1-f2 e5-f4 f2-g3 d6-e5 g1-f2 e5-d4 c3xe5 f4xd6",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f6-g5 g3-h4 g5xe3 f2xf6 g7xe5 b2-c3 h8-g7 c3-b4 e5-f4 a1-b2 f8-e7 e1-f2 g7-f6 d2-c3 d6-e5",
        "c3-b4 f6-e5 e3-f4 e7-f6 b4-a5 f8-e7 b2-c3 f6-g5 c3-b4 g5xe3 f2xf6 e7xg5 g3-h4 g5-f4 d2-e3 f4xd2 c1xe3 d6-e5 h2-g3 e5-d4",
        "c3-b4 f6-e5 e3-f4 e7-f6 d2-e3 b6-a5 b4-c5 d6xb4 a3xc5 f6-g5 f4xd6 c7xe5 c1-d2 e5-d4 c5-d6 g7-f6 e3xc5 f6-e5 d6xf4 g5xa3",
        "c3-b4 f6-e5 e3-f4 e7-f6 d2-e3 f6-g5 b2-c3 b4-a5 a7-b6 c3-b4 b8-a7 f4-g5 h6xf4 e3xg5 h4xf6 d2-c3 g7-h6 g3-f4 e5xg3 h2xf4",
        "c3-b4 f6-e5 e3-f4 e7-f6 d2-e3 f6-g5 b2-c3 g5-h4 c1-d2 b6-c5 c7-b6 b4-a5 f8-e7 a5xc7 d8xb6 c3-b4 e5-d4 b4-a5 d4-c3 a5xe5",
        "c3-b4 f6-e5 e3-f4 e7-f6 d2-e3 f6-g5 b2-c3 g7-f6 c1-d2 b6-a5 b4-c5 d6xb4 f4xd6 c7xe5 a3xc5 g5-f4 e3xe7 f8xb4 g3-f4 e5xg3",
        "c3-b4 f6-e5 e3-f4 e7-f6 d2-e3 f6-g5 b4-c5 b6xd4 e3xe7 g5xe3 f2xf6 g7xe5 g3-h4 f8xd6 h2-g3 a7-b6 c1-d2 h8-g7 g3-f4 e5xg3",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 b2-c3 b6-c5 e3-d4 c5xe3 e5xg3 h4xd4 g5-h4 b4-c5 d6xb4 a3xc5 g7-f6 a1-b2 h6-g5 h2-g3",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 b2-c3 g5-h4 g1-f2 b6-c5 b4-a5 c7-b6 a5xc7 d8xb6 c3-d4 e5xc3 d2xb4 d6-e5 f4xd6 c5xe7",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 b2-c3 g5-h4 g1-f2 b6-c5 f8-e7 a1-b2 a7-b6 c3-b4 e7-f6 f4-g5 h6xf4 e3xe7 d8xf6 d2-e3",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 b2-c3 g5-h4 g1-f2 b6-c5 f8-e7 a1-b2 c7-b6 a5xc7 d8xb6 c3-b4 e5-d4 b2-c3 d4xb2 d2-c3",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b2-c3 g7-f6 b4-a5 b6-c5 c3-b4 h8-g7 d2-e3 f4xd2",
        "c3-b4 f6-e5 e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 b2-c3 g7-f6 b4-a5 b6-c5 c3-b4 h8-g7 f2-g3 f6-e5",
        "c3-b4 f6-e5 e3-f4 g5xe3 d2xd6 c7xe5 b4-a5 b6-c5 b2-c3 c5-d4 e7-f6 a5-b6 a7xc5 b4xf4 f6-g5 c1-b2 g5xe3 b2-c3 d4xb2 a3xc1",
        "c3-b4 f6-e5 e3-f4 g7-f6 b2-c3 b6-a5 b4-c5 d6xb4 f4xd6 e7xc5 c3-d4 c5xe3 a3xc5 f8-e7 f2xd4 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7",
        "c3-b4 f6-e5 e3-f4 g7-f6 b2-c3 b6-a5 b4-c5 d6xb4 f4xd6 e7xc5 c5xe3 a3xc5 f8-e7 f2xd4 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5",
        "c3-b4 f6-e5 e3-f4 g7-f6 b2-c3 b6-a5 d2-e3 c7-b6 c3-d4 e5xc3 b4xd2 b6-c5 g3-h4 f6-g5 h4xf6 e7xg5 d2-c3 g5-h4 c1-b2 h8-g7",
        "c3-b4 f6-e5 e3-f4 g7-f6 b2-c3 b6-a5 f2-e3 c7-b6 g3-h4 e5xg3 h4xf2 h6-g5 a1-b2 b6-c5 e3-d4 c5xe3 d2xh6 f6-e5 b4-c5 d6xd2",
        "c3-b4 f6-e5 e3-f4 g7-f6 b2-c3 b6-c5 d2-e3 a7-b6 b4-a5 b8-a7 c3-b4 c5-d4 e3xc5 b6xd4 c1-b2 f6-g5 b2-c3 g5xe3 g3-h4 d4xb2",
        "c3-b4 f6-e5 e3-f4 g7-f6 b2-c3 b6-c5 d2-e3 c7-b6 b4-a5 c5-b4 a5xc7 b4xd2 e1xc3 d8xb6 e3-d4 b6-c5 d4xb6 a7xc5 c5-d4 e3xc5",
        "c3-b4 f6-e5 e3-f4 g7-f6 b2-c3 b6-c5 d2-e3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 f2xf6 f8-e7 h2-g3 e7xg5 a1-b2 f6-g5 g3-h4 e5xg3",
        "c3-b4 f6-e5 e3-f4 g7-f6 b4-a5 a7-b6 f2-e3 b8-a7 c1-d2 c5-d4 e3xc5 b6xd4 b2-c3 d4xb2 a1xc3 a7-b6 c3-b4 b6-c5 d2-e3 c7-b6",
        "c3-b4 f6-e5 e3-f4 g7-f6 b4-a5 f6-g5 b2-c3 g5xe3 f2xf6 e7xg5 g3-h4 f8-e7 h4xf6 e7xg5 a1-b2 h8-g7 e1-f2 g7-f6 d2-e3 g5-h4",
        "c3-b4 f6-e5 e3-f4 g7-f6 b4-a5 f6-g5 d2-e3 g5-h4 b2-c3 b6-c5 c3-b4 a7-b6 c1-d2 h8-g7 a1-b2 e5-d4 d2-c3 e7-f6 c3xe5 f6xd4",
        "c3-b4 f6-e5 e3-f4 g7-f6 b4-a5 f6-g5 d2-e3 g5-h4 b2-c3 b6-c5 h8-g7 e1-d2 e5-d4 a1-b2 a7-b6 d2-c3 e7-f6 c3xe5 f6xd4 f4-e5",
        "c3-b4 f6-e5 e3-f4 g7-f6 b4-a5 f6-g5 g3-h4 g5xe3 f2xf6 e7xg5 h4xf6 f8-g7 h2-g3 g7xe5 g3-h4 d6-c5 e1-f2 h8-g7 f2-g3 g7-f6",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b2-c3 f8-g7 a7-b6 g5-h4 c1-d2 h4xf2 e3xg1 f8-g7 b4-c5 d6xb4 g7-h6 a3xa7 e5-f4 c3-b4 f6-g5",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 b2-c3 c7-b6 c3-d4 e5xc3 b4xd2 b6-c5 g3-h4 f6-g5 h4xf6 e7xg5 d2-c3 g5-h4 a1-b2 h8-g7",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 b2-c3 c7-b6 c3-d4 e5xc3 b4xd2 b6-c5 g3-h4 f6-g5 h4xf6 e7xg5 d2-c3 g5-h4 c1-b2 h8-g7",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 a7xc5 f4-e5 d4-c3 b2xb6 f6xd4 e3xc5 b8-a7 g3-f4 c7-d6 b6-c7",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 c5-b6 a7xc5 f4-e5 d4-c3 b2xb6 f6xd4 e3xc5 b8-a7 g3-f4 c7-d6",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 c5-b6 a7xc5 f4-e5 d4-c3 b2xb6 f6xd4 e3xc5 b8-a7 g3-f4 h6-g5",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 c5-d6 e7xc5 f4-e5 h6-g5 e5xc3 g5-h4 c3-d4 c7-d6 d4xb6 a7xc5",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 a7-b6 b4-a5 h8-g7 b2-c3 b6-c5 c3-b4 e5-d4 g3-h4 f6-e5 a1-b2 e5xg3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 a7-b6 b4-a5 h8-g7 b2-c3 b6-c5 c3-b4 e5-d4 g3-h4 f6-e5 h4-g5 e5xg3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 a7-b6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 h8-g7 f4xd6 c7xe5 g3-f4 e5xg3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 a7-b6 h8-g7 b2-c3 b6-c5 c3-b4 e5-d4 g3-h4 f6-e5 a1-b2 e5xg3 h2xf4",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 a7-b6 h8-g7 b2-c3 b6-c5 c3-b4 e5-d4 g3-h4 f6-e5 h4-g5 e5xg3 h2xf4",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 b4-c5 d6xb4 a3xc5 c7-b6 f4xd6 b6xd4 d2-c3 e7xc5 c3xe5 h8-g7 b2-c3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 h8-g7 b2-c3 a7-b6 b4-a5 b6-c5 c3-b4 e5-d4 g3-h4 f6-e5 a1-b2 e5xg3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 h8-g7 b2-c3 a7-b6 b4-a5 b6-c5 c3-b4 e5-d4 g3-h4 f6-e5 h4-g5 e5xg3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 h8-g7 b4-a5 a7-b6 b2-c3 b6-c5 c3-b4 e5-d4 a1-b2 f6-e5 g3-h4 e5xg3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-a5 c1-d2 a5xc3 d2xb4 h8-g7 b4-a5 a7-b6 b2-c3 b6-c5 c3-b4 e5-d4 g3-h4 f6-e5 h4-g5 e5xg3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-c5 b2-c3 a7-b6 b4-a5 b8-a7 b8-a7 c3-b4 f6-g5 d2-c3 g5-h4 c3-d4 e5xc3 b4xd2 f4-g5 h6xf4",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-c5 b2-c3 a7-b6 b4-a5 b8-a7 c3-b4 c5-d4 e3xc5 b6xd4 c1-b2 f6-g5 g3-h4 g5xe3 b2-c3 d4xb2",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-c5 b2-c3 a7-b6 b4-a5 b8-a7 c3-b4 c5-d4 e3xc5 b6xd4 c1-d2 h6-g5 f4xh6 f6-g5 h6xf4 d4-e3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-c5 b2-c3 a7-b6 b4-a5 b8-a7 c3-d4 e5xc3 c1-d2 c5-b4 a3xc5 b6xd4 d2xb4 f6-e5 e3xc5 c7-b6",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-c5 b2-c3 a7-b6 b4-a5 b8-a7 c3-d4 e5xc3 c1-d2 f6-g5 d2xb4 c5-d4 e3xc5 b6xd4 a1-b2 g5xe3",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-c5 b2-c3 a7-b6 b4-a5 b8-a7 c5-d4 e3xc5 b6xd4 c1-d2 h6-g5 f4xh6 f6-g5 h6xf4 d4-e3 f2xf6",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-c5 b2-c3 c7-b6 b4-a5 c5-b4 a3xc5 d6xd2 e1xc3 e7-d6 a5xc7 d8xb6 e3-d4 b6-a5 c1-b2 a7-b6",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 b6-c5 b2-c3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 f2xf6 f8-g7 c1-d2 g7xe5 e3-f4 e5xg3 h2xf4 h8-g7",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 f2xf6 f8-e7 e3-d4 e7xg5 b4-c5 d6xb4 a3xc5 c7-d6 c5xe7 d8xf6",
        "c3-b4 f6-e5 e3-f4 g7-f6 d2-e3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 f2xf6 f8-e7 e3-d4 e7xg5 b4-c5 d6xb4 a3xc5 g5-h4 e1-f2 c7-d6",
        "c3-b4 f6-e5 e3-f4 g7-f6 f2-e3 b6-a5 g3-h4 e5xg3 h4xf2 a5xc3 d2xb4 f6-e5 b2-c3 a7-b6 b4-a5 h8-g7 a1-b2 g7-f6 c3-b4 e5-f4",
        "c3-b4 f6-e5 e3-f4 g7-f6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 h8-g7 g7-f6 b4-a5 b6-c5 c3-b4 g5-h4 d2-c3 f6-g5 a1-b2 g5-f4 e3xg5",
        "c3-b4 f6-e5 g3-f4 e5xg3 h2xf4 b6-c5 b2-c3 e7-f6 a1-b2 f6-e5 f2-g3 g7-f6 g3-h4 e5xg3 h4xf2 h8-g7 b4-a5 d6-e5 c3-b4 c7-d6",
        "c3-b4 f6-e5 g3-f4 e5xg3 h2xf4 b6-c5 b2-c3 e7-f6 c3-d4 f6-e5 d4xf6 g7xg3 f2xh4 h8-g7 e1-f2 g7-f6 e3-f4 f6-g5 h4xf6 d6-e5",
        "c3-b4 f6-e5 g3-f4 e5xg3 h2xf4 d6-c5 b4xd6 c7xg3 f2xh4 h6-g5 h4xf6 g7xe5 e1-f2 h8-g7 f2-g3 g7-f6 g3-h4 b8-c7 a3-b4 b6-a5",
        "c3-b4 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 f6-g5 h4xf6 e7xg5 b4-a5 h8-g7 c1-b2 g5-h4 e1-d2 f8-e7 c3-b4 e7-f6 f4-g5 h6xf4",
        "c3-b4 f6-e5 g3-f4 h6-g5 b4-a5 g7-f6 b2-c3 g5-f4 c3-b4 h8-g7 d2-e3 d6-e5 e3-d4 g7-f6 a3-b4 f6-e5 a1-b2 e7-d6 b2-a3 d8-e7",
        "c3-b4 f6-e5 g3-h4 b6-a5 f2-g3 a5xc3 b2xf6 g7xe5 e3-f4 h8-g7 g7-f6 b2-c3 a7-b6 c3-b4 b6-c5 d2-c3 c5-d4 b4-c5 d6xd2 c1xc5",
        "c3-b4 f6-e5 g3-h4 b6-a5 h4-g5 h6xf4 e3xg5 a5xc3 b2xf6 g7xe5 a7-b6 g3-h4 d6-c5 f2-e3 b6-a5 e3-f4 e5xg3 h4xf2 h8-g7 g5-h6",
        "c3-b4 f6-e5 g3-h4 b6-a5 h4-g5 h6xf4 e3xg5 a5xc3 b2xf6 g7xe5 a7-b6 g3-h4 d6-c5 f2-g3 b6-a5 g3-f4 e5xg3 h4xf2 h8-g7 g5-h6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 b4-a5 b6-c5 b4-a5 a1-b2 c5-b4 a3xc5 d6xb4 c3-d4 f2-g3 b4-a3 f2-g3 a1-b2 e7-d6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 b6-c5 a1-b2 b4-a5 a7-b6 b4-a5 f2-g3 f2-e3 b6-a5 e3xg5 c5-d4 d2-e3 b4-a5 d6-e5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 b6-c5 g7-f6 b4-a5 h8-g7 b6-c5 b4-a5 b6-c5 c3-b4 h8-g7 f2-e3 g7-h6 e3xg5 h6xf4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b2-c3 g7-f6 b4-a5 b6-c5 h8-g7 f2-g3 a7-b6 g3xe5 d6xf4 b4xd6 c7xe5 a5xc7 b8xd6 a1-b2",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 f2-g3 e7-d6 g3xe5 d6xf4 g1-f2 d8-e7",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 e7-f6 c3-b4 g7-h6 d2-c3 f8-g7 f2-e3 f4xd2 c1xe3 f6-g5 h4xf6 g7xe5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 a7-b6 a1-b2 f6-e5 f2-g3 h8-g7 e1-f2 g7-h6 b2-c3 e5-d4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 a7-b6 f2-g3 f6-e5 e1-f2 f8-g7 a1-b2 e7-f6 f2-e3 f6-g5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 f6-e5 e1-f2 c7-b6 a5xc7 d8xb6 b4-a5 b8-c7",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 e7-f6 d6-e5 c3-b4 a7-b6 b4xd6 e7xc5 a1-b2 c7-d6 a5xc7 d8xb6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 h8-g7 f2-g3 f6-e5 e1-f2 c7-b6 a5xc7 d8xb6 b4-a5 b8-c7 a3-b4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 d2-c3 d6-e5 c3-b4 e7-d6 b2-c3 g7-f6 f2-g3 h8-g7 e1-f2 c5-d4 a1-b2 f4-e3",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 e7-f6 b2-c3 f6-e5 f2-g3 b6-c5 c3-b4 d8-e7 f8-e7 e1-f2 a7-b6 a1-b2 e7-f6 b2-c3",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 e7-f6 b2-c3 f6-g5 h4xf6 g7xe5 c3-b4 h8-g7 a1-b2 g7-h6 f2-g3 b6-c5 g1-f2 a7-b6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 e7-f6 b2-c3 f6-g5 h4xf6 g7xe5 c3-b4 h8-g7 d2-c3 b6-c5 c3-d4 e5xc3 b4xd2 g7-f6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 b6-c5 c3-b4 h8-g7 a1-b2 f6-e5 f2-g3 e7-f6 g1-f2 c7-b6 a5xc7 d8xb6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 f6-g5 h4xf6 e7xg5 a1-b2 d6-e5 a3-b4 c3-b4 b6-c5 b4xd6 f4-g3 f2xd4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 f6-g5 h4xf6 e7xg5 a1-b2 h8-g7 f2-g3 g7-h6 g3xe5 d6xf4 a3-b4 b6-c5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 f6-g5 h4xf6 e7xg5 c3-b4 h8-g7 f2-g3 f8-e7 g3xe5 d6xf4 a1-b2 e7-d6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 f6-g5 h4xf6 e7xg5 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 g7-h6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 a1-b2 g7-h6 f2-g3 d6-e5 c3-b4 e7-d6 d2-c3 f4-e3 e1-f2 e1-d2",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-b4 d6-c5 b4xd6 c7xe5 a5xc7 b8xd6 a3-b4 d6-c5 b4xd6 e5xc7",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-b4 d6-c5 b4xd6 c7xe5 a5xc7 b8xd6 f4-g3 h2xf4 d6-c5 b4xd6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-b4 g7-h6 b4-c5 b6xd4 d2-e3 f4xd2 e1xg7 h6-g5 h4xf6 f8xh6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-b4 g7-h6 b4-c5 d6xb4 a3xc5 b6xd4 d2-e3 f4xd2 e1xg7 h6-g5",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 g7-h6 b4-c5 b6xd4 d2-e3 f4xd2 e1xg7 h6-g5 h4xf6 f8xh6 f2-g3",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 g7-h6 b4-c5 d6xb4 a3xc5 b6xd4 d2-e3 f4xd2 e1xg7 h6-g5 h4xf6",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 g7-h6 f2-g3 d6-e5 c3-b4 b6-c5 b4xd6 e7xc5 g1-f2 d8-e7 b2-c3",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 d2-c3 h8-g7 c1-d2 g7-h6 f2-g3 f8-g7 g3xe5 d6xf4 g1-f2 e7-d6 d2-e3 f4xb4",
        "c3-b4 f6-e5 g3-h4 e5-f4 e3xg5 h6xf4 f2-g3 d6-e5 b4-a5 b6-c5 b2-c3 c5-d4 a1-b2 e7-f6 e1-f2 f8-e7 a3-b4 f6-g5 h4xf6 e7xg5",
        "c3-b4 f6-g5 b2-c3 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 g3-f4 g7-f6 c3-d4 f6-g5 c5-b6 a7xc5 d4xb6 a5-b4 b6-a7 e7-d6 a1-b2 b4-a3",
        "c3-b4 f6-g5 b2-c3 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5 g7-f6 c3-b4 h8-g7 a1-b2 f6-e5 b2-c3 g7-h6 f2-g3 e5-d4 c3xe5 f4xd6",
        "c3-b4 f6-g5 b2-c3 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5 g7-f6 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 f6-g5 c3-b4 e7-d6",
        "c3-b4 f6-g5 b2-c3 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 b4-a5 g7-f6 f2-g3 f6-e5 c1-b2 b6-c5 c3-b4 h8-g7 b4xd6 e7xc5 e1-f2 g7-f6",
        "c3-b4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4-a5 g7-f6 a1-b2 h8-g7 c3-b4 b6-c5 b4xd6 c7xe5 b2-c3 d8-c7 c3-b4 a7-b6",
        "c3-b4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c1-b2 b6-c5 b4xd6 e7xc5 c3-b4 c7-d6 f2-g3 d8-c7 g3xe5 d6xf4 b4xd6 c7xe5",
        "c3-b4 f6-g5 b2-c3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c1-b2 c7-d6 b4-c5 d6xb4 c3xc7 b8xd6 d2-c3 d6-e5 c3-d4 e5xc3 b2xd4 e7-f6",
        "c3-b4 f6-g5 b2-c3 g5-h4 a1-b2 b6-c5 e3-f4 e7-f6 f4-g5 h6xf4 g3xe5 f6xd4 c3xe5 d6xf4 b4xd6 c7xe5 b2-c3 a7-b6 d2-e3 f4xb4",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 g7-f6 c3-b4 b6-c5 g3-f4 h8-g7 f6-e5 c1-d2 e5xg3 h2xf4 g7-f6 c3-d4 f6-g5 d4xb6 a7xc5 d2-c3",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 g7-f6 c3-d4 d6-e5 d2-c3 e7-d6 c3-b4 e5xc3 b4xd2 h8-g7 a3-b4 f8-e7 b4-c5 b6xd4 e3xc5 d6xb4",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 g7-f6 g3-f4 f6-e5 a1-b2 e5xg3 h2xf4 d6-e5 f4xd6 c7xe5 a5xc7 b8xd6 c3-b4 e5-f4 e3xg5 h4xf6",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 g7-f6 g3-f4 f6-e5 a1-b2 e5xg3 h2xf4 h8-g7 c3-d4 g7-f6 b2-c3 d6-c5 f2-g3 h4xf2 e1xg3 h6-g5",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 h6-g5 g3-f4 g7-h6 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 c5-b4 a3xc5 d6xb4 f4-e5 b4-a3",
        "c3-b4 f6-g5 b2-c3 g5-h4 b4-a5 h6-g5 g3-f4 g7-h6 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 c5-b4 a3xc5 d6xb4 f4-e5 g7-f6",
        "c3-b4 f6-g5 b2-c3 g5-h4 c3-d4 b6-a5 d4-c5 a5xc3 d2xb4 g7-f6 d6xb4 a5xc3 e7-d6 c3-b4 f8-e7 a1-b2 a7-b6 c1-d2 f6-g5 b4-c5",
        "c3-b4 f6-g5 b2-c3 g5-h4 c3-d4 g7-f6 d4-c5 b6xd4 e3xc5 c7-b6 b6xd4 e3xc5 h6-g5 b4-a5 d6xb4 a5xc3 a7-b6 c3-b4 e7-d6 g3-f4",
        "c3-b4 f6-g5 b2-c3 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 b6-c5 a1-b2 h8-g7 b4-a5 c5-b4 a3xc5 d6xb4 b2-a3 g7-f6",
        "c3-b4 f6-g5 b2-c3 g7-f6 a1-b2 g5-h4 b4-a5 f6-e5 g3-f4 e5xg3 h2xf4 h8-g7 c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 g7-f6 c3-d4 f6-e5",
        "c3-b4 f6-g5 b2-c3 g7-f6 b4-a5 b6-c5 g3-f4 g5-h4 c3-d4 f6-g5 d4xb6 a7xc5 a1-b2 h8-g7 d2-c3 c5-b4 a3xc5 d6xd2 e1xc3 e7-d6",
        "c3-b4 f6-g5 b2-c3 g7-f6 b4-a5 f6-e5 a1-b2 e5-f4 g3xe5 d6xf4 f2-g3 e7-d6 g3xe5 d6xf4 a3-b4 h8-g7 e1-f2 g5-h4 e3xg5 h4xf6",
        "c3-b4 f6-g5 b2-c3 g7-f6 b4-a5 f6-e5 g3-h4 e5-f4 h4xf6 e7xg5 a1-b2 g5-h4 e3xg5 h4xf6 h2-g3 f6-e5 g3-h4 h8-g7 c3-b4 g7-f6",
        "c3-b4 f6-g5 b2-c3 g7-f6 c3-d4 b6-c5 d4xb6 c7xc3 d2xb4 d6-e5 g3-f4 e5xg3 h2xf4 d8-c7 a1-b2 h8-g7 b4-a5 c7-d6 e1-d2 g5-h4",
        "c3-b4 f6-g5 b2-c3 g7-f6 c3-d4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 a1-b2 b6-a5 g3-f4 f6-g5 c5-b6 a7xc5 d4xb6 c7-d6 b6-a7 d6-c5",
        "c3-b4 f6-g5 b2-c3 g7-f6 c3-d4 h8-g7 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 g3-f4 g7-f6 h2-g3 b6-a5 f4-e5 f8-g7 g3-f4 c7-d6 e5xc7",
        "c3-b4 f6-g5 b2-c3 g7-f6 g3-f4 h8-g7 b4-a5 g5-h4 f4-g5 h6xf4 e3xg5 b6-c5 g5-h6 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 d2-e3 c7-b6",
        "c3-b4 f6-g5 b4-a5 b6-c5 g3-h4 g5-f4 e3xg5 h6xf4 f2-g3 e7-f6 g3xe5 d6xf4 b2-c3 d8-e7 g1-f2 c7-d6 a1-b2 f6-e5 f2-e3 g7-h6",
        "c3-b4 f6-g5 b4-a5 g5-h4 b2-c3 h6-g5 c3-b4 g5-f4 e3xg5 h4xf6 b6-c5 g3-h4 g7-h6 f2-g3 f6-g5 h4xf6 e7xg5 c1-d2 c7-b6 a5xe5",
        "c3-b4 f6-g5 b4-a5 g5-h4 b2-c3 h6-g5 c3-b4 g5-f4 g3xe5 d6xf4 e3xg5 h4xf6 h2-g3 f6-e5 d2-e3 g7-f6 a1-b2 h8-g7 b2-c3 e5-f4",
        "c3-b4 f6-g5 b4-a5 g7-f6 b2-c3 f6-e5 g3-h4 e5-f4 h4xf6 e7xg5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 g5-h4 e3xg5 h4xf6 c3-b4",
        "c3-b4 f6-g5 b4-a5 h6-g5 a3-b4 e5-f4 b4-c5 h8-g7 c3-b4 g5-h4 b4-a5 b6-c5 b2-c3 c7-b6 a1-b2 f6-e5 b2-a3 e5-f4 c3-b4 d6-e5",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-b6 d2-e3 b6xd4 e3xc5 g5-h4 g3-f4 g7-f6 b2-c3 f6-g5 e1-d2 g5xe3 d2xf4 h8-g7",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 b6xd4 d2-e3 g7xe5 e3xc5 b8-c7 c1-d2 c7-b6 d2-e3 b6xd4 e3xc5",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 e3-f4 b4-a3 b2-c3 b6-a5 h2-g3 d8-e7",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 f8-e7 g3-f4 b6-a5 b2-c3 b8-c7",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 f8-e7 g3-f4 b6-a5 b2-c3 g7-f6",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 f8-e7 g3-h4 b6-a5 b2-c3 b8-c7",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-g3 c5-b4 d2-e3 b4-a3 e3-f4 d8-e7 b2-c3 e7-f6",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 c5-b4 b2-c3 b4-a3",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 c5-b4 b2-c3 f8-e7",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 d8-e7 g1-f2 e7-d6",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 e5-d6 b4-a3 b2-c3 b6-a5 f2-e3 h6-g5",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 e5-d6 b4-a3 b2-c3 h6-g5 a1-b2 b6-a5",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 f2-e3 f8-e7 g3-f4 b6-a5 d2-c3 b4xd2",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 b2-c3 b6-a5 g1-h2 b8-c7",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 f2-g3 b6-a5 b2-c3 d8-e7",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 a7-b6",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 g7-f6",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 g1-h2 a7-b6",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 c5-b4 e3-f4 f8-e7 b2-c3 b6-a5 g1-f2 b8-c7 a1-b2",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 c5-b4 h2-g3 f8-e7 e3-f4 b4-a3 b2-c3 g7-f6 e5xg7",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 f2-e3 f8-e7 g3-h4 b8-c7 b2-c3 b6-a5 e3-d4",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 b2-c3 b6-a5 f2-e3 a7-b6 g1-f2",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 b4-a3 f2-g3 b6-a5 b2-c3 d8-e7 g1-h2",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 a1-b2 b8-c7 g1-h2",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 a7-b6 g1-f2",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 b8-c7 a1-b2",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 g7-f6 e5xg7",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 g1-h2 b8-c7 a1-b2",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 b2-c3 h6-g5 g7-h6 c3-b4 h8-g7 b2-c3 c7-b6 c3-d4 b6-a5 d2-e3 a5xe5 e3-f4",
        "c3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5-h4 g3-f4 c7-b6 b6xd4 e3xc5 g7-f6 b2-c3 f6-g5 a1-b2 g5xe3 f2xd4 h8-g7 e1-f2",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-d6 c5xe7 f8xd6 b2-a3 g5-f4 g3xe5 d6xf4 f2-g3 h6-g5 g3xe5 d8-e7 d2-c3 e7-d6",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 d2-e3 f6-e5 c5-d6 e5-d4 e3xc5 c7xe5 b2-c3 f8-e7 c1-b2 b8-c7 g3-h4 g5-f4",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 e7-f6 d2-e3 f6-e5 c5-d6 e5-d4 e3xc5 c7xe5 b2-c3 f8-e7 c1-b2 b8-c7 g3-h4 g7-f6",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 e1-f2 f8-e7 e5-d6 e7xc5 b2-a3 b8-c7",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 f2-e3 c5-b4 h2-g3 b6-a5 b2-c3 a7-b6 e3-f4 f8-e7",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 b6-a5 g3-f4 a7-b6 f2-e3 c5-b4 b2-c3 f8-e7",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 a7-b6",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 c5-d6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 f2-e3 g7-f6",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 b6-a5 g1-f2 a7-b6 f2-g3 c5-b4 e3-f4 f8-e7 b2-c3",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 f2-e3 c5-b4 e3-f4 b4-a3 b2-c3 b6-a5 h2-g3 d8-e7 a1-b2",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-f4 g3xe5 c7-b6 e7xc5 h2-g3 c5-b4 g3-f4 f8-e7 b2-c3 b6-a5 c1-b2 a7-b6 f2-g3",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 g3-f4 g5xe3 f2xd4 h8-g7 h2-g3 h4xf2 e1xg3 g7-f6",
        "c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5-h4 g3-f4 g7-f6 f6-g5 d2-e3 e7-d6 c5xe7 f8xd6 a1-b2 a7-b6 b2-a3 b6-a5 c1-b2",
        "c3-b4 f6-g5 b4-c5 e7-d6 g3-f4 g7-f6 a3-b4 f6-e5 f8-e7 b2-c3 e7-d6 c3-d4 d6-e5 e3-d4 h8-g7 f2-e3 e7-d6 d4-c5 a7-b6 e3-d4",
        "c3-b4 f6-g5 d2-c3 b6-a5 g3-h4 c7-b6 h4xf6 e7xg5 e1-d2 b6-c5 e3-d4 c5xe3 f2xd4 g7-f6 b4-c5 d6xb4 a3xc5 f8-e7 g1-f2 b8-c7",
        "c3-b4 f6-g5 d2-c3 b6-a5 g3-h4 c7-b6 h4xf6 e7xg5 e1-d2 d6-e5 b4-c5 b6xd4 e3xc5 g5-f4 f2-g3 g7-f6 c5-d6 e5xc7 g3xg7 h8xf6",
        "c3-b4 f6-g5 d2-c3 b6-a5 g3-h4 c7-b6 h4xf6 e7xg5 e3-d4 b6-c5 d4xb6 a7xc5 h2-g3 g7-f6 f2-e3 f8-e7 e1-f2 g5-h4 g3-f4 f6-e5",
        "c3-b4 f6-g5 d2-c3 g5-h4 c3-d4 g7-f6 b2-c3 e7-d6 h8-g7 d2-e3 f6-e5 e3-d4 g7-f6 a1-b2 f8-g7 g3-f4 f6-g5 d2-e3 d6-e5 e3-f4",
        "c3-b4 f6-g5 d2-c3 g5-h4 c3-d4 g7-f6 b2-c3 h8-g7 e7-d6 a1-b2 f6-g5 g3-f4 b6-c5 c3-d4 g7-f6 b2-c3 f6-e5 c1-b2 f8-e7 c3-d4",
        "c3-b4 f6-g5 d2-c3 g7-f6 c1-d2 d6-e5 g3-h4 g5-f4 e3xg5 h6xf4 f6-g5 h4xd4 c7-d6 e3xg5 d6-c5 b4xd6 e7xc1 g5-h6 d8-e7 h2-g3",
        "c3-b4 f6-g5 d4-c5 c7-b6 d2-e3 g7-f6 f6-e5 a3-b4 a7-b6 b4-a5 e7-d6 c3-d4 g3-f4 d6-e5 c1-d2 h6-g5 b2-c3 f8-e7 a1-b2 e7-d6",
        "c3-b4 f6-g5 e3-d4 d6-c5 b4xd6 e7xe3 f2xd4 g7-f6 b2-c3 g5-h4 a3-b4 h4xf2 g1xe3 h6-g5 b4-a5 h8-g7 a1-b2 g5-h4 e1-f2 b6-c5",
        "c3-b4 f6-g5 e3-d4 d6-c5 b4xd6 e7xe3 f2xd4 g7-f6 b2-c3 g5-h4 a3-b4 h4xf2 g1xe3 h6-g5 b4-c5 h8-g7 a1-b2 g7-h6 e3-f4 g5xe3",
        "c3-b4 f6-g5 e3-d4 e7-f6 d4-e5 f6xd4 b4-c5 d6xb4 a3xe3 f8-e7 b2-c3 g5-h4 g3-f4 b6-c5 c1-b2 c7-b6 b2-a3 e7-d6 h2-g3 g7-f6",
        "c3-b4 f6-g5 e3-d4 e7-f6 d4-e5 f6xd4 b4-c5 d6xb4 a3xe3 g5-h4 b2-c3 b6-a5 c3-d4 c7-b6 d4-c5 b6xd4 e3xc5 b8-c7 a1-b2 f8-e7",
        "c3-b4 f6-g5 e3-d4 g5-f4 g3xe5 d6xf4 b2-c3 b6-c5 d4xb6 a7xc5 b4xd6 c7xe5 c3-b4 g7-f6 a1-b2 h8-g7 b2-c3 f6-g5 b4-c5 g7-f6",
        "c3-b4 f6-g5 e3-d4 g5-f4 g3xe5 d6xf4 b2-c3 g7-f6 f2-g3 h8-g7 g3xe5 b6-c5 d4xb6 f6xb2 a1xc3 a7xc5 b4xd6 e7xc5 c3-d4 c5xe3",
        "c3-b4 f6-g5 e3-d4 g5-f4 g3xe5 d6xf4 f2-g3 e7-d6 g3xe5 d6xf4 g7-f6 b2-c3 f8-g7 f2-g3 f6-e5 d4xf6 g7xe5 d2-e3 f4xd2 c1xe3",
        "c3-b4 f6-g5 e3-d4 g5-f4 g3xe5 d6xf4 f2-g3 e7-d6 g3xe5 d6xf4 g7-f6 b4-c5 f6-g5 d2-e3 f4xd2 c1xe3 h8-g7 h2-g3 g5-h4 g3-f4",
        "c3-b4 f6-g5 e3-d4 g5-f4 g3xe5 d6xf4 f2-g3 e7-d6 g3xe5 d6xf4 g7-f6 b4-c5 f6-g5 d2-e3 f4xd2 c1xe3 h8-g7 h2-g3 g7-f6 g3-h4",
        "c3-b4 f6-g5 e3-d4 g5-h4 b2-c3 g7-f6 c3-d4 e7-d6 h6-g5 b2-c3 f6-e5 g3-f4 h8-g7 c3-b4 b6-c5 d2-e3 g7-h6 c1-d2 a7-b6 d2-c3",
        "c3-b4 f6-g5 e3-d4 g5-h4 b4-a5 h6-g5 b2-c3 e7-f6 a1-b2 f6-e5 d4xf6 g5xe7 c3-d4 g7-f6 b2-c3 b6-c5 d4xb6 a7xc5 c3-b4 h8-g7",
        "c3-b4 f6-g5 e3-d4 g5-h4 b4-a5 h6-g5 b2-c3 g7-h6 a1-b2 h8-g7 g5-f4 e3xg5 h4xf6 g3-h4 b6-c5 d4xb6 a7xc5 c3-d4 c5xe3 f2xd4",
        "c3-b4 f6-g5 g3-f4 b6-a5 b4-c5 d6xb4 a3xc5 g7-f6 b2-c3 h8-g7 c7-b6 a1-b2 d8-c7 d4-e5 b6xd4 e5xc3 e7-d6 f2-g3 a5-b4 c3xa5",
        "c3-b4 f6-g5 g3-f4 b6-c5 b2-c3 g7-f6 b4-a5 g5-h4 c3-b4 f6-g5 e7-f6 c3-d4 a7-b6 c1-d2 f6-e5 d4xf6 g5xe7 d2-c3 e7-f6 c3-d4",
        "c3-b4 f6-g5 g3-f4 b6-c5 b2-c3 g7-f6 c3-d4 g5-h4 d4xb6 c7xc3 d2xb4 f6-g5 b4-a5 h8-g7 a1-b2 d8-c7 h2-g3 d6-c5 a3-b4 c5xa3",
        "c3-b4 f6-g5 g3-f4 d6-c5 b4xd6 c7xg3 f2xf6 g7xe5 h2-g3 h8-g7 g7-f6 e3-f4 e7-d6 d2-e3 b6-a5 g3-h4 e5xg3 h4xf2 a7-b6 f2-g3",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 a1-b2 e5xg3 f2xf6 e7xg5 b6-a5 b4-c5 d6xb4 a3xc5 h8-g7 h2-g3 g5-h4 g3-f4 c7-d6 c5xe7",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 a1-b2 e5xg3 f2xf6 e7xg5 h2-g3 b6-c5 b4-a5 h8-g7 g3-f4 g7-f6 c3-d4 f8-e7 d4xb6 a7xc5",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 a1-b2 e5xg3 f2xf6 e7xg5 h2-g3 g5-h4 e3-f4 h4xf2 e1xg3 h8-g7 b4-a5 g7-f6 d2-e3 f6-g5",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 a1-b2 e5xg3 f2xf6 e7xg5 h8-g7 b4-a5 g5-f4 e3xg5 h6xf4 c3-d4 b6-c5 d4xb6 a7xc5 d2-e3",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 b4-a5 e5xg3 f2xf6 e7xg5 b6-c5 d2-c3 h8-g7 e1-f2 g5-f4 e3xg5 h6xf4 f2-g3 g7-h6 g3xe5",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 b4-a5 e5xg3 f2xf6 e7xg5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 g5-f4 e3xg5 h6xf4 c3-b4",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 f6-e5 b4-a5 e5xg3 f2xf6 e7xg5 c3-d4 b6-c5 d4xb6 a7xc5 h2-g3 g5-f4 g3xe5 d6xf4 e3xg5 h6xf4",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 b4-a5 b6-c5 c3-d4 h8-g7 d4xb6 a7xc5 a1-b2 b8-a7 h2-g3 f6-e5 b2-c3 h6-g5 f4xh6 e5-d4",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 g5-h4 b4-a5 f6-e5 a1-b2 e5xg3 h2xf4 h8-g7 e3-d4 e7-f6 f2-g3 h4xf2 g1xe3 d6-c5 e1-f2 h6-g5",
        "c3-b4 f6-g5 g3-f4 g7-f6 b2-c3 h8-g7 a1-b2 g5-h4 b4-c5 d6xb4 c3xa5 f6-g5 b2-c3 b6-c5 c3-d4 a7-b6 h2-g3 e7-f6 d4-e5 f6xd4",
        "c3-b4 f6-g5 g3-f4 g7-f6 b4-a5 f6-e5 b2-c3 e5xg3 f2xf6 e7xg5 h2-g3 b6-c5 g3-f4 h8-g7 a1-b2 g7-f6 c3-d4 f8-e7 d4xb6 a7xc5",
        "c3-b4 f6-g5 g3-f4 g7-f6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 c7-b6 d4-e5 b6xd4 e5xc3 h6-g5 h2-g3 h8-g7 c3-d4 e7-d6",
        "c3-b4 f6-g5 g3-f4 g7-f6 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 f8-g7 d2-e3 f6-e5 d4xf6 g7xe5 h2-g3 h6-g5 e3-d4 e5xc3",
        "c3-b4 f6-g5 g3-f4 g7-f6 h2-g3 g5-h4 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 h8-g7 b2-c3 c7-d6 c3-b4 d8-c7 d2-e3 d6-e5 f4xd6 c7xe5",
        "c3-b4 f6-g5 g3-h4 b6-a5 h4xf6 a5xc3 b2xd4 g7xc3 d2xb4 h6-g5 a1-b2 h8-g7 b4-a5 d6-c5 e1-d2 g5-h4 b2-c3 g7-f6 c3-d4 c7-b6",
        "c3-b4 f6-g5 g3-h4 b6-a5 h4xf6 a5xc3 b2xd4 g7xc3 d2xb4 h8-g7 h2-g3 a7-b6 b4-a5 g7-f6 a1-b2 b6-c5 g3-f4 f8-g7 c1-d2 f6-e5",
        "c3-b4 f6-g5 g3-h4 c5-d4 d2-e3 h8-g7 g7-f6 c7-b6 a7-b6 b4-a5 b6-c5 h2-g3 h6-g5 g3-h4 g5-f4 c1-d2 f8-g7 c3-b4 b8-c7 d2-c3",
        "c3-b4 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 f2-g3 e7-d6 g3xe5 d6xf4 g1-f2 d8-e7",
        "c3-b4 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 f6-g5 h4xf6 e7xg5 f2-e3 g5-h4 e3xg5 h4xf6 d2-e3 f6-g5 e1-f2",
        "c3-b4 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 h8-g7 f2-g3 a7-b6 g3xe5 f6xd4 a1-b2 e7-f6 e1-f2 d4-c3 b2xd4",
        "c3-b4 f6-g5 g3-h4 g5-f4 e3xg5 h6xf4 b4-a5 g7-f6 d2-c3 f6-g5 h4xf6 e7xg5 c3-b4 h8-g7 b2-c3 g7-f6 e1-d2 f4-e3 d2xh6 f6-g5",
        "c3-b4 f6-g5 h2-g3 e5-f4 c7-d6 c3-d4 d6-c5 b6-c5 g1-f2 f8-e7 f2-e3 e7-d6 b2-c3 d8-e7 c3-b4 e7-f6 a1-b2 f6-e5 b2-c3 h8-g7",
        "c3-b4 f6-g5 h4xf6 e7xg5 e3-d4 g5-h4 b4-c5 h4xf2 g1xe3 d6xb4 a3xc5 c7-d6 c5xe7 f8xd6 b2-c3 h6-g5 a1-b2 g7-f6 b2-a3 g5-h4",
        "c3-b4 f6-g5 h4xf6 g7xe5 e3-f4 h8-g7 b4-a5 g7-f6 b2-c3 f6-g5 a1-b2 g5xe3 d2xf4 b6-c5 c3-b4 e7-f6 e1-d2 f6-g5 b2-c3 g5xe3",
        "c3-b4 g3-f4 b2-c3 c3-d4 f6-g5 b6-c5 g7-f6 h8-g7 d4xb6 d2xb4 b4-a5 a1-b2 c7xc3 d8-c7 g5-h4 f6-e5 h2-g3 b2-c3 a3-b4 e3-d4",
        "c3-b4 g3-f4 b2xd4 d4xf6 b6-a5 a5xc3 f6-e5 g7xg3 h2xf4 a1-b2 b2-c3 e3-d4 h8-g7 g7-f6 a7-b6 f6-g5 d2-e3 f2-g3 c1-d2 g1-h2",
        "c3-b4 g3-f4 b4-c5 a3xc5 f6-g5 b6-a5 d6xb4 g7-f6 b2-c3 c3-d4 a1-b2 c5-b6 h8-g7 g5-h4 f6-g5 a7xc5 d4xb6 b6-a7 f4-e5 e3-d4",
        "c3-b4 g3-f4 b4-c5 e3xc5 f6-g5 g7-f6 b6xd4 d6xb4 a3xc5 f2xd4 e1-f2 d2-e3 g5xe3 c7-b6 h8-g7 b8-c7 h2-g3 c5xg5 b2-c3 a1-b2",
        "c3-b4 g3-f4 b4-c5 e3xc5 f6-g5 g7-f6 b6xd4 g5xe3 f2xd4 a3xc5 h2-g3 b2-a3 d6xb4 f6-g5 h8-g7 g7-f6 d2-e3 g3-f4 c5xe7 a1-b2",
        "c3-b4 g3-f4 b4xd6 f2xf6 f6-g5 d6-c5 c7xg3 g7xe5 h2-g3 e3-d4 b2xd4 a1-b2 h8-g7 e5xc3 g7-f6 e7-d6 b2-c3 e1-f2 f2xd4 a3-b4",
        "c3-b4 g3-h4 e3xg5 b4-a5 f6-e5 e5-f4 h6xf4 b6-c5 b2-c3 c3-b4 d2-c3 f2-e3 e7-f6 g7-h6 f8-g7 f4xd2 c1xe3 h4xf6 e3-f4 h2xf4",
        "c3-b4 g3-h4 e3xg5 b4-a5 f6-e5 e5-f4 h6xf4 g7-f6 b2-c3 h4xf6 c3-d4 d4xb6 f6-g5 e7xg5 b6-c5 a7xc5 a1-b2 b2-c3 c3-b4 f2-g3",
        "c3-b4 g3-h4 e3xg5 b4-a5 f6-e5 e5-f4 h6xf4 g7-f6 b2-c3 h4xf6 c3-d4 d4xb6 f6-g5 e7xg5 b6-c5 a7xc5 a1-b2 b2-c3 f2-e3 e1-f2",
        "c3-b4 g5-f4 b4-a5 f4-e3 d4-e5 e7-d6 g7-f6 e1-d2 f6-g5 d2-e3 g5-h4 g1-f2 h8-g7 h2-g3 g7-f6 g3-f4 b6-c5 f6-e5 f4-g5 e3-f4",
        "c3-b4 g5-f4 f2-g3 b6-a5 f6-e5 h2-g3 g7-f6 f2-e3 h8-g7 g3-h4 d8-e7 e3-f4 f6-e5 a1-b2 e7-d6 b2-c3 g7-h6 f2-e3 d6-c5 e1-f2",
        "c3-b4 g5-h4 b4-a5 a7-b6 b6-c5 h6-g5 b2-c3 g7-f6 a3-b4 h8-g7 a1-b2 f6-e5 b2-a3 g7-h6 b4-a5 d8-c7 c3-b4 e5-f4 d2-e3 g5-f4",
        "c3-b4 g5-h4 b4-a5 a7-b6 b6-c5 h6-g5 b2-c3 g7-f6 a3-b4 h8-g7 a1-b2 g7-h6 b2-a3 f6-e5 b4-a5 e5-f4 a5-b6 f4-e3 c3-d4 h6-g5",
        "c3-b4 g5-h4 b4-a5 h4xf2 a5xe5 a7-b6 e1xg3 b6-c5 d4xb6 f6xh4 g7-f6 b2-c3 f6-e5 c3-b4 h6-g5 a1-b2 h8-g7 b2-c3 d8-c7 b4-a5",
        "c3-b4 g5-h4 b4-c5 b6-a5 c3-d4 f6-g5 b2-c3 c7-b6 b6-c5 a3-b4 e7-d6 b4-a5 h8-g7 c3-d4 d6-c5 d2-c3 c5-b4 c1-b2 f8-e7 c3-d4",
        "c3-b4 g5-h4 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 e7-f6 d2-e3 d8-e7 a1-b2 e7-d6 c5xe7 f6xd8 e3-d4 a7-b6 c1-d2 h8-g7",
        "c3-b4 g5-h4 b4-c5 d6xb4 a5xc3 b6-c5 g3-f4 f6-g5 c3-d4 c7-b6 b6-a5 d4xb6 a5xc7 c3-d4 g7-f6 a3-b4 f6-e5 d4xf6 g5xe7 b4-a5",
        "c3-b4 g5-h4 b4-c5 f6-g5 d2-e3 c7-b6 a3-b4 g7-f6 b2-a3 h6-g5 g1-f2 d8-c7 c1-d2 c7-b6 d4-e5 g5-f4 b4-a5 h8-g7 a1-b2 d6-c5",
        "c3-b4 g5-h4 d2-e3 b6-c5 b2-c3 f6-e5 c3-d4 g7-f6 f8-e7 c3-b4 f6-e5 c1-b2 e7-f6 b2-c3 h8-g7 c3-d4 f6-g5 d2-c3 g5-f4 c3-b4",
        "c3-b4 g5-h4 d2-e3 b6-c5 b2-c3 f6-e5 c3-d4 g7-f6 h8-g7 c3-b4 f6-g5 g3-f4 g7-f6 e3-d4 a7-b6 d2-e3 f6-e5 b4-c5 a3-b4 c7-b6",
        "c3-b4 g5-h4 g3-f4 h4-g3 b4-a5 g3xc3 a5xe5 f6xf2 b2xd4 e7-d6 g1xe3 a7-b6 e3-f4 d6-c5 d2-e3 g7-f6 c1-d2 f6-g5 h2-g3 g5-h4",
        "c3-b4 g7-f6 b4-c5 f6-e5 b2-c3 c7-b6 g3-f4 f8-g7 g7-f6 b2-c3 h8-g7 c1-b2 g7-f6 d2-e3 d8-c7 e3-d4 c7-d6 f2-e3 a7-b6 g1-f2",
        "c3-b4 h6-g5 b2-c3 g5-h4 b4-a5 f6-e5 c3-b4 e5-f4 e3xg5 h4xf6 f6-e5 b4-c5 d6xb4 a5xc3 g7-f6 e3-f4 c7-d6 f2-e3 b6-a5 e3-d4",
        "c3-b4 h6-g5 b4-a5 g7-h6 a3-b4 d6-e5 b2-a3 g5-f4 e3xg5 h6xf4 b6-c5 b4xd6 e7xc5 c3-d4 e5xc3 g3xg7 h8xf6 c1-d2 c5-b4 a3xc5",
        "c3-b4 h6-g5 g3-f4 g7-h6 b2-c3 h8-g7 b4-a5 g5-h4 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 f6-e5 b2-c3 e5xg3 h2xf4 c5-b4 a3xc5 d6xb4",
        "c3-b4 h6-g5 g3-h4 b6-a5 b4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 c5xe3 d2xh6 b6-c5 h2-g3 b8-c7 f2-e3 c7-d6 b2-c3 c5-b4 e3-f4",
        "c3-b4 h6-g5 g3-h4 b6-a5 b4-c5 d6xb4 a3xc5 c7-b6 c5-d6 e7xc5 e3-d4 c5xe3 d2xh6 b6-c5 f2-e3 b8-c7 b2-c3 c5-b4 e1-d2 c7-d6",
        "c3-b4 h6-g5 g3-h4 b6-a5 b4-c5 d6xb4 a3xc5 c7-b6 e3-d4 g5-f4 f6-g5 h4xf6 g7xc3 b2xd4 b8-c7 e3xg5 c7-d6 a1-b2 d6xb4 b2-c3",
        "c3-b4 h6-g5 g3-h4 b6-a5 f2-g3 a5xc3 d2xb4 g7-h6 b2-c3 d6-e5 b4-a5 f8-g7 c3-d4 e5xc3 g3-f4 a7-b6 a3-b4 c3-d2 e1xc3 e7-d6",
        "c3-b4 h6-g5 g3-h4 b6-a5 h2-g3 a5xc3 d2xb4 d6-e5 b4-a5 e5-d4 e3xc5 g5-f4 g3xe5 f6xb6 a3-b4 g7-f6 f2-e3 h8-g7 e1-f2 g7-h6",
        "c3-b4 h6-g5 g3-h4 d6-e5 b4-a5 e7-d6 b2-c3 f8-e7 c3-d4 e5xc3 d2xb4 d6-e5 e3-f4 g5xe3 f2xd4 e5xc3 b4xd2 b6-c5 d2-e3 c7-d6",
        "c3-b4 h6-g5 g3-h4 g5-f4 f2-g3 b6-c5 g3xe5 f6xd4 h4-g5 g7-f6 g5-h6 f6-e5 h2-g3 h8-g7 g1-h2 a7-b6 d2-c3 g7-f6 g3-h4 d4-e3",
        "c3-b4 h6-g5 g3-h4 g7-h6 b4-a5 d6-e5 e3-d4 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 h2-g3 e7-d6 d2-e3 f8-g7 e1-d2 b8-a7 g3-f4 d8-e7",
        "c3-b4 h6-g5 g3-h4 g7-h6 b4-a5 g5-f4 e3xg5 h6xf4 b2-c3 h8-g7 b6-c5 f2-g3 a7-b6 g3xe5 d6xf4 b4xd6 e7xc5 e1-f2 d8-e7 a1-b2",
        "c3-b4 h6-g5 g3-h4 g7-h6 f2-g3 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6 d6xb4 a3xc5 b8-c7 a1-b2 c7-b6 e3-d4 f6-e5 d4xf6 b6xd4 g1-f2",
        "c3-b4 h8-g7 g3-f4 g5-h4 b4-c5 f6-g5 g7-f6 f2-g3 c7-d6 c3-b4 d8-c7 b4-a5 a7-b6 h2-g3 b6-a5 a1-b2 c7-d6 c3-d4 b8-a7 b2-c3",
        // --- g3-h4 (357 linhas de campeonato) ---
        "g3-h4 e5-d4 h4-g5 h8-g7 g5-h6 g7-f6",
        "g3-h4 f6-e5 e3-d4 e7-f6 d2-e3 h6-g5 h2-g3",
        "g3-h4 f6-e5 h2-g3 e5-d4 e3xc5 b6xd4 c3xe5 d6xh2",
        "g3-h4 f6-g5 f2-g3 h8-g7 e3-f4 g7-f6 c3-b4 f6-g5",
        "g3-h4 g7-h6 e3-c1 f8-g7 c1-a3 c3-d2 h4-g5 h6xd6 a3xc1",
        "g3-h4 b6-a5 f2-g3 a7-b6 f4-g5 g7-h6 g1-f2 f2-g3 b6-c5 h4-g5 c3-b4",
        "g3-h4 b6-c5 d2-e3 a7-b6 c3-b4 f8-e7 h2-g3 g5-f4 g3xe5 d6xd2 b4xf8",
        "g3-h4 g7-h6 f2-g3 h2-g3 a7-b6 f8-g7 c1-d2 g7-h6 d2-e3 a5-b4 c7-b6",
        "g3-h4 d6-c5 h2-g3 c5xe3 d2xf4 g5xe3 f2xd4 e7-d6 c3-b4 f6-g5 h4xf6 g7xa5",
        "g3-h4 f6-e5 g1-h2 g7-f6 f2-g3 b6-c5 c3-d4 e5xc3 b2xb6 a7xc5 a1-b2 f6-g5",
        "g3-h4 g5-f4 e3xc5 b6xd4 c3xe5 a7-b6 a3-b4 f8-e7 b2-a3 e7-d6 h6xf4 e5xg3",
        "g3-h4 d6-e5 h4-g5 h6xf4 e3xg5 f6xh4 d4xh8 c7-d6 c3-b4 b6-c5 d8-c7 d2-e3 a7-b6",
        "g3-h4 f6-g5 b4-c5 e7-d6 c3-d4 h8-g7 a1-b2 c7-b6 b2-c3 b8-a7 f2-g3 d4-e5 b6-c5",
        "g3-h4 b6-a5 f2-g3 c7-b6 c3-d4 d6-c5 b2-c3 c5-b4 a3xc5 f6-g5 h4xf6 g7xe5 d4xf6 b6xh4",
        "g3-h4 g7-h6 f2-e3 d6-e5 c1-b2 b8-c7 c7-d6 g5-h6 b6-c5 f2-e3 c5-b4 h2-g3 b4-a3 e3-f4",
        "g3-h4 b6-a5 b4-c5 d6xb4 a3xc5 c7-b6 c3-d4 h6-g5 c5-d6 e7xc5 f6xd4 h4xh8 a5-b4 h8xc7 d8xb6",
        "g3-h4 b6-a5 f4-g5 d6-e5 g5-h6 a7-b6 d2-e3 b8-c7 c7-d6 b2-a3 b6-c5 c1-b2 e5-f4 d8-c7 f2-g3",
        "g3-h4 d2-e3 d6-e5 c1-d2 d8-e7 c3-b4 e5-f4 b2-c3 c7-d6 c3-d4 f4-g3 b4-c5 b8-c7 a1-b2 g7-h6",
        "g3-h4 d6-e5 h2-g3 a7-b6 g1-h2 b6-a5 d4-c5 e5-d4 c3xe5 f6xb6 b6-c5 d2-c3 c5-b4 e1-d2 c7-b6",
        "g3-h4 b6-c5 e3-f4 a7-b6 f2-e3 d6-e5 f4xd6 c7xe5 b4xf4 b8-a7 f6-e5 f4xd6 e7xc5 c3-b4 a5xc3 d2xd6",
        "g3-h4 d2-e3 b6-a5 c1-d2 d8-e7 c3-d4 g7-f6 d6-e5 e1-d2 h6-g5 d4-c5 h8-g7 c5-b6 e3-f4 c3-b4 e1-d2",
        "g3-h4 f6-g5 b2-c3 g7-f6 c3-d4 g5-h4 f8-e7 a1-b2 h8-g7 d2-e3 f6-e5 b2-c3 c7-b6 c5-d4 e7-d6 f2-e3 b2-a1",
        "g3-h4 b6-a5 c3-d4 c7-b6 b2-c3 c5-b4 h2-g3 b8-c7 b4-a3 f2-g3 c7-d6 f4-g5 b6-c5 g1-h2 c7-b6 c3-d4 d6-e5 g3-f4",
        "g3-h4 b6-c5 b2-c3 a7-b6 c3-b4 b6-a5 g5-h6 e5-d4 f2-e3 f6-e5 b4-a5 e5-d4 e3-f4 d4-c3 c1-b2 c5-d4 a3-b4 c7-b6",
        "g3-h4 d6-c5 a3-b4 d4-e5 h6-g5 h8-g7 a1-b2 g7-f6 b2-c3 f6-g5 c3-b4 e7-f6 c1-d2 c7-d6 d2-c3 f6-e5 c3-b4 e5-d4",
        "g3-h4 g7-f6 h2-g3 f6-g5 h4xf6 e7xg5 g3-h4 f8-e7 h4xf6 e7xg5 b2-a3 d6-e5 a3xc5 b6xb2 a1xc3 g5-f4 e3xg5 h6xf4",
        "g3-h4 h6-g5 f2-g3 g7-h6 g3-f4 b6-c5 h2-g3 c7-b6 g1-h2 b8-c7 f6-e5 h4xd4 f8-g7 f4-g5 h6xf4 g3xe5 d6xf4 b4xh6",
        "g3-h4 b6-a5 d4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 g5-f4 f6-e5 h4-g5 d8-c7 g5xe3 h6-g5 e3-f4 g5xe3 f2xb6 a5xc7",
        "g3-h4 b6-a5 g5-h6 c7-d6 f2-e3 a7-b6 h2-g3 d6-c5 b2-c3 b6-a5 e1-d2 d8-c7 g1-h2 c7-d6 e3-f4 f6-e5 f4-g5 c5-d4 g5-f6",
        "g3-h4 g7-h6 f2-e3 d6-e5 c3-d4 b8-c7 a1-b2 c7-d6 b2-c3 d6-c5 e1-f2 b6-c5 d2-e3 c5-d4 h8-g7 e3-d4 g7-f6 g1-f2 d8-c7",
        "g3-h4 h6-g5 b4-c5 b6xd4 e3xc5 c7-d6 f2-e3 d6xb4 a3xc5 d8-c7 c7-d6 d4-e5 f6xb6 h4xd8 b6-a5 c3-b4 a5xc3 d2xb4 g7-h6",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b6-a5 g1-f2 a7-b6 f2-e3 b8-a7 e3-f4 b6-c5 f4-e5 d6xh6 c3-b4 a5xc3 d2xb8",
        "g3-h4 a7-b6 d4-c5 b6xd4 e3xc5 d6xb4 c3xa5 f6-g5 h4xf6 g7xe5 h8-g7 f2-e3 h6-g5 g3-h4 e7-f6 b2-c3 g7-h6 g1-h2 e5-f4 c3-d4",
        "g3-h4 a7-b6 g5-h6 b6-a5 f2-e3 f6-e5 e3-f4 g7-f6 h2-g3 f6-e5 g3-h4 h8-g7 f2-e3 g7-f6 g1-h2 c7-b6 h2-g3 b8-a7 e3-f4 b6-c5",
        "g3-h4 a7-b6 g5-h6 b6-a5 f2-e3 f6-e5 g1-f2 g7-f6 c7-b6 e3-f4 b6-c5 c3-b4 b8-a7 f4-g5 c1-b2 g3-f4 b6-a7 e7-f6 h2-g3 d8-c7",
        "g3-h4 a7-b6 g5-h6 b6-c5 f2-e3 f6-e5 h2-g3 g7-f6 h8-g7 g1-h2 c5-b4 g3-f4 b4-a3 f2-e3 f6-e5 h2-g3 g7-f6 b2-c3 e7-d6 g3-h4",
        "g3-h4 b6-a5 a3-b4 c7-b6 b4-c5 f6-g5 d8-c7 e3-f4 h8-g7 f2-g3 c7-d6 d4-e5 g7-f6 b2-c3 f8-g7 g3-h4 g7-f6 a1-b2 b6-c5 b2-a3",
        "g3-h4 b6-a5 a3-b4 c7-b6 b4-c5 h6-g5 e3-f4 f6-e5 e7-f6 f2-e3 f6-g5 e3-f4 h8-g7 e1-f2 f8-e7 b2-a3 c7-d6 c1-d2 a5-b4 f2-e3",
        "g3-h4 b6-a5 a3-b4 c7-b6 b4-c5 h6-g5 e3-f4 g7-h6 h8-g7 f4-e5 a5-b4 g7-f6 b2-c3 e7-d6 a1-b2 a7-b6 b2-a3 b6-a5 e3-f4 f8-e7",
        "g3-h4 b6-a5 a3-b4 f6-g5 h4xf6 e7xg5 b2-a3 g7-f6 a1-b2 c7-b6 d8-c7 e3-f4 g5xe3 d2xf4 h8-g7 f4-e5 c7-d6 c5xg5 h6xd6 d4-e5",
        "g3-h4 b6-a5 a3-b4 f6-g5 h4xf6 e7xg5 b4-c5 c7-b6 e3-f4 g5xe3 d2xf4 d8-e7 c1-d2 b8-c7 b2-a3 c7-d6 a1-b2 d6xb4 a3xc5 e7-d6",
        "g3-h4 b6-a5 b2-c3 a7-b6 g5-h6 e5-f4 c3-b4 f4-g3 d6-c5 a1-b2 e7-d6 c1-d2 d8-c7 b2-c3 g3-h2 d2-e3 b6-c5 c3-b4 h8-g7 e3-f4",
        "g3-h4 b6-a5 b2-c3 c5-b4 f2-e3 g7-h6 b4-a3 f2-e3 d8-c7 h2-g3 c7-d6 g5-h6 a7-b6 g3-f4 b8-a7 f4-g5 d6-e5 e3-d4 b6-c5 d2-e3",
        "g3-h4 b6-a5 b4-c5 c7-b6 c3-b4 h6-g5 g5-f4 f2-e3 g7-h6 d2-c3 b8-c7 e1-d2 f6-g5 d2-e3 h8-g7 b2-c3 g7-f6 e1-f2 g5-h4 a1-b2",
        "g3-h4 b6-a5 b4-c5 d6xb4 a3xc5 b8-a7 c3-b4 a5xc3 d2xb4 f6-e5 g7-f6 e1-d2 h6-g5 a1-b2 e5-f4 f2-g3 c7-b6 g3xg7 b6xf2 g1xe3",
        "g3-h4 b6-a5 c1-d2 d6-e5 f2-g3 g5-f4 d4-c5 c7-d6 d8-c7 c5-b6 f4-e3 f2-e3 c7-d6 g3-f4 d6-c5 e1-d2 a7-b6 b2-a3 b8-a7 f4-g5",
        "g3-h4 b6-a5 c3-b4 a5xc3 b2xb6 c7xa5 a1-b2 a7-b6 b2-c3 b8-a7 d6-c5 c3-b4 a5xc3 d2xd6 e7xc5 e1-d2 f6-e5 g3-f4 e5xg3 h4xf2",
        "g3-h4 b6-a5 c3-d4 d6-e5 b2-c3 e5-f4 e3xg5 h6xf4 d4-c5 f6-e5 c5-d6 e7xc5 h4-g5 f4xh6 c3-b4 a5xc3 d2xf4 g7-f6 a1-b2 a7-b6",
        "g3-h4 b6-a5 c3-d4 d6-e5 h6-g5 c1-b2 e7-d6 d6-c5 a1-b2 h8-g7 b2-c3 d8-c7 e3-d4 g7-f6 a3-b4 f8-e7 e1-f2 b8-a7 f2-e3 f6-g5",
        "g3-h4 b6-a5 c3-d4 f6-g5 h4xf6 g7xc3 b2xd4 h6-g5 h2-g3 g5-h4 a1-b2 h8-g7 g3-f4 g7-h6 g1-h2 d6-c5 d4xb6 a7xc5 b2-c3 c7-d6",
        "g3-h4 b6-a5 c3-d4 f6-g5 h4xf6 g7xc3 d2xb4 a5xc3 b2xd4 a7-b6 h8-g7 g3-f4 b6-a5 a1-b2 a5-b4 a3xc5 d6xb4 e1-d2 b4-a3 d4-c5",
        "g3-h4 b6-a5 e3-d4 d6-e5 b4-c5 e5-f4 f2-e3 c7-d6 g1-h2 d6xb4 a3xc5 e7-d6 c5xe7 f8xd6 d4-c5 d6xb4 b2-a3 d8-c7 a3xc5 c7-d6",
        "g3-h4 b6-a5 e3-d4 d6-e5 b4-c5 g5-f4 c5-b6 f4-e3 a7-b6 d2-e3 c7-d6 a3-b4 f6-e5 f2-g3 b6-c5 b2-a3 e5-d4 e3-f4 g1-h2 d8-c7",
        "g3-h4 b6-a5 e3-f4 d6-e5 f4xd6 e7xe3 d2xf4 a7-b6 f2-g3 f6-e5 f4xd6 c7xe5 c3-d4 e5xc3 b2xd4 g7-f6 d4-e5 f6xd4 h4-g5 h6xf4",
        "g3-h4 b6-a5 e3-f4 d6-e5 f4xd6 e7xe3 d2xf4 c7-d6 f2-e3 d8-e7 a7-b6 b2-c3 b6-c5 d4xb6 a5xc7 h2-g3 c7-b6 c3-d4 b6-a5 e1-d2",
        "g3-h4 b6-a5 f2-e3 a7-b6 g5-h6 b6-c5 c3-d4 a5-b4 b2-c3 b8-a7 g1-f2 d6-c5 c3-d4 e7-d6 a1-b2 d6-e5 e3-f4 f6-e5 f2-g3 d8-c7",
        "g3-h4 b6-a5 f2-g3 a7-b6 g1-f2 b8-a7 c3-b4 a5xc3 d2xb4 f6-g5 h4xf6 g7xe5 c1-d2 h8-g7 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 f6-e5",
        "g3-h4 b6-a5 f2-g3 a7-b6 g1-f2 d6-c5 c3-d4 c7-d6 b2-c3 b8-a7 g3-f4 c5-b4 a3xc5 d6xb4 d4-e5 f6xb2 c1xc5 b6xd4 e3xc5 d8-c7",
        "g3-h4 b6-a5 f4-g5 g7-h6 f2-e3 a7-b6 h8-g7 a3-b4 b6-c5 b2-a3 c5-d4 e1-d2 g7-f6 d2-e3 c7-b6 a1-b2 b6-c5 b2-c3 d8-e7 c3-b4",
        "g3-h4 b6-a5 g5-h6 a7-b6 c3-d4 b8-a7 b2-c3 d6-c5 b6-c5 d2-e3 f6-e5 e3-f4 c7-d6 c3-d4 d6-c5 c1-d2 h8-g7 e1-f2 c7-d6 b2-c3",
        "g3-h4 b6-a5 g5-h6 a7-b6 h2-g3 b6-c5 b2-c3 c5-d4 c7-b6 f2-e3 b8-a7 g3-f4 h8-g7 h2-g3 f6-e5 g3-h4 g7-f6 f2-g3 b6-c5 c1-b2",
        "g3-h4 b6-a5 g5-h6 d6-e5 b2-c3 e5-d4 a7-b6 b2-c3 g7-f6 f2-e3 f6-e5 e3-f4 c5-d4 h2-g3 b6-c5 g3-f4 h8-g7 f2-g3 e7-d6 g1-f2",
        "g3-h4 b6-a5 g5-h6 d6-e5 f2-e3 e5-d4 b2-c3 a7-b6 h2-g3 e7-d6 c3-b4 f6-e5 c1-d2 b6-a5 g3-f4 d8-c7 f2-g3 g7-f6 g3-h4 f6-e5",
        "g3-h4 b6-a5 g5-h6 f6-e5 f2-e3 b8-c7 e3-f4 g7-f6 h2-g3 f6-e5 g3-h4 h8-g7 f2-e3 g7-f6 e3-f4 f6-e5 b2-c3 c7-b6 f2-g3 c5-b4",
        "g3-h4 b6-a5 g5-h6 f6-e5 f2-e3 c7-b6 h2-g3 g7-f6 b8-a7 g3-f4 h8-g7 h2-g3 f6-e5 g3-h4 g7-f6 f2-g3 b6-c5 g3-f4 c5-b4 f2-g3",
        "g3-h4 b6-a5 h2-g3 a7-b6 e3-d4 b6-c5 d4xb6 a5xc7 c3-d4 g5-f4 g3xe5 d6xf4 b2-c3 f6-g5 h4xf6 e7xg5 d2-e3 f4xd2 c1xe3 g5-f4",
        "g3-h4 b6-a5 h2-g3 a7-b6 e3-f4 d6-c5 c3-b4 a5xc3 d2xd6 e7xc5 g1-h2 f8-e7 f4-e5 f6xd4 h4-g5 h6xf4 g3xc3 g7-f6 c1-d2 h8-g7",
        "g3-h4 b6-a5 h2-g3 a7-b6 e3-f4 f6-g5 h4xf6 e7xe3 d2xf4 g7-f6 g3-h4 f8-e7 f2-e3 f6-g5 h4xf6 e7xg5 c3-d4 h8-g7 d4-e5 g5-h4",
        "g3-h4 b6-a5 h2-g3 c7-b6 g3-f4 b6-c5 c3-d4 d6-c5 b2-c3 a7-b6 a1-b2 f6-e5 c3-d4 g7-f6 b2-c3 h6-g5 f2-g3 f6-e5 h4-g5 c5-b4",
        "g3-h4 b6-a5 h2-g3 f6-e5 e3-d4 d2-e3 e5-d4 h8-g7 e3-f4 a7-b6 b2-c3 e7-f6 g1-h2 c7-d6 f4-g5 d8-e7 g3-f4 b8-a7 h2-g3 f6-e5",
        "g3-h4 b6-a5 h2-g3 f6-e5 e3-d4 g7-f6 d2-e3 c7-b6 e3-f4 b6-c5 d4xb6 a5xc7 f2-e3 a7-b6 g1-h2 b6-a5 c1-d2 b8-a7 f4-g5 h6xf4",
        "g3-h4 b6-a5 h2-g3 f6-e5 e3-d4 g7-f6 d2-e3 c7-b6 e3-f4 b6-c5 d4xb6 a5xc7 f2-e3 a7-b6 g1-h2 b6-a5 c1-d2 f8-g7 c3-b4 a5xc3",
        "g3-h4 b6-a5 h2-g3 h6-g5 g3-f4 g7-h6 d4-e5 f2-e3 c7-d6 g1-h2 f6-g5 h2-g3 g5-h4 c3-d4 a7-b6 d4-e5 f8-e7 b2-c3 b8-c7 a1-b2",
        "g3-h4 b6-c5 b2-a3 c5-b4 e3-d4 b4-a3 e7-d6 g1-f2 c7-b6 f2-g3 d8-e7 a1-b2 b8-a7 e1-f2 b6-c5 e3-f4 a7-b6 c3-d4 d6-c5 d2-e3",
        "g3-h4 b6-c5 b2-a3 c5-b4 e3-d4 b8-a7 b4-a3 g3-f4 c7-d6 a1-b2 d8-c7 d2-e3 c7-b6 e1-d2 b6-c5 e3-d4 f6-g5 c3-d4 f8-e7 b2-c3",
        "g3-h4 b6-c5 c3-b4 a1-b2 a7-b6 b2-c3 b6-c5 b8-c7 f2-e3 c7-b6 c1-d2 f6-e5 d2-c3 b6-a5 g1-f2 g7-f6 f2-g3 d8-c7 c3-d4 c5-b4",
        "g3-h4 b6-c5 c3-b4 a1-b2 d6-e5 e1-d2 b8-a7 e5-d4 f2-g3 g7-f6 g1-f2 f6-e5 d2-c3 c7-b6 c1-d2 h8-g7 f2-e3 c5-d4 g7-f6 d2-e3",
        "g3-h4 b6-c5 c3-b4 a1-b2 d6-e5 g5-h6 e5-d4 f6-e5 g3-f4 g7-f6 b2-c3 f6-e5 c3-d4 c1-d2 c7-b6 d2-c3 b6-a5 f2-g3 h8-g7 e1-d2",
        "g3-h4 b6-c5 c3-b4 a1-b2 d6-e5 h2-g3 a5-b4 e5-f4 b2-c3 f6-g5 d2-e3 e5-f4 e7-f6 d8-e7 f2-e3 h8-g7 c3-d4 e7-d6 e3-f4 g7-f6",
        "g3-h4 b6-c5 c3-b4 a5xc3 b2xb6 a7xc5 a1-b2 d6-e5 d2-c3 e7-d6 e1-d2 b8-a7 e3-d4 c5xe3 f2xd4 c7-b6 g1-f2 b6-a5 d4-c5 d6xb4",
        "g3-h4 b6-c5 c3-b4 a5xc3 b2xb6 a7xc5 d2-c3 c5-d4 e3xc5 d6xd2 c1xe3 c7-b6 a1-b2 e7-d6 b2-c3 b6-a5 e3-d4 d8-c7 f2-e3 c7-b6",
        "g3-h4 b6-c5 c3-b4 a5xc3 b2xb6 a7xc5 f2-g3 f6-g5 h4xf6 g7xe5 e5-d4 e1-f2 d6-e5 f2-g3 d4xf2 g3xe1 h8-g7 h2-g3 e5-f4 g3xe5",
        "g3-h4 b6-c5 c3-b4 a5xc3 d2xd6 e7xc5 b2-c3 c7-d6 c3-b4 f6-g5 h4xf6 g7xe5 h2-g3 h8-g7 a1-b2 g7-f6 b2-c3 a7-b6 b4-a5 f8-e7",
        "g3-h4 b6-c5 c3-b4 e1-d2 d6-e5 h2-g3 c5-d4 e5-f4 a1-b2 g7-f6 b2-c3 b6-a5 f2-e3 c7-b6 g1-f2 d8-c7 e3-d4 c7-d6 d2-e3 b6-c5",
        "g3-h4 b6-c5 c3-b4 f6-e5 b4-a5 g7-f6 f2-g3 e5-d4 d6-e5 d2-e3 e5-d4 a1-b2 f6-e5 h2-g3 c7-d6 e1-d2 h8-g7 b2-c3 g7-f6 c3-b4",
        "g3-h4 b6-c5 c3-b4 g7-f6 f4-g5 h8-g7 g5-h6 f6-e5 g7-f6 b4-a5 c7-b6 e1-d2 b8-c7 b2-c3 c5-d4 c7-b6 d2-e3 b6-a5 c1-b2 a7-b6",
        "g3-h4 b6-c5 c3-b4 g7-h6 f2-g3 h2-g3 h8-g7 e1-f2 g7-h6 f2-e3 f6-e5 g3-f4 e7-f6 a1-b2 a7-b6 b4-a5 f6-e5 b2-c3 e5-f4 c1-d2",
        "g3-h4 b6-c5 c3-d4 a7-b6 f2-g3 b6-c5 c7-b6 b2-c3 d8-c7 a1-b2 b6-a5 g1-f2 c7-b6 f2-e3 d6-c5 g3-f4 b8-c7 e1-f2 c7-d6 h2-g3",
        "g3-h4 b6-c5 c3-d4 c7-b6 b2-c3 c5-b4 a3xc5 d6xb4 f2-g3 b4-a3 g1-h2 b6-c5 d4xb6 a5xc7 a1-b2 a7-b6 e3-f4 b6-a5 f4-g5 c7-d6",
        "g3-h4 b6-c5 c3-d4 d6-c5 e3-d4 a7-b6 b6-a5 e3-f4 c7-d6 e1-d2 d6-c5 d2-e3 f6-e5 f2-g3 g7-f6 b2-c3 b8-c7 e3-f4 c7-d6 a1-b2",
        "g3-h4 b6-c5 c3-d4 f6-e5 d4xf6 e7xg5 h4xf6 g7xe5 b2-c3 f8-g7 a7-b6 b4-a5 d8-e7 e3-f4 e5xg3 h2xf4 e7-f6 a1-b2 f6-e5 f2-g3",
        "g3-h4 b6-c5 c3-d4 f6-e5 d4xf6 e7xg5 h4xf6 g7xe5 e3-d4 c5xe3 f2xf6 f8-g7 d2-e3 g7xe5 h2-g3 e5-f4 g3xe5 d6xd2 c1xe3 c7-d6",
        "g3-h4 b6-c5 c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 e5-f4 e3xg5 h6xf4 h8-g7 b4-a5 g7-f6 a1-b2 f8-g7 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4",
        "g3-h4 b6-c5 c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 e5-f4 e3xg5 h6xf4 h8-g7 b4-a5 g7-f6 a1-b2 f8-g7 f2-e3 g7-h6 e3xg5 h6xf4 b2-c3",
        "g3-h4 b6-c5 c3-d4 g5-f4 d4xb6 c7xc3 d2xb4 f4xd2 c1xe3 d6-e5 e5-d4 h4-g5 h6xd2 c5xc1 f6-e5 a3-b4 g7-f6 b2-c3 h8-g7 b4-c5",
        "g3-h4 b6-c5 d4xb6 a7xc5 b2-a3 c5-b4 a3xc5 d6xb4 e3-d4 c7-d6 f2-g3 b8-a7 d4-c5 b4-a3 c3-b4 a5xc3 d2xb4 h6-g5 e1-d2 g5-f4",
        "g3-h4 b6-c5 d4xb6 a7xc5 c3-d4 c7-b6 d4-e5 f6xd4 a3-b4 c5xa3 e3xa7 e7-d6 b2-c3 f8-e7 d2-e3 g7-f6 c3-d4 h6-g5 a1-b2 d8-c7",
        "g3-h4 b6-c5 d4xb6 a7xc5 f2-g3 c5-d4 e3xc5 d6xb4 b2-a3 h6-g5 a3xc5 g5-f4 g3xe5 f6xb6 a1-b2 b6-c5 e1-f2 g7-f6 f2-e3 c7-d6",
        "g3-h4 b6-c5 e3-f4 c5-d4 c3xe5 a5xc3 d2xb4 f6xd4 f2-g3 d6-e5 f4xd6 e7xc5 b4xd6 c7xe5 c1-b2 g7-f6 e1-d2 f8-e7 b2-c3 d4xb2",
        "g3-h4 b6-c5 h2-g3 c5-b4 a3xc5 d6xb4 g3-f4 b4-a3 f4-g5 g7-h6 h6xf4 e3xg5 c7-d6 g5-h6 h8-g7 f2-e3 f6-e5 e3-d4 g7-f6 h4-g5",
        "g3-h4 b6-c5 h2-g3 c7-b6 e3-f4 f6-g5 g7-f6 d8-e7 f4-g5 b8-c7 e1-d2 c5-b4 b2-c3 c7-d6 f2-e3 h8-g7 g1-h2 d6-e5 e3-f4 b4-a3",
        "g3-h4 b8-c7 d4-c5 f6-e5 b2-c3 e7-d6 g7-f6 d2-e3 d8-e7 b4-c5 e5-f4 c3-d4 f4-g3 c1-b2 c7-b6 b2-c3 h8-g7 a1-b2 b6-c5 c3-d4",
        "g3-h4 b8-c7 g5-h6 b6-a5 f2-e3 f6-e5 e3-f4 g7-f6 h2-g3 f6-e5 g3-h4 h8-g7 h4-g5 c7-b6 f2-g3 g7-f6 g3-h4 c5-b4 g1-f2 b4-a3",
        "g3-h4 b8-c7 g5-h6 b6-a5 h2-g3 d6-e5 f2-e3 c5-d4 e5-f4 b2-c3 g7-f6 g1-f2 c7-d6 f2-e3 b6-c5 c3-b4 f6-e5 a1-b2 e5-d4 e1-f2",
        "g3-h4 b8-c7 g5-h6 b6-c5 c3-b4 c5-b4 f2-e3 b4-a3 b2-c3 c7-b6 e1-f2 f6-e5 f2-g3 g7-f6 g3-f4 f6-e5 e3-d4 e7-f6 f2-g3 b6-a5",
        "g3-h4 b8-c7 g5-h6 b6-c5 h2-g3 e5-f4 c7-d6 c3-b4 f4-g3 b4-a5 g3-h2 a1-b2 d8-c7 d2-e3 f6-e5 e1-d2 g7-f6 b2-c3 c5-b4 e3-d4",
        "g3-h4 b8-c7 g5-h6 f6-e5 f2-e3 g7-f6 e3-f4 f6-e5 c3-d4 h8-g7 a1-b2 b6-a5 b2-c3 c7-b6 f2-e3 g7-f6 h2-g3 b6-c5 g3-h4 c7-b6",
        "g3-h4 b8-c7 g5-h6 f6-e5 f2-e3 g7-f6 h2-g3 b6-a5 h8-g7 g1-h2 c7-b6 h2-g3 f6-e5 g3-h4 g7-f6 f2-g3 b6-c5 c3-b4 g3-f4 d6-e5",
        "g3-h4 c7-d6 c3-d4 b6-a5 b2-c3 a7-b6 f4-g5 d6-e5 b6-c5 f2-e3 c7-b6 h2-g3 b6-a5 g1-h2 b8-a7 g3-f4 f6-e5 f2-g3 g7-f6 g3-h4",
        "g3-h4 c7-d6 f2-g3 b8-c7 g3-f4 f6-e5 h2-g3 b6-c5 c3-d4 e5xc3 b2xb6 a7xc5 a1-b2 c5-b4 a3xc5 d6xb4 g1-h2 b4-a3 b2-c3 c7-b6",
        "g3-h4 c7-d6 h2-g3 b8-c7 c3-b4 b6-a5 c1-d2 f6-g5 e3-f4 c7-b6 b4-a5 h8-g7 b2-c3 a7-b6 c3-d4 f8-e7 g1-f2 e7-d6 a1-b2 b8-a7",
        "g3-h4 d2-e3 d6-e5 a3-b4 g7-f6 b2-a3 h8-g7 h6-g5 b4-c5 g7-h6 f2-g3 c5-d6 b6-a5 a3-b4 c7-b6 d6-e7 f4-g3 g5-h4 f2-g3 d8-e7",
        "g3-h4 d2xb4 a3xa7 h6xd2 e1xc3 c7-b6 a7xc5 d6xd2 c1xe3 e7-d6 b8-a7 e3-f4 d6-c5 g1-f2 a7-b6 b2-c3 b6-a5 a1-b2 d8-c7 f4-g5",
        "g3-h4 d2xb4 a3xa7 h6xd2 e1xc3 c7-b6 a7xc5 d6xd2 c1xe3 g7-h6 b8-a7 a1-b2 d8-c7 b2-a3 f8-g7 e3-f4 e7-d6 f2-e3 c7-b6 c3-b4",
        "g3-h4 d6-c5 a3-b4 d4-e5 h6-g5 h8-g7 a1-b2 g7-f6 b2-c3 f6-g5 d4-c5 e7-f6 d2-e3 d8-e7 c3-b4 e7-d6 b4-a5 f8-e7 e1-d2 e7-f6",
        "g3-h4 d6-c5 c3-b4 b6-a5 a1-b2 b8-c7 c7-b6 a3-b4 h6-g5 b4-c5 e7-d6 d4-e5 g5-f4 h8-g7 g5-h6 g7-f6 d2-c3 d8-e7 e1-d2 d6-c5",
        "g3-h4 d6-c5 c3-b4 b6-a5 b2-c3 a7-b6 f6-e5 b4-a5 b6-c5 e3-d4 c1-b2 d8-c7 c3-b4 e5-d4 b2-c3 g7-f6 b4-c5 b8-a7 f2-e3 c7-d6",
        "g3-h4 d6-c5 c3-b4 b6-a5 b4xd6 e7xc5 b2-c3 c7-b6 c3-b4 a5xc3 d2xd6 f6-g5 h4xf6 g7xc7 a1-b2 h8-g7 b2-c3 g7-f6 h2-g3 b6-a5",
        "g3-h4 d6-c5 c3-b4 b6-a5 b8-c7 e3-f4 c7-b6 b6-c5 b2-c3 e7-d6 c3-d4 d6-c5 f2-e3 c7-b6 d2-c3 f8-e7 c1-d2 d8-c7 c3-d4 c7-d6",
        "g3-h4 d6-c5 c3-b4 b6-a5 d4-c5 b8-a7 f6-e5 b2-c3 g7-f6 e3-d4 h6-g5 c5-d6 g5-f4 d6-e7 f2-e3 h8-g7 g5-h6 g7-f6 h4-g5 h6-g7",
        "g3-h4 d6-c5 c3-b4 b6-a5 f8-g7 c1-b2 f6-g5 h6-g5 d4-e5 h8-g7 a1-b2 e7-d6 b2-c3 g7-f6 e3-d4 d8-c7 d4-c5 c7-d6 c3-d4 a7-b6",
        "g3-h4 d6-c5 c3-b4 b6-a5 f8-g7 d2-c3 a7-b6 e7-d6 h4-g5 g7-f6 e1-d2 b8-c7 d2-e3 c7-d6 e3-f4 h8-g7 b2-c3 g7-h6 a1-b2 b6-c5",
        "g3-h4 d6-c5 c3-b4 c7-d6 b2-c3 b6-a5 d4xb6 a7xc5 e3-f4 d8-c7 d2-e3 c7-b6 c1-d2 d6-e5 b4xd6 e5xg3 c3-b4 a5xc3 d2xb4 e7xc5",
        "g3-h4 d6-c5 c3-b4 c7-d6 b4-a5 d6-e5 a5xc7 d8xb6 b2-c3 e5-f4 e3xg5 h6xf4 a1-b2 c5xe3 f2xd4 b6-a5 a3-b4 e7-d6 b2-a3 g7-h6",
        "g3-h4 d6-c5 c3-b4 f6-e5 h8-g7 b2-c3 g7-f6 a3-b4 h6-g5 e3-d4 a7-b6 b4-a5 e7-d6 d2-e3 d6-c5 c1-b2 b8-a7 b2-a3 f8-e7 e3-f4",
        "g3-h4 d6-c5 c3-b4 h6-g5 g7-h6 a1-b2 b6-a5 a7-b6 c1-b2 b6-c5 c3-d4 g5-f4 f2-g3 f4-e3 c7-b6 b2-c3 b8-a7 e1-f2 f6-e5 a3-b4",
        "g3-h4 d6-c5 h2-g3 e7-d6 g3-f4 f6-e5 e3-d4 d6-c5 f2-g3 c5-b4 b2-a3 f8-e7 c1-b2 h8-g7 g1-f2 g7-f6 f2-e3 b8-c7 e3-f4 f6-g5",
        "g3-h4 d6-c5 h2-g3 e7-d6 g3-f4 f6-e5 e3-d4 h8-g7 c3-d4 g7-f6 f2-e3 d6-e5 b2-c3 b6-c5 e3-f4 f6-e5 h2-g3 c5-d4 a1-b2 h6-g5",
        "g3-h4 d6-e5 a3-b4 e5-f4 b4-a5 f6-e5 h8-g7 a1-b2 g7-h6 b2-c3 h6-g5 c3-b4 f8-g7 f2-g3 g7-h6 c7-b6 d2-e3 d8-c7 e1-f2 c7-d6",
        "g3-h4 d6-e5 a3-b4 e5-f4 c3-d4 g7-h6 f2-g3 f4-e3 b2-c3 f4-g3 d2-e3 g3-h2 c1-d2 f6-e5 a1-b2 h8-g7 b2-a3 g7-f6 e3-d4 e5-f4",
        "g3-h4 d6-e5 a3-b4 f6-g5 b6-c5 h6-g5 c1-b2 h8-g7 c3-d4 a7-b6 d2-c3 g7-f6 c3-b4 b6-a5 d4-c5 e3-f4 f6-g5 b2-c3 g5-h4 e1-f2",
        "g3-h4 d6-e5 a3-b4 g5-f4 e3xg5 h6xf4 b4-c5 b6-a5 b2-a3 g7-h6 b8-c7 e1-f2 h6-g5 a1-b2 h8-g7 b2-a3 c7-d6 d2-e3 f4xd2 c1xe3",
        "g3-h4 d6-e5 a3-b4 g5-f4 e3xg5 h6xf4 b4-c5 b6-a5 b2-a3 g7-h6 b8-c7 g1-f2 h6-g5 a1-b2 h8-g7 b2-a3 g7-h6 f2-e3 c7-d6 c5-b6",
        "g3-h4 d6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-h6 e7-d6 f2-g3 h8-g7 g3xe5 f6xd4 a1-b2 g7-f6 e1-f2 f6-e5 f2-g3",
        "g3-h4 d6-e5 c3-d4 b6-c5 d2-c3 e7-d6 d6-e5 b8-a7 a1-b2 b2-c3 c5-b4 e5-d4 e3-d4 f8-e7 c1-b2 e7-d6 b2-a3 d6-c5 d4-e5 g7-f6",
        "g3-h4 d6-e5 c3-d4 f6-g5 h8-g7 g7-f6 b2-c3 h6-g5 c3-d4 g5-f4 c1-d2 e7-f6 d2-e3 f6-g5 e1-d2 g5-f4 d2-e3 f6-g5 d4-c5 c7-b6",
        "g3-h4 d6-e5 d4-c5 b6xd4 e3xc5 e5-f4 c3-b4 f6-g5 h4xf6 e7xg5 g5-h4 f2-g3 h4xf2 e1xe5 c7-d6 e5xc7 d8xb2 a1xc3 h6-g5 d2-e3",
        "g3-h4 d6-e5 d4-c5 b6xd4 e3xc5 e5-f4 c3-b4 f8-g7 b4-a5 f6-g5 h4xf6 e7xg5 a3-b4 g5-h4 b2-a3 f4-g3 d2-e3 g7-f6 e3-f4 g3xe5",
        "g3-h4 d6-e5 e3-d4 c7-d6 f2-g3 b6-c5 a1-b2 a7-b6 b6-c5 c3-b4 h6-g5 d2-e3 e5-f4 g5-f4 g7-h6 g1-f2 e1-d2 d8-c7 b2-c3 f8-g7",
        "g3-h4 d6-e5 e3-d4 c7-d6 f2-g3 b6-c5 b4-c5 h6-g5 a1-b2 g5-f4 a3-b4 f4-e3 e1-d2 c7-d6 g1-f2 g7-h6 f2-e3 f8-e7 b2-c3 f6-g5",
        "g3-h4 d6-e5 e3-d4 h6-g5 d2-e3 e7-d6 c3-b4 e5xc3 b4xd2 d6-c5 c5xe3 d2xh6 b6-c5 b2-c3 c7-d6 c3-d4 c5xe3 f2xd4 d6-e5 a3-b4",
        "g3-h4 d6-e5 e3-d4 h6-g5 f2-e3 g7-h6 e3-f4 g5xc5 b4xf4 c7-d6 f6-g5 h4xf6 e7xg5 c3-d4 g5-h4 h2-g3 h4xf2 e1xg3 d6-c5 g3-h4",
        "g3-h4 d6-e5 e3-f4 e5xg3 h2xf4 f6-e5 f4xd6 c7xe5 f2-g3 e7-d6 g7-f6 c3-b4 b6-a5 c1-d2 a5xc3 d2xb4 a7-b6 b4-a5 b6-c5 b2-c3",
        "g3-h4 d6-e5 e3-f4 e5xg3 h2xf4 f6-e5 f4xd6 c7xe5 f2-g3 e7-d6 g7-f6 c3-b4 b6-a5 c1-d2 a5xc3 d2xb4 a7-b6 b4-a5 b8-a7 a5xc7",
        "g3-h4 d6-e5 f2-g3 a7-b6 g3-f4 e5xg3 h4xf2 b6-a5 d4-c5 h6-g5 a5xc3 b2xd4 g5-f4 e3xg5 f6xh4 a1-b2 e7-f6 b2-c3 g7-h6 c3-b4",
        "g3-h4 d6-e5 h2-g3 b6-c5 g5-h6 c7-d6 e3-d4 c5xe3 d2xf4 a7-b6 b6-c5 c1-d2 c5-d4 e1-f2 b8-a7 d2-e3 d6-c5 e3-f4 e7-d6 g5xe7",
        "g3-h4 d6-e5 h2-g3 h6-g5 e3-f4 g5xe3 d2xd6 c7xe5 f2-e3 b6-c5 e3-f4 e5-d4 c3xe5 f6xd4 f4-g5 g7-f6 c1-d2 a7-b6 b2-c3 d4xb2",
        "g3-h4 d6-e5 h2-g3 h6-g5 e3-f4 g5xe3 d2xd6 c7xe5 f2-e3 b6-c5 g3-f4 e5xg3 h4xf2 f6-e5 c3-b4 e5-d4 b4xd6 e7xc5 b2-c3 d4xb2",
        "g3-h4 d6-e5 h2-g3 h6-g5 e3-f4 g5xe3 d2xd6 c7xe5 f2-e3 e5-d4 e3xc5 b6xd4 c3xe5 f6xd4 a3-b4 g7-f6 b4-a5 h8-g7 g3-f4 d8-c7",
        "g3-h4 d6-e5 h2-g3 h6-g5 e3-f4 g5xe3 d2xd6 e7xc5 c3-b4 c7-d6 b4-a5 b8-c7 g3-f4 f8-e7 e1-d2 g7-h6 f2-g3 c5-d4 b2-c3 d4xb2",
        "g3-h4 d6xf4 e3xe7 d8xf6 a3-b4 b6-a5 b4-c5 h6-g5 b2-a3 g5-f4 c7-b6 a3-b4 b6xd4 c3xg3 a5xc3 b2xd4 h2xf4 f2-e3 f6-g5 h4xf6",
        "g3-h4 d6xf4 e3xe7 f8xd6 c3-b4 d6-e5 b4-a5 c7-d6 a5xc7 d8xb6 b6-a5 h4-g5 h6xf4 d2-e3 f4xb4 a3xe7 g7-f6 e7xg5 e5-d4 a1-b2",
        "g3-h4 f6-e5 a3-b4 b6-a5 e3-d4 a7-b6 d4xf6 g7xe5 f2-g3 b6-c5 h8-g7 g1-f2 e7-f6 d2-e3 c7-b6 c3-d4 e5xc3 b4xd2 f6-e5 a1-b2",
        "g3-h4 f6-e5 a3-b4 b6-a5 e3-d4 c7-b6 b6-c5 b2-a3 f8-e7 d2-e3 e3-f4 e1-f2 h8-g7 a1-b2 g7-f6 c1-d2 d6-e5 b4-c5 f6-g5 c3-b4",
        "g3-h4 f6-e5 a3-b4 b6-c5 b2-a3 e5-f4 e3xg5 h6xf4 f2-g3 a7-b6 g3xe5 d6xf4 b4xd6 e7xc5 c3-b4 d8-e7 b4xd6 c7xe5 a1-b2 e7-d6",
        "g3-h4 f6-e5 b2-c3 g7-f6 a1-b2 e5-f4 f4-e3 f6-g5 f8-g7 h4-g5 h8-g7 g5-h6 g7-f6 c1-d2 a7-b6 a3-b4 d8-c7 d2-e3 f6-g5 a1-f6",
        "g3-h4 f6-e5 b2-c3 g7-f6 h2-g3 e7-d6 a7-b6 g3-f4 f8-e7 f2-g3 f6-e5 g1-h2 b6-c5 c3-d4 e7-f6 g3-h4 f6-e5 e1-f2 d8-e7 f2-g3",
        "g3-h4 f6-e5 b4-a5 g7-f6 c3-d4 e5xc3 b2xd4 d6-e5 c1-b2 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 d2-c3 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4",
        "g3-h4 f6-e5 b4-c5 e5-f4 b2-c3 g7-f6 f6-e5 d2-e3 h8-g7 c3-d4 g7-f6 e3-d4 c7-d6 d4-c5 a7-b6 c3-d4 b8-a7 a1-b2 b6-c5 f2-e3",
        "g3-h4 f6-e5 c3-b4 b6-a5 b2-c3 c7-b6 e3-d4 b8-c7 d4xf6 g7xe5 c1-b2 h8-g7 d2-e3 e5-d4 e3xc5 b6xd4 c3xe5 a5xc3 b2xd4 d6xf4",
        "g3-h4 f6-e5 c3-b4 b6-a5 b2-c3 c7-b6 e3-d4 g7-f6 d2-e3 b6-c5 c3-d4 f6-e5 f2-g3 b8-a7 g1-f2 e5-d4 c1-b2 d6-e5 d2-c3 a7-b6",
        "g3-h4 f6-e5 c3-b4 b6-a5 b2-c3 c7-b6 e3-d4 g7-f6 h4-g5 d8-c7 f2-g3 b6-c5 d2-e3 h8-g7 c1-b2 c7-b6 g3-h4 g7-h6 g1-f2 f8-g7",
        "g3-h4 f6-e5 c3-b4 b6-c5 b4-a5 a7-b6 d2-e3 b8-a7 h8-g7 c1-d2 g7-f6 f2-g3 c5-d4 g1-h2 b6-c5 d2-c3 c7-b6 h2-g3 d4-e3 c3-d4",
        "g3-h4 f6-e5 c3-b4 e3-d4 b6-c5 c7-b6 h2-g3 b6-a5 a1-b2 e7-f6 d2-e3 f8-e7 e1-d2 c5-b4 b2-a3 b8-c7 g3-f4 c7-d6 f2-g3 b4-a3",
        "g3-h4 f6-e5 c3-b4 e5-d4 b4-a5 c5-d4 g7-f6 b2-c3 f6-e5 g3-f4 h8-g7 d2-e3 g7-f6 f2-g3 f6-e5 e3-f4 a7-b6 c3-b4 e7-f6 g3-h4",
        "g3-h4 f6-e5 c3-b4 e5-f4 c5-d6 e3-f4 c7-d6 h8-b2 d6-c5 b2-c1 c5-b4 f2-e3 d8-e7 e3-f4 e7-d6 c1-d2 b4-c3 e1-f2 a7-b6 a1-b2",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 f2-g3 e7-d6 g3xe5 d6xf4 g1-f2 d8-e7",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 f2-g3 e7-d6 g3xe5 d6xf4 g1-f2 f8-e7",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 f2-g3 e7-d6 g3xe5 d6xf4 e1-f2 d8-e7 c3-d4 b4-a3",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 f2-g3 e7-d6 g3xe5 d6xf4 e1-f2 d8-e7 f2-g3 e7-d6",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 a7-b6 g3xe5 d6xf4 b4xd6 c7xe5 a5xc7 b8xd6",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 f6-e5 e1-f2 a7-b6 f2-e3 g7-h6 e3xg5 h6xf4",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 f6-e5 e1-f2 c5-d4 a1-b2 g7-h6 h4-g5 f4-e3",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 f6-e5 e1-f2 c7-b6 a5xc7 d8xb6 b4-a5 b8-c7",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 f6-e5 e1-f2 e7-f6 f2-e3 d8-e7 e3xg5 g7-h6",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 f6-e5 e1-f2 g7-f6 f2-e3 c5-d4 e3xg5 d4-c3",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 c3-b4 h8-g7 f2-g3 f6-e5 e1-f2 g7-f6 f2-e3 f8-g7 e3xg5 g7-h6",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 h8-g7 f2-g3 a7-b6 g3xe5 d6xf4 b4xd6 c7xe5 a5xc7 b8xd6 a1-b2",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 h8-g7 f2-g3 f6-e5 e1-f2 a7-b6 f2-e3 g7-h6 e3xg5 h6xf4 g1-f2",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 h8-g7 f2-g3 f6-e5 e1-f2 c5-d4 a1-b2 g7-h6 h4-g5 f4-e3 d2xf4",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 h8-g7 f2-g3 f6-e5 e1-f2 e7-f6 f2-e3 d8-e7 e3xg5 g7-h6 g1-f2",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 b2-c3 g7-f6 h8-g7 f2-g3 f6-e5 e1-f2 g7-f6 f2-e3 f8-g7 e3xg5 g7-h6 g1-f2",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 b6-c5 d2-c3 g7-f6 c3-b4 f6-e5 f2-g3 a7-b6 b2-c3 e7-f6 e1-d2 h8-g7 a1-b2 g7-h6",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 f6-g5 h4xf6 e7xg5 c3-d4 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 b2-c3 g7-h6",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 b2-c3 h8-g7 c3-b4 d6-c5 b4xd6 c7xe5 a5xc7 b8xd6 d2-e3 f4xd2 c1xe3 d6-c5",
        "g3-h4 f6-e5 c3-b4 e5-f4 e3xg5 h6xf4 b4-a5 g7-f6 d2-c3 b6-c5 c3-b4 h8-g7 b2-c3 g7-h6 f2-g3 f8-g7 g3xe5 f6xb2 a1xc3 c7-b6",
        "g3-h4 f6-e5 c3-b4 e5-f4 f2-e3 g7-h6 e7-f6 b2-c3 f8-g7 a1-b2 g7-h6 e3-f4 f6-e5 e1-d2 b6-c5 d2-e3 h6-g5 c3-d4 a7-b6 b2-c3",
        "g3-h4 f6-e5 c3-b4 g7-f6 b4-a5 e5-f4 e3xg5 h6xf4 b2-c3 b6-c5 c3-b4 h8-g7 a1-b2 g7-h6 b2-c3 f6-g5 h4xf6 e7xg5 f2-g3 g5-h4",
        "g3-h4 f6-e5 c3-b4 g7-f6 f2-g3 a7-b6 d2-e3 e5-d4 e1-d2 f6-g5 b2-c3 h8-g7 a1-b2 g7-f6 d2-e3 f6-e5 c1-d2 d8-e7 e1-f2 g5-h4",
        "g3-h4 f6-e5 c3-d4 e5xc3 b2xd4 b6-c5 d4xb6 a7xc5 a1-b2 b2-c3 e5-f4 e3xg5 h6xf4 c3-d4 c5xe3 f2xd4 g7-f6 a3-b4 f8-g7 d2-e3",
        "g3-h4 f6-e5 c3-d4 e5xc3 b2xd4 g7-f6 d4-c5 d6xb4 a5xc3 b6-a5 a5xc3 d2xb4 f6-e5 a1-b2 a7-b6 b2-c3 e7-f6 c1-d2 d8-e7 b4-a5",
        "g3-h4 f6-e5 c3-d4 e5xc3 d2xb4 e7-f6 b4-a5 f6-g5 h4xf6 g7xe5 a3-b4 e5-f4 e3xg5 h6xf4 b2-a3 h8-g7 f2-e3 f4xd2 c1xe3 g7-f6",
        "g3-h4 f6-e5 c3-d4 e5xc3 d2xb4 e7-f6 b4-a5 f6-g5 h4xf6 g7xe5 b2-c3 h8-g7 e3-d4 g7-f6 c3-b4 e5xc3 b4xd2 h6-g5 a1-b2 g5-h4",
        "g3-h4 f6-e5 c3-d4 e5xc3 d2xb4 e7-f6 b4-a5 f6-g5 h4xf6 g7xe5 e5-f4 e3xg5 h6xf4 c3-b4 h8-g7 f2-e3 f4xd2 c1xe3 g7-f6 h2-g3",
        "g3-h4 f6-e5 c3-d4 e5xc3 d2xb4 e7-f6 b4-a5 f6-g5 h4xf6 g7xe5 h8-g7 e3-d4 g7-f6 c3-b4 e5xc3 b4xd2 b6-c5 a1-b2 d6-e5 h2-g3",
        "g3-h4 f6-e5 c3-d4 e5xc3 d2xb4 h6-g5 h4xf6 g7xe5 b4-a5 b6-c5 h2-g3 h8-g7 c1-d2 g7-f6 e3-f4 a7-b6 b2-c3 f6-g5 f4xh6 e5-d4",
        "g3-h4 f6-e5 c3-d4 e5xc3 d2xb4 h6-g5 h4xf6 g7xe5 h2-g3 h8-g7 c1-d2 g7-h6 g3-h4 e5-d4 e3xc5 b6xd4 b2-c3 d4xb2 a3xc1 a7-b6",
        "g3-h4 f6-e5 e3-d4 b6-c5 f2-e3 h8-g7 g1-f2 g7-f6 c7-b6 a1-b2 b8-c7 e3-f4 c5-d4 f4-g5 d4-e3 b6-c5 e1-f2 c7-b6 c1-d2 c5-d4",
        "g3-h4 f6-e5 e3-d4 b8-a7 b4-a5 h8-g7 f8-e7 a1-b2 g7-f6 b2-c3 h6-g5 c3-b4 b6-c5 d2-c3 f6-e5 f2-e3 e7-f6 e1-f2 g5-h4 c3-d4",
        "g3-h4 f6-e5 e3-d4 b8-a7 c3-b4 h8-g7 d2-c3 g7-f6 b6-c5 c1-b2 c5-d4 b2-c3 f6-e5 b4-c5 e7-d6 a1-b2 c7-b6 c1-d2 d8-c7 b2-a3",
        "g3-h4 f6-e5 e3-d4 e5-f4 d4-c5 b6xd4 c3xg3 h2xf4 b2-c3 h6-g5 h4xf6 g7xe5 a3-b4 a7-b6 d2-e3 f4xd2 c1xe3 e7-d6 c3-d4 e5xc3",
        "g3-h4 f6-e5 e3-d4 e7-d6 b4-a5 h8-g7 c3-b4 d8-e7 g7-f6 c3-d4 d6-c5 d2-c3 e7-d6 f2-e3 f6-e5 c3-d4 d6-e5 c5-d4 f6-g7 h6-g5",
        "g3-h4 f6-e5 e3-d4 g7-f6 a3-b4 b8-a7 b2-a3 e5-f4 f2-g3 f4-e3 d2-e3 f6-e5 c3-d4 d6-e5 f2-g3 c7-d6 a1-b2 h8-g7 b2-c3 g7-f6",
        "g3-h4 f6-e5 e3-d4 g7-f6 b4-c5 b6-c5 a1-b2 c7-d6 b2-c3 f6-e5 c1-b2 e5-f4 c3-b4 e7-f6 h4-g5 f2-g3 b2-c3 h6-g5 d2-e3 g5-f4",
        "g3-h4 f6-e5 e3-d4 g7-f6 f2-e3 b6-c5 c3-d4 a5-b4 a1-b2 b2-a3 b8-c7 c7-d6 e3-d4 d2-c3 e7-d6 c1-b2 d8-c7 g1-f2 c7-b6 b2-a3",
        "g3-h4 f6-e5 e3-d4 g7-f6 f2-g3 b6-c5 c3-b4 d2-c3 b8-c7 c1-b2 h8-g7 g3-f4 d6-e5 f2-e3 e5-f4 g1-f2 g7-f6 e1-d2 f6-e5 d2-e3",
        "g3-h4 f6-e5 e3-d4 g7-f6 h4-g5 f6xh4 d4xf6 e7xg5 h6xf4 h8-g7 c3-d4 d6-c5 d2-e3 g7-f6 b2-c3 c7-d6 c1-b2 b6-a5 d4xb6 a5xc7",
        "g3-h4 f6-e5 e3-f4 e5xg3 h2xf4 g7-f6 d2-e3 f8-g7 f2-g3 f6-g5 h4xf6 g7xe5 g1-h2 h8-g7 b2-c3 g7-f6 c1-d2 a7-b6 g3-h4 e5xg3",
        "g3-h4 f6-e5 e3-f4 e5xg3 h4xf2 b6-a5 c3-b4 a5xc3 b2xb6 c7xa5 g7-f6 b2-c3 a7-b6 h2-g3 b6-c5 g3-h4 b8-a7 f2-e3 c5-b4 a3xc5",
        "g3-h4 f6-e5 f2-g3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 a3-b4 e7-d6 b6-c5 b2-a3 g7-f6 c3-b4 f8-g7 d2-e3 f4xd2 c1xe3 f6-e5 h2-g3",
        "g3-h4 f6-e5 f2-g3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 c3-b4 g7-f6 b4-a5 b6-c5 b2-c3 h8-g7 c3-b4 a7-b6 b4xd6 c7xe5 a5xc7 b8xd6",
        "g3-h4 f6-e5 f2-g3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 a3-b4 c7-d6 b4-c5 d6xb4 c3xc7 b8xd6 g1-f2 a7-b6 f2-g3 d8-c7 g3xe5 d6xf4",
        "g3-h4 f6-e5 f2-g3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 a3-b4 e7-d6 d6xb4 c3xa5 b6-c5 d2-e3 f4xd2 c1xe3 g7-f6 h2-g3 h8-g7 e3-f4",
        "g3-h4 f6-e5 f2-g3 g7-f6 f4-g5 b6-a5 g5-h6 a7-b6 f6-g5 f8-g7 d6-c5 b2-a3 d8-e7 d2-e3 e7-f6 g3-h4 c7-d6 h2-g3 d6-e5 g3-f4",
        "g3-h4 f6-e5 f2-g3 g7-f6 f4-g5 h6xf4 e3xg5 b6-a5 g5-h6 a7-b6 g3-f4 e5xg3 h4xf2 b6-c5 h2-g3 c5-b4 g1-h2 d6-e5 f2-e3 c7-b6",
        "g3-h4 f6-e5 f2-g3 g7-f6 f4-g5 h6xf4 e3xg5 b6-a5 g5-h6 a7-b6 g3-f4 e5xg3 h4xf2 d6-c5 h2-g3 c7-d6 g1-h2 b8-a7 g3-h4 c5-b4",
        "g3-h4 f6-e5 f2-g3 g7-f6 g3-f4 f6-e5 c3-d4 h8-g7 a1-b2 b6-c5 e3-f4 g7-f6 f2-e3 f8-g7 g1-f2 b8-a7 d2-c3 c5-b4 e1-d2 f6-e5",
        "g3-h4 f6-e5 g1-h2 g7-f6 f2-g3 b6-c5 c3-b4 a5xc3 b2xb6 a7xc5 g3-f4 e5xg3 h4xf2 f6-e5 a1-b2 c7-b6 b2-c3 b6-a5 f2-g3 h8-g7",
        "g3-h4 f6-e5 h4-g5 g7-h6 f2-e3 h8-g7 g5-h6 e5-f4 e1-f2 g7-f6 f2-g3 f6-e5 a3-b4 a7-b6 g3-h4 b6-c5 d2-e3 d8-e7 e3-f4 e7-f6",
        "g3-h4 f6-g5 b4-c5 c7-b6 c3-d4 h6-g5 e3-f4 h8-g7 f2-g3 g7-h6 g3-h4 b6-a5 a1-b2 b8-c7 e1-f2 e7-d6 d4-c5 c7-b6 c1-d2 d2-e3",
        "g3-h4 f6-g5 c3-b4 g7-f6 d4-c5 a1-b2 f6-e5 b2-c3 c7-b6 f2-g3 b6-c5 d2-e3 h8-g7 g3-f4 g7-f6 c3-d4 b8-c7 c1-d2 d8-c7 d2-c3",
        "g3-h4 f6-g5 c3-d4 d6-c5 b2-c3 g5-h4 f4-e5 h6-g5 h8-g7 g7-f6 b4-c5 d8-e7 a3-b4 b8-c7 b4-a5 e7-f6 a1-b2 c7-d6 b2-c3 d8-e7",
        "g3-h4 f6-g5 c3-d4 h8-g7 b2-c3 g7-f6 a1-b2 d6-e5 d8-e7 b2-a3 g5-h4 c1-b2 h6-g5 d4-c5 e7-d6 b4-c5 c7-b6 a3-b4 g5-f4 b2-a3",
        "g3-h4 f6-g5 d4-c5 g7-f6 c3-d4 d8-e7 h8-g7 e3-f4 c7-d6 c3-b4 f6-g5 d4-e5 h6-g5 a1-b2 g7-f6 b4-a5 g5-h4 c3-b4 f6-g5 b2-c3",
        "g3-h4 f6-g5 h4xf6 e7xg5 a3-b4 g5-h4 c3-d4 h6-g5 b4-c5 g5-f4 e3xg5 h4xf6 d4-e5 f6xd4 c5xe3 g7-h6 b2-c3 b6-c5 a1-b2 c5-b4",
        "g3-h4 f6-g5 h4xf6 e7xg5 b4-c5 b6xd4 e3xe7 f8xd6 c3-d4 c7-b6 g7-f6 f2-g3 h2xf4 d4-e5 f6xd4 d2-e3 d4xf2 e1xa5 h8-g7 b2-c3",
        "g3-h4 f6-g5 h4xf6 e7xg5 c3-b4 g5-h4 b2-c3 h6-g5 c3-d4 g7-f6 f6-e5 d4xf6 g5xe7 c3-d4 e7-f6 c1-b2 f6-g5 b2-c3 h8-g7 a1-b2",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 b6-a5 b2-a3 c7-b6 c1-b2 b6-c5 c3-d4 e5xc3 b2xb6 a5xc7 e3-d4 h8-g7 h2-g3 h6-g5 f2-e3 g7-h6",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 b6-a5 b2-a3 c7-b6 h2-g3 f8-g7 e3-d4 b8-c7 d4xf6 g7xe5 g3-h4 h8-g7 g1-h2 b6-c5 c3-d4 c5xg1",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 b6-a5 b2-a3 c7-b6 h2-g3 f8-g7 e3-d4 b8-c7 d4xf6 g7xe5 g3-h4 h8-g7 g1-h2 e5-d4 c3xe5 a5xc3",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 b6-c5 b2-a3 e5-f4 e3xg5 h6xf4 b4-a5 h8-g7 c3-b4 e7-f6 d2-c3 f6-e5 c3-d4 e5xc3 b4xd2 g7-f6",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 b6-c5 b2-a3 e5-f4 e3xg5 h6xf4 f2-g3 a7-b6 g3xe5 d6xf4 b4xd6 c7xe5 a3-b4 h8-g7 d2-e3 f4xd2",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 h6-g5 e3-d4 g5-h4 d4xf6 e7xg5 b4-a5 h8-g7 c3-d4 g7-f6 d2-e3 f6-e5 d4xf6 g5xe7 b2-c3 e7-f6",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 h8-g7 b2-a3 g7-f6 h2-g3 f6-g5 e5-f4 h4xf6 e7xg5 b4-a5 g5-h4 e3xg5 h4xf6 f2-g3 f6-g5 a1-b2",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 h8-g7 b4-a5 e5-f4 e3xg5 h6xf4 b2-a3 g7-f6 c3-b4 f6-g5 a1-b2 f8-g7 d2-c3 e7-f6 e1-d2 f6-e5",
        "g3-h4 f6-g5 h4xf6 g7xe5 a3-b4 h8-g7 e3-d4 g7-f6 b4-c5 d6xb4 c3xa5 e5xc3 b2xd4 e7-d6 a1-b2 b6-c5 d4xb6 a7xc5 h2-g3 f6-e5",
        "g3-h4 f6-g5 h4xf6 g7xe5 c3-b4 h6-g5 b4-a5 g5-h4 a3-b4 e5-f4 e3xg5 h4xf6 d2-e3 b6-c5 b2-a3 f6-g5 c1-d2 h8-g7 h2-g3 g5-h4",
        "g3-h4 f6-g5 h4xf6 g7xe5 c3-b4 h6-g5 b4-a5 g5-h4 a3-b4 e5-f4 e3xg5 h4xf6 d2-e3 d6-c5 b4xd6 c7xe5 a5xc7 b8xd6 h2-g3 h8-g7",
        "g3-h4 f6-g5 h4xf6 g7xe5 c3-d4 e5xc3 b2xd4 h6-g5 a1-b2 d6-c5 b2-c3 g5-h4 h2-g3 h8-g7 c3-b4 b6-a5 b4xd6 c7xc3 d2xb4 a5xc3",
        "g3-h4 f6-g5 h4xf6 g7xe5 c3-d4 e5xc3 b2xd4 h6-g5 a1-b2 d6-c5 g5-h4 h2-g3 h8-g7 g3-f4 c7-d6 d4-e5 d8-c7 c3-d4 e7-f6 d2-c3",
        "g3-h4 f6-g5 h4xf6 g7xe5 e3-d4 c5xe3 f2xf6 e7xg5 b4-c5 d6xb4 a3xc5 d8-e7 a1-b2 h8-g7 h2-g3 c7-d6 g3-h4 d6xb4 h4xd8 b8-c7",
        "g3-h4 f6-g5 h4xf6 g7xe5 e3-d4 e7-f6 f2-g3 h6-g5 d2-e3 g5-h4 e3-f4 h4xf2 e1xg3 b6-c5 d4xb6 a7xc5 c1-d2 h8-g7 c3-b4 g7-h6",
        "g3-h4 f6-g5 h4xf6 g7xe5 e3-f4 e5xg3 h2xf4 f8-g7 f2-e3 a7-b6 b8-a7 c3-d4 e7-f6 g1-f2 f6-e5 d4xf6 g7xg3 f2xh4 d8-e7 a1-b2",
        "g3-h4 f6-g5 h4xf6 g7xe5 f2-g3 e5-f4 e3xg5 h6xf4 g3xe5 d6xf4 a3-b4 c7-d6 b4-c5 d6xb4 c3xc7 b8xd6 b2-c3 h8-g7 c3-d4 d6-c5",
        "g3-h4 f6-g5 h4xf6 g7xe5 f2-g3 h8-g7 e3-f4 b6-c5 c3-b4 c7-b6 b8-c7 b2-c3 g7-f6 c3-b4 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 h2xf4",
        "g3-h4 f6-g5 h4xf6 g7xg3 f2xh4 d6-e5 c3-d4 e5xc3 b2xd4 h8-g7 b6-c5 b4xd6 c7xc3 d2xb4 g7-f6 a1-b2 f6-e5 e3-f4 e5xg3 h4xf2",
        "g3-h4 f6-g5 h4xf6 g7xg3 f2xh4 d6-e5 e3-f4 e5xg3 h4xf2 h8-g7 h6-g5 f2-g3 h2xf4 b4-c5 b6xd4 c3xg3 g7-f6 b2-c3 g5-h4 a1-b2",
        "g3-h4 f6-g5 h6-g5 f8-e7 e1-f2 b6-c5 f2-g3 h8-g7 c1-d2 g7-f6 c3-b4 f6-e5 b4-a5 a7-b6 g3-h4 d8-e7 d2-e3 e7-f6 b2-c3 f6-g5",
        "g3-h4 f6-g5 h6-g5 f8-e7 e3-f4 b6-c5 e1-f2 h8-g7 f2-g3 g7-f6 c3-b4 f6-e5 c1-d2 a7-b6 g3-h4 d8-e7 b4-a5 e7-f6 b2-c3 d6-e5",
        "g3-h4 f6-g5 h6-g5 h2-g3 g5-h4 g3-f4 h8-g7 g7-h6 b2-c3 c7-d6 g1-h2 d6-c5 f4-e5 a5-b4 f2-e3 e7-d6 e3-f4 f8-e7 d2-c3 f6-e5",
        "g3-h4 f6-g5 h8-g7 c3-d4 g7-f6 b2-c3 b6-a5 d6-c5 f4-e5 f8-g7 e3-d4 e7-f6 f2-g3 g3-h4 a5-b4 c1-d2 d4-e3 h8-f6 b4-a3 f6-a1",
        "g3-h4 f6-g5 h8-g7 c3-d4 g7-f6 b2-c3 f6-g5 g5-h4 a1-b2 b6-a5 c3-d4 a7-b6 b2-c3 e7-d6 g1-h2 h6-g5 d2-e3 c7-d6 h2-g3 d6-e5",
        "g3-h4 f6-g5 h8-g7 e3-f4 d6-e5 b6-a5 a1-b2 a7-b6 b2-c3 b6-c5 c3-d4 g7-f6 a3-b4 f8-e7 d2-e3 e7-d6 d4-c5 d6-e5 b4-a5 h6-g5",
        "g3-h4 f8-e7 c3-d4 d6-e5 d2-c3 g5-f4 c3-b4 f4-g3 b2-c3 g3-h2 c3-b4 e7-d6 b4-c5 c7-d6 d2-e3 b6-a5 e3-f4 d6-e5 f6-g5 f2-e3",
        "g3-h4 f8-e7 e3-d4 b6-c5 c3-b4 g5-f4 b2-c3 f6-g5 f2-e3 h8-g7 e1-f2 e7-f6 a1-b2 f6-g5 d2-e3 d8-e7 b2-c3 e7-f6 f2-e3 e5-d4",
        "g3-h4 f8-e7 e3-f4 f6-e5 b4-a5 h6-g5 c3-b4 g5-h4 e5-f4 c1-d2 g7-h6 d2-e3 b6-c5 h2-g3 f6-g5 b2-c3 g5-h4 a1-b2 h8-g7 g3-f4",
        "g3-h4 f8-e7 e3-f4 f6-e5 b4-a5 h6-g5 c3-d4 b6-c5 d2-e3 g7-f6 h2-g3 g5-h4 a1-b2 h8-g7 c1-d2 d6-e5 b2-c3 c7-d6 c3-b4 f6-g5",
        "g3-h4 g5-f4 e3xg5 h6xf4 c3-b4 h8-g7 b2-c3 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6 f2-e3 d6xb4 e3xg5 g7-h6 a1-b2 h6xf4 b2-a3 b8-c7",
        "g3-h4 g7-f6 c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 b4-a5 f8-g7 f2-g3 f6-g5 e1-f2 g5-h4 c1-d2 g7-f6 a5-b6 f4-e5 g3-f4 f6-g5",
        "g3-h4 g7-f6 c3-d4 d6-c5 f4-e5 f6-g5 b2-c3 g5-h4 h6-g5 g5-f4 f8-e7 b4-a5 h8-g7 c3-d4 d6-c5 a1-b2 g7-f6 c1-d2 f6-e5 d2-e3",
        "g3-h4 g7-f6 c3-d4 d6-e5 b2-c3 e7-d6 f2-g3 f6-g5 d4xf6 g5xe7 g3-f4 b6-c5 c3-d4 a7-b6 h2-g3 e7-f6 a1-b2 f8-g7 b2-c3 c5-b4",
        "g3-h4 g7-f6 f4-g5 b6-a5 g5-h6 a7-b6 c3-d4 d6-c5 e7-d6 b2-c3 h8-g7 e1-f2 d8-e7 a1-b2 b8-a7 d4-e5 c5-d4 f2-g3 d2-e3 g7-f6",
        "g3-h4 g7-f6 f4-g5 f6-e5 g5-h6 h8-g7 f2-g3 g7-f6 b6-c5 c3-b4 f6-e5 b4-a5 c7-b6 b2-c3 e7-f6 h2-g3 c5-d4 g3-h4 b6-c5 d2-e3",
        "g3-h4 g7-f6 f4-g5 h8-g7 g5-h6 b6-a5 f2-e3 c7-b6 f6-e5 f4-g5 g7-f6 d2-e3 b8-c7 e3-d4 b6-c5 c3-d4 a3-b4 c7-b6 a1-b2 d6-c5",
        "g3-h4 g7-f6 h2-g3 b6-c5 g3-f4 f6-g5 h8-g7 c3-d4 g7-f6 a1-b2 f8-e7 b2-c3 g5-h4 f4-g5 e7-d6 f2-e3 f8-e7 e3-f4 c7-d6 d2-e3",
        "g3-h4 g7-h6 a3-b4 h6xf4 e3xg5 d6-e5 h2-g3 c7-d6 g1-f2 b6-c5 c5xa3 e3-d4 d8-c7 e1-f2 c7-b6 d2-e3 b6-c5 d4xb6 a5xc7 e3-d4",
        "g3-h4 g7-h6 c3-d4 d6-e5 h2-g3 e5xc3 d2xb4 a5xc3 b2xd4 e7-d6 d6-c5 g3-f4 f8-g7 f4-e5 b6-a5 d4xb6 f6xd4 e3xc5 a5-b4 c5-d6",
        "g3-h4 g7-h6 f2-e3 a7-b6 b2-c3 b6-c5 c5-b4 a1-b2 b4-a3 c3-d4 c7-d6 b2-c3 d6-c5 f2-e3 c7-b6 h2-g3 d8-c7 g3-f4 c7-d6 c3-d4",
        "g3-h4 g7-h6 f2-e3 a7-b6 b2-c3 f6-e5 h8-g7 g1-f2 g7-f6 f2-g3 b6-c5 c3-b4 c7-b6 g3-f4 b6-a5 c1-d2 c5-d4 f2-g3 d8-c7 a1-b2",
        "g3-h4 g7-h6 f2-e3 a7-b6 c3-d4 d6-c5 b8-a7 b2-c3 c7-d6 c3-b4 b6-a5 a1-b2 c7-b6 b2-c3 b6-a5 e1-f2 a7-b6 g5-h6 b6-c5 e3-d4",
        "g3-h4 g7-h6 f2-e3 b6-c5 c3-b4 a1-b2 h8-g7 g5-h6 f6-e5 e1-f2 b8-c7 b2-c3 g7-f6 f2-e3 c7-b6 c3-b4 b6-a5 d2-c3 c5-d4 e5-f4",
        "g3-h4 g7-h6 f2-e3 b6-c5 g1-f2 c7-b6 h8-g7 c3-b4 g7-h6 f2-e3 b6-a5 c1-b2 b8-a7 a1-b2 b2-c3 d8-c7 g5-h6 c7-b6 d2-e3 b6-a5",
        "g3-h4 g7-h6 f2-e3 b6-c5 g5-h6 b8-c7 g1-f2 c7-b6 a1-b2 h8-g7 f2-e3 d6-e5 e3-f4 f6-e5 d2-e3 g7-f6 b2-c3 e5-f4 c1-d2 e7-d6",
        "g3-h4 g7-h6 f2-e3 b6-c5 g5-h6 c7-d6 f6-e5 c3-d4 a1-b2 h8-g7 b2-c3 g7-f6 e1-f2 b8-a7 c3-d4 d6-e5 c1-d2 e5-d4 a3-b4 d8-c7",
        "g3-h4 g7-h6 f2-e3 b6-c5 g5-h6 e5-f4 a7-b6 f2-g3 h8-g7 g7-f6 g1-f2 b6-a5 f2-e3 c7-d6 h2-g3 b8-a7 c3-d4 f6-g5 d6-e5 e3-f4",
        "g3-h4 g7-h6 f2-e3 b6-c5 g5-h6 h8-g7 c5-d4 b2-c3 a7-b6 b4-a5 b6-c5 e1-f2 g7-f6 f2-e3 f6-e5 e3-d4 e7-f6 c3-d4 d6-c5 b8-a7",
        "g3-h4 g7-h6 f2-e3 b8-c7 g1-f2 b6-c5 e5-f4 f2-g3 h8-g7 b2-c3 g7-f6 d2-e3 d6-e5 h2-g3 e7-d6 c3-b4 c7-b6 c1-d2 b6-a5 d2-c3",
        "g3-h4 g7-h6 f2-e3 b8-c7 g5-h6 b6-c5 c5-b4 f2-e3 b4-a3 e3-f4 c7-d6 f4-g5 h8-g7 c3-d4 a7-b6 b2-c3 d6-e5 a1-b2 d8-c7 d4-c5",
        "g3-h4 g7-h6 f2-e3 b8-c7 g5-h6 e5-d4 d4-c3 b6-c5 a1-b2 c7-b6 b2-c3 h8-g7 e1-f2 b6-a5 f2-e3 d8-c7 g1-f2 c7-b6 e3-f4 f6-e5",
        "g3-h4 g7-h6 f2-e3 c7-d6 c3-d4 b6-a5 d6-c5 c3-d4 c7-d6 a1-b2 a7-b6 b2-c3 b6-a5 g1-f2 d8-c7 f2-e3 c7-b6 g5-h6 b6-c5 c3-d4",
        "g3-h4 g7-h6 f2-e3 e5-d4 g5-h6 d6-c5 b8-a7 b2-c3 c7-d6 c3-b4 f6-e5 g3-f4 e7-f6 f2-e3 f6-e5 d2-c3 h8-g7 e1-f2 c5-d4 d8-c7",
        "g3-h4 g7-h6 f2-e3 f6-e5 c3-b4 c7-d6 b6-c5 g5-h6 b8-c7 d2-e3 h8-g7 e3-f4 g7-f6 c1-d2 d6-e5 b2-c3 c5-b4 c7-b6 e7-d6 c3-b4",
        "g3-h4 g7-h6 f2-e3 f6-e5 g5-h6 b6-a5 h8-g7 f2-e3 b8-a7 c3-d4 g7-f6 a1-b2 c7-b6 b2-c3 b6-c5 h2-g3 c7-b6 e1-f2 b6-a5 g3-f4",
        "g3-h4 g7-h6 f2-e3 f6-e5 g5-h6 h8-g7 b6-a5 f2-e3 b8-a7 e3-f4 g7-f6 f2-g3 c7-b6 g3-h4 b6-c5 c3-b4 h2-g3 d8-c7 g3-f4 c7-b6",
        "g3-h4 g7-h6 f2-e3 f6-e5 g5-h6 h8-g7 g7-f6 f2-e3 b6-a5 e3-f4 b8-a7 h2-g3 f6-e5 f2-e3 e7-f6 g3-h4 c7-b6 e3-f4 d8-e7 f2-g3",
        "g3-h4 g7-h6 f2-e3 h8-g7 d2-e3 g7-h6 d6-c5 g5-h6 c7-d6 e1-f2 a7-b6 d2-e3 b8-a7 c3-b4 f6-e5 b4-a5 d8-c7 h4-g5 e5-f4 e3-d4",
        "g3-h4 g7-h6 f2-e3 h8-g7 g5-h6 b6-c5 b8-c7 f2-e3 c5-b4 e3-f4 b4-a3 f4-g5 c7-d6 d2-e3 d8-c7 e1-f2 d6-e5 c3-d4 c7-d6 f2-g3",
        "g3-h4 g7-h6 f2-e3 h8-g7 g5-h6 b6-c5 g7-f6 d2-e3 f6-e5 h4-g5 a7-b6 b4-a5 b8-a7 c1-d2 e5-f4 b2-c3 f4-g3 c3-b4 c5-d4 d2-c3",
        "g3-h4 g7-h6 f2-e3 h8-g7 g5-h6 b8-c7 d6-c5 d2-e3 c7-d6 e1-d2 e5-d4 f2-g3 f6-e5 b2-c3 g7-f6 h2-g3 d8-c7 c3-b4 e5-d4 b4-a5",
        "g3-h4 g7-h6 f2-e3 h8-g7 g5-h6 e5-f4 f6-e5 b2-c3 d6-c5 c3-b4 c7-d6 a1-b2 b8-c7 b4-a5 g7-f6 b2-c3 d6-e5 c3-b4 c7-d6 d2-c3",
        "g3-h4 g7-h6 f2-e3 h8-g7 g5-h6 e5-f4 f6-e5 b4-a5 b8-c7 a3-b4 g7-f6 b2-a3 b6-c5 a1-b2 c7-b6 a3-b4 c7-d6 b2-a3 b8-c7 d2-c3",
        "g3-h4 g7-h6 f2-g3 d2-e3 b6-a5 c7-b6 b2-c3 d6-c5 g1-f2 b8-c7 f2-g3 c7-d6 g3-f4 f8-g7 h2-g3 g7-h6 e1-d2 d8-c7 c1-b2 c5-b4",
        "g3-h4 g7-h6 f2-g3 d2-e3 b6-c5 c3-b4 h8-g7 a1-b2 f6-e5 h2-g3 g7-f6 f2-e3 a7-b6 b2-c3 d6-c5 e1-f2 b6-a5 e3-d4 e7-d6 g1-f2",
        "g3-h4 g7-h6 f2-g3 d2-e3 h6-g5 c3-d4 b6-c5 e1-f2 c7-b6 b2-c3 d8-e7 c3-b4 e7-f6 b4-a5 d6-e5 a1-b2 g5-h4 b2-c3 f6-g5 c3-b4",
        "g3-h4 g7-h6 f2-g3 d2-e3 h6-g5 e1-f2 b6-c5 c3-d4 c7-b6 b2-c3 b6-a5 c3-d4 c7-b6 d4-c5 b8-c7 c1-d2 c7-d6 a1-b2 f6-e5 b2-c3",
        "g3-h4 g7-h6 f2-g3 g1-f2 h8-g7 g7-h6 h2-g3 b6-c5 c3-b4 f6-e5 g3-f4 e7-f6 a1-b2 h6-g5 b2-c3 a7-b6 c3-d4 b6-a5 c1-d2 f6-e5",
        "g3-h4 g7-h6 f2-g3 h2-g3 b6-a5 c7-b6 b2-c3 d6-c5 d2-e3 f6-e5 c5-b4 e1-f2 a7-b6 f2-e3 b6-c5 g1-f2 b8-c7 e3-f4 c5-b4 c3-d4",
        "g3-h4 g7-h6 f2-g3 h2-g3 b6-c5 c5-b4 a1-b2 b8-c7 f4-e5 e7-d6 g1-f2 f2-e3 f4-g3 b4-a3 b2-c3 d8-e7 f2-g3 c7-d6 e3-f4 a7-b6",
        "g3-h4 g7-h6 f2-g3 h2-g3 d6-e5 c7-d6 c3-d4 b6-c5 g3-f4 b8-a7 a1-b2 a7-b6 b2-c3 b6-a5 c3-d4 c5-b4 e1-d2 d6-c5 e3-d4 c7-b6",
        "g3-h4 g7-h6 f2-g3 h2-g3 e7-f6 d6-e5 c1-b2 c7-d6 g3-f4 b6-c5 d2-e3 f6-e5 c3-d4 d8-e7 f2-g3 e7-f6 g3-h4 h6-g5 b2-c3 d6-e5",
        "g3-h4 g7-h6 h2-g3 b6-c5 c3-b4 a5xc3 b2xb6 a7xc5 g3-f4 f6-g5 h4xf6 e7xg5 a1-b2 h8-g7 b2-c3 g5-h4 c1-b2 f8-e7 c3-d4 c7-b6",
        "g3-h4 h6-g5 c3-d4 b6-a5 b4-c5 g7-h6 c5-b6 g5-f4 b6-a7 h8-g7 b2-c3 e7-d6 c1-b2 g7-h6 d4-e5 g1-h2 d8-e7 f2-g3 f8-g7 b2-c3",
        "g3-h4 h6-g5 d4-c5 b6xd4 e3xc5 d6xb4 c3xa5 g7-h6 b2-c3 a7-b6 g5-f4 d2-c3 b6-c5 b4xd6 e7xc5 c1-d2 c7-b6 a5xc7 d8xb6 h2-g3",
        "g3-h4 h6-g5 e3-f4 g5xe3 f2xd4 d6-e5 d2-e3 e7-d6 h2-g3 g7-h6 g3-f4 e5xg3 h4xf2 f8-g7 c1-d2 b6-c5 d4xb6 a7xc5 e3-f4 f6-g5",
        "g3-h4 h6-g5 e3-f4 g5xe3 f2xd4 d6-e5 h2-g3 e7-d6 d2-e3 b6-a5 g7-h6 g1-h2 c7-b6 c1-d2 f6-g5 h4xf6 e5xg7 g3-h4 d6-c5 d2-e3",
        "g3-h4 h6-g5 e3-f4 g5xe3 f2xd4 d6-e5 h2-g3 e7-d6 d2-e3 g7-h6 b6-a5 g1-h2 f6-g5 h4xf6 e5xg7 c1-d2 c7-b6 d4-c5 d6xb4 a3xc5",
        "g3-h4 h6-g5 e3-f4 g5xe3 f2xd4 d6-e5 h2-g3 e7-d6 g3-f4 e5xg3 h4xf2 f8-e7 c3-b4 f6-e5 d4xf6 g7xe5 d2-e3 h8-g7 f2-g3 e5-d4",
        "g3-h4 h6-g5 e3-f4 g5xe3 f2xd4 d6-e5 h2-g3 e7-d6 g3-f4 e5xg3 h4xf2 g7-h6 c3-b4 f6-g5 b4-c5 d6xb4 a3xc5 h8-g7 f2-g3 g7-f6",
        "g3-h4 h6-g5 e3-f4 g5xe3 f2xd4 d6-e5 h2-g3 g7-h6 a3-b4 e7-d6 f6-g5 h4xf6 e5xg7 b4-c5 d6xb4 a3xc5 g7-f6 a1-b2 f8-g7 e1-f2",
        "g3-h4 h6-g5 f2-g3 g7-h6 g3-f4 d6-c5 b4xd6 c7xg3 h2xf4 e7-d6 b6-c5 c3-b4 a5xc3 d2xb4 d6-e5 f4xd6 c5xe7 h2-g3 a7-b6 a1-b2",
        "g3-h4 h6-g5 h4xf6 e7xg5 h2-g3 g7-h6 g3-f4 b4-a3 c3-d4 h8-g7 b2-c3 g7-f6 a1-b2 d6-e5 f4xd6 c7xe5 a5xc7 b8xd6 d4-c5 d6xb4",
        "g3-h4 h6xf4 e3xg5 a7-b6 g5-h6 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 c3-d4 c7-d6 b2-c3 a5-b4 c3xa5 f6-g5 h4xf6 g7xc3",
        "g3-h4 h6xf4 e3xg5 b6-a5 g5-h6 f6-e5 f2-g3 g7-f6 g3-f4 e5xg3 h4xf2 b8-c7 f2-e3 c5-b4 a3xc5 d6xb4 b2-c3 c7-d6 h2-g3 h8-g7",
        "g3-h4 h6xf4 e3xg5 b6-a5 g5-h6 f6-e5 f2-g3 g7-f6 g3-f4 e5xg3 h4xf2 f6-e5 f2-g3 h8-g7 g3-h4 g7-f6 h2-g3 a7-b6 d2-c3 b8-a7",
        "g3-h4 h6xf4 e3xg5 b6-c5 c3-b4 a5xc3 d2xb4 g7-h6 f2-g3 h6xf4 g3xc7 b8xd6 g1-f2 f8-g7 f2-e3 f6-g5 h4xf6 g7xe5 a1-b2 e7-f6",
        "g3-h4 h6xf4 e3xg5 b6-c5 c3-b4 a5xc3 d2xb4 g7-h6 f2-g3 h6xf4 g3xg7 f8xh6 c1-d2 a7-b6 b4-a5 c5-d4 a1-b2 h6-g5 h4xf6 e7xg5",
        "g3-h4 h6xf4 e3xg5 b6-c5 g5-h6 a7-b6 c3-d4 c5xe3 d2xf4 d6-e5 f4xd6 e7xc5 f2-e3 c5-b4 h2-g3 d8-e7 g1-f2 c7-d6 g3-f4 f6-e5",
        "g3-h4 h6xf4 e3xg5 b6-c5 g5-h6 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 b8-c7 f2-e3 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 f2-e3",
        "g3-h4 h6xf4 e3xg5 b6-c5 g5-h6 c5-b4 a3xc5 d6xb4 f2-e3 c7-d6 h2-g3 a7-b6 g3-f4 f6-e5 a1-b2 e5xg3 h4xf2 b4-a3 c3-d4 g7-f6",
        "g3-h4 h6xf4 e3xg5 b6-c5 g5-h6 c5-b4 a3xc5 d6xb4 f2-e3 f6-e5 g7-f6 g3-f4 e5xg3 h4xf2 c7-d6 f2-g3 b4-a3 g3-h4 a7-b6 g1-h2",
        "g3-h4 h6xf4 e3xg5 b6-c5 g5-h6 c5-d4 c3xe5 f6xd4 h2-g3 d6-c5 a7-b6 c1-b2 c7-d6 g3-h4 b8-c7 f2-g3 d4-c3 d2xb4 a5xc3 b2xd4",
        "g3-h4 h6xf4 e3xg5 b6-c5 g5-h6 c7-b6 f2-e3 c5-b4 a3xc5 b6xb2 a1xc3 a7-b6 e3-d4 b6-c5 d4xb6 a5xc7 c3-d4 b8-a7 h2-g3 c7-b6",
        "g3-h4 h6xf4 e3xg5 b6-c5 g5-h6 c7-b6 f2-e3 c5-b4 a3xc5 b6xf2 g1xe3 f6-e5 a1-b2 a7-b6 e3-f4 e5xg3 h4xf2 g7-f6 f2-e3 b6-c5",
        "g3-h4 h6xf4 e3xg5 b6-c5 g5-h6 c7-b6 h2-g3 c5-b4 a3xc5 b6xb2 a1xc3 f6-e5 f2-e3 g7-f6 g3-f4 e5xg3 h4xf2 d6-c5 c3-d4 e7-d6",
        "g3-h4 h6xf4 e3xg5 b6-c5 g5-h6 e5-f4 f2-e3 f6-g5 h4xf6 e7xg5 g5-h4 e3xg5 h4xf6 c3-b4 f6-e5 h2-g3 g7-f6 d2-e3 e5-d4 e1-f2",
        "g3-h4 h6xf4 e3xg5 c7-d6 g5-h6 b6-a5 f2-e3 b8-c7 h2-g3 c7-b6 f6xd4 c3xc7 b6-c5 c7-b8 d8-c7 b8xb4 a3xc5 b2-c3 g7-f6 a1-b2",
        "g3-h4 h6xf4 e3xg5 d6-e5 g5-h6 b6-a5 f2-g3 a7-b6 g3-f4 e5xg3 h4xf2 f6-e5 h2-g3 g7-f6 b2-c3 e7-d6 d2-e3 b8-a7 g3-h4 d8-e7",
        "g3-h4 h6xf4 e3xg5 d6-e5 g5-h6 e7-d6 b2-c3 b6-a5 f2-e3 a7-b6 b8-a7 e1-f2 d8-c7 e3-d4 c5xe3 f2xd4 e5-f4 g3xe5 d6xf4 g1-h2",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b6-a5 g1-f2 f6-e5 a7-b6 h2-g3 c7-d6 e3-d4 f8-g7 d4xf6 g7xe5 d2-e3 b8-a7 e3-d4",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b6-a5 g1-f2 h8-g7 e5-d4 c3xe5 f6xd4 c1-b2 c7-d6 h2-g3 b8-c7 g3-f4 d6-c5 f2-g3",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b6-c5 b2-c3 h8-g7 e5-d4 c3xe5 f6xd4 h2-g3 g7-f6 a1-b2 c7-b6 a3-b4 c5xa3 h4-g5",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b6-c5 c3-b4 c5-d4 d4xb2 a1xc3 d6-e5 g5-h6 e5-f4 d2-e3 f4xd2 c1xe3 a7-b6 b4-a5",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b6-c5 c3-b4 h8-g7 b4xd6 e7xc5 g5xe7 d8xf6 b2-c3 c7-d6 c3-b4 a7-b6 b4-a5 d6-e5",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b6-c5 g5-h6 a7-b6 b6-a5 d2-e3 a5xc3 b2xb6 c7xa5 c1-d2 d6-c5 d2-c3 e7-d6 e3-f4",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b8-c7 g1-f2 b6-c5 c7-b6 f2-g3 e5-d4 g3-f4 f6-e5 b4-a5 e5xg3 a5xc3 g3-h2 g5-h6",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b8-c7 g1-f2 h8-g7 g5-h6 e5-d4 c3xe5 f6xd4 d2-e3 g7-f6 e3xc5 b6xd4 a3-b4 d6-e5",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 c7-d6 g1-f2 b8-c7 f6-e5 g5-h6 h8-g7 e3-d4 g7-f6 h4-g5 f6xh4 d4xf6 e7xg5 h6xf4",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 c7-d6 g1-f2 b8-c7 h8-g7 g5-h6 e5-d4 c3xe5 f6xd4 d2-c3 d6-c5 c3xe5 c5-b4 a3xc5",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 f6-e5 c3-d4 e5xc3 b2xd4 h8-g7 a1-b2 a7-b6 b2-c3 g7-f6 h2-g3 b6-a5 d2-e3 c7-b6",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 f6-e5 g5-h6 h8-g7 c3-d4 e5xc3 b2xd4 g7-f6 a1-b2 a7-b6 b2-c3 b6-a5 d2-e3 c7-b6",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 f6-e5 g5-h6 h8-g7 g1-f2 a7-b6 f2-e3 g7-f6 h2-g3 b6-a5 g3-f4 e5xg3 h4xf2 d6-e5",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 f6-e5 g5-h6 h8-g7 g1-f2 g7-f6 f2-e3 a7-b6 e3-d4 b6-c5 d4xb6 c7xa5 d2-e3 b8-c7",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 f6-e5 g5-h6 h8-g7 g7-f6 e3-d4 d6-c5 d4xb6 c7xa5 h2-g3 a7-b6 e1-f2 e7-d6 h4-g5",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h8-g7 g5-h6 b6-a5 g7-f6 c1-d2 c7-b6 c3-b4 a5xc3 d2xb4 f8-g7 h6xf8 f6-g5 h4xf6",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h8-g7 g5-h6 b6-a5 g7-f6 e3-f4 a7-b6 f4-g5 b8-a7 a3-b4 b6-c5 b2-a3 c7-b6 e1-f2",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h8-g7 g5-h6 e5-f4 d6-c5 d2-e3 f4xd2 c1xe3 b6-a5 d4xb6 a5xc7 b2-c3 f6-e5 a1-b2",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h8-g7 g5-h6 f6-e5 a3-b4 g7-f6 b4-a5 e5-f4 b2-a3 f6-g5 h4xf6 e7xg5 a3-b4 g5-h4",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h8-g7 g5-h6 f6-e5 a7-b6 f2-e3 g7-f6 e3-d4 b6-a5 h4-g5 f6xh4 d4xf6 e7xg5 h6xf4",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h8-g7 g5-h6 f6-e5 g7-f6 e3-f4 e5xg3 h4xf2 c7-d6 f2-g3 b6-a5 c3-d4 a7-b6 b2-c3",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h8-g7 g5-h6 f6-e5 g7-f6 h2-g3 a7-b6 g3-f4 e5xg3 h4xf2 b6-a5 f2-g3 c7-b6 g3-h4",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-g3 h2xf4 g5xe3 b6-a5 e3-f4 a7-b6 d6-e5 f4xd6 c7xe5 a3-b4 h6-g5 b2-a3 e5-f4 e3-d4 e7-d6 c1-d2",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-g3 h2xf4 g5xe3 d6-e5 e3-f4 e5xg3 h4xf2 h6-g5 a3-b4 f6-e5 b4-a5 e5-f4 b2-a3 b6-c5 c3-b4 g5-h4",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-g3 h6xf4 g3xg7 f8xh6 d2-e3 e7-f6 h6xb4 a3xg5 d8-e7 h2-g3 c7-d6 g3-h4 a5-b4 g5-f6 e7xg5 h4xf6",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-g3 h6xf4 g3xg7 h8xf6 d2-e3 a7-b6 b6-a5 g3-f4 c7-b6 f4-g5 b8-c7 g5-h6 b6-c5 c3-b4 a5xc3 b2xb6",
        "g3-h4 h6xf4 e3xg5 g7-h6 f2-g3 h6xf4 g3xg7 h8xf6 h2-g3 a7-b6 b2-c3 b6-c5 g3-f4 f6-e5 g1-h2 e5xg3 h4xf2 e7-f6 f2-e3 f8-g7",
        "g3-h4 h8-g7 g5-h6 b6-c5 d2-e3 a7-b6 f2-g3 b8-a7 f6-e5 h2-g3 g7-f6 g3-h4 b6-a5 f2-g3 c7-b6 g3-f4 c5-d4 c1-d2 f6-g5 d4-e3",
        "g3-h4 h8-g7 g5-h6 f6-e5 f2-e3 g7-f6 h2-g3 b6-a5 a7-b6 f2-g3 b6-c5 c3-b4 g1-h2 d6-c5 a1-b2 f6-e5 g3-f4 f8-g7 f4-g5 b8-c7",
        // --- g3-f4 (204 linhas de campeonato) ---
        "g3-f4 d6-c5 f4-e5 h6-g5 h2-g3 g5-f4",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 f6-g5 f6-e5 f6-g5",
        "g3-f4 c7-b6 d4-e5 f6xd4 c3xa5 e7-d6 h2-g3 b8-c7",
        "g3-f4 f6-e5 f2-g3 e7-f6 e3-d4 b6-c5 c3-b4 f6-g5",
        "g3-f4 f6-e5 h2-g3 b6-c5 c3-b4 a7-b6 g7-f6 a7-b6",
        "g3-f4 f6xd4 c3xe5 d6-c5 h2-g3 e7-d6 b2-c3 h6-g5 f4xh6 d6xh2 c7-d6 d4xb6 a7xc5",
        "g3-f4 a3xc5 b2-a3 g7-h6 c1-b2 f6-g5 c3-d4 b6-a5 d4xb6 a7xc5 a5-b4 c3xa5 c5-d4 e3xc5 g5xc1",
        "g3-f4 b6-c5 b2-c3 g5-h4 c3-d4 f6-g5 d4xb6 c7xc3 d2xb4 g7-f6 a7-b6 f2-g3 h4xd4 b4-a5 g5xe3 a5xg7",
        "g3-f4 e3xg5 b2-c3 b4xd2 c1xe3 g5-f4 e3xe7 e7xg5 h6xf4 g1-f2 h8-g7 f2-g3 f4-e3 g3-f4 e3xg5 h4xh8",
        "g3-f4 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 a3-b4 c7-d6 b2-a3 b6-c5 d4xb6 a7xc5 h2-g3 g5-h4 g1-h2 d8-c7",
        "g3-f4 b6xd4 c3xe5 f6xd4 e3xc5 c7-b6 d2-e3 b6xd4 e3xc5 d8-c7 f4-g5 h6xf4 c5-d6 e7xc5 c1-d2 a3xe3 f2xd8",
        "g3-f4 f6-g5 b2-c3 g7-f6 c3-d4 h8-g7 a1-b2 g5-h4 f6-g5 d4-e5 e7-f6 d2-c3 f8-e7 b2-c3 e7-d6 c3-d4 d6-c5",
        "g3-f4 f6-g5 c3-b4 b6-a5 h2-g3 a5xc3 d2xb4 g5-h4 b4-a5 d6-c5 h6-g5 f4xh6 c5-b4 a3xc5 c7-b6 a5xc7 b8xh2",
        "g3-f4 g5xe3 f2xd4 b6-c5 d4xb6 a7xc5 c3-b4 f6-e5 b2-c3 f8-e7 e7-f6 f2-g3 h6-g5 d2-e3 e5-d4 c3xe5 f6xh4",
        "g3-f4 f6-g5 d2-e3 d6-c5 f4-e5 f8-e7 c1-d2 e7-d6 f2-g3 g7-f6 h2-g3 c7-d6 g3-h4 d6-e5 g1-h2 d8-e7 c3-b4 b6-c5",
        "g3-f4 d6-c5 h2-g3 c7-d6 c3-b4 f6-e5 b4-a5 d8-c7 b2-c3 e5-d4 c3xe5 h6-g5 f4xh6 e3-f4 g7-f6 a1-b2 h8-g7 d2-c3 f6-g5",
        "g3-f4 a5-b4 a3xc5 d6xb4 b2-c3 b4-a3 c3-d4 e7-f6 f4-g5 h6xf4 e3xe7 d8xf6 d2-c3 c7-d6 f2-e3 f6-e5 d4xf6 g7xe5 h2-g3 b6-a5",
        "g3-f4 a7-b6 c3-b4 b6-a5 c1-d2 a1-b2 d6-c5 g7-h6 f2-e3 b8-c7 h2-g3 c7-d6 g1-f2 h8-g7 g5-h6 d6-e5 f2-e3 c5-d4 e5-f4 d2-e3",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 f6-e5 h2-g3 a7-b6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g7-f6 f4xd6 c7xe5 g3-h4 e5-f4 b2-c3 f4-g3",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 f6-e5 h2-g3 g7-f6 a7-b6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g7-f6 f4xd6 c7xe5 b2-c3 h6-g5 g3-h4",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 f6-g5 b4-c5 d6xb4 a3xc5 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 b2-a3 c7-b6 c1-b2 b6xd4 c3xe5 a7-b6",
        "g3-f4 b6-a5 c3-b4 a5xc3 d2xb4 f6-g5 b4-c5 d6xb4 a3xc5 g7-f6 b2-c3 g5-h4 a1-b2 f6-g5 b2-a3 h8-g7 c3-d4 c7-b6 a3-b4 b6-a5",
        "g3-f4 b6-a5 c3-d4 d6-c5 b2-c3 c7-b6 f4-e5 a5-b4 a1-b2 f6-e5 b2-c3 g7-f6 d2-e3 e5-f4 c3-d4 e7-d6 a3-b4 d8-c7 e1-d2 h8-g7",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 f2xh4 h8-g7 b2-c3 g7-f6 h2-g3 a7-b6 a1-b2 b6-c5 c3-d4 c7-b6 b2-c3 b8-a7 g3-f4 c5-b4",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 c7-b6 b8-c7 b2-c3 b6-c5 c3-b4 a5xc3 d2xb4 a7-b6 f2-e3 b6-a5 f4-g5",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 c7-b6 b8-c7 b2-c3 b6-c5 c3-b4 a5xc3 d2xb4 e7-f6 c1-d2 f6xd4 f4-g5",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 c7-b6 d4-e5 b8-c7 b2-c3 b6-c5 c3-b4 a5xc3 d2xb4 a7-b6 f2-e3 b6-a5",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 c7-b6 d4-e5 b8-c7 b2-c3 b6-c5 c3-b4 a5xc3 d2xb4 e7-f6 c1-d2 f6xd4",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 c7-b6 d4-e5 b8-c7 b2-c3 e7-f6 c3-b4 a5xc3 d2xb4 f6xd4 b4-c5 d6xb4",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 c7-b6 d4-e5 b8-c7 f4-g5 h6xf4 e5xg3 b6-c5 g3-f4 g7-f6 b2-c3 c5-b4",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 c7-b6 d4-e5 d6-c5 e5-d6 c5-b4 a3xc5 b6xd4 f4-g5 e7xc5 d2-c3 h6xf4",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 c7-b6 d4-e5 d6-c5 e5-d6 c5-d4 d6-c7 b8xd6 f4-g5 h6xf4 d2-e3 f4xd2",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 c7-b6 d6-c5 e5-d6 c5-d4 d6-c7 b8xd6 f4-g5 h6xf4 d2-e3 f4xd2 e1xc7",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 d6-c5 d4xb6 a7xc5 b2-c3 c7-d6 c1-b2 g7-f6 f2-e3 f6-e5 g1-h2 e5xg3",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 d6-c5 d4xb6 a7xc5 b2-c3 g7-f6 c1-b2 c7-b6 f4-e5 f6xd4 c3xe5 h6-g5",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 d6-c5 d4xb6 a7xc5 b2-c3 g7-f6 c1-b2 c7-d6 c3-b4 a5xc3 b2xb6 d6-c5",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 d6-c5 d4xb6 a7xc5 b2-c3 g7-f6 c1-b2 c7-d6 f2-e3 f6-e5 g1-f2 e5xg3",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 d6-c5 d4xb6 a7xc5 b2-c3 g7-f6 c1-b2 c7-d6 f2-e3 f6-e5 g1-h2 e5xg3",
        "g3-f4 b6-a5 c3-d4 f6-e5 d4xf6 g7xg3 h2xf4 h8-g7 e3-d4 d6-c5 d4xb6 a7xc5 b2-c3 g7-f6 c3-b4 a5xc3 d2xd6 c7xg3 f2xh4 e7-d6",
        "g3-f4 b6-a5 c3-d4 g5-h4 d4-c5 f6-g5 c5-b6 g7-f6 e7-d6 b2-c3 d6-c5 a1-b2 c7-d6 b2-a3 f6-e5 c3-b4 h8-g7 b4-a5 d8-c7 c1-b2",
        "g3-f4 b6-a5 e3-d4 d6-e5 c7-d6 h2-g3 a7-b6 b6-c5 c3-d4 g7-f6 b2-c3 f8-g7 d2-e3 f6-g5 g1-h2 h8-g7 g7-f6 e1-f2 d6-e5 d4-c5",
        "g3-f4 b6-a5 e3-d4 d6-e5 c7-d6 h4-g5 d6-c5 c5-b4 g3-f4 b8-c7 h2-g3 g7-h6 g1-f2 h8-g7 f2-e3 g7-f6 e3-d4 f6-g5 d4-e5 d8-e7",
        "g3-f4 b6-a5 f2-g3 f6-g5 g1-f2 g5-h4 c3-d4 a5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 a1-b2 b4-a3 b2-c3 a7-b6 f4-e5 e7-f6",
        "g3-f4 b6-a5 h2-g3 a7-b6 g3-h4 d6-e5 f4xd6 c7xe5 a3-b4 e7-d6 e3-d4 b8-a7 b2-a3 e5-f4 f2-e3 f8-e7 e3xg5 h6xf4 g1-h2 b6-c5",
        "g3-f4 b6-a5 h2-g3 a7-b6 g3-h4 d6-e5 f4xd6 c7xe5 c3-b4 a5xc3 b2xd4 e5xc3 d2xb4 f6-g5 h4xf6 g7xe5 a1-b2 e7-d6 b2-c3 d8-c7",
        "g3-f4 b6-c5 b2-c3 g5-h4 c3-d4 f6-g5 d4xb6 c7xc3 d2xb4 d8-c7 g7-f6 b4-a5 f6-e5 b2-c3 e5xg3 h2xf4 e7-f6 c3-d4 d6-e5 f4xd6",
        "g3-f4 b6-c5 b2-c3 g5-h4 c3-d4 f6-g5 g7-f6 d8-c7 b4-a5 f6-e5 c1-d2 d6-e5 b2-c3 g5-f4 f2-g3 f8-g7 c3-d4 e7-d6 g3-f4 f6-g5",
        "g3-f4 b6-c5 c3-b4 f6-e5 b2-c3 e5xg3 h2xf4 g7-f6 c3-d4 h8-g7 d4xb6 c7xc3 d2xb4 f6-e5 f2-g3 g7-f6 g3-h4 e5xg3 h4xf2 f6-e5",
        "g3-f4 b6-c5 f2-g3 c5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 a7-b6 g1-f2 b4-a3 e3-d4 b6-c5 d4xb6 a5xc7 b2-c3 g7-f6 f2-e3",
        "g3-f4 b6-c5 f2-g3 c5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 b4-a3 g1-f2 a5-b4 f2-e3 a7-b6 a1-b2 b4-c3 d2xb4 a3xc5 c1-d2",
        "g3-f4 b6-c5 f2-g3 c5-b4 a3xc5 d6xb4 b2-a3 c7-d6 a3xc5 d6xb4 b4-a3 g1-f2 a7-b6 e3-d4 b6-c5 d4xb6 a5xc7 b2-c3 g7-f6 f4-g5",
        "g3-f4 b6-c5 f2-g3 c5-b4 b2-a3 c7-b6 a5-b4 e3-d4 b4-a3 a1-b2 a7-b6 d4-c5 f4-g5 g7-f6 c3-d4 e7-d6 b2-c3 h8-g7 e1-f2 f8-e7",
        "g3-f4 b6-c5 f2-g3 g7-f6 f4-g5 h2-g3 c7-b6 b8-c7 f4-g5 d6-e5 g5-h6 c7-d6 b2-c3 c5-b4 a7-b6 d2-e3 b6-c5 g3-f4 c5-b4 e1-d2",
        "g3-f4 b6-c5 f2-g3 g7-f6 f4-g5 h6xf4 g3xg7 f8xh6 b2-c3 c7-b6 c5-b4 a3xc5 b6xf2 g1xe3 a7-b6 g3-f4 b6-c5 a1-b2 e7-f6 b2-a3",
        "g3-f4 b6-c5 f4-g5 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 h8-g7 c7-b6 h2-g3 g7-f6 g1-h2 c5-b4 a3xc5 d6xb4 b2-a3 b4-c3 d2xb4",
        "g3-f4 b6xd4 c3xe5 f6xd4 e3xc5 g7-f6 b2-c3 f6-g5 d2-e3 g5-h4 h8-g7 c3-d4 c7-b6 a1-b2 b6-a5 b2-c3 g7-f6 f4-g5 h6xf4 e3xg5",
        "g3-f4 b6xd4 c3xe5 f6xd4 e3xc5 g7-f6 b2-c3 f6-g5 d2-e3 g5-h4 h8-g7 c3-d4 e7-f6 f4-g5 h6xf4 e3xe7 f8xb4 a3xc5 g7-f6 a1-b2",
        "g3-f4 b6xd4 c3xe5 f6xd4 e3xc5 g7-f6 b2-c3 f6-g5 f2-e3 g5-h4 a1-b2 h8-g7 c3-d4 g7-f6 f4-g5 h6xf4 e3xg5 c7-b6 d2-e3 f8-g7",
        "g3-f4 b6xd4 c3xe5 f6xd4 e3xc5 g7-f6 f2-e3 c7-b6 g1-f2 b6xd4 e3xc5 f6-g5 f2-e3 h8-g7 h2-g3 g5-h4 e3-d4 h4xf2 e1xg3 g7-f6",
        "g3-f4 b6xd4 c3xe5 f6xd4 e3xc5 g7-f6 f2-e3 f6-g5 e3-d4 g5xe3 d4xf2 h8-g7 b2-c3 g7-f6 f2-g3 h6-g5 a1-b2 g5-h4 c3-d4 h4xf2",
        "g3-f4 b6xd4 e3xc5 d6xb4 c3xa5 g7-f6 b2-c3 e7-d6 h2-g3 f6-g5 g5xe3 d2xf4 d6-e5 f4xd6 c7xe5 g1-h2 f8-g7 f2-g3 e5-f4 g3xe5",
        "g3-f4 c3-b4 b4-c5 e3xc5 f6-g5 g7-f6 b6xd4 d6xb4 a3xc5 f2xd4 h2-g3 d4xf6 g5xe3 f8-g7 f6-e5 g7xe5 d2-e3 c1-d2 g3xe5 e5xc7",
        "g3-f4 c3-b4 d2-c3 c3-d4 f6-g5 b6-c5 g7-f6 d6-e5 d4xb6 f4xd6 b2xb6 e3-f4 c7xc3 e7xc5 a7xc5 g5xe3 f2xb6 b6-c7 a3-b4 b4-c5",
        "g3-f4 c3-d4 d2-c3 c1-d2 f6-g5 d6-c5 g5-h4 g7-f6 c3-b4 d4xb6 b4xd6 h2xf4 b6-a5 a7xc5 c7xg3 f6-e5 f4xd6 d2-c3 c3-b4 b2xb6",
        "g3-f4 c3-d4 d6-c5 d2-e3 c7-d6 b2-c3 b6-a5 a1-b2 a7-b6 c1-d2 b6-c5 c3-d4 c7-b6 d4-e5 b6-a5 b2-c3 g7-f6 c3-d4 f6-g5 d2-c3",
        "g3-f4 c7-b6 c3-d4 f6-g5 b2-a3 b6-a5 f2-e3 g7-f6 a1-b2 f6-g5 c1-d2 e7-f6 b2-c3 f8-e7 e1-f2 g5-h4 f4-e5 h6-g5 g5-f4 f2-e3",
        "g3-f4 d6-c5 b2-c3 c5-b4 a3xc5 b6xb2 a1xc3 a7-b6 c1-b2 b6-c5 c7-d6 c3-d4 g7-f6 d4xb6 a5xc7 f4-e5 d6xf4 e3xg5 h6xf4 f2-e3",
        "g3-f4 d6-c5 b2-c3 g5-h4 c3-b4 e7-d6 b4-a5 d8-e7 f2-g3 h6-g5 d6-e5 d2-c3 c7-d6 a7-b6 c5-b4 c1-b2 b8-c7 e7-d6 g1-f2 f2-g3",
        "g3-f4 d6-c5 c3-b4 e7-d6 b4-a5 f8-e7 b2-c3 c5-b4 d6-c5 h2-g3 c5-b4 f4-e5 g3-h4 b4-a3 f4-g5 g1-h2 e7-d6 c7-b6 a7-b6 a1-b2",
        "g3-f4 d6-c5 c3-b4 e7-d6 h2-g3 f6-g5 g3-h4 b6-a5 h4xf6 g7xg3 f2xh4 a5xc3 b2xb6 c7xa5 a1-b2 h8-g7 b2-c3 g7-f6 e3-f4 f8-e7",
        "g3-f4 d6-c5 c3-d4 f6-g5 d2-c3 g5-h4 c3-b4 c7-d6 b4-a5 b8-c7 f2-g3 h4xf2 e1xg3 g7-f6 g3-h4 f8-g7 h2-g3 f6-e5 d4xf6 g7xe5",
        "g3-f4 d6-c5 c3-d4 f6-g5 h2-g3 g5-h4 b2-c3 g7-f6 c3-b4 f6-e5 d4xf6 e7xg5 b4xd6 c7xe5 f4xd6 d8-e7 a1-b2 e7xc5 b2-c3 c5-d4",
        "g3-f4 d6-c5 d2-e3 f6-g5 c1-d2 g7-f6 c3-b4 c7-d6 d2-c3 b6-a5 d4xb6 a5xc7 b4-a5 a7-b6 c3-b4 b6-c5 b2-c3 f6-e5 a1-b2 e5xg3",
        "g3-f4 d6-c5 h2-g3 c7-d6 c3-b4 f6-e5 b4-a5 d8-c7 b2-c3 e5-d4 c3xe5 h6-g5 f4xh6 a1-b2 g7-f6 b2-c3 c5-b4 a3xc5 c1xa3 c7-d6",
        "g3-f4 d6-c5 h2-g3 e7-d6 g3-h4 f6-e5 f2-g3 e5-d4 c3xe5 f8-e7 g7xe5 e1-f2 h8-g7 d2-c3 g7-f6 c3-b4 c5-d4 e3xc5 b6xd4 b2-c3",
        "g3-f4 d6-e5 f4xd6 c7xe5 h2-g3 e5-d4 e3xc5 b6xd4 g3-f4 b8-c7 c7-b6 a3-b4 a5xc3 d2xb4 b6-c5 b4xd6 e7xc5 f2-g3 a7-b6 f4-g5",
        "g3-f4 d6-e5 h2-g3 h6-g5 c3-b4 e5-f4 c1-d2 b8-c7 d2-e3 c7-b6 a1-b2 h8-g7 e1-d2 d8-c7 b4-a5 g7-f6 g1-h2 a7-b6 h2-g3 f8-g7",
        "g3-f4 d6xb4 c3xa5 f6-g5 b2-c3 g7-f6 c3-d4 h8-g7 a1-b2 g5-h4 f4-g5 h6xf4 e3xg5 h4-g3 h2xf4 f6xh4 f2-e3 g7-h6 b2-c3 f8-g7",
        "g3-f4 e3-d4 g7-f6 d4-c5 f4-e5 h8-g7 b2-c3 g7-f6 a3-b4 h6-g5 e1-f2 f6-e5 a1-b2 g5-h4 b2-a3 f8-g7 b4-a5 e5-f4 a3-b4 g7-f6",
        "g3-f4 e3-d4 g7-f6 f2-g3 f6-g5 g5-h4 e1-f2 h8-g7 b2-c3 g7-f6 f4-g5 d6-e5 f2-e3 e5-f4 g5-h6 f4-g3 f8-g7 c3-b4 g3-h2 e3-f4",
        "g3-f4 e3-d4 g7-f6 f4-e5 f2-g3 b2-c3 e7-d6 a1-b2 d6-e5 h2-g3 h6-g5 b2-a3 g5-f4 g1-h2 f8-g7 a3-b4 c7-d6 c1-b2 g7-h6 b2-a3",
        "g3-f4 e3-d4 g7-f6 f4-e5 f2-g3 c1-d2 e7-d6 b2-c3 f8-e7 h2-g3 h6-g5 a1-b2 g5-h4 g1-f2 f6-g5 d4-c5 e7-d6 d2-e3 d6-e5 b2-a3",
        "g3-f4 e5xg3 h2xf4 f6-g5 d2-e3 g5-h4 c1-d2 b6-c5 c3-d4 g7-f6 d4xb6 a7xc5 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 b8-a7 d2-e3 e5-f4",
        "g3-f4 e5xg3 h2xf4 f6-g5 d2-e3 g7-f6 c3-d4 g5-h4 c1-d2 f6-g5 e7-d6 g1-h2 f8-g7 f4-e5 d6xf4 f2-g3 h4xf2 e1xe5 g5-h4 a3-b4",
        "g3-f4 e7-d6 f4-e5 b2-c3 g7-f6 h8-g7 c3-b4 d6-e5 e3-d4 h6-g5 d2-e3 g5-h4 a3-b4 f6-e5 e3-d4 g7-f6 a1-b2 f6-e5 b2-c3 c7-b6",
        "g3-f4 f2-g3 a7-b6 g3-h4 b6-a5 h2-g3 f6-g5 g3-h4 f8-e7 d2-c3 c7-b6 c3-d4 b6-c5 b2-c3 d8-e7 e1-f2 e7-f6 f2-g3 g5-h4 e3-d4",
        "g3-f4 f2-g3 a7-b6 g3-h4 d6-c5 h2-g3 b6-a5 f6-g5 g3-h4 f8-e7 f4-e5 g5-h4 e5-f6 c5-d4 h6-g5 f6-g7 c7-d6 h2-g3 h8-g7 b2-c3",
        "g3-f4 f6-e5 a1-b2 b6-c5 c3-d4 g7-f6 f6-e5 c3-b4 e3-d4 h8-g7 c1-b2 g7-f6 b2-c3 c7-b6 b4-a5 b6-c5 c3-b4 f6-e5 f2-g3 e7-f6",
        "g3-f4 f6-e5 c1-d2 b6-a5 g1-h2 c7-b6 f2-g3 f8-e7 e3-f4 c5-b4 d2-e3 g7-h6 e1-f2 h8-g7 b2-c3 g7-f6 f2-e3 b6-c5 a1-b2 d8-c7",
        "g3-f4 f6-e5 c3-b4 e5xg3 f2xf6 g7xe5 d2-c3 e5-f4 e3xg5 h6xf4 d6xd2 c1xg5 b6-c5 g1-h2 h8-g7 h2-g3 d8-e7 g3-h4 g7-f6 e1-d2",
        "g3-f4 f6-e5 c3-d4 b6-a5 b2-c3 g7-f6 f4-e5 c7-d6 g5-h6 a7-b6 f2-e3 b6-c5 c3-d4 c7-b6 a1-b2 b6-a5 b2-c3 b8-a7 g1-f2 a7-b6",
        "g3-f4 f6-e5 c3-d4 b6-a5 b2-c3 g7-f6 f4-g5 c7-b6 g5-h6 b6-c5 f2-e3 c7-b6 a1-b2 b6-a5 g1-h2 h8-g7 h2-g3 f6-e5 g3-f4 g7-f6",
        "g3-f4 f6-e5 c3-d4 b6-a5 f4-g5 g7-f6 c7-b6 f2-e3 b6-c5 g5-h6 c7-b6 g1-h2 b6-a5 a1-b2 h8-g7 c3-d4 a5-b4 b2-c3 d6-e5 h2-g3",
        "g3-f4 f6-e5 c3-d4 g7-h6 a1-b2 b6-a5 b2-c3 d6-c5 f4-g5 c7-d6 g5-f6 c5-b4 h2-g3 f8-g7 f2-e3 e3-d4 e5-f4 e1-f2 d8-e7 f2-g3",
        "g3-f4 f6-e5 c3-d4 h8-g7 e3-f4 f8-e7 e7-f6 b2-c3 b6-c5 d2-e3 c7-b6 f4-g5 d8-e7 c1-d2 e7-f6 g1-f2 f6-e5 f2-g3 g7-f6 a1-b2",
        "g3-f4 f6-e5 e3-f4 b6-c5 c3-d4 c7-b6 b2-c3 d6-e5 d2-e3 b6-c5 h2-g3 h8-g7 e3-f4 e7-d6 a3-b4 c3-d4 c3-d4 b6-a5 d4-c5 d2-c3",
        "g3-f4 f6-e5 f2-g3 g7-f6 e3-d4 b6-a5 d2-e3 c7-b6 c1-d2 b6-c5 d4xb6 a5xc7 e3-d4 c7-b6 d2-e3 b6-a5 g1-f2 a7-b6 e1-d2 b6-c5",
        "g3-f4 f6-e5 f2-g3 g7-f6 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 g3-h4 e5xg3 h4xf2 h6-g5 h2-g3 d6-e5 b4-a5 g5-h4 a3-b4 f6-g5",
        "g3-f4 f6-e5 f2-g3 g7-f6 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 f6-g5 b2-c3 g5xe3 d2xf4 c5-d4 a1-b2 h8-g7 c1-d2 e7-f6 g3-h4 e5xg3",
        "g3-f4 f6-e5 f2-g3 g7-f6 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 f6-g5 b2-c3 g5xe3 d2xf4 e7-f6 b4-a5 c5-d4 a1-b2 f6-g5 e1-d2 g5xe3",
        "g3-f4 f6-e5 f2-g3 g7-f6 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 f6-g5 b2-c3 g5xe3 d2xf4 h8-g7 c1-d2 e7-f6 b4-a5 d8-e7 c3-b4 c7-b6",
        "g3-f4 f6-e5 f2-g3 g7-f6 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 f6-g5 b2-c3 g5xe3 d2xf4 h8-g7 c1-d2 e7-f6 b4-a5 d8-e7 c3-b4 f6-g5",
        "g3-f4 f6-e5 f2-g3 g7-f6 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 f6-g5 g5xe3 d2xf4 e7-f6 b4-a5 c5-d4 a1-b2 f6-g5 e1-d2 g5xe3 d2xf4",
        "g3-f4 f6-e5 f2-g3 g7-f6 g3-h4 e5xg3 h4xf2 f6-e5 c3-b4 h8-g7 b4-a5 e5-f4 e3xg5 h6xf4 b2-c3 g7-f6 c3-b4 d6-e5 a1-b2 b6-c5",
        "g3-f4 f6-e5 f2-g3 g7-f6 g3-h4 e5xg3 h4xf2 h6-g5 h2-g3 g5-h4 c3-d4 d6-c5 b2-c3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 a1-b2 f6-e5",
        "g3-f4 f6-e5 h2-g3 b6-a5 e3-d4 c7-b6 d4xf6 e7xe3 d2xf4 g7-f6 f8-g7 c1-d2 d6-e5 f4xd6 f6-g5 h4xf6 g7xc7 f2-g3 h8-g7 g3-h4",
        "g3-f4 f6-e5 h2-g3 b6-a5 e3-d4 c7-b6 d4xf6 e7xe3 d2xf4 g7-f6 g3-h4 f8-e7 f2-e3 f6-g5 h4xf6 e7xg5 c3-d4 b6-c5 h8-g7 d4-e5",
        "g3-f4 f6-e5 h2-g3 b6-c5 c1-b2 g7-f6 g1-h2 c7-b6 f4-g5 g3-f4 f6-e5 f4-g5 b8-c7 g5-h6 c5-d4 d2-e3 b6-c5 h4-g5 a7-b6 e3-f4",
        "g3-f4 f6-e5 h2-g3 b6-c5 c3-b4 a7-b6 b4-a5 b8-a7 g1-h2 g7-f6 b2-c3 c5-d4 h8-g7 c3-b4 c5-d4 e3xc5 b6xd4 d2-c3 d4xb2 a1xc3",
        "g3-f4 f6-e5 h2-g3 b6-c5 c3-b4 g7-f6 b4-a5 f8-g7 h8-g7 g1-h2 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 f2xf6 f8-e7 f8-g7 b2-c3 e7xg5",
        "g3-f4 f6-e5 h2-g3 b6-c5 c3-d4 e5xc3 b2xb6 a7xc5 g3-h4 g7-f6 f4-g5 h6xf4 e3xg5 c7-b6 a1-b2 h8-g7 g1-h2 b6-a5 g5-h6 d6-e5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 b6-c5 b4xd6 e7xc5 b2-c3 a7-b6 a1-b2 c7-d6 e3-f4 g7-f6 f2-g3 f6-e5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b2-a3 b6-c5 a1-b2 b8-c7 e3-f4 c7-b6 b4-a5 d8-c7 f2-g3 g7-f6",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b2-a3 b6-c5 a1-b2 b8-c7 e3-f4 g7-f6 f4-e5 f6xd4 f2-g3 h2xf4",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b2-a3 b6-c5 a1-b2 g7-f6 b2-c3 a7-b6 c3-d4 h8-g7 b4-a5 d6-e5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b2-a3 b6-c5 a1-b2 g7-f6 b4-a5 f6-e5 b2-c3 c5-b4 a3xc5 d6xb4",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b2-a3 b6-c5 a1-b2 g7-f6 b4-a5 h8-g7 e3-f4 b8-c7 d2-e3 f6-e5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b2-a3 b6-c5 a1-b2 g7-f6 b8-c7 e3-f4 c7-b6 g7-f6 e7-f6 f4-e5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b2-a3 b6-c5 a1-b2 g7-f6 d2-c3 h8-g7 e1-d2 a7-b6 b4-a5 d6-e5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b2-a3 b6-c5 a1-b2 g7-f6 e3-d4 c5xe3 f2xd4 d6-c5 d4xb6 a7xc5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b4-a5 d6-e5 a5xc7 b8xd6 b2-c3 e5-f4 e3xg5 g7-f6 a1-b2 f6xh4",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b4-c5 g7-f6 e3-d4 c7-b6 d2-e3 d8-c7 c1-d2 c7-d6 b2-a3 d6xb4",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b6-c5 a1-b2 b8-c7 e3-f4 g7-f6 f4-e5 f6xd4 f2-g3 h2xf4 d2-e3",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b6-c5 a1-b2 g7-f6 b4-a5 f6-e5 b2-c3 c5-b4 a3xc5 d6xb4 e3-d4",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b6-c5 a1-b2 g7-f6 b4-a5 h8-g7 e3-f4 b8-c7 d2-e3 f6-e5 f2-g3",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 c7-d6 b6-c5 a1-b2 g7-f6 e3-d4 c5xe3 f2xd4 d6-c5 d4xb6 a7xc5 b4xd6",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 b2-c3 f6-e5 e3-d4 e7-f6 b4-c5 b6-a5 c5-d6 a5-b4 d6xf4 f6-g5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 b2-c3 f6-e5 e3-d4 e7-f6 b4-c5 b6-a5 c5-d6 e5-f4 f2-e3 c7xe5",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 b2-c3 f6-e5 e3-d4 e7-f6 b4-c5 d8-e7 a1-b2 b6-a5 h6-g7 f8xh6",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 b2-c3 f6-e5 e3-d4 e7-f6 b4-c5 d8-e7 a1-b2 c7-d6 b2-a3 d6xb4",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 b2-c3 f6-e5 e3-d4 e7-f6 b4-c5 d8-e7 a1-b2 h8-g7 f2-e3 e5-f4",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 b2-c3 h8-g7 a1-b2 f6-e5 b4-a5 g7-f6 b2-a3 c7-d6 a5xc7 d8xb6",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 b4-c5 b6xd4 e3xc5 f6-e5 b2-a3 c7-b6 d2-e3 b6xd4 e3xc5 h8-g7",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 b4-c5 b6xd4 e3xc5 f6-e5 d2-c3 c7-d6 c3-b4 b8-c7 c1-d2 c7-b6",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 f6-e5 e3-d4 e7-f6 b4-c5 d8-e7 a1-b2 b6-a5 h6-g7 f8xh6 c5-b6",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 f6-e5 e3-d4 e7-f6 b4-c5 d8-e7 a1-b2 c7-d6 b2-a3 d6xb4 c3xc7",
        "g3-f4 f6-e5 h2-g3 e5-d4 c3xe5 h6-g5 f4xh6 d6xh2 a3-b4 g7-f6 h8-g7 a1-b2 f6-e5 b4-c5 b6xd4 e3xc5 g7-f6 c3-b4 c7-b6 d2-e3",
        "g3-f4 f6-e5 h2-g3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 c5-b6 a7xc5 f4-e5 h6-g5 e5xc3 g5-h4 c3-d4 c7-d6 d4xb6 a5xc7",
        "g3-f4 f6-e5 h2-g3 g7-f6 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 c5-d6 e7xc5 f4-e5 h6-g5 e5xc3 g5-h4 g3-f4 d8-e7 f4-g5 c7-d6",
        "g3-f4 f6-e5 h2-g3 g7-f6 c3-b4 e5-d4 b6-a5 b4-c5 d6xb4 a3xc5 e5-d4 c5-d6 e7xc5 f4-e5 f6-g5 b4-c5 e3xc5 b6xd4 d2-e3 c7-b6",
        "g3-f4 f6-e5 h2-g3 h6-g5 f4xh6 e5-d4 c3xe5 d6xh2 a3-b4 g7-f6 b2-c3 b6-a5 b4-c5 c7-d6 a1-b2 d6xb4 b2-a3 f6-e5 a3xc5 h8-g7",
        "g3-f4 f6-g5 b2-c3 e7-d6 c3-d4 g7-f6 d4-c5 f6-e5 h2-g3 a7-b6 a1-b2 h8-g7 b2-c3 g7-f6 c3-b4 b6-c5 e3-d4 g5-f4 g1-h2 f4-e3",
        "g3-f4 f6-g5 b2-c3 e7-d6 c3-d4 g7-f6 d4-e5 f6xd4 e3xe7 g5xe3 d2xf4 f8xd6 c1-d2 d6-e5 f4xd6 c7xe5 a5xc7 b8xd6 d2-c3 a7-b6",
        "g3-f4 f6-g5 b2-c3 g5-h4 a1-b2 g7-f6 d4-e5 h8-g7 b2-c3 e7-d6 f2-e3 f8-e7 e3-d4 g7-f6 h2-g3 d6-c5 f4-g5 c7-d6 c3-d4 e7-f6",
        "g3-f4 f6-g5 b2-c3 g7-f6 c1-b2 c7-d6 f4-e5 d6xf4 d4-c5 b6xd4 c3xg3 h8-g7 e3-d4 e7-d6 g3-h4 a7-b6 f2-g3 b6-c5 d4xb6 a5xc7",
        "g3-f4 f6-g5 b2-c3 g7-f6 c3-d4 h8-g7 f2-g3 g5-h4 e7-d6 f4-e5 d4-c5 g7-f6 c3-d4 c7-d6 d2-c3 d6-c5 g3-f4 f6-g5 c3-d4 c5-b4",
        "g3-f4 f6-g5 c3-b4 b6-a5 b4-c5 c7-d6 e7-d6 a1-b2 a7-b6 b2-c3 b8-a7 c3-d4 b6-c5 f2-g3 h8-g7 g3-h4 g7-f6 c1-d2 c7-b6 f4-e5",
        "g3-f4 f6-g5 c3-b4 b6-c5 b2-c3 g7-f6 b4-a5 g5-h4 f4-g5 h6xf4 e3xg5 f6-e5 g5-h6 c5-b4 a3xc5 d6xb4 f2-e3 h8-g7 e1-f2 g7-f6",
        "g3-f4 f6-g5 c3-b4 b6-c5 b2-c3 g7-f6 c3-d4 h8-g7 d4xb6 c7xc3 d2xb4 g5-h4 b4-a5 f6-g5 a1-b2 d8-c7 b2-c3 g7-f6 c3-d4 d6-e5",
        "g3-f4 f6-g5 c3-b4 b6-c5 b2-c3 g7-f6 c3-d4 h8-g7 d4xb6 c7xc3 d2xb4 g5-h4 b4-a5 f6-g5 a1-b2 d8-c7 g7-f6 f2-g3 h4xd4 a3-b4",
        "g3-f4 f6-g5 c3-b4 b6-c5 b2-c3 g7-f6 c3-d4 h8-g7 d4xb6 c7xc3 d2xb4 g5-h4 b4-a5 f6-g5 a1-b2 e7-f6 a3-b4 d8-c7 b4-c5 d6xb4",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 a1-b2 e5xg3 f2xf6 e7xg5 e1-f2 g5-h4 b4-c5 b6xd4 e3xe7 f8xd6 c3-b4 a7-b6 d2-e3 h4-g3",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 b4-a5 e5xg3 f2xf6 e7xg5 g5xe3 d2xf4 h8-g7 h2-g3 g7-f6 c1-d2 d6-c5 g3-h4 c5-b4 a3xc5",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 c1-b2 e5xg3 f2xf6 e7xg5 c3-d4 g5-h4 b4-c5 d6xb4 a3xc5 h6-g5 h2-g3 h4xf2 e1xg3 g5-h4",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 c1-b2 e5xg3 f2xf6 e7xg5 c3-d4 g5-h4 b4-c5 d6xb4 a3xc5 h8-g7 g1-f2 c7-d6 c5xe7 f8xd6",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 c1-b2 e5xg3 f2xf6 e7xg5 c3-d4 g5-h4 g1-f2 h6-g5 b4-c5 d6xb4 a3xc5 g5-f4 e3xg5 h4xf6",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 c1-b2 e5xg3 f2xf6 e7xg5 c3-d4 h8-g7 b4-c5 d6xb4 a3xc5 c7-d6 c5xe7 f8xd6 h2-g3 g7-f6",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 c1-b2 e5xg3 f2xf6 e7xg5 c3-d4 h8-g7 g1-f2 b6-c5 d4xb6 c7xc3 b2xd4 g7-f6 f2-g3 a7-b6",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 c1-b2 e5xg3 f2xf6 e7xg5 c3-d4 h8-g7 g1-f2 g7-f6 f2-g3 b6-c5 d4xb6 c7xc3 b2xd4 a7-b6",
        "g3-f4 f6-g5 c3-b4 g7-f6 b2-c3 f6-e5 c1-b2 e5xg3 f2xf6 e7xg5 c3-d4 h8-g7 g1-f2 g7-f6 f2-g3 g5-h4 b4-c5 d6xb4 a3xc5 h4xf2",
        "g3-f4 f6-g5 c3-b4 g7-f6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 f8-g7 h2-g3 f6-e5 d4xf6 g7xe5 d2-e3 h8-g7 e3-f4 e7-f6",
        "g3-f4 f6-g5 c3-b4 g7-f6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 d2-e3 h6-g5 h2-g3 g7-h6 c1-d2 g5-h4 g3-f4 f6-g5",
        "g3-f4 f6-g5 c3-b4 g7-f6 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h8-g7 h2-g3 f6-g5 e1-f2 g7-f6 d2-e3 c7-b6 g3-h4 g5-f4",
        "g3-f4 f6-g5 c3-b4 g7-f6 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 h8-g7 d2-e3 h6-g5 h2-g3 g7-h6 c1-d2 c7-b6 g3-f4 e7-d6",
        "g3-f4 f6-g5 c3-b4 g7-f6 b4-c5 h6-g5 g1-f2 h8-g7 a3-b4 e7-d6 b2-a3 g7-h6 b4-c5 f6-e5 d2-e3 h6-g5 c1-d2 g5-f4 f2-e3 b8-a7",
        "g3-f4 f6-g5 c3-b4 g7-f6 h2-g3 b6-a5 b4-c5 d6xb4 a3xc5 g5-h4 f6-g5 c3-b4 a5xc3 d2xb4 c7-d6 a1-b2 d8-c7 b2-c3 h8-g7 e3-d4",
        "g3-f4 f6-g5 c3-b4 g7-f6 h2-g3 g5-h4 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 f6-g5 b2-c3 g5xe3 d2xf4 h8-g7 a1-b2 e7-f6 e1-d2 f6-g5",
        "g3-f4 f6-g5 c3-d4 d6-c5 d2-c3 g5-h4 c3-b4 b6-a5 d4xb6 a5xc3 b2xd4 c7xa5 a1-b2 d8-c7 b2-c3 e7-d6 e1-d2 a7-b6 f2-g3 h4xf2",
        "g3-f4 f6-g5 c3-d4 d6-c5 d2-c3 g7-f6 f2-g3 g5-h4 e1-d2 h4xf2 c5xa3 d4-c5 f2xd4 c3xg7 h8xf6 d2-c3 b6xd4 c3xg7 e7-f6 g7xe5",
        "g3-f4 f6-g5 c3-d4 g5-h4 b2-c3 e7-d6 c1-b2 d6-c5 f4-e5 h6-g5 g5-f4 d8-e7 a1-b2 d6-c5 d2-e3 f6-e5 b2-c3 e7-d6 e3-d4 c3-b4",
        "g3-f4 f6-g5 c3-d4 g7-f6 d4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g5xe3 f2xd4 h6-g5 e1-f2 h8-g7 c5-b6 a7xe3 d2xh6 f6-e5 f2-e3 g7-f6",
        "g3-f4 f6-g5 c3-d4 g7-f6 d4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g5xe3 f2xd4 f8-g7 d2-e3 f6-e5 d4xf6 g7xe5 h2-g3 h6-g5 e3-d4 e5xc3",
        "g3-f4 f6-g5 d2-e3 g7-f6 c3-d4 g5-h4 a3-b4 f8-g7 f6-g5 b2-c3 g7-f6 a1-b2 h8-g7 e1-d2 g5-f4 b4-a5 g7-h6 b2-a3 f6-g5 c3-b4",
        "g3-f4 f6-g5 d4-c5 a5-b4 e7-f6 f6-g5 f2-e3 d8-c7 b2-c3 g7-f6 c3-d4 c7-d6 a1-b2 h8-g7 b2-c3 a7-b6 c3-b4 f8-e7 b4-c5 b8-a7",
        "g3-f4 f6-g5 d4-c5 a7-b6 a3-b4 b6-a5 a1-b2 c7-b6 b2-a3 b6-c5 f2-e3 e7-d6 a3-b4 g7-f6 b4-a5 d8-e7 h2-g3 d6-e5 g3-f4 c7-d6",
        "g3-f4 f6-g5 f2-g3 g5-h4 e3-d4 h8-g7 g7-f6 g3-h4 f6-g5 d6-e5 e3-f4 d8-e7 e1-f2 b6-a5 f2-g3 a7-b6 g3-h4 b6-c5 c3-d4 g7-f6",
        "g3-f4 f6-g5 h2-g3 g7-f6 g1-h2 c7-d6 a7-b6 b2-c3 e7-d6 d2-e3 f8-g7 e1-f2 b6-a5 f2-g3 h6-g5 c3-b4 g3-f4 d6-c5 e3-f4 b8-c7",
        "g3-f4 f6-g5 h4xf6 g7xg3 f2xh4 f8-e7 h4-g5 h6xf4 e3xg5 d6-e5 g5-h6 e7-d6 d2-e3 b6-c5 c3-b4 a7-b6 b4-a5 b8-a7 e1-d2 e5-d4",
        "g3-f4 f6-g5 h4xf6 g7xg3 h2xf4 b6-a5 c3-d4 c7-d6 f2-g3 d6-c5 d4xb6 a5xc7 b2-c3 h8-g7 e3-d4 g7-f6 a1-b2 f6-e5 d4xf6 e7xe3",
        "g3-f4 f6-g5 h4xf6 g7xg3 h2xf4 b6-a5 e3-d4 c7-d6 d4-e5 b8-c7 f8-g7 f4-g5 h6xf4 e5xg3 g7-f6 g3-f4 h8-g7 h2-g3 g7-h6 f2-e3",
        "g3-f4 f6-g5 h8-g7 c1-d2 g7-f6 c3-d4 c7-b6 b6-a5 c3-d4 d6-c5 b2-c3 e7-d6 c3-d4 b8-a7 a1-b2 f8-e7 b2-c3 f6-e5 f2-g3 c7-b6",
        "g3-f4 f6-g5 h8-g7 c3-d4 g7-f6 b2-c3 c7-d6 b6-a5 g3-f4 a7-b6 a1-b2 b6-c5 e1-f2 f6-g5 c3-d4 c7-b6 f2-g3 b6-a5 g1-h2 f8-e7",
        "g3-f4 f6-g5 h8-g7 c3-d4 g7-f6 h2-g3 b6-a5 a7-b6 g1-h2 b6-c5 a1-b2 b8-a7 c3-d4 c7-b6 b2-c3 b6-a5 g3-f4 a7-b6 e1-f2 f6-g5",
        "g3-f4 f6-g5 h8-g7 h2-g3 g7-f6 g3-f4 d6-e5 g1-h2 b8-c7 e1-f2 c7-d6 f2-g3 b6-c5 e3-d4 d8-c7 f4-g5 c3-d4 a7-b6 h2-g3 d6-c5",
        "g3-f4 f6-g5 h8-g7 h2-g3 g7-f6 g3-f4 d6-e5 g1-h2 b8-c7 e1-f2 c7-d6 f2-g3 b6-c5 e3-d4 d8-c7 f4-g5 c3-d4 c7-b6 a1-b2 b6-c5",
        "g3-f4 f6-g5 h8-g7 h2-g3 g7-f6 g3-f4 d8-e7 b6-a5 g1-f2 d6-e5 f2-e3 c7-d6 g5-h6 a7-b6 e3-d4 b6-c5 d2-e3 c7-b6 e3-d4 d6-c5",
        "g3-f4 f6xd4 c3xe5 d6-c5 h2-g3 c5-b4 b2-c3 a7-b6 c3xa5 b6-c5 c7xe5 f4xb4 a3xc5 d2-c3 c5-b4 c3-d4 b4-a3 d4-c5 b8-a7 e3-d4",
        "g3-f4 f6xd4 e3xc5 b6xd4 c3xe5 a7-b6 b2-c3 b6-c5 f4-g5 h6xf4 e5xg3 g7-h6 g3-f4 e7-f6 c3-b4 d6-e5 f4xd6 c5xe7 b4-c5 c7-d6",
        "g3-f4 f6xd4 e3xc5 d6xb4 c3xa5 g7-f6 b2-c3 e7-d6 h2-g3 a7-b6 g3-h4 f8-e7 f2-e3 f6-g5 h4xf6 e7xg5 c3-d4 h8-g7 e1-f2 b6-c5",
        "g3-f4 f6xd4 e3xc5 d6xb4 c3xa5 g7-f6 b2-c3 f6-g5 f2-e3 h8-g7 c3-d4 g5-h4 g1-f2 g7-f6 f4-g5 h6xf4 e3xg5 c7-d6 a1-b2 d6-e5",
        "g3-f4 f8-e7 f4-g5 h6xf4 e3xg5 g7-h6 f2-e3 h6xf4 e3xg5 b6-c5 g5-h6 f6-e5 c3-d4 e5xc3 b2xb6 a7xc5 h2-g3 c7-b6 g3-f4 b6-a5",
        "g3-f4 g5-h4 b4-c5 f6-g5 b2-c3 g7-f6 f2-g3 f6-e5 e3-f4 b8-c7 a1-b2 c7-d6 c3-b4 f8-g7 b2-a3 g7-f6 b4-a5 d8-c7 c1-d2 f6-g5",
        "g3-f4 g7-f6 b2-c3 f6-g5 c3-d4 g5-h4 d2-c3 h8-g7 b6-c5 c3-b4 e7-f6 d8-c7 f2-g3 h6-g5 c7-b6 a1-b2 g7-f6 g3-f4 a7-b6 g1-f2",
        "g3-f4 g7-f6 b2-c3 f6-g5 d2-e3 c7-b6 e7-d6 a1-b2 h8-g7 b2-c3 g7-f6 c1-d2 d6-c5 c3-b4 d8-c7 b6-a5 b4-c5 b8-c7 c5-d6 a7-b6",
        "g3-f4 g7-f6 c3-d4 b6-c5 b2-c3 c5-b4 c3-d4 b4-a3 h8-g7 h2-g3 g7-f6 f2-e3 c7-d6 e1-d2 d8-c7 a1-b2 f6-g5 c3-d4 e7-f6 b2-c3",
        "g3-f4 g7-f6 c3-d4 b6-c5 d4xb6 a7xc5 b2-c3 c5-b4 f4-e5 f6xb2 c1xc5 d6xb4 a5xc3 e7-d6 h2-g3 d6-c5 a1-b2 f8-e7 b2-a3 h8-g7",
        "g3-f4 g7-f6 c3-d4 f6-g5 d2-e3 h8-g7 c7-b6 a1-b2 g7-f6 f4-e5 g5-f4 e7-d6 a3-b4 f8-e7 e3-f4 e7-d6 b2-a3 b6-c5 f4-e5 h8-g7",
        "g3-f4 g7-f6 d2-e3 f6-g5 b2-c3 g5-h4 h8-g7 e1-d2 g7-f6 f4-g5 c7-b6 a1-b2 a7-b6 g5-h6 d6-c5 b2-c3 d8-c7 d4-e5 d2-c3 h2-g3",
        "g3-f4 g7-f6 f4-g5 b6-a5 g5-h6 c7-b6 f2-e3 b6-c5 b8-c7 b2-c3 f6-e5 e3-f4 c5-b4 c3-d4 c7-d6 d4-e5 d6-c5 e5-d6 b4-a3 a1-b2",
        "g3-f4 g7-f6 f4-g5 f6-e5 g5-h6 b6-c5 c3-b4 h8-g7 g7-f6 h2-g3 c5-d4 d2-e3 b4-c5 e7-d6 a1-b2 c7-b6 a3-b4 b6-a5 b2-c3 a7-b6",
        "g3-f4 g7-f6 f4-g5 h8-g7 g5-h6 b6-a5 h2-g3 f6-e5 g7-f6 e3-d4 c7-b6 h4-g5 d6-c5 g1-h2 c5-b4 f4-e5 d8-e7 g3-f4 b6-c5 c3-b4",
        "g3-f4 g7-f6 f4-g5 h8-g7 g5-h6 f6-e5 f2-e3 g7-f6 b6-a5 g3-f4 a7-b6 f2-g3 b6-c5 c3-b4 g3-h4 d6-c5 a1-b2 f8-g7 d2-c3 b8-c7",
        "g3-f4 g7-h6 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 f6-e5 h2-g3 h4xf6 c5-d4 a1-b2 f6-g5 e1-d2 g5xe3 d2xf4 d4-e3 f2xf6 e7xe3 b4-a5",
        "g3-f4 h2-g3 c3-b4 b2-c3 f6-g5 g5-h4 b6-c5 g7-f6 c3-d4 b4-c5 f6-g5 a7-b6 h6-g5 a1-b2 g1-f2 b2-a3 a3-b4 d8-c7 h8-g7 g7-f6",
        // --- e3-f4 (121 linhas de campeonato) ---
        "e3-f4 e7-f6 a1-b2 f6-g5 c3-b4 g3-h4 h6-g5 d6-c5",
        "e3-f4 f6-g5 f4-e5 g5-h4 d2-e3 h6-g5 a3-b4 b6-a5",
        "e3-f4 e5-d4 f4-g5 f6xf2 g1xe7 g7-f6 c1-d2 f6-g5 f4-e5",
        "e3-f4 f6-e5 f4xd6 h2xf4 b4-c5 c7xe5 c3-b4 b6xd4 b4-a5 g7-f6",
        "e3-f4 f6-e5 f2-e3 e7-f6 a3-b4 b6-c5 g3-h4 c5xa3 f4-g5 h6xf4 e3xc5",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-a5 e5-f6 g7xe5 c3-b4 a5xc3 b2xh4",
        "e3-f4 f6xd4 c3xe5 b6-c5 g3-h4 c5-b4 a3xc5 d6xb4 b2-c3 b4-a3 e7-f6 c1-b2",
        "e3-f4 a7-b6 g3-h4 d6-c5 h2-g3 e7-d6 f2-e3 f8-e7 b6-a5 b2-c3 e7-f6 c3-d4 c5-b4 h4-g5 g1-h2 g7-f6",
        "e3-f4 b6-c5 g3-h4 a7-b6 d2-e3 c5-b4 b2-c3 b6-a5 c1-b2 c3-b4 e3-d4 e7-d6 h8-c3 d6-c5 c3-e1 c5-d4 f2-e3 e1-d2",
        "e3-f4 e5xg3 h2xf4 f6-e5 g1-h2 e5xg3 h2xf4 g7-f6 f2-e3 f6-g5 h4xf6 e7xg5 c3-b4 d6-c5 b4xd6 c7xg3 e3-f4 g3xe5",
        "e3-f4 g7-f6 b2-c3 f8-g7 d2-e3 f6-g5 c3-b4 b6-c5 a1-b2 g7-f6 e5xg3 h2xf4 a7-b6 f4-e5 d6xd2 b4xf8 b8-a7 c1xe3",
        "e3-f4 b6-a5 c3-d4 a5-b4 b2-c3 g7-f6 c3xa5 f6-g5 h4xf6 e7xc5 h8-g7 a1-b2 g7-f6 d2-e3 f8-g7 f4-g5 h6xd2 c1xe3 a3xc1",
        "e3-f4 b6-a5 c3-d4 e5xc3 b2xd4 d6-e5 f4xd6 c7xc3 d2xb4 a5xc3 a7-b6 d2xb4 b6-a5 b4-c5 a5-b4 f2-e3 b4xd6 a3-b4 d8-c7",
        "e3-f4 f6-g5 f2-e3 g5-h4 g1-f2 b6-a5 c3-d4 a7-b6 b2-c3 d6-c5 d4-e5 e7-d6 c3-d4 f8-e7 a1-b2 e7-f6 b2-c3 f6-g5 e5-f6",
        "e3-f4 a7-b6 f2-e3 f6-g5 g3-h4 e5xg3 h4xf2 g5-f4 e3xg5 h6xf4 d2-e3 f4xb4 a3xa7 g7-f6 b2-c3 f6-e5 a1-b2 h8-g7 c3-b4 e5-f4",
        "e3-f4 b6-a5 c3-b4 a5xc3 d2xb4 a7-b6 b4-a5 b6-c5 e1-d2 h8-g7 c5-d4 d2-c3 c7-b6 a5xc7 d8xb6 f2-e3 d4xf2 g3xe1 e5xg3 h2xf4",
        "e3-f4 b6-a5 c3-d4 d6-e5 f4xd6 e7xe3 d2xf4 f6-g5 b2-c3 g5xe3 f2xd4 g7-f6 c1-b2 c7-d6 d4-e5 f6xd4 c3xc7 b8xd6 a3-b4 a5xc3",
        "e3-f4 b6-a5 c3-d4 d6-e5 f4xd6 e7xe3 f2xd4 a7-b6 b2-c3 c7-d6 c1-b2 d6-c5 d2-e3 d8-c7 g3-h4 c7-d6 h2-g3 b8-c7 g1-h2 d6-e5",
        "e3-f4 b6-a5 c3-d4 d6-e5 f4xd6 e7xe3 f2xd4 a7-b6 d2-e3 c7-d6 g1-f2 d6-c5 g3-f4 f6-g5 h2-g3 g5-h4 a3-b4 a5xe5 f4xb4 d8-c7",
        "e3-f4 b6-a5 c3-d4 f6-e5 d4xf6 e7xe3 d2xf4 g7-f6 b2-c3 f6-g5 f4-e5 d6xf4 g3xe5 f8-e7 c1-d2 h8-g7 c3-d4 c7-b6 a3-b4 a5xc3",
        "e3-f4 b6-a5 d2-e3 c7-b6 c1-d2 b6-c5 c3-b4 a5xc3 b2xb6 a7xc5 c5-d4 e3xc5 d6xd2 e1xc3 d8-c7 f4xd6 e7xc5 a1-b2 h8-g7 c3-d4",
        "e3-f4 b6-a5 d4-c5 c7-d6 b2-a3 h6-g5 e5-f4 f2-e3 g7-f6 h2-g3 b8-c7 e1-f2 c7-d6 g3-h4 b6-c5 f2-g3 c5-b4 g3-f4 b4-a3 g1-f2",
        "e3-f4 b6-a5 d4-c5 h6-g5 g3-f4 d8-c7 f2-e3 e3-f4 g7-h6 c3-d4 f6-g5 e1-d2 e7-d6 g1-f2 a7-b6 b2-c3 b6-c5 c3-d4 c7-b6 f2-e3",
        "e3-f4 b6-a5 f2-e3 a7-b6 g3-h4 f6-e5 c3-b4 a5xc3 b2xf6 g7xg3 h4xf2 h8-g7 a1-b2 g7-f6 h2-g3 f6-g5 b2-c3 b6-c5 c3-d4 c7-b6",
        "e3-f4 b6-a5 f2-e3 a7-b6 g3-h4 f6-e5 c3-b4 a5xc3 b2xf6 g7xg3 h4xf2 h8-g7 a1-b2 g7-f6 h2-g3 f6-g5 b2-c3 d6-e5 e3-f4 g5xe3",
        "e3-f4 b6-a5 f2-e3 c7-b6 g3-h4 f6-e5 h2-g3 g7-f6 g1-h2 b6-c5 a5xc3 b2xb6 a7xc5 d2-c3 c5-d4 e3xc5 d6xd2 e1xc3 d8-c7 f4xd6",
        "e3-f4 b6-a5 f2-e3 c7-b6 g3-h4 f6-e5 h2-g3 g7-f6 g1-h2 b6-c5 a5xc3 b2xb6 a7xc5 d2-c3 h8-g7 c3-b4 e5-d4 e1-f2 f6-e5 b4-a5",
        "e3-f4 b6-a5 f2-e3 e5-d4 c7-b6 b2-c3 b6-c5 g7-f6 f4-g5 h8-g7 g5-h6 f6-e5 g3-f4 c5-b4 h2-g3 b4-a3 g3-f4 e7-d6 a1-b2 a7-b6",
        "e3-f4 b6-a5 f2-e3 f6-e5 c3-d4 e5xc3 b2xd4 c7-b6 f4-g5 h6xf4 g3xc7 b8xd6 a1-b2 g7-f6 g1-f2 d6-c5 h2-g3 e7-d6 b2-c3 f6-g5",
        "e3-f4 b6-a5 f2-e3 f6-e5 c3-d4 e5xc3 b2xd4 c7-b6 g1-f2 d6-c5 a3-b4 a5xe5 f4xb4 b6-c5 b4xd6 e7xc5 a1-b2 g7-f6 b2-c3 a7-b6",
        "e3-f4 b6-a5 f2-e3 f6-g5 g3-h4 a7-b6 h4xf6 g7xg3 h2xf4 h8-g7 a5xc3 b2xd4 g7-f6 c1-b2 d6-c5 g1-h2 f6-g5 h2-g3 g5-h4 d2-c3",
        "e3-f4 b6-c5 b2-c3 c5-b4 a3xc5 d6xb4 f4xd6 e7xc5 c3-d4 c5xe3 a5xc3 a7-b6 f2xd4 f8-e7 g3-f4 b6-a5 d2-e3 g7-f6 h2-g3 e7-d6",
        "e3-f4 b6-c5 c3-b4 a5xc3 d2xb4 f6-e5 f2-e3 g7-f6 b4-a5 e5-d4 d4xf2 g1xe3 f6-e5 f4-g5 h6xf4 e3xg5 c5-d4 a1-b2 d6-c5 d2-c3",
        "e3-f4 b6-c5 c3-b4 a7-b6 b4-a5 h8-g7 d2-c3 c5-d4 c1-d2 b6-c5 a1-b2 c7-b6 b2-a3 b6-a5 f2-e3 e5-d4 f4-e5 f6-e5 a3-b4 c1-b2",
        "e3-f4 b6-c5 c3-b4 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 f2xf6 f8-g7 d8xf6 h2-g3 h6-g5 g3-h4 g5-f4 d2-e3 f4xd2 c1xe3 g7-h6 e3-f4",
        "e3-f4 b6-c5 d2-e3 a7-b6 b2-c3 f6-e5 c1-b2 b6-a5 c3-d4 e5xc3 b2xb6 a5-b4 a3xc5 c7xa5 c5-b6 a5xc7 e3-d4 d6-c5 d4xb6 c7xa5",
        "e3-f4 b6-c5 d2-e3 a7-b6 c3-d4 f6-g5 g3-h4 d6-e5 f4xb4 c7-d6 h4xf6 g7xa5 a3-b4 a5xc3 b2xd4 h8-g7 h2-g3 g7-f6 g3-f4 b6-a5",
        "e3-f4 b6-c5 f2-e3 a7-b6 c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 b6-a5 g3-h4 f8-e7 h4xf6 g7xg3 h2xf4 e7-f6 c3-d4 d6-e5 f4xb4 a5xe5",
        "e3-f4 b6-c5 f2-e3 a7-b6 c3-d4 f6-e5 d4xf6 e7xg5 g3-h4 b6-a5 h4xf6 g7xg3 h2xf4 h8-g7 d2-c3 g7-f6 c3-b4 a5xc3 b2xb6 c7xa5",
        "e3-f4 b6-c5 f2-e3 c7-b6 c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 f8-e7 c3-b4 g7-f6 d2-c3 f6-e5 e3-d4 c5xe3 f4xd2 b8-c7 g3-f4 e5xg3",
        "e3-f4 b6-c5 f2-e3 c7-b6 c3-d4 f6-e5 d4xf6 g7xe5 f4-g5 h6xf4 e3xg5 h8-g7 g5-h6 b8-c7 g3-h4 g7-f6 h2-g3 b6-a5 g3-f4 e5xg3",
        "e3-f4 b6-c5 g3-h4 e7-f6 d2-c3 f8-e7 c5-b4 e3-d4 g7-f6 b2-a3 c7-d6 f4-g5 b8-c7 e1-d2 e7-f6 a1-b2 b4-a3 d4-c5 f8-e7 b2-c3",
        "e3-f4 c3-b4 d2xf4 b4-a5 f6-g5 g5xe3 b6-c5 g7-f6 f2-e3 g3-h4 h4xf6 h2xf4 f6-g5 f8-g7 g7xg3 e7-f6 b2-c3 g1-h2 h2xf4 e1-d2",
        "e3-f4 c3-d4 d2xb4 b4-c5 f6-e5 e5xc3 g7-f6 b6xd4 f4-e5 g3xc3 c3-d4 a3-b4 d6xf4 a7-b6 e7-d6 h6-g5 b4-a5 b2-c3 a1-b2 h2-g3",
        "e3-f4 c5-b4 g3-h4 b4-a3 f4-g5 b6-a5 g7-f6 a1-b2 c7-d6 f2-g3 b8-a7 g3-f4 d6-c5 f4-g5 h8-g7 g5-h6 f6-e5 d2-e3 e7-d6 g1-f2",
        "e3-f4 c5-b4 g3-h4 b4-a3 f4-g5 g7-f6 h8-g7 f4-g5 b6-a5 h2-g3 d6-c5 g5-h6 c5-b4 g3-f4 c7-d6 b2-c3 d8-c7 f2-e3 d6-c5 c3-d4",
        "e3-f4 d6-c5 c3-b4 a5xc3 d2xd6 c7xe5 f4xd6 f6-g5 h4xf6 g7xc7 h8-g7 b2-c3 g7-f6 f2-e3 b6-a5 g3-h4 f8-e7 h2-g3 a7-b6 g3-f4",
        "e3-f4 d6-c5 e5-d6 b4-a5 g7-f6 b2-c3 f6-e5 a3-b4 a7-b6 b4-a5 d8-c7 c3-b4 h6-g5 a1-b2 f8-g7 b4-c5 d2-e3 c7-b6 f2-e3 b6-c5",
        "e3-f4 d6-c5 e5-d6 b4-a5 g7-f6 b2-c3 f6-e5 c3-d4 d6-e5 b4-c5 e7-d6 f2-e3 d8-e7 a1-b2 a7-b6 b2-c3 e5-f4 c3-d4 d6-c5 e1-f2",
        "e3-f4 d6-c5 g3-h4 e7-d6 h2-g3 f6-e5 c3-d4 c5xg5 h4xd4 g7-f6 b6-c5 d4xb6 a7xc5 d2-e3 f8-e7 a1-b2 h8-g7 c3-b4 f6-g5 e3-d4",
        "e3-f4 d6-c5 g3-h4 e7-d6 h2-g3 f6-e5 c3-d4 c5xg5 h4xd4 g7-f6 h6-g5 g3-h4 d6-e5 f2-g3 c7-d6 d2-e3 h8-g7 g3-f4 e5xg3 h4xf2",
        "e3-f4 d6-c5 g3-h4 e7-d6 h2-g3 f6-e5 f2-e3 e5-d4 c3xe5 f8-e7 g7xe5 e1-f2 b6-a5 g1-h2 h8-g7 d2-c3 g7-f6 c3-b4 a5xc3 b2xb6",
        "e3-f4 d6-c5 g3-h4 e7-d6 h2-g3 f6-e5 f2-e3 e5-d4 c3xe5 f8-e7 g7xe5 e1-f2 h8-g7 g1-h2 b6-a5 d2-c3 g7-f6 c3-b4 a5xc3 b2xb6",
        "e3-f4 d6-e5 f4xd6 h2xf4 c3-b4 c7xe5 a5xc7 d8xb6 b4-a5 b6-c5 e7-d6 e1-d2 b8-c7 g1-h2 h6-g5 c3-b4 g5-h4 d2-c3 f4-g3 h2xf4",
        "e3-f4 e5xg3 h2xf4 d6-e5 f4xd6 c7xe5 f2-g3 h6-g5 g3-f4 e5xg3 h4xf2 g5-f4 g1-h2 f6-e5 f2-e3 g7-h6 e3xg5 h6xf4 e1-f2 f8-g7",
        "e3-f4 e5xg3 h2xf4 d6-e5 f4xd6 e7xc5 c3-b4 d8-e7 b4xd6 e7xc5 b6-a5 f2-e3 a7-b6 e3-f4 f8-e7 c3-b4 a5xc3 d2xf8 b6-a5 a3-b4",
        "e3-f4 e5xg3 h2xf4 f6-e5 f2-e3 e5xg3 h4xf2 g7-f6 e3-f4 f6-e5 e5xg3 f2xh4 b6-a5 c3-d4 c7-b6 b2-c3 d6-c5 g1-f2 e7-f6 f2-g3",
        "e3-f4 e7-f6 d2-c3 f8-e7 b2-c3 g7-f6 f4-g5 b6-c5 g3-f4 a7-b6 h2-g3 b6-a5 g3-h4 c5-b4 c3-d4 c7-b6 f2-e3 b6-c5 g5-f6 b4-c3",
        "e3-f4 e7-f6 d2-e3 b6-c5 g3-h4 e5xg3 h2xf4 f8-e7 f2-g3 f6-g5 h4xf6 g7xe5 g1-h2 h8-g7 g3-h4 e5xg3 h2xf4 g7-f6 b2-c3 h6-g5",
        "e3-f4 e7-f6 f2-e3 f6-g5 g3-h4 g5-f4 g7-h6 a1-b2 h8-g7 b4-c5 d2-e3 h2-g3 h6-g5 b2-c3 g7-h6 c3-d4 g5-f4 a3-b4 h6-g5 g1-h2",
        "e3-f4 f6-e5 c3-d4 e5xc3 d2xb4 b6-a5 b4-c5 d6xb4 a3xc5 c7-b6 b6xd4 f4-g5 h6xf4 g3xc3 e7-d6 c3-b4 a5xc3 b2xd4 g7-f6 a1-b2",
        "e3-f4 f6-e5 c3-d4 e5xc3 d2xb4 b6-c5 b4-a5 g7-f6 f2-e3 f6-g5 f8-g7 h4xf6 g7xg3 h2xf4 h8-g7 e1-d2 g7-f6 b2-c3 c5-b4 a3xc5",
        "e3-f4 f6-e5 f2-e3 b6-c5 c3-b4 a5xc3 d2xb4 c7-b6 b4-a5 g7-f6 a5xc7 d8xb6 e1-d2 f8-e7 f4-g5 h6xf4 e3xg5 e5-d4 g5-h6 f6-e5",
        "e3-f4 f6-e5 f2-e3 b6-c5 c3-b4 a5xc3 d2xb4 g7-f6 c1-d2 e5-d4 d4xf2 g5xe7 d8xf6 g1xe3 f8-g7 e3-f4 f6-g5 h4xf6 g7xe5 g3-h4",
        "e3-f4 f6-g5 b4-a5 g3-h4 b6-c5 c3-b4 h8-g7 e5-f4 e1-f2 g7-f6 a1-b2 f6-e5 f2-e3 e7-f6 h2-g3 e5-d4 e3-f4 f8-g7 g1-h2 f6-e5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 g7-f6 f2-e3 f6-g5 e1-d2 c7-d6",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 b6-c5 b2-c3 g7-f6 f2-e3 c7-b6 c3-d4 b6-a5 d4xb6 a5xc7 g3-h4 a7-b6 b4-a5 b6-c5 h2-g3 f8-g7",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 b6-c5 b4-a5 g7-f6 f2-e3 f6-e5 g3-h4 e5xg3 h2xf4 f8-g7 e1-d2 e7-f6 a3-b4 c5xa3 f4-g5 h6xf4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 b6-c5 b4-a5 g7-f6 f2-e3 f6-g5 g3-h4 f8-g7 h4xf6 g7xg3 h2xf4 h8-g7 e1-d2 e7-f6 d2-c3 f6-e5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 b6-c5 f2-e3 g7-f6 b4-a5 f6-e5 g3-h4 e5xg3 h2xf4 e7-f6 b2-c3 f6-e5 g1-h2 e5xg3 h2xf4 f8-e7",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 b6-c5 f2-e3 g7-f6 b4-a5 f6-g5 g3-h4 f8-g7 h4xf6 g7xg3 h2xf4 h8-g7 e1-d2 e7-f6 d2-c3 f6-g5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 b6-c5 f2-e3 g7-f6 b4-a5 f6-g5 g3-h4 f8-g7 h4xf6 g7xg3 h2xf4 h8-g7 e1-f2 g7-f6 f2-g3 f6-g5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 d6-c5 b4xd6 e7xc5 b2-c3 b6-a5 c1-d2 c7-b6 c3-b4 a5xc3 d2xd6 d8-e7 a1-b2 e7xc5 b2-c3 b6-a5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 b4-c5 d6xb4 a3xc5 b6xd4 d4-e3 f2xd4 h6-g5 g3-h4 f8-e7 g1-f2 c7-b6 d4-c5 b6xd4 e5xc3",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 c1-d2 f6-g5 f2-e3 g5-h4 g1-f2 d8-e7 b4-c5 d6xb4 a3xc5 b6xd4 e3xc5 g7-f6 f4-g5 h6xf4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 f2-e3 f6-g5 c1-d2 b6-a5 f4-e5 a5xc3 b2xd4 d6xf4 g3xe5 f8-e7 g1-f2 a7-b6 a1-b2 e7-d6",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 f2-e3 f6-g5 c1-d2 b6-c5 f4-e5 d6xf4 g3xe5 d8-e7 b4xd6 e7xc5 d2-c3 a7-b6 e1-f2 g5-h4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 f2-e3 f6-g5 c1-d2 g5-h4 g1-f2 b6-a5 b4-c5 d6xb4 a3xc5 d8-e7 e3-d4 e7-d6 c5xe7 f8xd6",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 f2-e3 f6-g5 c1-d2 g5-h4 g1-f2 d8-e7 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-b6 d2-e3 b6xd4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 f2-e3 f6-g5 c1-d2 g5-h4 g1-f2 d8-e7 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 c7-d6 b2-a3 d6xb4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 f2-e3 f6-g5 c1-d2 g5-h4 g1-f2 d8-e7 b4-c5 b6xd4 e3xc5 d6xb4 a3xc5 g7-f6 f4-g5 h6xf4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 f2-e3 f6-g5 c1-d2 g5-h4 g1-f2 d8-e7 f4-e5 d6xf4 g3xe5 e7-d6 e3-d4 d6xf4 b4-a5 h6-g5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 f2-e3 f6-g5 c1-d2 g5-h4 g1-f2 f8-e7 b2-c3 b6-a5 b4-c5 d6xb4 a3xc5 c7-d6 a1-b2 d6xb4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 e7-f6 g3-h4 f8-e7 h2-g3 f6-g5 h4xf6 e7xe3 f2xd4 d6-e5 d4xf6 g7xe5 g3-h4 h8-g7 b2-c3 c7-d6",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 b4-c5 b6xd4 f4-e5 d6xf4 g3xc3 f6-e5 h2-g3 a7-b6 f2-e3 e7-d6 c3-d4 e5xc3 b2xd4 h8-g7",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 b4-c5 b6xd4 f4-e5 d6xf4 g3xc3 h6-g5 a3-b4 h8-g7 b4-a5 e7-d6 f2-e3 g5-h4 c3-d4 d6-c5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 b4-c5 d6xb4 a3xc5 b6xd4 f4-e5 d4-e3 e5xg7 h8xf6 f2xd4 e7-d6 b2-c3 a7-b6 a1-b2 f8-g7",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 b4-c5 d6xb4 a3xc5 b6xd4 f4-e5 d4-e3 e5xg7 h8xf6 f2xd4 e7-d6 b2-c3 a7-b6 g1-f2 d6-c5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 f2-e3 f6-g5 c1-d2 g5-h4 g1-f2 b6-a5 b2-c3 a7-b6 a1-b2 b6-c5 f4-e5 d6xf4 b4xd6 c7xe5",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 f4-e5 d6xf4 g3xg7 h8xf6 b4-a5 b6-c5 b2-c3 f6-e5 c3-b4 e5-f4 b4xd6 c7xe5 a1-b2 d8-c7",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 f4-e5 d6xf4 g3xg7 h8xf6 b4-a5 h6-g5 a3-b4 f6-e5 b2-c3 e5-f4 a1-b2 e7-d6 b2-a3 f8-g7",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 f4-e5 d6xf4 g3xg7 h8xf6 b4-a5 h6-g5 b2-c3 b6-c5 c3-b4 e7-d6 a1-b2 f6-e5 b2-c3 g5-h4",
        "e3-f4 f6-g5 c3-b4 g5xe3 d2xf4 g7-f6 f4-e5 d6xf4 g3xg7 h8xf6 b4-a5 h6-g5 b2-c3 b6-c5 c3-b4 g5-h4 b4xd6 c7xe5 a1-b2 d8-c7",
        "e3-f4 f6-g5 c3-b4 g5xe3 f2xd4 d6-c5 b4xd6 e7xe3 d2xf4 g7-f6 b2-c3 b6-a5 g1-f2 c7-d6 f2-e3 a7-b6 c1-d2 f8-e7 c3-d4 f6-g5",
        "e3-f4 f6-g5 d2-e3 g5-h4 c1-d2 a7-b6 c3-b4 b6-c5 b4-a5 b8-a7 e5-d4 e7-f6 f4-g5 g3-f4 a3-b4 f8-e7 h2-g3 g7-f6 g3-h4 h8-g7",
        "e3-f4 f6-g5 d2-e3 g5-h4 c1-d2 b6-a5 c3-d4 g7-f6 f4-e5 d6xf4 g3xg7 h8xf6 h2-g3 f6-g5 g3-f4 c7-b6 b2-c3 e7-d6 d4-e5 d8-e7",
        "e3-f4 f6-g5 d2-e3 g5-h4 c1-d2 b6-c5 c3-b4 a7-b6 b4-a5 b8-a7 b2-c3 c5-b4 a3xc5 b6xb2 a1xc3 d6-c5 c3-d4 c7-b6 a5xc7 d8xb6",
        "e3-f4 f6-g5 d4-e5 g5xe3 d2xf4 d6-c5 g3-h4 c5-d4 e5-f6 e7xe3 c3xe5 f8-e7 f2xd4 b6-c5 d4xb6 a7xc5 g1-f2 e7-f6 e1-d2 f6xd4",
        "e3-f4 f6-g5 f2-e3 g5-h4 e3-d4 h4xf2 e1xg3 g7-f6 d2-e3 f6-e5 d4xf6 e7xg5 c3-d4 g5-h4 g1-f2 f8-g7 b2-c3 g7-f6 a1-b2 f6-g5",
        "e3-f4 f6-g5 f2-e3 g5-h4 g1-f2 g7-f6 f4-g5 h6xf4 g3xg7 h8xf6 c3-d4 f6-e5 d4xf6 e7xg5 b2-c3 b6-c5 c3-b4 f8-g7 d2-c3 g7-h6",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-c5 c3-b4 a7-b6 b4xd6 e7xc5 d2-c3 f8-e7 c3-b4 e7-d6 f2-g3 d6xf4 g3xe5 g7-f6 b4xd6 f6xd4",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-c5 c3-b4 e7-d6 f2-g3 d6xf4 g3xe5 d8-e7 b4xd6 e7xc5 e1-f2 f8-e7 h2-g3 e7-d6 g3-f4 g5xe3",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-c5 c3-b4 e7-d6 f2-g3 d6xf4 g3xe5 d8-e7 b4xd6 e7xc5 e1-f2 f8-e7 h2-g3 e7-d6 g5-f4 e5-d6",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-c5 c3-b4 e7-d6 f2-g3 d6xf4 g3xe5 d8-e7 b4xd6 e7xc5 e1-f2 f8-e7 h2-g3 e7-f6 d2-e3 f6xd4",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-c5 c3-b4 e7-d6 f2-g3 d6xf4 g3xe5 d8-e7 b4xd6 e7xc5 e1-f2 f8-e7 h2-g3 g5-f4 e5-d6 c7xe5",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 b6-c5 c3-b4 e7-d6 f2-g3 d6xf4 g3xe5 d8-e7 b4xd6 e7xc5 e1-f2 f8-e7 h2-g3 g5-h4 e5-f6 g7xe5",
        "e3-f4 f6-g5 f4-e5 d6xf4 g3xe5 g5-h4 h2-g3 e7-d6 g3-f4 f8-e7 d2-e3 b6-a5 c3-d4 a7-b6 f2-g3 h4xf2 e1xg3 b6-c5 d4xb6 a5-b4",
        "e3-f4 f6-g5 g3-h4 f8-e7 h2-g3 g5-f4 c3-d4 b6-c5 h4-g5 c5-b4 b2-c3 f4-g3 a1-b2 h6-g5 b2-a3 h8-g7 a3-b4 g3-h2 e1-f2 c7-d6",
        "e3-f4 f6-g5 g3-h4 f8-e7 h2-g3 g5-f4 c3-d4 h8-g7 d4-e5 f4-g3 d2-e3 g7-f6 b2-c3 c7-d6 f2-g3 b6-c5 c3-b4 a7-b6 b4-a5 d6-e5",
        "e3-f4 f6-g5 h4xf6 g7xe5 g3-h4 e5xg3 h2xf4 f8-g7 f2-e3 g7-f6 f6-e5 g1-h2 e5xg3 h2xf4 b6-a5 c3-b4 a5xc3 b2xb6 c7xa5 a1-b2",
        "e3-f4 f6xd4 c3xe5 b6-a5 g3-h4 d6-c5 h2-g3 c5-b4 f2-e3 e7-d6 d8-e7 e1-f2 d6-c5 h4-g5 a7-b6 g5-f6 e7xg5 g3-h4 g7-f6 e5xg7",
        "e3-f4 f6xd4 c3xe5 b6-c5 g3-h4 e7-f6 d2-c3 f6xd4 c3xe5 f8-e7 g7-f6 e5xg7 h6xf8 h4-g5 a7-b6 h2-g3 c5-b4 g1-h2 d6-e5 f4xd6",
        "e3-f4 f6xd4 c3xe5 c5-b4 g3-h4 b4-a3 f4-g5 h6xf4 e5xg3 d6-e5 c7-d6 b2-c3 b6-a5 g3-f4 e5xg3 h4xf2 g7-f6 h2-g3 h8-g7 g3-h4",
        "e3-f4 f6xd4 c3xe5 c5-b4 g3-h4 b4-a3 f4-g5 h6xf4 e5xg3 d6-e5 c7-d6 b2-c3 b6-a5 g5-h6 b8-c7 g3-h4 c7-b6 h2-g3 b6-c5 h4-g5",
        "e3-f4 f6xd4 c3xe5 e7-f6 d2-e3 f6xd4 e3xe7 f8xd6 f2-e3 d6-e5 f4xd6 c7xe5 e3-f4 d8-c7 f4xd6 c7xe5 g3-f4 e5xg3 h2xf4 a7-b6",
        "e3-f4 f6xd4 c3xe5 e7-f6 d2-e3 f6xd4 e3xe7 f8xd6 g3-h4 g7-f6 b6-a5 f2-g3 f6-e5 g1-f2 a7-b6 h4-g5 d8-e7 g3-h4 e5xg3 h2xf4",
        "e3-f4 f6xd4 c3xe5 f8-e7 b2-c3 b6-c5 c3-b4 e7-f6 a1-b2 f6xd4 g7-f6 d2-c3 f6-e5 c1-d2 a7-b6 c3-b4 d8-e7 d2-c3 e7-f6 g3-h4",
        "e3-f4 f6xd4 c3xe5 g7-f6 e5xg7 h8xf6 g3-h4 a7-b6 f2-g3 f6-e5 h6-g5 h4xd4 a3-b2 c1xa3 d6-e5 d4xf6 e7xc1 a3-b4 b6-c5 b4xd6",
        "e3-f4 f8-e7 f2-e3 b6-c5 c3-d4 a7-b6 b2-c3 b8-a7 g1-f2 f6-e5 d4xf6 g7xe5 a1-b2 h8-g7 h4-g5 g7-f6 g3-h4 e5xg3 h2xf4 f6-e5",
        "e3-f4 f8-e7 f2-e3 b6-c5 c3-d4 a7-b6 g1-f2 f6-g5 h4xf6 g7xc3 b2xd4 a5-b4 g3-h4 e7-f6 d2-c3 b4xd2 e1xc3 c5-b4 c3xa5 d6-e5",
        "e3-f4 g7-f6 b2-c3 f6-g5 g3-h4 d6-c5 f8-e7 h2-g3 g3-h4 g5-f4 h4-g5 f4-g3 g5-f6 g3-h2 c3-d4 b6-c5 b2-c3 c7-b6 c3-b4 a7-b6",
        // --- e3-d4 (133 linhas de campeonato) ---
        "e3-d4 c5xe3 f4xd2 h6xf4 d2-e3 f4xd2 e1xb6",
        "e3-d4 c5xe3 f4xd2 h6xf4 d2-e3 f4xd2 e1xc7",
        "e3-d4 d6-e5 f2-e3 e7-d6 e3-f4 b6-c5 g3-h4",
        "e3-d4 c5xe3 g3-f4 e3xg5 h4xh8 d8-e7 h8-g7 h8-g7",
        "e3-d4 h6-g5 g3-h4 d6-e5 a3-b4 g7-h6 b4-a5 g5-f4 f2-g3 b6-c5",
        "e3-d4 c5xe3 c3-b4 a5xc3 g3-f4 e5xg3 h4xb2 b8-c7 b2-c3 c7-d6 c3-d4",
        "e3-d4 a7-b6 a3-b4 h6-g5 g3-f4 g5xa3 d2-e3 b6-a5 e3-d4 c7-b6 b6-c5 d4xb6 a5xc7",
        "e3-d4 b6-a5 d4-e5 f6xd4 c3xe5 d6xf4 g3xe5 e7-f6 c1-d2 f6xd4 c7-b6 c3xe5 a5-b4 a3xc5 b6xf6",
        "e3-d4 c5xe3 f2xd4 a7-b6 d2-c3 h6-g5 c3-b4 g7-h6 b4-c5 d6xb4 a3xa7 e7-d6 d4-c5 d6xb4 a5xc3",
        "e3-d4 h6-g5 g3-h4 b6-a5 b4-c5 g5-f4 f2-g3 g7-h6 c3-b4 c7-b6 g1-f2 d2-e3 f8-g7 f2-e3 e5-f4",
        "e3-d4 d6xb4 c3xa5 b6-c5 d4xb6 a7xc5 g3-f4 h8-g7 h2-g3 c7-d6 f6-e5 e3-d4 c5xg5 g3-f4 e5xg3 f2xh8",
        "e3-d4 f6-g5 c3-b4 d6-c5 b4xd6 e7xe3 f2xd4 g7-f6 b2-c3 c7-d6 a1-b2 g5-h4 d4-c5 d6xb4 c3xc7 h4xf2 g1xe3",
        "e3-d4 f6-g5 c3-b4 d6-c5 b4xd6 e7xe3 f2xd4 g7-f6 b2-c3 g5-h4 a1-b2 h4xf2 e1xg3 f8-e7 d4-c5 b6xd4 c3xg7",
        "e3-d4 d6-c5 d2-e3 e7-d6 g3-h4 h6-g5 f2-g3 b6-a5 d4xb6 a7xc5 e5xg3 h2xh6 d6-e5 h4-g5 f6xh4 c3-b4 a5xc3 b2xf6",
        "e3-d4 f6-g5 d2-e3 g7-f6 a3-b4 g5-h4 g3-f4 f6-e5 d4xf6 e7xg5 h8-g7 c1-b2 d8-e7 e1-d2 d6-c5 b4xd6 c7xe1 c3-d4 e1xf6",
        "e3-d4 f6-g5 f2-e3 g7-f6 c3-b4 d6-c5 b4xd6 c7xc3 b2xd4 f8-g7 a1-b2 b6-a5 a3-b4 a5xa1 e1-f2 a1xe5 e3-f4 g5xe3 d2xf8",
        "e3-d4 a7-b6 a3-b4 b6-a5 b2-a3 h6-g5 g3-h4 g7-h6 f2-g3 g5-f4 h6-g5 d2-e3 f4xd2 c3xe1 a5xc3 d4xb2 g5-f4 b2-c3 h8-g7 e1-d2",
        "e3-d4 b6-a5 a3-b4 a7-b6 d4-e5 h8-g7 a1-b2 b6-a5 b2-c3 c7-b6 e1-d2 e7-d6 f2-g3 g7-f6 g3-h4 d6-c5 d2-e3 c5-b4 c1-d2 b4-a3",
        "e3-d4 b6-a5 b4-c5 d6xb4 a3xc5 h6-g5 c5-d6 e7xe3 d2xh6 e5-d4 c3xe5 f6xd4 c1-d2 d4-c3 d2xb4 a5xc3 b2xd4 f8-e7 h6xd6 c7xc3",
        "e3-d4 b6-a5 b4-c5 h6-g5 c5-d6 e5-d4 g3-f4 c7-b6 b2-c3 g7-f6 f2-g3 b6-c5 g3-h4 h8-g7 e1-d2 c5-d4 d2-e3 d8-e7 e3-d4 b8-c7",
        "e3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 d2-e3 f6-g5 b2-a3 g5-h4 c7-b6 a1-b2 b6xd4 c3xe5 a7-b6 h8-g7",
        "e3-d4 b6-a5 d4-c5 d6xb4 a3xc5 f6-g5 c3-d4 g5-h4 g3-f4 g7-f6 c7-b6 c1-d2 f6-g5 f4-e5 b8-c7 b2-c3 e7-d6 c5xe7 f8xf4 f2-g3",
        "e3-d4 b6-c5 c3-b4 e5-f4 b2-c3 f6-e5 f2-g3 g7-f6 h8-g7 c3-b4 c5-d4 g3-h4 b8-a7 a1-b2 d4-e3 b2-c3 c7-b6 e1-f2 b6-a5 d6-c5",
        "e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 a5xc3 b2xb6 c7xa5 a1-b2 d6-c5 c5-d4 c3xe5 f6xd4 a3-b4 a5xc3 d2xb4 g7-f6 g3-h4 d8-c7 f2-g3",
        "e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 a5xc3 b2xb6 c7xa5 a1-b2 d6-e5 e5-f4 e3xg5 f6xh4 b2-c3 e7-d6 c1-d2 g7-f6 d2-e3 d8-e7 e3-d4",
        "e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 a5xc3 b2xb6 c7xa5 f2-e3 a5-b4 a3xc5 d6xb4 a1-b2 b4-a3 b2-c3 b8-c7 g3-h4 c7-b6 g1-h2 f6-e5",
        "e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 c5-d4 g3-f4 a3xc5 d2-e3 g7-f6 d4xb2 a1xc3 f6-e5 h2-g3 e7-f6 g1-h2 f6-g5 g3-h4 e5xg3 h4xf6",
        "e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 e5-f4 g3xe5 d6xf4 b4xd6 e7xc5 f6-e5 c3-b4 c7-d6 f2-e3 f4xd2 c1xe3 g7-f6 h2-g3 e5-d4 a1-b2",
        "e3-d4 b6-c5 d4xb6 a7xc5 d2-e3 c5-d4 e3xc5 d6xd2 c1xe3 e7-d6 c7-b6 c3-b4 f6-e5 a1-b2 b6-c5 b2-c3 g7-f6 e3-d4 c5xe3 f2xd4",
        "e3-d4 b6-c5 g3-h4 e5-f4 b4-c5 f4-g3 g3-h2 c3-b4 d8-c7 a1-b2 h6-g5 c1-d2 e7-d6 b4-c5 h8-g7 b2-c3 g7-h6 c3-b4 h6-g5 d2-c3",
        "e3-d4 b8-a7 h2-g3 b6-a5 b4-c5 d6xb4 a3xc5 e7-d6 c5xg5 h6xh2 d4xf6 g7xe5 d2-e3 f8-e7 c1-d2 e7-f6 e3-d4 d8-e7 d4-c5 h8-g7",
        "e3-d4 b8-a7 h2-g3 h6-g5 c3-b4 e5xc3 b2xd4 g5-h4 b4-c5 d6xb4 a5xc3 e7-d6 c3-b4 f8-e7 b4-a5 b6-c5 d4xb6 a7xc5 d2-e3 f6-e5",
        "e3-d4 d2-e3 c3-b4 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 b4-c5 a3xc5 g3-f4 h2xf4 d6xb4 f6-e5 e5xg3 g7-f6 e3-d4 f2-e3 c1-d2 b2-c3",
        "e3-d4 d2-e3 c3-b4 d4xb6 d6-c5 c7-d6 b6-a5 a5xc7 g3-f4 f2-g3 g3-h4 h4xf2 f6-e5 a7-b6 e5xg3 h6-g5 b4-a5 h2-g3 b2-c3 c1-d2",
        "e3-d4 d4-c5 d6-c5 b2-c3 f6-e5 c3-b4 e7-d6 g7-f6 e3-d4 d6-c5 g3-f4 c7-d6 e1-f2 h8-g7 a1-b2 f6-e5 f2-g3 g7-f6 g3-h4 f6-e5",
        "e3-d4 d4-c5 f6-e5 g3-f4 h6-g5 d2-e3 h8-g7 b2-c3 g7-f6 e1-f2 a7-b6 f2-g3 b6-a5 c3-d4 c7-d6 a1-b2 d6-c5 b2-c3 e7-d6 g3-h4",
        "e3-d4 d4-c5 f6-e5 g3-h4 a7-b6 b4-a5 b6-c5 c5-b4 f2-g3 e7-d6 g1-h2 h8-g7 a1-b2 b4-a3 e1-f2 f8-e7 f2-e3 e5-f4 c3-d4 g7-f6",
        "e3-d4 d4-c5 f6-e5 g3-h4 a7-b6 b4-a5 b6-c5 e5-f4 b2-c3 h8-g7 a1-b2 g7-f6 c3-b4 f4-g3 f2-e3 g3-h2 b2-c3 f6-e5 e3-f4 e7-f6",
        "e3-d4 d4-c5 f6-g5 g3-f4 g7-f6 f6-e5 a3-b4 h8-g7 a1-b2 g7-f6 f2-e3 f8-e7 e1-f2 e5-f4 c3-d4 b8-c7 f2-e3 f6-e5 g1-f2 c7-d6",
        "e3-d4 d4-c5 g7-f6 b2-c3 a7-b6 b6-a5 a1-b2 f6-g5 b2-c3 g5-h4 d4-c5 h8-g7 g3-f4 g7-f6 f2-e3 c7-d6 c3-b4 d8-c7 b4-a5 c7-d6",
        "e3-d4 d4-c5 g7-f6 b2-c3 a7-b6 f6-g5 a1-b2 g5-h4 b2-c3 h8-g7 g3-f4 g7-f6 f2-e3 c7-d6 f4-e5 b8-c7 g5-h6 c7-d6 h2-g3 b6-a5",
        "e3-d4 d4-c5 h6-g5 g3-h4 g5-f4 b2-c3 f4-g3 g7-h6 a1-b2 f8-g7 d2-e3 g3-h2 b2-c3 e7-d6 c3-d4 d6-e5 d4-c5 c7-b6 b8-c7 b4-a5",
        "e3-d4 d4-e5 h8-g7 b2-c3 b6-c5 c3-b4 g7-f6 f6-e5 g3-h4 e7-f6 f2-g3 e5-d4 e3-f4 f6-e5 e1-f2 f8-e7 f2-e3 e7-f6 a1-b2 f6-e5",
        "e3-d4 d4-e5 h8-g7 b2-c3 h6-g5 g3-h4 g5-f4 g7-h6 c3-b4 d6-e5 d2-e3 e5-d4 e1-d2 e7-f6 d2-e3 a7-b6 a1-b2 f8-e7 b2-c3 e7-d6",
        "e3-d4 d4xf6 g3-h4 c3-b4 f6-e5 g7xe5 h8-g7 g7-f6 b4-a5 b2-c3 h4xf6 c3-b4 e5-f4 f6-g5 e7xg5 d8-e7 b4-c5 d2-e3 c1xc5 a5xc3",
        "e3-d4 d6-c5 d2-c3 c5xe3 f2xd4 g7-f6 d4-c5 b6xd4 c3xg7 h8xf6 a5xc3 b2xd4 h6-g5 c1-b2 e7-d6 d4-e5 f6xd4 h4xf6 d6-e5 b2-c3",
        "e3-d4 d6-c5 d2-e3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b2-c3 f6-g5 g5-h4 g3-f4 g7-f6 f4-g5 h6xf4 e3xg5 a7-b6 b4-a5 b6-c5 c3-b4",
        "e3-d4 d6-c5 d2-e3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b2-c3 f6-g5 g7-f6 b4-a5 g5-h4 c3-d4 f6-g5 d4-c5 d6xb4 a5xc3 a7-b6 c3-d4",
        "e3-d4 d6-c5 d2-e3 e7-d6 g3-h4 d6-e5 f2-g3 b6-a5 d4xb6 a7xc5 c3-d4 e5xc3 b8-a7 c1-b2 a7xc5 e3-f4 c7-b6 b2-c3 f8-e7 e1-f2",
        "e3-d4 d6-c5 d2-e3 f6-e5 d4xf6 g7xe5 c3-b4 c5-d4 e3xc5 b6xd4 g3-f4 e5xg3 h2xf4 e7-d6 c1-d2 d8-e7 d2-c3 h8-g7 c3xe5 e7-f6",
        "e3-d4 d6-c5 d2-e3 f6-g5 c3-b4 e7-d6 b2-c3 g5-f4 g3xe5 d6xd2 c1xe3 d8-e7 b4xd6 e7xc5 h2-g3 c7-d6 g3-h4 g7-f6 h4-g5 h6xb4",
        "e3-d4 d6-c5 d2-e3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g3-f4 g7-f6 a1-b2 f6-g5 d4-c5 a5-b4 c5-d6 e7xc5 e3-d4 c5xe3",
        "e3-d4 d6-c5 d2-e3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g3-f4 g7-f6 c1-b2 f6-g5 e1-d2 h8-g7 d2-c3 e7-d6 d4-e5 b8-c7",
        "e3-d4 d6-c5 d2-e3 f6-g5 c3-b4 g5-h4 b4xd6 c7xc3 b2xd4 b6-a5 g3-f4 g7-f6 f4-e5 f6-g5 d4-c5 h8-g7 e5-d6 a5-b4 a1-b2 g5-f4",
        "e3-d4 d6-c5 f2-e3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 b2-c3 f6-e5 f4xd6 c7xe5",
        "e3-d4 d6-c5 f2-e3 c7-d6 c3-b4 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 f6-g5 e3-d4 g5-h4 g1-f2 h6-g5 b2-c3 g7-h6 a1-b2 h8-g7",
        "e3-d4 d6-c5 f2-e3 c7-d6 c3-b4 f6-g5 g1-f2 b6-a5 d4xb6 a5xc7 b4-c5 d6xb4 a3xc5 g5-h4 b2-c3 g7-f6 a1-b2 f6-g5 e3-d4 c7-b6",
        "e3-d4 d6-c5 f2-e3 c7-d6 c3-b4 f6-g5 g1-f2 g5-h4 b4-a5 d8-c7 g3-f4 g7-f6 f2-g3 h4xf2 e1xg3 h8-g7 f4-e5 d6xf4 g3xe5 h6-g5",
        "e3-d4 d6-c5 f2-e3 f6-g5 g3-h4 c7-d6 h4xf6 g7xe5 d4xf6 e7xg5 h8-g7 c3-b4 g7-f6 g3-h4 f8-e7 b4-a5 b8-c7 g1-f2 d6-e5 b2-c3",
        "e3-d4 d6-c5 f2-e3 h6-g5 e3-f4 g5xe3 d4xf2 c7-d6 c3-b4 f6-e5 b8-c7 d2-e3 g7-f6 e3-f4 c5-d4 a3-b4 b6-c5 b2-a3 h8-g7 g3-h4",
        "e3-d4 d6-e5 a3-b4 g5-h4 b4-c5 b6-a5 g3-f4 e5xg3 h2xf4 f6-g5 f2-g3 h4xf2 e1xg3 g5xe3 d4xf2 h6-g5 c3-d4 g5-h4 g3-f4 h8-g7",
        "e3-d4 d6-e5 a3-b4 h6-g5 b2-a3 g5-h4 b4-c5 f6-g5 d4xf6 b6xb2 a1xc3 g7xe5 a3-b4 c7-d6 b4-a5 b8-c7 g3-f4 g5xe3 f2xf6 e7xg5",
        "e3-d4 d6-e5 a3-b4 h6-g5 d2-e3 g5-f4 e3xg5 f6xh4 d4xf6 g7xe5 b4-a5 b6-c5 b2-a3 e7-d6 c1-d2 d8-e7 c3-b4 e7-f6 d2-e3 h8-g7",
        "e3-d4 d6xb4 c3xa5 f6-g5 b2-c3 g5-h4 g3-f4 h8-g7 f2-g3 h4xf2 g1xe3 g7-f6 h2-g3 e7-d6 a1-b2 d6-e5 f4xd6 c7xe5 a5xc7 b8xd6",
        "e3-d4 d6xb4 c3xa5 g7-f6 d2-c3 f6-g5 g3-h4 f8-g7 h4xf6 e7xg5 g7-f6 e5xg7 h6xf8 c3-d4 b6-c5 d4xb6 a7xc5 h2-g3 g5-h4 g3-f4",
        "e3-d4 d6xf4 g3xe5 b6-c5 d4xb6 f6xd4 c3xe5 a7xc5 d2-e3 e7-f6 c1-d2 f6xd4 d2-c3 f8-e7 c3xe5 e7-f6 e1-d2 f6xd4 d2-c3 d8-e7",
        "e3-d4 d6xf4 g3xe5 f8-e7 d2-e3 b6-a5 a3-b4 h6-g5 c1-d2 g7-h6 e5xg7 h6xf8 b4-c5 c7-b6 b2-a3 b8-c7 a1-b2 c7-d6 f2-g3 h2xf4",
        "e3-d4 e5-f4 g3xe5 d6xf4 d2-e3 f4xd2 c1xe3 b6-a5 a1-b2 f6-e5 d4xf6 g7xe5 e3-f4 e5xg3 f2xh4 f8-g7 g1-f2 h6-g5 h4xf6 g7xe5",
        "e3-d4 f6-e5 d2-e3 c7-d6 g3-h4 e5-f4 b6-c5 d2-e3 a1-b2 h8-g7 h2-g3 g7-f6 b2-c3 b8-c7 g3-f4 c7-b6 g1-f2 b6-a5 f2-e3 f6-e5",
        "e3-d4 f6-e5 d4xf6 g7xe5 a3-b4 h6-g5 g3-h4 g5-f4 b4-a5 b6-c5 b2-a3 c5-b4 a3xc5 d6xb4 f2-e3 b4-a3 e3xg5 e5-d4 c3xe5 c7-b6",
        "e3-d4 f6-e5 d4xf6 g7xe5 a3-b4 h6-g5 g3-h4 g5-f4 b4-a5 b6-c5 b2-a3 c5-d4 c3-b4 h8-g7 f2-e3 d4xf2 g1xg5 g7-h6 c1-b2 h6xf4",
        "e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 f8-g7 c3-b4 b6-a5 b4-c5 d6xb4 a3xc5 g7-f6 d2-c3 c7-d6 e1-d2 d6xb4 b2-a3 e5-f4 a3xc5 b8-c7",
        "e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 f8-g7 c3-b4 g7-f6 b2-c3 h8-g7 b4-a5 h6-g5 f2-g3 g7-h6 c3-b4 b6-c5 a1-b2 g5-f4 b2-c3 h6-g5",
        "e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 f8-g7 c3-b4 g7-f6 h2-g3 h8-g7 b4-a5 e5-f4 g3xe5 f6xd4 a3-b4 d4-c3 b2xd4 b6-c5 d4xb6 a7xa3",
        "e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 f8-g7 f2-g3 b6-a5 a3-b4 a7-b6 d2-e3 b6-c5 b2-a3 g7-f6 c3-d4 e5xc3 b4xd2 b8-a7 g3-f4 f6-e5",
        "e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 f8-g7 f2-g3 e5-f4 g3xe5 d6xf4 h4-g5 f4-e3 d2xf4 g7-f6 c3-d4 f6xh4 b2-c3 h4-g3 d4-e5 e7-f6",
        "e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 h8-g7 c3-b4 g7-f6 b4-a5 e5-f4 b2-c3 f6-g5 h4xf6 e7xg5 c3-b4 d8-e7 f2-g3 g5-h4 g3xe5 d6xf4",
        "e3-d4 f6-e5 d4xf6 g7xe5 g3-h4 h8-g7 c3-b4 g7-f6 b4-a5 e5-f4 f6-g5 h4xf6 e7xg5 c3-b4 d8-e7 f2-g3 g5-h4 g3xe5 d6xf4 a1-b2",
        "e3-d4 f6-g5 b2-c3 e7-f6 a1-b2 f6-e5 c3-d4 g7-f6 f6-g5 d2-e3 h8-g7 c3-b4 e7-d6 b4-c5 g7-f6 e1-d2 f6-e5 c1-b2 c7-b6 b2-a3",
        "e3-d4 f6-g5 c3-b4 d6-c5 b4xd6 e7xe3 f2xd4 f8-e7 a3-b4 c7-d6 b2-a3 b6-c5 d4xb6 a7xc5 e1-f2 g5-h4 g3-f4 g7-f6 a1-b2 f6-e5",
        "e3-d4 f6-g5 c3-b4 d6-c5 b4xd6 e7xe3 f2xd4 g5-h4 g1-f2 b6-c5 d4xb6 a7xc5 b2-c3 g7-f6 d2-e3 f8-e7 c3-d4 c7-b6 a1-b2 e7-d6",
        "e3-d4 f6-g5 c3-b4 g5-h4 b4-c5 d6xb4 a3xc5 h6-g5 b2-a3 b6-a5 a1-b2 c7-b6 b2-c3 e7-f6 g3-f4 g5xe3 d2xf4 f6-e5 f4xd6 d8-c7",
        "e3-d4 f6-g5 c3-b4 g5-h4 b4-c5 d6xb4 a3xc5 h6-g5 d2-e3 g7-h6 g3-f4 c7-d6 b2-a3 d6xb4 a3xc5 b8-c7 a1-b2 c7-d6 b2-a3 d6xb4",
        "e3-d4 f6-g5 c3-b4 g5-h4 b4-c5 d6xb4 a3xc5 h6-g5 g3-f4 g5xe3 d2xf4 g7-h6 f2-g3 h4xf2 g1xe3 h8-g7 h2-g3 g7-f6 g3-h4 f6-e5",
        "e3-d4 f6-g5 d2-e3 b6-a5 c1-d2 g5-h4 d4-c5 d6xb4 a3xc5 g7-f6 a5xc3 b2xd4 f6-g5 a1-b2 e7-f6 g3-f4 f6-e5 d4xf6 g5xe7 b2-a3",
        "e3-d4 f6-g5 d2-e3 g5-h4 c1-d2 b6-a5 d4-c5 d6xb4 a3xc5 h6-g5 c3-b4 a5xc3 d2xb4 g5-f4 g3xe5 e7-d6 c5xe7 f8xd2 e1xc3 a7-b6",
        "e3-d4 f6-g5 d2-e3 g5-h4 c1-d2 d6-c5 c3-b4 g7-f6 b4xd6 c7xc3 b2xd4 b6-a5 g3-f4 f6-g5 a1-b2 a7-b6 d4-e5 d8-c7 b2-c3 e7-d6",
        "e3-d4 f6-g5 d2-e3 g5-h4 c1-d2 g7-f6 c3-b4 b6-a5 d4-c5 a5xc3 b2xd4 d6xb4 a3xc5 f6-g5 a1-b2 c7-b6 b2-a3 h8-g7 g3-f4 g7-f6",
        "e3-d4 f6-g5 d2-e3 g5-h4 c1-d2 g7-f6 c3-b4 h8-g7 d4-c5 b6xd4 e3xc5 f6-g5 b4-a5 d6xb4 a5xc3 e7-d6 a3-b4 a7-b6 b4-a5 b6-c5",
        "e3-d4 f6-g5 d2-e3 g5-h4 c1-d2 g7-f6 d4-c5 b6xd4 c3xg7 h8xf6 a3-b4 a7-b6 b4-a5 f6-g5 b2-c3 g5-f4 e3xg5 h4xf6 d2-e3 e3-d4",
        "e3-d4 f6-g5 d2-e3 g5-h4 c3-b4 h6-g5 b4-c5 d6xb4 a3xc5 g7-h6 b2-a3 e7-f6 a1-b2 f6-e5 d4xf6 g5xe7 g3-f4 b6xd4 e3xc5 c7-b6",
        "e3-d4 f6-g5 d2-e3 g7-f6 c3-b4 g5-h4 b4-c5 d6xb4 a3xc5 f6-e5 d4xf6 b6xd4 e3xc5 e7xg5 b2-c3 h8-g7 a1-b2 g7-f6 c5-b6 a7xc5",
        "e3-d4 f6-g5 d2-e3 g7-f6 g3-h4 d6-e5 f2-g3 g5-f4 e3xg5 h6xf4 h4-g5 f6xf2 g1xg5 e7-f6 g5xe7 d8xf6 a3-b4 c7-d6 b2-a3 b6-c5",
        "e3-d4 f6-g5 f2-e3 g5-h4 g3-f4 d6-c5 c3-b4 h4-g3 b4xd6 c7xc3 d2xb4 g3xe5 e1-d2 e5-f4 e3xg5 h6xf4 d2-e3 f4xd2 c1xe3 g7-f6",
        "e3-d4 f6-g5 f2-e3 g7-f6 g1-f2 d6-e5 g3-f4 e5xg3 h2xf4 g5-h4 d4-c5 b6xd4 c3xg7 h8xf6 b2-c3 a7-b6 c3-d4 b6-a5 c1-b2 f6-g5",
        "e3-d4 f6-g5 g3-h4 b6-c5 d4xb6 a7xc5 h4xf6 g7xe5 c3-d4 c5xe3 f2xf6 e7xg5 b2-c3 h8-g7 a1-b2 d6-e5 a3-b4 c7-b6 b2-a3 f8-e7",
        "e3-d4 f6-g5 g3-h4 d6-c5 h4xf6 c5xe3 f2xd4 e7xg5 a3-b4 g5-h4 d2-e3 h6-g5 h2-g3 h4xf2 e1xg3 c7-d6 b4-a5 g5-h4 a5xe5 h4xf2",
        "e3-d4 f6-g5 g3-h4 d6-c5 h4xf6 c5xe3 f2xd4 g7xe5 d4xf6 e7xg5 c3-d4 g5-f4 a3-b4 c7-d6 b2-a3 b6-c5 d4xb6 a7xc5 g1-f2 h6-g5",
        "e3-d4 f6-g5 g3-h4 e7-d6 d6-c5 g7-f6 g3-f4 f8-e7 g1-f2 b8-c7 c3-d4 h8-g7 d2-e3 c7-d6 b2-c3 b6-c5 c1-b2 c5-b4 f6-g5 c3-d4",
        "e3-d4 f6-g5 g3-h4 g7-f6 d4-c5 b6xd4 c3xg7 h8xf6 b2-c3 d6-e5 c3-b4 a7-b6 b4-a5 e5-d4 h2-g3 e7-d6 d2-e3 b6-c5 c1-b2 d6-e5",
        "e3-d4 g5-f4 c7xe5 e7xc5 b6xd4 b6-c7 b8xd6 d8xb6 a5xc7 b8xd6 e3-f4 g5xe3 f2xd8 e3-d4 e5xc3 a7-b8 d6-c5 d8-c7 a5-b6 c7xa5",
        "e3-d4 g5-h4 a3-b4 b6-c5 b4xd6 e7xe3 d2xf4 f6-g5 b2-c3 g5xe3 f2xd4 h4xf2 g1xe3 g7-f6 h2-g3 f8-e7 c3-b4 f6-e5 d4xf6 e7xg5",
        "e3-d4 g5-h4 c3-b4 b6-a5 b2-c3 f6-g5 d4-c5 e7-f6 d2-e3 d8-e7 g5-f4 e3xg5 h6xf4 g3xe5 f6xb6 d2-e3 b6-c5 b4xd6 e7xc5 c3-d4",
        "e3-d4 g5-h4 d2-e3 f6-e5 a3-b4 h8-g7 b2-c3 g7-f6 f6-g5 d2-c3 e7-d6 g3-f4 d6-e5 e3-d4 a7-b6 a1-b2 d6-e5 c1-d2 h6-g5 d2-e3",
        "e3-d4 g5-h4 d2-e3 f6-e5 d4xf6 g7xe5 a3-b4 h8-g7 e3-d4 e5xc3 b4xd2 b6-c5 b2-c3 c5-b4 c3-d4 b4-a3 g3-f4 g7-f6 f4-g5 h6xf4",
        "e3-d4 g5-h4 d2-e3 f6-g5 a3-b4 g5-f4 g3xe5 e7-d6 e5-f6 g7xc3 b4xd2 h6-g5 e3-f4 g5xe3 d2xf4 d6-e5 f4xd6 c7xe5 a5xc7 b8xd6",
        "e3-d4 g5-h4 d4-c5 b6xd4 c3xg7 h8xf6 a3-b4 f6-g5 b2-c3 a7-b6 b4-a5 d6-e5 g3-f4 e5xg3 h2xf4 g5xe3 d2xf4 b6-c5 f2-e3 c5-b4",
        "e3-d4 g7-f6 d2-e3 d6-e5 a3-b4 f6-e5 h8-g7 a1-b2 d8-c7 b2-c3 a7-b6 g3-f4 g7-f6 c3-d4 f6-g5 f2-e3 b6-a5 d2-c3 c7-b6 d4-e5",
        "e3-d4 h2xf4 d4-c5 b6xd4 c3xg3 a7-b6 b2-c3 b6-c5 c3-b4 f6-e5 g7-f6 g1-h2 e5-d4 f2-g3 d4-c3 b4-a5 c5-b4 a3xc5 d6xb4 c1-b2",
        "e3-d4 h2xf4 d4-c5 b6xd4 c3xg3 f6-e5 d2-e3 h6-g5 b4-a5 g5-h4 e7-d6 b4-c5 d6xb4 a5xc3 c7-d6 c1-d2 a7-b6 c3-d4 e5xc3 b2xd4",
        "e3-d4 h2xf4 d4-c5 b6xd4 c3xg3 f6-e5 d2-e3 h6-g5 e3-d4 e5xc3 b2xd4 g7-f6 a3-b4 h8-g7 f2-e3 g7-h6 g3-f4 g5-h4 c1-d2 f6-g5",
        "e3-d4 h2xf4 d4-c5 b6xd4 c3xg3 f6-e5 g3-h4 a7-b6 b2-c3 g7-f6 b8-a7 c1-b2 h8-g7 e3-d4 b6-c5 d4xb6 a7xc5 c3-b4 e5-d4 b4-a5",
        "e3-d4 h2xf4 d4-c5 b6xd4 c3xg3 f6-e5 g3-h4 e5-f4 b2-c3 a7-b6 f4-g3 f2xh4 h6xf4 c1-b2 b6-c5 b4xd6 e7xc5 c3-b4 c7-d6 b2-c3",
        "e3-d4 h2xf4 d4-c5 b6xd4 c3xg3 h6-g5 d2-e3 f6-e5 a3-b4 g5-h4 e5xc3 b4xd2 g7-f6 d2-e3 f6-e5 e3-d4 e5xc3 b2xd4 h8-g7 a1-b2",
        "e3-d4 h2xf4 d4-c5 b6xd4 c3xg3 h6-g5 d2-e3 g5-h4 b2-c3 f6-e5 g7-f6 c3-d4 e5xc3 b4xd2 f6-e5 c1-b2 h8-g7 e3-d4 e5xc3 b2xd4",
        "e3-d4 h2xf4 d4-e5 f6xd4 c3xg3 e7-f6 b2-c3 f6-e5 g3-h4 h8-g7 g7-f6 a1-b2 h6-g5 b2-a3 g5-f4 d2-e3 f4xd2 c1xe3 d8-e7 f2-g3",
        "e3-d4 h2xf4 d4-e5 f6xd4 c3xg3 g7-f6 b2-c3 b6-c5 c3-b4 f6-e5 e7-f6 d2-e3 e5-d4 h4-g5 h6xd2 e1xg7 f8xh6 c1-d2 c5-d4 d2-e3",
        "e3-d4 h2xf4 d4-e5 f6xd4 c3xg3 h8-g7 d2-e3 g7-f6 b2-c3 f6-g5 g5-f4 g3xe5 d6xd2 c1xe3 b6-c5 d4xb6 a7xc5 e3-d4 c5xe3 f2xd4",
        "e3-d4 h6-g5 a3-b4 g5-h4 b2-a3 f6-g5 d2-e3 g5-f4 c3-d4 h8-g7 a1-b2 f6-e5 b2-c3 g7-h6 f2-e3 h6-g5 e3-d4 g5-h4 e1-f2 d6-e5",
        "e3-d4 h6-g5 a3-b4 g5-h4 d2-e3 f6-g5 c3-d4 g5-f4 d2-e3 h8-g7 b2-c3 g7-h6 h2-g3 f6-g5 g3-f4 e7-f6 f2-g3 b6-c5 g3-h4 c5-b4",
        "e3-d4 h6-g5 b4-a5 g5-h4 c3-b4 d6-e5 d2-e3 f6-e5 a1-b2 e5-f4 b2-c3 e7-d6 c3-b4 a7-b6 d2-e3 f6-e5 h2-g3 b6-c5 g3-h4 g7-h6",
        "e3-d4 h6-g5 c3-b4 e5xc3 b2xd4 d6-c5 b4xd6 c7xc3 a5xc7 d8xb6 d2xb4 f6-e5 a1-b2 g7-f6 b2-c3 h8-g7 f2-e3 g7-h6 e1-f2 g5-f4",
        "e3-d4 h6-g5 f2-e3 g5-f4 g1-f2 a7-b6 b6-c5 c3-b4 e7-f6 d2-e3 f6-g5 b2-c3 h8-g7 c3-d4 g7-f6 a1-b2 f6-e5 d2-c3 f8-g7 c3-b4",
        "e3-d4 h6-g5 g3-h4 d6-e5 a3-b4 g7-h6 b2-a3 b6-a5 f2-g3 g5-f4 c7-b6 a3-b4 b8-c7 g1-f2 f8-g7 a1-b2 h6-g5 d2-e3 f4xd2 c1xe3",
        "e3-d4 h6-g5 g3-h4 d6-e5 a3-b4 g7-h6 b4-a5 g5-f4 b2-a3 b6-c5 d4xb6 a7xc5 c3-b4 e7-d6 f2-g3 f8-e7 d2-e3 f4xd2 c1xe3 e5-d4",
        "e3-d4 h6-g5 g3-h4 d6-e5 a3-b4 g7-h6 b4-c5 g5-f4 f2-e3 f8-g7 e3xg5 h6xf4 g1-f2 g7-h6 b2-a3 h6-g5 a3-b4 b6-a5 f2-g3 h8-g7",
        "e3-d4 h6-g5 g3-h4 d6-e5 f2-e3 c7-d6 h2-g3 b8-c7 g3-f4 e5xg3 h4xf2 g5-f4 e3xg5 f6xh4 c3-b4 d6-e5 d4xf6 g7xe5 b4-a5 e7-d6",
        "e3-d4 h6-g5 g3-h4 d6-e5 f2-e3 c7-d6 h2-g3 b8-c7 g3-f4 e5xg3 h4xf2 g5-f4 e3xg5 f6xh4 d2-e3 e7-f6 c1-d2 b6-c5 d4xb6 a7xc5",
        "e3-d4 h6-g5 g3-h4 d6-e5 f2-e3 g7-h6 g1-f2 b6-a5 d4-c5 e5-f4 c3-d4 c7-b6 b2-c3 b8-c7 c1-b2 f8-g7 a3-b4 c7-d6 b2-a3 d6-e5",
        "e3-d4 h6-g5 g3-h4 d6-e5 f2-e3 g7-h6 g1-f2 g5-f4 e3xg5 h6xf4 f2-e3 h8-g7 e3xg5 g7-h6 e1-f2 h6xf4 f2-e3 f8-g7 e3xg5 g7-h6",
        "e3-d4 h6-g5 g3-h4 d6-e5 f2-e3 g7-h6 g1-f2 g5-f4 e3xg5 h6xf4 h8-g7 e3xg5 g7-h6 e1-f2 h6xf4 f2-e3 f8-g7 e3xg5 g7-h6 a3-b4",
        "e3-d4 h6-g5 g3-h4 e7-d6 d4-e5 b4-c5 a7-b6 b6-c5 g3-f4 g7-h6 b2-c3 f8-g7 c1-b2 b8-a7 h2-g3 c7-b6 e1-f2 d8-c7 c3-d4 a5-b4",
        "e3-d4 h6-g5 g3-h4 g7-h6 d4-c5 d6xb4 a3xc5 g5-f4 f2-g3 f8-g7 b2-a3 c7-d6 a1-b2 d6xb4 a3xc5 b8-c7 c3-b4 c7-b6 b2-a3 b6xd4",
        // --- a3-b4 (119 linhas de campeonato) ---
        "a3-b4 f6-e5 e3-d4 b6-c5 d4xf6 c5xa3",
        "a3-b4 h6-g5 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 f6-e5 d2-e3",
        "a3-b4 b6-a5 g3-h4 f6-g5 h4xf6 e7xg5 b2-a3 c7-b6 h2-g3 g5-h4 e3-d4 g7-f6 c1-b2",
        "a3-b4 h6-g5 b4-a5 g5-h4 e3-d4 d6-e5 d2-e3 g7-h6 b2-a3 h8-g7 c7-d6 a5xc7 d8xb6 e1-d2",
        "a3-b4 a5xc3 b2xd4 b6-a5 d4-e5 d6xf4 e3xg5 h6xf4 g3xe5 a7-b6 b6-c5 b2-a3 e7-f6 c1-b2 f6xd4 d2-c3 c7-b6 c3xe5 b8-a7 h4-g5",
        "a3-b4 b2-a3 a1-b2 e3-d4 b6-a5 c7-b6 b6-c5 c5xe3 f2xd4 d4xb6 d2-e3 g1-f2 d6-c5 a5xc7 a7-b6 b6-a5 c1-d2 b4-c5 c5-b6 e3-d4",
        "a3-b4 b6-a5 b2-a3 a7-b6 a1-b2 d6-e5 e3-d4 e7-d6 f2-e3 f8-e7 g3-h4 h6-g5 h2-g3 b6-c5 d4xb6 g5-f4 e3xg5 e5-d4 c3xe5 a5xa1",
        "a3-b4 b6-a5 b2-a3 a7-b6 a1-b2 d6-e5 e3-d4 e7-d6 f2-e3 f8-e7 h6-g5 h2-g3 b6-c5 d4xb6 g5-f4 e3xg5 e5-d4 c3xe5 a5xa1 g5-h6",
        "a3-b4 b6-a5 b2-a3 a7-b6 e3-d4 b8-a7 d2-e3 f6-g5 c1-b2 e7-f6 g3-h4 f8-e7 f2-g3 g5-f4 e3xg5 h6xf4 g3xe5 d6xf4 e1-f2 c7-d6",
        "a3-b4 b6-a5 b2-a3 a7-b6 e3-d4 d6-c5 b4xd6 e7xe3 d2xf4 f6-g5 f2-e3 c7-d6 c1-d2 d8-c7 g3-h4 b6-c5 h4xf6 g7xg3 h2xf4 h8-g7",
        "a3-b4 b6-a5 b2-a3 a7-b6 e3-d4 d6-c5 b4xd6 e7xe3 d2xf4 f6-g5 f2-e3 g5-h4 g1-f2 c7-d6 c1-d2 f8-e7 c3-d4 d8-c7 f4-e5 d6xf4",
        "a3-b4 b6-a5 b2-a3 a7-b6 e3-d4 f6-e5 d4xf6 e7xg5 c1-b2 b6-c5 d2-e3 c7-b6 e3-d4 c5xe3 f2xd4 b6-c5 d4xb6 a5xc7 c3-d4 g5-f4",
        "a3-b4 b6-a5 b2-a3 a7-b6 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 d6-e5 d4xf6 g7xe5 d2-e3 c7-d6 c3-d4 a5xc3 d4xf6 f8-e7",
        "a3-b4 b6-a5 b2-a3 a7-b6 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 d6-e5 d4xf6 g7xe5 d2-e3 c7-d6 c3-d4 e5xc3 b4xd2 h6-g5",
        "a3-b4 b6-a5 b2-a3 a7-b6 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 d6-e5 d4xf6 g7xe5 d2-e3 c7-d6 h2-g3 h6-g5 c3-d4 e5xc3",
        "a3-b4 b6-a5 b2-a3 a7-b6 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 d6-e5 d4xf6 g7xe5 d2-e3 c7-d6 h2-g3 h6-g5 e1-f2 g5-h4",
        "a3-b4 b6-a5 b2-a3 a7-b6 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 d6-e5 d4xf6 g7xe5 d2-e3 h6-g5 c3-d4 e5xc3 b4xd2 g5-h4",
        "a3-b4 b6-a5 b2-a3 a7-b6 g3-f4 b6-c5 f2-g3 c7-b6 g1-f2 b8-a7 g3-h4 f6-g5 h4xf6 g7xg3 f2xh4 h8-g7 h2-g3 g7-f6 g3-f4 f6-g5",
        "a3-b4 b6-a5 b2-a3 a7-b6 g3-h4 f6-e5 e3-d4 b8-a7 d4xf6 e7xg5 h4xf6 g7xe5 f2-e3 e5-f4 h8-g7 c3-d4 e5xc3 e3-d4 c3xe5 c1-b2",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 d6-c5 b4xd6 e7xe3 d2xf4 f8-e7 g1-f2 f6-g5 f2-e3 a7-b6 c3-d4 e7-d6",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 d6-c5 d4xb6 a5xc7 c3-d4 h6-g5 b2-c3 g5-h4 g1-f2 a7-b6 b4-c5 b6-a5",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 b6-c5 e3-d4 c5xe3 f2xd4 d6-c5 d4xb6 a5xc7 c3-d4 h6-g5 b2-c3 g5-h4 g1-f2 f6-e5 d4xf6 g7xe5",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 d6-c5 b4xd6 e7xc5 g3-f4 f6-g5 c3-d4 b8-c7 f4-e5 g7-f6 e5xg7 h8xf6 d4-e5 f6xd4 a3-b4 a5xa1",
        "a3-b4 b6-a5 b2-a3 c7-b6 a1-b2 d6-e5 g3-f4 e5xg3 h2xf4 b6-c5 b4xd6 e7xc5 f4-e5 f6xd4 c3xe5 f8-e7 d2-c3 b8-c7 e1-d2 g7-f6",
        "a3-b4 b6-a5 b2-a3 d6-e5 e3-f4 a7-b6 f4xd6 c7xe5 c1-b2 h6-g5 d2-e3 g5-h4 e3-d4 e7-d6 d4-c5 b6xd4 g3-f4 e5xg3 c3xc7 b8xd6",
        "a3-b4 b6-a5 b2-a3 d6-e5 e3-f4 e7-d6 d2-e3 c7-b6 c3-d4 a5xc3 d4xb2 f6-g5 a3-b4 g5-h4 b2-a3 b6-c5 a1-b2 g7-f6 b4-a5 a7-b6",
        "a3-b4 b6-a5 b2-a3 d6-e5 e3-f4 e7-d6 d2-e3 c7-b6 e3-d4 b6-c5 d4xb6 a5xc7 b4-a5 a7-b6 f2-e3 f6-g5 c3-b4 g5-h4 e3-d4 h4xf2",
        "a3-b4 b6-a5 b2-a3 d6-e5 e3-f4 e7-d6 d2-e3 c7-b6 e3-d4 d6-c5 f4xd6 c5xe7 c1-b2 h6-g5 b4-c5 g5-h4 g3-f4 g7-h6 f4-g5 h6xf4",
        "a3-b4 b6-a5 b2-a3 f6-e5 b4-c5 d6xb4 a3xc5 g7-f6 a1-b2 h8-g7 g3-f4 e5xg3 f2xh4 f6-e5 e3-f4 e5xg3 h4xf2 c7-b6 c3-d4 b8-c7",
        "a3-b4 b6-a5 b2-a3 f6-g5 b4-c5 d6xb4 a3xc5 c7-d6 a1-b2 d6xb4 b2-a3 b8-c7 a3xc5 c7-d6 c3-b4 a5xc3 d2xb4 d6-e5 g3-f4 e5xg3",
        "a3-b4 b6-a5 b2-a3 f6-g5 g3-h4 g7-f6 b4-c5 d6xb4 a3xc5 g5-f4 e3xg5 h6xf4 a1-b2 h8-g7 f2-e3 c7-d6 e3xg5 d6xb4 b2-a3 g7-h6",
        "a3-b4 b6-a5 b2-a3 h6-g5 g3-h4 g7-h6 f2-g3 h8-g7 a1-b2 d6-c5 g3-f4 c7-d6 e1-f2 f6-e5 f2-e3 g7-f6 c3-d4 h6-g5 b2-c3 g5-h4",
        "a3-b4 b6-a5 b4-c5 f6-g5 b2-a3 c7-b6 c1-b2 e7-f6 g5-f4 h6-g5 g3-f4 d8-e7 d4-c5 g7-f6 g1-f2 f6-g5 h2-g3 h8-g7 c3-b4 g7-f6",
        "a3-b4 b6-a5 b4-c5 f6-g5 c3-d4 c7-b6 b2-c3 d8-c7 a1-b2 g7-f6 e7-d6 d4-c5 d8-e7 h2-g3 c7-d6 b2-a3 e7-d6 e3-f4 h8-g7 d4-e5",
        "a3-b4 b6-a5 b4-c5 g7-f6 c5-b6 e7-d6 f6-g5 b6-a7 d6-e5 g3-f4 f8-e7 c3-d4 e7-d6 f2-g3 h8-g7 g1-f2 g7-f6 d4-c5 f4-e5 c7-d6",
        "a3-b4 b6-a5 d2-e3 e5-f4 e3xg5 f6xh4 b2-a3 g7-f6 c1-d2 h8-g7 b8-a7 d2-e3 c7-b6 e1-d2 b6-c5 d4xb6 a7xc5 e3-f4 f6-e5 d2-e3",
        "a3-b4 b6-a5 e3-d4 a7-b6 d4-e5 f6xd4 c3xe5 a5xc3 b2xd4 d6xf4 g3xe5 g7-f6 e5xg7 h8xf6 a1-b2 c7-d6 b2-c3 b6-a5 h2-g3 f6-g5",
        "a3-b4 b6-a5 e3-d4 a7-b6 f2-e3 b8-a7 b2-a3 f6-e5 d4xf6 e7xg5 g5xe3 d2xf4 g7-f6 g3-h4 f8-e7 e1-d2 f6-e5 c1-b2 e5xg3 h2xf4",
        "a3-b4 b6-a5 e3-d4 a7-b6 f2-e3 b8-a7 b2-a3 f6-e5 d4xf6 g7xe5 f8-g7 d4xf6 g7xe5 g3-f4 e5xg3 h2xf4 h8-g7 e1-f2 e7-f6 f2-g3",
        "a3-b4 b6-a5 e3-d4 d6-c5 b4xd6 e7xe3 f2xd4 c7-b6 g1-f2 b6-c5 d4xb6 a5xc7 d2-e3 f6-g5 c3-d4 f8-e7 c1-d2 c7-d6 b2-c3 a7-b6",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 e7xg5 b2-a3 c7-b6 c1-b2 b6-c5 d2-e3 a7-b6 e3-d4 c5xe3 f2xd4 b6-c5 d4xb6 a5xc7 c3-d4 g5-f4",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 e7xg5 d2-e3 c7-b6 b2-a3 g5-h4 g7-f6 c1-b2 f6-e5 d4xf6 h6-g5 e1-d2 g5xe7 g3-f4 d6-c5 b4xd6",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 g7-f6 h2-g3 f6-g5 b4-c5 d6xb4 b2-a3 f8-e7 a3xc5 c7-d6 a1-b2 d6xb4",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 g7-f6 h2-g3 f8-g7 g1-h2 a7-b6 d2-e3 f6-g5 e1-f2 b6-c5 d4xb6 b8-a7",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 g7-f6 h2-g3 h6-g5 g3-h4 f6-e5 h4xf6 e5xg7 b2-a3 g7-f6 c1-b2 f8-e7",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 e7xg5 g3-f4 g5xe3 f2xd4 g7-f6 h6-g5 b2-a3 d6-e5 b4-c5 c7-b6 g1-h2 g5-f4 g3-h4 h8-g7 c1-b2",
        "a3-b4 b6-a5 e3-d4 f6-e5 d4xf6 g7xe5 d2-e3 a7-b6 c3-d4 a5xc3 d4xf6 e7xg5 b2xd4 g5-h4 a1-b2 h6-g5 b2-a3 d6-e5 d4xf6 g5xe7",
        "a3-b4 b6-a5 e3-d4 f6-g5 d4-e5 d6xf4 g3xe5 e7-d6 f2-g3 d6xf4 g3xe5 f8-e7 g1-f2 e7-d6 f2-g3 d6xf4 g3xe5 g7-f6 e5xg7 h6xf8",
        "a3-b4 b6-a5 e3-d4 f6-g5 g3-h4 a7-b6 h4xf6 g7xe5 d4xf6 e7xg5 d2-e3 g5-f4 e3xg5 h6xf4 b2-a3 h8-g7 f2-g3 d8-e7 g3xe5 d6xf4",
        "a3-b4 b6-a5 e3-d4 h6-g5 d4-e5 d6xf4 g3xe5 f6xd4 c3xe5 a5xc3 b2xd4 a7-b6 a1-b2 g5-h4 b2-c3 b6-a5 c3-b4 a5xc3 d4xb2 c7-b6",
        "a3-b4 b6-a5 e3-d4 h6-g5 d4-e5 f6xd4 c3xe5 d6xf4 g3xe5 a5xc3 b2xd4 g7-h6 a1-b2 g5-h4 b2-c3 a7-b6 c1-b2 h6-g5 b2-a3 h8-g7",
        "a3-b4 b6-a5 e3-d4 h6-g5 g3-h4 d6-e5 b4-c5 g5-f4 f2-e3 g7-h6 e3xg5 h6xf4 c5-d6 e7xe3 c3-b4 a5xc3 b2xf2 e5-d4 f2-e3 d4xf2",
        "a3-b4 b6-a5 e3-d4 h6-g5 g3-h4 d6-e5 f2-g3 g7-h6 b2-a3 g5-f4 a7-b6 d2-e3 f4xd2 c3xe1 e5xc3 b4xd2 b6-c5 f2-e3 c7-d6 a1-b2",
        "a3-b4 b6-a5 e3-d4 h6-g5 g3-h4 g7-h6 b2-a3 g5-f4 b4-c5 d6xb4 a3xc5 f4-e3 d2xf4 c7-d6 e1-d2 d6xb4 f2-e3 f8-g7 a1-b2 b4-a3",
        "a3-b4 b6-a5 e3-d4 h6-g5 g3-h4 g7-h6 b2-a3 g5-f4 f2-e3 c7-b6 e3xg5 h6xf4 b4-c5 d6xb4 a3xc5 b8-c7 a1-b2 f8-g7 g1-f2 f6-e5",
        "a3-b4 b6-a5 f4-g5 a1-b2 a7-b6 e5-f4 f2-g3 e7-d6 g1-f2 d8-e7 f2-g3 e7-d6 e1-f2 f8-e7 f2-g3 e7-d6 d2-e3 b6-c5 h2-g3 c7-d6",
        "a3-b4 b6-a5 f4-g5 a1-b2 a7-b6 h8-g7 b2-c3 g7-f6 f2-e3 b6-a5 g3-h4 c7-b6 h2-g3 b6-c5 g3-f4 c5-b4 f2-g3 d6-c5 g3-h4 e7-d6",
        "a3-b4 b6-a5 g3-h4 f6-g5 h4xf6 e7xg5 e3-f4 g5xe3 f2xd4 g7-f6 h2-g3 f6-g5 e1-f2 g5-f4 g3xe5 d6xf4 g1-h2 d8-e7 b4-c5 h6-g5",
        "a3-b4 b6-c5 b2-a3 f6-e5 e3-f4 g7-f6 d2-e3 f6-g5 g3-h4 e5xg3 h4xf6 e7xg5 f2xf6 f8-e7 h2-g3 e7xg5 g3-f4 h8-g7 a1-b2 g7-f6",
        "a3-b4 b6-c5 b2-a3 f6-g5 c3-d4 g7-f6 d4xb6 c7xc3 d2xb4 h8-g7 a1-b2 d8-c7 b4-a5 g5-h4 a3-b4 f6-e5 b4-c5 d6xb4 a5xc3 g7-f6",
        "a3-b4 b6-c5 b2-a3 f6-g5 g3-f4 g5-h4 a1-b2 g7-f6 f4-g5 h6xf4 e3xg5 c7-b6 d2-e3 b6-a5 e3-d4 c5xe3 f2xd4 a7-b6 g5-h6 f6-g5",
        "a3-b4 b6-c5 b4-a5 c5-b4 c3-d4 b4-a3 b2-c3 f6-g5 g3-h4 a7-b6 h4xf6 e7xg5 h2-g3 g7-f6 a1-b2 g5-h4 g3-f4 d6-c5 d4-e5 f6xd4",
        "a3-b4 b6-c5 b4-a5 c5-b4 c3-d4 b4-a3 b2-c3 f6-g5 g3-h4 g7-f6 d6-e5 g3-f4 e5xg3 h2xf4 e7-d6 e1-f2 f8-g7 c3-b4 a3xc5 d4xb6",
        "a3-b4 b6-c5 b4-a5 c5-b4 c3-d4 b4-a3 d4-c5 d6xb4 a5xc3 a7-b6 c3-d4 b6-a5 g3-f4 f6-g5 b2-c3 e7-d6 f2-g3 g5-h4 a1-b2 h4xf2",
        "a3-b4 b6-c5 b4-a5 c5-b4 c3-d4 b4-a3 d4-c5 d6xb4 a5xc3 a7-b6 g3-f4 b6-c5 c3-b4 f6-g5 b4xd6 c7xg3 f2xf6 g7xe5 e3-d4 e5xc3",
        "a3-b4 b6-c5 b4-a5 c5-b4 g3-h4 b4-a3 h2-g3 f6-e5 e3-f4 a7-b6 b6-c5 c3-d4 e5xc3 b2xb6 d6-e5 f4xd6 e7xa7 a1-b2 g7-f6 e3-f4",
        "a3-b4 b6-c5 b4-a5 c5-b4 g3-h4 f6-e5 b2-a3 e5-f4 a3xc5 d6xb4 e3xg5 h6xf4 c3-d4 b4-a3 a1-b2 g7-f6 f2-g3 f8-g7 g3xe5 e7-d6",
        "a3-b4 b6-c5 b4-a5 c5-b4 g3-h4 f6-e5 h2-g3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b2-a3 c7-d6 a3xc5 d6xb4 a5-b6 a7xc5 c3xa5 g7-f6",
        "a3-b4 b6-c5 b4-a5 c5-b4 g3-h4 f6-g5 h4xf6 g7xe5 c3-d4 e5xc3 b2xd4 b4-a3 h2-g3 h8-g7 d4-c5 d6xb4 a5xc3 g7-f6 c3-d4 c7-d6",
        "a3-b4 b6-c5 b4-a5 c5-b4 g3-h4 f6-g5 h4xf6 g7xe5 h2-g3 b4-a3 c3-d4 e5xc3 b2xd4 h8-g7 a1-b2 g7-f6 b2-c3 f6-g5 g3-h4 a7-b6",
        "a3-b4 d6-e5 b2-a3 f6-g5 e3-f4 g5xe3 d2xd6 c7xe5 b4-a5 h6-g5 a5xc7 b8xd6 a3-b4 g5-f4 f2-e3 f4xd2 c1xe3 a7-b6 b4-a5 d6-c5",
        "a3-b4 d6-e5 b2-a3 f6-g5 e3-f4 g5xe3 d2xd6 c7xe5 b4-a5 h6-g5 a5xc7 b8xd6 a3-b4 g7-f6 f2-e3 g5-h4 e3-d4 h4xf2 e1xg3 a7-b6",
        "a3-b4 d6-e5 e3-d4 h6-g5 b4-a5 e7-d6 b2-a3 g5-h4 d2-e3 f6-g5 d4xf6 g5xe7 a1-b2 g7-f6 c3-d4 b6-c5 d4xb6 a7xc5 e3-d4 c5xe3",
        "a3-b4 d6-e5 e3-d4 h6-g5 b4-a5 g5-h4 d2-e3 e7-d6 e3-f4 g7-h6 f2-e3 h4xf2 e1xg3 f8-g7 c3-b4 e5xc3 b4xd2 f6-e5 b2-a3 g7-f6",
        "a3-b4 d6-e5 e3-d4 h6-g5 b4-a5 g5-h4 d2-e3 g7-h6 c3-b4 e5xc3 b4xd2 b6-c5 b2-c3 c5-b4 c3-d4 b4-a3 a1-b2 f6-g5 g3-f4 h8-g7",
        "a3-b4 d6-e5 e3-d4 h6-g5 b4-a5 g7-h6 d2-e3 e7-d6 c3-b4 e5xc3 b4xd2 g5-h4 b2-c3 h8-g7 a1-b2 f8-e7 g3-f4 f6-g5 b2-a3 g7-f6",
        "a3-b4 d6xf4 g3xe5 f6xd4 c3xe5 h6-g5 e3-f4 g5xe3 d2xf4 b6-a5 a5xc3 b2xd4 c7-b6 e1-d2 e7-f6 g3-h4 b6-c5 d4xb6 a7xc5 a1-b2",
        "a3-b4 e5-f4 b4-a5 e7-d6 b2-a3 h6-g5 c3-b4 d6-e5 a1-b2 g7-f6 d2-e3 f6-e5 h2-g3 e7-d6 b2-c3 e5-f4 h8-g7 c3-d4 b6-c5 a3-b4",
        "a3-b4 e5-f4 b4-c5 g7-f6 b2-a3 f6-g5 e7-d6 b2-c3 f8-g7 c3-b4 d6-e5 d2-c3 g7-f6 c3-d4 d8-e7 d2-c3 e7-d6 c3-b4 a7-b6 c1-d2",
        "a3-b4 e5-f4 e3xg5 f6xh4 d2-e3 h6-g5 h2-g3 e7-d6 b4-a5 g5-f4 e3xg5 h4xf6 f2-e3 f6-e5 d4xf6 g7xe5 e3-d4 f8-g7 d4xf6 g7xe5",
        "a3-b4 e7-d6 b2-a3 b6-c5 d2-e3 c7-b6 g3-h4 f8-e7 f6-g5 g3-h4 g5-f4 f2-e3 g7-f6 e1-f2 h8-g7 f2-g3 g7-h6 g1-h2 b8-a7 g3-f4",
        "a3-b4 e7-d6 b2-a3 f6-e5 d2-e3 b6-c5 c3-d4 h8-g7 g3-h4 g7-f6 a1-b2 d8-e7 b2-c3 c7-b6 c3-d4 d6-e5 f2-g3 e3-f4 b8-c7 g1-f2",
        "a3-b4 f6-e5 b4-a5 b6-c5 b2-a3 e5-f4 a1-b2 f6-e5 c5-b4 g3-f4 b4-a3 d2-e3 g7-f6 f2-g3 e7-d6 g3-h4 h8-g7 e3-d4 d8-e7 e1-f2",
        "a3-b4 f6-e5 b4-a5 e5-f4 b2-a3 b6-c5 f6-e5 f2-e3 e5-d4 e1-f2 g7-f6 c1-b2 h8-g7 b2-c3 f6-e5 a1-b2 c5-d4 e5-f4 c7-b6 b2-c3",
        "a3-b4 f6-e5 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 a7-b6 b2-c3 e7-d6 b6-c5 a1-b2 g7-f6 b2-a3 f8-g7 c3-b4 e5-f4 f2-g3 b8-a7 g3xe5",
        "a3-b4 f6-e5 g3-h4 g5-f4 e3xg5 h6xf4 b2-a3 b6-c5 b4xd6 e7xc5 a1-b2 f8-e7 d2-e3 f4xd2 c1xe3 g7-f6 f2-g3 h8-g7 e3-f4 e7-d6",
        "a3-b4 f6-e5 g3-h4 g7-f6 f2-g3 b6-a5 e3-d4 d6-c5 b4xf4 f6-g5 h4xf6 e7xc5 b2-a3 c7-d6 g3-f4 h8-g7 h2-g3 g7-f6 g3-h4 f6-e5",
        "a3-b4 f6-e5 g3-h4 g7-f6 f2-g3 b6-a5 e3-d4 d6-c5 b4xf4 f6-g5 h4xf6 e7xc5 b2-a3 c7-d6 g3-h4 h8-g7 h2-g3 g7-f6 g1-h2 f8-e7",
        "a3-b4 f6-g5 b4-a5 e7-d6 b2-a3 g5-f4 c3-b4 f6-e5 e5-f4 f2-g3 f8-e7 e7-d6 g1-f2 f2-g3 d8-e7 e7-d6 e1-f2 a1-b2 g7-f6 c1-d2",
        "a3-b4 f6-g5 b4-a5 e7-d6 g3-f4 g7-f6 b2-a3 f6-e5 h2-g3 h8-g7 b6-c5 d2-c3 g7-f6 c3-d4 f8-e7 d2-c3 c5-b4 e7-d6 c3-b4 a7-b6",
        "a3-b4 f6-g5 b4-a5 e7-d6 g3-f4 g7-f6 c3-d4 f6-e5 h8-g7 e3-d4 b6-c5 d2-e3 c5-b4 c3-d4 b4-a3 a1-b2 g7-f6 b2-c3 f6-e5 c3-d4",
        "a3-b4 f6-g5 b4-a5 g5-h4 c3-d4 g7-f6 b2-c3 f6-g5 a1-b2 g5-f4 g3xe5 d6xf4 e3xg5 h4xf6 d2-e3 e7-d6 h2-g3 f6-g5 g3-f4 h8-g7",
        "a3-b4 f6-g5 b4-a5 g5-h4 c3-d4 g7-f6 b2-c3 f6-g5 g3-f4 e7-f6 h4xf2 e1xg3 g5-h4 a1-b2 h4xf2 d4-e5 f6xd4 e3xe7 d8xf6 g1xe3",
        "a3-b4 f6-g5 b4-a5 g5-h4 c3-d4 g7-f6 d4-c5 b6xd4 e3xc5 d6xb4 a5xc3 e7-d6 c3-b4 f6-e5 b2-c3 a7-b6 b4-a5 h8-g7 d2-e3 e5-f4",
        "a3-b4 f6-g5 b4-a5 g5-h4 c3-d4 g7-f6 d4-c5 d6xb4 a5xc3 b6-a5 c7-d6 b2-a3 h8-g7 a1-b2 d6-c5 d4xb6 a5xc7 b2-c3 e7-d6 a3-b4",
        "a3-b4 f6-g5 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 g5-h4 b2-c3 g7-f6 g3-f4 f6-g5 a1-b2 g5xe3 d2xf4 h8-g7 c3-d4 g7-f6 f4-g5 h6xf4",
        "a3-b4 f6-g5 c3-d4 b6-c5 g3-f4 g7-f6 b2-a3 h8-g7 e7-d6 d2-c3 g5-h4 c3-d4 f8-e7 c1-d2 f6-e5 b2-c3 c5-b4 e3-d4 b4-a3 f2-e3",
        "a3-b4 f6xd4 c3xe5 d6xf4 g3xe5 h6-g5 e3-f4 g5xe3 d2xf4 b6-a5 f2-g3 a5xc3 b2xd4 a7-b6 g3-h4 b6-c5 d4xb6 c7xa5 a1-b2 e7-f6",
        "a3-b4 g5-h4 b4-c5 f6-e5 b2-c3 h8-g7 g7-f6 c3-d4 b6-c5 f6-e5 a1-b2 f8-e7 b2-c3 e7-f6 c3-d4 c7-b6 d2-e3 h6-g5 c1-d2 d8-e7",
        "a3-b4 g5-h4 b4-c5 f6-e5 d2-e3 b6-c5 h8-g7 b2-c3 c7-b6 a1-b2 b8-a7 e1-d2 b6-a5 g1-h2 a7-b6 b2-a3 e7-d6 c3-d4 g7-f6 d2-c3",
        "a3-b4 h6-g5 b2-a3 b6-a5 b4-c5 d6xb4 a3xc5 e5-f4 g3xe5 c7-d6 e5xc7 b8xb4 h2-g3 b4-a3 d2-e3 e7-d6 g3-h4 g7-h6 f2-g3 f6-e5",
        "a3-b4 h6-g5 b2-a3 b6-a5 b4-c5 d6xb4 a3xc5 e5-f4 g3xe5 e7-d6 c5xe7 f8xf4 d4-c5 b8-a7 f2-e3 d8-e7 c5-b6 a7xc5 e3-d4 c5xe3",
        "a3-b4 h6-g5 b2-a3 g5-h4 e3-d4 g7-f6 d2-e3 b6-c5 f6-e5 c3-d4 h8-g7 d2-c3 c5-b4 c7-d6 a1-b2 g7-f6 c3-d4 d6-c5 b2-c3 c7-d6",
        "a3-b4 h6-g5 b4-a5 g5-h4 c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 h8-g7 a1-b2 e7-f6 b2-a3 b6-c5 c3-d4 e5xc3 d2xb4 g7-h6 g3-f4 f6-e5",
        "a3-b4 h6-g5 b4-a5 g5-h4 c3-d4 f6-e5 d4xf6 g7xe5 b2-c3 h8-g7 a1-b2 e7-f6 e3-f4 g7-h6 b2-a3 b6-c5 f4-g5 h6xf4 c3-d4 e5xc3",
        "a3-b4 h6-g5 b4-a5 g5-h4 e3-d4 d6-e5 d2-e3 g7-h6 c3-b4 e5xc3 b4xd2 b6-c5 b2-a3 h8-g7 g3-f4 c7-d6 f4-g5 h6xf4 e3xg5 f6-e5",
        "a3-b4 h6-g5 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 f6-e5 g3-h4 g5-f4 b2-c3 a7-b6 a1-b2 b6-c5 b2-a3 c7-d6 c3-b4 b8-c7 f2-g3 c7-b6",
        "a3-b4 h6-g5 b4-c5 b6xd4 e3xc5 d6xb4 c3xa5 g5-h4 b2-c3 f6-g5 g3-f4 g5xe3 d2xf4 g7-f6 c3-d4 f6-e5 d4xf6 e7xe3 f2xd4 c7-b6",
        "a3-b4 h6-g5 b4-c5 d6xb4 c3xa5 g5-h4 b2-c3 g7-h6 c3-d4 f6-g5 a1-b2 e7-d6 d4-c5 d6xb4 a5xc3 b6-a5 c3-d4 h8-g7 d4-c5 c7-d6",
        "a3-b4 h6-g5 b4-c5 d6xb4 c3xa5 g5-h4 b2-c3 g7-h6 g3-f4 f6-g5 b6-c5 d4xb6 a7xc5 a1-b2 h8-g7 d2-c3 c5-b4 b2-a3 b4xd2 e1xc3",
        "a3-b4 h6-g5 b4-c5 g5-f4 e7-d6 h2-g3 g7-f6 d2-e3 d6-e5 b2-c3 c7-d6 e3-f4 b6-a5 d4-c5 b8-a7 a7-b6 c1-d2 h8-g7 d2-e3 g7-h6",
        "a3-b4 h6-g5 g3-f4 b6-c5 f4xh6 c5xa3 c3-d4 a7-b6 h2-g3 b6-a5 g3-h4 b8-a7 b2-c3 c7-b6 f2-g3 d6-c5 g3-f4 f6-g5 h4xf6 g7xg3",
        "a3-b4 h6-g5 g3-f4 b6-c5 f4xh6 c5xa3 c3-d4 a7-b6 h2-g3 b6-a5 g3-h4 f6-e5 d4xf6 g7xe5 b2-c3 h8-g7 g1-h2 g7-f6 f2-g3 c7-b6",
        "a3-b4 h6-g5 g3-f4 b6-c5 f4xh6 c5xa3 h2-g3 a7-b6 g3-h4 b6-a5 f2-g3 c7-b6 c3-d4 b8-a7 b2-c3 b6-c5 d4xb6 a5xc7 a1-b2 a7-b6",
        "a3-b4 h6-g5 h2-g3 g5-h4 b4-c5 f6-g5 g3-f4 g7-h6 b2-a3 c7-d6 e7-d6 f2-g3 g5-h4 b2-a3 f4-e5 d8-e7 d2-e3 b6-c5 c1-d2 h8-g7",
        "a3-b4 h6-g5 h2-g3 g5-h4 b4-c5 g7-h6 g1-h2 b6-a5 c5-b6 a7xc5 d4xb6 f6-g5 b6-a7 c7-b6 a7xc5 e5-d4 c3xe5 g5-f4 e3xg5 h4xb6",
        "a3-b4 h6-g5 h2-g3 g5-h4 b4-c5 g7-h6 g3-f4 f6-g5 b2-a3 c7-d6 h8-g7 b2-a3 g7-f6 f4-e5 b8-c7 g5-f4 f2-g3 h8-g7 g3-f4 c7-d6",
        "a3-b4 h8-g7 b4-a5 e7-d6 c3-d4 h6-g5 a7-b6 d2-e3 g7-h6 d4-c5 a1-b2 d6-e5 b2-c3 d8-e7 c1-d2 c7-b6 d2-e3 b6-a5 g3-f4 e7-d6",
        "a3-b4 h8-g7 b4-a5 e7-d6 d2-e3 f6-e5 a7-b6 c3-d4 b6-a5 c1-d2 c7-b6 b2-a3 d6-c5 a1-b2 g7-f6 b2-c3 b8-a7 g1-h2 d8-c7 f2-g3",
        // --- b2-c3 (24 linhas de campeonato) ---
        "b2-c3 b8-a7 b8-c7 c3-b4 c3-b4 a5xe5 f4xb4 b6-a5 b4-c5 a5-b4 c5-d6 b4-c3 d6-c7",
        "b2-c3 d6-c5 g3-f4 f6-g5 f4-e5 g7-f6 b6-a5 c1-b2 f8-e7 g5-f4 f2-g3 e7-d6 d4-c5 b8-c7 a1-b2 h6-g5 b2-a3 c7-d6",
        "b2-c3 b6-a5 e3-d4 a7-b6 d4xf6 e7xe3 d2xf4 g7-f6 f2-e3 b6-c5 g3-h4 f8-e7 e1-d2 f6-g5 h4xf6 e7xg5 a1-b2 g5-h4 g1-f2 d8-e7",
        "b2-c3 b6-a5 g3-f4 f6-g5 h8-g7 c3-b4 g7-f6 a1-b2 a7-b6 b4-a5 b6-c5 h2-g3 f6-e5 e1-f2 e5-f4 c7-d6 e3-d4 h6-g5 g1-f2 g5-f4",
        "b2-c3 b6-a5 g3-h4 e5xg3 h2xf4 g7-f6 f4-g5 h6xf4 e3xg5 f6-e5 f2-e3 a7-b6 c1-b2 b6-c5 c3-b4 a5xc3 b2xf6 f8-g7 g5-h6 g7xe5",
        "b2-c3 b6-c5 c3-d4 e7-d6 a1-b2 f8-e7 g3-f4 f6-g5 c5-b4 c3-d4 b4-a3 d2-c3 e7-d6 e1-d2 g7-f6 d4-c5 c3-d4 b4-c3 c7-d6 d2-c3",
        "b2-c3 c5-b4 a1-b2 b4-a3 c3-d4 f6-g5 b2-c3 g5-h4 a7-b6 f2-g3 g7-f6 g3-h4 f6-g5 h2-g3 h8-g7 d4-e5 g5-h4 e5-f6 b2-a1 f4-e5",
        "b2-c3 c5-b4 a1-b2 b4-a3 c3-d4 f6-g5 g3-f4 g7-f6 a7-b6 f2-g3 g5-h4 f4-e5 f6-g5 g3-f4 e7-d6 h2-g3 g5-h4 g1-h2 f8-e7 h2-g3",
        "b2-c3 c5-b4 a3xc5 d6xb4 c3-d4 b4-a3 a1-b2 f6-e5 d4xf6 g7xe5 b2-c3 h8-g7 g3-h4 e5-f4 e3xg5 h6xf4 c3-d4 g7-f6 d2-e3 f4xd2",
        "b2-c3 c5-b4 c3-d4 b4-a3 a1-b2 f6-g5 b2-c3 a7-b6 g7-f6 f2-g3 g5-h4 f4-e5 f6-g5 g3-f4 e7-f6 h2-g3 g5-h4 f4-e5 b6-c5 d2-c3",
        "b2-c3 d6-c5 g3-f4 c7-d6 a1-b2 f6-e5 c3-b4 e5xg3 h2xf4 c5-d4 e3xc5 b6xd4 d2-e3 d6-c5 b4xd6 e7xc5 e1-d2 g7-f6 g1-h2 f6-g5",
        "b2-c3 d6-c5 g3-h4 c7-d6 f2-g3 f8-e7 g3-f4 d6-e5 b8-c7 g3-f4 c7-d6 g1-h2 f6-e5 h8-g7 c3-d4 b6-a5 d2-c3 g7-f6 c3-b4 c1-b2",
        "b2-c3 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 c3-d4 g7-f6 f2-g3 h8-g7 g3xe5 b6-c5 d4xb6 a7xc5 e1-f2 f6xd4 d2-e3 d4-c3 e3-f4 b8-a7",
        "b2-c3 e5-f4 g7-f6 c3-b4 h8-g7 h2-g3 g7-h6 b6-a5 g3-h4 c7-d6 f2-g3 a7-b6 g3-f4 b6-c5 c3-b4 f6-e5 c1-d2 f8-g7 d2-c3 g7-f6",
        "b2-c3 e5-f4 g7-f6 h2-g3 h8-g7 c3-b4 f6-g5 g7-h6 e3-d4 b6-c5 d2-e3 g5-h4 c1-b2 f8-e7 b2-c3 e7-f6 c3-d4 b8-a7 e3-d4 d6-e5",
        "b2-c3 e7-f6 g1-f2 f6-e5 d4xf6 b6xb2 a3xc1 a5xc3 f6-e7 a7-b6 e7-f8 b6-a5 f8-h6 c7-d6 h6-f4 d6-c5 f4-e5 c5-d4 e5-f6 a5-b4",
        "b2-c3 f6-e5 a1-b2 b6-c5 e3-f4 e7-f6 d2-e3 f6-g5 e3-d4 f8-g7 c1-d2 g3-f4 c7-b6 f4-e5 b6-a5 a3-b4 h8-g7 b4-c5 f4-g3 c3-d4",
        "b2-c3 f6-e5 a1-b2 e7-f6 b4-c5 f6-g5 e3-f4 f2-e3 d8-c7 e3-f4 g7-f6 b2-c3 f6-g5 e1-f2 f8-g7 c1-d2 g3-f4 h8-g7 d2-e3 c7-b6",
        "b2-c3 f6-e5 c3-b4 e5-f4 g3xe5 d6xf4 e3xg5 h6xf4 b4xd6 c7xe5 e7-d6 b2-c3 b8-c7 c3-b4 a7-b6 d2-e3 f4xd2 c1xe3 b6-c5 e3-f4",
        "b2-c3 f6-e5 c3-b4 e7-f6 b4-a5 b6-c5 a1-b2 c7-b6 a5xc7 d8xb6 b6-a5 c3-b4 a5xc3 d2xb4 e5-d4 b4-a5 d6-e5 e3-f4 b8-c7 f4xb8",
        "b2-c3 f6-e5 c3-d4 e5xc3 d2xb4 g7-f6 a1-b2 f6-e5 g3-f4 e5xg3 h2xf4 h8-g7 c1-d2 e7-f6 b2-c3 f6-e5 g1-h2 e5xg3 f2xh4 g7-f6",
        "b2-c3 f6-e5 e3-d4 c5xe3 f2xf6 g7xe5 g3-f4 e5xg3 h2xf4 d6-c5 h8-g7 f2-e3 g7-f6 c3-d4 e7-d6 d4xb6 a7xc5 a1-b2 f8-g7 d2-c3",
        "b2-c3 f6-g5 g3-f4 c5-b4 a3xc5 d6xb4 a1-b2 b4-a3 c3-d4 g7-f6 h2-g3 g5-h4 d2-c3 f6-g5 d4-e5 e7-d6 c3-d4 a7-b6 e1-d2 f8-g7",
        "b2-c3 g5-f4 a1-b2 b6-c5 f6-g5 e1-f2 g7-h6 d4-c5 e7-d6 b2-c3 c7-b6 d2-e3 h2-g3 f6-e5 g3-h4 g5-f4 g1-h2 e5-d4 f2-g3 d4-e3",
        // --- b2-a3 (7 linhas de campeonato) ---
        "b2-a3 f6-g5 g3-f4 g7-f6 a1-b2 b6-c5 f2-g3 g5-h4 b6-a7 d4-e3 f4-e5 b2-c3 f4-g3",
        "b2-a3 d6-c5 g3-f4 f6-g5 h2-g3 e7-d6 g3-h4 g7-f6 f2-g3 f6-e5 g3-h4 f8-e7 d4-e5 c5-b4 a7-b6 f4-g5 b6-c5 g5-h6 g7-f6 g1-f2",
        "b2-a3 f6-e5 e3-f4 b6-c5 c3-b4 g7-f6 d2-c3 f6-g5 c3-d4 e5xc3 b4xd2 g5xe3 f2xb6 a7xc5 a1-b2 h8-g7 b2-c3 g7-f6 c3-b4 f6-e5",
        "b2-a3 f6-g5 a3xc5 b6xb2 a1xc3 g5-h4 c3-b4 g7-f6 c1-b2 c7-d6 f6-e5 g3-f4 e5xg3 h2xf4 e7-f6 f4-g5 h6xf4 e3xc5 h8-g7 c5-d6",
        "b2-a3 f6-g5 g7-f6 g3-f4 g5-h4 f4-g5 f6-e5 g5-h6 h8-g7 f2-e3 g7-f6 e3-d4 e7-d6 d2-e3 d6-c5 g1-f2 d8-e7 h2-g3 e5-d4 e7-f6",
        "b2-a3 h6-g5 a3xc5 b6xb2 a1xc3 g5-h4 c3-d4 g7-f6 d4-c5 d6xb4 a5xc3 h8-g7 e3-d4 f6-g5 c3-b4 a7-b6 b4-a5 e7-d6 d2-e3 g7-f6",
        "b2-a3 h6-g5 a3xc5 b6xb2 a1xc3 g5-h4 c3-d4 g7-h6 d4-c5 d6xb4 a5xc3 a7-b6 e3-d4 e7-d6 d4-e5 d6xf4 g3xe5 h6-g5 d2-e3 b6-a5",
        // --- d2-c3 (10 linhas de campeonato) ---
        "d2-c3 a3-b2 c3-b4 c5xa3 a1xc3 h2-g3 h4xf2 g1xe3",
        "d2-c3 b4xd2 c1xe3 f8-e7 e3-d4 e7-d6 b6-a7 g3-h2",
        "d2-c3 b4xd2 c1xe3 f8-e7 e3-d4 e7-d6 b6-a7 g3-h4",
        "d2-c3 d4xb2 c1xa3 b8-a7 a3-b4 c7-b6 b4-a5 b6-c5",
        "d2-c3 h8-g7 g3-h4 g7-f6 e3-f4 e5xg3 h4xf2 f6-e5 f2-e3",
        "d2-c3 h6-g5 e1-d2 c5-d4 c3-b4 d4-c3 f2-e3 c3xa5 g1-f2 a5-b4 d2-c3 f4xd2 f2-g3",
        "d2-c3 d6-c5 e3-d4 c5xe3 f2xd4 h4xf2 e1xg3 b6-a5 g3-f4 f6-e5 d4xf6 g7xg3 h2xf4 f8-g7 h6xd6 c7xg3 c3-d4 a7-b6 d4-e5 d8-e7",
        "d2-c3 f6-e5 a3-b4 e7-d6 c3-d4 e5xc3 b4xd2 g7-f6 b2-c3 b6-c5 f8-g7 d4xb6 a7xc5 g3-f4 f6-g5 d2-c3 c5-b4 c3-d4 b4-a3 h2-g3",
        "d2-c3 g5-f4 c5-d4 e3xe7 g5xg1 c7-b6 a5xc7 b8xd6 f8xc5 g1xb6 g3-h4 g7-f6 d2-c3 a7-b6 f2-g3 b8-a7 e3xg5 h6xf4 f2-e3 g7-h6",
        "d2-c3 g5-h4 c3-d4 f6-e5 a3-b4 h8-g7 b2-c3 g7-f6 e7-d6 a1-b2 f6-e5 b2-c3 e5-f4 g3-h4 b6-c5 f2-g3 d6-e5 g3-f4 c7-b6 d2-e3",
        // --- d2-e3 (16 linhas de campeonato) ---
        "d2-e3 f4xd2 c3xe1 a5xc3 e1-d2 c3xg3 h2xb8",
        "d2-e3 d2-c3 b8-c7 e3-f4 c7-d6 f4-g5 d6-e5 g5-h4",
        "d2-e3 g1xa1 g1xb2 a3-b4 a5xc3 c1xa3 a3-b4 a5xc3 c1-b2 c3-d2 e1xc3",
        "d2-e3 b6-a5 e1-d2 f6-e5 e3-d4 c5xe3 f2xf6 g7xe5 b4-c5 d6xb4 a3xc5 h8-g7 c3-b4 a5xe1 g3-f4 e5xg3 h2xf4",
        "d2-e3 b6-c5 c3-b4 e7-d6 b2-c3 a7-b6 c3-d4 f6-g5 c1-d2 g7-f6 f6-e5 d4xf6 g5xe7 e3-f4 h8-g7 d2-c3 e7-f6 f4-e5 f6xd4 c3xe5",
        "d2-e3 c7-b6 c3-d4 b6-a5 b4-c5 f6-g5 g5-h4 g3-f4 g7-f6 a1-b2 f6-g5 b2-a3 h8-g7 c3-d4 c7-b6 c1-d2 b6-a5 f4-e5 a5-b4 e5-d6",
        "d2-e3 d6-c5 g3-f4 c7-d6 h2-g3 b6-a5 f6-g5 e3-f4 h6-g5 e5-d4 b4-c5 h8-g7 b2-c3 g7-f6 c1-b2 c7-d6 c3-b4 d6-e5 b2-c3 e5-f4",
        "d2-e3 e7-d6 e3-f4 f8-e7 a3-b4 b6-c5 b2-a3 c7-b6 a5xc7 d8xb6 b8-c7 c3-b4 e5-d4 f4-e5 d6xf4 b4xf8 f4-e3 a3-b4 f6-g5 b4-c5",
        "d2-e3 f6-e5 c3-b4 e5-f4 b4-a5 f6-e5 b2-c3 b6-c5 g7-f6 g3-h4 h8-g7 f2-g3 e5-f4 h2-g3 g7-f6 e1-f2 f6-e5 c1-d2 e7-f6 d2-e3",
        "d2-e3 f6-e5 c3-b4 e5-f4 g3-h4 b6-c5 f2-e3 f6-e5 g7-f6 b2-c3 c7-b6 g1-h2 c5-d4 a7-b6 e1-d2 b6-c5 d2-e3 b8-a7 c1-d2 a7-b6",
        "d2-e3 f6-g5 c1-d2 b6-a5 b4-c5 g5-h4 c3-b4 g7-f6 b2-a3 f6-g5 a1-b2 g5-f4 e7-d6 a7-b6 b4-a5 b6-c5 c3-b4 c7-d6 b2-c3 h8-g7",
        "d2-e3 f6-g5 c3-d4 a7-b6 g3-f4 g7-f6 b4-a5 g5-h4 b2-c3 f6-g5 e7-f6 c1-b2 f8-e7 c3-d4 b8-a7 b2-c3 c5-b4 e7-d6 a1-b2 f6-e5",
        "d2-e3 f6-g5 c3-d4 g5-f4 g3xe5 d6xd2 c1xe3 e7-d6 b2-c3 h6-g5 h2-g3 g7-f6 g3-f4 g5-h4 a1-b2 d6-c5 g1-h2 h8-g7 e1-d2 d8-e7",
        "d2-e3 f6-g5 c3-d4 g5-h4 a1-b2 g7-f6 b2-c3 e7-d6 f6-g5 f2-e3 g5-h4 c1-d2 f4-e5 b6-c5 d2-e3 h8-g7 g5-h6 g7-f6 h2-g3 f6-e5",
        "d2-e3 f6-g5 g3-f4 d6-e5 f4xd6 e7xc5 c3-b4 g5-f4 b4xd6 c7xe5 a5xc7 b8xd6 e3xg5 h4xf6 h2-g3 h6-g5 g3-h4 g5-f4 b2-c3 d6-c5",
        "d2-e3 g5-h4 a5-b6 h4xd4 b6-c7 d4-e3 c7-d8 e3-d2 d8-g5 d2-c1 g5-h4 c1-b2 h4-f2 e5-d4 f2-g1 b2-c3 g1-f2 c3-d2 f2-g3 c5-b4",
        // --- f2-e3 (10 linhas de campeonato) ---
        "f2-e3 d4xf2 e5-f6 d8xg5 f2-e3 h4xf2",
        "f2-e3 c3-d2 e3-f4 g5xe3 g3-f4 e3xg5 c1xe3",
        "f2-e3 d4xf2 d2-e3 f2xd4 f4-g5 h4xf2 g5xg1",
        "f2-e3 h6xc5 d4xh8 d4-c5 d4-e5 d6xb4 d6xf4",
        "f2-e3 b6-a5 g3-f4 a7-b6 h2-g3 d6-c5 c3-b4 b8-a7 e3-d4 c7-d6 c3-b4 f6-e5 f2-e3 h8-g7 b4-a5 g7-f6 a1-b2 f8-e7 g3-f4 d6-e5",
        "f2-e3 b6-a5 g3-f4 d6-e5 g1-f2 e7-d6 f2-g3 a7-b6 b8-c7 c1-d2 b6-c5 d2-e3 c7-b6 e1-d2 d8-c7 f4-g5 e5-d4 d2-c3 h8-g7 c3-d4",
        "f2-e3 b6-c5 c3-b4 a1-b2 a7-b6 b2-c3 b6-c5 c5-b4 e1-f2 b8-c7 f2-g3 c7-d6 g3-f4 f6-g5 h8-g7 g1-f2 g7-f6 c3-d4 f6-e5 f2-g3",
        "f2-e3 d6-c5 g3-h4 e7-d6 h2-g3 f8-e7 g3-f4 e5xg3 h4xf2 d6-e5 b8-a7 g1-h2 e7-d6 g3-h4 d8-e7 a3-b4 c5xa3 h4-g5 h6xf4 e3xg5",
        "f2-e3 f6-e5 g3-f4 e5xg3 h2xf4 g7-f6 c3-d4 h8-g7 g1-h2 d6-c5 c7-d6 g3-h4 b8-c7 f4-e5 d6xf4 e3xg5 c5xe3 d2xf4 c7-d6 c1-d2",
        "f2-e3 f6-g5 g3-h4 b6-c5 h8-g7 c3-b4 g7-f6 f6-e5 f4-g5 e7-f6 d2-e3 f8-e7 e1-f2 c7-b6 c5-d4 f2-e3 e7-d6 e3-d4 a7-b6 g1-f2",
        // --- f2-g3 (3 linhas de campeonato) ---
        "f2-g3 g5-h4 b8-c7 g3-h4 c3-d4 h4xf2 d4xc5 f2xd4 b4-c5 d6xb4 a3xe3",
        "f2-g3 b6-a5 g3-f4 e5xg3 h2xf4 c7-b6 g1-h2 d8-c7 c3-d4 d6-e5 f4xd6 c7xc3 b2xd4 b8-c7 h2-g3 c7-d6 g3-f4 b6-c5 d4xb6 a7xc5",
        "f2-g3 h4xf2 g1xg5 h6xf4 e1-f2 c5-d4 f2-g3 d4-e3 d2-c3 e3-d2 c3xe1 f4-e3 g3-f4 e3xg5 h2-g3 g5-h4 e1-f2 e5-d4 g3-f4 d4-c3",
        // --- h2-g3 (13 linhas de campeonato) ---
        "h2-g3 h8-g7 h4-g5 f6xf2 g1xc5 b8-c7 d2-e3 g7-f6 e3-f4",
        "h2-g3 h4xd4 d2-c3 d4xb2 h6-c1 g1-h2 h8-d4 c7-d8 d4xg1 d8-a5 h4xf2 a5-e1",
        "h2-g3 f6-e5 g3-f4 e5xg3 h4xf2 h8-g7 f2-e3 d4xf2 g1xe3 b8-c7 d2-c3 c7-d6 c3-d4 g7-f6",
        "h2-g3 b6-c5 c3-d4 c7-b6 b2-c3 c5-b4 a1-b2 b4-a3 g3-h4 f6-g5 b2-c3 a7-b6 f4-e5 a5-b4 g1-h2 g5-h4 f2-e3 f8-e7 e3-d4 e7-d6",
        "h2-g3 d6-e5 g3-h4 e5-d4 e3xc5 b6xd4 c3xe5 f6xd4 d2-e3 c7-b6 e3xc5 b6xd4 b2-c3 d4xb2 a1xc3 a7-b6 c1-d2 e7-d6 f2-e3 g7-f6",
        "h2-g3 e5-f4 c3-d4 f6-e5 h8-g7 d2-c3 g7-f6 c3-d4 e7-d6 b2-a3 b6-c5 a1-b2 d6-e5 b2-c3 d8-e7 f2-e3 c7-d6 e1-f2 e7-f6 d2-e3",
        "h2-g3 e7-d6 d4-c5 b6xd4 e3xg5 h6xh2 c3-b4 a5xc3 b2xd4 g7-f6 a7-b6 d2-e3 b6-a5 c1-d2 f6-g5 d4-c5 h8-g7 b2-c3 g7-f6 c3-b4",
        "h2-g3 e7-d6 d4-c5 b6xd4 e3xg5 h6xh2 c3-b4 a5xc3 b2xd4 g7-f6 h8-g7 b4-a5 f6-g5 a1-b2 g7-f6 d2-e3 f8-e7 c1-d2 c7-d6 d4-c5",
        "h2-g3 e7-d6 g3-f4 f6-e5 d4xf6 g7xg3 f2xh4 h6-g5 h4xf6 f8-e7 f6-g7 h8xf6 e3-f4 f6-e5 g1-f2 e5xg3 f2xh4 b6-c5 c3-d4 c5xe3",
        "h2-g3 e7-d6 g3-f4 f6-e5 d4xf6 g7xg3 f2xh4 h8-g7 e3-f4 d8-e7 c3-d4 e7-f6 b2-c3 d6-e5 f4xd6 c7xe5 a3-b4 f8-e7 b4-c5 a5-b4",
        "h2-g3 f6-g5 g3-h4 c7-d6 h4xf6 g7xe5 d4xf6 e7xg5 c3-b4 a5xc3 b2xd4 d6-c5 a1-b2 g5-h4 g1-h2 b6-a5 d4xb6 a5xc7 e3-d4 h6-g5",
        "h2-g3 f6-g5 g3-h4 f8-g7 h8-g7 e3-f4 g7-f6 f6-e5 g1-h2 d6-c5 c3-d4 c7-d6 c1-d2 b8-c7 e1-f2 e7-f6 b2-c3 d8-e7 a1-b2 h6-g5",
        "h2-g3 h6-g5 g3-h4 g7-h6 a3-b4 g5-f4 b4-c5 h8-g7 h4-g5 f8-g7 e1-f2 d8-e7 b2-c3 e7-d6 c3-d4 d4-c5 a7-b6 f4-g3 f2-e3 g3-f2",
    ];

    function algToIdx(sq) {
        if (!sq || sq.length < 2) return -1;
        const col = sq.charCodeAt(0) - 97;
        const row = parseInt(sq[1]) - 1;
        if (col < 0 || col > 7 || row < 0 || row > 7) return -1;
        return row * 8 + col;
    }

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

    // ── Árvore do livro ───────────────────────────────────────────────────────
    // Mapa: chave = hash da posição (int), valor = array de índices de jogadas
    const bookMap = new Map();

    function bookAddLine(state, moveIdxs) {
        const s = state.clone();
        for (const mi of moveIdxs) {
            const lm = s.getMoves();
            const found = lm.find(m => m.from === mi.from && m.to === mi.to);
            if (!found) return; // linha inválida — para aqui
            const h = s.hash;
            if (!bookMap.has(h)) bookMap.set(h, []);
            const arr = bookMap.get(h);
            if (!arr.includes(found.from * 64 + found.to))
                arr.push(found.from * 64 + found.to);
            s.applyMove(found);
        }
    }

    // ── [BOOK-V31-FULL] Campeonatos Brasileiros — 4780 linhas (auto-geradas) ──────
    // Parseadas de 233.848 linhas do Livro Completo, validadas pelo motor.
    // Processadas assíncronamente (junto com PDN_EXTRA_LINES) para não bloquear a UI.
    const BOOK_DATA_EXT =
        "IMUQEIVS|IMUQEIWS|IMUQEIWT|IMUQEIYU|IMUQEIZU|IMUQKNVR|IMUQKNWS|IMUQKNWT|IMUQKNXT|IMUQKNYU|IMUQLPWT|IMUREIWS|IMUREIWT|IMURMQRM|IMVRMVaR|IMVSEIWT|IMVSKNXT|IMVSMQWT|IMWSLPbW|IMWTMQTP|IMWTMRUN|IMXTLOUR|IMXTMQTP|IMXTMRUN|IMXTMRVM|JMUQEJWT|JMUQEJZU|JMUQFJWS|JMUQFJYU|JMUQLOQJ|JMUQMRVM|JMUREJWS|JMUREJWT|JMURFJWS|JMURKNRK|JMURKOWT|JMURLOWT|JMURMQVS|JMVSEJWT|JMVSFJaV|JMVSFJWT|JMVSKOaV|JMVSKOUQ|JMVSLPSO|JMVSMQaV|JMVSMQUR|JMVSMQWT|JMWSEJaW|JMWSEJbW|JMWSEJSO|JMWSEJUR|JMWSFJbW|JMWSKOaW|JMWSKObW|JMWSKOUQ|JMWSKOUR|JMWSLOSL|JMWSLPSO|JMWSMRUN|JMWTEJbW|JMWTEJTO|JMWTEJTP|JMWTEJUQ|JMWTFJUQ|JMWTKNaW|JMWTKNTO|JMWTKNTP|JMWTKNVR|JMWTLObW|JMWTLOUR|JMWTLPTO|JMWTLPUQ|JMWTMQTO|JMWTMQTP|JMWTMRUN|JMWTMRVM|JMXTLObX|JMXTLPbX|JMXTLPUQ|JMXTLPVS|JNUQEJWS|JNUQEJWT|JNUQEJYU|JNUQEJZU|JNUQKOWT|JNUQLOWS|JNUQLOWT|JNUQLOZU|JNUQLPVS|JNUQNRVM|JNUQNSWN|JNURNUYR|JNURNUZQ|JNVREJaV|JNVREJWT|JNVREJXT|JNVREJZV|JNVRFJaV|JNVRFJWS|JNVRFJWT|JNVRFJZV|JNVRLOWT|JNVRLOZV|JNVRLPWT|JNVRLPXT|JNVRLPZV|JNVSEJaV|JNVSEJUQ|JNVSEJUR|JNVSEJZV|JNVSFJaV|JNVSFJZV|JNVSLOSJ|JNVSLOSL|JNVSLPSJ|JNWSNWaT|JNWSNWbS|JNWTEJaW|JNWTEJbW|JNWTEJTO|JNWTEJTP|JNWTEJUQ|JNWTEJUR|JNWTEJVR|JNWTFJTP|JNWTFJUQ|JNWTFJVR|JNWTLObW|JNWTLOVR|JNWTLPUQ|JNWTNRUN|JNWTNRVM|JNWTNSVO|JNXTEJbX|JNXTEJTO|JNXTEJTP|JNXTLObX|JNXTLOTP|JNXTLPbX|JNXTLPUQ|JNXTLPVR|JNXTLPVS|KNVRFKWS|KNVRFKWT|KNVRGKZV|KNVSIMUQ|KNVSIMXT|KNWSNWbS|KNWTFKbW|KNWTFKTP|KNWTGKbW|KNWTGKTP|KNWTJMTP|KNWTJMVR|KNWTLPbW|KNWTLPUR|KNWTLPVR|KNXTLPVS|KOUQGKWS|KOUQGKWT|KOUQGKYU|KOUQJNVS|KOUQJNWS|KOURFKYU|KOURGKYU|KOURGKZU|KOWTFKTP|KOWTGKTP|KOWTJMTK|KOWTOSVO|LOUQHLYU|LOUQJMQJ|LOUQJNWS|LOURJMWS|LOVRJMaV|LOVRJNWT|LOWSGLbW|LOWSHLbW|LOWSHLSN|LOWSHLUQ|LOWSHLUR|LOWSHLXT|LOWTJMbW|LOWTJMUR|LOWTJNbW|LOWTJNVR|LPUQGLYU|LPUQHLWS|LPUQHLYU|LPUQJNWT|LPURJNWS|LPVRHLZV|LPVRJMUQ|LPVSHLXT|LPWSGLSO|LPWSIMUR|LPWSJMSO|LPWSJMUQ|LPWSJNSJ|LPWSKNaW|LPWTPWbS|LPXTKOTK|IMUQEIVSKOaV|IMUQEIVSKOYU|IMUQEIWSMRVM|IMUQEIWTLPbW|IMUQEIWTMRVM|IMUQEIYUAEVS|IMUQEIYUKNcY|IMUQEIYUKNVR|IMUQEIYUKNWS|IMUQEIYULOUR|IMUQEIZUAEUR|IMUQEIZUAEVR|IMUQEIZUAEVS|IMUQKNVRMVaK|IMUQKNWSNWaT|IMUQKNWSNWbS|IMUQKNWTLPYU|IMUQKNWTNSVO|IMUQKNXTLPbX|IMUQKNXTLPVS|IMUQKNXTNSVO|IMUQKNXTNSWN|IMUQKNYUNSWN|IMUQLPWTPWaT|IMUREIWSKObW|IMUREIWTJNbW|IMUREIWTLOTP|IMURMQRMJNMI|IMURMQRMLPWS|IMURMQRMLPWT|IMVRMVaRLPZV|IMVSEIWTKOTK|IMVSKNXTMQaV|IMVSKNXTMQbX|IMVSKNXTMQTP|IMVSMQWTKNTP|IMWSLPbWGLUQ|IMWTMQTPJNbW|IMWTMRUNKRVM|IMXTLOUROXRI|IMXTMQTPJNWS|IMXTMQTPKNVS|IMXTMRUNKRVM|IMXTMRVMJQTP|JMUQEJWTAETO|JMUQEJWTLPTO|JMUQEJZUKOUR|JMUQFJWSLPZU|JMUQFJYULPUR|JMUQLOQJFMWT|JMUQLOQJFMYU|JMUQMRVMIRWS|JMUQMRVMIRWT|JMUREJWSKObW|JMUREJWSKORN|JMUREJWTJNbW|JMUREJWTLObW|JMUREJWTLOTP|JMUREJWTLPTO|JMURFJWSKOaW|JMURFJWSKObW|JMURKNRKGNVS|JMURKNRKGNWT|JMURKOWTLPTK|JMURLOWTEJbW|JMURLOWTGLTP|JMURMQVSKOaV|JMVSEJWTLPTO|JMVSFJaVMQea|JMVSFJWTMQSN|JMVSFJWTMQTO|JMVSKOaVFKUR|JMVSKOaVMQea|JMVSKOUQOVQJ|JMVSLPSOKTXO|JMVSMQaVIMUR|JMVSMQaVIMWT|JMVSMQUREJRN|JMVSMQURFJRM|JMVSMQURKNRK|JMVSMQURKOaV|JMVSMQURKOSN|JMVSMQURLPSO|JMVSMQWTEJTO|JMVSMQWTKOTK|JMWSEJaWKNea|JMWSEJaWKNXT|JMWSEJaWMQea|JMWSEJbWAEfb|JMWSEJbWAEWT|JMWSEJbWKOUQ|JMWSEJSOKTXO|JMWSEJSOLSVO|JMWSEJURKOaW|JMWSEJURKOYU|JMWSFJbWMQWT|JMWSKOaWEJWT|JMWSKOaWFKUQ|JMWSKOaWFKWT|JMWSKOaWGKWT|JMWSKOaWMQea|JMWSKOaWMQUR|JMWSKOaWMQWT|JMWSKObWEJUQ|JMWSKObWEJUR|JMWSKObWFKUQ|JMWSKObWFKUR|JMWSKObWFKWT|JMWSKObWGKUQ|JMWSKObWMQWT|JMWSKOUQEJZU|JMWSKOUQGKQJ|JMWSKOUREJaW|JMWSLOSLHOUR|JMWSLOSLHOVR|JMWSLPSOKTXO|JMWSMRUNKRVM|JMWTEJbWAETP|JMWTEJbWJNfb|JMWTEJbWJNUR|JMWTEJbWLOfb|JMWTEJbWMQUR|JMWTEJbWMQWS|JMWTEJTOKTXO|JMWTEJTOLSVO|JMWTEJTPAEUR|JMWTEJTPLObW|JMWTEJTPMQbW|JMWTEJTPMQXT|JMWTEJUQMRVM|JMWTFJUQLPZU|JMWTKNaWNSWN|JMWTKNTOLSVO|JMWTKNTPMQXT|JMWTKNVRMVaK|JMWTLObWEJfb|JMWTLObWEJTP|JMWTLObWEJWS|JMWTLObWMQWS|JMWTLObWMRUN|JMWTLObWMRVM|JMWTLOUREJbW|JMWTLPTOKTXO|JMWTLPUQPWQJ|JMWTMQTPEJXT|JMWTMRUNKRVM|JMWTMRVMIRUN|JMXTLObXEJfb|JMXTLPbXMQTO|JMXTLPbXMQVS|JMXTLPUQGLQJ|JMXTLPUQHLQJ|"+
        "JMXTLPUQMRVM|JMXTLPVSHLbX|JMXTLPVSMQaV|JNUQEJWSNWbS|JNUQEJWTAETP|JNUQEJWTLPbW|JNUQEJWTNRVM|JNUQEJYUAEVR|JNUQEJZUAEWT|JNUQEJZULPUR|JNUQEJZULPVR|JNUQKOWTGKQM|JNUQKOWTNRTK|JNUQLOWSNWbL|JNUQLOWTEJbW|JNUQLOWTEJZU|JNUQLOZUEJWT|JNUQLPVSEJSO|JNUQNRVMIRWS|JNUQNRVMIRWT|JNUQNRVMIRZU|JNUQNRVMIRZV|JNUQNSWNKRVM|JNURNUYREJWS|JNURNUYREJWT|JNURNUZQEJWS|JNURNUZQKNVR|JNURNUZQLOWS|JNURNUZQLPWS|JNVREJaVBEWT|JNVREJaVJMUQ|JNVREJaVJMXT|JNVREJaVLOWT|JNVREJaVLPea|JNVREJaVLPVS|JNVREJaVLPXT|JNVREJWTBEbW|JNVREJWTBEZV|JNVREJWTJMaW|JNVREJWTJMUQ|JNVREJWTLObW|JNVREJXTBETO|JNVREJXTJMUQ|JNVREJXTLOTP|JNVREJXTLPaV|JNVREJXTLPbX|JNVREJXTLPZV|JNVREJZVJMUQ|JNVREJZVLOUQ|JNVREJZVLOWT|JNVREJZVLPUQ|JNVRFJaVJMUQ|JNVRFJaVJMWT|JNVRFJaVLPXT|JNVRFJWSNWbS|JNVRFJWTJMaV|JNVRFJWTJMTP|JNVRFJWTJMZV|JNVRFJWTLObW|JNVRFJWTLOTP|JNVRFJWTLOZV|JNVRFJZVJMUQ|JNVRFJZVJMWT|JNVRLOWTFJbW|JNVRLOZVEJWT|JNVRLPWTPWbJ|JNVRLPXTGLbX|JNVRLPZVGLRM|JNVRLPZVHLUQ|JNVRLPZVHLVS|JNVSEJaVAEVR|JNVSEJaVKOda|JNVSEJaVKOea|JNVSEJaVKOUQ|JNVSEJaVKOUR|JNVSEJaVLPUQ|JNVSEJaVLPVR|JNVSEJUQAEZV|JNVSEJUQIMZU|JNVSEJUQKOYU|JNVSEJURNUYR|JNVSEJZVKOUQ|JNVSEJZVKOUR|JNVSFJaVKOUQ|JNVSFJaVKOUR|JNVSFJaVLPXT|JNVSFJZVKOUQ|JNVSFJZVKOUR|JNVSLOSJENUQ|JNVSLOSJFMWT|JNVSLOSLHOUQ|JNVSLOSLHOUR|JNVSLPSJFMWS|JNVSLPSJFMWT|JNWSNWaTEJUQ|JNWSNWaTIMTP|JNWSNWaTIMUR|JNWSNWaTKNbW|JNWSNWaTLOda|JNWSNWaTLOea|JNWSNWbSEJfb|JNWSNWbSEJUQ|JNWSNWbSIMaW|JNWSNWbSIMeb|JNWSNWbSIMfb|JNWSNWbSLOSL|JNWTEJaWBETP|JNWTEJaWLOda|JNWTEJaWLPea|JNWTEJbWAEUQ|JNWTEJbWAEVR|JNWTEJbWJMeb|JNWTEJbWJMfb|JNWTEJbWJMTP|JNWTEJbWJMUQ|JNWTEJbWJMUR|JNWTEJbWLOfb|JNWTEJTOKTXO|JNWTEJTOLSVO|JNWTEJTPBEbW|JNWTEJTPJMbW|JNWTEJTPJMUQ|JNWTEJTPJMVS|JNWTEJTPJMXT|JNWTEJTPLOVR|JNWTEJUQAETP|JNWTEJURNUZQ|JNWTEJVRBEbW|JNWTEJVRJMUQ|JNWTEJVRLObW|JNWTFJTPBFbW|JNWTFJTPBFVR|JNWTFJTPJMXT|JNWTFJUQBFTP|JNWTFJVRJMZV|JNWTLObWHLTP|JNWTLObWHLUQ|JNWTLObWNRUN|JNWTLOVREJaV|JNWTLOVREJbW|JNWTLOVREJTP|JNWTLOVRFJbW|JNWTLPUQPWbJ|JNWTNRUNKRVM|JNWTNRVMIRUN|JNWTNSVOLSaV|JNXTEJbXJMVS|JNXTEJTOLSVO|JNXTEJTPJMWS|JNXTEJTPLOUQ|JNXTLObXHLfb|JNXTLObXHLTP|JNXTLObXHLUQ|JNXTLObXNRUN|JNXTLObXNRVM|JNXTLOTPOTVS|JNXTLPbXGLVR|JNXTLPbXGLVS|JNXTLPbXHLVS|JNXTLPbXNRUN|JNXTLPbXNRVM|JNXTLPUQEJVS|JNXTLPUQEJZU|JNXTLPUQFJVS|JNXTLPUQGLbX|JNXTLPUQGLYU|JNXTLPUQGLZU|JNXTLPUQHLVS|JNXTLPUQHLZU|JNXTLPUQNRVM|JNXTLPVREJaV|JNXTLPVREJbX|JNXTLPVRFJbX|JNXTLPVRGLaV|JNXTLPVRGLbX|JNXTLPVRHLaV|JNXTLPVSEJUQ|JNXTLPVSGLSJ|JNXTLPVSHLSJ|KNVRFKWSNWbS|KNVRFKWTJMaV|KNVRFKWTJMTP|KNVRGKZVJMUQ|KNVRGKZVJMWT|KNVSIMUQEIXT|KNVSIMXTEITP|KNVSIMXTFKTO|KNWSNWbSIMXT|KNWSNWbSLPeb|KNWSNWbSLPfb|KNWTFKbWJMTP|KNWTFKbWLPVS|KNWTFKTPBFbW|KNWTFKTPBFUQ|KNWTFKTPBFVR|KNWTFKTPJMXT|KNWTGKbWDGVS|KNWTGKbWJMVR|KNWTGKTPLOVR|KNWTJMTPMRVM|KNWTJMVRMVaK|KNWTLPbWNRUN|KNWTLPURNUYR|KNWTLPVRPWRK|KNXTLPVSGKbX|KNXTLPVSGKZV|KNXTLPVSIMbX|KOUQGKWSJNSJ|KOUQGKWTLPYU|KOUQGKYULPWS|KOUQJNVSOVaK|KOUQJNWSNWaK|KOURFKYUJNWT|KOURGKYUJNWS|KOURGKZUJNWS|KOWTFKTPBFUQ|KOWTFKTPBFUR|KOWTGKTPDGbW|KOWTGKTPDGUQ|KOWTGKTPKNPG|KOWTJMTKFOaW|KOWTJMTKFObW|KOWTJMTKFOUQ|KOWTJMTKFOUR|KOWTJMTKFOVR|KOWTJMTKGNVR|KOWTOSVOLSTP|KOWTOSVOLSUR|LOUQHLYULPVS|LOUQJMQJFMWS|LOUQJMQJFMWT|LOUQJNWSNWbL|LOURJMWSEJSL|LOVRJMaVHLWT|LOVRJNWTFJTP|LOWSGLbWKNUQ|LOWSGLbWKNUR|LOWSGLbWLPSL|LOWSHLbWJMUQ|LOWSHLSNJSXT|LOWSHLUQKNZU|LOWSHLURJNSJ|LOWSHLXTOXSN|LOWTJMbWEJWS|LOWTJMbWHLTP|LOWTJMbWMRUN|LOWTJMbWMRVM|LOWTJMUREJbW|LOWTJNbWNRUN|LOWTJNbWNRVM|LOWTJNVRFJTP|LPUQGLYUDGcY|LPUQGLYUDGVR|LPUQHLWSKNbW|LPUQHLYUKOVR|LPUQHLYUKOWT|LPUQJNWTPWbJ|LPURJNWSNWaT|LPVRHLZVLOWT|LPVRJMUQMVaR|LPVSHLXTKOTK|LPWSGLSOKTXO|LPWSGLSOLSVO|LPWSIMUREISO|LPWSJMSOKTXO|LPWSJMUQEJZU|LPWSJNSJFMaW|LPWSJNSJFMXT|LPWSKNaWFKXT|LPWTPWbSGLSO|LPWTPWbSIMfb|LPWTPWbSIMUQ|LPWTPWbSIMUR|LPWTPWbSIMXT|LPWTPWbSJMXT|LPWTPWbSJNSJ|LPWTPWbSKNaW|LPXTKOTKGNVS|IMUQEIVSKOaVFKZU|IMUQEIVSKOYUOVZS|IMUQEIWSMRVMIRbW|IMUQEIWTLPbWMRVM|IMUQEIWTMRVMIRZV|IMUQEIYUAEVSKNaV|IMUQEIYUKNcYFKWT|IMUQEIYUKNVRMVaK|IMUQEIYUKNWSNWaT|IMUQEIYULOURGLZU|IMUQEIZUAEURKNRK|"+
        "IMUQEIZUAEVRMVaR|IMUQEIZUAEVSLOSL|IMUQKNVRMVaKGNZU|IMUQKNWSNWaTEIZU|IMUQKNWSNWaTLOTK|IMUQKNWSNWbSFKYU|IMUQKNWTLPYUPWbS|IMUQKNWTNSVOLSaV|IMUQKNXTLPbXEITO|IMUQKNXTLPVSMRTO|IMUQKNXTNSVOLSWN|IMUQKNXTNSWNJSVO|IMUQKNYUNSWNJSQJ|IMUQLPWTPWaTEIZU|IMUQLPWTPWaTKOTK|IMUREIWSKObWFKWT|IMUREIWTJNbWNUZJ|IMUREIWTLOTPAEbW|IMURMQRMJNMIEJWT|IMURMQRMJNMINRVM|IMURMQRMLPWSEISO|IMURMQRMLPWSHLSO|IMURMQRMLPWTPWbS|IMVRMVaRLPZVGLWT|IMVSEIWTKOTKFVZS|IMVSKNXTMQaVEITP|IMVSKNXTMQbXFKaV|IMVSKNXTMQTPFKaV|IMVSKNXTMQTPFKbX|IMVSMQWTKNTPNWbS|IMWSLPbWGLUQKNVR|IMWTMQTPJNbWEJWT|IMWTMQTPJNbWNRUN|IMWTMRUNKRVMJQTP|IMXTLOUROXRIHLYU|IMXTLOUROXRIJNYU|IMXTMQTPJNWSNWbS|IMXTMQTPKNVSFKbX|IMXTMRUNKRVMJQTP|IMXTMRUNKRVMJQWS|IMXTMRVMJQTPEJbX|JMUQEJWTAETOKTXO|JMUQEJWTLPTOKTXO|JMUQEJZUKOURFKWS|JMUQFJWSLPZUJNSJ|JMUQFJYULPURHLZU|JMUQLOQJFMWTEJbW|JMUQLOQJFMWTMRVM|JMUQLOQJFMYUMRUN|JMUQMRVMIRWSEJbW|JMUQMRVMIRWSEJSO|JMUQMRVMIRWSLOSL|JMUQMRVMIRWTEJbW|JMUQMRVMIRWTEJZV|JMUQMRVMIRWTKNbW|JMUQMRVMIRWTLOTP|JMUREJWSKObWAEWT|JMUREJWSKObWFKYU|JMUREJWSKObWGKWT|JMUREJWSKORNAEbW|JMUREJWTJNbWNUZJ|JMUREJWTLObWJNfb|JMUREJWTLObWJNTP|JMUREJWTLObWMQTP|JMUREJWTLObWMQWS|JMUREJWTLOTPJNbW|JMUREJWTLPTOKTXO|JMURFJWSKOaWMQWT|JMURFJWSKObWMQeb|JMURKNRKGNVSEJSO|JMURKNRKGNWTMRVM|JMURKOWTLPTKGUZJ|JMURLOWTEJbWAEfb|JMURLOWTEJbWJNTP|JMURLOWTEJbWMQRM|JMURLOWTEJbWMQTP|JMURLOWTEJbWMQWS|JMURLOWTGLTPCGbW|JMURMQVSKOaVEJWT|JMVSEJWTLPTOKTXO|JMVSFJaVMQeaJNSJ|JMVSFJWTMQSNKRUN|JMVSFJWTMQTOKTXO|JMVSKOaVFKUREJWT|JMVSKOaVMQeaEJWT|JMVSKOUQOVQJENaK|JMVSLPSOKTXOMQUR|JMVSMQaVIMUREIWT|JMVSMQaVIMWTMRUN|JMVSMQUREJRNKRSO|JMVSMQURFJRMIRZU|JMVSMQURKNRKFVaR|JMVSMQURKOaVEJWT|JMVSMQURKOaVFKWT|JMVSMQURKOaVGKWT|JMVSMQURKOSNOSNK|JMVSMQURLPSOKTXO|JMVSMQWTEJTOKTXO|JMVSMQWTKOTKFVaR|JMVSMQWTKOTKFVZS|JMWSEJaWKNeaMQSO|JMWSEJaWKNXTMRVM|JMWSEJaWMQeaJMWT|JMWSEJbWAEfbMRUN|JMWSEJbWAEWTMRUN|JMWSEJbWKOUQFKZU|JMWSEJbWKOUQGKZU|JMWSEJSOKTXOLSVO|JMWSEJSOLSVOKTXO|JMWSEJURKOaWFKWT|JMWSEJURKOYUMQcY|JMWSFJbWMQWTJNSJ|JMWSKOaWEJWTFKbW|JMWSKOaWFKUQMRVM|JMWSKOaWFKWTEJbW|JMWSKOaWFKWTMRUN|JMWSKOaWGKWTEJTP|JMWSKOaWGKWTLPSL|JMWSKOaWMQeaEJWT|JMWSKOaWMQUREJWT|JMWSKOaWMQWTEJTK|JMWSKOaWMQWTFKTP|JMWSKOaWMQWTGKTP|JMWSKOaWMQWTGKUR|JMWSKOaWMQWTLPTK|JMWSKObWEJUQFKZU|JMWSKObWEJUQGKZU|JMWSKObWEJUQMRVM|JMWSKObWEJURFKWT|JMWSKObWEJURFKYU|JMWSKObWEJURFKZU|JMWSKObWFKUQBFQJ|JMWSKObWFKUQEJZU|JMWSKObWFKUQMRVM|JMWSKObWFKUREJWT|JMWSKObWFKUREJYU|JMWSKObWFKUREJZU|JMWSKObWFKWTLPSL|JMWSKObWGKUQLPSL|JMWSKObWMQWTEJTK|JMWSKObWMQWTLPTK|JMWSKOUQEJZUGKaW|JMWSKOUQGKQJEWaT|JMWSKOUQGKQJEWbS|JMWSKOUREJaWFKWT|JMWSLOSLHOUREJaW|JMWSLOSLHOVRMVZL|JMWSLPSOKTXOMQaW|JMWSLPSOKTXOMQbW|JMWSLPSOKTXOMQUR|JMWSMRUNKRVMIRbW|JMWSMRUNKRVMIRZU|JMWTEJbWAETPMQWS|JMWTEJbWJNfbMRVM|JMWTEJbWJNURNUZJ|JMWTEJbWLOfbMQTP|JMWTEJbWMQURLOTP|JMWTEJbWMQWSAESO|JMWTEJbWMQWSLPSO|JMWTEJTOKTXOLSVO|JMWTEJTOLSVOKTXO|JMWTEJTPAEURKOaW|JMWTEJTPLObWOTXO|JMWTEJTPMQbWJNVS|JMWTEJTPMQbWLOWS|JMWTEJTPMQXTLObX|JMWTEJUQMRVMIRTP|JMWTFJUQLPZUPWaT|JMWTKNaWNSWNMRVM|JMWTKNTOLSVOEJbW|JMWTKNTOLSVOEJUR|JMWTKNTPMQXTEJaW|JMWTKNVRMVaKGNbW|JMWTLObWEJfbAETP|JMWTLObWEJTPMQUR|JMWTLObWEJTPMQWS|JMWTLObWEJWSAESL|JMWTLObWEJWSMQSL|JMWTLObWMQWSEJSL|JMWTLObWMRUNKRVM|JMWTLObWMRVMIRUN|JMWTLOUREJbWJNTP|JMWTLPTOKTXOMQbW|JMWTLPTOKTXOMQUR|JMWTLPUQPWQJENbJ|JMWTMQTPEJXTJMTO|JMWTMRUNKRVMIRTO|JMWTMRUNKRVMIRZU|JMWTMRVMIRUNKRaW|JMWTMRVMIRUNKRTO|JMWTMRVMIRUNKRTP|JMXTLObXEJfbMQTP|JMXTLPbXMQTOKTXO|JMXTLPbXMQVSKNSJ|JMXTLPUQGLQJFMbX|JMXTLPUQHLQJFMVS|JMXTLPUQMRVMIRZU|JMXTLPVSHLbXDHeb|JMXTLPVSMQaVEJea|JNUQEJWSNWbSKOZU|JNUQEJWTAETPLObW|JNUQEJWTAETPLOVR|JNUQEJWTLPbWGLZU|JNUQEJWTNRVMIRbW|JNUQEJYUAEVRIMRI|JNUQEJZUAEWTLOVR|JNUQEJZUAEWTLPQM|JNUQEJZULPURNUQZ|JNUQEJZULPVRGLRM|JNUQKOWTGKQMIRVM|JNUQKOWTNRTKGNVM|JNUQLOWSNWbLHOYU|JNUQLOWTEJbWAETP|JNUQLOWTEJZUNScZ|JNUQLOWTEJZUNSdZ|JNUQLOWTEJZUNSVR|JNUQLOZUEJWTNSVR|JNUQLPVSEJSOKTXO|JNUQNRVMIRWSEJbW|JNUQNRVMIRWSEJSN|JNUQNRVMIRWSEJSO|JNUQNRVMIRWSLOSL|JNUQNRVMIRWTEJbW|"+
        "JNUQNRVMIRWTEJTP|JNUQNRVMIRWTEJZV|JNUQNRVMIRWTKNTP|JNUQNRVMIRWTKNZU|JNUQNRVMIRWTLObW|JNUQNRVMIRWTLOTP|JNUQNRVMIRWTLOZU|JNUQNRVMIRZUKNdZ|JNUQNRVMIRZUKNWT|JNUQNRVMIRZULOUN|JNUQNRVMIRZVEIVM|JNUQNSWNKRVMIRZV|JNURNUYREJWSKObW|JNURNUYREJWTAETP|JNURNUYREJWTJMTO|JNURNUYREJWTJMTP|JNURNUYREJWTJNRM|JNURNUYREJWTLObW|JNURNUYREJWTLOTP|JNURNUYREJWTLPTO|JNURNUZQEJWSKObW|JNURNUZQEJWSKOYU|JNURNUZQKNVRNUQZ|JNURNUZQLOWSGLYU|JNURNUZQLPWSPTXO|JNVREJaVBEWTJMTP|JNVREJaVJMUQNUQJ|JNVREJaVJMXTMQbX|JNVREJaVJMXTMQTP|JNVREJaVLOWTBETP|JNVREJaVLOWTBEUQ|JNVREJaVLOWTHLTP|JNVREJaVLOWTJMUQ|JNVREJaVLPeaGLVS|JNVREJaVLPVSGLZV|JNVREJaVLPXTHLbX|JNVREJWTBEbWJMTP|JNVREJWTBEZVJMbW|JNVREJWTJMaWMVZJ|JNVREJWTJMUQMVZJ|JNVREJWTJMUQNUQJ|JNVREJWTLObWBETP|JNVREJWTLObWJMUQ|JNVREJXTBETOLSaV|JNVREJXTJMUQNUQJ|JNVREJXTLOTPBEaV|JNVREJXTLOTPJMWS|JNVREJXTLOTPOTbX|JNVREJXTLOTPOTZV|JNVREJXTLPaVHLbX|JNVREJXTLPbXGLZV|JNVREJXTLPbXHLaV|JNVREJXTLPbXHLZV|JNVREJXTLPZVGLbX|JNVREJXTLPZVJMUQ|JNVREJZVJMUQNUQJ|JNVREJZVJMUQNUQZ|JNVREJZVLOUQNUQZ|JNVREJZVLOWTNScZ|JNVREJZVLOWTNSUQ|JNVREJZVLPUQNUQZ|JNVRFJaVJMUQNUQJ|JNVRFJaVJMWTMQTO|JNVRFJaVLPXTGLbX|JNVRFJWSNWbSJMRN|JNVRFJWSNWbSJMSN|JNVRFJWTJMaVMQTO|JNVRFJWTJMTPMVZJ|JNVRFJWTJMZVMQcZ|JNVRFJWTLObWJMTP|JNVRFJWTLOTPJMbW|JNVRFJWTLOZVNScZ|JNVRFJWTLOZVNSdZ|JNVRFJWTLOZVNSUQ|JNVRFJZVJMUQNUQZ|JNVRFJZVJMWTMQcZ|JNVRLOWTFJbWJMTP|JNVRLOZVEJWTNSUQ|JNVRLPWTPWbJFVaR|JNVRLPXTGLbXEJaV|JNVRLPZVGLRMIRVM|JNVRLPZVHLUQNUQZ|JNVRLPZVHLVSDHSJ|JNVSEJaVAEVRLPRM|JNVSEJaVKOdaOTXO|JNVSEJaVKOeaFKUR|JNVSEJaVKOeaGKUR|JNVSEJaVKOUQFKZU|JNVSEJaVKOUQGKZU|JNVSEJaVKOURNUYR|JNVSEJaVKOURNUZQ|JNVSEJaVLPUQGLZU|JNVSEJaVLPVRGLZV|JNVSEJUQAEZVIMdZ|JNVSEJUQAEZVIMYU|JNVSEJUQKOYUOVaK|JNVSEJURNUYRKORN|JNVSEJZVKOUQGKYU|JNVSEJZVKOUQNRVM|JNVSEJZVKOURNUYR|JNVSFJaVKOUQGKZU|JNVSFJaVKOURNUYR|JNVSFJaVLPXTCFUQ|JNVSFJZVKOUQGKYU|JNVSFJZVKOURNUYR|JNVSLOSJENUQAEWS|JNVSLOSJFMWTMQbW|JNVSLOSJFMWTMRUN|JNVSLOSLHOUQNRWT|JNVSLOSLHOURNUYR|JNVSLPSJFMWSGLaV|JNVSLPSJFMWSHLaV|JNVSLPSJFMWSHLUQ|JNVSLPSJFMWTPWbS|JNWSNWaTEJUQAEZU|JNWSNWaTIMTPLOUQ|JNWSNWaTIMUREITP|JNWSNWaTKNbWFKTP|JNWSNWaTKNbWFKVR|JNWSNWaTLOdaEJbW|JNWSNWaTLOeaFJbW|JNWSNWbSEJfbKObW|JNWSNWbSEJUQKOZU|JNWSNWbSIMaWMQWT|JNWSNWbSIMebMQSO|JNWSNWbSIMfbMQbW|JNWSNWbSLOSLHOfb|JNWTEJaWBETPNRVM|JNWTEJaWLOdaGLTP|JNWTEJaWLPeaAEVR|JNWTEJbWAEUQNSVO|JNWTEJbWAEVRLPaV|JNWTEJbWJMebMRVM|JNWTEJbWJMfbMQTO|JNWTEJbWJMfbMRVM|JNWTEJbWJMTPMQUR|JNWTEJbWJMTPNRUN|JNWTEJbWJMUQNRQJ|JNWTEJbWJMURNUZJ|JNWTEJTOKTXOLSVO|JNWTEJTOLSVOKTXO|JNWTEJTPBEbWJMUQ|JNWTEJTPJMbWBEUQ|JNWTEJTPJMbWMQUR|JNWTEJTPJMbWMQWT|JNWTEJTPJMbWMRVM|JNWTEJTPJMbWNRUN|JNWTEJTPJMUQNRQJ|JNWTEJTPJMVSNWbS|JNWTEJTPJMXTMQTO|JNWTEJTPJMXTMRVM|JNWTEJTPJMXTNRUN|JNWTEJTPLOVRBEbW|JNWTEJTPLOVRJMUQ|JNWTEJUQAETPLObW|JNWTEJURNUZQAEYU|JNWTEJVRBEbWJMTP|JNWTEJVRJMUQMVZJ|JNWTEJVRJMUQNUQJ|JNWTEJVRLObWBEaV|JNWTFJTPBFbWJMWT|JNWTFJTPBFVRJMZV|JNWTFJTPJMXTMRVM|JNWTFJUQBFTPLObW|JNWTFJVRJMZVMQcZ|JNWTLObWHLTPNRUN|JNWTLObWHLUQNRVM|JNWTLObWHLUQNSWN|JNWTLObWNRUNKRVM|JNWTLOVREJaVBEbW|JNWTLOVREJbWJMUQ|JNWTLOVREJTPJMUQ|JNWTLOVRFJbWJMfb|JNWTLOVRFJbWJMTP|JNWTLPUQPWbJENXT|JNWTLPUQPWbJFMQJ|JNWTNRUNKRVMIRaW|JNWTNRUNKRVMIRTO|JNWTNRUNKRVMIRTP|JNWTNRVMIRUNKRTO|JNWTNRVMIRUNKRTP|JNWTNRVMIRUNKRZU|JNWTNSVOLSaVKOTK|JNXTEJbXJMVSMQSJ|JNXTEJTOLSVOKTWP|JNXTEJTPJMWSNWbS|JNXTEJTPLOUQOTZU|JNXTLObXHLfbLPVS|JNXTLObXHLTPNRUN|JNXTLObXHLUQNRVM|JNXTLObXHLUQNSWN|JNXTLObXNRUNKRVM|JNXTLObXNRVMIRUN|JNXTLOTPOTVSTXSJ|JNXTLPbXGLVRLOaV|JNXTLPbXGLVSDGSJ|JNXTLPbXGLVSLOSL|JNXTLPbXHLVSDHSJ|JNXTLPbXNRUNKRVM|JNXTLPbXNRVMIRUN|JNXTLPUQEJVSAEbX|JNXTLPUQEJZUGLbX|JNXTLPUQEJZUGLVR|JNXTLPUQEJZUHLVS|JNXTLPUQFJVSGLbX|JNXTLPUQGLbXLOZU|JNXTLPUQGLYULObX|JNXTLPUQGLZUDGbX|JNXTLPUQGLZULObX|JNXTLPUQHLVSDHSJ|JNXTLPUQHLVSEJbX|JNXTLPUQHLZULObX|JNXTLPUQNRVMIRaV|JNXTLPUQNRVMIRZU|JNXTLPVREJaVHLbX|JNXTLPVREJbXGLZV|JNXTLPVREJbXHLaV|JNXTLPVREJbXJMTO|JNXTLPVRFJbXJMTO|JNXTLPVRGLaVLObX|JNXTLPVRGLbXEJaV|JNXTLPVRHLaVEJbX|JNXTLPVSEJUQGLbX|"+
        "JNXTLPVSGLSJFMbX|JNXTLPVSHLSJENZV|KNVRFKWSNWbSJMRN|KNVRFKWTJMaVEJTO|KNVRFKWTJMTPMVZJ|KNVRGKZVJMUQNUQZ|KNVRGKZVJMWTDGTP|KNVRGKZVJMWTDGUQ|KNVSIMUQEIXTLPbX|KNVSIMXTEITPMRWT|KNVSIMXTFKTOKTWP|KNWSNWbSIMXTLPTO|KNWSNWbSLPebGLSO|KNWSNWbSLPebGLUQ|KNWSNWbSLPebJMbW|KNWSNWbSLPebJMUQ|KNWSNWbSLPfbJMbW|KNWTFKbWJMTPMRVM|KNWTFKbWLPVSGLTO|KNWTFKTPBFbWJMfb|KNWTFKTPBFbWJMUQ|KNWTFKTPBFbWNRUN|KNWTFKTPBFUQNRVM|KNWTFKTPBFVRJMbW|KNWTFKTPJMXTMRVM|KNWTGKbWDGVSLOSL|KNWTGKbWJMVRMVZJ|KNWTGKTPLOVRJMPL|KNWTJMTPMRVMIRXT|KNWTJMVRMVaKGNbW|KNWTJMVRMVaKGNea|KNWTJMVRMVaKGNTP|KNWTLPbWNRUNJbfW|KNWTLPURNUYRPWbS|KNWTLPVRPWRKGNaT|KNWTLPVRPWRKGNbS|KNXTLPVSGKbXDGTO|KNXTLPVSGKbXDGUQ|KNXTLPVSGKZVHLcZ|KNXTLPVSIMbXMQTO|KNXTLPVSIMbXMRTO|KOUQGKWSJNSJENZU|KOUQGKWTLPYUPWbL|KOUQGKYULPWSJMQJ|KOUQJNVSOVaKFOWT|KOUQJNVSOVaKGNYU|KOUQJNWSNWaKFObW|KOURFKYUJNWTLPVS|KOURGKYUJNWSNWaT|KOURGKZUJNWSNWaT|KOURGKZUJNWSNWbS|KOWTFKTPBFUQJNbW|KOWTFKTPBFURJMYU|KOWTGKTPDGbWOTXO|KOWTGKTPDGUQJNYU|KOWTGKTPKNPGCLbW|KOWTJMTKFOaWBFWT|KOWTJMTKFOaWGKWT|KOWTJMTKFOaWLPea|KOWTJMTKFObWGKWT|KOWTJMTKFObWMRUN|KOWTJMTKFObWMRVM|KOWTJMTKFObWOSVO|KOWTJMTKFOUQMRVM|KOWTJMTKFOUREJbW|KOWTJMTKFOURGKbW|KOWTJMTKFOURMQbW|KOWTJMTKFOVRMVaR|KOWTJMTKGNVRMVaK|KOWTOSVOLSTPHLaV|KOWTOSVOLSURJMYU|LOUQHLYULPVSOVZS|LOUQJMQJFMWSHLYU|LOUQJMQJFMWTMRVM|LOUQJNWSNWbLGPfb|LOUQJNWSNWbLHOfb|LOURJMWSEJSLHObW|LOVRJMaVHLWTLPUQ|LOVRJNWTFJTPJMZV|LOWSGLbWKNUQFKZU|LOWSGLbWKNURNUYR|LOWSGLbWLPSLPGWS|LOWSGLbWLPSLPGXT|LOWSHLbWJMUQMRVM|LOWSHLSNJSXTOXVH|LOWSHLUQKNZUNWaK|LOWSHLURJNSJEUYR|LOWSHLXTOXSNJSVH|LOWTJMbWEJWSAESL|LOWTJMbWEJWSBESL|LOWTJMbWHLTPMRUN|LOWTJMbWMRUNKRVM|LOWTJMbWMRVMIRUN|LOWTJMUREJbWJNfb|LOWTJMUREJbWMQTP|LOWTJNbWNRUNKRVM|LOWTJNbWNRVMIRUN|LOWTJNVRFJTPJMUQ|LPUQGLYUDGcYJMQJ|LPUQGLYUDGVRJNZV|LPUQHLWSKNbWFKZU|LPUQHLYUKOVRJMQJ|LPUQHLYUKOWTPWaK|LPUQJNWTPWbJENXT|LPURJNWSNWaTPWbS|LPVRHLZVLOWTPWbL|LPVRJMUQMVaREJZU|LPVSHLXTKOTKFVaR|LPVSHLXTKOTKFVZS|LPWSGLSOKTXOLSVO|LPWSGLSOLSVOKTXO|LPWSIMUREISOKTXO|LPWSJMSOKTXOMQbW|LPWSJMSOKTXOMQUR|LPWSJMUQEJZUKNcZ|LPWSJNSJFMaWMQWT|LPWSJNSJFMXTPWbS|LPWTPWbSGLSOKTXO|LPWTPWbSIMfbKNbW|LPWTPWbSIMfbMQSO|LPWTPWbSIMUQEIZU|LPWTPWbSIMUREISO|LPWTPWbSIMXTKNTP|LPWTPWbSJMXTMQTP|LPWTPWbSJNSJENXT|LPWTPWbSKNaWGLXT|LPXTKOTKGNVSFKaV|LPXTKOTKGNVSHLaV|IMUQEIVSKOaVFKZUJNQJ|IMUQEIVSKOaVFKZUKNUR|IMUQEIVSKOaVFKZUKNVR|IMUQEIVSKOYUOVZSBEXT|IMUQEIWSMRVMIRbWAEfb|IMUQEIWTLPbWMRVMIRTO|IMUQEIWTMRVMIRZVAEVM|IMUQEIYUAEVSKNaVGKea|IMUQEIYUKNcYFKWTBEaW|IMUQEIYUKNVRMVaKFOWT|IMUQEIYUKNWSNWaTBEUR|IMUQEIYUKNWSNWaTLOTK|IMUQEIYULOURGLZUDGcY|IMUQEIZUAEURKNRKGNVR|IMUQEIZUAEVRMVaRLOWT|IMUQEIZUAEVSLOSLHOUR|IMUQKNVRMVaKGNZUDGUR|IMUQKNWSNWaTEIZUBEUR|IMUQKNWSNWaTLOTKGNbW|IMUQKNWSNWbSFKYUJNQJ|IMUQKNWTLPYUPWbSNWaT|IMUQKNWTNSVOLSaVGLVO|IMUQKNXTLPbXEITOGKZU|IMUQKNXTLPbXEITOMRVM|IMUQKNXTLPVSMRTOGKbX|IMUQKNXTNSVOLSWNJSQJ|IMUQKNXTNSWNJSVOLSQJ|IMUQKNYUNSWNJSQJENVO|IMUQLPWTPWaTEIZUHLTP|IMUQLPWTPWaTKOTKGNbW|IMUREIWSKObWFKWTLPSL|IMUREIWTJNbWNUZJFMfb|IMUREIWTLOTPAEbWOTXO|IMURMQRMJNMIEJWTLPYU|IMURMQRMJNMINRVMQJYU|IMURMQRMLPWSEISOIRVM|IMURMQRMLPWSHLSOLSVO|IMURMQRMLPWTPWbSHLMI|IMURMQRMLPWTPWbSJNSJ|IMVRMVaRLPZVGLWTPWbS|IMVSEIWTKOTKFVZSMQXT|IMVSKNXTMQaVEITPFKWT|IMVSKNXTMQbXFKaVJMSJ|IMVSKNXTMQTPFKaVKObX|IMVSKNXTMQTPFKbXJMSJ|IMVSMQWTKNTPNWbSJMfb|IMWSLPbWGLUQKNVRMOWT|IMWTMQTPJNbWEJWTAETO|IMWTMQTPJNbWNRUNKRVM|IMWTMRUNKRVMJQTPEJbW|IMXTLOUROXRIHLYULPUQ|IMXTLOUROXRIJNYUHLUQ|IMXTMQTPJNWSNWbSEJfb|IMXTMQTPKNVSFKbXJMSJ|IMXTMRUNKRVMJQTPEJWT|IMXTMRUNKRVMJQWSLPTO|IMXTMRVMJQTPEJbXJNWT|JMUQEJWTAETOKTXOLSVO|JMUQEJWTLPTOKTXOMRVM|JMUQEJZUKOURFKWSLPSL|JMUQFJWSLPZUJNSJMFUR|JMUQFJYULPURHLZUDHWS|JMUQLOQJFMWTEJbWBFTP|JMUQLOQJFMWTMRVMIRbW|JMUQLOQJFMYUMRUNKRVM|JMUQMRVMIRWSEJbWAEfb|JMUQMRVMIRWSEJbWBEfb|JMUQMRVMIRWSEJSOLSZV|JMUQMRVMIRWSLOSLHObW|JMUQMRVMIRWTEJbWAETP|JMUQMRVMIRWTEJbWLOZU|JMUQMRVMIRWTEJZVAEVM|JMUQMRVMIRWTKNbWFKTP|JMUQMRVMIRWTLOTPEJbW|JMUREJWSKObWAEWTLPTK|JMUREJWSKObWFKYUMQeb|JMUREJWSKObWGKWTLPSL|"+
        "JMUREJWSKORNAEbWFKZU|JMUREJWSKORNAEbWLPSL|JMUREJWTJNbWNUZJFMfb|JMUREJWTLObWJNfbNUZJ|JMUREJWTLObWJNTPNUZJ|JMUREJWTLObWMQTPJNWT|JMUREJWTLObWMQWSJMSL|JMUREJWTLOTPJNbWNUZJ|JMUREJWTLPTOKTXOMQRM|JMURFJWSKOaWMQWTJMTK|JMURFJWSKObWMQebJMYU|JMURKNRKGNVSEJSOLSaV|JMURKNRKGNWTMRVMIRZU|JMURKOWTLPTKGUZJENXT|JMURLOWTEJbWAEfbMQTP|JMURLOWTEJbWAEfbMQYU|JMURLOWTEJbWJNTPNUZJ|JMURLOWTEJbWMQRMIRVM|JMURLOWTEJbWMQTPOTXO|JMURLOWTEJbWMQWSJMSL|JMURLOWTGLTPCGbWOTXO|JMURMQVSKOaVEJWTLPTK|JMVSEJWTLPTOKTXOGKUQ|JMVSFJaVMQeaJNSJENUR|JMVSFJWTMQSNKRUNJSTO|JMVSFJWTMQTOKTXOIMSN|JMVSKOaVFKUREJWTKNTK|JMVSKOaVMQeaEJWTJMTK|JMVSKOUQOVQJENaKFOYU|JMVSLPSOKTXOMQUREJaV|JMVSMQaVIMUREIWTLPSN|JMVSMQaVIMWTMRUNKaeV|JMVSMQUREJRNKRSOLSWE|JMVSMQURFJRMIRZUQZcO|JMVSMQURKNRKFVaREJea|JMVSMQURKOaVEJWTGKSN|JMVSMQURKOaVEJWTJMTK|JMVSMQURKOaVFKWTKNTK|JMVSMQURKOaVGKWTLPSL|JMVSMQURKOSNOSNKGUWN|JMVSMQURLPSOKTXOEJZU|JMVSMQWTEJTOKTXOJMUR|JMVSMQWTKOTKFVaRLObW|JMVSMQWTKOTKFVZSQZdU|JMWSEJaWKNeaMQSOLSVO|JMWSEJaWKNXTMRVMIRbX|JMWSEJaWMQeaJMWTMRUN|JMWSEJbWAEfbMRUNKRVM|JMWSEJbWAEWTMRUNKRVM|JMWSEJbWKOUQFKZUJNSJ|JMWSEJbWKOUQGKZULPSL|JMWSEJSOKTXOLSVOMQbW|JMWSEJSOKTXOLSVOMQUR|JMWSEJSOLSVOKTXOAEUR|JMWSEJSOLSVOKTXOBEUQ|JMWSEJSOLSVOKTXOBEZV|JMWSEJSOLSVOKTXOGLaW|JMWSEJSOLSVOKTXOMQUR|JMWSEJURKOaWFKWTKNTK|JMWSEJURKOYUMQcYJMbW|JMWSFJbWMQWTJNSJENTO|JMWSFJbWMQWTJNSJENTP|JMWSKOaWFKUQMRVMIRWT|JMWSKOaWFKWTEJbWBFUQ|JMWSKOaWFKWTMRUNKaTK|JMWSKOaWGKWTEJTPDGUR|JMWSKOaWGKWTLPSLPGTO|JMWSKOaWMQeaEJWTJMTK|JMWSKOaWMQUREJWTJMTK|JMWSKOaWMQWTEJTKGWbS|JMWSKOaWMQWTFKTPEJUR|JMWSKOaWMQWTGKTPDGUR|JMWSKOaWMQWTGKURLPSL|JMWSKOaWMQWTLPTKGWbS|JMWSKObWEJUQFKZUJNSJ|JMWSKObWEJUQGKZULPSL|JMWSKObWEJUQMRVMOVaR|JMWSKObWEJURFKWTLPSL|JMWSKObWEJURFKYUMQcY|JMWSKObWFKUQBFQJFMfb|JMWSKObWFKUQBFQJFMYU|JMWSKObWFKUQEJZUJNSJ|JMWSKObWFKUQMRVMIRSN|JMWSKObWFKUREJWTLPSL|JMWSKObWFKUREJYUMQcY|JMWSKObWFKUREJZUMQRM|JMWSKObWFKWTLPSLPWaT|JMWSKObWGKUQLPSLPGQJ|JMWSKObWMQWTEJTKGWaT|JMWSKObWMQWTLPTKGWaT|JMWSKOUQEJZUGKaWKNVR|JMWSKOUQGKQJEWaTAETP|JMWSKOUQGKQJEWaTAEYU|JMWSKOUQGKQJEWaTIMTP|JMWSKOUQGKQJEWaTIMZU|JMWSKOUQGKQJEWaTLPYU|JMWSKOUQGKQJEWbSIMaW|JMWSKOUQGKQJEWbSIMYU|JMWSKOUREJaWFKWTKNTK|JMWSLOSLHOUREJaWAEWS|JMWSLOSLHOUREJaWJNWS|JMWSLOSLHOVRMVZLGPXT|JMWSLPSOKTXOMQaWEJWT|JMWSLPSOKTXOMQbWEJfb|JMWSLPSOKTXOMQbWEJWT|JMWSLPSOKTXOMQUREJaW|JMWSLPSOKTXOMQUREJbW|JMWSLPSOKTXOMQUREJRM|JMWSMRUNKRVMIRbWLOSL|JMWSMRUNKRVMIRZUFKUN|JMWTEJbWAETPMQWSLOSL|JMWTEJbWJNfbMRVMIRTP|JMWTEJbWJNURNUZJFMVS|JMWTEJbWLOfbMQTPOTXO|JMWTEJbWMQURLOTPJNWT|JMWTEJbWMQWSAESOLSVO|JMWTEJbWMQWSLPSOPWaT|JMWTEJTOKTXOLSVOMQbW|JMWTEJTOLSVOKTXOBEUR|JMWTEJTOLSVOKTXOBEZV|JMWTEJTOLSVOKTXOMQbW|JMWTEJTPAEURKOaWOTXO|JMWTEJTPLObWOTXOKTWS|JMWTEJTPMQbWJNVSFJaV|JMWTEJTPMQbWLOWSAESL|JMWTEJTPMQXTLObXJNUR|JMWTEJUQMRVMIRTPLObW|JMWTFJUQLPZUPWaTCFUR|JMWTFJUQLPZUPWaTCFVS|JMWTFJUQLPZUPWaTKNUR|JMWTKNaWNSWNMRVMIKea|JMWTKNaWNSWNMRVMIKTP|JMWTKNTOLSVOEJbWGLfb|JMWTKNTOLSVOEJURNUYR|JMWTKNTPMQXTEJaWAEWS|JMWTKNVRMVaKGNbWEJTP|JMWTLObWEJfbAETPMRVM|JMWTLObWEJTPMQURJNfb|JMWTLObWEJTPMQWSAESL|JMWTLObWEJWSAESLGWaT|JMWTLObWEJWSMQSLGWaT|JMWTLObWMQWSEJSLGWaT|JMWTLObWMRUNKRVMIRTK|JMWTLObWMRVMIRUNKRTK|JMWTLOUREJbWJNTPNUZJ|JMWTLPTOKTXOMQbWFJWT|JMWTLPTOKTXOMQUREJRM|JMWTLPUQPWQJENbJFMfb|JMWTLPUQPWQJENbJFMXT|JMWTMQTPEJXTJMTOLSVO|JMWTMRUNKRVMIRTOLSZU|JMWTMRUNKRVMIRZUFKUN|JMWTMRVMIRUNKRaWFKWS|JMWTMRVMIRUNKRTOLSZU|JMWTMRVMIRUNKRTPEJbW|JMXTLObXEJfbMQTPJNUR|JMXTLPbXMQTOKTXOGKWT|JMXTLPbXMQVSKNSJENUR|JMXTLPUQGLQJFMbXEJVS|JMXTLPUQHLQJFMVSMQSN|JMXTLPUQMRVMIRZURVaR|JMXTLPVSHLbXDHebKOTD|JMXTLPVSMQaVEJeaJNSJ|JNUQEJWSNWbSKOZUJNSJ|JNUQEJWTAETPLObWNSWN|JNUQEJWTAETPLOVRNUYR|JNUQEJWTLPbWGLZULOUR|JNUQEJWTNRVMIRbWLOfb|JNUQEJYUAEVRIMRINSWN|JNUQEJZUAEWTLOVROSaW|JNUQEJZUAEWTLPQMJSaV|JNUQEJZULPURNUQZIMYU|JNUQEJZULPVRGLRMIRWT|JNUQKOWTGKQMIRVMEIZV|JNUQKOWTNRTKGNVMIRbW|JNUQLOWSNWbLHOYUOTXO|JNUQLOWTEJbWAETPNRVM|JNUQLOWTEJZUNScZKNTR|JNUQLOWTEJZUNSdZSWbL|JNUQLOWTEJZUNSVRJNcZ|JNUQLOZUEJWTNSVRJNTP|"+
        "JNUQLPVSEJSOKTXOAEWS|JNUQNRVMIRWSEJbWAEfb|JNUQNRVMIRWSEJbWBEfb|JNUQNRVMIRWSEJbWBEZU|JNUQNRVMIRWSEJbWLOSL|JNUQNRVMIRWSEJSNJSZV|JNUQNRVMIRWSEJSOLSaV|JNUQNRVMIRWSLOSLHObW|JNUQNRVMIRWTEJbWLOaV|JNUQNRVMIRWTEJbWLOfb|JNUQNRVMIRWTEJbWLOTP|JNUQNRVMIRWTEJbWLOZV|JNUQNRVMIRWTEJTPAEbW|JNUQNRVMIRWTEJTPLObW|JNUQNRVMIRWTEJZVAEVM|JNUQNRVMIRWTEJZVJMQJ|JNUQNRVMIRWTKNTPFKXT|JNUQNRVMIRWTKNZUFKcZ|JNUQNRVMIRWTLObWEJfb|JNUQNRVMIRWTLObWEJTP|JNUQNRVMIRWTLObWEJZV|JNUQNRVMIRWTLObWKNTK|JNUQNRVMIRWTLOTPEJbW|JNUQNRVMIRWTLOTPHLbW|JNUQNRVMIRWTLOZUHLUN|JNUQNRVMIRZUKNdZLOWT|JNUQNRVMIRZUKNdZLOZV|JNUQNRVMIRZUKNWTFKTP|JNUQNRVMIRZULOUNKRdZ|JNUQNRVMIRZULOUNKRWT|JNUQNRVMIRZVEIVMIRWT|JNUQNSWNKRVMIRZVEIVM|JNURNUYREJWSKObWJMWT|JNURNUYREJWTAETPJNRM|JNURNUYREJWTJMTOLSVO|JNURNUYREJWTJMTPLObW|JNURNUYREJWTJNRMIRVM|JNURNUYREJWTLObWJMfb|JNURNUYREJWTLObWJMTP|JNURNUYREJWTLOTPAEbW|JNURNUYREJWTLOTPJMbW|JNURNUYREJWTLOTPJNbW|JNURNUYREJWTLPTOKTXO|JNURNUZQEJWSKObWGKYU|JNURNUZQEJWSKOYUJNSJ|JNURNUZQKNVRNUQZEJaV|JNURNUZQKNVRNUQZFKaV|JNURNUZQLOWSGLYUOTXO|JNURNUZQLPWSPTXOKTYU|JNVREJaVBEWTJMTPLOUQ|JNVREJaVJMUQNUQJFMZJ|JNVREJaVJMXTMQbXLOfb|JNVREJaVJMXTMQTPFJWT|JNVREJaVJMXTMQTPLOWS|JNVREJaVLOWTBETPJMUQ|JNVREJaVLOWTBEUQNUYR|JNVREJaVLOWTHLTPDHUQ|JNVREJaVLOWTJMUQNUQJ|JNVREJaVLPeaGLVSLOSL|JNVREJaVLPVSGLZVLOSL|JNVREJaVLPXTHLbXLOWS|JNVREJWTBEbWJMTPMVZJ|JNVREJWTBEZVJMbWMQcZ|JNVREJWTJMaWMVZJFMWS|JNVREJWTJMUQMVZJFMQJ|JNVREJWTJMUQNUQJFMZJ|JNVREJWTLObWBETPJMWT|JNVREJWTLObWJMUQMVZJ|JNVREJXTBETOLSaVJMVO|JNVREJXTJMUQNUQJFMZJ|JNVREJXTLOTPBEaVHLWS|JNVREJXTLOTPBEaVJMVS|JNVREJXTLOTPJMWSNWbL|JNVREJXTLOTPOTbXJMXO|JNVREJXTLOTPOTZVJMUQ|JNVREJXTLPaVHLbXLOWS|JNVREJXTLPbXGLZVLOUQ|JNVREJXTLPbXHLaVJMWS|JNVREJXTLPbXHLZVJMUQ|JNVREJXTLPZVGLbXJMUQ|JNVREJXTLPZVJMUQNUQZ|JNVREJZVJMUQNUQJFMYR|JNVREJZVJMUQNUQZAEVS|JNVREJZVJMUQNUQZAEWS|JNVREJZVJMUQNUQZAEWT|JNVREJZVJMUQNUQZAEXT|JNVREJZVJMUQNUQZAEYU|JNVREJZVJMUQNUQZFJWS|JNVREJZVJMUQNUQZKNVR|JNVREJZVJMUQNUQZKNVS|JNVREJZVJMUQNUQZKNWS|JNVREJZVJMUQNUQZKNXT|JNVREJZVJMUQNUQZLOWS|JNVREJZVJMUQNUQZLOWT|JNVREJZVJMUQNUQZMQWS|JNVREJZVJMUQNUQZMQWT|JNVREJZVJMUQNUQZMRVM|JNVREJZVLOUQNUQZAEWS|JNVREJZVLOWTNScZIMRI|JNVREJZVLOWTNSUQSZdU|JNVREJZVLPUQNUQZHLWS|JNVRFJaVJMUQNUQJENYR|JNVRFJaVJMWTMQTOLSVF|JNVRFJaVLPXTGLbXLOWS|JNVRFJWSNWbSJMRNKRUN|JNVRFJWSNWbSJMSNMVaR|JNVRFJWTJMaVMQTOLSVF|JNVRFJWTJMTPMVZJENUQ|JNVRFJWTJMZVMQcZLOTP|JNVRFJWTLObWJMTPMVZJ|JNVRFJWTLOTPJMbWMVZJ|JNVRFJWTLOZVNScZIMRI|JNVRFJWTLOZVNSdZSWbL|JNVRFJWTLOZVNSUQSZcV|JNVRFJWTLOZVNSUQSZdU|JNVRFJZVJMUQNUQZEJWT|JNVRFJZVJMUQNUQZMQWS|JNVRFJZVJMUQNUQZMRVM|JNVRFJZVJMWTMQcZLObW|JNVRFJZVJMWTMQcZLOTP|JNVRLOWTFJbWJMTPMVZJ|JNVRLOZVEJWTNSUQSZdU|JNVRLPWTPWbJFVaREJZV|JNVRLPXTGLbXEJaVLOWS|JNVRLPZVGLRMIRVMEIcZ|JNVRLPZVHLUQNUQZIMWS|JNVRLPZVHLUQNUQZIMWT|JNVRLPZVHLUQNUQZIMYU|JNVRLPZVHLVSDHSJFVaR|JNVSEJaVAEVRLPRMIRSO|JNVSEJaVKOdaOTXOGKbX|JNVSEJaVKOeaFKURNUYR|JNVSEJaVKOeaGKURNUYR|JNVSEJaVKOUQFKZUJMQJ|JNVSEJaVKOUQGKZUBEUR|JNVSEJaVKOUQGKZUDGUR|JNVSEJaVKOUQGKZULPSL|JNVSEJaVKOURNUYRJMea|JNVSEJaVKOURNUYRJMZU|JNVSEJaVKOURNUZQGKYU|JNVSEJaVLPUQGLZUKOUR|JNVSEJaVLPVRGLZVLOSL|JNVSEJUQAEZVIMdZKOZU|JNVSEJUQAEZVIMYUEIUR|JNVSEJUQKOYUOVaKFOWT|JNVSEJURNUYRKORNOVaR|JNVSEJZVKOUQGKYUBEcY|JNVSEJZVKOUQGKYUBEUR|JNVSEJZVKOUQGKYUDGUR|JNVSEJZVKOUQNRVMIRXT|JNVSEJZVKOURNUYRJMcZ|JNVSFJaVKOUQGKZUDGUR|JNVSFJaVKOURNUYRBFWT|JNVSFJaVKOURNUYRJMRN|JNVSFJaVKOURNUYRJMZU|JNVSFJaVLPXTCFUQGLZU|JNVSFJZVKOUQGKYULPSL|JNVSFJZVKOURNUYRJMRN|JNVSLOSJENUQAEWSNWbL|JNVSLOSJFMWTMQbWEJTP|JNVSLOSJFMWTMRUNKRTK|JNVSLOSLHOUQNRWTIMQJ|JNVSLOSLHOURNUYREJaV|JNVSLPSJFMWSGLaVLOSL|JNVSLPSJFMWSHLaVKObW|JNVSLPSJFMWSHLUQEJaV|JNVSLPSJFMWTPWbSEJfb|JNVSLPSJFMWTPWbSEJXT|JNWSNWaTEJUQAEZUJNUR|JNWSNWaTIMTPLOUQEIQJ|JNWSNWaTIMUREITPLObW|JNWSNWaTKNbWFKTPNRVM|JNWSNWaTKNbWFKVREJTP|JNWSNWaTLOdaEJbWJMUQ|JNWSNWaTLOeaFJbWJNUR|JNWSNWbSEJfbKObWGKUR|JNWSNWbSEJUQKOZUJNSJ|JNWSNWbSIMaWMQWTKNSJ|JNWSNWbSIMebMQSOLSVO|JNWSNWbSIMfbMQbWEIUR|JNWSNWbSLOSLHOfbEJVR|"+
        "JNWTEJaWBETPNRVMJQUR|JNWTEJaWLOdaGLTPAEPG|JNWTEJaWLPeaAEVRJMUQ|JNWTEJaWLPeaAEVRJMZV|JNWTEJbWAEUQNSVOLbfW|JNWTEJbWAEVRLPaVGLWS|JNWTEJbWJMebMRVMIRTP|JNWTEJbWJMfbMQTOKTXO|JNWTEJbWJMfbMRVMIRTP|JNWTEJbWJMTPMQURNUYR|JNWTEJbWJMTPNRUNKRWS|JNWTEJbWJMTPNRUNKRZU|JNWTEJbWJMUQNRQJFMfb|JNWTEJbWJMURNUZJFMfb|JNWTEJTOKTXOLSVOAEUR|JNWTEJTOKTXOLSVOIMOK|JNWTEJTOLSVOKTXOAEUR|JNWTEJTPBEbWJMUQNRQJ|JNWTEJTPJMbWBEUQNRQJ|JNWTEJTPJMbWMQURNUYR|JNWTEJTPJMbWMQWTLOUR|JNWTEJTPJMbWMRVMIRfb|JNWTEJTPJMbWNRUNKRWS|JNWTEJTPJMbWNRUNKRZU|JNWTEJTPJMUQNRQJFMbW|JNWTEJTPJMVSNWbSMQfb|JNWTEJTPJMXTMQTOKTPW|JNWTEJTPJMXTMQTOLSVO|JNWTEJTPJMXTMRVMIRZV|JNWTEJTPJMXTNRUNKRTO|JNWTEJTPJMXTNRUNKRZU|JNWTEJTPLOVRBEbWJMWT|JNWTEJTPLOVRJMUQMVZJ|JNWTEJUQAETPLObWNSWN|JNWTEJURNUZQAEYUJNVR|JNWTEJVRBEbWJMTPMVZJ|JNWTEJVRJMUQMVZJFMQJ|JNWTEJVRJMUQNUQJFMZJ|JNWTEJVRLObWBEaVJMVS|JNWTFJTPBFbWJMWTNRUN|JNWTFJTPBFVRJMZVMQcZ|JNWTFJTPJMXTMRVMIRbX|JNWTFJUQBFTPLObWOTXO|JNWTFJVRJMZVMQcZLOTP|JNWTLObWHLTPNRUNKRVM|JNWTLObWHLUQNRVMIRTP|JNWTLObWHLUQNSWNKRVM|JNWTLObWNRUNKRVMIRTK|JNWTLOVREJaVBEbWJMUQ|JNWTLOVREJbWJMUQNUQJ|JNWTLOVREJTPJMUQMVZJ|JNWTLOVREJTPJMUQNUQJ|JNWTLOVRFJbWJMfbMVZJ|JNWTLOVRFJbWJMTPMVZJ|JNWTLPUQPWbJENXTAEfb|JNWTLPUQPWbJENXTAETP|JNWTLPUQPWbJENXTAEYU|JNWTLPUQPWbJENXTHLTP|JNWTLPUQPWbJFMQJENYU|JNWTNRUNKRVMIRaWFKda|JNWTNRUNKRVMIRaWGKTP|JNWTNRUNKRVMIRaWLOTK|JNWTNRUNKRVMIRTOLSZU|JNWTNRUNKRVMIRTPEJbW|JNWTNRUNKRVMIRTPEJZU|JNWTNRUNKRVMIRTPLObW|JNWTNRVMIRUNKRTOLSZU|JNWTNRVMIRUNKRTPFKbW|JNWTNRVMIRUNKRZUFKUN|JNWTNSVOLSaVKOTKFObW|JNXTEJbXJMVSMQSJFMTP|JNXTEJTOLSVOKTWPAEaV|JNXTEJTPJMWSNWbSMQfb|JNXTEJTPJMWSNWbSMQSO|JNXTEJTPLOUQOTZUTXVR|JNXTLObXHLfbLPVSOVZJ|JNXTLObXHLTPNRUNKRVM|JNXTLObXHLUQNRVMIRTP|JNXTLObXHLUQNSWNKRTK|JNXTLObXHLUQNSWNKRVM|JNXTLObXNRUNKRVMIRTK|JNXTLObXNRVMIRUNKRTK|JNXTLOTPOTVSTXSJENWS|JNXTLPbXGLVRLOaVHLWS|JNXTLPbXGLVSDGSJENUR|JNXTLPbXGLVSDGSJFMUQ|JNXTLPbXGLVSLOSLPGTO|JNXTLPbXHLVSDHSJENUQ|JNXTLPbXHLVSDHSJENUR|JNXTLPbXHLVSDHSJFMUR|JNXTLPbXNRUNKRVMIReb|JNXTLPbXNRUNKRVMIRTO|JNXTLPbXNRUNKRVMIRZV|JNXTLPbXNRVMIRUNKRZV|JNXTLPUQEJVSAEbXIMZU|JNXTLPUQEJZUGLbXLOUR|JNXTLPUQEJZUGLVRLObX|JNXTLPUQEJZUHLVSBEaV|JNXTLPUQFJVSGLbXLOSL|JNXTLPUQGLbXLOZUHLVR|JNXTLPUQGLYULObXHLVS|JNXTLPUQGLZUDGbXEJUR|JNXTLPUQGLZULObXEJUR|JNXTLPUQGLZULObXHLUR|JNXTLPUQGLZULObXHLVR|JNXTLPUQHLVSDHSJFMQJ|JNXTLPUQHLVSEJbXDHYU|JNXTLPUQHLZULObXNSWN|JNXTLPUQNRVMIRaVRaeV|JNXTLPUQNRVMIRZUEIUN|JNXTLPUQNRVMIRZUKNTO|JNXTLPUQNRVMIRZURVaR|JNXTLPVREJaVHLbXLOWS|JNXTLPVREJbXGLZVLOUQ|JNXTLPVREJbXHLaVLOWS|JNXTLPVREJbXJMTOMVZJ|JNXTLPVRFJbXJMTOMVZJ|JNXTLPVRGLaVLObXEJWS|JNXTLPVRGLaVLObXHLWS|JNXTLPVRGLbXEJaVAEWS|JNXTLPVRHLaVEJbXJMWS|JNXTLPVSEJUQGLbXLOSL|JNXTLPVSGLSJFMbXLOUQ|JNXTLPVSHLSJENZVAETO|JNXTLPVSHLSJENZVLObX|KNVRFKWSNWbSJMRNKRUN|KNVRFKWTJMaVEJTOLSVF|KNVRFKWTJMTPMVZJENUQ|KNVRGKZVJMUQNUQZMRVM|KNVRGKZVJMWTDGTPMQdZ|KNVRGKZVJMWTDGUQNUQZ|KNVSIMUQEIXTLPbXMRTO|KNVSIMXTEITPMRWTNWUE|KNVSIMXTFKTOKTWPNWbS|KNWSNWbSIMXTLPTOMQUR|KNWSNWbSLPebGLSOLSVO|KNWSNWbSLPebGLUQIMYU|KNWSNWbSLPebJMbWEJfb|KNWSNWbSLPebJMbWHLfb|KNWSNWbSLPebJMUQMRVM|KNWSNWbSLPfbJMbWMQSO|KNWTFKbWJMTPMRVMIRWS|KNWTFKbWLPVSGLTOKTXO|KNWTFKTPBFbWJMfbNRUN|KNWTFKTPBFbWJMUQNRQJ|KNWTFKTPBFbWNRUNJbfW|KNWTFKTPBFUQNRVMIRXT|KNWTFKTPBFVRJMbWMVZJ|KNWTFKTPJMXTMRVMIRbX|KNWTGKbWDGVSLOSLHOTP|KNWTGKbWJMVRMVZJENeb|KNWTGKTPLOVRJMPLMVZJ|KNWTJMTPMRVMIRXTEIUQ|KNWTJMTPMRVMIRXTFKbX|KNWTJMTPMRVMIRXTLOTK|KNWTJMVRMVaKGNbWEJTP|KNWTJMVRMVaKGNbWEJZV|KNWTJMVRMVaKGNeaIMZV|KNWTJMVRMVaKGNTPDGUR|KNWTLPbWNRUNJbfWEJVS|KNWTLPURNUYRPWbSJNRK|KNWTLPVRPWRKGNaTIMTP|KNWTLPVRPWRKGNbSNWaT|KNXTLPVSGKbXDGTOKTXO|KNXTLPVSGKbXDGUQNRSO|KNXTLPVSGKZVHLcZLOSL|KNXTLPVSIMbXMQTOEIUR|KNXTLPVSIMbXMQTOGLUR|KNXTLPVSIMbXMRTOGKeb|KOUQGKWSJNSJENZUDGVR|KOUQGKWSJNSJENZUOTXO|KOUQGKWTLPYUPWbLHOfb|KOUQGKYULPWSJMQJEWbL|KOUQJNVSOVaKFOWTEJTK|KOUQJNVSOVaKGNYUEJZV|KOUQJNVSOVaKGNYUFKZV|KOUQJNWSNWaKFObWEJWT|KOURFKYUJNWTLPVSOMZV|KOURGKYUJNWSNWaTEJUQ|KOURGKYUJNWSNWaTLPUQ|KOURGKZUJNWSNWaTEJea|"+
        "KOURGKZUJNWSNWbSOTXO|KOWTFKTPBFUQJNbWOSVO|KOWTFKTPBFURJMYUMQcY|KOWTGKTPDGbWOTXOLbfW|KOWTGKTPDGUQJNYUEJVR|KOWTGKTPKNPGCLbWFKWS|KOWTJMTKFOaWBFWTGKTP|KOWTJMTKFOaWGKWTBFTP|KOWTJMTKFOaWGKWTBFUQ|KOWTJMTKFOaWGKWTBFUR|KOWTJMTKFOaWLPeaHLWT|KOWTJMTKFObWGKWTBFTP|KOWTJMTKFObWMRUNOSVO|KOWTJMTKFObWMRVMIRUN|KOWTJMTKFObWOSVOLbfW|KOWTJMTKFOUQMRVMIRZV|KOWTJMTKFOUREJbWGKZU|KOWTJMTKFOURGKbWMQWS|KOWTJMTKFOURGKbWMQWT|KOWTJMTKFOURMQbWGKWS|KOWTJMTKFOURMQbWGKWT|KOWTJMTKFOVRMVaREJUQ|KOWTJMTKGNVRMVaKFObW|KOWTOSVOLSTPHLaVLOea|KOWTOSVOLSURJMYUMVaR|LOUQHLYULPVSOVZSIMaV|LOUQHLYULPVSOVZSJMQJ|LOUQJMQJFMWSHLYUMRUN|LOUQJMQJFMWTMRVMIRbW|LOUQJNWSNWbLGPfbEJbW|LOUQJNWSNWbLHOfbKNVR|LOUQJNWSNWbLHOfbKNZU|LOURJMWSEJSLHObWJNfb|LOVRJMaVHLWTLPUQPWbL|LOVRJNWTFJTPJMZVMQcZ|LOWSGLbWKNUQFKZUBFUR|LOWSGLbWKNURNUYRJMRN|LOWSGLbWKNURNUYRJMWT|LOWSGLbWLPSLPGWSJMfb|LOWSGLbWLPSLPGXTHLTP|LOWSHLbWJMUQMRVMIRSN|LOWSHLSNJSXTOXVHIMbW|LOWSHLSNJSXTOXVHIMUR|LOWSHLSNJSXTOXVHIMZV|LOWSHLUQKNZUNWaKFObW|LOWSHLURJNSJEUYRLPbW|LOWSHLXTOXSNJSVHIMbW|LOWTJMbWEJWSAESLGWaT|LOWTJMbWEJWSBESLGWaT|LOWTJMbWHLTPMRUNKRVM|LOWTJMbWMRUNKRVMIRTK|LOWTJMbWMRVMIRUNKRTK|LOWTJMUREJbWJNfbNUZJ|LOWTJMUREJbWMQTPOTXO|LOWTJNbWNRUNKRVMIRTK|LOWTJNbWNRVMIRUNKRTK|LOWTJNVRFJTPJMUQNUQJ|LPUQGLYUDGcYJMQJFMWT|LPUQGLYUDGVRJNZVEJcY|LPUQHLWSKNbWFKZUKOUR|LPUQHLYUKOVRJMQJFVaR|LPUQHLYUKOWTPWaKFObW|LPUQJNWTPWbJENXTHLTP|LPURJNWSNWaTPWbSKNRK|LPVRHLZVLOWTPWbLGPfb|LPVRJMUQMVaREJZUJMQJ|LPVSHLXTKOTKFVaRJMZV|LPVSHLXTKOTKFVZSGKSN|LPVSHLXTKOTKFVZSGKUR|LPWSGLSOKTXOLSVOJMbW|LPWSGLSOLSVOKTXOIMZV|LPWSIMUREISOKTXOGLYU|LPWSJMSOKTXOMQbWEJfb|LPWSJMSOKTXOMQbWEJWT|LPWSJMSOKTXOMQUREJbW|LPWSJMSOKTXOMQUREJRM|LPWSJMSOKTXOMQURFJbW|LPWSJMUQEJZUKNcZNWbS|LPWSJNSJFMaWMQWTPWbS|LPWSJNSJFMXTPWbSHLfb|LPWSJNSJFMXTPWbSMQUR|LPWTPWbSGLSOKTXOLSVO|LPWTPWbSIMfbKNbWMRVM|LPWTPWbSIMfbMQSOKTXO|LPWTPWbSIMUQEIZUBEUR|LPWTPWbSIMUQEIZUHLeb|LPWTPWbSIMUREISOKTXO|LPWTPWbSIMXTKNTPNWaT|LPWTPWbSJMXTMQTPIMSO|LPWTPWbSJNSJENXTAEVR|LPWTPWbSKNaWGLXTFKTP|LPXTKOTKGNVSFKaVHLbX|LPXTKOTKGNVSHLaVLOSL|IMUQEIVSKOaVFKZUJNQJNEWT|IMUQEIVSKOaVFKZUKNURNUQZ|IMUQEIVSKOaVFKZUKNVROVRa|IMUQEIVSKOYUOVZSBEXTFKTP|IMUQEIWSMRVMIRbWAEfbLOSL|IMUQEIWTLPbWMRVMIRTOKTXO|IMUQEIWTMRVMIRZVAEVMEIcZ|IMUQEIYUAEVSKNaVGKeaLPXT|IMUQEIYUKNcYFKWTBEaWLPea|IMUQEIYUKNVRMVaKFOWTGKTP|IMUQEIYUKNVRMVaKFOWTGKZV|IMUQEIYUKNWSNWaTBEURFKZU|IMUQEIYUKNWSNWaTLOTKGNVS|IMUQEIYULOURGLZUDGcYLPWT|IMUQEIZUAEURKNRKGNVRMVaK|IMUQEIZUAEURKNRKGNVRNUQZ|IMUQEIZUAEVRMVaRLOWTJNcZ|IMUQEIZUAEVSLOSLHOURMVaR|IMUQKNVRMVaKGNZUDGURNUQZ|IMUQKNWSNWaTEIZUBEURFKYU|IMUQKNWSNWaTLOTKGNbWHLeb|IMUQKNWSNWaTLOTKGNbWHLWT|IMUQKNWSNWaTLOTKGNbWHLXT|IMUQKNWSNWbSFKYUJNQJNWaT|IMUQKNWTLPYUPWbSNWaTFKTO|IMUQKNWTNSVOLSaVGLVOLSea|IMUQKNXTLPbXEITOGKZUKTXO|IMUQKNXTLPbXEITOMRVMIROK|IMUQKNXTLPVSMRTOGKbXKTXO|IMUQKNXTNSVOLSWNJSQJENYU|IMUQKNXTNSWNJSVOLSQJENbX|IMUQKNYUNSWNJSQJENVOLSbW|IMUQLPWTPWaTEIZUHLTPKNbW|IMUQLPWTPWaTKOTKGNbWHLWT|IMUREIWSKObWFKWTLPSLPWaT|IMUREIWTJNbWNUZJFMfbAEdZ|IMUREIWTLOTPAEbWOTXOKTZU|IMURMQRMJNMIEJWTLPYUPWaT|IMURMQRMJNMINRVMQJYUJNUQ|IMURMQRMJNMINRVMQJYULOUR|IMURMQRMLPWSEISOIRVMKTXO|IMURMQRMLPWSHLSOLSVOKTXO|IMURMQRMLPWTPWbSHLMIJNSJ|IMURMQRMLPWTPWbSJNSJENMI|IMVRMVaRLPZVGLWTPWbSKNRK|IMVSEIWTKOTKFVZSMQXTQZcV|IMVSKNXTMQaVEITPFKWTNWTa|IMVSKNXTMQbXFKaVJMSJMFTP|IMVSKNXTMQTPFKaVKObXGKPG|IMVSKNXTMQTPFKbXJMSJMFUR|IMVSMQWTKNTPNWbSJMfbFKbW|IMWSLPbWGLUQKNVRMOWTPWaR|IMWTMQTPJNbWEJWTAETOLSVO|IMWTMQTPJNbWNRUNKRVMQJaV|IMWTMRUNKRVMJQTPEJbWLOWT|IMXTLOUROXRIHLYULPUQGLZU|IMXTLOUROXRIJNYUHLUQLPcY|IMXTLOUROXRIJNYUHLUQLPWS|IMXTMQTPJNWSNWbSEJfbAEaW|IMXTMQTPKNVSFKbXJMSJMFUR|IMXTMRUNKRVMJQTPEJWTLOTK|IMXTMRUNKRVMJQWSLPTOEJYU|IMXTMRVMJQTPEJbXJNWTAEaV|JMUQEJWTAETOKTXOLSVOGLaW|JMUQEJWTLPTOKTXOMRVMIRbW|JMUQEJZUKOURFKWSLPSLHObW|JMUQFJWSLPZUJNSJMFURHLbW|JMUQFJWSLPZUJNSJMFURHLYU|JMUQFJYULPURHLZUDHWSJNSJ|JMUQLOQJFMWTEJbWBFTPMQWS|JMUQLOQJFMWTMRVMIRbWEJTP|JMUQLOQJFMYUMRUNKRVMIRWT|JMUQMRVMIRWSEJbWAEfbLOSL|"+
        "JMUQMRVMIRWSEJbWBEfbLOSL|JMUQMRVMIRWSEJSOLSZVSZdE|JMUQMRVMIRWSLOSLHObWEJWT|JMUQMRVMIRWTEJbWAETPEIWT|JMUQMRVMIRWTEJbWLOZUJNdZ|JMUQMRVMIRWTEJZVAEVMEIcZ|JMUQMRVMIRWTKNbWFKTPLOZU|JMUQMRVMIRWTLOTPEJbWOTXO|JMUREJWSKObWAEWTLPTKGWaT|JMUREJWSKObWFKYUMQebJMWT|JMUREJWSKObWGKWTLPSLPWaT|JMUREJWSKORNAEbWFKZUKRUN|JMUREJWSKORNAEbWLPSLJbfW|JMUREJWTJNbWNUZJFMfbMQdZ|JMUREJWTLObWJNfbNUZJFMdZ|JMUREJWTLObWJNTPNUZJFMWT|JMUREJWTLObWMQTPJNWTNUYR|JMUREJWTLObWMQWSJMSLGWaT|JMUREJWTLPTOKTXOMQRMIRVM|JMURFJWSKOaWMQWTJMTKGWbS|JMURFJWSKObWMQebJMYUGKWT|JMURKNRKGNVSEJSOLSaVCGVO|JMURKNRKGNVSEJSOLSaVDGVO|JMURKNRKGNWTMRVMIRZUEJbW|JMURKOWTLPTKGUZJENXTPWbJ|JMURLOWTEJbWAEfbMQTPHLWS|JMURLOWTEJbWAEfbMQTPJNWT|JMURLOWTEJbWAEfbMQTPJNYU|JMURLOWTEJbWAEfbMQYUJNRM|JMURLOWTEJbWJNTPNUZJFMWT|JMURLOWTEJbWMQRMIRVMGLMI|JMURLOWTEJbWMQRMIRVMGLTP|JMURLOWTEJbWMQTPOTXOKTRM|JMURLOWTEJbWMQWSJMSLGWaT|JMURLOWTGLTPCGbWOTXOLbfW|JMURMQVSKOaVEJWTLPTKGWbS|JMVSEJWTLPTOKTXOGKUQKTbX|JMVSFJaVMQeaJNSJENURNUYR|JMVSFJWTMQSNKRUNJSTOSVZS|JMVSFJWTMQTOKTXOIMSNLSNW|JMVSKOaVFKUREJWTKNTKNWbS|JMVSKOaVMQeaEJWTJMTKGWaT|JMVSKOUQOVQJENaKFOYUGKWT|JMVSLPSOKTXOMQUREJaVGKea|JMVSMQaVIMUREIWTLPSNPWbS|JMVSMQaVIMWTMRUNKaeVEJYU|JMVSMQUREJRNKRSOLSWEAJZU|JMVSMQURKNRKFVaREJeaLOaV|JMVSMQURKOaVEJWTGKSNJSRM|JMVSMQURKOaVEJWTJMTKGWbS|JMVSMQURKOaVFKWTKNTKNWbS|JMVSMQURKOaVGKWTLPSLPGTO|JMVSMQURKOSNOSNKGUWNCGYR|JMVSMQURLPSOKTXOEJZUQZcV|JMVSMQWTEJTOKTXOJMURMVaR|JMVSMQWTKOTKFVaRLObWHLea|JMVSMQWTKOTKFVZSQZdUIMbW|JMWSEJaWKNeaMQSOLSVOJMWS|JMWSEJaWKNXTMRVMIRbXGKZV|JMWSEJaWMQeaJMWTMRUNKRVM|JMWSEJbWAEfbMRUNKRVMJQXT|JMWSEJbWAEWTMRUNKRVMJQTP|JMWSEJbWKOUQFKZUJNSJMFWS|JMWSEJbWKOUQGKZULPSLPGXT|JMWSEJSOKTXOLSVOMQbWAEfb|JMWSEJSOKTXOLSVOMQURGLRN|JMWSEJSOLSVOKTXOAEURMVaR|JMWSEJSOLSVOKTXOBEUQGLaV|JMWSEJSOLSVOKTXOBEZVMRVM|JMWSEJSOLSVOKTXOGLaWLSWE|JMWSEJSOLSVOKTXOMQURJMaV|JMWSEJURKOaWFKWTKNTKNWbS|JMWSEJURKOYUMQcYJMbWFKRN|JMWSFJbWMQWTJNSJENTOLSVF|JMWSFJbWMQWTJNSJENTPNRUN|JMWSKOaWFKUQMRVMIRWTOVZS|JMWSKOaWFKWTEJbWBFUQMRVM|JMWSKOaWFKWTMRUNKaTKGWbS|JMWSKOaWGKWTEJTPDGURMQZU|JMWSKOaWGKWTLPSLPGTOKTXO|JMWSKOaWMQeaEJWTJMTKGWaT|JMWSKOaWMQUREJWTJMTKGWbS|JMWSKOaWMQWTEJTKGWbSLPfb|JMWSKOaWMQWTEJTKGWbSLPUR|JMWSKOaWMQWTEJTKGWbSLPVR|JMWSKOaWMQWTFKTPEJURJMbW|JMWSKOaWMQWTGKTPDGUREJYU|JMWSKOaWMQWTGKURLPSLPGTO|JMWSKOaWMQWTLPTKGWbSEJfb|JMWSKOaWMQWTLPTKGWbSEJUR|JMWSKObWEJUQFKZUJNSJMFUR|JMWSKObWEJUQGKZULPSLPGXT|JMWSKObWEJUQMRVMOVaRJNRK|JMWSKObWEJURFKWTLPSLPWaT|JMWSKObWEJURFKYUMQcYJMRN|JMWSKObWFKUQBFQJFMfbMQYU|JMWSKObWFKUQBFQJFMYUMQfb|JMWSKObWFKUQBFQJFMYUMRUN|JMWSKObWFKUQEJZUJNSJMFUR|JMWSKObWFKUQMRVMIRSNRUYR|JMWSKObWFKUQMRVMIRSNRVaR|JMWSKObWFKUREJWTLPSLPWaT|JMWSKObWFKUREJYUMQcYJMRN|JMWSKObWFKUREJYUMQcYJNSJ|JMWSKObWFKUREJZUMQRMIRVF|JMWSKObWFKWTLPSLPWaTGWea|JMWSKObWGKUQLPSLPGQJFMWS|JMWSKObWMQWTEJTKGWaTLPea|JMWSKObWMQWTLPTKGWaTPWeb|JMWSKOUQEJZUGKaWKNVRMVSZ|JMWSKOUQGKQJEWaTAETPDGYU|JMWSKOUQGKQJEWaTAEYUEJUR|JMWSKOUQGKQJEWaTIMTPCGVS|JMWSKOUQGKQJEWaTIMTPDGda|JMWSKOUQGKQJEWaTIMZUOSVO|JMWSKOUQGKQJEWaTLPYUPWbL|JMWSKOUQGKQJEWbSIMaWAEWT|JMWSKOUQGKQJEWbSIMaWAEYU|JMWSKOUQGKQJEWbSIMaWMQWT|JMWSKOUQGKQJEWbSIMYUMQaW|JMWSKOUREJaWFKWTKNTKNWbS|JMWSLOSLHOUREJaWAEWSGLbW|JMWSLOSLHOUREJaWJNWSNWbL|JMWSLOSLHOVRMVZLGPXTPWbS|JMWSLPSOKTXOMQaWEJWTPWbS|JMWSLPSOKTXOMQbWEJfbJMbX|JMWSLPSOKTXOMQbWEJfbJMVR|JMWSLPSOKTXOMQbWEJWTPWaT|JMWSLPSOKTXOMQUREJaWJMbX|JMWSLPSOKTXOMQUREJbWJMfb|JMWSLPSOKTXOMQUREJbWJMYU|JMWSLPSOKTXOMQUREJRMIRVM|JMWSMRUNKRVMIRbWLOSLHOfb|JMWSMRUNKRVMIRbWLOSLHOWT|JMWSMRUNKRVMIRZUFKUNKRXT|JMWTEJbWAETPMQWSLOSLHOfb|JMWTEJbWJNfbMRVMIRTPAEUQ|JMWTEJbWJNURNUZJFMVSLOSL|JMWTEJbWLOfbMQTPOTXOKTUR|JMWTEJbWMQURLOTPJNWTNUYR|JMWTEJbWMQWSAESOLSVOGLaV|JMWTEJbWMQWSLPSOPWaTAETP|JMWTEJTOKTXOLSVOMQbWGLWS|JMWTEJTOKTXOLSVOMQbWJMfb|JMWTEJTOKTXOLSVOMQbWJNUR|JMWTEJTOLSVOKTXOBEURMVaR|JMWTEJTOLSVOKTXOBEZVMRVM|JMWTEJTOLSVOKTXOMQbWAEfb|JMWTEJTPAEURKOaWOTXOLSWN|JMWTEJTPLObWOTXOKTWSTXUR|JMWTEJTPMQbWJNVSFJaVJMSJ|JMWTEJTPMQbWLOWSAESLHOfb|"+
        "JMWTEJTPMQXTLObXJNURNUYR|JMWTEJUQMRVMIRTPLObWJNWT|JMWTFJUQLPZUPWaTCFURKNRK|JMWTFJUQLPZUPWaTCFVSMRUN|JMWTFJUQLPZUPWaTKNURNUYR|JMWTKNaWNSWNMRVMIKeaEJTP|JMWTKNaWNSWNMRVMIKTPEJUQ|JMWTKNTOLSVOEJbWGLfbLSUR|JMWTKNTOLSVOEJURNUYRMVZS|JMWTKNTPMQXTEJaWAEWSNWTa|JMWTKNVRMVaKGNbWEJTPIMPG|JMWTLObWEJfbAETPMRVMJQWT|JMWTLObWEJTPMQURJNfbNUYR|JMWTLObWEJTPMQWSAESLHOfb|JMWTLObWEJWSAESLGWaTHLTP|JMWTLObWEJWSAESLGWaTHLUR|JMWTLObWEJWSMQSLGWaTJNUR|JMWTLObWMQWSEJSLGWaTHLUR|JMWTLObWMRUNKRVMIRTKGNZU|JMWTLObWMRVMIRUNKRTKGNeb|JMWTLOUREJbWJNTPNUZJFMWT|JMWTLPTOKTXOMQbWFJWTPWaT|JMWTLPTOKTXOMQUREJRMIRVM|JMWTLPUQPWQJENbJFMfbHLYU|JMWTLPUQPWQJENbJFMXTAEfb|JMWTMQTPEJXTJMTOLSVOKTPW|JMWTMRUNKRVMIRTOLSZURVaR|JMWTMRUNKRVMIRZUFKUNKRTP|JMWTMRVMIRUNKRaWFKWSRVSN|JMWTMRVMIRUNKRTOLSZURVaR|JMWTMRVMIRUNKRTPEJbWAEWT|JMXTLObXEJfbMQTPJNURNUYR|JMXTLPbXMQTOKTXOGKWTPWaT|JMXTLPbXMQVSKNSJENURNUYR|JMXTLPUQGLQJFMbXEJVSMQeb|JMXTLPUQHLQJFMVSMQSNKRTO|JMXTLPUQMRVMIRZURVaRKNRK|JMXTLPVSHLbXDHebKOTDMRUN|JMXTLPVSMQaVEJeaJNSJFMVS|JNUQEJWSNWbSKOZUJNSJFMQJ|JNUQEJWTAETPLObWNSWNKRVM|JNUQEJWTAETPLOVRNUYRJNZV|JNUQEJWTLPbWGLZULOURNUQZ|JNUQEJWTNRVMIRbWLOfbAETP|JNUQEJYUAEVRIMRINSWNKYbW|JNUQEJZUAEWTLOVROSaWGLTP|JNUQEJZUAEWTLPQMJSaVPWVO|JNUQEJZULPURNUQZIMYUMQWS|JNUQEJZULPVRGLRMIRWTPWbS|JNUQKOWTGKQMIRVMEIZVIRVM|JNUQKOWTNRTKGNVMIRbWFKWT|JNUQLOWSNWbLHOYUOTXOKTUR|JNUQLOWTEJbWAETPNRVMIRWT|JNUQLOWTEJZUNScZKNTRBEVO|JNUQLOWTEJZUNSVRJNcZSWbL|JNUQLOZUEJWTNSVRJNTPAEcZ|JNUQLPVSEJSOKTXOAEWSNWbS|JNUQNRVMIRWSEJbWAEfbLOSL|JNUQNRVMIRWSEJbWBEfbLOSL|JNUQNRVMIRWSEJbWBEZULOSL|JNUQNRVMIRWSEJbWLOSLHOWS|JNUQNRVMIRWSEJSNJSZVSZcM|JNUQNRVMIRWSEJSOLSaVRadE|JNUQNRVMIRWSLOSLHObWGLWT|JNUQNRVMIRWSLOSLHObWGLZU|JNUQNRVMIRWSLOSLHObWKNfb|JNUQNRVMIRWSLOSLHObWKNWT|JNUQNRVMIRWTEJbWLOaVRaeV|JNUQNRVMIRWTEJbWLOfbAEaV|JNUQNRVMIRWTEJbWLOTPAEWT|JNUQNRVMIRWTEJbWLOTPJNWT|JNUQNRVMIRWTEJbWLOTPOTXO|JNUQNRVMIRWTEJbWLOZVBEVM|JNUQNRVMIRWTEJTPAEbWEIfb|JNUQNRVMIRWTEJTPAEbWJNZU|JNUQNRVMIRWTEJTPLObWJNZU|JNUQNRVMIRWTEJZVAEVMEIcZ|JNUQNRVMIRWTEJZVJMQJFMVS|JNUQNRVMIRWTKNTPFKXTLObX|JNUQNRVMIRWTKNZUFKcZLObW|JNUQNRVMIRWTLObWEJfbJNTP|JNUQNRVMIRWTLObWEJTPAEWT|JNUQNRVMIRWTLObWEJTPJNWS|JNUQNRVMIRWTLObWEJTPJNWT|JNUQNRVMIRWTLObWEJTPOTXO|JNUQNRVMIRWTLObWEJZVJMQJ|JNUQNRVMIRWTLObWKNTKFOWT|JNUQNRVMIRWTLOTPEJbWJNWT|JNUQNRVMIRWTLOTPHLbWEJfb|JNUQNRVMIRWTLOTPHLbWEJWT|JNUQNRVMIRWTLOZUHLUNKRTK|JNUQNRVMIRZUKNdZLOWTFJTK|JNUQNRVMIRZUKNdZLOZVEIVM|JNUQNRVMIRZUKNWTFKTPLObW|JNUQNRVMIRZULOUNKRdZFKZU|JNUQNRVMIRZULOUNKRWTHLTK|JNUQNRVMIRZVEIVMIRWTKNbW|JNUQNRVMIRZVEIVMIRWTKNdZ|JNUQNSWNKRVMIRZVEIVMIRcZ|JNURNUYREJWSKObWJMWTMQTK|JNURNUYREJWTAETPJNRMIRVM|JNURNUYREJWTJMTOLSVOKTXO|JNURNUYREJWTJMTPLObWOTXO|JNURNUYREJWTJNRMIRVMAEMI|JNURNUYREJWTJNRMIRVMAETP|JNURNUYREJWTLObWJMfbMQTP|JNURNUYREJWTLObWJMTPAEfb|JNURNUYREJWTLOTPAEbWJNWT|JNURNUYREJWTLOTPJMbWOTXO|JNURNUYREJWTLOTPJNbWNUZQ|JNURNUYREJWTLPTOKTXOJMVS|JNURNUZQEJWSKObWGKYUBEeb|JNURNUZQEJWSKOYUJNSJFMQJ|JNURNUZQKNVRNUQZEJaVIMYU|JNURNUZQKNVRNUQZFKaVEJWS|JNURNUZQLOWSGLYUOTXOKTbX|JNURNUZQLPWSPTXOKTYUTWaT|JNVREJaVBEWTJMTPLOUQNUYR|JNVREJaVJMUQNUQJFMZJBFVS|JNVREJaVJMXTMQbXLOfbGLTP|JNVREJaVJMXTMQTPFJWTJMbX|JNVREJaVJMXTMQTPFJWTLOda|JNVREJaVJMXTMQTPLOWSNWbL|JNVREJaVLOWTBETPJMUQNUYR|JNVREJaVLOWTBEUQNUYRJMQJ|JNVREJaVLOWTHLTPDHUQNUYR|JNVREJaVLOWTJMUQNUQJFMZJ|JNVREJaVLPeaGLVSLOSLPGXT|JNVREJaVLPVSGLZVLOSLPGea|JNVREJaVLPVSGLZVLOSLPGUQ|JNVREJaVLPVSGLZVLOSLPGVS|JNVREJaVLPXTHLbXLOWSNWTa|JNVREJWTBEbWJMTPMVZJFMWT|JNVREJWTBEZVJMbWMQcZLOTP|JNVREJWTJMaWMVZJFMWSLOSL|JNVREJWTJMaWMVZJFMWSMQTO|JNVREJWTJMaWMVZJFMWSMRUN|JNVREJWTJMUQMVZJFMQJBEYU|JNVREJWTJMUQMVZJFMQJBFYU|JNVREJWTJMUQNUQJFMZJBEJF|JNVREJWTJMUQNUQJFMZJBFYU|JNVREJWTLObWBETPJMWTMVZL|JNVREJWTLObWJMUQMVZJFMQJ|JNVREJXTBETOLSaVJMVOKaRB|JNVREJXTJMUQNUQJFMZJBEaV|JNVREJXTLOTPBEaVHLWSNWbS|JNVREJXTLOTPBEaVJMVSMVSL|JNVREJXTLOTPJMWSNWbLMVaR|JNVREJXTLOTPOTbXJMXOMVZJ|JNVREJXTLOTPOTZVJMUQNUQZ|JNVREJXTLPaVHLbXLOWSNWTa|JNVREJXTLPaVHLbXLOWSPWSb|"+
        "JNVREJXTLPbXGLZVLOUQNUQZ|JNVREJXTLPbXHLaVJMWSNWTa|JNVREJXTLPbXHLZVJMUQNUQZ|JNVREJXTLPZVGLbXJMUQNUQZ|JNVREJXTLPZVJMUQNUQZMRVM|JNVREJZVJMUQNUQJFMYRAEWS|JNVREJZVJMUQNUQZAEVSLOSL|JNVREJZVJMUQNUQZAEWSEJaW|JNVREJZVJMUQNUQZAEWSEJSO|JNVREJZVJMUQNUQZAEWSEJYU|JNVREJZVJMUQNUQZAEWTEJbW|JNVREJZVJMUQNUQZAEWTEJTP|JNVREJZVJMUQNUQZAEWTMRVM|JNVREJZVJMUQNUQZAEXTLObX|JNVREJZVJMUQNUQZAEXTMQTO|JNVREJZVJMUQNUQZAEYUMQWS|JNVREJZVJMUQNUQZAEYUMRUN|JNVREJZVJMUQNUQZFJWSAEYU|JNVREJZVJMUQNUQZFJWSBFYU|JNVREJZVJMUQNUQZKNVRNUZJ|JNVREJZVJMUQNUQZKNVSFJXT|JNVREJZVJMUQNUQZKNWSNWbS|JNVREJZVJMUQNUQZKNXTMQTO|JNVREJZVJMUQNUQZKNXTMRVM|JNVREJZVJMUQNUQZLOWSGLbW|JNVREJZVJMUQNUQZLOWSGLYU|JNVREJZVJMUQNUQZLOWSHLYU|JNVREJZVJMUQNUQZLOWTAEbW|JNVREJZVJMUQNUQZMQWSAEYU|JNVREJZVJMUQNUQZMQWTFJTO|JNVREJZVJMUQNUQZMQWTKNTO|JNVREJZVJMUQNUQZMRVMIRWS|JNVREJZVJMUQNUQZMRVMIRXT|JNVREJZVLOUQNUQZAEWSGLYU|JNVREJZVLOWTNScZIMRIKNTR|JNVREJZVLOWTNSUQSZdUAEcZ|JNVREJZVLOWTNSUQSZdUAETP|JNVREJZVLOWTNSUQSZdUIMRI|JNVREJZVLPUQNUQZHLWSKOYU|JNVRFJaVJMUQNUQJENYRNUZQ|JNVRFJaVJMWTMQTOLSVFBKbW|JNVRFJaVJMWTMQTOLSVFBKXT|JNVRFJaVLPXTGLbXLOWSNWTa|JNVRFJWSNWbSJMRNKRUNBFXT|JNVRFJWSNWbSJMSNMVaRBFXT|JNVRFJWTJMaVMQTOLSVFBKbW|JNVRFJWTJMaVMQTOLSVFBKXT|JNVRFJWTJMTPMVZJENUQAEbW|JNVRFJWTJMTPMVZJENUQLObW|JNVRFJWTJMZVMQcZLOTPBFbW|JNVRFJWTJMZVMQcZLOTPCFbW|JNVRFJWTJMZVMQcZLOTPGLPG|JNVRFJWTJMZVMQcZLOTPHLbW|JNVRFJWTLObWJMTPMVZJENUQ|JNVRFJWTLOTPJMbWMVZJENWT|JNVRFJWTLOZVNScZIMRIKNTR|JNVRFJWTLOZVNSUQSZcVJMQJ|JNVRFJWTLOZVNSUQSZdUIMRI|JNVRFJWTLOZVNSUQSZdUJNcZ|JNVRFJWTLOZVNSUQSZdUKNTK|JNVRFJZVJMUQNUQZEJWTLObW|JNVRFJZVJMUQNUQZMQWSKOaW|JNVRFJZVJMUQNUQZMRVMIRWS|JNVRFJZVJMUQNUQZMRVMIRWT|JNVRFJZVJMUQNUQZMRVMIRXT|JNVRFJZVJMUQNUQZMRVMIRZU|JNVRFJZVJMWTMQcZLObWHLTP|JNVRFJZVJMWTMQcZLOTPBFbW|JNVRFJZVJMWTMQcZLOTPGLPG|JNVRLOWTFJbWJMTPMVZJENUQ|JNVRLOZVEJWTNSUQSZdUAETP|JNVRLPWTPWbJFVaREJZVHLfb|JNVRLPXTGLbXEJaVLOWSPWSb|JNVRLPZVGLRMIRVMEIcZIRWT|JNVRLPZVHLUQNUQZIMWSKOSN|JNVRLPZVHLUQNUQZIMWSMQYU|JNVRLPZVHLUQNUQZIMWTPWbS|JNVRLPZVHLUQNUQZIMYUMQWS|JNVRLPZVHLVSDHSJFVaREJea|JNVRLPZVHLVSDHSJFVaREJUQ|JNVSEJaVAEVRLPRMIRSOKaeM|JNVSEJaVKOdaOTXOGKbXKTWG|JNVSEJaVKOeaFKURNUYRIMRI|JNVSEJaVKOeaGKURNUYRLPSL|JNVSEJaVKOUQFKZUJMQJNEUR|JNVSEJaVKOUQFKZUJMQJNEWT|JNVSEJaVKOUQGKZUBEURNUQZ|JNVSEJaVKOUQGKZUBEURNUYR|JNVSEJaVKOUQGKZUDGURNUQZ|JNVSEJaVKOUQGKZUDGURNUYR|JNVSEJaVKOUQGKZULPSLPGVR|JNVSEJaVKOURNUYRJMeaAEWT|JNVSEJaVKOURNUYRJMZUGKSN|JNVSEJaVKOURNUYRJMZUMQWT|JNVSEJaVKOURNUZQGKYUBEea|JNVSEJaVKOURNUZQGKYULPSL|JNVSEJaVLPUQGLZUKOURNUQZ|JNVSEJaVLPVRGLZVLOSLPGUQ|JNVSEJUQAEZVIMdZKOZUOTXO|JNVSEJUQAEZVIMYUEIURNUQZ|JNVSEJUQKOYUOVaKFOWTGKZV|JNVSEJURNUYRKORNOVaRJSWN|JNVSEJZVKOUQGKYUBEcYDGUR|JNVSEJZVKOUQGKYUBEURNUQZ|JNVSEJZVKOUQGKYUDGURNUQZ|JNVSEJZVKOUQNRVMIRXTOXSO|JNVSEJZVKOURNUYRJMcZGKWT|JNVSEJZVKOURNUYRJMcZMQZU|JNVSFJaVKOUQGKZUDGURNUQZ|JNVSFJaVKOURNUYRBFWTFKSN|JNVSFJaVKOURNUYRJMRNMQWT|JNVSFJaVKOURNUYRJMZUEJWT|JNVSFJaVKOURNUYRJMZUGKWT|JNVSFJaVLPXTCFUQGLZULOSL|JNVSFJZVKOUQGKYULPSLPGXT|JNVSFJZVKOURNUYRJMRNEJNE|JNVSFJZVKOURNUYRJMRNMQcZ|JNVSLOSJENUQAEWSNWbLHOfb|JNVSLOSJFMWTMQbWEJTPJMWT|JNVSLOSJFMWTMRUNKRTKGNXT|JNVSLOSLHOUQNRWTIMQJFMbW|JNVSLOSLHOURNUYREJaVJNWS|JNVSLPSJFMWSGLaVLOSLPGXT|JNVSLPSJFMWSHLaVKObWMQUR|JNVSLPSJFMWSHLUQEJaVKObW|JNVSLPSJFMWSHLUQEJaVKOZU|JNVSLPSJFMWTPWbSEJfbMQSO|JNVSLPSJFMWTPWbSEJXTMQSO|JNWSNWaTEJUQAEZUJNURNUQZ|JNWSNWaTIMTPLOUQEIQJFMbW|JNWSNWaTIMUREITPLObWOTXO|JNWSNWaTKNbWFKTPNRVMIRUN|JNWSNWaTKNbWFKVREJTPLOZV|JNWSNWaTLOdaEJbWJMUQMRVM|JNWSNWaTLOeaFJbWJNURNUYR|JNWSNWbSEJfbKObWGKURLPSL|JNWSNWbSEJUQKOZUJNSJFMQJ|JNWSNWbSIMaWMQWTKNSJENfb|JNWSNWbSIMebMQSOLSVOKTXO|JNWSNWbSIMfbMQbWEIURAEZU|JNWSNWbSLOSLHOfbEJVRJNUQ|JNWTEJaWBETPNRVMJQUREJXT|JNWTEJaWLOdaGLTPAEPGCLVS|JNWTEJaWLPeaAEVRJMUQMeQM|JNWTEJaWLPeaAEVRJMZVEJUQ|JNWTEJbWAEUQNSVOLbfWHLTP|JNWTEJbWAEVRLPaVGLWSPWSb|JNWTEJbWJMebMRVMIRTPAEUQ|JNWTEJbWJMfbMQTOKTXOLSVO|JNWTEJbWJMfbMRVMIRTPAEUQ|JNWTEJbWJMfbMRVMIRTPAEWT|JNWTEJbWJMfbMRVMIRTPLOWT|"+
        "JNWTEJbWJMTPMQURNUYRAEfb|JNWTEJbWJMTPNRUNKRWSMQVM|JNWTEJbWJMTPNRUNKRZUFKUN|JNWTEJbWJMUQNRQJFMfbLOZU|JNWTEJbWJMUQNRQJFMfbMQVM|JNWTEJbWJMURNUZJFMfbAEdZ|JNWTEJTOKTXOLSVOAEURNUYR|JNWTEJTOKTXOLSVOIMOKFOUR|JNWTEJTOLSVOKTXOAEURNUYR|JNWTEJTPBEbWJMUQNRQJFMWT|JNWTEJTPJMbWBEUQNRQJFMWT|JNWTEJTPJMbWMQURNUYRAEfb|JNWTEJTPJMbWMQURNUYRLOfb|JNWTEJTPJMbWMQWTLOURNUYR|JNWTEJTPJMbWMRVMIRfbLOWT|JNWTEJTPJMbWNRUNKRWSAEfb|JNWTEJTPJMbWNRUNKRWSMQVM|JNWTEJTPJMbWNRUNKRZUFKUN|JNWTEJTPJMbWNRUNKRZULOUN|JNWTEJTPJMUQNRQJFMbWAEWT|JNWTEJTPJMUQNRQJFMbWBFWT|JNWTEJTPJMUQNRQJFMbWMQVM|JNWTEJTPJMVSNWbSMQfbFJbW|JNWTEJTPJMXTMQTOKTPWGKbX|JNWTEJTPJMXTMQTOLSVOKTPW|JNWTEJTPJMXTMRVMIRZVAEVM|JNWTEJTPJMXTNRUNKRTOLSVO|JNWTEJTPJMXTNRUNKRZUFKUN|JNWTEJTPLOVRBEbWJMWTMVZJ|JNWTEJTPLOVRBEbWJMWTMVZL|JNWTEJTPLOVRJMUQMVZJFMQJ|JNWTEJUQAETPLObWNSWNKRVM|JNWTEJURNUZQAEYUJNVREJTP|JNWTEJVRBEbWJMTPMVZJFMUQ|JNWTEJVRJMUQMVZJFMQJBEYU|JNWTEJVRJMUQMVZJFMQJKOTK|JNWTEJVRJMUQNUQJFMZJBEYU|JNWTEJVRLObWBEaVJMVSMVSL|JNWTFJTPBFbWJMWTNRUNKRVS|JNWTFJTPBFVRJMZVMQcZLObW|JNWTFJTPJMXTMRVMIRbXLOZV|JNWTFJUQBFTPLObWOTXOKTfb|JNWTFJVRJMZVMQcZLOTPCFbW|JNWTLObWHLTPNRUNKRVMIRfb|JNWTLObWHLTPNRUNKRVMIRWT|JNWTLObWHLUQNRVMIRTPEJWT|JNWTLObWHLUQNSWNKRVMIRTK|JNWTLObWNRUNKRVMIRTKGNfb|JNWTLObWNRUNKRVMIRTKGNXT|JNWTLOVREJaVBEbWJMUQNUQJ|JNWTLOVREJbWJMUQNUQJFMZJ|JNWTLOVREJTPJMUQMVZJFMQJ|JNWTLOVREJTPJMUQNUQJFMZJ|JNWTLOVRFJbWJMfbMVZJENUR|JNWTLOVRFJbWJMTPMVZJENUQ|JNWTLPUQPWbJENXTAEfbHLTP|JNWTLPUQPWbJENXTAETPHLYU|JNWTLPUQPWbJENXTAETPKOfb|JNWTLPUQPWbJENXTAEYUHLTP|JNWTLPUQPWbJENXTHLTPAEfb|JNWTLPUQPWbJENXTHLTPAEYU|JNWTLPUQPWbJENXTHLTPFJfb|JNWTLPUQPWbJENXTHLTPLOfb|JNWTLPUQPWbJFMQJENYUAEVR|JNWTLPUQPWbJFMQJENYUHLfb|JNWTNRUNKRVMIRaWFKdaLOaV|JNWTNRUNKRVMIRaWGKTPLOPL|JNWTNRUNKRVMIRaWLOTKFOWT|JNWTNRUNKRVMIRTOLSZURVaR|JNWTNRUNKRVMIRTPEJbWAEfb|JNWTNRUNKRVMIRTPEJbWAEWT|JNWTNRUNKRVMIRTPEJZUJNdZ|JNWTNRUNKRVMIRTPLObWEJWT|JNWTNRUNKRVMIRTPLObWHLWT|JNWTNRVMIRUNKRTOLSZURVaR|JNWTNRVMIRUNKRTPFKbWEIWS|JNWTNRVMIRUNKRZUFKUNKRaW|JNWTNSVOLSaVKOTKFObWSbfW|JNXTEJbXJMVSMQSJFMTPAEfb|JNXTEJTOLSVOKTWPAEaVHLbX|JNXTEJTPJMWSNWbSMQfbAEaW|JNXTEJTPJMWSNWbSMQSOKTPW|JNXTEJTPLOUQOTZUTXVRHLaV|JNXTLObXHLfbLPVSOVZJENTO|JNXTLObXHLTPNRUNKRVMIRfb|JNXTLObXHLTPNRUNKRVMIRWS|JNXTLObXHLTPNRUNKRVMIRWT|JNXTLObXHLUQNRVMIRTPEJWT|JNXTLObXHLUQNSWNKRTKGNVM|JNXTLObXHLUQNSWNKRVMIRTK|JNXTLObXNRUNKRVMIRTKFOWS|JNXTLObXNRUNKRVMIRTKGNfb|JNXTLObXNRUNKRVMIRTKGNXT|JNXTLObXNRVMIRUNKRTKGNfb|JNXTLOTPOTVSTXSJENWSNWbS|JNXTLPbXGLVRLOaVHLWSNWTa|JNXTLPbXGLVRLOaVHLWSPWSb|JNXTLPbXGLVSDGSJENURNUYR|JNXTLPbXGLVSDGSJFMUQBFQJ|JNXTLPbXGLVSLOSLPGTOKTXO|JNXTLPbXHLVSDHSJENUQAEZU|JNXTLPbXHLVSDHSJENURNUYR|JNXTLPbXHLVSDHSJFMURMVaR|JNXTLPbXNRUNKRVMIRebEJZU|JNXTLPbXNRUNKRVMIRTOEJeb|JNXTLPbXNRUNKRVMIRZVEIVM|JNXTLPbXNRUNKRVMIRZVEJVM|JNXTLPbXNRVMIRUNKRZVEIVM|JNXTLPUQEJVSAEbXIMZUEIaV|JNXTLPUQEJZUGLbXLOURNUQZ|JNXTLPUQEJZUGLVRLObXHLaV|JNXTLPUQEJZUHLVSBEaVDHbX|JNXTLPUQFJVSGLbXLOSLPGTO|JNXTLPUQGLbXLOZUHLVRIMQS|JNXTLPUQGLYULObXHLVSOVZJ|JNXTLPUQGLZUDGbXEJURNUQZ|JNXTLPUQGLZULObXEJURNUQZ|JNXTLPUQGLZULObXHLURNUQZ|JNXTLPUQGLZULObXHLURNUYR|JNXTLPUQGLZULObXHLVRIMQS|JNXTLPUQHLVSDHSJFMQJENZU|JNXTLPUQHLVSEJbXDHYUIMZV|JNXTLPUQHLZULObXNSWNPWaT|JNXTLPUQNRVMIRaVRaeVKNVS|JNXTLPUQNRVMIRZUEIUNKRQM|JNXTLPUQNRVMIRZUKNTOGKbX|JNXTLPUQNRVMIRZUKNTOGLWS|JNXTLPUQNRVMIRZURVaRKNRK|JNXTLPVREJaVHLbXLOWSPWSb|JNXTLPVREJbXGLZVLOUQNUQZ|JNXTLPVREJbXHLaVLOWSPWSL|JNXTLPVREJbXJMTOMVZJKTXO|JNXTLPVRFJbXJMTOMVZJENOF|JNXTLPVRGLaVLObXEJWSPWSb|JNXTLPVRGLaVLObXHLWSPWSb|JNXTLPVRGLbXEJaVAEWSNWTa|JNXTLPVRHLaVEJbXJMWSNWTa|JNXTLPVSEJUQGLbXLOSLPGTP|JNXTLPVSGLSJFMbXLOUQBFQJ|JNXTLPVSHLSJENZVAETOLQWT|JNXTLPVSHLSJENZVLObXFJUQ|KNVRFKWSNWbSJMRNKRUNLOSL|KNVRFKWTJMaVEJTOLSVFBKda|KNVRFKWTJMTPMVZJENUQLObW|KNVRGKZVJMUQNUQZMRVMIRWS|KNVRGKZVJMUQNUQZMRVMIRWT|KNVRGKZVJMWTDGTPMQdZLObW|KNVRGKZVJMWTDGUQNUQZMRVM|KNVSIMUQEIXTLPbXMRTOGKeb|KNVSIMXTEITPMRWTNWUEAJbS|KNVSIMXTFKTOKTWPNWbSMQUR|KNWSNWbSIMXTLPTOMQUREIRM|"+
        "KNWSNWbSIMXTLPTOMQUREIRN|KNWSNWbSLPebGLSOLSVOPTOK|KNWSNWbSLPebGLUQIMYUFKUR|KNWSNWbSLPebJMbWEJfbMQXT|KNWSNWbSLPebJMbWHLfbMQSO|KNWSNWbSLPebJMUQMRVMIRbW|KNWSNWbSLPfbJMbWMQSOEJWT|KNWTFKbWJMTPMRVMIRWSNWUN|KNWTFKbWLPVSGLTOKTXOPTWG|KNWTFKTPBFbWJMfbNRUNKRWT|KNWTFKTPBFbWJMUQNRQJENVM|KNWTFKTPBFbWNRUNJbfWIMYU|KNWTFKTPBFUQNRVMIRXTJMQJ|KNWTFKTPBFVRJMbWMVZJENUQ|KNWTFKTPJMXTMRVMIRbXEIaW|KNWTGKbWDGVSLOSLHOTPNRUN|KNWTGKbWJMVRMVZJENebAEUQ|KNWTGKTPLOVRJMPLMVZJFMLS|KNWTJMTPMRVMIRXTEIUQAEZU|KNWTJMTPMRVMIRXTFKbXLOZV|KNWTJMTPMRVMIRXTLOTKFObX|KNWTJMVRMVaKGNbWEJTPAEPG|KNWTJMVRMVaKGNbWEJZVAETP|KNWTJMVRMVaKGNeaIMZVEIUR|KNWTJMVRMVaKGNTPDGURNUYR|KNWTLPbWNRUNJbfWEJVSJMYU|KNWTLPURNUYRPWbSJNRKGWaT|KNWTLPVRPWRKGNaTIMTPFKXT|KNWTLPVRPWRKGNbSNWaTJNTO|KNXTLPVSGKbXDGTOKTXOGKfb|KNXTLPVSGKbXDGUQNRSOJNZU|KNXTLPVSGKZVHLcZLOSLPGTO|KNXTLPVSIMbXMQTOEIURNUYR|KNXTLPVSIMbXMRTOGKebKTXO|KOUQGKWSJNSJENZUDGVRIMQS|KOUQGKWSJNSJENZUOTXOLZcV|KOUQGKWTLPYUPWbLHOfbDGbW|KOUQGKYULPWSJMQJEWbLPGfb|KOUQJNVSOVaKFOWTEJTKGNbW|KOUQJNVSOVaKGNYUEJZVBEVR|KOUQJNVSOVaKGNYUFKZVDGVR|KOUQJNWSNWaKFObWEJWTOSVO|KOURFKYUJNWTLPVSOMZVPWbQ|KOURGKYUJNWSNWaTEJUQLPea|KOURGKYUJNWSNWaTLPUQPWbL|KOURGKZUJNWSNWaTEJeaJMbW|KOURGKZUJNWSNWbSOTXOKTfb|KOWTFKTPBFUQJNbWOSVOLbfW|KOWTFKTPBFURJMYUMQcYEJRM|KOWTGKTPDGbWOTXOLbfWJNWS|KOWTGKTPDGUQJNYUEJVRNSaV|KOWTGKTPKNPGCLbWFKWSNWaT|KOWTJMTKFOaWBFWTGKTPDGda|KOWTJMTKFOaWGKWTBFTPDGda|KOWTJMTKFOaWGKWTBFTPDGea|KOWTJMTKFOaWGKWTBFTPDGUQ|KOWTJMTKFOaWGKWTBFUQOSQJ|KOWTJMTKFOaWGKWTBFUROSVO|KOWTJMTKFOaWLPeaHLWTPWaK|KOWTJMTKFObWGKWTBFTPDGUQ|KOWTJMTKFObWMRUNOSVOLJWS|KOWTJMTKFObWMRUNOSVOLJXT|KOWTJMTKFObWMRVMIRUNOSNK|KOWTJMTKFObWOSVOLbfWMQUR|KOWTJMTKFObWOSVOLbfWMQXT|KOWTJMTKFOUQMRVMIRZVEIVM|KOWTJMTKFOUREJbWGKZUJNUQ|KOWTJMTKFOURGKbWMQWSLPSL|KOWTJMTKFOURGKbWMQWTLPeb|KOWTJMTKFOURMQbWGKWSLPSL|KOWTJMTKFOURMQbWGKWTLPeb|KOWTJMTKFOVRMVaREJUQBFZU|KOWTJMTKGNVRMVaKFObWEJUQ|KOWTOSVOLSTPHLaVLOeaFKUQ|KOWTOSVOLSURJMYUMVaRFJea|LOUQHLYULPVSOVZSIMaVKNcY|LOUQHLYULPVSOVZSJMQJENSJ|LOUQJMQJFMWSHLYUMRUNKRVM|LOUQJMQJFMWTMRVMIRbWEJTP|LOUQJNWSNWbLGPfbEJbWHLYU|LOUQJNWSNWbLHOfbKNVRNUYR|LOUQJNWSNWbLHOfbKNZUNScZ|LOUQJNWSNWbLHOfbKNZUNSVR|LOURJMWSEJSLHObWJNfbNUZJ|LOVRJMaVHLWTLPUQPWbLGPQJ|LOVRJNWTFJTPJMZVMQcZGLPG|LOWSGLbWKNUQFKZUBFURNUQZ|LOWSGLbWKNURNUYRJMRNLPSL|LOWSGLbWKNURNUYRJMWTEJTK|LOWSGLbWLPSLPGWSJMfbMQSO|LOWSGLbWLPSLPGXTHLTPJNVR|LOWSHLbWJMUQMRVMIRSNRUYR|LOWSHLbWJMUQMRVMIRSNRVaR|LOWSHLSNJSXTOXVHIMbWEJfb|LOWSHLSNJSXTOXVHIMbWEJWS|LOWSHLSNJSXTOXVHIMbWMRUN|LOWSHLSNJSXTOXVHIMURMVaR|LOWSHLSNJSXTOXVHIMZVEIUR|LOWSHLSNJSXTOXVHIMZVMQVS|LOWSHLUQKNZUNWaKFObWLPea|LOWSHLURJNSJEUYRLPbWOTXO|LOWSHLXTOXSNJSVHIMbWEJUQ|LOWTJMbWEJWSAESLGWaTCGTP|LOWTJMbWEJWSBESLGWaTJNfb|LOWTJMbWEJWSBESLGWaTJNTP|LOWTJMbWHLTPMRUNKRVMIRWT|LOWTJMbWMRUNKRVMIRTKGNeb|LOWTJMbWMRUNKRVMIRTKGNfb|LOWTJMbWMRVMIRUNKRTKGNfb|LOWTJMUREJbWJNfbNUZJFMTP|LOWTJMUREJbWMQTPOTXOKTWS|LOWTJNbWNRUNKRVMIRTKGNXT|LOWTJNbWNRVMIRUNKRTKGNeb|LOWTJNVRFJTPJMUQNUQJENZQ|LPUQGLYUDGcYJMQJFMWTPWbS|LPUQGLYUDGVRJNZVEJcYLORM|LPUQHLWSKNbWFKZUKOURNUQZ|LPUQHLYUKOVRJMQJFVaRDHea|LPUQHLYUKOWTPWaKFObWLPea|LPUQJNWTPWbJENXTHLTPAEfb|LPURJNWSNWaTPWbSKNRKGWeb|LPVRHLZVLOWTPWbLGPfbKObW|LPVRJMUQMVaREJZUJMQJFVWT|LPVSHLXTKOTKFVaRJMZVMQcZ|LPVSHLXTKOTKFVZSGKSNKRUN|LPVSHLXTKOTKFVZSGKURKOSN|LPVSHLXTKOTKFVZSGKURLOSL|LPWSGLSOKTXOLSVOJMbWMQUR|LPWSGLSOLSVOKTXOIMZVMRVM|LPWSIMUREISOKTXOGLYULSVO|LPWSJMSOKTXOMQbWEJfbJMVR|LPWSJMSOKTXOMQbWEJWTPWaT|LPWSJMSOKTXOMQUREJbWJMfb|LPWSJMSOKTXOMQUREJRMIRVM|LPWSJMSOKTXOMQURFJbWJMWS|LPWSJMUQEJZUKNcZNWbSBEfb|LPWSJNSJFMaWMQWTPWbSEJfb|LPWSJNSJFMaWMQWTPWbSIMSO|LPWSJNSJFMXTPWbSHLfbBFbX|LPWSJNSJFMXTPWbSMQURHLfb|LPWTPWbSGLSOKTXOLSVOIMZV|LPWTPWbSIMfbKNbWMRVMJQSJ|LPWTPWbSIMfbMQSOKTXOEIbW|LPWTPWbSIMUQEIZUBEURJNSJ|LPWTPWbSIMUQEIZUHLebKNcZ|LPWTPWbSIMUREISOKTXOGLYU|LPWTPWbSIMUREISOKTXOMQfb|LPWTPWbSIMXTKNTPNWaTMQfb|LPWTPWbSJMXTMQTPIMSOKTPW|LPWTPWbSJNSJENXTAEVREJTP|LPWTPWbSKNaWGLXTFKTPKOPG|LPXTKOTKGNVSFKaVHLbXLOSL|"+
        "LPXTKOTKGNVSHLaVLOSLPGbX|LPXTKOTKGNVSHLaVLOSLPGea|IMUQEIVSKOaVFKZUJNQJNEWTIMTP|IMUQEIVSKOaVFKZUKNURNUQZMQYU|IMUQEIVSKOaVFKZUKNVROVRaBEXT|IMUQEIVSKOYUOVZSBEXTFKTPKNaV|IMUQEIWSMRVMIRbWAEfbLOSLGPWS|IMUQEIWTLPbWMRVMIRTOKTXOAEfb|IMUQEIWTMRVMIRZVAEVMEIcZIRZV|IMUQEIYUAEVSKNaVGKeaLPXTHLUR|IMUQEIYUKNcYFKWTBEaWLPeaGLTO|IMUQEIYUKNVRMVaKFOWTGKTPDGZV|IMUQEIYUKNVRMVaKFOWTGKZVBFdZ|IMUQEIYUKNWSNWaTBEURFKZUKNRK|IMUQEIYUKNWSNWaTLOTKGNVSNWbS|IMUQEIYULOURGLZUDGcYLPWTPWbL|IMUQEIZUAEURKNRKGNVRMVaKFOea|IMUQEIZUAEURKNRKGNVRNUQZJNXT|IMUQEIZUAEVRMVaRLOWTJNcZOSbW|IMUQEIZUAEVSLOSLHOURMVaROSWN|IMUQKNVRMVaKGNZUDGURNUQZFKWT|IMUQKNWSNWaTEIZUBEURFKYUKNRK|IMUQKNWSNWaTLOTKGNbWHLebDHYU|IMUQKNWSNWaTLOTKGNbWHLWTMRVM|IMUQKNWSNWaTLOTKGNbWHLXTLPWS|IMUQKNWSNWbSFKYUJNQJNWaTENTP|IMUQKNWTLPYUPWbSNWaTFKTOKTXO|IMUQKNWTNSVOLSaVGLVOLSeaDGaV|IMUQKNXTLPbXEITOGKZUKTXOMRVM|IMUQKNXTLPbXEITOMRVMIROKFOZV|IMUQKNXTLPVSMRTOGKbXKTXORVaK|IMUQKNXTNSVOLSWNJSQJENYUAETP|IMUQKNXTNSWNJSVOLSQJENbXAETP|IMUQKNYUNSWNJSQJENVOLSbWSbfW|IMUQLPWTPWaTKOTKGNbWHLWTCGTO|IMUREIWSKObWFKWTLPSLPWaTGWea|IMUREIWTJNbWNUZJFMfbAEdZMQTP|IMUREIWTLOTPAEbWOTXOKTZUFKUQ|IMURMQRMJNMIEJWTLPYUPWaTHLbW|IMURMQRMJNMINRVMQJYUJNUQLOWT|IMURMQRMJNMINRVMQJYULOURJMWT|IMURMQRMLPWSEISOIRVMKTXOJNMI|IMURMQRMLPWSHLSOLSVOKTXOEIZV|IMURMQRMLPWTPWbSHLMIJNSJENfb|IMURMQRMLPWTPWbSJNSJENMIHLfb|IMVRMVaRLPZVGLWTPWbSKNRKFOUR|IMVSEIWTKOTKFVZSMQXTQZcVIMbW|IMVSEIWTKOTKFVZSMQXTQZcVIMTO|IMVSKNXTMQaVEITPFKWTNWTaAEbW|IMVSKNXTMQbXFKaVJMSJMFTPEJfb|IMVSKNXTMQTPFKaVKObXGKPGCLeb|IMVSKNXTMQTPFKbXJMSJMFUREJRM|IMVSMQWTKNTPNWbSJMfbFKbWEJaV|IMWSLPbWGLUQKNVRMOWTPWaREIZV|IMWTMQTPJNbWEJWTAETOLSVOKTPW|IMWTMQTPJNbWNRUNKRVMQJaVJMWS|IMWTMRUNKRVMJQTPEJbWLOWTAETK|IMXTLOUROXRIHLYULPUQGLZUJNcY|IMXTLOUROXRIJNYUHLUQLPcYEJZU|IMXTLOUROXRIJNYUHLUQLPWSNWbS|IMXTMQTPJNWSNWbSEJfbAEaWEIUR|IMXTMQTPJNWSNWbSEJfbAEaWKObX|IMXTMQTPKNVSFKbXJMSJMFUREIfb|IMXTMRUNKRVMJQTPEJWTLOTKFObW|IMXTMRUNKRVMJQWSLPTOEJYUAEUR|IMXTMRVMJQTPEJbXJNWTAEaVNRVM|JMUQEJWTAETOKTXOLSVOGLaWLSWN|JMUQEJWTLPTOKTXOMRVMIRbWAEfb|JMUQEJZUKOURFKWSLPSLHObWBEWS|JMUQFJWSLPZUJNSJMFURHLbWLOYU|JMUQFJWSLPZUJNSJMFURHLYUEJcY|JMUQFJYULPURHLZUDHWSJNSJMFbW|JMUQLOQJFMWTEJbWBFTPMQWSAESL|JMUQLOQJFMWTMRVMIRbWEJTPAEWT|JMUQLOQJFMYUMRUNKRVMIRWTEJTK|JMUQMRVMIRWSEJbWAEfbLOSLGPWS|JMUQMRVMIRWSEJbWBEfbLOSLHOZU|JMUQMRVMIRWSEJSOLSZVSZdEAJXT|JMUQMRVMIRWSLOSLHObWEJWTDHTP|JMUQMRVMIRWTEJbWAETPEIWTJMQJ|JMUQMRVMIRWTEJbWLOZUJNdZAEaV|JMUQMRVMIRWTEJZVAEVMEIcZIRZV|JMUQMRVMIRWTKNbWFKTPLOZUEJWT|JMUQMRVMIRWTLOTPEJbWOTXOKTZV|JMUREJWSKObWAEWTLPTKGWaTPWeb|JMUREJWSKObWFKYUMQebJMWTLPSL|JMUREJWSKObWGKWTLPSLPWaTHOfb|JMUREJWSKORNAEbWFKZUKRUNLPSL|JMUREJWSKORNAEbWLPSLJbfWHOVR|JMUREJWTJNbWNUZJFMfbMQdZIMTO|JMUREJWTJNbWNUZJFMfbMQdZKNTP|JMUREJWTLObWJNfbNUZJFMdZMQYU|JMUREJWTLObWJNTPNUZJFMWTMQfb|JMUREJWTLObWMQTPJNWTNUYRAEcY|JMUREJWTLObWMQTPJNWTNUYRAEfb|JMUREJWTLObWMQWSJMSLGWaTAETP|JMUREJWTLPTOKTXOMQRMIRVMJNMI|JMURFJWSKOaWMQWTJMTKGWbSLPeb|JMURFJWSKOaWMQWTJMTKGWbSLPRN|JMURFJWSKOaWMQWTJMTKGWbSLPYU|JMURFJWSKObWMQebJMYUGKWTLPSL|JMURKNRKGNVSEJSOLSaVCGVOFKOF|JMURKNRKGNVSEJSOLSaVDGVOGLea|JMURKNRKGNWTMRVMIRZUEJbWAEdZ|JMURKOWTLPTKGUZJENXTPWbJFMYU|JMURLOWTEJbWAEfbMQTPHLWSOTXH|JMURLOWTEJbWAEfbMQTPJNWTNUYR|JMURLOWTEJbWAEfbMQTPJNYUGLPG|JMURLOWTEJbWAEfbMQYUJNRMIYVS|JMURLOWTEJbWJNTPNUZJFMWTMQfb|JMURLOWTEJbWMQRMIRVMGLMILPYU|JMURLOWTEJbWMQRMIRVMGLTPJNPG|JMURLOWTEJbWMQTPOTXOKTRMIRVM|JMURLOWTEJbWMQWSJMSLGWaTAETP|JMURLOWTEJbWMQWSJMSLGWaTHLZU|JMURLOWTGLTPCGbWOTXOLbfWKOWS|JMURMQVSKOaVEJWTLPTKGWbSCGYU|JMVSEJWTLPTOKTXOGKUQKTbXBEXO|JMVSFJaVMQeaJNSJENURNUYRKOWS|JMVSFJWTMQSNKRUNJSTOSVZSLPbW|JMVSFJWTMQTOKTXOIMSNLSNWJNUR|JMVSKOaVFKUREJWTKNTKNWbSGWeb|JMVSKOaVMQeaEJWTJMTKGWaTLPTO|JMVSKOUQOVQJENaKFOYUGKWTLPea|JMVSLPSOKTXOMQUREJaVGKeaKTRN|JMVSMQaVIMUREIWTLPSNPWbSKOSL|JMVSMQaVIMWTMRUNKaeVEJYUAETO|JMVSMQUREJRNKRSOLSWEAJZUQZdE|JMVSMQURKNRKFVaREJeaLOaVBFWT|JMVSMQURKOaVEJWTGKSNJSRMIadP|JMVSMQURKOaVEJWTJMTKGWbSLPda|"+
        "JMVSMQURKOaVEJWTJMTKGWbSLPeb|JMVSMQURKOaVEJWTJMTKGWbSLPfb|JMVSMQURKOaVEJWTJMTKGWbSLPSO|JMVSMQURKOaVFKWTKNTKNWbSGWeb|JMVSMQURKOaVGKWTLPSLPGTOKTXO|JMVSMQURKOSNOSNKGUWNCGYRLOcY|JMVSMQURLPSOKTXOEJZUQZcVGLdZ|JMVSMQWTEJTOKTXOJMURMVaRAEea|JMVSMQWTKOTKFVaRLObWHLeaCFWT|JMVSMQWTKOTKFVZSQZdUIMbWMQXT|JMWSEJaWKNeaMQSOLSVOJMWSNWbS|JMWSEJaWKNXTMRVMIRbXGKZVRaeV|JMWSEJaWMQeaJMWTMRUNKRVMQJaV|JMWSEJbWAEfbMRUNKRVMJQXTIMYU|JMWSEJbWAEfbMRUNKRVMJQXTLPZV|JMWSEJbWAEWTMRUNKRVMJQTPIMfb|JMWSEJbWKOUQFKZUJNSJMFWSKNSJ|JMWSEJbWKOUQGKZULPSLPGXTAETO|JMWSEJSOKTXOLSVOMQbWAEfbJMUR|JMWSEJSOKTXOLSVOMQURGLRNJSOV|JMWSEJSOLSVOKTXOAEURMVaRJMOK|JMWSEJSOLSVOKTXOAEURMVaRJNRK|JMWSEJSOLSVOKTXOBEUQGLaVLSVO|JMWSEJSOLSVOKTXOBEZVMRVMJZcV|JMWSEJSOLSVOKTXOGLaWLSWEAJbW|JMWSEJSOLSVOKTXOGLaWLSWEAJUQ|JMWSEJSOLSVOKTXOMQURJMaVAEbW|JMWSEJURKOaWFKWTKNTKNWbSGWeb|JMWSEJURKOYUMQcYJMbWFKRNKRUN|JMWSFJbWMQWTJNSJENTOLSVFBKUR|JMWSFJbWMQWTJNSJENTPNRUNKRVM|JMWSKOaWFKUQMRVMIRWTOVZSBFSN|JMWSKOaWFKWTEJbWBFUQMRVMOVZS|JMWSKOaWFKWTMRUNKaTKGWbSLPeV|JMWSKOaWGKWTEJTPDGURMQZUQZdU|JMWSKOaWGKWTLPSLPGTOKTXOEJbW|JMWSKOaWMQeaEJWTJMTKGWaTLPTO|JMWSKOaWMQUREJWTJMTKGWbSLPeb|JMWSKOaWMQWTEJTKGWbSLPfbCGbW|JMWSKOaWMQWTEJTKGWbSLPfbJMbW|JMWSKOaWMQWTEJTKGWbSLPURCGea|JMWSKOaWMQWTEJTKGWbSLPURJMfb|JMWSKOaWMQWTEJTKGWbSLPVRJMSN|JMWSKOaWMQWTFKTPEJURJMbWCFfb|JMWSKOaWMQWTGKTPDGUREJYUBEbW|JMWSKOaWMQWTGKURLPSLPGTOKTXO|JMWSKOaWMQWTLPTKGWbSEJfbJMSO|JMWSKOaWMQWTLPTKGWbSEJURCGSO|JMWSKObWEJUQFKZUJNSJMFURLPWT|JMWSKObWEJUQGKZULPSLPGXTAEUR|JMWSKObWEJUQMRVMOVaRJNRKIRea|JMWSKObWEJURFKWTLPSLPWaTGWea|JMWSKObWEJURFKYUMQcYJMRNKRUN|JMWSKObWFKUQBFQJFMfbMQYUEJUR|JMWSKObWFKUQBFQJFMfbMQYUIMSN|JMWSKObWFKUQBFQJFMYUMQfbEJUR|JMWSKObWFKUQBFQJFMYUMRUNKRVM|JMWSKObWFKUQEJZUJNSJMFURLPWT|JMWSKObWFKUQMRVMIRSNRUYROSNJ|JMWSKObWFKUQMRVMIRSNRVaROSXT|JMWSKObWFKUREJWTLPSLPWaTGWeb|JMWSKObWFKUREJYUMQcYJMRNKRUN|JMWSKObWFKUREJYUMQcYJNSJBFRM|JMWSKObWFKUREJYUMQcYJNSJBFWT|JMWSKObWFKUREJZUMQRMIRVFCJaV|JMWSKObWFKWTLPSLPWaTGWeaKNaT|JMWSKObWGKUQLPSLPGQJFMWSEJYU|JMWSKObWMQWTEJTKGWaTLPeaPWaT|JMWSKObWMQWTLPTKGWaTPWebHLbS|JMWSKOUQEJZUGKaWKNVRMVSZBEWT|JMWSKOUQGKQJEWaTAETPDGYUEJea|JMWSKOUQGKQJEWaTAEYUEJURLPea|JMWSKOUQGKQJEWaTIMTPCGVSOVZS|JMWSKOUQGKQJEWaTIMTPDGdaKNbW|JMWSKOUQGKQJEWaTIMTPDGdaMQbW|JMWSKOUQGKQJEWaTIMZUOSVOLSda|JMWSKOUQGKQJEWaTIMZUOSVOLSea|JMWSKOUQGKQJEWaTLPYUPWbLHOfb|JMWSKOUQGKQJEWbSIMaWAEWTLPSL|JMWSKOUQGKQJEWbSIMaWAEYUMQUR|JMWSKOUQGKQJEWbSIMaWMQWTLPSL|JMWSKOUQGKQJEWbSIMYUMQaWAEWT|JMWSLOSLHOUREJaWAEWSGLbWLPSL|JMWSLOSLHOUREJaWJNWSNWbLGPfb|JMWSLOSLHOVRMVZLGPXTPWbSCGfb|JMWSLPSOKTXOMQaWEJWTPWbSJMfb|JMWSLPSOKTXOMQbWEJfbJMbXMRUN|JMWSLPSOKTXOMQbWEJfbJMbXMRVM|JMWSLPSOKTXOMQbWEJfbJMVRMVZS|JMWSLPSOKTXOMQbWEJWTPWaTJMfb|JMWSLPSOKTXOMQUREJaWJMbXFJeb|JMWSLPSOKTXOMQUREJbWJMfbGLWS|JMWSLPSOKTXOMQUREJbWJMYUAEWS|JMWSLPSOKTXOMQUREJbWJMYUGLWS|JMWSLPSOKTXOMQUREJRMIRVMJNMI|JMWSMRUNKRVMIRbWLOSLHOfbEJWS|JMWSMRUNKRVMIRbWLOSLHOWTFKfb|JMWSMRUNKRVMIRZUFKUNKRXTEJTO|JMWSMRUNKRVMIRZUFKUNKRXTGKbX|JMWSMRUNKRVMIRZUFKUNKRXTGKSN|JMWTEJbWAETPMQWSLOSLHOfbJNUR|JMWTEJbWJNfbMRVMIRTPAEUQLOWT|JMWTEJbWJNURNUZJFMVSLOSLHOdZ|JMWTEJbWLOfbMQTPOTXOKTURTXRM|JMWTEJbWMQURLOTPJNWTNUYRAEfb|JMWTEJbWMQWSAESOLSVOGLaVLSVO|JMWTEJbWMQWSLPSOPWaTAETPKTPW|JMWTEJTOKTXOLSVOMQbWGLWSBEUR|JMWTEJTOKTXOLSVOMQbWJMfbAEWS|JMWTEJTOKTXOLSVOMQbWJNURNUYR|JMWTEJTOLSVOKTXOBEURMVaRJMZV|JMWTEJTOLSVOKTXOBEZVMRVMJZcV|JMWTEJTOLSVOKTXOMQbWAEfbJMUR|JMWTEJTPAEURKOaWOTXOLSWNJSVO|JMWTEJTPLObWOTXOKTWSTXURAEfb|JMWTEJTPMQbWJNVSFJaVJMSJMFfb|JMWTEJTPMQbWLOWSAESLHOfbJNbW|JMWTEJTPMQXTLObXJNURNUYRAEfb|JMWTEJUQMRVMIRTPLObWJNWTRUYR|JMWTFJUQLPZUPWaTCFURKNRKGNbW|JMWTFJUQLPZUPWaTCFVSMRUNKRTO|JMWTFJUQLPZUPWaTKNURNUYRHLbW|JMWTKNaWNSWNMRVMIKeaEJTPLOUR|JMWTKNaWNSWNMRVMIKTPEJUQJNZU|JMWTKNTOLSVOEJbWGLfbLSURNUWE|JMWTKNTOLSVOEJURNUYRMVZSJMbW|JMWTKNTPMQXTEJaWAEWSNWTaJNbW|JMWTKNVRMVaKGNbWEJTPIMPGDKXT|JMWTLObWEJfbAETPMRVMJQWTEJUR|JMWTLObWEJTPMQURJNfbNUYRAEcY|JMWTLObWEJTPMQWSAESLHOfbKNaW|"+
        "JMWTLObWEJWSAESLGWaTHLTPKOPG|JMWTLObWEJWSAESLGWaTHLURMQfb|JMWTLObWEJWSMQSLGWaTJNURNUYR|JMWTLObWMQWSEJSLGWaTHLURLOfb|JMWTLObWMRUNKRVMIRTKGNZUNSUN|JMWTLObWMRVMIRUNKRTKGNebFKWS|JMWTLOUREJbWJNTPNUZJFMWTMQfb|JMWTLPTOKTXOMQbWFJWTPWaTJMfb|JMWTLPTOKTXOMQUREJRMIRVMJNMI|JMWTLPUQPWQJENbJFMfbHLYUMQbW|JMWTLPUQPWQJENbJFMXTAEfbMQVR|JMWTMQTPEJXTJMTOLSVOKTPWHLWS|JMWTMRUNKRVMIRTOLSZURVaRGKRM|JMWTMRUNKRVMIRTOLSZURVaRGLRM|JMWTMRUNKRVMIRTOLSZURVaRHLRM|JMWTMRUNKRVMIRTOLSZURVaRHLUQ|JMWTMRUNKRVMIRZUFKUNKRTPLObW|JMWTMRVMIRUNKRaWFKWSRVSNKRZS|JMWTMRVMIRUNKRTOLSZURVaRGKRM|JMWTMRVMIRUNKRTPEJbWAEWTLOTK|JMXTLObXEJfbMQTPJNURNUYRAEWS|JMXTLPbXMQTOKTXOGKWTPWaTEJfb|JMXTLPbXMQVSKNSJENURNUYRHLaV|JMXTLPUQGLQJFMbXEJVSMQebJNSJ|JMXTLPUQHLQJFMVSMQSNKRTOLSWU|JMXTLPUQMRVMIRZURVaRKNRKFXUR|JMXTLPVSHLbXDHebKOTDMRUNCGDK|JMXTLPVSMQaVEJeaJNSJFMVSKOTK|JNUQEJWSNWbSKOZUJNSJFMQJOTXO|JNUQEJWTAETPLObWNSWNKRVMIRaW|JNUQEJWTAETPLOVRNUYRJNZVNUQZ|JNUQEJWTLPbWGLZULOURNUQZJMYU|JNUQEJWTNRVMIRbWLOfbAETPOTXO|JNUQEJYUAEVRIMRINSWNKYbWJNZV|JNUQEJZUAEWTLOVROSaWGLTPDGQM|JNUQEJZUAEWTLPQMJSaVPWVOKTbA|JNUQEJZULPURNUQZIMYUMQWSKNbW|JNUQEJZULPVRGLRMIRWTPWbSNWUP|JNUQKOWTGKQMIRVMEIZVIRVMAEMI|JNUQKOWTNRTKGNVMIRbWFKWTLOfb|JNUQLOWSNWbLHOYUOTXOKTURTXfb|JNUQLOWTEJbWAETPNRVMIRWTJNZU|JNUQLOWTEJZUNScZKNTRBEVOJMQJ|JNUQLOWTEJZUNSVRJNcZSWbLGWaT|JNUQLOZUEJWTNSVRJNTPAEcZEJaV|JNUQLOZUEJWTNSVRJNTPAEcZIMQA|JNUQLPVSEJSOKTXOAEWSNWbSGKaV|JNUQNRVMIRWSEJbWAEfbLOSLHOWS|JNUQNRVMIRWSEJbWBEfbLOSLHOZU|JNUQNRVMIRWSEJbWBEZULOSLHOUN|JNUQNRVMIRWSEJbWLOSLHOWSOVZS|JNUQNRVMIRWSEJSNJSZVSZcMAEMI|JNUQNRVMIRWSEJSOLSaVRadEAJea|JNUQNRVMIRWSLOSLHObWGLWTKNTK|JNUQNRVMIRWSLOSLHObWGLZUKNWT|JNUQNRVMIRWSLOSLHObWKNfbGLWT|JNUQNRVMIRWSLOSLHObWKNWTGLTK|JNUQNRVMIRWTEJbWLOaVRaeVAEVR|JNUQNRVMIRWTEJbWLOfbAEaVRaeV|JNUQNRVMIRWTEJbWLOTPAEWTJNZU|JNUQNRVMIRWTEJbWLOTPJNWTAEZU|JNUQNRVMIRWTEJbWLOTPOTXOKTZV|JNUQNRVMIRWTEJbWLOZVBEVMOSWN|JNUQNRVMIRWTEJTPAEbWEIfbJMQJ|JNUQNRVMIRWTEJTPAEbWJNZULOWT|JNUQNRVMIRWTEJTPLObWJNZUOTXO|JNUQNRVMIRWTEJZVAEVMEIcZIRZV|JNUQNRVMIRWTEJZVJMQJFMVSLOSL|JNUQNRVMIRWTKNTPFKXTLObXCFZU|JNUQNRVMIRWTKNTPFKXTLObXHLZU|JNUQNRVMIRWTKNZUFKcZLObWBFfb|JNUQNRVMIRWTLObWEJfbJNTPAEWT|JNUQNRVMIRWTLObWEJTPAEWTJNZU|JNUQNRVMIRWTLObWEJTPJNWSNWaT|JNUQNRVMIRWTLObWEJTPJNWTAEZU|JNUQNRVMIRWTLObWEJTPJNWTRUYR|JNUQNRVMIRWTLObWEJTPOTXOKTWS|JNUQNRVMIRWTLObWEJZVJMQJFMTP|JNUQNRVMIRWTLObWKNTKFOWTGKfb|JNUQNRVMIRWTLOTPEJbWJNWTRUYR|JNUQNRVMIRWTLOTPHLbWEJfbJMQJ|JNUQNRVMIRWTLOTPHLbWEJWTJMQJ|JNUQNRVMIRWTLOZUHLUNKRTKGNaV|JNUQNRVMIRWTLOZUHLUNKRTKGNbW|JNUQNRVMIRZUKNdZLOWTFJTKJMQS|JNUQNRVMIRZUKNdZLOZVEIVMIRcZ|JNUQNRVMIRZUKNWTFKTPLObWHLWT|JNUQNRVMIRZULOUNKRdZFKZUKNcZ|JNUQNRVMIRZULOUNKRdZFKZUKNWT|JNUQNRVMIRZULOUNKRWTHLTKGNaV|JNUQNRVMIRZVEIVMIRWTKNbWAEdZ|JNUQNRVMIRZVEIVMIRWTKNdZAEbW|JNUQNSWNKRVMIRZVEIVMIRcZAEZV|JNURNUYREJWSKObWJMWTMQTKGUcY|JNURNUYREJWTAETPJNRMIRVMLOMI|JNURNUYREJWTJMTOLSVOKTXOMVZS|JNURNUYREJWTJMTPLObWOTXOKTcY|JNURNUYREJWTJNRMIRVMAEMILOTP|JNURNUYREJWTJNRMIRVMAEMINRcY|JNURNUYREJWTJNRMIRVMAEMINRTP|JNURNUYREJWTJNRMIRVMAETPEIZV|JNURNUYREJWTLObWJMfbMQTPAEWS|JNURNUYREJWTLObWJMTPAEfbOTXO|JNURNUYREJWTLOTPAEbWJNWTNUZQ|JNURNUYREJWTLOTPJMbWOTXOKTWS|JNURNUYREJWTLOTPJNbWNUZQAEWT|JNURNUYREJWTLPTOKTXOJMVSMVaR|JNURNUZQEJWSKObWGKYUBEebDGcZ|JNURNUZQEJWSKOYUJNSJFMQJOTXO|JNURNUZQKNVRNUQZEJaVIMYUMQWS|JNURNUZQKNVRNUQZFKaVEJWSLOSL|JNURNUZQLOWSGLYUOTXOKTbXDGXO|JNURNUZQLPWSPTXOKTYUTWaTIMQJ|JNVREJaVBEWTJMTPLOUQNUYRHLQJ|JNVREJaVJMUQNUQJFMZJBFVSFMWT|JNVREJaVJMXTMQbXLOfbGLTPAEPG|JNVREJaVJMXTMQbXLOfbGLTPBEPG|JNVREJaVJMXTMQbXLOfbGLTPOTPG|JNVREJaVJMXTMQTPFJWTJMbXLOda|JNVREJaVJMXTMQTPFJWTLOdaOXRM|JNVREJaVJMXTMQTPLOWSNWbLHOea|JNVREJaVLOWTBETPJMUQNUYRHLQJ|JNVREJaVLOWTBEUQNUYRJMQJEUZQ|JNVREJaVLOWTHLTPDHUQNUYRBEbW|JNVREJaVLOWTJMUQNUQJFMZJBEbW|JNVREJaVLPeaGLVSLOSLPGXTJMZV|JNVREJaVLPVSGLZVLOSLPGeaJMUQ|JNVREJaVLPVSGLZVLOSLPGUQNUQZ|JNVREJaVLPVSGLZVLOSLPGVSGLUQ|JNVREJaVLPXTHLbXLOWSNWTaGLaW|JNVREJWTBEbWJMTPMVZJFMWTMQTO|"+
        "JNVREJWTBEZVJMbWMQcZLOTPHLWS|JNVREJWTJMaWMVZJFMWSLOSLGWbS|JNVREJWTJMaWMVZJFMWSMQTOKTXO|JNVREJWTJMaWMVZJFMWSMRUNKRea|JNVREJWTJMUQMVZJFMQJBEYUENUQ|JNVREJWTJMUQMVZJFMQJBFYUFMUQ|JNVREJWTJMUQNUQJFMZJBEJFKBTP|JNVREJWTJMUQNUQJFMZJBFYUFMUQ|JNVREJWTLObWBETPJMWTMVZLHOaV|JNVREJWTLObWJMUQMVZJFMQJBEYU|JNVREJXTBETOLSaVJMVOKaRBEJeV|JNVREJXTJMUQNUQJFMZJBEaVENVS|JNVREJXTLOTPBEaVHLWSNWbSJMfb|JNVREJXTLOTPBEaVJMVSMVSLHOZL|JNVREJXTLOTPJMWSNWbLMVaRHOZV|JNVREJXTLOTPOTbXJMXOMVZJKTUQ|JNVREJXTLOTPOTZVJMUQNUQZAEWS|JNVREJXTLPaVHLbXLOWSNWTaDHUQ|JNVREJXTLPaVHLbXLOWSPWSbGLUQ|JNVREJXTLPbXGLZVLOUQNUQZJMVS|JNVREJXTLPbXHLaVJMWSNWTaMQfb|JNVREJXTLPbXHLZVJMUQNUQZMQVS|JNVREJXTLPZVGLbXJMUQNUQZMQVR|JNVREJXTLPZVJMUQNUQZMRVMIRZU|JNVREJZVJMUQNUQJFMYRAEWSBFbW|JNVREJZVJMUQNUQJFMYRAEWSCFbW|JNVREJZVJMUQNUQJFMYRAEWSCFcY|JNVREJZVJMUQNUQJFMYRAEWSCFdZ|JNVREJZVJMUQNUQJFMYRAEWSKORN|JNVREJZVJMUQNUQJFMYRAEWSLOSL|JNVREJZVJMUQNUQZAEVSLOSLHOWS|JNVREJZVJMUQNUQZAEWSEJaWKOXT|JNVREJZVJMUQNUQZAEWSEJSOLSVO|JNVREJZVJMUQNUQZAEWSEJYUKOaW|JNVREJZVJMUQNUQZAEWTEJbWMQTP|JNVREJZVJMUQNUQZAEWTEJTPJNVS|JNVREJZVJMUQNUQZAEWTEJTPMRVM|JNVREJZVJMUQNUQZAEWTMRVMIRbW|JNVREJZVJMUQNUQZAEXTLObXEJfb|JNVREJZVJMUQNUQZAEXTLObXEJTP|JNVREJZVJMUQNUQZAEXTLObXEJWS|JNVREJZVJMUQNUQZAEXTLObXEJYU|JNVREJZVJMUQNUQZAEXTLObXMRVM|JNVREJZVJMUQNUQZAEXTMQTOLSVO|JNVREJZVJMUQNUQZAEYUMQWSEJSO|JNVREJZVJMUQNUQZAEYUMRUNKRVM|JNVREJZVJMUQNUQZFJWSAEYUMQSO|JNVREJZVJMUQNUQZFJWSBFYUKNUQ|JNVREJZVJMUQNUQZKNVRNUZJFMYU|JNVREJZVJMUQNUQZKNVSFJXTMQTP|JNVREJZVJMUQNUQZKNWSNWbSLPfb|JNVREJZVJMUQNUQZKNWSNWbSLPYU|JNVREJZVJMUQNUQZKNXTMQTOLSVO|JNVREJZVJMUQNUQZKNXTMRVMIRTP|JNVREJZVJMUQNUQZLOWSGLbWLPSL|JNVREJZVJMUQNUQZLOWSGLYUMQbW|JNVREJZVJMUQNUQZLOWSHLYUAEUR|JNVREJZVJMUQNUQZLOWTAEbWMRVM|JNVREJZVJMUQNUQZMQWSAEYUEJSO|JNVREJZVJMUQNUQZMQWTFJTOKTXO|JNVREJZVJMUQNUQZMQWTKNTOLSVO|JNVREJZVJMUQNUQZMRVMIRWSFJbW|JNVREJZVJMUQNUQZMRVMIRWSFJZU|JNVREJZVJMUQNUQZMRVMIRWSLOSL|JNVREJZVJMUQNUQZMRVMIRXTAETO|JNVREJZVLOUQNUQZAEWSGLYULPSL|JNVREJZVLOWTNScZIMRIKNTRJMVO|JNVREJZVLOWTNSUQSZdUAEcZJMQA|JNVREJZVLOWTNSUQSZdUAETPJNbW|JNVREJZVLOWTNSUQSZdUIMRIBEIB|JNVREJZVLPUQNUQZHLWSKOYUBEXT|JNVREJZVLPUQNUQZHLWSKOYUDHXT|JNVREJZVLPUQNUQZHLWSKOYUJMbW|JNVRFJaVJMUQNUQJENYRNUZQAEdZ|JNVRFJaVJMWTMQTOLSVFBKbWHLWT|JNVRFJaVJMWTMQTOLSVFBKXTGLZV|JNVRFJaVJMWTMQTOLSVFBKXTHLbX|JNVRFJaVLPXTGLbXLOWSNWTaJNfb|JNVRFJWSNWbSJMRNKRUNBFXTLPeb|JNVRFJWSNWbSJMSNMVaRBFXTLPea|JNVRFJWTJMaVMQTOLSVFBKbWHLfb|JNVRFJWTJMaVMQTOLSVFBKXTHLbX|JNVRFJWTJMTPMVZJENUQAEbWBFcZ|JNVRFJWTJMTPMVZJENUQAEbWBFfb|JNVRFJWTJMTPMVZJENUQAEbWEJYU|JNVRFJWTJMTPMVZJENUQAEbWLOWT|JNVRFJWTJMTPMVZJENUQLObWAEWT|JNVRFJWTJMTPMVZJENUQLObWOSWT|JNVRFJWTJMZVMQcZLOTPBFbWHLfb|JNVRFJWTJMZVMQcZLOTPCFbWEJeb|JNVRFJWTJMZVMQcZLOTPCFbWHLeb|JNVRFJWTJMZVMQcZLOTPCFbWNSWN|JNVRFJWTJMZVMQcZLOTPGLPGCLbW|JNVRFJWTJMZVMQcZLOTPHLbWBFWS|JNVRFJWTLObWJMTPMVZJENUQAEWT|JNVRFJWTLOTPJMbWMVZJENWTAEUQ|JNVRFJWTLOZVNScZIMRIKNTRJMVO|JNVRFJWTLOZVNSUQSZcVJMQJEUYR|JNVRFJWTLOZVNSUQSZdUIMRIBFIB|JNVRFJWTLOZVNSUQSZdUJNcZIMQL|JNVRFJWTLOZVNSUQSZdUKNTKJMQS|JNVRFJZVJMUQNUQZEJWTLObWAETP|JNVRFJZVJMUQNUQZMQWSKOaWGKWT|JNVRFJZVJMUQNUQZMRVMIRWSLOSL|JNVRFJZVJMUQNUQZMRVMIRWTKNTP|JNVRFJZVJMUQNUQZMRVMIRWTLObW|JNVRFJZVJMUQNUQZMRVMIRXTKNTP|JNVRFJZVJMUQNUQZMRVMIRXTLObX|JNVRFJZVJMUQNUQZMRVMIRZULOUN|JNVRFJZVJMWTMQcZLObWHLTPNSWN|JNVRFJZVJMWTMQcZLOTPBFbWHLeb|JNVRFJZVJMWTMQcZLOTPBFbWHLfb|JNVRFJZVJMWTMQcZLOTPGLPGCLbW|JNVRLOWTFJbWJMTPMVZJENUQOScZ|JNVRLOZVEJWTNSUQSZdUAETPJNbW|JNVRLPWTPWbJFVaREJZVHLfbJNbW|JNVRLPXTGLbXEJaVLOWSPWSbHLUQ|JNVRLPZVGLRMIRVMEIcZIRWTPWbJ|JNVRLPZVHLUQNUQZIMWSKOSNMQYU|JNVRLPZVHLUQNUQZIMWSMQYUKOSN|JNVRLPZVHLUQNUQZIMWTPWbSKOfb|JNVRLPZVHLUQNUQZIMWTPWbSKOYU|JNVRLPZVHLUQNUQZIMYUMQWSKOUR|JNVRLPZVHLVSDHSJFVaREJeaJMRN|JNVRLPZVHLVSDHSJFVaREJUQBFda|JNVSEJaVAEVRLPRMIRSOKaeMJQXT|JNVSEJaVKOeaFKURNUYRIMRIKNZU|JNVSEJaVKOeaGKURNUYRLPSLPGWS|JNVSEJaVKOUQFKZUJMQJNEURBFYU|JNVSEJaVKOUQFKZUJMQJNEWTIMTP|JNVSEJaVKOUQFKZUJMQJNEWTLPSL|"+
        "JNVSEJaVKOUQGKZUBEURNUQZIMYU|JNVSEJaVKOUQGKZUBEURNUQZJNSJ|JNVSEJaVKOUQGKZUBEURNUQZKNYU|JNVSEJaVKOUQGKZUBEURNUQZKNZU|JNVSEJaVKOUQGKZUBEURNUYRJMQJ|JNVSEJaVKOUQGKZUDGURNUQZIMYU|JNVSEJaVKOUQGKZUDGURNUQZJMWT|JNVSEJaVKOUQGKZUDGURNUQZJNSJ|JNVSEJaVKOUQGKZUDGURNUQZKNYU|JNVSEJaVKOUQGKZUDGURNUQZKNZU|JNVSEJaVKOUQGKZUDGURNUYRBEcY|JNVSEJaVKOUQGKZUDGURNUYRJNSJ|JNVSEJaVKOUQGKZULPSLPGVRAEXT|JNVSEJaVKOUQGKZULPSLPGVRGLRM|JNVSEJaVKOUQGKZULPSLPGVRHLea|JNVSEJaVKOURNUYRJMeaAEWTGKSN|JNVSEJaVKOURNUYRJMeaAEWTGKTP|JNVSEJaVKOURNUYRJMZUGKSNDGNJ|JNVSEJaVKOURNUYRJMZUGKSNOSNP|JNVSEJaVKOURNUYRJMZUMQWTQZdU|JNVSEJaVKOURNUZQGKYUBEeaDGcZ|JNVSEJaVKOURNUZQGKYULPSLPGXT|JNVSEJaVLPUQGLZUKOURNUQZJMYU|JNVSEJaVLPVRGLZVLOSLPGUQNUQZ|JNVSEJUQAEZVIMdZKOZUOTXOMRVM|JNVSEJUQAEZVIMYUEIURNUQZKNXT|JNVSEJUQKOYUOVaKFOWTGKZVBFTP|JNVSEJURNUYRKORNOVaRJSWNBEXT|JNVSEJZVKOUQGKYUBEcYDGURNUQZ|JNVSEJZVKOUQGKYUBEURNUQZKNZU|JNVSEJZVKOUQGKYUDGURNUQZKNZU|JNVSEJZVKOUQNRVMIRXTOXSOLSWU|JNVSEJZVKOURNUYRJMcZGKWTAESN|JNVSEJZVKOURNUYRJMcZGKWTAETP|JNVSEJZVKOURNUYRJMcZMQZUQZdU|JNVSFJaVKOUQGKZUDGURNUQZKNZU|JNVSFJaVKOURNUYRBFWTFKSNJSTP|JNVSFJaVKOURNUYRJMRNMQWTIMTK|JNVSFJaVKOURNUYRJMZUEJWTGKTP|JNVSFJaVKOURNUYRJMZUGKWTCFTP|JNVSFJaVLPXTCFUQGLZULOSLHXVR|JNVSFJZVKOUQGKYULPSLPGXTIMUR|JNVSFJZVKOURNUYRJMRNEJNEAJWT|JNVSFJZVKOURNUYRJMRNMQcZBFXT|JNVSFJZVKOURNUYRJMRNMQcZIMZU|JNVSLOSJFMWTMQbWEJTPJMWTAEfb|JNVSLOSJFMWTMRUNKRTKGNXTHLbX|JNVSLOSLHOUQNRWTIMQJFMbWEJTP|JNVSLOSLHOURNUYREJaVJNWSNUSL|JNVSLPSJFMWSGLaVLOSLPGXTHLVS|JNVSLPSJFMWSHLaVKObWMQUREJYU|JNVSLPSJFMWSHLUQEJaVKObWGKZU|JNVSLPSJFMWSHLUQEJaVKOZUJNSJ|JNVSLPSJFMWTPWbSEJfbMQSOKTXO|JNVSLPSJFMWTPWbSEJXTMQSOJNOF|JNWSNWaTEJUQAEZUJNURNUQZEJea|JNWSNWaTIMTPLOUQEIQJFMbWAEfb|JNWSNWaTIMUREITPLObWOTXOKadW|JNWSNWaTKNbWFKTPNRVMIRUNKRWT|JNWSNWaTKNbWFKVREJTPLOZVJMUQ|JNWSNWaTLOdaEJbWJMUQMRVMIRaV|JNWSNWaTLOeaFJbWJNURNUYRKNRK|JNWSNWbSEJfbKObWGKURLPSLPGWS|JNWSNWbSEJUQKOZUJNSJFMQJOTXO|JNWSNWbSIMaWMQWTKNSJENfbAEbW|JNWSNWbSIMebMQSOLSVOKTXOEJbW|JNWSNWbSIMfbMQbWEIURAEZUQZdU|JNWSNWbSLOSLHOfbEJVRJNUQNUYR|JNWTEJaWBETPNRVMJQUREJXTLObX|JNWTEJaWLOdaGLTPAEPGCLVSOVaR|JNWTEJaWLPeaAEVRJMUQMeQMIRda|JNWTEJaWLPeaAEVRJMZVEJUQNUQZ|JNWTEJbWAEUQNSVOLbfWHLTPLOWT|JNWTEJbWAEVRLPaVGLWSPWSbLOUQ|JNWTEJbWJMebMRVMIRTPAEUQEJWS|JNWTEJbWJMfbMQTOKTXOLSVOIMUR|JNWTEJbWJMfbMRVMIRTPAEUQEIZU|JNWTEJbWJMfbMRVMIRTPAEUQLOWT|JNWTEJbWJMfbMRVMIRTPAEWTEIbW|JNWTEJbWJMfbMRVMIRTPAEWTEJbW|JNWTEJbWJMfbMRVMIRTPAEWTEJUQ|JNWTEJbWJMfbMRVMIRTPAEWTEJZV|JNWTEJbWJMfbMRVMIRTPAEWTLOaV|JNWTEJbWJMfbMRVMIRTPLOWTAEZV|JNWTEJbWJMTPMQURNUYRAEfbLOcY|JNWTEJbWJMTPNRUNKRWSMQVMQJfb|JNWTEJbWJMTPNRUNKRZUFKUNKRXT|JNWTEJbWJMUQNRQJFMfbLOZUMQUN|JNWTEJbWJMUQNRQJFMfbMQVMQJTO|JNWTEJbWJMURNUZJFMfbAEdZKOTK|JNWTEJTOKTXOLSVOAEURNUYRJNRK|JNWTEJTOKTXOLSVOIMOKFOURNUYI|JNWTEJTOLSVOKTXOAEURNUYRJNRK|JNWTEJTPBEbWJMUQNRQJFMWTKNTO|JNWTEJTPJMbWBEUQNRQJFMWTMQVM|JNWTEJTPJMbWMQURNUYRAEfbKOWS|JNWTEJTPJMbWMQURNUYRAEfbLOcY|JNWTEJTPJMbWMQURNUYRAEfbLOWT|JNWTEJTPJMbWMQURNUYRLOfbOTXO|JNWTEJTPJMbWMQWTLOURNUYRAEaW|JNWTEJTPJMbWMRVMIRfbLOWTAEaV|JNWTEJTPJMbWNRUNKRWSAEfbMQVM|JNWTEJTPJMbWNRUNKRWSMQVMQJfb|JNWTEJTPJMbWNRUNKRZUFKUNKRdZ|JNWTEJTPJMbWNRUNKRZUFKUNKRXT|JNWTEJTPJMbWNRUNKRZULOUNFKPL|JNWTEJTPJMUQNRQJFMbWAEWTMQVM|JNWTEJTPJMUQNRQJFMbWBFWTMQVM|JNWTEJTPJMUQNRQJFMbWMQVMQJYU|JNWTEJTPJMVSNWbSMQfbFJbWIMWT|JNWTEJTPJMXTMQTOKTPWGKbXAEXT|JNWTEJTPJMXTMQTOLSVOKTPWAEWT|JNWTEJTPJMXTMRVMIRZVAEVMEIaW|JNWTEJTPJMXTMRVMIRZVAEVMEIcZ|JNWTEJTPJMXTNRUNKRTOLSVOAEbX|JNWTEJTPJMXTNRUNKRTOLSVOFKOF|JNWTEJTPJMXTNRUNKRZUFKUNKRbW|JNWTEJTPLOVRBEbWJMWTMVZJENUQ|JNWTEJTPLOVRBEbWJMWTMVZLHOaV|JNWTEJTPLOVRJMUQMVZJFMQJBFYU|JNWTEJUQAETPLObWNSWNKRVMIRfb|JNWTEJURNUZQAEYUJNVREJTPLOcY|JNWTEJVRBEbWJMTPMVZJFMUQLOQJ|JNWTEJVRJMUQMVZJFMQJBEYUENUQ|JNWTEJVRJMUQMVZJFMQJKOTKGEXT|JNWTEJVRJMUQNUQJFMZJBEYUENUQ|JNWTEJVRLObWBEaVJMVSMVSLHOZJ|JNWTFJTPBFbWJMWTNRUNKRVSMQSO|JNWTFJTPBFVRJMZVMQcZLObWHLeb|JNWTFJTPJMXTMRVMIRbXLOZVEIVM|JNWTFJUQBFTPLObWOTXOKTfbTXZU|"+
        "JNWTFJVRJMZVMQcZLOTPCFbWEJeb|JNWTLObWHLTPNRUNKRVMIRfbEJZV|JNWTLObWHLTPNRUNKRVMIRWTEJTK|JNWTLObWHLUQNRVMIRTPEJWTJMQJ|JNWTLObWHLUQNSWNKRVMIRTKGNfb|JNWTLObWNRUNKRVMIRTKGNfbFKXT|JNWTLObWNRUNKRVMIRTKGNXTHLfb|JNWTLOVREJaVBEbWJMUQNUQJENZQ|JNWTLOVREJbWJMUQNUQJFMZJBEJF|JNWTLOVREJTPJMUQMVZJFMQJBEYU|JNWTLOVREJTPJMUQNUQJFMZJBFYU|JNWTLOVRFJbWJMfbMVZJENURNUYR|JNWTLOVRFJbWJMTPMVZJENUQOSWT|JNWTLPUQPWbJENXTAEfbHLTPEJYU|JNWTLPUQPWbJENXTAETPHLYULOVS|JNWTLPUQPWbJENXTAETPKOfbFKbX|JNWTLPUQPWbJENXTAEYUHLTPLOVS|JNWTLPUQPWbJENXTHLTPAEfbEJYU|JNWTLPUQPWbJENXTHLTPAEfbLObX|JNWTLPUQPWbJENXTHLTPAEYULOVS|JNWTLPUQPWbJENXTHLTPFJfbKOZU|JNWTLPUQPWbJENXTHLTPLOfbAEbX|JNWTLPUQPWbJENXTHLTPLOfbAEYU|JNWTLPUQPWbJFMQJENYUAEVRHLXT|JNWTLPUQPWbJFMQJENYUHLfbAEbW|JNWTNRUNKRVMIRaWFKdaLOaVRaWd|JNWTNRUNKRVMIRaWGKTPLOPLOTXO|JNWTNRUNKRVMIRaWLOTKFOWTHLTK|JNWTNRUNKRVMIRTOLSZURVaRFKRM|JNWTNRUNKRVMIRTOLSZURVaRGKcZ|JNWTNRUNKRVMIRTOLSZURVaRGKRM|JNWTNRUNKRVMIRTOLSZURVaRGKUQ|JNWTNRUNKRVMIRTOLSZURVaRHLRM|JNWTNRUNKRVMIRTOLSZURVaRHLUQ|JNWTNRUNKRVMIRTPEJbWAEfbJNWT|JNWTNRUNKRVMIRTPEJbWAEWTJNaW|JNWTNRUNKRVMIRTPEJZUJNdZAEXT|JNWTNRUNKRVMIRTPLObWEJWTHLTK|JNWTNRUNKRVMIRTPLObWHLWTEJTK|JNWTNRVMIRUNKRTOLSZURVaRGKRM|JNWTNRVMIRUNKRTOLSZURVaRGKUQ|JNWTNRVMIRUNKRTOLSZURVaRHLRM|JNWTNRVMIRUNKRTOLSZURVaRHLUQ|JNWTNRVMIRUNKRTPFKbWEIWSLOSL|JNWTNRVMIRUNKRZUFKUNKRaWGKdZ|JNWTNSVOLSaVKOTKFObWSbfWEJWT|JNXTEJbXJMVSMQSJFMTPAEfbLOWT|JNXTEJTOLSVOKTWPAEaVHLbXLOfb|JNXTEJTPJMWSNWbSMQfbAEaWIMUR|JNXTEJTPJMWSNWbSMQSOKTPWLPfb|JNXTEJTPLOUQOTZUTXVRHLaVLOWS|JNXTLObXHLfbLPVSOVZJENTOKTXO|JNXTLObXHLTPNRUNKRVMIRfbEJWS|JNXTLObXHLTPNRUNKRVMIRfbEJWT|JNXTLObXHLTPNRUNKRVMIRfbEJZV|JNXTLObXHLTPNRUNKRVMIRWSOVZS|JNXTLObXHLTPNRUNKRVMIRWTEITK|JNXTLObXHLTPNRUNKRVMIRWTEJTK|JNXTLObXHLUQNRVMIRTPEJWTJMQJ|JNXTLObXHLUQNSWNKRTKGNVMIRfb|JNXTLObXHLUQNSWNKRVMIRTKGNfb|JNXTLObXHLUQNSWNKRVMIRTKGNXT|JNXTLObXNRUNKRVMIRTKFOWSOVZS|JNXTLObXNRUNKRVMIRTKGNfbHLXT|JNXTLObXNRUNKRVMIRTKGNXTHLfb|JNXTLObXNRVMIRUNKRTKGNfbFKXT|JNXTLOTPOTVSTXSJENWSNWbSIMfb|JNXTLOTPOTVSTXSJENWSNWbSIMSO|JNXTLPbXGLVRLOaVHLWSNWTaEJUQ|JNXTLPbXGLVRLOaVHLWSPWSbLPUQ|JNXTLPbXGLVSDGSJENURNUYRAEeb|JNXTLPbXGLVSDGSJFMUQBFQJENaV|JNXTLPbXGLVSLOSLPGTOKTXOGKWT|JNXTLPbXHLVSDHSJENUQAEZUEJaV|JNXTLPbXHLVSDHSJENURNUYRAEeb|JNXTLPbXHLVSDHSJFMURMVaREJeb|JNXTLPbXNRUNKRVMIRebEJZUJNcZ|JNXTLPbXNRUNKRVMIRTOEJebJMZV|JNXTLPbXNRUNKRVMIRZVEIVMIReb|JNXTLPbXNRUNKRVMIRZVEJVMJQTO|JNXTLPbXNRVMIRUNKRZVEIVMIReb|JNXTLPUQEJVSAEbXIMZUEIaVGLeb|JNXTLPUQEJZUGLbXLOURNUQZJMVS|JNXTLPUQEJZUGLVRLObXHLaVDHeb|JNXTLPUQEJZUHLVSBEaVDHbXNRVM|JNXTLPUQFJVSGLbXLOSLPGTOKTWP|JNXTLPUQGLbXLOZUHLVRIMQSOMaV|JNXTLPUQGLYULObXHLVSOVZJFMQJ|JNXTLPUQGLZUDGbXEJURNUQZJNYU|JNXTLPUQGLZULObXEJURNUQZJMVS|JNXTLPUQGLZULObXHLURNUQZEJYU|JNXTLPUQGLZULObXHLURNUYREJRM|JNXTLPUQGLZULObXHLURNUYRKNRK|JNXTLPUQGLZULObXHLURNUYRKNTK|JNXTLPUQGLZULObXHLVRIMQSOMeb|JNXTLPUQHLVSDHSJFMQJENZUIMbX|JNXTLPUQHLVSDHSJFMQJENZUIMUR|JNXTLPUQHLVSEJbXDHYUIMZVAETO|JNXTLPUQHLZULObXNSWNPWaTKadW|JNXTLPUQNRVMIRaVRaeVKNVSEISJ|JNXTLPUQNRVMIRZUEIUNKRQMRUYR|JNXTLPUQNRVMIRZUKNTOGKbXKTXO|JNXTLPUQNRVMIRZUKNTOGLWSNWbS|JNXTLPUQNRVMIRZURVaRKNRKFXcZ|JNXTLPUQNRVMIRZURVaRKNRKFXUR|JNXTLPUQNRVMIRZURVaRKNRKFXWS|JNXTLPVREJaVHLbXLOWSPWSbGLUQ|JNXTLPVREJbXGLZVLOUQNUQZHLVR|JNXTLPVREJbXHLaVLOWSPWSLGPVS|JNXTLPVREJbXJMTOMVZJKTXOFMeb|JNXTLPVRFJbXJMTOMVZJENOFBKeb|JNXTLPVRGLaVLObXEJWSPWSbHLUQ|JNXTLPVRGLaVLObXHLWSPWSbLPUQ|JNXTLPVRGLbXEJaVAEWSNWTaJNVS|JNXTLPVRHLaVEJbXJMWSNWTaMQfb|JNXTLPVSEJUQGLbXLOSLPGTPAEWT|JNXTLPVSGLSJFMbXLOUQBFQJFMaV|JNXTLPVSHLSJENZVAETOLQWTPWbA|JNXTLPVSHLSJENZVLObXFJUQGLYU|KNVRFKWSNWbSJMRNKRUNLOSLHOaV|KNVRFKWTJMaVEJTOLSVFBKdaMVaR|KNVRFKWTJMTPMVZJENUQLObWAEWT|KNVRFKWTJMTPMVZJENUQLObWBEWT|KNVRFKWTJMTPMVZJENUQLObWOSWT|KNVRGKZVJMUQNUQZMRVMIRWSLOSL|KNVRGKZVJMUQNUQZMRVMIRWTKNTP|KNVRGKZVJMWTDGTPMQdZLObWGLPG|KNVRGKZVJMWTDGUQNUQZMRVMIRTP|KNVSIMUQEIXTLPbXMRTOGKebKTXO|KNVSIMXTEITPMRWTNWUEAJbSIMZV|KNVSIMXTFKTOKTWPNWbSMQUREIaV|"+
        "KNWSNWbSIMXTLPTOMQUREIRMIRVM|KNWSNWbSIMXTLPTOMQUREIRNJMfb|KNWSNWbSLPebGLSOLSVOPTOKFObW|KNWSNWbSLPebGLUQIMYUFKUREIbW|KNWSNWbSLPebJMbWEJfbMQXTGLbX|KNWSNWbSLPebJMbWHLfbMQSOLSWN|KNWSNWbSLPebJMUQMRVMIRbWFJZV|KNWSNWbSLPfbJMbWMQSOEJWTPWaT|KNWTFKbWJMTPMRVMIRWSNWUNKRaT|KNWTFKbWLPVSGLTOKTXOPTWGDTaW|KNWTFKTPBFbWJMfbNRUNKRWTMQVM|KNWTFKTPBFbWJMUQNRQJENVMIRWT|KNWTFKTPBFbWNRUNJbfWIMYUMQWT|KNWTFKTPBFUQNRVMIRXTJMQJFMTO|KNWTFKTPBFVRJMbWMVZJENUQLOWT|KNWTFKTPJMXTMRVMIRbXEIaWAEWS|KNWTGKbWDGVSLOSLHOTPNRUNJbfW|KNWTGKbWJMVRMVZJENebAEUQIMQA|KNWTGKTPLOVRJMPLMVZJFMLSCFSO|KNWTJMTPMRVMIRXTEIUQAEZUEJaW|KNWTJMTPMRVMIRXTFKbXLOZVEIVM|KNWTJMTPMRVMIRXTLOTKFObXGLPG|KNWTJMVRMVaKGNbWEJTPAEPGCLea|KNWTJMVRMVaKGNbWEJZVAETPNRVM|KNWTJMVRMVaKGNeaIMZVEIURNUYR|KNWTJMVRMVaKGNTPDGURNUYREJbW|KNWTLPbWNRUNJbfWEJVSJMYUMQSN|KNWTLPURNUYRPWbSJNRKGWaTEJfb|KNWTLPVRPWRKGNaTIMTPFKXTHLPG|KNWTLPVRPWRKGNbSNWaTJNTOIMZV|KNXTLPVSGKbXDGTOKTXOGKfbKTbX|KNXTLPVSGKbXDGUQNRSOJNZUEJcZ|KNXTLPVSGKZVHLcZLOSLPGTOKTWP|KNXTLPVSIMbXMQTOEIURNUYRJMaV|KNXTLPVSIMbXMRTOGKebKTXODGbX|KOUQGKWSJNSJENZUDGVRIMQSOMUR|KOUQGKWSJNSJENZUOTXOLZcVAEbW|KOUQGKWTLPYUPWbLHOfbDGbWGLcY|KOUQGKYULPWSJMQJEWbLPGfbAEbW|KOUQJNVSOVaKFOWTEJTKGNbWBEZV|KOUQJNVSOVaKGNYUEJZVBEVRFKdZ|KOUQJNVSOVaKGNYUFKZVDGVRLOWT|KOUQJNWSNWaKFObWEJWTOSVOLSea|KOURFKYUJNWTLPVSOMZVPWbQIMQJ|KOURGKYUJNWSNWaTEJUQLPeaPWbL|KOURGKYUJNWSNWaTLPUQPWbLHOfb|KOURGKZUJNWSNWaTEJeaJMbWFJWS|KOURGKZUJNWSNWbSOTXOKTfbTXcZ|KOWTFKTPBFUQJNbWOSVOLbfWHLWT|KOWTFKTPBFURJMYUMQcYEJRMIRUE|KOWTGKTPDGbWOTXOLbfWJNWSNWaT|KOWTGKTPDGUQJNYUEJVRNSaVJNea|KOWTGKTPKNPGCLbWFKWSNWaTJNTP|KOWTJMTKFOaWBFWTGKTPDGdaMRVM|KOWTJMTKFOaWGKWTBFTPDGdaMRUN|KOWTJMTKFOaWGKWTBFTPDGdaOSVO|KOWTJMTKFOaWGKWTBFTPDGeaEJUQ|KOWTJMTKFOaWGKWTBFTPDGUQMRVM|KOWTJMTKFOaWGKWTBFUQOSQJENVO|KOWTJMTKFOaWGKWTBFUROSVOLSda|KOWTJMTKFOaWLPeaHLWTPWaKGNVS|KOWTJMTKFObWGKWTBFTPDGUQEJYU|KOWTJMTKFObWMRUNOSVOLJWSHLYU|KOWTJMTKFObWMRUNOSVOLJXTIMfb|KOWTJMTKFObWMRVMIRUNOSNKSbfW|KOWTJMTKFObWOSVOLbfWMQUREJWS|KOWTJMTKFObWOSVOLbfWMQXTEJUR|KOWTJMTKFObWOSVOLbfWMQXTIMWS|KOWTJMTKFOUQMRVMIRZVEIVMIRcZ|KOWTJMTKFOUREJbWGKZUJNUQNUQZ|KOWTJMTKFOURGKbWMQWSLPSLHOaW|KOWTJMTKFOURGKbWMQWTLPebPWbL|KOWTJMTKFOURMQbWGKWSLPSLHOeb|KOWTJMTKFOURMQbWGKWTLPebPWbL|KOWTJMTKFOVRMVaREJUQBFZUJMQJ|KOWTJMTKGNVRMVaKFObWEJUQDGZV|KOWTOSVOLSTPHLaVLOeaFKUQJNYU|KOWTOSVOLSURJMYUMVaRFJeaJMaV|LOUQHLYULPVSOVZSIMaVKNcYEISO|LOUQHLYULPVSOVZSJMQJENSJFMWT|LOUQJMQJFMWSHLYUMRUNKRVMIRbW|LOUQJMQJFMWTMRVMIRbWEJTPAEWT|LOUQJNWSNWbLGPfbEJbWHLYUAEUR|LOUQJNWSNWbLHOfbKNVRNUYREJbW|LOUQJNWSNWbLHOfbKNVRNUYREJZV|LOUQJNWSNWbLHOfbKNZUNScZEJaW|LOUQJNWSNWbLHOfbKNZUNScZEJUR|LOUQJNWSNWbLHOfbKNZUNScZOTXO|LOUQJNWSNWbLHOfbKNZUNSVRSVRM|LOUQJNWSNWbLHOfbKNZUNSVRSVRN|LOURJMWSEJSLHObWJNfbNUZJFMWS|LOVRJMaVHLWTLPUQPWbLGPQJEUZQ|LOVRJNWTFJTPJMZVMQcZGLPGCLbW|LOWSGLbWKNUQFKZUBFURNUQZKNZU|LOWSGLbWKNURNUYRJMRNLPSLPGXT|LOWSGLbWKNURNUYRJMWTEJTKFOaW|LOWSGLbWKNURNUYRJMWTEJTKFOfb|LOWSGLbWKNURNUYRJMWTEJTKFORN|LOWSGLbWLPSLPGWSJMfbMQSOKTXO|LOWSGLbWLPSLPGXTHLTPJNVREJZV|LOWSHLbWJMUQMRVMIRSNRUYROSXT|LOWSHLbWJMUQMRVMIRSNRVaROSXT|LOWSHLSNJSXTOXVHIMbWEJfbAEWS|LOWSHLSNJSXTOXVHIMbWEJWSKNaW|LOWSHLSNJSXTOXVHIMbWMRUNKRWS|LOWSHLSNJSXTOXVHIMURMVaREJYU|LOWSHLSNJSXTOXVHIMZVEIURAEbW|LOWSHLSNJSXTOXVHIMZVEIURAEcZ|LOWSHLSNJSXTOXVHIMZVMQVSQZcV|LOWSHLUQKNZUNWaKFObWLPeaGKWT|LOWSHLURJNSJEUYRLPbWOTXOKTZU|LOWSHLXTOXSNJSVHIMbWEJUQMRZV|LOWTJMbWEJWSAESLGWaTCGTPMRUN|LOWTJMbWEJWSBESLGWaTJNfbDGbW|LOWTJMbWEJWSBESLGWaTJNfbDGUR|LOWTJMbWEJWSBESLGWaTJNfbMRVM|LOWTJMbWEJWSBESLGWaTJNTPDGXT|LOWTJMbWEJWSBESLGWaTJNTPMRVM|LOWTJMbWHLTPMRUNKRVMIRWTEJTK|LOWTJMbWMRUNKRVMIRTKGNebHLWS|LOWTJMbWMRUNKRVMIRTKGNfbFKXT|LOWTJMbWMRUNKRVMIRTKGNfbHLWT|LOWTJMbWMRVMIRUNKRTKGNfbFKXT|LOWTJMUREJbWJNfbNUZJFMTPMQWT|LOWTJMUREJbWMQTPOTXOKTWSTXRM|LOWTJNbWNRUNKRVMIRTKGNXTCGfb|LOWTJNbWNRVMIRUNKRTKGNebFKWS|LOWTJNVRFJTPJMUQNUQJENZQAEdZ|LPUQGLYUDGcYJMQJFMWTPWbSBFfb|LPUQGLYUDGVRJNZVEJcYLORMIRVM|LPUQHLWSKNbWFKZUKOURNUQZGKYU|"+
        "LPUQHLYUKOVRJMQJFVaRDHeaOSWN|LPUQHLYUKOWTPWaKFObWLPeaGKWT|LPUQJNWTPWbJENXTHLTPAEfbLObX|LPURJNWSNWaTPWbSKNRKGWebFKbS|LPVRHLZVLOWTPWbLGPfbKObWFKWS|LPVRJMUQMVaREJZUJMQJFVWTPWbZ|LPVSHLXTKOTKFVaRJMZVMQcZLOea|LPVSHLXTKOTKFVZSGKSNKRUNJSWN|LPVSHLXTKOTKFVZSGKURKOSNJSWN|LPVSHLXTKOTKFVZSGKURLOSLPGWS|LPWSGLSOKTXOLSVOJMbWMQUREJfb|LPWSGLSOLSVOKTXOIMZVMRVMJZcV|LPWSIMUREISOKTXOGLYULSVOMVaR|LPWSJMSOKTXOMQbWEJfbJMVRMVZS|LPWSJMSOKTXOMQbWEJWTPWaTJNUR|LPWSJMSOKTXOMQUREJbWJMfbGLWS|LPWSJMSOKTXOMQUREJbWJMfbGLYU|LPWSJMSOKTXOMQUREJRMIRVMGLaV|LPWSJMSOKTXOMQUREJRMIRVMJNMI|LPWSJMSOKTXOMQURFJbWJMWSGLYU|LPWSJMUQEJZUKNcZNWbSBEfbFKSN|LPWSJNSJFMaWMQWTPWbSEJfbKNbW|LPWSJNSJFMaWMQWTPWbSIMSOKTXO|LPWSJNSJFMXTPWbSHLfbBFbXLPSN|LPWSJNSJFMXTPWbSMQURHLfbBFbW|LPWTPWbSGLSOKTXOLSVOIMZVMRVM|LPWTPWbSIMfbKNbWMRVMJQSJENaV|LPWTPWbSIMfbMQSOKTXOEIbWJMWT|LPWTPWbSIMUQEIZUBEURJNSJEUQZ|LPWTPWbSIMUQEIZUHLebKNcZNWbS|LPWTPWbSIMUREISOKTXOGLYULSVO|LPWTPWbSIMUREISOKTXOMQfbJMaW|LPWTPWbSIMXTKNTPNWaTMQfbJNbW|LPWTPWbSJMXTMQTPIMSOKTPWFKUR|LPWTPWbSJMXTMQTPIMSOKTPWFKVR|LPWTPWbSJNSJENXTAEVREJTPHLfb|LPWTPWbSKNaWGLXTFKTPKOPGCLUR|LPXTKOTKGNVSFKaVHLbXLOSLPGeb|LPXTKOTKGNVSHLaVLOSLPGbXJMWT|LPXTKOTKGNVSHLaVLOSLPGeaJMWS|IMUQEIVSKOaVFKZUJNQJNEWTIMTPEIUR|IMUQEIVSKOaVFKZUKNURNUQZMQYUGKWT|IMUQEIVSKOaVFKZUKNVROVRaBEXTMRTP|IMUQEIVSKOYUOVZSBEXTFKTPKNaVNRUN|IMUQEIWSMRVMIRbWAEfbLOSLGPWSKOSL|IMUQEIWTLPbWMRVMIRTOKTXOAEfbGKZV|IMUQEIWTMRVMIRZVAEVMEIcZIRZVJMQJ|IMUQEIYUAEVSKNaVGKeaLPXTHLURNUTO|IMUQEIYUKNcYFKWTBEaWLPeaGLTOKTXO|IMUQEIYUKNVRMVaKFOWTGKTPDGZVBFea|IMUQEIYUKNVRMVaKFOWTGKZVBFdZLPUR|IMUQEIYUKNWSNWaTBEURFKZUKNRKGNUR|IMUQEIYUKNWSNWaTLOTKGNVSNWbSFKXT|IMUQEIYUKNWSNWaTLOTKGNVSNWbSFKZV|IMUQEIYULOURGLZUDGcYLPWTPWbLGPfb|IMUQEIZUAEURKNRKGNVRMVaKFOeaDGWT|IMUQEIZUAEURKNRKGNVRNUQZJNXTEJTP|IMUQEIZUAEVRMVaRLOWTJNcZOSbWSbfW|IMUQEIZUAEVSLOSLHOURMVaROSWNJSea|IMUQKNVRMVaKGNZUDGURNUQZFKWTJNea|IMUQKNWSNWaTEIZUBEURFKYUKNRKGNUR|IMUQKNWSNWaTLOTKGNbWHLebDHYUFKWT|IMUQKNWSNWaTLOTKGNbWHLWTMRVMEIea|IMUQKNWSNWaTLOTKGNbWHLXTLPWSPWSb|IMUQKNWSNWbSFKYUJNQJNWaTENTPAEXT|IMUQKNWTLPYUPWbSNWaTFKTOKTXOEIfb|IMUQKNWTNSVOLSaVGLVOLSeaDGaVGLVO|IMUQKNXTLPbXEITOGKZUKTXOMRVMIRcZ|IMUQKNXTLPbXEITOMRVMIROKFOZVCFVM|IMUQKNXTLPVSMRTOGKbXKTXORVaKJMQJ|IMUQKNXTNSVOLSWNJSQJENYUAETPEJUQ|IMUQKNXTNSWNJSVOLSQJENbXAETPEJYU|IMUQKNYUNSWNJSQJENVOLSbWSbfWAEZV|IMUQLPWTPWaTKOTKGNbWHLWTCGTOLSVO|IMUREIWSKObWFKWTLPSLPWaTGWeaHLaT|IMUREIWTJNbWNUZJFMfbAEdZMQTPIMWS|IMUREIWTLOTPAEbWOTXOKTZUFKUQKNRK|IMURMQRMJNMIEJWTLPYUPWaTHLbWAETP|IMURMQRMJNMINRVMQJYUJNUQLOWTEJaV|IMURMQRMJNMINRVMQJYULOURJMWTMVZL|IMURMQRMLPWSEISOIRVMKTXOJNMIAEbW|IMURMQRMLPWSHLSOLSVOKTXOEIZVIRVM|IMURMQRMLPWTPWbSHLMIJNSJENfbAEbW|IMURMQRMLPWTPWbSJNSJENMIHLfbNRVM|IMVRMVaRLPZVGLWTPWbSKNRKFOURLPSL|IMVSEIWTKOTKFVZSMQXTQZcVIMbWGKTP|IMVSEIWTKOTKFVZSMQXTQZcVIMTOGKOF|IMVSKNXTMQaVEITPFKWTNWTaAEbWJNUR|IMVSKNXTMQbXFKaVJMSJMFTPEJfbAEea|IMVSKNXTMQTPFKaVKObXGKPGCLebJMSJ|IMVSKNXTMQTPFKbXJMSJMFUREJRMJNMI|IMVSMQWTKNTPNWbSJMfbFKbWEJaVJNSJ|IMWSLPbWGLUQKNVRMOWTPWaREIZVLOfb|IMWSLPbWGLUQKNVRMOWTPWaREIZVLPfb|IMWTMQTPJNbWEJWTAETOLSVOKTPWFKaV|IMWTMQTPJNbWNRUNKRVMQJaVJMWSEJYU|IMWTMRUNKRVMJQTPEJbWLOWTAETKFOfb|IMXTLOUROXRIHLYULPUQGLZUJNcYEJUR|IMXTLOUROXRIJNYUHLUQLPcYEJZUGLVR|IMXTLOUROXRIJNYUHLUQLPWSNWbSEJfb|IMXTMQTPJNWSNWbSEJfbAEaWEIURJNSJ|IMXTMQTPJNWSNWbSEJfbAEaWKObXEIUR|IMXTMQTPKNVSFKbXJMSJMFUREIfbLOZV|IMXTMRUNKRVMJQTPEJWTLOTKFObWJNWS|IMXTMRUNKRVMJQWSLPTOEJYUAEUREIZV|IMXTMRVMJQTPEJbXJNWTAEaVNRVMQJUQ|JMUQEJWTAETOKTXOLSVOGLaWLSWNJSQA|JMUQEJWTLPTOKTXOMRVMIRbWAEfbJNZV|JMUQEJZUKOURFKWSLPSLHObWBEWSDHSL|JMUQFJWSLPZUJNSJMFURHLbWLOYUEJcY|JMUQFJWSLPZUJNSJMFURHLYUEJcYLORM|JMUQFJYULPURHLZUDHWSJNSJMFbWEJcY|JMUQLOQJFMWTEJbWBFTPMQWSAESLHOfb|JMUQLOQJFMWTMRVMIRbWEJTPAEWTEIfb|JMUQLOQJFMYUMRUNKRVMIRWTEJTKGNbW|JMUQMRVMIRWSEJbWAEfbLOSLGPWSKOSL|JMUQMRVMIRWSEJbWBEfbLOSLHOZUJMQJ|JMUQMRVMIRWSEJSOLSZVSZdEAJXTHLTP|JMUQMRVMIRWSLOSLHObWEJWTDHTPJMQJ|JMUQMRVMIRWTEJbWAETPEIWTJMQJFMZU|"+
        "JMUQMRVMIRWTEJbWLOZUJNdZAEaVRaWd|JMUQMRVMIRWTEJZVAEVMEIcZIRZVJMQJ|JMUQMRVMIRWTKNbWFKTPLOZUEJWTAEaV|JMUQMRVMIRWTLOTPEJbWOTXOKTZVJMQJ|JMUREJWSKObWAEWTLPTKGWaTPWebFKbS|JMUREJWSKObWFKYUMQebJMWTLPSLPWbS|JMUREJWSKObWGKWTLPSLPWaTHOfbAEda|JMUREJWSKORNAEbWFKZUKRUNLPSLJZcV|JMUREJWSKORNAEbWLPSLJbfWHOVRMVZL|JMUREJWTJNbWNUZJFMfbMQdZIMTOLSVF|JMUREJWTJNbWNUZJFMfbMQdZKNTPNRVM|JMUREJWTLObWJNfbNUZJFMdZMQYUAEUR|JMUREJWTLObWJNTPNUZJFMWTMQfbAEbW|JMUREJWTLObWMQTPJNWTNUYRAEcYFJRM|JMUREJWTLObWMQTPJNWTNUYRAEfbEJRM|JMUREJWTLObWMQWSJMSLGWaTAETPCGfb|JMUREJWTLPTOKTXOMQRMIRVMJNMIGLaV|JMURFJWSKOaWMQWTJMTKGWbSLPebHLbW|JMURFJWSKOaWMQWTJMTKGWbSLPRNEJNE|JMURFJWSKOaWMQWTJMTKGWbSLPYUHLfb|JMURFJWSKObWMQebJMYUGKWTLPSLPGTO|JMURKNRKGNVSEJSOLSaVCGVOFKOFJCWS|JMURKNRKGNVSEJSOLSaVDGVOGLeaLSaV|JMURKNRKGNWTMRVMIRZUEJbWAEdZLPaV|JMURKOWTLPTKGUZJENXTPWbJFMYUHLfb|JMURLOWTEJbWAEfbMQTPHLWSOTXHKNRK|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRM|JMURLOWTEJbWAEfbMQTPJNWTNUYRFJaW|JMURLOWTEJbWAEfbMQTPJNYUGLPGCLRM|JMURLOWTEJbWAEfbMQYUJNRMIYVSOVZA|JMURLOWTEJbWJNTPNUZJFMWTMQfbAEbW|JMURLOWTEJbWJNTPNUZJFMWTMQfbAEdZ|JMURLOWTEJbWJNTPNUZJFMWTMQfbAEVR|JMURLOWTEJbWMQRMIRVMGLMILPYUHLaV|JMURLOWTEJbWMQTPOTXOKTRMIRVMGKMI|JMURLOWTEJbWMQWSJMSLGWaTAETPCGfb|JMURLOWTEJbWMQWSJMSLGWaTAETPEJZU|JMURLOWTEJbWMQWSJMSLGWaTHLZUQSTP|JMURLOWTGLTPCGbWOTXOLbfWKOWSGLPG|JMURMQVSKOaVEJWTLPTKGWbSCGYUGLRN|JMURMQVSKOaVEJWTLPTKGWbSCGYUJMXT|JMVSEJWTLPTOKTXOGKUQKTbXBEXODGeb|JMVSFJaVMQeaJNSJENURNUYRKOWSAERN|JMVSFJWTMQSNKRUNJSTOSVZSLPbWEJaV|JMVSFJWTMQTOKTXOIMSNLSNWJNURMVaK|JMVSKOaVFKUREJWTKNTKNWbSGWebBFbS|JMVSKOaVMQeaEJWTJMTKGWaTLPTOFKOF|JMVSKOUQOVQJENaKFOYUGKWTLPeaPWbL|JMVSLPSOKTXOMQUREJaVGKeaKTRNJSVX|JMVSMQaVIMUREIWTLPSNPWbSKOSLHOfb|JMVSMQaVIMWTMRUNKaeVEJYUAETOEIUR|JMVSMQUREJRNKRSOLSWEAJZUQZdEFJEN|JMVSMQURKNRKFVaREJeaLOaVBFWTFKTP|JMVSMQURKNRKFVaREJeaLOaVBFWTGKTP|JMVSMQURKOaVEJWTJMTKGWbSLPdaAEaW|JMVSMQURKOaVEJWTJMTKGWbSLPebHLSN|JMVSMQURKOaVEJWTJMTKGWbSLPfbAEbW|JMVSMQURKOaVEJWTJMTKGWbSLPfbHLbW|JMVSMQURKOaVEJWTJMTKGWbSLPfbHLea|JMVSMQURKOaVEJWTJMTKGWbSLPSOCGVS|JMVSMQURKOaVEJWTJMTKGWbSLPSOPTOL|JMVSMQURKOaVFKWTKNTKNWbSGWebEJbS|JMVSMQURKOaVGKWTLPSLPGTOKTXOEJbW|JMVSMQURKOSNOSNKGUWNCGYRLOcYEJNE|JMVSMQURLPSOKTXOEJZUQZcVGLdZLSWE|JMVSMQWTEJTOKTXOJMURMVaRAEeaEJSN|JMVSMQWTKOTKFVaRLObWHLeaCFWTLPTK|JMVSMQWTKOTKFVZSQZdUIMbWMQXTQZcV|JMWSEJaWKNeaMQSOLSVOJMWSNWbSGLfb|JMWSEJaWKNXTMRVMIRbXGKZVRaeVLPda|JMWSEJaWMQeaJMWTMRUNKRVMQJaVJMYU|JMWSEJbWAEfbMRUNKRVMJQXTIMYUEITO|JMWSEJbWAEfbMRUNKRVMJQXTLPZVGKbX|JMWSEJbWAEWTMRUNKRVMJQTPIMfbFKbW|JMWSEJbWKOUQFKZUJNSJMFWSKNSJFMQJ|JMWSEJbWKOUQGKZULPSLPGXTAETOKTWP|JMWSEJSOKTXOLSVOMQbWAEfbJMURMVaR|JMWSEJSOKTXOLSVOMQURGLRNJSOVAEVR|JMWSEJSOLSVOKTXOAEURMVaRJMOKGUZA|JMWSEJSOLSVOKTXOAEURMVaRJNRKGNbX|JMWSEJSOLSVOKTXOBEUQGLaVLSVODGbW|JMWSEJSOLSVOKTXOBEZVMRVMJZcVEJVS|JMWSEJSOLSVOKTXOGLaWLSWEAJbWDGZV|JMWSEJSOLSVOKTXOGLaWLSWEAJUQMRZU|JMWSEJSOLSVOKTXOMQURJMaVAEbWGKWT|JMWSEJURKOaWFKWTKNTKNWbSGWebBFbS|JMWSEJURKOYUMQcYJMbWFKRNKRUNBFXT|JMWSFJbWMQWTJNSJENTOLSVFBKURNUYR|JMWSFJbWMQWTJNSJENTPNRUNKRVMQJfb|JMWSKOaWFKUQMRVMIRWTOVZSBFSNRVbW|JMWSKOaWFKWTEJbWBFUQMRVMOVZSIRTO|JMWSKOaWFKWTMRUNKaTKGWbSLPeVHLYU|JMWSKOaWGKWTEJTPDGURMQZUQZdUJNSJ|JMWSKOaWGKWTLPSLPGTOKTXOEJbWMQUR|JMWSKOaWMQeaEJWTJMTKGWaTLPTOFKOF|JMWSKOaWMQUREJWTJMTKGWbSLPebHLSN|JMWSKOaWMQWTEJTKGWbSLPfbCGbWHLVR|JMWSKOaWMQWTEJTKGWbSLPfbJMbWFKUR|JMWSKOaWMQWTEJTKGWbSLPURCGeaJMfb|JMWSKOaWMQWTEJTKGWbSLPURJMfbAEbW|JMWSKOaWMQWTEJTKGWbSLPVRJMSNMVZS|JMWSKOaWMQWTFKTPEJURJMbWCFfbOTXO|JMWSKOaWMQWTGKTPDGUREJYUBEbWJNSJ|JMWSKOaWMQWTGKURLPSLPGTOKTXOEJbW|JMWSKOaWMQWTLPTKGWbSEJfbJMSOAEea|JMWSKOaWMQWTLPTKGWbSEJURCGSOGLVS|JMWSKObWEJUQFKZUJNSJMFURLPWTPWaT|JMWSKObWEJUQGKZULPSLPGXTAEURKNRK|JMWSKObWEJUQMRVMOVaRJNRKIReaGNZV|JMWSKObWEJURFKWTLPSLPWaTGWeaHLaT|JMWSKObWEJURFKYUMQcYJMRNKRUNBEWT|JMWSKObWFKUQBFQJFMfbMQYUEJURJMSN|JMWSKObWFKUQBFQJFMfbMQYUIMSNKYVS|JMWSKObWFKUQBFQJFMYUMQfbEJURJMSN|JMWSKObWFKUQBFQJFMYUMRUNKRVMIRfb|"+
        "JMWSKObWFKUQEJZUJNSJMFURLPWTPWaT|JMWSKObWFKUQMRVMIRSNRUYROSNJEUWN|JMWSKObWFKUQMRVMIRSNRVaROSXTSJTP|JMWSKObWFKUREJWTLPSLPWaTGWebBFbS|JMWSKObWFKUREJYUMQcYJMRNKRUNBEWT|JMWSKObWFKUREJYUMQcYJMRNKRUNBFXT|JMWSKObWFKUREJYUMQcYJNSJBFRMIRUN|JMWSKObWFKUREJYUMQcYJNSJBFWTFMRN|JMWSKObWFKUREJZUMQRMIRVFCJaVQZdU|JMWSKObWFKWTLPSLPWaTGWeaKNaTMRVM|JMWSKObWGKUQLPSLPGQJFMWSEJYUMQfb|JMWSKObWMQWTEJTKGWaTLPeaPWaTAEfb|JMWSKObWMQWTLPTKGWaTPWebHLbSLPVR|JMWSKOUQEJZUGKaWKNVRMVSZBEWTOSTP|JMWSKOUQGKQJEWaTAETPDGYUEJeaBEUQ|JMWSKOUQGKQJEWaTAEYUEJURLPeaPWbL|JMWSKOUQGKQJEWaTIMTPCGVSOVZSMRda|JMWSKOUQGKQJEWaTIMTPDGdaKNbWOSVO|JMWSKOUQGKQJEWaTIMTPDGdaMQbWOSVO|JMWSKOUQGKQJEWaTIMZUOSVOLSdaAEbW|JMWSKOUQGKQJEWaTIMZUOSVOLSeaKNcZ|JMWSKOUQGKQJEWaTLPYUPWbLHOfbAEbW|JMWSKOUQGKQJEWbSIMaWAEWTLPSLPGYU|JMWSKOUQGKQJEWbSIMaWAEYUMQURLPSL|JMWSKOUQGKQJEWbSIMaWMQWTLPSLPGfb|JMWSKOUQGKQJEWbSIMYUMQaWAEWTLPSL|JMWSLOSLHOUREJaWAEWSGLbWLPSLPGfb|JMWSLOSLHOUREJaWJNWSNWbLGPfbCGbW|JMWSLOSLHOVRMVZLGPXTPWbSCGfbGLbW|JMWSLPSOKTXOMQaWEJWTPWbSJMfbAEbX|JMWSLPSOKTXOMQaWEJWTPWbSJMfbFJUR|JMWSLPSOKTXOMQbWEJfbJMbXMRUNFKOF|JMWSLPSOKTXOMQbWEJfbJMbXMRVMIRUN|JMWSLPSOKTXOMQbWEJfbJMVRMVZSQZcV|JMWSLPSOKTXOMQbWEJWTPWaTJMfbGLea|JMWSLPSOKTXOMQUREJaWJMbXFJebGKOF|JMWSLPSOKTXOMQUREJbWJMfbGLWSCGZU|JMWSLPSOKTXOMQUREJbWJMYUAEWSGLfb|JMWSLPSOKTXOMQUREJbWJMYUGLWSCGeb|JMWSLPSOKTXOMQUREJRMIRVMJNMIGLaV|JMWSMRUNKRVMIRbWLOSLHOfbEJWSOVZS|JMWSMRUNKRVMIRbWLOSLHOWTFKfbRVZL|JMWSMRUNKRVMIRZUFKUNKRXTEJTOBEaW|JMWSMRUNKRVMIRZUFKUNKRXTGKbXLOSL|JMWSMRUNKRVMIRZUFKUNKRXTGKSNLONU|JMWTEJbWAETPMQWSLOSLHOfbJNURNUYR|JMWTEJbWJNfbMRVMIRTPAEUQLOWTRUYR|JMWTEJbWJNURNUZJFMVSLOSLHOdZAEfb|JMWTEJbWLOfbMQTPOTXOKTURTXRMIRVM|JMWTEJbWMQURLOTPJNWTNUYRAEfbFJRM|JMWTEJbWMQWSAESOLSVOGLaVLSVOIMfb|JMWTEJbWMQWSLPSOPWaTAETPKTPWHLWS|JMWTEJTOKTXOLSVOMQbWGLWSBEURJMfb|JMWTEJTOKTXOLSVOMQbWJMfbAEWSEJbX|JMWTEJTOKTXOLSVOMQbWJNURNUYRAEfb|JMWTEJTOLSVOKTXOBEURMVaRJMZVGLdZ|JMWTEJTOLSVOKTXOBEZVMRVMJZcVFJVS|JMWTEJTOLSVOKTXOMQbWAEfbJMURMVZS|JMWTEJTPAEURKOaWOTXOLSWNJSVOMVZS|JMWTEJTPLObWOTXOKTWSTXURAEfbMQRM|JMWTEJTPMQbWJNVSFJaVJMSJMFfbIMea|JMWTEJTPMQbWLOWSAESLHOfbJNbWEJVR|JMWTEJTPMQXTLObXJNURNUYRAEfbEJRM|JMWTEJUQMRVMIRTPLObWJNWTRUYRNUQM|JMWTFJUQLPZUPWaTCFURKNRKGNbWMRVM|JMWTFJUQLPZUPWaTCFVSMRUNKRTOGLbW|JMWTFJUQLPZUPWaTKNURNUYRHLbWGKea|JMWTKNaWNSWNMRVMIKeaEJTPLOURBEZU|JMWTKNaWNSWNMRVMIKTPEJUQJNZUNRUN|JMWTKNTOLSVOEJbWGLfbLSURNUWEAJYR|JMWTKNTOLSVOEJURNUYRMVZSJMbWAEfb|JMWTKNTPMQXTEJaWAEWSNWTaJNbWEJUR|JMWTKNVRMVaKGNbWEJTPIMPGDKXTMQfb|JMWTKNVRMVaKGNbWEJTPIMPGDKXTMRfb|JMWTLObWEJfbAETPMRVMJQWTEJURJNYU|JMWTLObWEJTPMQURJNfbNUYRAEcYHLWS|JMWTLObWEJTPMQWSAESLHOfbKNaWGLPG|JMWTLObWEJWSAESLGWaTHLTPKOPGCLfb|JMWTLObWEJWSAESLGWaTHLURMQfbLObW|JMWTLObWEJWSMQSLGWaTJNURNUYRHLTO|JMWTLObWMQWSEJSLGWaTHLURLOfbAEbW|JMWTLObWMRUNKRVMIRTKGNZUNSUNSJXT|JMWTLObWMRVMIRUNKRTKGNebFKWSNWbS|JMWTLOUREJbWJNTPNUZJFMWTMQfbAEdZ|JMWTLPTOKTXOMQbWFJWTPWaTJMfbEJbW|JMWTLPTOKTXOMQUREJRMIRVMJNMIGLaV|JMWTLPUQPWQJENbJFMfbHLYUMQbWAEUR|JMWTLPUQPWQJENbJFMXTAEfbMQVRCFTP|JMWTMQTPEJXTJMTOLSVOKTPWHLWSFKbW|JMWTMRUNKRVMIRTOLSZURVaRGKRMHLea|JMWTMRUNKRVMIRTOLSZURVaRGKRMKOMI|JMWTMRUNKRVMIRTOLSZURVaRGLRMFKMI|JMWTMRUNKRVMIRTOLSZURVaRHLRMGKea|JMWTMRUNKRVMIRTOLSZURVaRHLRMLOea|JMWTMRUNKRVMIRTOLSZURVaRHLRMLOMI|JMWTMRUNKRVMIRTOLSZURVaRHLRMSVMI|JMWTMRUNKRVMIRTOLSZURVaRHLUQLOYU|JMWTMRUNKRVMIRZUFKUNKRTPLObWEJWT|JMWTMRVMIRUNKRaWFKWSRVSNKRZSEJea|JMWTMRVMIRUNKRTOLSZURVaRGKRMCGea|JMWTMRVMIRUNKRTOLSZURVaRGKRMHLUQ|JMWTMRVMIRUNKRTPEJbWAEWTLOTKGNfb|JMXTLObXEJfbMQTPJNURNUYRAEWSEJSL|JMXTLPbXMQTOKTXOGKWTPWaTEJfbAEbX|JMXTLPbXMQVSKNSJENURNUYRHLaVFKeb|JMXTLPUQGLQJFMbXEJVSMQebJNSJLOYU|JMXTLPUQHLQJFMVSMQSNKRTOLSWUIMbW|JMXTLPUQMRVMIRZURVaRKNRKFXURGKcZ|JMXTLPVSMQaVEJeaJNSJFMVSKOTKGNSJ|JNUQEJWTAETPLObWNSWNKRVMIRaWGKfb|JNUQEJWTAETPLOVRNUYRJNZVNUQZFJbW|JNUQEJWTLPbWGLZULOURNUQZJMYUMQUR|JNUQEJWTNRVMIRbWLOfbAETPOTXOKTPL|JNUQEJYUAEVRIMRINSWNKYbWJNZVEJVR|JNUQEJZUAEWTLOVROSaWGLTPDGQMJZcO|"+
        "JNUQEJZULPURNUQZIMYUMQWSKNbWGLeb|JNUQEJZULPVRGLRMIRWTPWbSNWUPJNaT|JNUQKOWTGKQMIRVMEIZVIRVMAEMINRcZ|JNUQKOWTNRTKGNVMIRbWFKWTLOfbHLTP|JNUQLOWSNWbLHOYUOTXOKTURTXfbGLbW|JNUQLOWTEJbWAETPNRVMIRWTJNZUOSfb|JNUQLOWTEJZUNSVRJNcZSWbLGWaTIMQS|JNUQLOZUEJWTNSVRJNTPAEcZEJaVHLXT|JNUQLOZUEJWTNSVRJNTPAEcZIMQABEAJ|JNUQLPVSEJSOKTXOAEWSNWbSGKaVKTSN|JNUQNRVMIRWSEJbWAEfbLOSLHOWSOVZS|JNUQNRVMIRWSEJbWBEfbLOSLHOZUJMQJ|JNUQNRVMIRWSEJbWBEZULOSLHOUNJbfW|JNUQNRVMIRWSEJbWLOSLHOWSOVZSKNSO|JNUQNRVMIRWSEJSNJSZVSZcMAEMIEJXT|JNUQNRVMIRWSEJSOLSaVRadEAJeaHLbW|JNUQNRVMIRWSLOSLHObWGLWTKNTKFOfb|JNUQNRVMIRWSLOSLHObWGLZUKNWTLPTK|JNUQNRVMIRWSLOSLHObWKNfbGLWTLPTK|JNUQNRVMIRWSLOSLHObWKNWTGLTKNGfb|JNUQNRVMIRWTEJbWLOaVRaeVAEVRJNZV|JNUQNRVMIRWTEJbWLOfbAEaVRaeVGLQM|JNUQNRVMIRWTEJbWLOTPAEWTJNZUOSfb|JNUQNRVMIRWTEJbWLOTPJNWTAEZUOSfb|JNUQNRVMIRWTEJbWLOTPOTXOKTZVJMQJ|JNUQNRVMIRWTEJbWLOZVBEVMOSWNKIaV|JNUQNRVMIRWTEJTPAEbWEIfbJMQJFMXT|JNUQNRVMIRWTEJTPAEbWJNZULOWTOSdZ|JNUQNRVMIRWTEJTPLObWJNZUOTXOKTcZ|JNUQNRVMIRWTEJZVAEVMEIcZIRZVJMQJ|JNUQNRVMIRWTEJZVJMQJFMVSLOSLGWbS|JNUQNRVMIRWTKNTPFKXTLObXCFZUFJaV|JNUQNRVMIRWTKNTPFKXTLObXHLZUEJdZ|JNUQNRVMIRWTKNZUFKcZLObWBFfbNSWN|JNUQNRVMIRWTLObWEJfbJNTPAEWTEIQM|JNUQNRVMIRWTLObWEJTPAEWTJNZUOSdZ|JNUQNRVMIRWTLObWEJTPAEWTJNZUOSfb|JNUQNRVMIRWTLObWEJTPJNWSNWaTAEfb|JNUQNRVMIRWTLObWEJTPJNWTAEZUOSfb|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUaV|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUQM|JNUQNRVMIRWTLObWEJTPOTXOKTWSTXfb|JNUQNRVMIRWTLObWEJTPOTXOKTWSTXZU|JNUQNRVMIRWTLObWEJTPOTXOKTWSTXZV|JNUQNRVMIRWTLObWEJZVJMQJFMTPAEVS|JNUQNRVMIRWTLObWEJZVJMQJFMTPAEWT|JNUQNRVMIRWTLObWKNTKFOWTGKfbDGTP|JNUQNRVMIRWTLOTPEJbWJNWTRUYRNUQM|JNUQNRVMIRWTLOTPHLbWEJfbJMQJFMWS|JNUQNRVMIRWTLOTPHLbWEJWTJMQJFMZU|JNUQNRVMIRWTLOZUHLUNKRTKGNaVRaeV|JNUQNRVMIRWTLOZUHLUNKRTKGNbWLOWT|JNUQNRVMIRZUKNdZLOWTFJTKJMQSGdUN|JNUQNRVMIRZUKNdZLOZVEIVMIRcZBEWT|JNUQNRVMIRZUKNWTFKTPLObWHLWTCFfb|JNUQNRVMIRZULOUNKRdZFKZUKNcZCFZV|JNUQNRVMIRZULOUNKRdZFKZUKNWTEJTK|JNUQNRVMIRZULOUNKRWTHLTKGNaVRaeV|JNUQNRVMIRZVEIVMIRWTKNbWAEdZFKZU|JNUQNRVMIRZVEIVMIRWTKNdZAEbWFKZU|JNUQNSWNKRVMIRZVEIVMIRcZAEZVEIVM|JNURNUYREJWSKObWJMWTMQTKGUcYLOSL|JNURNUYREJWTAETPJNRMIRVMLOMINRbW|JNURNUYREJWTJMTOLSVOKTXOMVZSFKOF|JNURNUYREJWTJMTPLObWOTXOKTcYAEWS|JNURNUYREJWTJNRMIRVMAEMILOTPNRbW|JNURNUYREJWTJNRMIRVMAEMILOTPNRcY|JNURNUYREJWTJNRMIRVMAEMINRcYEJTP|JNURNUYREJWTJNRMIRVMAEMINRTPLObW|JNURNUYREJWTJNRMIRVMAEMINRTPLOcY|JNURNUYREJWTJNRMIRVMAETPEIZVIRVM|JNURNUYREJWTLObWJMfbMQTPAEWSHLcY|JNURNUYREJWTLObWJMTPAEfbOTXOKTWS|JNURNUYREJWTLOTPAEbWJNWTNUZQEJfb|JNURNUYREJWTLOTPJMbWOTXOKTWSTXcY|JNURNUYREJWTLOTPJMbWOTXOKTWSTXfb|JNURNUYREJWTLOTPJNbWNUZQAEWTEJfb|JNURNUYREJWTLPTOKTXOJMVSMVaRAEea|JNURNUZQEJWSKObWGKYUBEebDGcZKNUR|JNURNUZQKNVRNUQZEJaVIMYUMQWSLPUR|JNURNUZQKNVRNUQZFKaVEJWSLOSLHObW|JNURNUZQLOWSGLYUOTXOKTbXDGXOIMQJ|JNVREJaVBEWTJMTPLOUQNUYRHLQJEUZQ|JNVREJaVJMUQNUQJFMZJBFVSFMWTLOSL|JNVREJaVJMXTMQbXLOfbGLTPAEPGCLXT|JNVREJaVJMXTMQbXLOfbGLTPBEPGCLXT|JNVREJaVJMXTMQbXLOfbGLTPOTPGTadW|JNVREJaVJMXTMQTPFJWTJMbXLOdaAEaW|JNVREJaVJMXTMQTPFJWTLOdaOXRMIRVO|JNVREJaVJMXTMQTPLOWSNWbLHOeaAEfb|JNVREJaVLOWTBETPJMUQNUYRHLQJEUZQ|JNVREJaVLOWTBEUQNUYRJMQJEUZQIMQJ|JNVREJaVLOWTHLTPDHUQNUYRBEbWOTXO|JNVREJaVLOWTJMUQNUQJFMZJBEbWENVR|JNVREJaVLPeaGLVSLOSLPGXTJMZVMQcZ|JNVREJaVLPVSGLZVLOSLPGeaJMUQNUQZ|JNVREJaVLPVSGLZVLOSLPGUQNUQZHLWT|JNVREJaVLPVSGLZVLOSLPGVSGLUQNUQZ|JNVREJaVLPXTHLbXLOWSNWTaGLaWJNUQ|JNVREJWTBEbWJMTPMVZJFMWTMQTOQZOF|JNVREJWTBEZVJMbWMQcZLOTPHLWSNWaT|JNVREJWTJMaWMVZJFMWSLOSLGWbSMQSO|JNVREJWTJMaWMVZJFMWSMQTOKTXOQZcV|JNVREJWTJMaWMVZJFMWSMRUNKReaIMcZ|JNVREJWTJMUQMVZJFMQJBEYUENUQAETP|JNVREJWTJMUQMVZJFMQJBEYUENUQLObW|JNVREJWTJMUQMVZJFMQJBFYUFMUQMRTP|JNVREJWTJMUQNUQJFMZJBEJFKBTPLOYU|JNVREJWTJMUQNUQJFMZJBFYUFMUQMRTP|JNVREJWTLObWBETPJMWTMVZLHOaVEJVR|JNVREJWTLObWJMUQMVZJFMQJBEYUENUQ|JNVREJXTBETOLSaVJMVOKaRBEJeVMQUR|JNVREJXTJMUQNUQJFMZJBEaVENVSLPSJ|JNVREJXTLOTPBEaVHLWSNWbSJMfbMQda|JNVREJXTLOTPBEaVJMVSMVSLHOZLDHbX|"+
        "JNVREJXTLOTPJMWSNWbLMVaRHOZVAEfb|JNVREJXTLOTPOTbXJMXOMVZJKTUQFMQJ|JNVREJXTLOTPOTZVJMUQNUQZAEWSTXSO|JNVREJXTLPaVHLbXLOWSNWTaDHUQGLZU|JNVREJXTLPaVHLbXLOWSPWSbGLUQNUYR|JNVREJXTLPbXGLZVLOUQNUQZJMVSOVZS|JNVREJXTLPbXHLaVJMWSNWTaMQfbLObW|JNVREJXTLPbXHLZVJMUQNUQZMQVSKOTK|JNVREJXTLPZVGLbXJMUQNUQZMQVRAEeb|JNVREJXTLPZVJMUQNUQZMRVMIRZUAEUN|JNVREJZVJMUQNUQJFMYRAEWSBFbWEJfb|JNVREJZVJMUQNUQJFMYRAEWSCFbWEJfb|JNVREJZVJMUQNUQJFMYRAEWSCFcYMQYU|JNVREJZVJMUQNUQJFMYRAEWSCFdZKObW|JNVREJZVJMUQNUQJFMYRAEWSKORNBFNJ|JNVREJZVJMUQNUQJFMYRAEWSKORNCFaW|JNVREJZVJMUQNUQJFMYRAEWSKORNLPSL|JNVREJZVJMUQNUQJFMYRAEWSKORNMQaW|JNVREJZVJMUQNUQJFMYRAEWSLOSLHObW|JNVREJZVJMUQNUQZAEVSLOSLHOWSOVZS|JNVREJZVJMUQNUQZAEWSEJaWKOXTOXSO|JNVREJZVJMUQNUQZAEWSEJSOLSVOKTXO|JNVREJZVJMUQNUQZAEWSEJYUKOaWMQXT|JNVREJZVJMUQNUQZAEWTEJbWMQTPJMWT|JNVREJZVJMUQNUQZAEWTEJTPJNVSNWbS|JNVREJZVJMUQNUQZAEWTEJTPMRVMJQbW|JNVREJZVJMUQNUQZAEWTMRVMIRbWEJTP|JNVREJZVJMUQNUQZAEXTLObXEJfbMQZU|JNVREJZVJMUQNUQZAEXTLObXEJfbMRVM|JNVREJZVJMUQNUQZAEXTLObXEJTPOTXO|JNVREJZVJMUQNUQZAEXTLObXEJWSHLTP|JNVREJZVJMUQNUQZAEXTLObXEJYUMQfb|JNVREJZVJMUQNUQZAEXTLObXEJYUMQWS|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfb|JNVREJZVJMUQNUQZAEXTLObXMRVMIRTP|JNVREJZVJMUQNUQZAEXTMQTOLSVOKTWP|JNVREJZVJMUQNUQZAEYUMQWSEJSOLSVO|JNVREJZVJMUQNUQZAEYUMRUNKRVMIRZV|JNVREJZVJMUQNUQZFJWSAEYUMQSOKTXO|JNVREJZVJMUQNUQZFJWSBFYUKNUQNWbS|JNVREJZVJMUQNUQZKNVRNUZJFMYUMQUR|JNVREJZVJMUQNUQZKNVSFJXTMQTPIMbX|JNVREJZVJMUQNUQZKNWSNWbSLPfbAEbW|JNVREJZVJMUQNUQZKNWSNWbSLPYUAEXT|JNVREJZVJMUQNUQZKNWSNWbSLPYUMQfb|JNVREJZVJMUQNUQZKNWSNWbSLPYUMQUR|JNVREJZVJMUQNUQZKNXTMQTOLSVOIMWS|JNVREJZVJMUQNUQZKNXTMRVMIRTPAEbX|JNVREJZVJMUQNUQZKNXTMRVMIRTPLObX|JNVREJZVJMUQNUQZLOWSGLbWLPSLPGfb|JNVREJZVJMUQNUQZLOWSGLYUMQbWAEWT|JNVREJZVJMUQNUQZLOWSHLYUAEURMQaW|JNVREJZVJMUQNUQZLOWTAEbWMRVMIRTP|JNVREJZVJMUQNUQZMQWSAEYUEJSOLSVO|JNVREJZVJMUQNUQZMQWTFJTOKTXOLSVO|JNVREJZVJMUQNUQZMQWTKNTOLSVOGLaW|JNVREJZVJMUQNUQZMRVMIRWSFJbWLOSL|JNVREJZVJMUQNUQZMRVMIRWSFJZUBEUN|JNVREJZVJMUQNUQZMRVMIRWSLOSLHObW|JNVREJZVJMUQNUQZMRVMIRWSLOSLHOZV|JNVREJZVJMUQNUQZMRVMIRXTAETOKTWP|JNVREJZVLOUQNUQZAEWSGLYULPSLPGXT|JNVREJZVLOWTNScZIMRIKNTRJMVOMcUR|JNVREJZVLOWTNSUQSZdUAEcZJMQAFJAL|JNVREJZVLOWTNSUQSZdUAETPJNbWEJWT|JNVREJZVLOWTNSUQSZdUIMRIBEIBAEBI|JNVREJZVLPUQNUQZHLWSKOYUBEXTPNVS|JNVREJZVLPUQNUQZHLWSKOYUDHXTPNVS|JNVREJZVLPUQNUQZHLWSKOYUJMbWMQUR|JNVRFJaVJMUQNUQJENYRNUZQAEdZKNWS|JNVRFJaVJMWTMQTOLSVFBKbWHLWTLOfb|JNVRFJaVJMWTMQTOLSVFBKXTGLZVQSTP|JNVRFJaVJMWTMQTOLSVFBKXTHLbXLOfb|JNVRFJaVLPXTGLbXLOWSNWTaJNfbHLbW|JNVRFJWSNWbSJMRNKRUNBFXTLPebPWaT|JNVRFJWSNWbSJMSNMVaRBFXTLPeaPWaT|JNVRFJWTJMaVMQTOLSVFBKbWHLfbLOea|JNVRFJWTJMaVMQTOLSVFBKXTHLbXLOfb|JNVRFJWTJMTPMVZJENUQAEbWBFcZLOZU|JNVRFJWTJMTPMVZJENUQAEbWBFfbNRQM|JNVRFJWTJMTPMVZJENUQAEbWEJYUKOWT|JNVRFJWTJMTPMVZJENUQAEbWLOWTEJdZ|JNVRFJWTJMTPMVZJENUQLObWAEWTEJYU|JNVRFJWTJMTPMVZJENUQLObWAEWTNRcZ|JNVRFJWTJMTPMVZJENUQLObWOSWTNRfb|JNVRFJWTJMZVMQcZLOTPBFbWHLfbNSWN|JNVRFJWTJMZVMQcZLOTPCFbWEJebHLWS|JNVRFJWTJMZVMQcZLOTPCFbWEJebOTXO|JNVRFJWTJMZVMQcZLOTPCFbWHLebEJWS|JNVRFJWTJMZVMQcZLOTPGLPGCLbWLPeb|JNVRFJWTJMZVMQcZLOTPHLbWBFWSNWaT|JNVRFJWTLObWJMTPMVZJENUQAEWTEJaV|JNVRFJWTLOTPJMbWMVZJENWTAEUQEJdZ|JNVRFJWTLOZVNSUQSZcVJMQJEUYRAEdZ|JNVRFJWTLOZVNSUQSZdUIMRIBFIBAEBI|JNVRFJWTLOZVNSUQSZdUJNcZIMQLGdRM|JNVRFJZVJMUQNUQZEJWTLObWAETPBFYU|JNVRFJZVJMUQNUQZMQWSKOaWGKWTLPSL|JNVRFJZVJMUQNUQZMRVMIRWSLOSLHObW|JNVRFJZVJMUQNUQZMRVMIRWTKNTPLObW|JNVRFJZVJMUQNUQZMRVMIRWTLObWEJfb|JNVRFJZVJMUQNUQZMRVMIRWTLObWEJTP|JNVRFJZVJMUQNUQZMRVMIRXTKNTPLObX|JNVRFJZVJMUQNUQZMRVMIRXTLObXEJTP|JNVRFJZVJMUQNUQZMRVMIRZULOUNKRdZ|JNVRFJZVJMWTMQcZLObWHLTPNSWNDHfb|JNVRFJZVJMWTMQcZLOTPBFbWHLebDHWS|JNVRFJZVJMWTMQcZLOTPBFbWHLebNSWN|JNVRFJZVJMWTMQcZLOTPBFbWHLfbNSWN|JNVRFJZVJMWTMQcZLOTPGLPGCLbWLPeb|JNVRLOWTFJbWJMTPMVZJENUQOScZSbfW|JNVRLOZVEJWTNSUQSZdUAETPJNbWEJWT|JNVRLPWTPWbJFVaREJZVHLfbJNbWAEVS|JNVRLPXTGLbXEJaVLOWSPWSbHLUQNUYR|JNVRLPZVGLRMIRVMEIcZIRWTPWbJFMUP|"+
        "JNVRLPZVHLUQNUQZIMWSKOSNMQYUFKUR|JNVRLPZVHLUQNUQZIMWSMQYUKOSNFKUR|JNVRLPZVHLUQNUQZIMWTPWbSKOfbMQbW|JNVRLPZVHLUQNUQZIMWTPWbSKOYUEIaW|JNVRLPZVHLUQNUQZIMWTPWbSKOYUMQaW|JNVRLPZVHLUQNUQZIMWTPWbSKOYUMQUR|JNVRLPZVHLUQNUQZIMYUMQWSKOUREJbW|JNVRLPZVHLVSDHSJFVaREJeaJMRNKRUN|JNVRLPZVHLVSDHSJFVaREJUQBFdaLOYU|JNVSEJaVAEVRLPRMIRSOKaeMJQXTPWbA|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEcY|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZ|JNVSEJaVKOeaGKURNUYRLPSLPGWSJNSJ|JNVSEJaVKOeaGKURNUYRLPSLPGWSKOSL|JNVSEJaVKOUQFKZUJMQJNEURBFYUFJcY|JNVSEJaVKOUQFKZUJMQJNEWTIMTPEIUR|JNVSEJaVKOUQFKZUJMQJNEWTIMTPMQUR|JNVSEJaVKOUQFKZUJMQJNEWTLPSLPWbS|JNVSEJaVKOUQGKZUBEURNUQZIMYUMQWT|JNVSEJaVKOUQGKZUBEURNUQZJNSJENYU|JNVSEJaVKOUQGKZUBEURNUQZKNYUFKUQ|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQ|JNVSEJaVKOUQGKZUBEURNUQZKNZUDGXT|JNVSEJaVKOUQGKZUBEURNUQZKNZUFKUQ|JNVSEJaVKOUQGKZUBEURNUQZKNZULPSL|JNVSEJaVKOUQGKZUBEURNUQZKNZUNRUN|JNVSEJaVKOUQGKZUBEURNUYRJMQJEUcY|JNVSEJaVKOUQGKZUDGURNUQZIMYUBEVR|JNVSEJaVKOUQGKZUDGURNUQZJMWTMRVM|JNVSEJaVKOUQGKZUDGURNUQZJNSJFMWT|JNVSEJaVKOUQGKZUDGURNUQZKNYUFKUQ|JNVSEJaVKOUQGKZUDGURNUQZKNYUIMUQ|JNVSEJaVKOUQGKZUDGURNUQZKNZUBEXT|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKcZ|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKUQ|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKUR|JNVSEJaVKOUQGKZUDGURNUQZKNZUGKcZ|JNVSEJaVKOUQGKZUDGURNUYRBEcYJMQJ|JNVSEJaVKOUQGKZUDGURNUYRJNSJFMQJ|JNVSEJaVKOUQGKZULPSLPGVRAEXTHLcZ|JNVSEJaVKOUQGKZULPSLPGVRAEXTHLea|JNVSEJaVKOUQGKZULPSLPGVRGLRMIRWS|JNVSEJaVKOUQGKZULPSLPGVRHLeaJMQS|JNVSEJaVKOURNUYRJMeaAEWTGKSNOSNP|JNVSEJaVKOURNUYRJMeaAEWTGKTPFJPN|JNVSEJaVKOURNUYRJMZUGKSNDGNJMQXT|JNVSEJaVKOURNUYRJMZUGKSNOSNPSQda|JNVSEJaVKOURNUYRJMZUMQWTQZdUGKUQ|JNVSEJaVKOURNUZQGKYUBEeaDGcZKNUR|JNVSEJaVKOURNUZQGKYULPSLPGXTJMQJ|JNVSEJaVLPUQGLZUKOURNUQZJMYUMRUN|JNVSEJaVLPVRGLZVLOSLPGUQNUQZIMYU|JNVSEJUQAEZVIMYUEIURNUQZKNXTLPbX|JNVSEJUQAEZVIMYUEIURNUQZKNXTLPSO|JNVSEJUQAEZVIMYUEIURNUQZKNXTMQTO|JNVSEJUQKOYUOVaKFOWTGKZVBFTPDGea|JNVSEJURNUYRKORNOVaRJSWNBEXTEJNE|JNVSEJZVKOUQGKYUBEcYDGURNUQZKNZU|JNVSEJZVKOUQGKYUBEURNUQZKNZUDGUQ|JNVSEJZVKOUQGKYUDGURNUQZKNZUGKUQ|JNVSEJZVKOUQNRVMIRXTOXSOLSWUGKcZ|JNVSEJZVKOURNUYRJMcZGKWTAESNOSNP|JNVSEJZVKOURNUYRJMcZGKWTAETPFJPN|JNVSEJZVKOURNUYRJMcZMQZUQZdULPSL|JNVSFJaVKOUQGKZUDGURNUQZKNZUGKcZ|JNVSFJaVKOUQGKZUDGURNUQZKNZUGKUQ|JNVSFJaVKOURNUYRBFWTFKSNJSTPCFcY|JNVSFJaVKOURNUYRJMRNMQWTIMTKEJNE|JNVSFJaVKOURNUYRJMZUEJWTGKTPAEPN|JNVSFJaVKOURNUYRJMZUGKWTCFTPFJPN|JNVSFJZVKOUQGKYULPSLPGXTIMURNUQZ|JNVSFJZVKOURNUYRJMRNEJNEAJWTCFTK|JNVSFJZVKOURNUYRJMRNMQcZBFXTOXWT|JNVSFJZVKOURNUYRJMRNMQcZIMZUQZVc|JNVSLOSJFMWTMQbWEJTPJMWTAEfbHLbW|JNVSLOSJFMWTMRUNKRTKGNXTHLbXCGfb|JNVSLOSLHOUQNRWTIMQJFMbWEJTPAEWT|JNVSLOSLHOURNUYREJaVJNWSNUSLGPZQ|JNVSLPSJFMWSGLaVLOSLPGXTHLVSBFTP|JNVSLPSJFMWSHLaVKObWMQUREJYUGKfb|JNVSLPSJFMWSHLUQEJaVKObWGKZUDHXT|JNVSLPSJFMWSHLUQEJaVKOZUJNSJMFVS|JNVSLPSJFMWTPWbSEJfbMQSOKTXOBFUR|JNVSLPSJFMWTPWbSEJXTMQSOJNOFBKfb|JNWSNWaTEJUQAEZUJNURNUQZEJeaKNZU|JNWSNWaTIMTPLOUQEIQJFMbWAEfbMRVM|JNWSNWaTIMUREITPLObWOTXOKadWFKfb|JNWSNWaTKNbWFKTPNRVMIRUNKRWTEJZV|JNWSNWaTKNbWFKVREJTPLOZVJMUQNUQZ|JNWSNWaTLOdaEJbWJMUQMRVMIRaVRaWd|JNWSNWaTLOeaFJbWJNURNUYRKNRKOFWS|JNWSNWbSEJfbKObWGKURLPSLPGWSAEaW|JNWSNWbSIMaWMQWTKNSJENfbAEbWFKTP|JNWSNWbSIMebMQSOLSVOKTXOEJbWJMfb|JNWSNWbSIMfbMQbWEIURAEZUQZdUEJUQ|JNWSNWbSLOSLHOfbEJVRJNUQNUYROSZU|JNWTEJaWBETPNRVMJQUREJXTLObXJNZU|JNWTEJaWLOdaGLTPAEPGCLVSOVaRLPZV|JNWTEJaWLPeaAEVRJMUQMeQMIRdaeVZA|JNWTEJaWLPeaAEVRJMZVEJUQNUQZJNTO|JNWTEJbWAEUQNSVOLbfWHLTPLOWTJNaW|JNWTEJbWAEVRLPaVGLWSPWSbLOUQNUYR|JNWTEJbWJMebMRVMIRTPAEUQEJWSNWaT|JNWTEJbWJMfbMQTOKTXOLSVOIMURMVZJ|JNWTEJbWJMfbMRVMIRTPAEUQEIZUKOdZ|JNWTEJbWJMfbMRVMIRTPAEUQEIZULOWT|JNWTEJbWJMfbMRVMIRTPAEUQLOWTEIZU|JNWTEJbWJMfbMRVMIRTPAEUQLOWTOSbW|JNWTEJbWJMfbMRVMIRTPAEWTEIbWLOUQ|JNWTEJbWJMfbMRVMIRTPAEWTEJbWLOUQ|JNWTEJbWJMfbMRVMIRTPAEWTEJUQJMQS|JNWTEJbWJMfbMRVMIRTPAEWTEJZVJMUQ|JNWTEJbWJMfbMRVMIRTPAEWTLOaVRaeV|JNWTEJbWJMfbMRVMIRTPLOWTAEZVEJVM|JNWTEJbWJMTPMQURNUYRAEfbLOcYOTXO|"+
        "JNWTEJbWJMTPNRUNKRWSMQVMQJfbLOSL|JNWTEJbWJMTPNRUNKRZUFKUNKRXTBFWS|JNWTEJbWJMUQNRQJFMfbLOZUMQUNKRTK|JNWTEJbWJMUQNRQJFMfbMQVMQJTOLSWE|JNWTEJbWJMURNUZJFMfbAEdZKOTKGNXT|JNWTEJTOKTXOLSVOAEURNUYRJNRKGNbW|JNWTEJTOKTXOLSVOIMOKFOURNUYIJNbW|JNWTEJTOLSVOKTXOAEURNUYRJNRKGNbW|JNWTEJTPBEbWJMUQNRQJFMWTKNTOLSVO|JNWTEJTPJMbWBEUQNRQJFMWTMQVMQJaV|JNWTEJTPJMbWMQURNUYRAEfbKOWSFJRM|JNWTEJTPJMbWMQURNUYRAEfbLOcYHLWS|JNWTEJTPJMbWMQURNUYRAEfbLOcYOTXO|JNWTEJTPJMbWMQURNUYRAEfbLOWTFJRM|JNWTEJTPJMbWMQURNUYRLOfbOTXOKTbX|JNWTEJTPJMbWMQWTLOURNUYRAEaWFJWS|JNWTEJTPJMbWMRVMIRfbLOWTAEaVRaeV|JNWTEJTPJMbWNRUNKRWSAEfbMQVMQJaV|JNWTEJTPJMbWNRUNKRWSMQVMQJfbLOSL|JNWTEJTPJMbWNRUNKRZUFKUNKRdZBFWS|JNWTEJTPJMbWNRUNKRZUFKUNKRdZBFWT|JNWTEJTPJMbWNRUNKRZUFKUNKRdZMQVM|JNWTEJTPJMbWNRUNKRZUFKUNKRXTBFWS|JNWTEJTPJMbWNRUNKRZULOUNFKPLGPNG|JNWTEJTPJMUQNRQJFMbWAEWTMQVMQJYU|JNWTEJTPJMUQNRQJFMbWBFWTMQVMQJYU|JNWTEJTPJMUQNRQJFMbWMQVMQJYUJMfb|JNWTEJTPJMUQNRQJFMbWMQVMQJYUJNUQ|JNWTEJTPJMVSNWbSMQfbFJbWIMWTJNSJ|JNWTEJTPJMXTMQTOKTPWGKbXAEXTEJTP|JNWTEJTPJMXTMQTOLSVOKTPWAEWTEJTP|JNWTEJTPJMXTMRVMIRZVAEVMEIaWIRWS|JNWTEJTPJMXTMRVMIRZVAEVMEIcZIRZV|JNWTEJTPJMXTNRUNKRTOLSVOAEbXEJXT|JNWTEJTPJMXTNRUNKRTOLSVOFKOFBKbX|JNWTEJTPJMXTNRUNKRZUFKUNKRbWAEfb|JNWTEJTPJMXTNRUNKRZUFKUNKRbWBFWS|JNWTEJTPJMXTNRUNKRZUFKUNKRbWMQVM|JNWTEJTPLOVRBEbWJMWTMVZJENUQFJaV|JNWTEJTPLOVRBEbWJMWTMVZLHOaVEJVR|JNWTEJTPLOVRJMUQMVZJFMQJBFYUFMUQ|JNWTEJUQAETPLObWNSWNKRVMIRfbJNbW|JNWTEJURNUZQAEYUJNVREJTPLOcYHLaV|JNWTEJVRBEbWJMTPMVZJFMUQLOQJENWT|JNWTEJVRJMUQMVZJFMQJBEYUENUQAEdZ|JNWTEJVRJMUQMVZJFMQJKOTKGEXTEJaV|JNWTEJVRJMUQNUQJFMZJBEYUENUQLOTP|JNWTEJVRLObWBEaVJMVSMVSLHOZJENUQ|JNWTFJTPBFbWJMWTNRUNKRVSMQSOLSZU|JNWTFJTPBFVRJMZVMQcZLObWHLebNSWN|JNWTFJTPJMXTMRVMIRbXLOZVEIVMIRcZ|JNWTFJUQBFTPLObWOTXOKTfbTXZUNRVM|JNWTFJVRJMZVMQcZLOTPCFbWEJebOTXO|JNWTLObWHLTPNRUNKRVMIRfbEJZVJMdZ|JNWTLObWHLTPNRUNKRVMIRWTEJTKGNPG|JNWTLObWHLUQNRVMIRTPEJWTJMQJFMaW|JNWTLObWNRUNKRVMIRTKGNfbFKXTHLbX|JNWTLObWNRUNKRVMIRTKGNXTHLfbFKbX|JNWTLOVREJaVBEbWJMUQNUQJENZQNRVM|JNWTLOVREJbWJMUQNUQJFMZJBEJFKBTK|JNWTLOVREJTPJMUQMVZJFMQJBEYUENUQ|JNWTLOVREJTPJMUQNUQJFMZJBFYUFMUQ|JNWTLOVRFJbWJMfbMVZJENURNUYRAEaV|JNWTLOVRFJbWJMfbMVZJENURNUYRAETP|JNWTLOVRFJbWJMTPMVZJENUQOSWTNRfb|JNWTLPUQPWbJENXTAEfbHLTPEJYULObX|JNWTLPUQPWbJENXTAETPHLYULOVSNWaT|JNWTLPUQPWbJENXTAETPKOfbFKbXCFVR|JNWTLPUQPWbJENXTAEYUHLTPLOVSNWaT|JNWTLPUQPWbJENXTHLTPAEfbEJYULObX|JNWTLPUQPWbJENXTHLTPAEfbLObXEJYU|JNWTLPUQPWbJENXTHLTPAEfbLObXEJZU|JNWTLPUQPWbJENXTHLTPAEYULOVSNWaT|JNWTLPUQPWbJENXTHLTPFJfbKOZUGKPG|JNWTLPUQPWbJENXTHLTPLOfbAEbXEJYU|JNWTLPUQPWbJENXTHLTPLOfbAEYUEJbX|JNWTLPUQPWbJFMQJENYUAEVRHLXTEJTP|JNWTLPUQPWbJFMQJENYUHLfbAEbWNRUN|JNWTNRUNKRVMIRaWFKdaLOaVRaWdEJYU|JNWTNRUNKRVMIRaWGKTPLOPLOTXOKaeM|JNWTNRUNKRVMIRaWLOTKFOWTHLTKGNXT|JNWTNRUNKRVMIRTOLSZURVaRFKRMKOea|JNWTNRUNKRVMIRTOLSZURVaRGKcZSWbS|JNWTNRUNKRVMIRTOLSZURVaRGKRMEJMI|JNWTNRUNKRVMIRTOLSZURVaRGKRMEJUQ|JNWTNRUNKRVMIRTOLSZURVaRGKRMHLea|JNWTNRUNKRVMIRTOLSZURVaRGKRMHLUQ|JNWTNRUNKRVMIRTOLSZURVaRGKUQEJQM|JNWTNRUNKRVMIRTOLSZURVaRGKUQHLda|JNWTNRUNKRVMIRTOLSZURVaRGKUQHLYU|JNWTNRUNKRVMIRTOLSZURVaRHLRMGKea|JNWTNRUNKRVMIRTOLSZURVaRHLRMGKMI|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOea|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOMI|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVMI|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVXT|JNWTNRUNKRVMIRTOLSZURVaRHLUQGKYU|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOda|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOYU|JNWTNRUNKRVMIRTPEJbWAEfbJNWTEIbW|JNWTNRUNKRVMIRTPEJbWAEWTJNaWEJWS|JNWTNRUNKRVMIRTPEJZUJNdZAEXTEIbX|JNWTNRUNKRVMIRTPLObWEJWTHLTKGNPG|JNWTNRUNKRVMIRTPLObWHLWTEJTKGNPG|JNWTNRVMIRUNKRTOLSZURVaRGKRMHLea|JNWTNRVMIRUNKRTOLSZURVaRGKUQHLda|JNWTNRVMIRUNKRTOLSZURVaRHLRMGKea|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOea|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOMI|JNWTNRVMIRUNKRTOLSZURVaRHLUQGKYU|JNWTNRVMIRUNKRTOLSZURVaRHLUQLOda|JNWTNRVMIRUNKRTOLSZURVaRHLUQLOYU|JNWTNRVMIRUNKRTPFKbWEIWSLOSLHOfb|JNWTNRVMIRUNKRZUFKUNKRaWGKdZKNTP|JNWTNSVOLSaVKOTKFObWSbfWEJWTHLTK|"+
        "JNXTEJbXJMVSMQSJFMTPAEfbLOWTEJbW|JNXTEJTOLSVOKTWPAEaVHLbXLOfbOSVO|JNXTEJTPJMWSNWbSMQfbAEaWIMUREIda|JNXTEJTPJMWSNWbSMQSOKTPWLPfbGKUR|JNXTEJTPLOUQOTZUTXVRHLaVLOWSNWbL|JNXTLObXHLfbLPVSOVZJENTOKTXOIMOK|JNXTLObXHLTPNRUNKRVMIRfbEJWSOVZS|JNXTLObXHLTPNRUNKRVMIRfbEJWTFKaV|JNXTLObXHLTPNRUNKRVMIRfbEJWTFKZV|JNXTLObXHLTPNRUNKRVMIRfbEJZVJMdZ|JNXTLObXHLTPNRUNKRVMIRWSOVZSFJaV|JNXTLObXHLTPNRUNKRVMIRWTEITKGNPG|JNXTLObXHLTPNRUNKRVMIRWTEJTKGNPG|JNXTLObXHLUQNRVMIRTPEJWTJMQJFMaV|JNXTLObXHLUQNSWNKRTKGNVMIRfbFKbW|JNXTLObXHLUQNSWNKRVMIRTKGNfbFKaV|JNXTLObXHLUQNSWNKRVMIRTKGNfbLObW|JNXTLObXHLUQNSWNKRVMIRTKGNXTLOTK|JNXTLObXNRUNKRVMIRTKFOWSOVZSEJfb|JNXTLObXNRUNKRVMIRTKGNfbHLXTRUYK|JNXTLObXNRUNKRVMIRTKGNXTHLfbLOTK|JNXTLObXNRVMIRUNKRTKGNfbFKXTHLbX|JNXTLOTPOTVSTXSJENWSNWbSIMfbAEUQ|JNXTLOTPOTVSTXSJENWSNWbSIMSOKTPW|JNXTLPbXGLVRLOaVHLWSNWTaEJUQJMQJ|JNXTLPbXGLVRLOaVHLWSPWSbLPUQNUYR|JNXTLPbXGLVSDGSJENURNUYRAEebFJaV|JNXTLPbXGLVSDGSJFMUQBFQJENaVNSVO|JNXTLPbXGLVSLOSLPGTOKTXOGKWTEJfb|JNXTLPbXHLVSDHSJENUQAEZUEJaVBEVS|JNXTLPbXHLVSDHSJENURNUYRAEebFJcY|JNXTLPbXHLVSDHSJFMURMVaREJebBFYU|JNXTLPbXNRUNKRVMIRebEJZUJNcZAEaV|JNXTLPbXNRUNKRVMIRebEJZUJNcZBETO|JNXTLPbXNRUNKRVMIRebEJZUJNcZGLZV|JNXTLPbXNRUNKRVMIRebEJZUJNcZHLZV|JNXTLPbXNRUNKRVMIRebEJZUJNcZNSUN|JNXTLPbXNRUNKRVMIRTOEJebJMZVAEcZ|JNXTLPbXNRUNKRVMIRZVEIVMIRebAEcZ|JNXTLPbXNRUNKRVMIRZVEIVMIRebAEdZ|JNXTLPbXNRUNKRVMIRZVEJVMJQTOAEcZ|JNXTLPbXNRUNKRVMIRZVEJVMJQTOAEfb|JNXTLPbXNRVMIRUNKRZVEIVMIRebAETO|JNXTLPUQEJVSAEbXIMZUEIaVGLebMRVM|JNXTLPUQEJZUGLbXLOURNUQZJMVSOVZS|JNXTLPUQEJZUGLVRLObXHLaVDHebAEWS|JNXTLPUQEJZUHLVSBEaVDHbXNRVMIRUN|JNXTLPUQFJVSGLbXLOSLPGTOKTWPHLaV|JNXTLPUQGLbXLOZUHLVRIMQSOMaVLOdZ|JNXTLPUQGLYULObXHLVSOVZJFMQJENaV|JNXTLPUQGLZUDGbXEJURNUQZJNYUFJUQ|JNXTLPUQGLZULObXEJURNUQZJMVSOVZS|JNXTLPUQGLZULObXHLURNUQZEJYUJMUQ|JNXTLPUQGLZULObXHLURNUYREJRMIRVM|JNXTLPUQGLZULObXHLURNUYRKNRKIMQJ|JNXTLPUQGLZULObXHLURNUYRKNTKNGcZ|JNXTLPUQGLZULObXHLURNUYRKNTKNGeb|JNXTLPUQGLZULObXHLVRIMQSOMebLOaV|JNXTLPUQHLVSDHSJFMQJENZUIMbXMQUR|JNXTLPUQHLVSDHSJFMQJENZUIMURMVaR|JNXTLPUQHLVSEJbXDHYUIMZVAETOKTXO|JNXTLPUQHLZULObXNSWNPWaTKadWFKUR|JNXTLPUQNRVMIRaVRaeVKNVSEISJFMQJ|JNXTLPUQNRVMIRZUEIUNKRQMRUYRAETO|JNXTLPUQNRVMIRZUKNTOGKbXKTXOCGeb|JNXTLPUQNRVMIRZUKNTOGKbXKTXOEIeb|JNXTLPUQNRVMIRZUKNTOGKbXKTXOFKOF|JNXTLPUQNRVMIRZUKNTOGLWSNWbSCGUN|JNXTLPUQNRVMIRZURVaRKNRKFXcZEJUR|JNXTLPUQNRVMIRZURVaRKNRKFXcZGKUR|JNXTLPUQNRVMIRZURVaRKNRKFXUREJcZ|JNXTLPUQNRVMIRZURVaRKNRKFXUREJRM|JNXTLPUQNRVMIRZURVaRKNRKFXUREJYU|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZ|JNXTLPUQNRVMIRZURVaRKNRKFXURHLcZ|JNXTLPUQNRVMIRZURVaRKNRKFXWSEJbW|JNXTLPUQNRVMIRZURVaRKNRKFXWSHLbW|JNXTLPVREJaVHLbXLOWSPWSbGLUQNUYR|JNXTLPVREJbXGLZVLOUQNUQZHLVRJMZU|JNXTLPVREJbXHLaVLOWSPWSLGPVSCGSb|JNXTLPVREJbXJMTOMVZJKTXOFMebMQcZ|JNXTLPVRFJbXJMTOMVZJENOFBKebNRUN|JNXTLPVRGLaVLObXEJWSPWSbHLUQNUYR|JNXTLPVRGLaVLObXHLWSPWSbLPUQNUYR|JNXTLPVRGLbXEJaVAEWSNWTaJNVSNWaT|JNXTLPVRHLaVEJbXJMWSNWTaMQfbLObW|JNXTLPVSEJUQGLbXLOSLPGTPAEWTHLfb|JNXTLPVSGLSJFMbXLOUQBFQJFMaVEJVS|JNXTLPVSHLSJENZVLObXFJUQGLYUCFUR|KNVRFKWSNWbSJMRNKRUNLOSLHOaVBFda|KNVRFKWTJMaVEJTOLSVFBKdaMVaRHLZV|KNVRFKWTJMTPMVZJENUQLObWAEWTNRQM|KNVRFKWTJMTPMVZJENUQLObWBEWTCFfb|KNVRFKWTJMTPMVZJENUQLObWOSWTNRfb|KNVRGKZVJMUQNUQZMRVMIRWSLOSLHObW|KNVRGKZVJMUQNUQZMRVMIRWTKNTPDGXT|KNVRGKZVJMWTDGTPMQdZLObWGLPGCLfb|KNVRGKZVJMWTDGUQNUQZMRVMIRTPEJbW|KNVSIMUQEIXTLPbXMRTOGKebKTXOHLOH|KNVSIMXTEITPMRWTNWUEAJbSIMZVMQcZ|KNVSIMXTFKTOKTWPNWbSMQUREIaVBFda|KNWSNWbSIMXTLPTOMQUREIRMIRVMGKMI|KNWSNWbSIMXTLPTOMQUREIRNJMfbGKNG|KNWSNWbSLPebGLSOLSVOPTOKFObWJNWP|KNWSNWbSLPebGLUQIMYUFKUREIbWJNSJ|KNWSNWbSLPebJMbWEJfbMQXTGLbXJMUR|KNWSNWbSLPebJMbWHLfbMQSOLSWNIMNJ|KNWSNWbSLPebJMUQMRVMIRbWFJZVCFVM|KNWSNWbSLPfbJMbWMQSOEJWTPWaTJMda|KNWTFKbWJMTPMRVMIRWSNWUNKRaTEJfb|KNWTFKbWLPVSGLTOKTXOPTWGDTaWTadW|KNWTFKTPBFbWJMfbNRUNKRWTMQVMQJaV|KNWTFKTPBFbWJMUQNRQJENVMIRWTAEZU|KNWTFKTPBFbWNRUNJbfWIMYUMQWTEJTO|KNWTFKTPBFUQNRVMIRXTJMQJFMTOLSaV|"+
        "KNWTFKTPBFVRJMbWMVZJENUQLOWTAEYU|KNWTFKTPJMXTMRVMIRbXEIaWAEWSNWTa|KNWTGKbWDGVSLOSLHOTPNRUNJbfWEJYU|KNWTGKbWJMVRMVZJENebAEUQIMQACGAS|KNWTGKTPLOVRJMPLMVZJFMLSCFSOKTXO|KNWTJMTPMRVMIRXTEIUQAEZUEJaWLOTK|KNWTJMTPMRVMIRXTFKbXLOZVEIVMIRcZ|KNWTJMTPMRVMIRXTLOTKFObXGLPGDKfb|KNWTJMVRMVaKGNbWEJTPAEPGCLeaNRUN|KNWTJMVRMVaKGNbWEJZVAETPNRVMJZPG|KNWTJMVRMVaKGNeaIMZVEIURNUYRCGTP|KNWTJMVRMVaKGNTPDGURNUYREJbWFKea|KNWTLPbWNRUNJbfWEJVSJMYUMQSNHLaV|KNWTLPURNUYRPWbSJNRKGWaTEJfbAEVS|KNWTLPVRPWRKGNaTIMTPFKXTHLPGCLZV|KNWTLPVRPWRKGNbSNWaTJNTOIMZVEIUR|KNXTLPVSGKbXDGTOKTXOGKfbKTbXCGXO|KNXTLPVSGKbXDGUQNRSOJNZUEJcZBEeb|KNXTLPVSGKZVHLcZLOSLPGTOKTWPFKaW|KNXTLPVSGKZVHLcZLOSLPGTOKTWPJMVS|KNXTLPVSIMbXMQTOEIURNUYRJMaVGLea|KNXTLPVSIMbXMRTOGKebKTXODGbXEIXT|KOUQGKWSJNSJENZUDGVRIMQSOMURMVaR|KOUQGKWSJNSJENZUOTXOLZcVAEbWDGVR|KOUQGKWTLPYUPWbLHOfbDGbWGLcYLPWS|KOUQGKYULPWSJMQJEWbLPGfbAEbWHLWT|KOUQJNVSOVaKFOWTEJTKGNbWBEZVNSWN|KOUQJNVSOVaKGNYUEJZVBEVRFKdZLPZV|KOUQJNVSOVaKGNYUFKZVDGVRLOWTHLTP|KOUQJNWSNWaKFObWEJWTOSVOLSeaBFfb|KOURFKYUJNWTLPVSOMZVPWbQIMQJENfb|KOURGKYUJNWSNWaTEJUQLPeaPWbLHOaW|KOURGKYUJNWSNWaTLPUQPWbLHOfbFJbW|KOURGKZUJNWSNWaTEJeaJMbWFJWSKNRK|KOURGKZUJNWSNWbSOTXOKTfbTXcZLPbW|KOWTFKTPBFUQJNbWOSVOLbfWHLWTLOZU|KOWTFKTPBFURJMYUMQcYEJRMIRUEAJVR|KOWTGKTPDGbWOTXOLbfWJNWSNWaTEJUR|KOWTGKTPDGUQJNYUEJVRNSaVJNeaAEaW|KOWTGKTPKNPGCLbWFKWSNWaTJNTPDGeb|KOWTJMTKFOaWBFWTGKTPDGdaMRVMIRUN|KOWTJMTKFOaWGKWTBFTPDGdaMRUNKRVM|KOWTJMTKFOaWGKWTBFTPDGdaOSVOLSaV|KOWTJMTKFOaWGKWTBFTPDGeaEJUQMRVM|KOWTJMTKFOaWGKWTBFTPDGUQMRVMIRda|KOWTJMTKFOaWGKWTBFUQOSQJENVOLSea|KOWTJMTKFOaWGKWTBFUROSVOLSdaMVaR|KOWTJMTKFOaWLPeaHLWTPWaKGNVSNWbS|KOWTJMTKFObWGKWTBFTPDGUQEJYUAEUR|KOWTJMTKFObWMRUNOSVOLJWSHLYUGKaV|KOWTJMTKFObWMRUNOSVOLJXTIMfbMQaV|KOWTJMTKFObWMRVMIRUNOSNKSbfWGNaV|KOWTJMTKFObWOSVOLbfWMQUREJWSJMSO|KOWTJMTKFObWOSVOLbfWMQXTEJURJMaV|KOWTJMTKFObWOSVOLbfWMQXTEJURJMTP|KOWTJMTKFObWOSVOLbfWMQXTIMWSEJSO|KOWTJMTKFOUQMRVMIRZVEIVMIRcZAEbW|KOWTJMTKFOUREJbWGKZUJNUQNUQZLPYU|KOWTJMTKFOURGKbWMQWSLPSLHOaWEJWS|KOWTJMTKFOURGKbWMQWTLPebPWbLHOfb|KOWTJMTKFOURMQbWGKWSLPSLHOebCFaW|KOWTJMTKFOURMQbWGKWTLPebPWbLHOfb|KOWTJMTKFOVRMVaREJUQBFZUJMQJFVda|KOWTJMTKGNVRMVaKFObWEJUQDGZVGKYU|KOWTOSVOLSTPHLaVLOeaFKUQJNYUGLPG|KOWTOSVOLSURJMYUMVaRFJeaJMaVGLVO|LOUQHLYULPVSOVZSIMaVKNcYEISOGKea|LOUQHLYULPVSOVZSJMQJENSJFMWTPWbS|LOUQJMQJFMWSHLYUMRUNKRVMIRbWOVZS|LOUQJMQJFMWTMRVMIRbWEJTPAEWTEIfb|LOUQJNWSNWbLGPfbEJbWHLYUAEURJNZU|LOUQJNWSNWbLHOfbKNVRNUYREJbWBEZU|LOUQJNWSNWbLHOfbKNVRNUYREJbWBEZV|LOUQJNWSNWbLHOfbKNVRNUYREJbWJMQJ|LOUQJNWSNWbLHOfbKNVRNUYREJZVBEbW|LOUQJNWSNWbLHOfbKNZUNScZEJaWJMQJ|LOUQJNWSNWbLHOfbKNZUNScZEJURJMQJ|LOUQJNWSNWbLHOfbKNZUNScZOTXOSLUR|LOUQJNWSNWbLHOfbKNZUNSVRSVRMIRUN|LOUQJNWSNWbLHOfbKNZUNSVRSVRNVZcV|LOURJMWSEJSLHObWJNfbNUZJFMWSGLbW|LOVRJMaVHLWTLPUQPWbLGPQJEUZQAEfb|LOVRJNWTFJTPJMZVMQcZGLPGCLbWLPeb|LOWSGLbWKNUQFKZUBFURNUQZKNZUFKUQ|LOWSGLbWKNURNUYRJMRNLPSLPGXTHLVS|LOWSGLbWKNURNUYRJMWTEJTKFOaWMQRN|LOWSGLbWKNURNUYRJMWTEJTKFOfbBFaW|LOWSGLbWKNURNUYRJMWTEJTKFORNAEfb|LOWSGLbWLPSLPGWSJMfbMQSOKTXOEJbW|LOWSGLbWLPSLPGXTHLTPJNVREJZVJMUQ|LOWSHLbWJMUQMRVMIRSNRUYROSXTSJTP|LOWSHLbWJMUQMRVMIRSNRVaROSXTSJTP|LOWSHLSNJSXTOXVHIMbWEJfbAEWSMQbW|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRda|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRUQ|LOWSHLSNJSXTOXVHIMbWMRUNKRWSEIZU|LOWSHLSNJSXTOXVHIMbWMRUNKRWSFJZV|LOWSHLSNJSXTOXVHIMURMVaREJYUAEZV|LOWSHLSNJSXTOXVHIMZVEIURAEbWEJYU|LOWSHLSNJSXTOXVHIMZVEIURAEbWFJfb|LOWSHLSNJSXTOXVHIMZVEIURAEbWKNRK|LOWSHLSNJSXTOXVHIMZVEIURAEbWMQfb|LOWSHLSNJSXTOXVHIMZVEIURAEbWMQWS|LOWSHLSNJSXTOXVHIMZVEIURAEcZKObW|LOWSHLSNJSXTOXVHIMZVEIURAEcZKOZU|LOWSHLSNJSXTOXVHIMZVMQVSQZcVEJSO|LOWSHLUQKNZUNWaKFObWLPeaGKWTPWaT|LOWSHLURJNSJEUYRLPbWOTXOKTZUAEfb|LOWSHLXTOXSNJSVHIMbWEJUQMRZVAEVM|LOWTJMbWEJWSAESLGWaTCGTPMRUNKaeV|LOWTJMbWEJWSBESLGWaTJNfbDGbWGLTP|LOWTJMbWEJWSBESLGWaTJNfbDGbWGLUR|LOWTJMbWEJWSBESLGWaTJNfbDGURNUZJ|LOWTJMbWEJWSBESLGWaTJNfbMRVMIRZV|LOWTJMbWEJWSBESLGWaTJNTPDGXTMRVM|"+
        "LOWTJMbWEJWSBESLGWaTJNTPMRVMIRfb|LOWTJMbWEJWSBESLGWaTJNTPMRVMIRXT|LOWTJMbWHLTPMRUNKRVMIRWTEJTKFOfb|LOWTJMbWMRUNKRVMIRTKGNebHLWSNWbS|LOWTJMbWMRUNKRVMIRTKGNfbFKXTHLbX|LOWTJMbWMRUNKRVMIRTKGNfbHLWTCGbW|LOWTJMbWMRVMIRUNKRTKGNfbFKXTHLbX|LOWTJMUREJbWJNfbNUZJFMTPMQWTAEaW|LOWTJMUREJbWJNfbNUZJFMTPMQWTAEdZ|LOWTJMUREJbWMQTPOTXOKTWSTXRMIRVM|LOWTJNbWNRUNKRVMIRTKGNXTCGfbRUYK|LOWTJNbWNRVMIRUNKRTKGNebFKWSNWbS|LOWTJNVRFJTPJMUQNUQJENZQAEdZEJaV|LPUQGLYUDGcYJMQJFMWTPWbSBFfbLOSL|LPUQGLYUDGVRJNZVEJcYLORMIRVMNSWE|LPUQHLWSKNbWFKZUKOURNUQZGKYUDHUQ|LPUQHLYUKOVRJMQJFVaRDHeaOSWNPTXO|LPUQHLYUKOWTPWaKFObWLPeaGKWTPWaT|LPUQJNWTPWbJENXTHLTPAEfbLObXDHVR|LPURJNWSNWaTPWbSKNRKGWebFKbSHLSO|LPVRHLZVLOWTPWbLGPfbKObWFKWSBFSL|LPVRJMUQMVaREJZUJMQJFVWTPWbZAEfb|LPVSHLXTKOTKFVaRJMZVMQcZLOeaCFbX|LPVSHLXTKOTKFVZSGKSNKRUNJSWNIMbW|LPVSHLXTKOTKFVZSGKURKOSNJSWNOTbW|LPVSHLXTKOTKFVZSGKURLOSLPGWSJMSN|LPWSGLSOKTXOLSVOJMbWMQUREJfbJMYU|LPWSGLSOLSVOKTXOIMZVMRVMJZcVDGYU|LPWSIMUREISOKTXOGLYULSVOMVaRJMda|LPWSJMSOKTXOMQbWEJfbJMVRMVZSQZcV|LPWSJMSOKTXOMQbWEJWTPWaTJNURNUYR|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGaW|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGbW|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGRN|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGYU|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGZU|LPWSJMSOKTXOMQUREJbWJMfbGLYULSVO|LPWSJMSOKTXOMQUREJRMIRVMGLaVLSVO|LPWSJMSOKTXOMQUREJRMIRVMJNMIGLaV|LPWSJMSOKTXOMQURFJbWJMWSGLYUEJaW|LPWSJMUQEJZUKNcZNWbSBEfbFKSNKRUN|LPWSJNSJFMaWMQWTPWbSEJfbKNbWJMSJ|LPWSJNSJFMaWMQWTPWbSIMSOKTXOEIfb|LPWSJNSJFMXTPWbSHLfbBFbXLPSNKRUN|LPWSJNSJFMXTPWbSMQURHLfbBFbWKOYU|LPWTPWbSGLSOKTXOLSVOIMZVMRVMJZcV|LPWTPWbSIMfbKNbWMRVMJQSJENaVAEUR|LPWTPWbSIMfbMQSOKTXOEIbWJMWTAEeb|LPWTPWbSIMUQEIZUBEURJNSJEUQZKNfb|LPWTPWbSIMUQEIZUHLebKNcZNWbSLPfb|LPWTPWbSIMUREISOKTXOGLYULSVOMVZS|LPWTPWbSIMUREISOKTXOMQfbJMaWFJWS|LPWTPWbSIMXTKNTPNWaTMQfbJNbWFKWS|LPWTPWbSJMXTMQTPIMSOKTPWFKUREIWT|LPWTPWbSJMXTMQTPIMSOKTPWFKVRMVZS|LPWTPWbSJNSJENXTAEVREJTPHLfbJMUQ|LPWTPWbSKNaWGLXTFKTPKOPGCLURNUYR|LPXTKOTKGNVSFKaVHLbXLOSLPGebBFUR|LPXTKOTKGNVSHLaVLOSLPGbXJMWTMRVM|LPXTKOTKGNVSHLaVLOSLPGeaJMWSNWbS|" +
        "JNXTEJTPIMVSMRZV|KOXT|KOWTGKTPCG|JNVREJaVJMXTLPUQ|IMUQEIYUAEUR|IMUQEIZUAEWS|IMUQKNWTGKTP|JMUQFJZUBFUR|JMUREJYUMQcY|JMVRMVaREJZV|JMVSFJUQBFZU|JMVSKOWTOVZS|JMWSEJbWLOSL|IMUQEIZUBEUR|JMUREJWSAEaW|JMURLPWSPTXO|JMVSKOaVGKUR|JMWSEJbWAEeb|JMWTMQbWLPTO|LPWSKOSLHOUR|IMURMQRMEIWT|JMVRMVaREJWT|JMVSEJUQKNZU|JMVSLOSLHOUQ|JMWTLOTPMRVM|JNVREJaVLOWS|LPWSKNURNUYR|IMUQEIWTKNTP|LOWSHLaWKNUQ|JNXTEJTPJMVS|JMWTLObWEJVS|JMXTLOTPMRUN|JNWTFJbWLOVS|LOWSHLSNKRUN|JNVSEJaVLOSL|JNVRFJWTLPZV|JMWTMQURLObW|JNUQLOZUOTXO|IMWTMRVMJQTP|JNWTLPURNUYR|JNWTNSVOLSTP|IMXTKNbXMQUR|LOWSGLUQLPSL|KNVRFKZVLOUQ|JMXTLPbXGLfb|LOVSOVZSKOSL|LPWTPWbSJMUR|LOWSHLbWKNUR|JMURLPWSHLSO|JMVRMVaREJea|JMXTFJTPMQWS|JMVSFJWTKNbW|JMWTEJVSKOTK|IMWSMRVMJQUR|JNWSNWaTIMea|JNVSEJURNUZQ|JNURNUZQEJWT|JMWTEJVSMQSN|IMUQEIWSKObW|LPVRJMaVMQWS|LOWSJNSJFMbW|JNWTNSVOLSaW|IMURMQWTLPTO|LOURJNYUNSWN|JMWSEJbWKNUR|IMUQKNYUFKVR|JMXTKOTKFOWS|KNXTLPVSIMUQ|KNVRGKWTLPbW|KNVSIMUQMRXT|JMUQFJWTBFTP|JNWSNWaTEJda|LOUQJMQJFMVS|IMWSMQSOLSVO|LOWTHLTPJNVR|JNXTLPbXGLeb|KOWTLPTKGNUR|LPWSIMSOKTXO|JMWSMQbWLPSO|LOWTJMaWMRVM|JNVRFJaVJMXT|JMWTLOTPMQbW|LPWSGLUQLOSL|JNWTLObWGLTP|JMUQLPQJFMVS|LPWSGLbWKOfb|KNWSNWbSJMXT|KNVRGKZVLPUQ|IMWTMQaWLPea|JNWSNWbSKOfb|JMWSFJbWKNXT|JNWTEJaWLOVR|IMXTMQTOKTWP|JMWTLOTPEJbW|LOUQHLWTJNQM|JMWTMQTPLOUR|KOWTGKTPCGUR|JNVREJZVBEWT|JNVRFJXTJMaV|LOWSHLbWJMWT|JMVSMQaVLPea|JNXTLOTPNRVM|JMUREJWSAESO|JNUQEJZUAEVR|JNWSNWaTEJUR|LOWTJMTPMRUN|IMURMQWTLObW|JNURNUZQIMQJ|JMWTKNbWMRVM|KNWSNWaTJMVS|KNWTLPVRPWaT|KNVSIMXTMQTO|JMURMQYUEJRN|KNVRFKaVJMXT|LOVSOVZSJNSJ|JNXTIMbXEJUQ|JNWSNWaTLPTO|JNWSNWaTEJTP|JMWTFJUQBFVS|JMWTEJbWAEfb|JNWTLOaWNRVM|JNVREJaVBEXT|KOWTLPTKFObW|JMWTFJUQBFTP|KOWTFKTPBFVR|JNWTLOaWGLTP|KNXTJMTOLSVO|JMWTLObWEJUR|JNVRLPZVFJUQ|JMWTMQTPEJUR|JNVRFJXTJMTP|JNVREJaVJMWT|JNXTLOTPNRUN|JMWSMQbWEJWT|LPWSGLaWLOSL|JMWSMQbWIMUREISNLPWS|JNVRFJaVJMWTEJbWLOTP|JNVRLOWTEJbWJMTPMVZJ|JMWSMRVMIRUNKRXTRVaRLOSLHXZV|JMWSKOUQGKQJEWaTIMYUMQURAETP|JNVSEJUQAEZVIMYUEIURNUQZKNXTMQTOIMbXLPOKFOSLHOWTPWaI|JNVSEJUQAEZVIMYUEIURNUQZKNXTMQTOIMcYLPbXGKebKTXOMRVMHLOHQUYKFXMFBK|JNUQNRVMIRWTLObWEJTPOTXOKTWSTXfbRVaRJMRIBEIKGf|JNUQNRVMIRWSEJbWAEfbLOSLHOWSOVZSKOSLGPcZCGbWGKZVEIVMIRWSKOSLPGdZBEXTJNaWGKZVRaeVFJYUDGURNUQZ|JNUQNRVMIRWTLObWEJTPOTXOKTWSTXZVJMQJFMfbAEcZCFZUFKUNKRdZBFbWHLYURYZUYRSNRKWTXOVSOVaB|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUQMUYMIAEaVEJfbJNeaFJZUYRVFCJaVNSdZHLVRSWTaKNRTJMIRLOTKGf|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUQMUYMIAEaVEJVRJNRMNSIEBRZVRadNKRTB|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUQMUYMIAEaVEJeaJNVRNUZQFJdZCFfbKNTRBEIKGf|JMUQMRVMIRWTKNbWFKTPLOZUEJWTAEaVRaeVNSdaSZcVJNURNUQZEJYUBEUQJNZUCFURNUQZFJaWJNWSNWTaKNfbEIbWIMWTNRTKGNXTDGTONSOKGNVOMQZVRUVRUZRKQUKFUYFBYcaWcY|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUQMUYMIAEaVEJeaJNVRNUZQFJdZCFaWHLfbKNTRBEIKGdPGdC|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUQMUYMIAEaVEJeaJNVRNUZQFJdZCFaWHLZVJNVRNUQZKNTRBEIKGdPGdC|JNUQNRVMIRWTLObWEJTPAEWTJNZUOSdZEIebIMQJFMUQBEQARVaRNdAWKOTKdB|JNUQNRVMIRWTLObWEJTPAEWTJNZUOSfbSVTOKTPWFJWTGLTPLOPLOSdZHOQMJQbWSbZAQZcM|JNUQNRVMIRWSLOSLHObWKNWTGLTKNGfbLOZVEIVMIRcZAEZVEIVMIR|JNUQNRVMIRWTLObWEJTPJNWTAEZUOSfbSVTOKTPWFJdZGKZSKOSLHOWTJMQLDGUNGd|JNUQNRVMIRWTLObWEJTPAEWTJNZUOSfbSVTOKTPWFJdZGLZSLOSLHOcZEIWTCGTKJMQSGdUNdG|JNUQNRVMIRWTEJbWLOTPAEWTJNZUOSfbSVTOKTPWFJWTGLTPLOPLVZcFCJLSNf|LOUQJNWSNWbLHOfbKNZUNScZOTXOSLURLObWEJRMIRVMAEebEIZUIRUEBIYUFJURGKaVJNbXNUQZCFZUFJWSOTXMIYSNYcdZDGNJGKJEKNEANRVMcI|LOUQJNWSNWbLHOfbKNZUNScZOTXOSLURLObWEJRMIRVMAEebEIZUIRUEBIYUFJURGKaVJNbXNUQZCFZUFJWS|JNUQNRVMIRWTEJbWLOTPOTXOKTZVJMQJFMWSTXcZMQVMQJ|JNUQNRVMIRWTLObWEJTPAEWTJNZUOSfbSVTOKTPWFJdZGLZSLOSLHOcZEIZVBFVMIRWTJMQLDGUNGd|JNUQNRVMIRWTLObWEJTPJNWTRUYRNUaVAEebFJcYJNYRNUVRUNPLGWbA|JNUQNRVMIRZULOUNKRdZFKZUKNcZCFZVEIVMIRWTFJTKJMQSGdUN|JNUQNRVMIRWSEJbWBEZULOSLHOUNJbfWEJYUAEUREIaVGLeaJMQJFMcZDHWSLPSLHO|JNUQNRVMIRZUKNWTFKTPLObWHLWTCFfbFJdZEIZVJMQSIMUNKRTKGdPGRaeVDK|JNUQNRVMIRWTEJbWLOTPOTXOKTZVJMQJFMWSTXcZMQVMQJaVBFfbAEYUFKSOKTPWEIWSGKbWHLURLPeaCFZUJMUQFJdZDHZUHL|JNUQNRVMIRWTLObWEJZVJMQJFMTPAEWTEIfbHLcZKNTKRUZSGfPG|JNUQNRVMIRWTLObWEJZVJMQJFMTPAEWTEJdZHLfbKNTKRUYICFKRBEIKGfPGDKebfZcVJNUQNRVMIRWSEJbWAEfbLOSLHOWSOVZSKOSLGPcZFKZVCFVMEIbWIRWSKOSLPGdZBEX" +
        "TGLTOLSaVRaeOJNZUFJURNUYRDGRMGKOFJCMIEJQMJQIEQUEAUY|JNUQNRVMIRWTLObWEJZVJMQJFMTPAEVSOVYURYaIHLWTEJeaLOdZCFfbKNTRBEIKGf|JNUQNRVMIRZVEIVMIRWTKNdZAEbWFKZUEITPBFfbFJWTRVaRJMQSKOTKGfPGCL|JNUQNRVMIRZVEIVMIRWTKNdZAEbWFKZUBFTPEIQMKOMVOTXOLQ|JNUQNRVMIRZVEIVMIRWTKNbWAEdZFKZUBFTPEIWTFJcZKOTKJMQSGdUNdG|JNUQNRVMIRWTKNTPFKXTLObXHLZUEJdZBEZVJMQSEIVMIRUNKRTKGdPG|JNUQNRVMIRWTKNTPFKXTLObXCFZUFJaVRaeVNScZEIfbHLdaIMURJNRINRVMSWbSOc|JNUQNRVMIRWTLObWEJTPJNWSNWaTAEfbFJdaRUYRJMQAKNALHOTKGf|JNUQNRVMIRZUKNdZLOZVEIVMIRcZBEWTFJTKJMQSGdUNdG|JNUQNRVMIRWSEJSNJSZVSZcMAEMIEJXTLPYUPWbSHLfbKObWOVaRGKRMLPURDHdaHLebLORNKRMVOTVSJMQJFMIRTXaVXeSNBFWSFKNGCLSNLONJOSVOeX|JNUQNRVMIRWSEJbWAEfbLOSLHOWSOVZSKOSLGPcZJNZVEIVMIRdZFKZVBEVMEIaVIaeVDGbWKOYUGKVROSRMSbXeCFMIFJURNUQZKNZVPTeaTXaWNSWEXbEAbeVReMIR|JNUQNRVMIRWTEJbWLOaVRaeVAEVRJNZVNUYRFJTPEIWTBEdZJMQAKNALHOTKGd|JNUQNRVMIRWTEJbWLOaVRaeVAEVRJNZVNUYRFJRMCFWSGLTPDGMIKNVROMID|JNUQLOZUEJWTNSVRJNTPAEcZEJaVHLXTOXVHJMQSKNSJFc|JNUQLOZUEJWTNSVRJNTPAEcZIMQABEAJFcdZcVaRCFbWSbfWOSeaSbXeFJaWHLUQNUYRKNRKGNPGDKeaNRWSJMQJKNSONEOKRUKGUZaVZSGCSW|JNUQNRVMIRZULOUNKRWTHLTKGNaVRaeVEIYUAEbWEJfbLPcYCGURNUYRGKWSIMRIBEIBKOBTPfSOfSOKScQMJQKFQUFBcSXTSfTOUYOL|JNUQEJWTAETPLObWNSWNKRVMIRaWGKfbEIPLDGLSRUYRJMQJFOeaBFaVGLWTLPbWCGcYIMZUOSVOMQOLHOUROSWNPWXTWPYUQZdUPTUQTWQMWbNJbfJLKOLSfQRNQF|JNWTEJbWJMfbMRVMIRTPAEWTEJUQJMQSKOTKGfPGDK|JNWTEJbWJMfbMRVMIRTPAEWTEJZVJMUQKOQSRUYRFJTKGfPGDKcYKOYUCF|JNWTEJTPJMbWMRVMIRfbLOWTAEaVRaeVEIUQFJYUNScYKNTRBFVOJMQJFc|JNWTEJTPJMbWMRVMIRfbLOWTAEaVRaeVEIUQFJYUNSVRJNQMBFUQNUZVIadNKRTB|JNWTEJTPJMbWMRVMIRfbLOWTAEaVRaeVEIUQFJYUNSVRJNQMCFbWSbXeOXebXedaeVZLHOMJ|JNWTEJTPJMbWMRVMIRfbLOWTAEaVRaeVEIUQFJYUNSVRJNQMHLMJNEbWSbXeOXebXeUQeMQA|JNWTEJTPJMbWMRVMIRfbLOWTAEaVRaeVEIUQFJYUNSVRKNTKSVRaJMQSGf|JNWTEJTPJMbWMRVMIRfbLOWTAEaVRaeVEIUQFJYUNSVRKNRKOF|JNVREJZVJMUQNUQJFMYRAEWSKORNLPSLHOVSOVaRMVNKGNXTPWbA|JNVREJZVJMUQNUQJFMYRAEWSKORNMQaWIMXTOXNKGNSA|JNVREJZVJMUQNUQJFMYRAEWSKORNCFaWFKXTKaTKaTbWTadWGNSA|JNVREJZVJMUQNUQJFMYRAEWSLOSLHObWEJWSGLXTOXRNKRSOLZdE|JNVREJZVJMUQNUQJFMYRAEWSLOSLHObWBFWTEJfbGLTPJNPGNUGNOTXOFKNGCZcVUY|JNVREJZVJMUQNUQJFMYRAEWSCFcYMQYUQZVcKOaVGKcZEJZULPSLHOUQJNQMNUMJFMVSOVXTPWbJ|JNVREJZVJMUQNUQZFJWSBFYUKNUQNWbSMRVMIRSOLSaVRadEAJZUHLURLOea|JNVREJZVJMUQNUQJFMYRAEWSCFcYMQYUQZVcEJRNKRSOLSaVRadE|JNVREJZVJMUQNUQJFMYRAEWSCFdZKObWGKSNDGXTOXVSMOWTKRTD|JNVREJZVJMUQNUQJFMYRAEWSBFbWEJfbMQdZKOWTLPTBPTXOCFBKGfSN|JNVREJZVJMUQNUQZKNWSNWbSLPYUMQfbAEURGLbWEJRMIRVMDGaVGKcYKOYUCGdaPTWPGKPEBYSLHO|JNVREJZVJMUQNUQZKNWSNWbSLPYUMQURAEfbEJRMIRVMGLbWDGaVGKcYKOYUCGURGKdaBEXTOXMIPTWNXbIKbfNEfI|JNVREJZVJMUQNUQZKNWSNWbSLPYUMQfbAEbWEJURJMebBESNHLWSEJNEIBRIBEIKGf|JNVRFJZVJMUQNUQZMRVMIRZULOUNKRdZEJWSOVZSCFaVRaeVGLcZLOSLHObWJNZUAEUQEJYUFKVRBERMDGMFKBURNUQZEJWTOSfbJNbWSbXeNSebBFTPFKZUSVbWKNWTVaTO|JNVREJZVJMUQNUQZAEWSEJSOLSVOKTXOJNbXGLaVLSVODGeaGLaVLSVOCGXTGLYULSTOSLURMVZC|JNVREJZVJMUQNUQZAEXTLObXEJfbMQZUQSWEIMEAFJALGf|JNVREJZVJMUQNUQZAEXTMQTOLSVOKTWPEJbWJNfbHLWTFKbXLOaVBFebNRVMQJYUJNbWFJZVJMVRMVWSNWTROSUQKNRKGNdaNRQMSVaWRUMJUZWSVOcVDGVRGKRMIRJERUEBUYPLOHBTYcTW|JNVRFJZVJMUQNUQZMRVMIRWTKNTPLObWEJZVBFVMJQWSNWaB|JNVRFJZVJMUQNUQZMRVMIRWTKNTPLObWEJZVCFVMJQPLGPWTPWaR|JNVREJZVJMUQNUQZMRVMIRWSFJbWLOSLHOWTJMZUCFUNKRTKFOfb|JNVREJZVLPUQNUQZHLWSKOYUJMbWMQURFKSNAEebCFNJEUVRUNWTPWbCQUZQIMQJKNJSOeCQBFQCLPCLPG|JNVREJZVLOWTNScZIMRIKNTRJMVOMcURcLbWLcaVcbfWFJ|JNVREJZVLOWTNSUQSZdUIMRIBEIBAEBIJMILGdQMdJbWJbfW|JNVRLOZVEJWTNSUQSZdUAETPJNbWEJWTHLaVNScZSWTaOSVHJMQJFc|JNVREJZVLOWTNSUQSZdUAETPJNbWEJWTHLaVNSeaSZcVOSVHJMQJFe|JNVREJZVLOWTNSUQSZdUAETPJNbWEJWTHLaVNSfbSZcVJMQJFMUQKNQSCFTKGfPGDK|JNVREJZVLOUQNUQZAEWSGLYULPSLPGXTJNbWHLTPFJebIMWSNWbSKNUQNWaTLOTKGNcYBFVSNWdaWUYKCGKFJCQMCFMIFJfbDHbW|JNVREJZVLOUQNUQZAEWSGLYULPSLPGXTJNbWHLTPFJebIMWSNWbSKNUQNWaTLOTKGNcYCFPLEIdaBEZUFKLGKOGCDGCSNdURdZVcMV|JNVRLPZVHLUQNUQZIMWSKOSNMQYUFKURBFbWDHWTPWaTFJRMKITD|JNVRLPZVHLUQNUQZIMWSKOSNMQYUFKURBFbWDHWTPWaTEJNEAJRNKaTD|JNVRLPZVHLUQNUQZIMWSMQYUKOSNFKURBFbWDHWTPWaTLPcYPWdaWUVSOMYBKRBY|JNVREJZVJMUQNUQZLOWSGLbWLPSLPGfbKOWSHLbWAESNJNVREJaVJMXTMQbXLOfbGLTPAEPGCLXTOXRMITeaXVZCQZCABEAGDKcVKOdaHLYULPUROTVSTXaWPTWPXbRNbePLeMLHM" +
        "QHD|JNVREJaVJMXTMQbXLOfbGLTPBEPGCLXTOXRMITeaXVZCQZCa|JNVREJaVJMXTMQbXLOfbGLTPOTPGTadWCLXTLPVSFJZVQZTOKaRKaRcF|JNVREJaVJMXTMQTPFJWTLOdaOXRMIRVONRUNGLPGCJbWJMYUDGWSBFebXOURMVZJ|JNVREJaVJMXTMQTPFJWTJMbXLOdaAEaWEJWSNWTaCFfbBERNKRUNJSbWSbVRMVZA|JNVRFJaVJMWTMQTOLSVFBKXTHLbXLOfbEJeaAEaWDHTPHLRMIRXTOedaeVZSQZcH|JNVRFJaVJMWTMQTOLSVFBKXTHLbXLOfbDHdaIMRBAEBINRILGd|JNVRFJaVJMWTMQTOLSVFBKXTHLbXLOfbEJeaDHaWAETPNSWNJSdaHLbWSbXeCFaWOTZVQbeH|JNVRFJaVJMWTMQTOLSVFBKbWHLWTLOfbEJeaDHaWAETPNSWNJSdaCFbWSbXeHLaWOSWNFJRMJSZVIaeHQZcV|JNVRFJaVJMWTMQTOLSVFBKXTHLbXLOfbEJeaDHaWAETPOSRMIRZVRTXMQJ|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGLYUDGdZGKZVSZUdOSbWSbXeAEMIJNfbKOQMEJbWJQIEBIWSNWaB|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGLYUDGdZGKZVSZUdOSbWSbXeAEMIJNfbKOQMNSbXLPcZCGaVSWdaWUVRUNMJFMIDOSebSVDHVabWaTXOEJHD|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGLYUDGdZGKZVSZUdOSbWSbXeAEMIJNfbKOQMNSbXLPcZCGaVPTebEJIEBadE|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVMIEJUQGKYUKNbWAEdaNRUNJbfWEJaRJMQJFV|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVMIEJUQGKYUKNbWAEfbFKdaLPaRCGRMKOMFBKIBNSWNKYBTPf|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVMIEJUQGKYUKNbWAEfbFKdaLPaRCGcYGLRMKOMFBKIBNSWGLCBTPf|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVMIEJUQGKbWKNYUAEfbFKdaLPaRCGcYGLeaLORMDGMFNSWNKRUNBRIBGLBTPd|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVMIEJUQGKYUKNbWAEfbFKdaCGaRLPcYGLeaLOaVDHXTOeRMeRMORVOKNGURVMQA|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVMIEJUQGKYUKNbWAEfbFKdaCGaRLPcYGLeaLOaVDGXTOeRMeRMOBFIDRIDRIBURBERMESMIPTQMTXYUXbURbf|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVMIEJUQGKYUKNbWAEfbFKdaCGaRLPcYGLeaLOaVDGRMGLMFNSWGBDIBDGBTPf|JNWTNRUNKRVMIRTOLSZURVaRHLRMSVXTEJMIGKUQDHYUVZcVBEIBJMQJFMBOLQ|JNWTNRUNKRVMIRTOLSZURVaRGKRMHLUQEIeaIRaVRadP|JNWTNRUNKRVMIRTOLSZURVaRGKRMEJMIHLcZSWbSJMIRKNRKFc|JNWTNRUNKRVMIRTOLSZURVaRGKRMEJUQHLeaKOcZDGbWSbfWGKMILPWTPWaTKNTRJMQJFc|JNWTNRUNKRVMIRTOLSZURVaRGKRMEJUQHLeaKOcZDGbWSbXeOSfbLObXAEMIJNebEJbWSbXeNSebGLbXSVaRJMQJFc|JNWTNRUNKRVMIRTOLSZURVaRHLUQGKYULORMEJeaDGbWSbXeKNMINSfbGLaVSZcVJNbWAEWTOXebXeVReMQANRUNFJNELOdZOSZUCFUQFKQMSWMJWbJFbeFOeXOLXKLHKD|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOYUGKRMEJeaDGbWSbXeKNMINSfbGLaVSZcVJNbWAEVSOVeaVeWSNWUReMQAWadWLOANOSNASbAfFKfSCGSHKNHDGKDHNRHDKNDGBFIEFKGDRUEANRDNRKAS|JMWTMRVMIRUNKRTOLSZURVaRGKRMHLUQEJYUKOeaAEMIFKbWSbXeJNURNUQZEJfbLPbWOTZVDHdZHLZUTXcYCGUQLOYUGLUROTRMBFVRLORNJbIEbfEBfABITWaTPW|JNWTNRVMIRUNKRTOLSZURVaRHLUQLOdaGLRMEJYULPcZAEMIDGaVGKeaOTVOKNaVTKQMJQXTPWbA|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOdaGLYUDGRMEJcZSWaDCGDEBYbWAEQMEI|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOdaFJYUGKcYKNRTSWbSJMQJEd|JNWTNRVMIRUNKRTOLSZURVaRHLUQLOdaGLYULPRMEJcZBEUREIaWAEWNJSeaDGaWPTWPGLPGCLbWSbXeLPfbPTeaOSbXSWXOWNMJFMQA|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOdaGLYULPRMDGcZEJMIGKaVPTeaTWaTKNTRJMQJFMVOMcOKcYUQYD|JNWTNRVMIRUNKRTOLSZURVaRHLUQLOdaGLYULPRMEJcZBEUREIaWAEWNJSeaDGaWFJMFCJWNJSXTOeZUeMQASV|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOdaGKYUDGRMEJURAEMISVRMJNaRNUQZEJbWJQ|JNWTNRVMIRUNKRTOLSZURVaRHLUQLOYUGKRMDGeaEJbWSbXeAEMIKNURNUQZJNfbNSZUGLUQLPQMPTcZTXaWFJMFBKWGCLIBLPBTPfZVfN|JMVSMQURKNRKFVaREJeaLOaVBFWTGKTPCGbWJNWTNUYRFJfbAEbWJNcYNUYREJWSKNSCNUCMIadWUd|JMVSMQURKNRKFVaREJeaLOaVBFWTFKTPCFdaAEYUJNRMIYVRNWbAQUXTUZcVYcTOcLPN|JMVSMQURKNRKFVaREJeaLOaVBFWTFKTPCFdaAEYUJMVSOeXTeOfbMVZAQZcV|JMVSMQURKNRKFVaREJeaLOaVBFWTFKTPCFbWJNWTNUYRFJfbAEbWJNWSNUSCEJCMIadWUd|JMVSMQURKOaVEJWTJMTKGWbSLPfbHLbWFKSNDGWTPWVSMOeaKRaD|JMVSMQURKOaVEJWTJMTKGWbSLPfbHLeaDHbWFKRNKRXTLOTKQUZJIMJQCFVMFe|JMVSMQURKOaVEJWTJMTKGWbSLPfbHLbWFKSNBFNGDKRNKTXH|JNVRFJWTLOTPJMbWMVZJENWTAEUQEJdZHLfbJMQSOVZSKOTKGdPGDK|JNVRFJWTLOTPJMbWMVZJENWTAEUQEJdZNRZUBEUNJScZSWaVWaVRadPLGWfbdNbA|JNVRFJWTJMTPMVZJENUQAEbWLOWTEJdZNRZUBEUNJScZSWaVWaVREJeVJMQJKNJLHOTKGd|JNVRFJWTJMTPMVZJENUQLObWAEWTEJYUNSfbJNdZIMQJNEURGLPWCGTKGd|JNVRFJWTJMTPMVZJENUQLObWAEWTEJYUNSfbJNdZIMQJNEUQEJaVHLeaJMQJKNTRBEVHEf|JMURLOWTEJbWJNTPNUZJFMWTMQfbAEbWGLPNIMTKMRVMQb|JMURLOWTEJbWJNTPNUZJFMWTMQfbAEdZEJVRGLPECGTKGf|JMWTLOUREJbWJNTPNUZJFMWTMQfbAEdZHLVRIMRIKNTRBFIKGfPG|JMURLOWTEJbWJNTPNUZJFMWTMQfbAEVRQURMIRcZEJZQKNTKJMQSGf|JMURLOWTEJbWMQWSJMSLGWaTAETPEJZUQSXTMVTOSLPEJMURLOWTEJbWMQWSJMSLGWaTAETPCGfbKOZUQSdZMVbWSbZA|JMUREJWTLObWMQWSJMSLGWaTAETPCGfbEJXTJNYUHLVSMXeaXVZCQZcVKOCJOTPWBFJC" +
        "LPCLPG|JMURLOWTEJbWMQRMIRVMGLMILPYUHLaVAEebCGVRJNWSOMIRPWbA|JMURLOWTEJbWMQRMIRVMGLMILPYUHLaVAEebCGVRJMWSPNbWMVZAQZ|JMURLOWTEJbWMQRMIRVMGLMILPYUHLaVAEebJMIREIdaCGcYIMRIDHUROSWNPUXTLPVSPWNJFObCUZCFKNYUBKUd|JMURLOWTEJbWMQTPOTXOKTRMIRVMGKMIJNWSNWebAEbSEJPWJMIRKNRKFe|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRMIRVMOSMIKNaVNRVORVZSBEIKGf|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRMIRVMJNMIFJaVNSdaKNTRCFVOBEIKGf|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRMIRVMJNMINSaVFJdaKNTRCFVOBEIKGf|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRMIRVMJNMINSZUQZdUFJUQCFcZKNTRBEIKGf|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRMIRVMJNMINSZUQZdUFJUQCFaWJNQMSVMJNEWSHLSZFJeaKNTRBFIKGfPGDK|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRMIRVMJNMINSZUQZdUFJUQCFaWJNQMSVMJNEWSHLSZFJZUJNeaNRUNKRTKGNPGDKaVRabWaTXFBKIB|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRMIRVMJNMINSZUQZdUFJUQCFaWJNQMSVMJNEWSHLSZFJZUJNeaNSaWSVWSVaSNKYTKGNPGDKbWaTXFBKIB|JMURLOWTEJbWAEfbMQTPJNWTNUYREJRMIRVMJNMINSZUQZdUFJUQCFaWJNQMSVMJNEWSHLSZFJZUJNeaNSaWSVWSKNTaBFIKGdPGDK|JMURLOWTEJbWAEfbMQTPJNWTNUYRFJaWJNcYNUYRKNTKNUWTGNPLHOTY|JMWTLObWEJTPMQWSAESLHOfbKNaWGLPGDKVRCGXTOXRMIReaXVZSQZcMJQSL|JMWSLPSOKTXOMQUREJRMIRVMJNMIGLaVLSVODGdaGLaVLSVOCGbWGKWTPWebKTbC|JMWSLPSOKTXOMQUREJRMIRVMJNMIGLaVLSVODGdaGLaVLSVOCGbWAEWTPWeaWUYD|JMWSLPSOKTXOMQUREJRMIRVMJNMIGLaVLSVODGdaGLaVLSVOCGbWNRfbGKeaKTbXQUZQRVaRTacZAERMad|JMWSLPSOKTXOMQUREJRMIRVMJNMIGLaVLSVODGdaGLaVLSVOCGbWGLWTLSebPWZVSZbCZdcZdUYR|JMWSLPSOKTXOMQUREJRMIRVMJNMIGLaVLSVODGdaGLaVLSVONRbWCGWSGKfbKTbXRVXOPTOXVOeaAEaWFKWTHLTPQUPNUd|JMWSLPSOKTXOMQUREJbWJMYUGLWSCGebAEaWGKWTPNbXKTXOLSVOMVZCQZcV|JMWSLPSOKTXOMQUREJbWJMYUAEWSGLfbCGbXEJSNJSaWSbVSMVXTPNZCLSCZbf|JMWSLPSOKTXOMQUREJbWJMfbGLWSCGZUQZdUMQcZIMRIBEIKGf|JMWSLPSOKTXOMQbWEJfbJMbXMRVMIRUNFKOFCbXTPWeXHLaTLPTODHdaBFaWGLWSPT|JMWSLPSOKTXOMQbWEJfbJMbXMRUNFKOFCbXTPWeXGLaTLPTOBFVSAEYUIMURMVXTPNZA|JNVRFJWTJMTPMVZJENUQAEbWBFfbNRQMRVaREJcZJQWTFJRMIRZUQZdE|JNVRFJWTLOZVNSUQSZcVJMQJEUYRAEdZEJZUBEUQJMQAKNALGd|JNVRFJWTLOZVNSUQSZcVJMQJEUYRAEdZEJZUJMUQKNQLGd|JNVRFJWTLObWJMTPMVZJENUQAEWTEJaVNScZKNTRBFVOJMQJFc|JNVRFJWTJMTPMVZJENUQLObWAEWTNRcZEJZVIMdZCFfbRUYIKNTRBEIKGf|JMUREJWSKORNAEbWLPSLJbfWHOVRMVZLDHYUHOWTPWaD|JMWSKObWFKUQBFQJFMYUMQfbEJURJMSNLPWSAESLHOaWCFXTOXVSMOeaXVZAKR|JMWSKObWFKUQBFQJFMYUMQfbEJURJMSNLPWSPTSLHObWOSXFSbeXCSVOMe|JMWSKObWFKUQBFQJFMYUMQfbEJURJMSNLPWSPTSLHOVSOVXFCSaWQUZJVFWNAE|JMWSKObWFKUQBFQJFMYUMQfbEJURJMSNLPWSPTSLHONJMFbWFJWPJNcYNUYRAEebEJRMIRVFCJZUQZdUJMaVKNUQOTQSTWSOWfOLGKLHfWXTWNPLNYTPYN|JMWSKObWFKUQBFQJFMYUMQfbEJURJMSNLPWSPTSLHOaWTadWAEWSDHSLHOXTOXbWEJNEIBRI|JNWTEJTPJMUQNRQJFMbWAEWTMQVMQJYUJNfbNRUNKRbWLOTKGNPLHOXTOXebXVZA|JNWTEJTPJMUQNRQJFMbWBFWTMQVMQJYUIMURMVaRAEeaEIaVJNZULOfbHLbWDHUQNUQZOSWNKadWFKZVIMcZKNZUMQVRQZRDLOTKZcKGCLPG|JNWTEJbWJMUQNRQJFMfbMQVMQJTOLSWEAJYUJNUQHLbWLOWTBEZUEJaVNScZJNeaCFURNUQMIRZQSZdNKRTB|JNXTLObXHLTPNRUNKRVMIRfbEJWTFKZVJMdZKNTKRUZSGdPGCL|JNXTLObXHLTPNRUNKRVMIRfbEJWTFKaVRaeVJNYUNSdaAEcYEJUQJMQJKNTRBEVHEf|JNXTLObXHLTPNRUNKRVMIRfbEJWSOVZSRUYRJMRIBEIKGfPGDK|JNXTLObXHLTPNRUNKRVMIRWTEJTKGNPGCLXTAEebRVaKFe|JNXTLObXHLTPNRUNKRVMIRWTEJTKGNPGCLXTAEfbFKaWBFbXLPTOKaeMJQXTPWdaWUYI|JNXTLObXHLTPNRUNKRVMIRWTEJTKGNPGCLfbLObWOSebSVZSRUYKFe|JMWSEJSOLSVOKTXOMQURJMaVAEbWGKWTEJZUQLTPMVPE|JNXTLPbXNRUNKRVMIRebEJZUJNcZAEaVRaTOaKXTPWbA|JNXTLPbXNRUNKRVMIRebEJZUJNcZBETOGLXTLSaVRabXSbXVPWdaWdUQdUYI|JNXTLPbXNRUNKRVMIRebEJZUJNcZGLZVNSVMFJWEAZdUPd|JNXTLPbXNRUNKRVMIRZVEIVMIRebAEcZFJTOEIZVJMOKGNWTPWbQ|JNXTLPbXNRUNKRVMIRZVEIVMIRebAEcZFJTOEIZVRUYRPTWPGLPGCZdUJMRNMRUQRKaV|JNXTLPVSHLSJENZVLObXFJUQGLYUCFURNUQZJMWSPNVRNUZC|JNXTLPVSHLSJENZVLObXFJUQGLYUCFURNUQZAEVRDHZUJNWSOMebPWbA|JNXTLPVSHLSJENZVLObXFJUQGLYUCFURNUQZDHZUJNWSNWdZWdURdNebPWbCLP|JNXTLPVSHLSJENZVLObXFJUQGLYUCFURNUQZAEVRJMWSPUZC|JNXTLPVRGLaVLObXHLWSPWSbLPUQNUYREJZUBEcYPTdaTWbLKOLSJMQJEd|JNXTLPVRGLaVLObXEJWSPWSbHLUQNUYRLPZUBEcYPTeaOSXOKTVXJMQJFe|JNXTLPVRGLaVLObXEJWSPWSbHLUQNUYRLPZUBEcYPTbWTadWDGfbOSVOKaeVFKXTGLbWLOTPCGWSOTPWGLRNKTSNJSQMIRUG|JNXTLPVRGLaVLObXEJWSPWSbHLUQNUYRLPZUBEeaOSVOKTXOJMQJFXJNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSEJRMBEMFCJeaOTVRTWaTXM|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSEJfbAEbWCFWTFKTPXbPNbfSLJZdU|JNXTLPUQNRVMIRZURVaRKN" +
        "RKFXURGKcZHLZVKOWTPWbSEJfbCFbWAEWTFKRMDHMFEJFMLPSLHOeaPWaTXbMJOXJEBIQMIadfKNYUNSURSWRNWafbXeNK|JNXTLPUQNRVMIRZUKNTOGKbXKTXOCGebGLQMRIWTLSaVSQYUQZcVPWbC|JNXTLPbXGLVSLOSLPGTOKTXOGKWTEJfbJMbXMQaVAEVREJZVQLTPNUPE|JMXTLPbXMQVSKNSJENURNUYRHLaVFKebCFcYLOdaAEWSPWbA|JMUQEJZUKOURFKWSLPSLHObWBEWSDHSLHOdZCFfbJNQJEf|JNURNUYREJWTJNRMIRVMAETPEIZVIRVMLOdZFJMFCJaVBEZUJMPLGPURNUVSOVXTPWbA|JNURNUYREJWTJNRMIRVMAEMILOTPNRcYEJbWOTXOKTZUJNdZFJUQGLPGDKWPRUYRNW|JNURNUYREJWTJNRMIRVMAEMILOTPNRbWOTXOKTcYEJZUJNdZFJfbCFUQGLPGDKWPRUYRNf|JNURNUYREJWTJNRMIRVMAEMILOTPNRbWOTXOKTcYEJWSHLPWRVaRJNRKFc|JNURNUYREJWTJNRMIRVMAEMINRTPLOcYEJbWOTXOKTZUJNdZFJaVRaWdTXZVHLfbLObWGKdaCFUQOSVOKTYUDGURNUQZJNZVGKPLFJWPKOLSNdPLdULHUYVSYDSODY|JNURNUYREJWTJNRMIRVMAEMINRcYEJTPLObWOTXOKTZUJNdZFJaVRaWdTXZVCFUQHLfbLObWGKdaOSVOKTYUDGURNUQZFKZVKNebXeVReMIDTaPLaeLH|JNURNUYREJWTJNRMIRVMAEMINRcYEJTPLObWOTXOKTZUJNdZFJaVRaWdTXZVHLfbDHeaXeVReMID|JNURNUYREJWTJNRMIRVMAEMINRTPLObWOTXOKTcYEJZUJNdZFJaVRaWdTXZVHLfbLObWGKdaCFUQOSVOKTPLFKWPKOLSNd|JNURNUYREJWTJMTPLObWOTXOKTcYAEWSTXebXefbeXSOXUZA|JNURNUYREJWTLObWJMfbMQTPAEWSHLcYEJXTOXSNJSVHKObWOT|JNURNUYREJWTLObWJMfbMQTPAEWSHLcYEJXTOXSNJSVHKObWOTaVTadWFJWSBFRNJMNJFKeaMF|JNURNUZQEJWSKObWGKYUBEebDGcZKNURNUWTGKSNJSQMIRZQSZdP|JNURNUYREJWTLPTOKTXOJMVSMVaRAEeaFJaWJMWTPUZA|JNURNUYREJWTLObWJMTPAEfbOTXOKTWSTXbWFKSNHLWSKOaWOTNKGUZATRPGCL|JNURNUYREJWTLOTPAEbWJNWTNUZQEJfbJNdZNSVRIMRIKNTRBEIKGf|JNURNUYREJWTLOTPAEbWJNWTNUZQEJfbJNdZNSVRIMQJFVaRGLPWCGTKGdXTdQcZQdTPdTPW|JNURNUYREJWTLOTPAEbWJNWTNUZQEJfbJNdZFJaWBEVSOVZSGLPGCLQMIRSOLSTOKaeF|JNURNUYREJWTLOTPJNbWNUZQAEWTEJfbJNdZFJaWBFeaOSVOGLPGCSaVDGVONRcYRVZSIMTPKaSNJSQLHObWSbXV|JNWTEJURNUZQAEYUJNVREJTPLOcYHLaVDHeaOSVOLSbWSbXeGLPGKDRKFOfbBFbWDGaVGKdaHLURJMQJFMYUCFUQFJebLPbXPTWPOSVFMeFMIRPL|JNVSEJaVKOUQGKZUDGURNUYRBEcYJMQJEUYRFJdZCFWTJNSCLPCSPd|JNVSEJaVKOUQGKZUDGURNUYRJNSJFMQJBEcYEUYRAEWTEJdZJNZUCFbWIMRIOSVOLbfWNSWNKYIEFJENGKNGHLGPYc|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKcZOTXMITSJTWbSCFJCLPCLHc|JNVSEJaVKOUQGKZUDGURNUQZKNYUIMUQAEVRNUSNJSQA|JNVSEJaVKOUQGKZUDGURNUQZIMYUBEVRMVURVMdaOVaB|JNVSEJaVKOUQGKZUDGURNUQZJMWTMRVMOVZSIRSNRVbWKRWSVOTD|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQEIZUMRVMIYdaOVaB|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQEIZUAEVRMVSZOSXTLPeaIMaVEIVOFKOFNRUEIKQJCFJCDGCLHe|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQEIZUAEVRMVSZOSXTIMURMVQMJQbXSbZA|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQEIZUAEVRMVSZOSXTLPdaNRUNFKNGCLWNPUQZJS|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQEIZUAEVRMVSZOSXTLPeaIMbXSbfWHLZVMRVMEIcYIRWSPWaTNPUE|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQEIZUAEVRMVSZOSXTLPeaIMbXSbfWHLaVMRVMEIURNUWSPNcYIRZVRaYBaeBIJMIH|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQMRVMOVZSEIXTIRbXDGeaGKaVRaQMJQSJFMTPaTXFCJPG|JNVSEJaVKOUQGKZUBEURNUQZKNZUFKUQIMYUDGcYNRUNKTdaOVaB|JNVSEJaVKOUQGKZUBEURNUQZIMYUMQWTJNSJENTPDGeaAEURNUVRUNXTOVZALOAbFJbEKNELHO|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQMRVMOVZSEIXTIRbXAEeaEITODGfbLPXTJMSJRUQZGLJQLSWNPf|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQMRVMOVZSEIXTIRdaLPcZRUTOUdOLHVaBdTBX|JNVSEJaVKOUQGKZUBEURNUYRJMQJEUcYLPYRIMSLHORIOTXOKR|JNVSEJaVKOURNUYRJMZUGKSNDGNJMQXTQSWNFVbXKRTD|JNVSEJaVKOURNUYRJMeaAEWTGKTPFJPNDGSLJSVOMe|JNVSEJaVKOURNUZQGKYUBEeaDGcZKNURNUWTGKSNJSQMIRZQSZdP|JNVSEJaVKOURNUZQGKYUBEeaDGcZKNURNUWTFKSNJSQMIRZQSZdNKRTD|JNVSEJaVLPUQGLZUKOURNUQZJMYUMRUNOTXOFKNGDR|JNVSEJaVKOUQGKZULPSLPGVRGLRMIRWSNWUPBEbSJMQJEWeb|JNVSEJaVKOUQGKZULPSLPGVRAEXTHLeaJMQADHASLOSLHM|JNVSEJaVKOUQGKZULPSLPGVRAEXTHLcZJMQANSWNBEAJFc|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEcYNRVFOeURBKIBeIBTIBTOBadWLO|JNVSEJZVKOUQGKYUBEURNUQZKNZUDGUQGKcYIMWTNPVSOVaBJMQJFMBTPWbS|JNVSEJZVKOUQGKYUBEcYDGURNUQZKNZUGKUQLPSLPGVSIMXTEITPMRbXIMXTAEYURYTOKTPLHVaDTaDU|JNVSEJZVKOURNUYRJMcZGKWTAETPFJPNDGSLJSVOMcaVcSOVGP|JNVSEJZVKOURNUYRJMcZMQZUQZdULPSLHOWSOTXOIMRIBEIKGd|JNVSEJaVKOUQGKZUDGURNUQZJNSJFMWTBFYUAEeaEJaWLPVRMVZLHOURJNcYNUYRFJdZGLRNKRTKLOKT|JNVSFJaVKOUQGKZUDGURNUQZKNZUGKUQCGYUIMURNUQZKNVRMVXTOXSOLSWTXObWSbZC|JNVSFJaVKOURNUYRJMZUGKWTCFTPFJPNMQSLJZcVQSdaHOaWIMRISVWSVZSLZdJNVSFJaVKOURNUYRJMZUEJWTGKTPAEPNDGSLJQdaMVaRHObW|JNVSFJaVKOURNUYRBFWTFKSNJSTPCFcYEJYUJMUQFJeaJNQJNUZQSZdUKNJSOeUReMQJIMJQLOQMAEMI|JMWSEJURKOYUMQcYJMbWFKRNKRUNBFXTOXWTXONKGWaB|JN" +
        "VSFJaVKOUQGKZUDGURNUQZKNZUGKcZBFeaLPSLPGWSNWaTIMTOKTXOEIVSMQZVQZdUJNSJFMbWMRVM|JNVSEJUQAEZVIMYUEIURNUQZKNXTLPbXGKTOKTXOMQcYIMYUBEVRMcdZcVaIQZOKZcSNJbfWPTWPcS|JNVSEJUQAEZVIMYUEIURNUQZKNXTLPbXGKTOKTXOMQcYIMfbHLOHPTWPNf|JNVSEJUQAEZVIMYUEIURNUQZKNXTLPbXGKTOKTXOMQcYIMebMRVMHLOHQUYKFXMFCJ|JNVSEJUQAEZVIMYUEIURNUQZKNXTLPbXGKTOKTXOMQcYIMZUQZVcMRebHLOHRUYKFX|JNVSEJUQAEZVIMYUEIURNUQZKNXTLPSOMRVMIRaVRaeVGKVSNRdaKNcYRUYKHLOHFc|JNVSEJURNUYRKORNOVaRJSWNBEXTEJNEIBTPAEbWEJfbLOZVOTdaTXVSJNRKFVaRCFWSFJcZGLPGDKbW|JNVSEJaVKOUQFKZUJMQJNEWTLPSLPWbSHOSLGPfbEJUQJNYUAEbWCGVREJcYGLeaBEdZLOZVDGXTOXRM|JNVSEJaVKOUQFKZUJMQJNEWTLPSLPWbSHOSLGPfbEJUQJNYUCGURNUQZAEbWGLVREJZUJMdaMVaRBFUQ|JNVSEJaVKOUQGKZUDGURNUQZJNSJFMWTBFVSOVZSLOSLGWbSKOSLHOYUAEdZMQUREJeaCGZVFKXTOXRM|JNVSEJaVKOUQGKZUBEURNUQZKNYUFKUQDGZUIMcYEIURNUYRJNSJMFeaFJWSLPSLHOaWJNWSNUQZGLZU|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKURNUYRBEcZJNSJEUZQAEeaEJVRLPWTPWbLHOaVJNVSOMQSGLfb|JNVSEJUQKOYUOVaKFOWTGKZVBFTPDGeaJNdZOSVOLSaVGLPGCLVOKTXOLSbWSbfWAEZVEJWTHLcYFKTP|JNVSEJaVLPVRGLZVLOSLPGUQNUQZIMYUMQWSAEXTJMTPMRUNKaeVEJbWFKfbJMbXMRVMQJWTKNZVNWTa|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKURNUYRBEcZJNSJEUZQKNWSNWbSCFVROMQCLPCLHOfbIMbWMRea|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQMRVMOVZSEIXTIRbXDGeaLPdZRUSOUdOLHOTD|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQMRVMOVZSEIXTIRbXDGeaLPdZJMSJRUTOUdOLHOWTdETR|JNVREJZVJMUQNUQZLOWTAEbWMRVMIRTPFJWTEIZUJNdZBEZVCFVMIRcZEJfbJMUQRUQJUfTOfEOFHLPG|JNUQNRVMIRWTEJTPAEbWJNZULOWTOSdZEIfbIMQJFMUQBEQARVaRNdAWKOTKdB|JNXTLPUQGLbXLOZUHLVRIMQSOMaVLOdZDHVRMVZLPG|JNUQNRVMIRWTEJTPAEbWEIfbJMQJFMXTLObXBEZUHLUNKRTKGNPGCLXTDGTPMQWTEJTOLSaVRaeO|JMWSKOaWMQWTFKTPEJURJMbWCFfbOTXOKadWFKSNLOPLGPNGDKZUQSWGMVGCAE|JMVSMQURKOaVGKWTLPSLPGTOKTXOEJbWJMWTGLYULSVOMVZSQZcVAEfbEJdZIMbXMQeaJNSJFMaWDGWS|JNWTEJaWLPeaAEVRJMUQMeQMIRdaeVZARVYUVaWdPWbSFJANKY|JNWTEJbWJMfbMRVMIRTPAEWTEJbWLOUQGLPGCLTPBEPGRUYRNUGNJb|JNURNUYREJWTLOTPJMbWOTXOKTWSTXcYAEebXefbeXSOXUZA|JNURNUYREJWTLOTPJMbWOTXOKTWSTXfbMQbWAEcYEJZUQZVcJMaVFJYUMQRNQZNECFdUFJENGLPGDTUR|JNWTEJVRJMUQNUQJFMZJBEYUENUQLOTPCFdZAEcYEJaVHLeaDHZUOSVOLSbWSbfWHLURNUYRLOXTOXWS|JNXTLPUQNRVMIRZURVaRKNRKFXURHLcZGKZVEJRMCFMIKOYUDGWTPWbSGKURLPSLPGVSGLSNJSebXedZ|JNWTNRUNKRVMIRTPEJZUJNdZAEXTEIbXIMfbMQaWFJeaRVaKGNPGDKURNdTPdTXMQJ|JNVSEJaVKOUQFKZUJMQJNEWTIMTPEIURBFYUMQcYQZdUAEeaEJRNKRUEIBSNGKNGDKPNOTXOFKNGCZaV|JNVSEJaVKOUQFKZUJMQJNEWTIMTPEIURBFYUMQcYQZdUAEUQEJYUOTXOKTPWFKRMITSOLSbWTaeM|JNVSEJaVKOUQFKZUJMQJNEWTIMTPEIURBFYUMQcYQZdUAEUQEJYUOTXOKTPWGKbXLPXTHLfbDHbXLOSL|JNVREJZVJMUQNUQZAEYUMRUNKRVMIRZVEIVMIRWSLOSLHOdZBEaVRaeVGKbWFJWSDGSLGPfbEIVSKNbW|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOYUGKRMEJeaDGbWSbXeKNMINSfbGLaVSZcVJNbWAEWTOXebXeVS|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOYUGKRMEJeaDGbWSbXeKNMINSfbGLaVSZcVJNbWAEWTOXebXeVR|JNUQNRVMIRWTLOTPEJbWJNWTRUYRNUQMUYaVFJMFCJVRAEeaBFRNJSZUYRaVRadNKRTI|JNUQNRVMIRWTLOTPEJbWJNWTRUYRNUQMUYaVFJMFCJVRAEeaEIfbHLbWBEaVJMVSOVRaKNaVMRVMIRWS|JNUQNRVMIRWTLOTPEJbWJNWTRUYRNUQMUYaVFJMFCJVRAEeaEIfbJNaVNUZQBEbWEJWSHLdaIMaWDHSN|JMVSMQURKOaVEJWTJMTKGWbSLPfbHLbWAEebFKSNCFNGLCWSCGdaEJaWDHSOFKOFJCWSCFbWFKXTBFYU|JNVREJZVJMUQNUQZAEVSLOSLHOWSOVZSGLbWEJfbKNYULPUQCGdZGLZULOSLPGcYMRWTGLaVRaeVFKbW|JNWTEJTPJMXTNRUNKRZUFKUNKRbWAEfbMQVMQJYUJNaVEJUQGKPGCLTPLObXBFWTDGdZNRVMIRZVRaeV|JMWTEJTPMQXTLObXJNURNUYRAEfbEJRMIRVMOSMIKNaVNRVORVZSBEIKGf|JMWTEJTPMQXTLObXJNURNUYRAEfbEJRMIRVMOSbWSbTOKTPfJNMIHLXTFKTPLOfbNSbXKNebGLPGCLbW|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNZUDGMIAEQMCFUQEJdZGLZVLOWSNWbLPGfbHLbWLPYU|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNdaKOZVCFVSOVaKFOWTPWbLHOMJOSeaSWaTXOfbOSYU|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNWSNWbSAEfbCFbWEJYUPTWPHLPEBYZUYRSOFJOKRVQM|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNWSNWbSAEfbCFbWEJZVKNVRNUYRDGMIGKRMHLdaKNaV|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNWSNWbSAEfbCFbWEJZVKNVRNUYRDGdaGKaVHLMILOSL|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNYUAEMJEIJSIMQJCFJCDGCLHc|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNYUDGWSNWbSGLZVAEVREIMJKNRKLOSLPEebXeUReMQAJNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNYUDGWSNWbSGLZVAEURCFMILOSLPGVSEJfbGLSNJSea|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSEJfbAEbWCFWTLPTKFOSLPGRMGLMFBKdaEJaW|JNXTLPUQNRVMIRZURVaRKNRKFXUR" +
        "GKcZHLZVKOWTPWbSEJfbAEbWCFWTDHTKFORMLPSLHOMFBKdaKNVR|JNXTLPUQNRVMIRZURVaRKNRKFXWSHLbWGKfbEJcZLOSLPGZVAEdaEIVSCFSNJSWNKRUNBEYUFJaWJSWN|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVEIWSBEbWKORNOTdaLOSLPGWPGLPGDRVMIRaVRaeVCFYU|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSOTYULPQMDHMIHLUQEJRMCFdaLOSLPGfbJNbW|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVEIWSCFRNKaeVXeVReMQC|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSEJfbAEbWEIdaBERMIRVFCJaVLPSLPGYUGKUR|JNXTLPUQNRVMIRZURVaRKNRKFXWSEJbWGKfbAEURKOSLHOcZCFdaDGZVPTWPGLPGFKGNJZaVZSeaXMQA|JNXTLPUQNRVMIRZURVaRKNRKFXUREJRMAEMFCJcZHLZVEIdZGKZUKOWTPWbSBEURDHfbOTbWTaRMaRMF|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEcYCFURNUYRGKWTKNRKJMIRLPSLPUVRUNaVHLbWEJdZJMZUMRVM|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEcYCFURNUYRGKdZJMSNLPNGDKWSEJSLHORNKRbWJNZURYITYcVR|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKcZJNXTDGbXNSVOLbfWHLWSLPSOPWXT|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKcZJNXTDGbXNSVOLbfWEJZVGLTPJNPG|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKcZJNXTDGbXNSVOLbfWEJZVHLVSLPSO|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKcZJNXTDGbXNSVOLbfWEJZVKNVRNUQZ|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZNRVFOeURBKIBeIBTIBWSLOSLGWbSBESODGZVCFcZEI|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZNRVFOecYBKIBeIBTIBUQLOTFBUYR|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZNRVFOecYCJUReMIRLORNJSWNGLbWLPZUDGfbGLUROTXOLJ|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZNRVFOecYCJUReMIRLOZVHLWTGKYUEIUQBEbWLP|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZNRVFOecYCJUReMIRLOZVHLWSGKbWDHYUEIUQLPSLHOWSKNRT|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZNRVFOecYCJUReMIRGKWSKOZVBFbWFKYUEIUQLPSLHOWSDHSL|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZNRVFOeWSCJUReMIRGKbWLOSLHOZVJNcYNUYREJWSDHSLHOfb|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZNRVFOeWSCJUReMIRGKbWLOSLHOZVJNRMBFMIEJWTJMIRNUcY|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKcZJNXTDGbXLOZUEJVRGLTPOTPGTaGC|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKcZJNWSNWbSEJfbDGbWLPZUGLURKNRK|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKcZJNWSNWbSEJfbDGZUKObWGKURLPSL|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKcZJNWSNWbSEJfbKNbWLOSLHOZUDGVS|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKcZJNWSNWbSEJfbDGXTJMQCLPCLHeVR|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKWSDGcZKObWGKZULPSLHOUROTXOKaVe|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKWSDGcZKObWGKZULPSLHOWSOTXOKTUR|JNVSEJaVKOeaFKURNUYRIMRIKNZUAEdZCFUQNRVMOeZVeRMVGKWSDGcZKObWGKZULPSLHOWSKNSLPGXT|JNWTNRUNKRVMIRTOLSZURVaRHLRMGKeaLOUQEJcZDGMIGLbWSbXeLPZVJNVRNUQZFJYUAE|JNWTNRUNKRVMIRTOLSZURVaRHLRMGKeaKOUQEJYUDGURLPcZGKaWJNZUFJMFCJRMBEMFKBURNUQZ|JNWTNRVMIRUNKRTOLSZURVaRHLUQLOYUGKRMEJMIDGbWSbfWAEWTJNURNUQZEJZVJN|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOMIEJeaJMIRSVaWVMdZGKURMVZLDHLGCLWTKNTPFKPGKDYUHLXT|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGfbAEMIJNcZEJaVGLbWLPdaOSVOKTZVCGYU|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKYUDGbWSbXeAEMIJNURNUQZOSfbEJcYKOaWJNeaGLaV|JNWTNRUNKRVMIRTOLSZURVaRHLRMGKeaDGMILObWSbXeEJfbOScZKOUQGLZUAEdZLPZVSZUdFKbWCFYU|JNWTNRVMIRUNKRTOLSZURVaRHLRMGKeaDGMILObWSbXeEJfbOScZKOUQGLZUAEdZLPZVSZUdJNbWEJQM|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGfbAEMIJNYUNRUNKRQMRUcZUYZUYRMVFK|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGfbAEMIJNcZNSYUKNQMEJURNUZQFKMFCJaW|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGfbAEMIJNcZNSYUKNQMEJURNUZQFKMFCJdZ|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGfbAEMIJNcZNSaVGLdaLPZUSZUdEJbWKNQM|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGfbAEMIJNcZNSaVGLdaLPZUSZUdEJbWJNQM|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGfbAEMIJNcZNSaVGLdaLPZUSZUdEJbWOTYU|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGYUAEMIJNURNUQZEJfbGLbWLPaVKNZUFKda|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGYUAEMIJNURNUQZKNZUNRUNFKdZKRZVCFVM|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGcZGLZVKNMINSdZLPfbPTZUSZUdTXbWJNaV|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGYUGLfbKNMINSdZLPZVSZUdJNcZNSaWAEWNJNWTNRVMIRUNKRTOLSZURVaRHLUQGKYUKORMDGeaEJURLPcZGLaVFKMFCJRNKadEAJbWBFZVFKfbKNVR|JNWTNRUNKRVMIRTOLSZURVaRHLUQGKYUKORMDGeaEJURLPcZFKMFCJRNKRZVSZdEAJaWGLWSOVXTPWbZ|JNWTNRUNKRVMIRTOLSZURVaRHLUQGKYUKORMDGeaEJURLPcZFKMFCJRMBEMFKBQMEJMFBKZ" +
        "UGLaWKNdZ|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOeaGKUQDGYUEJbWSbXeAEMIGLURLPRMKNfbNScZPTZUCGdZGLZV|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKcZDGbWSbXeAEMIJNfbEJaVGLbWLPdaCGYUOSVOKTZV|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKcZDGbWSbXeAEMIJNfbEJZVNSdZKNaWGKYUCGeaGLQM|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaGKUQEJYUDGbWSbXeJNfbNSMIAEUROTcYTXaWKOWNGLeaXMQA|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaGKUQEJYUDGbWSbXeJNfbNSMIAEUROTcYTXaWKOWNGLdaLPYU|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKcZDGbWSbXeAEfbKNMINSYUJNbXEJaVSWeaGKaTNSQM|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOYUGKRMEJeaDGbWSbXeAEfbKNMINScZJNbXEJaVOTXOSLVRGKZV|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKcZDGbWSbXeAEfbKNMINSYUGLbXFKebLPbWSbXeKNeb|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOeaGKMIDGcZEJbWSbXeGLfbLPbWJNZVAEUQOSVOKTdZEJZVCGYU|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaGKMIDGcZEJbWSbXeGLfbLPbWJNZVAEUQOSVOKTdZNSWNTWaT|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQDHcZAEMIHLbWSbXeJNZVNSVRLPebOTYUFKaWTadNPTQM|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQDHcZAEMIHLbWSbXeJNZVNSdZLPfbFKZUSZUdGLbWOTdZ|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRUQRVSOGKZSKadWNRfbBESOJMQJENcZFKOFCJZUAEUQEIWTXObW|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRdaAEUQXbeXRUYKFe|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRdaAEZVEIVMJZcVNRVMIRSOFJWSGLfbJNSJLS|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRdaAEZVEIVMJZcVNRVMIRSOFJWSRUYRJMRIBEIBCFBKGdOKdQKG|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRdaAEZVEIVMJZSJFMcVMRVMIRWSCFaVRaeVGKVRFJYUBEUQEIQM|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRdaAEZVEIVMJZSJFMcVMRVMIRWSCFfbBEbWEJSOJNWTGLOKNGHO|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRdaAEfbGKSOKTWPCGUQNSZVSZcMEIbWIRWSFKSOKTPWJNQMRIaV|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRdaAEfbGKSOKTWPCGZVEIVMJZcVNRVMIRbWFJWSJMaWBEPLGPSO|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRdaAEfbGKSOKTWPCGbWEIUQFKZUBFcZKOWTFKZVIMaWRaeVOSVF|LOWSHLSNJSXTOXVHIMbWEJWSKNaWMRUQRVQMVOWTJQTRAEfbEJRMJNMIGKeaXVZJFMIRCGYUQZcVKNRK|LOWSHLSNJSXTOXVHIMURMVaREJYUAEZVKObWGLWSCGfbOTHOTKbWGLUQEIdaLPRMIRVMDHcZBEZVEIVR|LOWSHLSNJSXTOXVHIMZVMQVSQZcVEJSOKTbWAEWPEIVRFKfbBFYUJNaVFJbWJMeaNSVFMeFBXbWfeXfb|LOWSHLSNJSXTOXVHIMbWMRUNKRWSFJZVJMcZBFZUFKUNKRdZCFfbEIbWMQVMIRZVQUVMUZSNZdNJdQJL|LOWSHLSNJSXTOXVHIMZVEIURAEbWMQfbKOcZFKWSGLZUQZdULPSLPGUQCFbWEJRMIRVMKNMINRWSBEIK|LOWSHLSNJSXTOXVHIMZVEIURAEbWMQfbKOcZFKWSGLZUQZdULPSLPGRNKRUNBFVRFJaWJSWNCFYUEJNE|LOWSHLSNJSXTOXVHIMZVMQVSQZcVEJSOKTbWAEWPFKfbKObWOSWNJZdUEJURBEYUEIUQCFaVFKeaJNRM|LOWSHLSNJSXTOXVHIMZVEIURAEbWFJfbCFYUMQVSQZcVKNRKGNSONSWNJZdUFKOFBKbWEJaVIMUQKNVS|LOWSHLSNJSXTOXVHIMZVEIURAEcZKOZUMQdZGLbWLPRNCGWSOTURFJZUQZVcJMaVMQcZIMRIGLHOTaeV|LOWSHLSNJSXTOXVHIMZVEIURAEcZKObWOSWNGLHOFKNGCSVOMc|LOWSHLSNJSXTOXVHIMZVEIURAEbWMQWSEJRMIRVMKNaWQUYKFVMFBKdaCFaRXbeXGLHOKa|LOWSHLSNJSXTOXVHIMZVEIURAEbWMQfbKOcZFKWSBFSLGPbWCGWSPTZUQZdU|LOWSHLSNJSXTOXVHIMZVEIURAEbWMQfbKOcZFKWSGLSNCGbWLPWTPWaTIMRIKadWEJTKGNZVBFVSNRSO|LOWSHLSNJSXTOXVHIMZVEIURAEbWKNRKGNVRNUYRMVaREJdaCGaVFKcZBFWSJMSNMQVSIMRIKRZVRaeV|LOWSHLSNJSXTOXVHIMZVEIURAEbWKNRKGNVRNUYRMVaREJdaFKcZKOfbCGZVBFWTFKTPIMRIKNbWOTVS|LOWSHLSNJSXTOXVHIMZVEIURAEbWKNRKGNVRNUYRMVaREJdaCGaVJNRKGNVSNRSOFKOFBKWSRUfbIMbW|LOWSHLSNJSXTOXVHIMZVEIURAEbWEJYUJNfbMQVSQZdUFJSOKTWPJMRKGNPLMRcYIMUQNSQJSVJFCJLG|LOWSGLbWKNURNUYRJMWTEJTKFOaWMQRNAEWTCFTKFOfbIMdaBFNKMRKIRUbWUdcZdUVROMIYLOaVJNVR|LOWSGLbWKNURNUYRJMWTEJTKFOaWMQRNAEWTCFTKFOfbIMdaBFbWLPSLJbVSHVaKbfKF|LOWSGLbWKNURNUYRJMWTEJTKFOaWMQRNAEWTCFTKFOfbIMdaBFbWEINEIBWTMRTKFOVMQJaVDGeaGKaW|LOWSGLbWKNURNUYRJMWTEJTKFORNAEfbBFaWLPSLPGeaJSVO|LOWSGLbWKNURNUYRJMWTEJTKFOaWMQRNAEWTCFTKFOfbIMdaDGbWMRVFBRWTOVZSLPTOPTSNTKNUQZcV|LOWSGLbWKNURNUYRJMRNLPSLPGXTHLVSMQTPIMWTFKTOKTPWEJNEAJfbGKSOKTWGDKaWJNbXCGWTMRTO|LOUQJNWSNWbLHOfbKNZUNSVRSVRNVZcVOTXOFKOFCZaVZSQMIRUW|LOUQJNWSNWbLHOfbKNZUNSVRSVRMIRUNOTaRFJXOJL|LOUQJNWSNWbLHOfbKNZUNScZEJURJMQJFMYUGKUQOTXFCJVOMc|LOUQJNWSNWbLHOfbKNZUNScZEJaWJMQJFMWNMRVMIK|LOUQJNWSNWbLHOfbKNZUNScZEJURJMQJFMaWBFWNOTXOFKOFCSVOMc|LOUQJNWSNWbLHOfbKNVRNUYREJbWBEZVJMQJEUVRUNWSOVaBLOUQJNWSNWbLHOfbKNVRNUYREJbWBEZVGKWSDGSLGPcYJMQJEUYRAEdZEJZUKOUQFKRMIRVFCJaVKNVR|LOUQJNWSNWbLHOfbKNVRNUYREJbWBEZVGKWSDHSLHOaWJMQJEUWSOTXOKTcYAEYREJdZJMZUMQeaQZVc|LOUQJNWSNWbLHOfbKNVRNUYREJZVBEbWGKWSDHSLHOaWJMQJEUWSOTXOKTcYAEYREJRNFKNGCLVR|LOUQJNWSNWbLHOfbKNVRNUYREJbWBEZUOSWNJSXTFJcYJM" +
        "QJENRKGNdZCGaVDHVOGLeaLSaVIMVOMQOK|JMWSKObWFKUQBFQJFMYUMRUNKRVMIRfbOVZSLOSLHOWTGKbWEJdZAEaVRaeVCGWSGLZULPSLPWVSWNLG|JMWSKObWFKUQBFQJFMYUMRUNKRVMIRfbOVZSLOSLHOWTGKbWEJdZAEaVRaeVDGTPKNVSOVZSGLPGCLXT|JMWSKObWFKUQBFQJFMfbMQYUEJURJMSNAEWSLPSLHOaWDHdaCFWSGLNGLCSLHORNEJNEIBVSOVaI|JMWSKObWFKUQBFQJFMfbMQYUEJURJMSNLPWSPTSLHOaWTadWAEWSDHSLHObWOSVFCbXTMVeXQUZSIMTO|JMWSKObWFKUQMRVMIRSNRUYROSNJEUWNKRcYLOXTOXZVAEQZCFVMGKMI|JMWSKObWFKUQMRVMIRSNRUYROSNJEUWNKRcYLOZVUZdNOTXOGKOFCZ|JMWSKObWFKUQEJZUJNSJMFURLPWTPWaTFJTPBEfbJMQJEUYRCFdZAEZUEJUQJNcYNUYRFJeaJNRMIRVM|JMWSKObWFKUQEJZUJNSJMFURLPWTPWaTFJTPAEfbCFdZJNPLNdLAdPeaPdcZdUYRBEAGDKbWHLWSLPSL|JMWSKObWFKUREJWTLPSLPWaTGWebBFbSKOSLHOfbFKbWMQdaJNYU|JMWSKObWFKUREJYUMQcYJMRNKRUNBFXTOXWTXONKGWaB|JMWSKObWEJURFKYUMQcYJMRNKRUNBEWTEJTKLPNEGWaTAJebPWbSDGYUJNSJMFURGKdaKOaWFKfbCGWT|JMWSKObWFKUREJYUMQcYJMRNKRUNBEWTLPTKEJNEGWaTAJebPWbSCFYUFKSOKTXOJNVSNWOKHLKFLOFC|JMWSKObWFKUREJYUMQcYJMRNKRUNBEWTLPTKEJNEGWaTAJebPWbSCFfbFKSOKTXOJNbWMRVMQJZUIMWT|JMWSKObWFKUREJYUMQcYJMRNKRUNBEWTLPTKEJNEGWaTAJebPWbSCFfbDGbWGLYUFKURLOSLHOWSJNSJ|JMWSKObWFKUREJYUMQcYJNSJBFRMIRUNFMWSKRZUQZdNAEYUMQfbQZVcOVaRLORMGKNGDKMIEJcZHLZU|JMWSKObWEJUQMRVMOVaRJNRKIReaGNZVAEVMEIcZIRZVBEVMEIdZIRZVDGVM|JMWSKObWEJUQGKZULPSLPGXTAEURKNRKFXWSMRVFBKfbEJbWHLYULPaVKOSLCFLCFKCMITURTWcZKOQM|JMWSKObWEJUQGKZULPSLPGXTAEURKNRKFXWSMRVFBKfbEJbWHLYULPdZKNSOIMOKMRWSNdUEGNEAdUQZ|JMWSKObWEJUQGKZULPSLPGXTAEURKNRKFXWSMRVFBKfbEJbWHLYULPdZKNSOCFZVFKOMIYQMNRMJRUJE|JMWSKObWEJUQGKZULPSLPGXTAEURKNRKFXWSMRVFBKfbEJbWHLYULPdZGLZVLOSLPGcYKNURNUYRJNRK|JMWSKObWEJUQGKZULPSLPGXTAEURKNRKFXWSMRVFBKfbEJbWHLYULPdZGLZVCGcZKNQMIYZUYRVFDHSJ|JNWTLPUQPWbJENXTHLTPLOfbAEbXEJYUGLPGCLaWDHVRLPcYOTXOKadWHLRKFOZVOTebTRUEIMQJBIJF|JNWTLPUQPWbJENXTHLTPLOfbAEbXEJYUGLPGCLaWDHVRLPcYOTXOKadWFKWSNWRMIRUGPTGDTXQMJQDN|JNWTLPUQPWbJENXTHLTPLOfbAEbXEJYUGLPGCLcYDHVROSaVSWeaLPaTPWVSIMRIWbXeNWURHLRMLPZU|JNWTLPUQPWbJENXTHLTPLOfbAEbXEJYUGLPGCLaWDHVRLPcYOSeaSbXeHLaWLOebOSbXSbXePTdaTXaW|JNWTLPUQPWbJENXTHLTPLOfbAEbXEJYUGLPGCLaWDHVROSeaSbXeNScYKNRKFOebIMaVLPdaJNQJNEUR|JNWTLPUQPWbJENXTHLTPLOfbAEYUEJbXGLPGCLVRDHaWOSeaSbXeNScYKNRKFOebIMaVLPdaJNQJNEUR|JNWTLPUQPWbJENXTAEfbHLTPEJYULObXGLPGCLcYDHebLPVRHLZVNSRNSZNEZcEAOSAWLOaVcSWD|JNWTLPUQPWbJENXTAEfbHLTPEJYULObXGLPGCLcYDHebLPVROTXOKTRKFObXBFURFKZUJNaVTWVSOMQb|JNWTLPUQPWbJFMQJENYUAEVRHLXTEJTPNSRNKYZUYRaVSZdE|JNWTLPUQPWbJFMQJENYUAEVRHLXTEJTPBFaWLOfbOTbXTadWDHebJMWTMVZJFMTOKTPWGKWSKOSLHObW|JNWTLPUQPWbJFMQJENYUAEVRHLXTEJTPBFaWLOfbOTbXTadWDHebGLPGCLWTLOZVNSUQSZcVJNbWNUQZ|JNWTLPUQPWbJENXTHLTPAEfbEJYULObXGLPGCLVRNSRNKYZUYRaVRadEFJENBEeaEJNEIBaWLPQMBFcZ|JNWTLPUQPWbJFMQJENYUAEVRHLXTEJTPBFaWLOfbOTbXTadWDHebGLPGCLWTLOZVOSVOJMbWMVUQNRWS|JNWTLPUQPWbJENXTHLTPAEfbEJYULObXGLPGCLaWLPdaDGVSOVaRGLZVLOeaOTXOKTRKFOWSTXSLPGaW|JNWTLPUQPWbJENXTHLTPAEfbEJYULObXGLPGCLaWLPdaDGVSOVaRGLZVLOXTOXcYKORTXOVROTWSBEeb|JNWTLPUQPWbJENXTHLTPAEfbEJYULObXGLPGCLaWLPdaDGVSOVaRGLZVLOXTOXcYBEeaNSWGFKGNJZUd|JNWTLPUQPWbJENXTHLTPAEfbEJYULObXGLPGCLaWLPVROTXOKadWDHRKFO|JNWTLPUQPWbJENXTHLTPAEfbLObXEJZUNSVRJNdZBEaVEJXTOXVOKTRBTW|JNWTLPUQPWbJENXTHLTPAEfbLObXEJZUNSVRJNdZDHebFJbWSbXeGLPGCLZVBFRMIRVM|JNWTLPUQPWbJENXTHLTPAEfbLObXEJYUNSVRJMQJFVaRBFebFJUQJNZUCFdaFJcZDHaWHLQMJQWTSVZJ|JNWTLPUQPWbJENXTHLTPAEfbLObXEJYUNSVRJNaVFJXTOXVMCFRKIYdaFOebXVZC|JNWTLPUQPWbJENXTHLTPFJfbKOZUGKPGCLbWLPVSOVaRAEcZDGZVGLdaBFebLObX|JNVREJaVBEWTJMTPLOUQNUYRHLQJEUZQFJbWJNWTAEdZNRVMIRZVRaeVCFfbFJbWJNWSNWTaDHVROSQM|JNVREJXTLPZVJMUQNUQZMRVMIRZUAEUNKRTOGKbXKTXOCGfbFJbXJMcZEIWTPWaTBFTPFJZURVUQMReb|JMWTMRUNKRVMIRTOLSZURVaRGLRMFKMIKOdaEJaWAEWNJSeaCFUQEJYUFKaWSVWSJMIaOebWKNXTLPcZ|JNWTNRUNKRVMIRTOLSZURVaRFKRMKOeaGLMICFUQFJYULPbWSbXeOTfbTXbWJNaVDGebXeVReMIDEJUR|JNXTLPbXNRUNKRVMIRebEJZUJNcZHLZVFKVMNSWNKIURPWbSAEYUBFUQLPaVEJfbGLbWFKRMITXMPTMJJNVREJaVJMXTMQTPLOWSNWbLHOeaAEfbFJRMIRVFCJURJNZVNUYREJbWOTWSTXRNKRVFBKcZDHaWHLZV|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOeaDHUQHLMIEJbWSbXeOSQMJQYUQZcH|JNXTEJTOLSVOKTWPAEaVHLbXLOfbOSVONRUNJLbWLOZVEJWSGLPGCLYUFKURLPSLPGeaJNcZNUZQKNdZ|JNXTLPUQNRVMIRZURVaRKNRKFXUREJYUHLRNJSWNLOURBEcYEJNEAJYUGKbWDGRMKNMFCJdaGKaVOTVR|JNVRFJWTJMTPMVZJENUQAEbWEJYUKOWTOSUR" +
        "NUQZIMfbJNTONROVMQVMQJbWJNWTBEaWNRdaLOTKGNPL|JMWTLObWEJWSAESLGWaTHLTPKOPGCLfbMQbWFKWTLPeaPWaTJNURNUYREJRNKadWIMTKMRcYJNKFBKZV|JMWTLObWEJWSAESLGWaTHLURMQfbLObWJNeaNUYREJWSDGSLGWaTKOTKFOdaBFaWFKWSCFSLJNRMIaZU|KNWTGKTPLOVRJMPLMVZJFMLSCFSOKTXOFKOFBKbWKOUQDGQJENWSNWaD|JNXTLPUQGLZUDGbXEJURNUQZJNYUFJUQBFZULOURNUQZJNZUAEVREJaVJMUQNUQZMRVMIRcYFJZUJNWS|JMWTMRUNKRVMIRTOLSZURVaRHLRMSVMIEJXTAEUQJNTPNRbWEJfbFKbXCFebKOWTFKdZDHZSOVbWKNYU|JMWTMRUNKRVMIRTOLSZURVaRHLRMSVMIEJUQGKXTKNYUNSTPDGdZSWbSVOZVJNURNUQZFKfbAEbWEJZU|JMWTLObWMQWSEJSLGWaTHLURLOfbAEbWJNeaNUYREJWSDHSLHOaWJNTPNUWSOTPWUYWTIMTPCGXTBESO|JNUQNRVMIRWSEJSOLSaVRadEAJeaHLbWLPZVGLYULOfbKNcYFKURNUQZJNZUCFUQFJVRNUYRJNRMDGMI|JNVREJZVJMUQNUQZKNVSFJXTMQTPIMbXBFXTFKZVLOSLHXdZNRVSAEYURYWTXVaBKNBIJMIKGNfbNRZV|JNUQNRVMIRWTEJTPLObWJNZUOTXOKTcZAEZVEIVMIRdZBEZVEIVMIRaVTaVMadMIFJebGLPGDKURNUYR|JNVREJaVLOWTBEUQNUYRJMQJEUZQIMQJFMdaMQVROSTPAEbWSbfWEJaVHLeaJNcYNUYRKNRKGNPGDKWT|JNWTNRUNKRVMIRTPEJbWAEfbJNWTEIbWIMZUNSWNRKUQMRaVRaeVFJYULOcYBEVRJNdaOSRMEIURNUYR|JNWTEJTPJMUQNRQJFMbWMQVMQJYUJMfbLOWSOVZSKOSLHOdZMQURBFZVAEbWFKcZDHWSHLaWEJWTCFea|JNVREJaVLOWTBETPJMUQNUYRHLQJEUZQDHVRAEdaEJbWOTXOLbfWKOaVOTWSTXcZJMQJFMZUMQRNQZVc|JMWSEJSOLSVOKTXOBEZVMRVMJZcVEJVSGLdZJMYUAEaVDGUREJbXLPOLHOSLGKLHKORNJSHDFJeaCFaW|JMWSKOaWMQWTGKTPDGUREJYUBEbWJNSJENWTAEfbFJbWCFWSNWTaJNcYEJRMIRVMNRUEQAYUKNURNUZQ|JMWTMRUNKRVMIRTOLSZURVaRGKRMHLeaLOUQEJcZJNaWDGdaFJMFCJWTGLTPSVPGVeGDOSbWSbfWeIWT|JMWTEJTOKTXOLSVOMQbWJNURNUYRAEfbEJWTJMaVGLdaLSVOMVaRFKOFBKbXHLeaLOZVKNTKNUVSUYSO|JMWTEJTOKTXOLSVOMQbWGLWSBEURJMfbMVaRCGbWEJWTJMRNLPeaPWaTAEdaEJNEIBSNGKNGDKTPKTPW|JNXTLPVSGLSJFMbXLOUQBFQJFMaVEJVSOVZSKNTODGYUGLUQMRebRVSZLSdaCGcYGLYUIMZVSZUdMRdZ|JNVREJXTBETOLSaVJMVOKaRBEJeVMQURJMbWAEWSEJfb|JNVREJXTLPZVGLbXJMUQNUQZMQVRAEebLORNKRTKFOWTPWbLHOfbDGbWGLWTCFTKFOZUQZdNBFaWFJWT|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOMIGKUQDGdZGLZULPeaSVaROTXOKTQMTXbWEJUQXbWSbeSOeXfb|KNWTLPVRPWRKGNbSNWaTJNTOIMZVEIURNUYRDGXTGLdZLSVOMVZSIMcZMRZVRaeVFJTPJMOLHOSLMQVR|LPWSGLSOKTXOLSVOJMbWMQUREJfbJMYUMVZSQZcVFKOFBKSOKTbXDGXOCFWSGKebKTbXTWSbHLbWFKVR|JNXTLPUQGLZULObXEJURNUQZJMVSOVZSCGYUMQURAEfbEJTOKTXOHLOHPTWPIMRIBEIKGfPLJNebfSaV|JNVRFJZVJMUQNUQZMQWSKOaWGKWTLPSLPGTOKTXOIMYUEIbWMRUNGKOFBT|KNWTJMTPMRVMIRXTFKbXLOZVEIVMIRcZAEZVEIVMIRdZBFZVOSVMSWaVNSVOKNTaFKOFCZaVZSeaNRaW|JMWTKNTPMQXTEJaWAEWSNWTaJNbWEJURNUYRJMfbFKbXLOWSBFSLHOaWOTXOKadWGLPGCLebFKWSDHbW|JNVREJWTBEbWJMTPMVZJFMWTMQTOQZOFCJdULOaVJMfbMRUNIMPLGPYUDGbWHLeaGKNGLCUREIWSAESL|JNXTLPbXNRVMIRUNKRZVEIVMIRebAETOEIcZFJZVRUYRPTWPGLPGCZdUJMRNMRUQRKaVBFbWHLfbKNVR|JNVREJZVJMUQNUQZKNWSNWbSLPYUMQURAEaWFKeaHLfbKOSNCFcYFKNJEUYRIMRIKN|JNWTNRUNKRVMIRTOLSZURVaRGKRMEJUQHLeaAEcZKOMIJNZULPURNUYRDGaWFJWNJSXTOedZeMQASVZS|JNXTLPbXNRUNKRVMIRTOEJebJMZVAEcZEIWTPWbSGLZUDGUNFKOFBRXTMQVMQJTOCFfbIMYUFKOFJCaV|JMWTFJUQLPZUPWaTKNURNUYRHLbWGKeaCGTPLOWSGLPNDHSLJZcVHOQJEUaWUYdZIMfbAE|JNURNUYREJWSKObWJMWTMQTKGUcYLOSLHOYRFKfbAEaWBFeaEJRMIRVMKNWTFKMFCJZUQZdUJMUQMRbW|JMWTMRUNKRVMIRTOLSZURVaRHLRMLOMIGLUQEJdaDHYUAEaWLPWNJSeaCGUREJaWSVRaGKcZJNZUFJaV|JNVSEJaVKOUQFKZUJMQJNEWTIMTPMQURBFcZEIeaAEaWOTXOKaVeLOSLHObWFJeaJMaVEJfbGKZUQSWE|LOWSGLbWLPSLPGXTHLTPJNVREJZVJMUQNUQZAEWSEJfbKNbWFKZUMQURNUYRKNRKGNPGCLebBFbXFKXT|JMWTEJTOKTXOLSVOMQbWJMfbAEWSEJbXGLSNJSOVLPXTPWaTFKebHLbXLPTOKTXOCFVSFJZVQZdUDGVR|JNWTEJTPJMUQNRQJFMbWMQVMQJYUJNUQLOWTAEZUNSdZEJaVBFfbJNVRFJZVSZUdNUQZOSbWSbTOKTPf|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSOTYUEISNBEfbEJNEAJdaLPbWDGVSGLRNLOSL|JNWTFJTPJMXTMRVMIRbXLOZVEIVMIRcZAEZVEIVMIRdZBFZVOSVMSWURNUYRWdeadWTaKOMIOSaWSbfW|JMWTEJTOLSVOKTXOBEZVMRVMJZcVFJVSJNSJENaWNRWSIMdZRVZUGLSZLSeaDGUQMRbWSbfWAEZUCFUN|JNVREJXTJMUQNUQJFMZJBEaVENVSLPSJHLYUKOTKGEWTPWbSCGURGKcZKOZVEJfbLPSLPGdZJMeaGKbXJNVREJaVLOWTBEUQNUYRJMQJEUZQIMQJFMbWMRVMOSWNKIfbHLbWAEeaEJaVJMcZLOTKGNWTMQTPNRVM|JNVREJXTLOTPBEaVHLWSNWbSJMfbMQdaFJRNKRVFCJbWOVZSQZcVJMYUGKPNMRVMIYNJENSJYcJFAEFC|JMWTMRUNKRVMIRTOLSZURVaRGKRMHLeaLPUQEJcZAEMIDHbWSbXeHLfbLObWKNaVNSWNJSdaEJZUSZUd|KOWTJMTKFOURGKbWMQWSLPSLHOaWEJWSDHSLHOeaCFRMIRVMOTXOKTaWTadWJNMIFKfbKObXAEZUQZcV|JNXTLPUQNRVMIRZURVaRKNRKFXURHLcZGKZVKOWSCFbWEJRMOTdaDGMIGKYUKNQMJZSCZbfWLOCJOSWN|JNWTNRUNKRVM" +
        "IRTOLSZURVaRHLRMGKMIEJUQKOdaLPcZDGaWAEWNJSeaFJbWSbXeGKZVJNVRNUQZEJfb|JNVSEJaVKOURNUZQGKYULPSLPGXTJMQJFMWSMQdZAEbXKOTKGWebHLbSLOSLCGLCEJCMIa|JNVSEJaVKOURNUZQGKYULPSLPGXTJMQJFMWSMQdZAESOKNOKNSVOGNOLHXeaXVZAQZcV|JNWSNWaTLOeaFJbWJNURNUYRKNRKOFWSEJTPIMXTMQfbQUZQJNSJFMQJCFJLHe|JMURMQVSKOaVEJWTLPTKGWbSCGYUJMXTPNRKFOVRMVZCQZcV|JMURMQVSKOaVEJWTLPTKGWbSCGYUGLRNAEfbJMURFJSOJSbWSbVSMVXTPNZALSAf|JMURMQVSKOaVEJWTLPTKGWbSCGYUGLRNAEfbJMURFJSOLSNWBFRNJSWNEJNEIBVSHLeaLOSLPG|KNWTLPbWNRUNJbfWEJVSJMYUMQSNHLaVFKURBEVSEJNEAJRMIRTOKaeFCJSNJSZUQZcHGKdaKNaVNSVO|JNWTEJbWJMfbMRVMIRTPLOWTAEZVEJVMJZcVFJYUNSdZJMUQHLQJKNTRBEVHEf|JMUREJWTJNbWNUZJFMfbMQdZKNTPNRVMQJXTIMTOLSWEAJZVMQbWBFVRFKRMQUMOUZcVGLPGCZaVZbeX|JNVREJWTJMUQNUQJFMZJBEJFKBTPLOYUEJaVJNVROSRKGNeaAEbWSbXeEJfbJMUQMRQMRUcYIRPLHOaV|JNXTLPbXNRUNKRVMIRebEJZUJNcZBETOGLXTLSaVRabXSbXVPWdaWdUQdUYIHLfb|JMVSEJWTLPTOKTXOGKUQKTbXBEXODGebMRZUIMUNFKOFEINEIKQJCFJLHXYUAE|JNXTLPbXNRUNKRVMIRebEJZUJNcZHLZVFKVMNSWNKIaVPWbSAEUQEJYUBFfbDHXTJNSJFMQJCFJCLPCL|JNXTLPUQNRVMIRZUKNTOGKbXKTXOFKOFCJebHLbXEIcZBEZVIMVSDHXTLOTKNGUNEINEIBQJBFJLHe|JNXTLPbXHLVSDHSJENURNUYRAEebFJcYLOZUBFaVJMWSPNUQNUQA|JNXTLPbXHLVSDHSJENURNUYRAEebFJcYJNTONUOFBKYR|JNXTLPbXHLVSDHSJENUQAEZUEJaVBEVSLOSLHOURNUYROSWNJSeaPWaTEJQMJQdZQUZQFJcYJNYUCFfb|JNXTLPbXHLVSDHSJFMURMVaREJebBFYUJMZVMQVSQZdUAEUQEJRMIRSOLSWEPWbSRVSZFJENKRXTRUTP|JNXTLPVREJaVHLbXLOWSPWSbGLUQNUYRLPZUDGcYBEdaOTXOKTbXGKXOKTRMIRVMTXaWEIWSIRUEAJSO|JNXTLPVREJaVHLbXLOWSPWSbGLUQNUYRJNZUNSdaSZUdLPbWOTXOKTfbTXcZAEZVEJWSDGbWGLRNJMQJ|JNXTLPbXNRUNKRVMIRebEJZUJNcZNSUNSJTOGLXTLSWEAJYUPWbSFKURCGZVGLaWKOfbLPSLHObX|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTBEZUJNcZEJaVRaeVNSUQJNdaIMQJNEYUCFURHLaW|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTBEZUJNcZEJaVRaeVNSUQJNdaIMQJNEYUEJUQCFaW|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTBEZUJNcZEJaVRaeVNSUQJNdaIMQJNEYUEIUQCFaW|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTJNZUOSUQBEaWEJdaSVTOKTXOGLPGCSWTHLTODHYU|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbEJTPKNWTOSaVRaeOGLPGCSZVSZcVHLbWFKYULOUQBEdZDGZU|JNVREJZVJMUQNUQZLOWSHLYUAEURMQaWEJWTKNTKNWbSGUSNJSVHUYXTFKfbIMbXCGeaKOTKGNXTMRTO|JNVREJZVJMUQNUQJFMYRAEWSCFbWEJfbKNRKGNXTLPbXNRSOJNVSFJaVRaeVMQcYIMVRNUYIDGdZGLOK|JNVREJZVJMUQNUQZAEXTLObXEJTPOTXOKTWSTXYUMQURJMfbBEaWFKdaHLWTXObXEJaWJNSJMFWSFJea|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbEJZVJMVSOVTOKTXOFKOFCJYURYaIGKea|JNWTEJbWJMfbMRVMIRTPAEWTLOaVRaeVFJUQNSYUEIURBEcYJNbWNUYRSbXeOXebXeVSeMQA|JNVREJZVJMUQNUQZAEXTLObXEJfbMRVMIRTPKNWTOSaVRaeOGLPGCSZVSZcVHLbWFKYUBEURNUdZUdTP|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTBEZUJNcZEJaVRaeVNSUQIMbWSbXeOXebXeZUeRUE|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTBEZUJNcZEJaVRaeVNSUQJNdaNRVMIRbWSbXeOXZV|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTBEZUJNcZCFaVRaeVFJUQNSYUJNbWSbXeOXebXeVR|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTBEZUJNcZCFaVRaeVFJUQNSYUIMUREIRNKadEIBTK|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTBEZUJNcZCFaVRaeVFJUQNSdaJNYUEJVRHLZVSZUd|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTBEZUJNcZCFaVRaeVFJUQNSYUHLVRDHRNKYTDYcPG|JNVREJZVJMUQNUQZAEXTLObXEJfbMRVMJQZVHLTPBEdZEJVRJMaVFJWSJNSJMFbWFJWSJMSNDHYUOSVF|JNVREJZVJMUQNUQZAEXTLObXEJfbMRVMJQZVHLTPBEdZEJVRJMaVFJWSJNSJMFeaDHYUFJbWJNWTCFaW|JNVREJZVJMUQNUQZAEXTLObXEJfbMRVMJQZVHLTPBEdZEJVRJMaVFJWSJNSJMFbWFJebJNYUCFWTDHcY|JNVREJZVJMUQNUQZMRVMIRWSLOSLHOZVAEVMEIcZIRZVRUYRFJbWGLfbLPXTOXVSKOSLPGWSGKaWDGSN|JNVREJZVJMUQNUQZAEXTLObXMRVMIRfbFJTPEIWTJNZUOSbWSbTOKTPfGKaVRaeVHLfbLObWBFURNUYR|JNVREJaVJMUQNUQJFMZJBFVSFMWTLOSLGWbSHLYUAEdZEJebCGXTMQZVQZTOKTbWTRcFGKFHIMSNMQNK|JNVREJaVJMUQNUQJFMZJBFVSFMWTLOSLGWbSHLYUAEdZEJXTCGebMQTPKNbWIMWTNWTaJNaVMRVMQJZV|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKUQBFYUAEURNUQZJMWTMRVMOVZSIRTOKTXOEIdZFJbWIMcYRVSNJNVSEJaVKOUQGKZUDGURNUQZKNZUGKcZBEeaLPSLPGWSNWaTIMTOKTXOMRVMJQ|JNVSEJaVKOUQGKZUDGURNUQZKNZUGKcZBEeaLPSLPGWSNWaTJNURNUYREJTOKTXO|JNVSEJaVKOUQGKZUDGURNUQZKNZUBEXTOXVRGKSOKaRBCGdWLOBTXO|JNVSEJaVKOUQGKZUDGURNUQZKNZUBEXTOXVRGKSOKaRBLOeVXeBXeMXeHLcZMReFCJURJMZVMQdZEJfb|JNVSEJaVKOUQGKZUBEURNUQZKNYUIMUQMRVMOVZSEIXTIRbXDGeaAETOEIXTJMSJLbfWFKJEIBQJCFJL|JNVSEJaVKOUQGKZUDGURNUYRBEcYJMQJEUYRFJdZJMWTLPSLPWbSHOSLGPebKORNAEbWCGWSGLfbMQbW|JNVSEJaVKOUQFKZUJMQJ" +
        "NEWTIMTPEIURBFYUMQeaQZdUAEUQEJcZJMQJFMbWCFWTFJaWMQfbJMSNOSVF|JNVSEJaVKOUQFKZUJMQJNEWTIMTPEIURMQYUQZdUBFUQAEcZEJZUOTXOKTPWGKQMJZVcKOSNDGcZLPZU|JNVSFJaVKOURNUYRJMRNMQWTIMTKEJNEGWbSAJZUQZdUMQURLOSLHOfbCFbWFKeaJNcYNUYRBFWSDHSL|JNVSFJaVKOURNUYRJMRNMQWTIMTKEJNEGWbSAJZUQZdUMQURLOSLHOfbCFbWFKebJNcYNUYRBFWSDHSL|JNVSFJZVKOURNUYRJMRNEJNEAJWTCFTKGWbSLOSLHOfbMRVMIRbWJNcZDGWTFKaVRaeVGLdaLPaWBEZU|LPWSJMSOKTXOMQUREJRMIRVMJNMIGLaVLSVODGeaGLaVLSVOCGdaNRaWRVZSQUYRGKOLHMIRKNRKFObX|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGaWGKdaKTbXDGXOGKebKTbXLOSLHOWSAESLPGXOGKRNKROLFKLH|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGZUQZdUMQcZIMRIBEIKGf|LPWSJMSOKTXOMQUREJbWJMfbGLYULSVOMVZSQZcVAEVREJaVJMdZFKOFBKZUHLUQCGQJPTWPKNRKGfPG|LPWSJMSOKTXOMQUREJbWJMfbGLYULSVOMVZSQZcVAEVREJaVJMdZFKOFBKZUHLbXMQeaQZVcLOSLPGWS|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGYUGKbXKTXODGebGKbXKTXOFKOFBKaWLOSLPGWTHLTPAEdaEJaW|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGbWGKRNKTNJFKJFKOFCBFCJMF|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGRNAEbXPTOKFOebMRNUTWaKGf|LPWSJMSOKTXOMQUREJbWJMfbGLWSCGbWGKebKTbXDGXOGKRNKTNJFKJFKNSJBKWSMFSOLSVX|LPWSJMSOKTXOMQUREJRMIRVMJNMIGLaVLSVODGdaGLaVLSVOCGeaNRbWGKfbKTbXQUZQRVaRTaRNAE|JNXTLPUQEJZUGLVRLObXHLaVDHebAEWSNWTaOTXOLZcVJNVSNWbSKOSLHOfbEJRMIRUEBI|JNWTEJVRJMUQMVZJFMQJBEYUENUQAEdZNRaVRaeVEJZULPcYPWbSHLfbLPbWPTXMITQMCFUQTXMJFMQJ|JNWTEJTPJMXTNRUNKRZUFKUNKRbWMQVMQJfbIMaVMQVSBFYUQZdUFKSOLSWEAJTOKTPW|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOMIEJUQGLdaLPcZDHaWAEWNJSeaFJbWSbXeJNZVNSYUSZUdOTaW|KNVRGKZVJMWTDGTPMQdZLObWGLPGCLfbOSVOLSXTEJaVKOTKNGWEAJRNJSVOGKbXKTXOFKOFBKURHLZU|JMVSLPSOKTXOMQUREJaVGKeaKTRNJSVXAEYUEJURHLaVJNRKFOWTPWbSLPSLPGVRGKZVKNRKCGKFBKVS|JNVREJWTJMUQMVZJFMQJBEYUENUQAETPNRbWKNdZCFQMRUZQIRXTFKaVRaeVLOWSNWTaKNQMEJMFGLPG|JNWTLOVRFJbWJMfbMVZJENURNUYRAEaVEJdaJNcYNUYRBETPCFWSGLPNFJSLJZaVZSeaHOaWDGWNGLbW|JNVREJWTJMUQMVZJFMQJBEYUENUQLObWCFfbAEcYHLTPOSWTLOdZDHYUFJaVIMeaEIaWHLURNdWEIBQJ|JMURKNRKGNWTMRVMIRZUEJbWAEdZLPaVRaWdPWeaHLaTLPZVPWVSWadWCGfbFKcZGLXTDHTPLOSLHObX|JNWTLPUQPWbJENXTHLTPAEfbLObXEJYUDHcYNSebJMQJFMbWSbXeBFUQFJZUCFUROSVOMVaRKTPWHLWS|JNWTLPUQPWbJENXTHLTPAEYULOVSNWaTOXebXeUReMQA|JNWTLPUQPWbJENXTAETPHLYULOVSNWaTOXebXeUReMQA|JNVSEJaVKOeaGKURNUYRLPSLPGWSKOSLHObWJMWSGLfbAEbWCGWTEJTKGWaTLPTOFKOFBKZUDHdaKOaW|JNWTLPUQPWbJENXTAEYUHLTPLOVSNWaTOXebXeUReMQA|JNWTLObWNRUNKRVMIRTKGNfbFKXTHLbXLOZVEIVMIRaVRaeVCGVRNUYRAEdZEJZVJNcYNUYRKNRKOFWS|JMWSMRUNKRVMIRZUFKUNKRXTGKbXLOSLHOaVRaeVEJfbJNbWCGVRNUYRAEdaEJaVJNcYNUYRKNRKOFWS|JNWTEJTPJMUQNRQJFMbWMQVMQJYUJNUQLOfbAEWTEJZUNSdZJNaVCFVRFJeaHLZVSZUdNUQZJMaVBEbW|JMWSKOaWMQWTEJTKGWbSLPfbJMbWFKURAESNCGeaGLNGLCRNEJNEMRVMQAWTPWaTAEYUEJZVHLdaCGTP|JNWTEJTPJMVSNWbSMQfbFJbWIMWTJNSJMFURAEebLObWEJZUQZdUJNUQNUYRFJaVBERMEIMFKBTKGNVR|JNWTNRUNKRVMIRaWFKdaLOaVRaWdEJYUAEeaJMaVMQbWEJfbGLTPKNPGDKWTBEbWEITPHLPGCLWTLPVS|JNUQKOWTNRTKGNVMIRbWFKWTLOfbHLTPDHPGKDbWHLWSOVZJENcZAEZVLOVMEIdZIRZVBEVMEIaVIaeV|JNWTEJTPJMbWNRUNKRZUFKUNKRdZMQVMQJYUJMfbLOWSOVZSAEaVMQcZIMXTEJbWJNSJMFWSGLPGCLSN|JNXTLPUQHLVSDHSJFMQJENZUIMURMVaRNUYRAERNKRTOLSWUEJbWHLURGKeaLOfbBEbXCFcZJNZUFJaV|LOUQJNWSNWbLHOfbKNVRNUYREJbWBEZVGKWSDGSLGPcYJMQJEUYRAEVSKOSLPGaVEJeaFKVSJMaVKOSL|JNVREJZVJMUQNUQZAEXTLObXMRVMIRTPOTXOKTZVEIVMIRdZFJaVRaWdTXYUHLZVLOURGKfbJNcZNUZQ|JMWTMRUNKRVMIRTOLSZURVaRHLUQLOYUGKRMEJeaDGbWSbXeJNURNUQZAEMIKNfbNRbWEJWSOVZSRUSO|LPWTPWbSKNaWGLXTFKTPKOPGCLURNUYRBFfbJMbXLPSLPGXTEJWSMQZUQZdUJMUQFJTOJNRKGWQJIMJQ|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMCFZVHLVRAEMIKOYUOTRNJSWNFKNGDKeaXVURVMQALOAJ|JMWSKOaWMQWTEJTKGWbSLPVRJMSNMVZSQZcVDGVRFKRMIRNUAEfbEJbWGLUQKOdaOVaRLOebCGRNJSWN|JMWTMQTPEJXTJMTOLSVOKTPWHLWSFKbWAEfbEJSOKTWPJNbWBFURNUYRMVaRLOZVGLPGCLdaLPWSOTcZJNWTEJVRJMUQMVZJFMQJBEYUENUQAEdZNRaVRaeVEJZULPcYPWbSHLfbLPbWPTXMITQMCFMIFJSNJSIE|JNXTLPbXNRUNKRVMIRZVEJVMJQTOAEfbEIcZIMaVMRVMQJdaJNYUGKUQKTXODGZVNSWNGKNGCZ|JNVSEJaVKOUQGKZUDGURNUYRBEcYJMQJEUYRAEdZEJZULPSLHOWSJMSLMQLHQSHDSVRaKODBCGBTPd|JNVSEJaVKOUQGKZUDGURNUYRBEcYJMQJEUYRFJWTJNSJCFJCLPCSPUVRUNea|JMUREJWSKObWFKYUMQebJMWTLPSLPWbSHOSLGPfbAEbWBFWTPWaTEJdaCGcYDHRNJSVOGLaVLSVOFJOF|JNXTLPUQNRVMIRZUKNTOGKbXKTXOFKOFCJcZEIZVIMfbBEbXHLVSDHdZEIXTLOTKNGUEIBQJBFJLHc|JMWSEJSOLSVOKTXOMQURJMaVAEbWGKWTKNRKHLOHFXfbEJeaXeaWeRZUQZdE|" +
        "JMWSEJSOKTXOLSVOMQURGLRNJSOVAEVREJbWJMaVLOdaCGYUBEWTOXVSMOebXVZAQZcV|JMWSEJSOLSVOKTXOBEUQGLaVLSVODGbWMRfbGKWSKTbXTWSbRVZSJMQJEf|KOWTOSVOLSTPHLaVLOeaFKUQJNYUGLPGCLURNUQMIRZQSZdP|JNVRFJWTJMTPMVZJENUQAEbWBFcZLOZUFJWTNRUNJSfbCFQMIRaVRadNKRTI|JNVRFJWTJMTPMVZJENUQAEbWBFcZLOZUFJWTNRUNJSfbCFdZFJaVJNeaEJZUSZUdNRaVRadWHLYUIMWS|JMWSKOaWMQWTEJTKGWbSLPfbJMbWFKURAESNCGeaGLNGLCRNEJNEMRVMQAWTPWaT|LPWTPWbSKNaWGLXTFKTPKOPGCLURNUYRBFfbJMbXLPSLPGXTEJWSMQZUQZdUJMUQFJTOJNRKGWQJDGJF|JNWTEJVRJMUQMVZJFMQJBEYUENUQAEdZNRaVRaeVEJZULPcYPWbSHLfbLPbWPTXMIT|JNXTLPbXNRUNKRVMIRZVEJVMJQTOAEfbEIcZIMaVMRVMQJdaJNYUGKUQKTXODGZVNRVMFJMFBTbXGLXO|IMUQKNXTNSWNJSVOLSQJENbXAETPEJYUBEXTEIfbJMUQFJaVGLPGCLVOLSZVSZcVHLbWDGebGKbXLOda|JNVREJZVJMUQNUQZAEXTLObXEJfbMRVMIRTPKNWTOSaVRaeOGLPGCSZVSZcVJMYUHLUQFJbWBFdZFKTP|JMWTMRVMIRUNKRTOLSZURVaRGKRMHLUQEJYUKOeaAEMIFKbWSbXeJNURNUQZEJfbLPbWOTZVDHdZHLZU|JNUQNRVMIRWTEJbWLOfbAEaVRaeVGLQMJQZUQSWPEJTKFOYUJNdZDGcYGLPGCLUQNRbWLPZUOSUNSJYU|JMWTLPTOKTXOMQUREJRMIRVMJNMIGLaVLSVODGdaGLaVLSVOCGeaNRbWGKfbKTbXQUZQRVaRTacZHLRM|JMUQMRVMIRWTLOTPEJbWOTXOKTZVJMQJFMfbTXdZMQVMQJWSAEYUEIbWJMZVMRUNGLPGDRVMIRSOCGcZ|JNUQNRVMIRWSLOSLHObWKNfbGLWTLPTKNGZUFKUNKRbWBFcZDHWSFJSOCFaWJNQMRIWTPWdaWUYD|JNWTEJbWJMebMRVMIRTPAEUQEJWSNWaTRVZSKOTKFVbWVadZaTPWLPfbGKWSHLZVKOYUDHbWOTXOJNSJ|JNVREJZVJMUQNUQZAEWTMRVMIRbWEJTPLOWTKNTKFOfbGLPGDKbWHLWTBETPCFPGKDZVDGVMJQdZEJeb|JNXTLPUQNRVMIRZUKNTOGLWSNWbSCGUNGKNGDTYUEJURLOSLHORMAEMIJNcZEJZVFKVRNUQZTWaTPWZV|JNVREJZVJMUQNUQZKNXTMRVMIRTPLObXOSfbAEaVRTXVHLbWEJYULOVSOVZSFKdaBEaV|JNUQNRVMIRWTLObWEJTPOTXOKTWSTXZUAEUNFKcZKRZVCFVMEIdZIRZVBEVMEIaVIaeVGLPGDKYUHLVR|JMWTLPUQPWQJENbJFMfbHLYUMQbWAEURLOebBFWSGLbWEJWTLPSLPGRMIRVMGLMIKNaVCGTOLSVODHXT|JNWTLPUQPWbJFMQJENYUHLfbAEbWNRUNKRVMIRWSEJcYLOSLGPaWDGeaCFZVJMWSMQVMQJSOGKYUKTXO|JMWTEJbWJNfbMRVMIRTPAEUQLOWTRUYRNUZVUYVROSaWKNRKFOWNCFTKFOeaBFNJENdZFJbWOSaVSbXe|JNXTLPUQGLYULObXHLVSOVZJFMQJENaVAEWSNWTaEJfbLObWCFUQJNVRNUQZFJZUBFdZJNUQOSebKOZU|JNVREJZVJMUQNUQZAEWTEJTPMRVMJQbWFJWTJNaVNRVMQJYUJMfbMQURKOTKGUPGDKcYBFYRFJeaJNZU|JNVREJZVJMUQNUQZAEXTLObXEJWSHLTPMRVMOVaRJQfbKNRKGNPGCLbWLOdaIMWTFKaWDGeaGLTPBFPG|JNWTEJUQAETPLObWNSWNKRVMIRfbJNbWOTXOGLPGCbeXFKZUDGaVRadWNRUNKRcZEJXTJNZVRaWdNRTO|JNWTEJTPJMUQNRQJFMbWBFWTMQVMQJYUIMURMVaRAEeaEIaVJNZULOfbHLbWDHUQNUQZOSWNKadWFKZV|JNXTLPUQGLZULObXHLURNUQZEJYUJMUQMRVMIRZVCGVMOSWNKIebPWbSFKfbAEbWEJcZKOaVGKZUKNUR|IMXTLOUROXRIJNYUHLUQLPWSNWbSEJfbDHbWGLZULOSLPGcYGLWSLPURKOSLPGRMHLaWGKYUCGdaLPUR|JMXTLPUQMRVMIRZURVaRKNRKFXURGKcZEJRMCFZVDGWSPTVRTWSOKTbSAEMIJMQLHMIRTWRNEJNEBIea|JNWTEJTPJMbWNRUNKRZUFKUNKRdZMQVMQJYUAEfbLOWSOVZSBFXTIMaVMRUNGLPGDaeVEIVRFKcZCGbX|JNWTEJbWJMTPNRUNKRZUFKUNKRXTBFWSMQVMQJYUJNSJFMfbMQbWQZcVAEVSEJTOCFdZIMZVMRVMJQaV|JNUQNRVMIRWSEJbWBEfbLOSLHOZUJMQJENWTAEUQGLTPFJPGCLaVRaeVNScZLPdaEIZUSZUdDGbWJNdZ|IMURMQRMJNMINRVMQJYULOURJMWTMVZLGWbSKNSJENcZAEZUHLXTFKaVEJUQDGTPLOfbNSdZJNeaGLPG|JMWTLObWEJWSMQSLGWaTJNURNUYRHLTOLSVOKTXOAEfbFKOFBKbWDGebEJWSJMZVGLbXKOSNCGdZLPVS|LOWTJMbWMRUNKRVMIRTKGNebHLWSNWbSFKfbKOaWOVZSLPdZEJZUPTUETabWaTXOAJYUDGURBFOLGPSO|JNXTLPUQEJZUHLVSBEaVDHbXNRVMIRUNKRdZJNSJENZVRaWdPWdaWdcZdUYD|JMVSMQWTKOTKFVZSQZdUIMbWMQXTQZcVEJfbGKbXLOSLHOVSOVaRCGeaKNRKGNTOAEOLJMXTEIaVMRVM|LPWTPWbSJMXTMQTPIMSOKTPWFKUREIWTBFfbHLTPLOaWOTYUTadWKObXGLPGCLebFKWSLPSLPGXTGLTP|IMWTMRUNKRVMJQTPEJbWLOWTAETKFOfbJNbWOTXOGLPGCbeXDGZUQZcVBFVRNUYRHLaVLORNFJXT|JNXTEJbXJMVSMQSJFMTPAEfbLOWTEJbWJNWSOVZJMFTOQZcVKTPWHLWSIMYUGKdZKOURCGRIOTXHBEIK|JNWTEJbWJMTPNRUNKRWSMQVMQJfbLOSLHObWJNaVNRVMIRWSOVZSAEdaEJaVRaeVGLPGCLYUFKcZKNSO|JNWTNRUNKRVMIRTOLSZURVaRGKUQHLYULOdaDGaVSZUdGLbWFJWTKNTKNGfbJNVREJZVJMUQNUQZAEXTLObXEJYUMQfbHLTPJNVSOVZJQZdUFMWSBEaVEJbWMQURKOcZCFWTFKSNJSRN|JNWTEJaWBETPNRVMJQUREJXTLObXJNZUQZdUFJUQNUYRJNWSOMQSAETOKTPWEJfbGKeaKNXTDGbXIMaV|JMWTMRUNKRVMIRTOLSZURVaRHLUQLOYUGKRMEJeaDGbWSbXeJNfbNSMIGLQMLPcZKNaWNRMVAEWNFJda|JNWTEJbWJMUQNRQJFMfbLOZUMQUNKRTKGNVMQJYUHLXTIMaVAEUQEIbXCFVSLOTRMOdZJNZUFKURNUQZ|JNVREJZVJMUQNUQZAEYUMQWSEJSOLSVOKTXOJNaWIMeaGKWTDGTPKTPWMRcYNSUNSJ|JMWSKOUQGKQJEWaTAEYUEJURLPeaPWbLHOfbJNZUCGcYGLUQNUYRLPbWOTXOKTWSTXaWFJdaBFSOPTWP|JNXTLPUQHLVSDHSJFMQJENZUIMbXMQURNUYRAEebBFaVFJcZEIVSLOSLHORN" +
        "JSWNPWbLGPNGCLfbIMZU|JNUQNRVMIRWSEJbWAEfbLOSLHOWSOVZSKOSLGPcZCGbWGKZVEIVMIRWSKOSLPGdZBEXTJNaWGKZVRaeV|JNVREJZVJMUQNUQZKNXTMRVMIRTPLObXOSaVRTXVHLfbAEbWEJVSBEZVGKPGCLYUKOcYNRUNLPSLJZdU|JNXTLPUQNRVMIRZURVaRKNRKFXURHLcZEJRNJSWNGKNGDKZVLOYUBFQMFJMFCJUQAEdZJNZUEJbWOTVR|IMUREIWTJNbWNUZJFMfbAEdZMQTPIMWSMRVMQJbWLOSLHOWTJNYUEJaVBEUQNScYJNYUGLPGCLTPSWPG|JMWSLPSOKTXOMQUREJRMIRVMJNMIGLaVLSVODGdaGLaVLSVONRbWCGWSGKfbKTbXRVXOPTOXVOeaAEaW|JMUQMRVMIRWTKNbWFKTPLOZUEJWTAEaVRaeVNSdaSZcVJNURNUQZEJYUBEUQJNZUCFURNUQZFJaWJNWS|JMWSKObWFKUQMRVMIRSNRVaROSXTSJTPJNZVNUYREIfbKNRKGNPGDKVRNUQZKNZVCGdZAEWTEJbWBFZU|JNWTEJTPJMbWMQURNUYRLOfbOTXOKTbXGKXOKTPLHOWPCGaWOTVSTadWAEWTEJZVFKTOKTPWBFSOQURY|JNWTEJTPJMbWNRUNKRZUFKUNKRdZBFWTAEVSFKTOKTXORVaRMVYUCFUQVaeVFKOFEJFMIafbaebWeIZV|JMWSFJbWMQWTJNSJENTPNRUNKRVMQJfbAEXTIMaVMQbXJNVSNWTaEJaVJNVRNUYRLOeaGLPGDKaWHLZU|JNWTLPUQPWbJENXTHLTPAEfbLObXEJYUDHVROSaVGLPGCLVOLSZVSZcVHLdaLOXTOXaWKORTXOURBEeb|IMXTMRUNKRVMJQWSLPTOEJYUAEUREIZVJMcZGLZUQZVcMVaRFKOFCJSOLSRNIMNWDGeaGKaVBFdZKNbX|JNWTEJTPBEbWJMUQNRQJFMWTKNTOLSVOEJXTCFaWFKOFJCWSNWTaCFaWAEfbMQbXIMWTFJeaJNTO|LOUQJNWSNWbLHOfbKNZUNScZOTXOSLURLObWEJRMIRVMAEebEIZUIRUEBIYUFJURGKaVJNbXNUQZCFZU|JMWTMRVMIRUNKRTPEJbWAEWTLOTKGNfbHLPGCLbWLOWSNWaKFOZVRaeVJNVRNUYREJdaDGaWGLcZLPZV|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKYUDGbWSbXeGLfbKNMINSaVSZcVJNbWFKebCGVRLPda|JNUQNRVMIRWSEJbWBEZULOSLHOUNJbfWEJYUAEUREIaVGLeaJMQJFMcZDHWSLPSLHOaWCFWSOTXOKTRN|JMWTMRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKYUDGbWSbXeAEfbEIcYIRUEBIbWGLaVLPYUFJUROTda|JMWTEJUQMRVMIRTPLObWJNWTRUYRNUQMUYaVAEMIEJeaJNZUYRVMFJMFCJaVJMIRNUfbUYdZBEVSOVZS|JNXTLPbXNRUNKRVMIRZVEJVMJQTOAEcZEJebJMaVGLXTLSWNPWbSHLYULOSLMRVMQSLHSW|IMUQKNWSNWbSFKYUJNQJNWaTENTPAEXTEIVSNWTaKNZVLOfbGKbWDGURNUcYUZdUOTURTXYUBEUQEJWS|JMVSMQWTEJTOKTXOJMURMVaRAEeaEJSNJSOVLOaWGLWSFKbWLPSLHOfbBFdaOTbXDGXOKTVSTXZUQZcV|JNUQNRVMIRWSEJbWAEfbLOSLHOWSOVZSKOSLGPcZFKZVCFVMEIbWIRWSKOSLPGdZBEXTGLTOLSaVRaeO|JNVREJZVJMUQNUQZMQWTFJTOKTXOLSVOJNaWGLWSNWbSDGYUIMZVQZdUAEUREIfbGKOFCJbWBFRNLONE|JNXTLPUQGLZULObXHLURNUQZEJYUJMUQMRVMIRZVDGVMOSWNKIebPWbSBEcZIMQJEWaTFKZVKNdZLPTO|JMWSKObWFKUQBFQJFMfbMQYUEJURJMSNLPWSPTSLHONJMFbWFJWPJNaWNUWSIMSLMRVMQJZQDHdZHOZV|JMWSLPSOKTXOMQUREJaWJMbXFJebGKOFBKWTPWbSJNSJMFVSDGXTGLTPLOSLHOfbAEbWCGZUQZcVOSWN|JNUQNRVMIRWTEJZVAEVMEIcZIRZVJMQJFMVSLOSLGWbSKOSLHOaVRaeVMQfbCFbWFKWSDHSLHOdaBFaW|JMWTEJbWMQWSLPSOPWaTAETPKTPWHLWSLPfbJMbWEJSOFKOFBKeaKNWTPWaTCFURNUYRFKTOKTXOJNRK|JMXTLPUQGLQJFMbXEJVSMQebJNSJLOYUIMJFCJaVBEUREIRNKaTKaTXOMRbWRUfbAEWSIMbWEIKFJCSN|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQDHcZHLbWSbXeGKZVAEMIJNfbNSdZLPZUSZUdEJbWCGaV|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGLYUAEMICGbWSbXeJNURNUQZGKfbKNbWNRWSOVZSDGcY|JNUQNRVMIRWSEJbWAEfbLOSLHOWSOVZSKOSLGPcZJNZVEIVMIRdZFKZVBEVMEIaVIaeVDGbWKOYUGKVR|JNUQNRVMIRWSEJSNJSZVSZcMAEMIEJXTLPYUPWbSHLfbKObWOVaRGKRMLPURDHdaHLebLORNKRMVOTVS|JNWTEJTPJMXTNRUNKRZUFKUNKRbWMQVMQJfbIMaVAEdZLOTKGNZUNRUNJZcVEJWSBFYUMQeaQZVcJNSJ|JNVREJZVJMUQNUQZAEWTEJbWMQTPJMWTMRVMQJYUKNUQFKaVBFfbLOZUOSVOIMeaGLPGCSbWSbXeMRQM|LOWTJMbWMRVMIRUNKRTKGNfbFKXTHLbXBFZULOaVRaeVEJUQAEYUDGURNUQZEIZUJNdZFJUQGLTPCFPG|JMUREJWTJNbWNUZJFMfbMQdZIMTOLSVFBKWSKNSJMFbWHLWSLPYUDHURGLaWLOSLHOZUQZcVFKWSKNRT|JNWTEJbWJMfbMRVMIRTPAEUQLOWTOSbWSbTOKTPfGKfbHLXTLPbXPWaTCGZVRaeVGLVRNUQZDGdaEJZV|JMWSKObWMQWTEJTKGWaTLPeaPWaTAEfbCGbWFKTPJNVSEJURNUYRHLZVKOcZJMRNGKPGKTSLDKXFBKLH|IMUQKNWSNWaTLOTKGNbWHLXTLPWSPWSbEIbWBEeaDHfbHLbXCGVSFKXTLPSONROFJCQJENTOGKOFCJZU|JNXTLPbXGLVSDGSJFMUQBFQJENaVNSVOLbfWHLYULOURFJeaAEaVJNcYNUYREJZUJNWSNWTaCFUQFJRMJNUQNRVMIRZULOUNKRWTHLTKGNaVRaeVEIYUAEbWEJfbLPcYCGURNUYRGKWSIMRIBEIBKOBTPfSOfSOK|JNUQEJWTAETPLObWNSWNKRVMIRaWGKfbEIPLDGLSRUYRJMQJFOeaBFaVGLWTLPbWCGcYIMZUOSVOMQOL|JNWTEJTPJMbWMQURNUYRAEfbLOcYOTXOKTbXEJXOGLPGCbeXJMRNFKNGDKaWMRVMQJZVHLYUIMURMQRM|JNWTEJTPJMbWNRUNKRZUFKUNKRXTBFWSFKTOKTPWLOSLHOdZGKZUDGUNKRcZMQVMQJaVJNZUAEfbEJbX|JNVREJZVJMUQNUQZAEXTLObXEJYUMQWSGLTPKNPGCLebNWaKFObWBFWTFKVRKNRKOFURJMTPMVPGDKZS|JNWTEJbWJMURNUZJFMfbAEdZKOTKGNXTLPVSEJZUBFbXFKUQHLTOKTXHPTWPNdcZdUQZCGeaJNaWMQWT|JNWTNRUNKRVMIRaWGKTPLOPLOTXOKaeMHOMIFKbWCGZVEJdZGLfbAEYUKNVSOVZSDHcZLOSLHObXNSWN|JNVRLPZVHLUQNUQZIMWTPWbSK" +
        "OYUEIaWMQebFJURBERNCFZUQZdUFKURJMWTMQcZIMRBKaTKGWbSadBO|JMWSKOaWMQWTEJTKGWbSLPURJMfbAEbWHLeaFJXTCGTODHZUQZdUMQcZBFRNIMWTPdOKFOURdURBUKYU|JNVREJZVJMUQNUQZFJWSBFYUKNUQNWbSMRVMIRSOLSaVRadEAJZUHLURLOeaGLfbLPbWDGcZGKRMOTXO|JMWSEJbWAEWTMRUNKRVMJQTPIMfbFKbWEJaVJNSJMFWTKNVSNWTaFJaWBEeaJNWTEIaWCFWSNWTaLOYU|JNXTLPUQEJZUGLbXLOURNUQZJMVSOVZSKOSLPGfbAEWSEJYUMQdZFKbWIMTOKTXOGKOFBKaVJNSJMFUR|JMUREJWTLPTOKTXOMQRMIRVMJNMIGLaVLSVODGdaGLaVLSVOCGbWNROKGNebRUYKFOWSOVZSHLbWBFfb|JMUQLOQJFMWTEJbWBFTPMQWSAESLHOfbDHVRJMbWMVZLHOYUQZcVGLPNOSVOFKNGCbaWbSXTSVTOIMOK|JNUQNRVMIRWTEJbWLOZVBEVMOSWNKIaVHLYUFKTPLOfbJMQJENVRAEbWEJWTNScYJNeaSWUQNUYRWbXe|JNWTEJTPJMbWMQURNUYRAEfbKOWSFJRMIRVFOVaRBKbWEJeaKNRKGNPGCLZUQZdUDGaVLOUQGKWTNSVR|JNWTEJbWJMUQNRQJFMfbMQVMQJTOLSWEAJYUHLbWBFWSKOZVGKURDHcZLPSLHOZUJNUQNUQZIMZUMQdZ|JNVRFJZVJMUQNUQZMRVMIRZULOUNKRdZEJWSOVZSCFaVRaeVGLcZLOSLHObWJNZUAEUQEJYUFKVRBERM|JNUQEJZULPURNUQZIMYUMQWSKNbWGLebLOSLPGWSNWbSGLURLOSLHOaWFKWSDHSLHOfbCGbWJNcYNUYR|JMUQMRVMIRWTEJbWAETPEIWTJMQJFMZUBFUNKRfbFKbWMQaVRaeVKNcZNRVMQJZVLOTKGNXTJMWSNWTa|JNVREJZVJMUQNUQZAEXTMQTOLSVOKTWPEJbWJNfbHLWTFKbXLOaVBFebNRVMQJYUJNbWFJZVJMVRMVWS|JMVSMQURKOaVEJWTJMTKGWbSLPfbHLbWFKSNKOWSCGebBFbWGKNGLCSLPGRNAEVSFKXTKRZUQZdNEJNE|JNWTLPUQPWbJENXTAETPKOfbFKbXCFVRNUYROScYFJRMIRaVRaeM|JNXTLPbXNRUNKRVMIRZVEIVMIRebAEdZEJaVRaWdPWbSHLfbFKbWDHYULPZVGLcZCFdaBEUQEIZUKNUR|IMUQKNYUNSWNJSQJENVOLSbWSbfWAEZVEJUQHLWTGKdZLOaWDGebNRVMGLTPJNPGCLZULPMJNEWSOVUR|JNVREJZVJMUQNUQZMRVMIRWSFJbWLOSLHOWTJMZUCFUNKRTKFOfbAEbWEJcZJNZUNSWNRKUQMRaVRaeV|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOYUGKdaDGaVSZUdGLbWLPeaEJWTPWaTJNfbNUQZAETPEJbWOTXO|JNWTEJaWLPeaAEVRJMZVEJUQNUQZJNTOKTXONRWSMQVMQJYUFKOMIYZVGKbWCFfbHLdZLOSLPGWSGLbW|JMWTMRUNKRVMIRTOLSZURVaRHLUQLOYUGKdaDGaVSZUdFJbWJNWTNUQZEJfbJNeaAEaVNSTPKNbWSbXe|JNWTEJVRJMUQMVZJFMQJKOTKGEXTEJaVIMbWMQWSCFTOJMYUQZdUMQURFKOFBKfbAEeaLPaWDGcZHLbX|JNWTEJbWJMfbMRVMIRTPAEUQEIZUKOdZFJWTGKPGCLbWLPZVIMVSOVTOKTXOBFWSNdUEdTQCTICJPTYU|JMWSKObWFKUREJYUMQcYJNSJBFWTFMRNKRUNAETKEJNEIBfbGNbWLPVSHLSJMFaVLOeaFKVRCFRNKRWT|JNXTLObXHLUQNSWNKRTKGNVMIRfbFKbWLPZUCGcZDHWTPWaTHLZVRaeVLPTOKTXOGKOFBKdaEIaWAEVS|IMUQKNVRMVaKGNZUDGURNUQZFKWTJNeaBFZVEJYUAEVREIUQNUQZJNZUIMcYMQdZFJTPLObWJMWTMRfb|JMWSLPSOKTXOMQbWEJfbJMVRMVZSQZcVIMVRMVSZAEZVEIWSIMYUMQURGKbXKTXOFKOFBKSNHLNGDKaW|JNXTEJTPJMWSNWbSMQfbAEaWIMUREIdaLOSLHOWSFJSLJNYUDHbWHOVSOVZJMVaRQZcVBFWSFMebMQbX|JNWTEJTPJMXTMRVMIRZVAEVMEIaWIRWSNWTaLOUNKRbWFJWSOVdZGKZSKOSLHO|JNWTEJbWJMfbMRVMIRTPAEWTLOaVRaeVGLPGCLURNUYRLPbWEJZUDGUQOSWEBITOKTXOGKRNKadWFJcZ|JNWTEJTPJMbWMQURNUYRAEfbLOWTFJRMIRVFCJaVJNbWNRVMQJWSOVZSEITOKTPWIMXTGKebKNbXDGTP|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKYUDGbWSbXeAEMIJNURNUQZKNfbFKbWCFWTOXebXVZL|JMWSEJaWKNeaMQSOLSVOJMWSNWbSGLfbDGaVGKURKTXOFKOFBKbXKOdaCFaWLPSLPGWSFKXTAESOEJOF|JNVRFJZVJMWTMQcZLOTPBFbWHLfbNSWNDHRMQSUREJaWAEWNJSeaFJRNKRVFCJYUSVaRJMRNMRUQRKZV|JNWSNWaTIMUREITPLObWOTXOKadWFKfbKOWSAESLHObWEJebOTYUTaVeMVZSGKbWIMebKNbXMQcZBEXT|LOWSHLbWJMUQMRVMIRSNRUYROSXTSJTPJNZVNUQZEJZUJNfbLOVRAEUQNUQZKNaVFJdaGKbXBFVSOVZS|JMWTEJTPMQbWJNVSFJaVJMSJMFfbIMeaMRUNKRVMQJYULOUQJMQJFMWTMQTKGNXTCGbXAEaWEJZVGKdZ|JMWTEJTOLSVOKTXOBEURMVaRJMZVGLdZLSVOMVZSEJYUIMeaAEaVFKOFMQFMQZMIEJSNJSVOZdIEdaEA|JNWTLPUQPWbJENXTHLTPAEfbEJYULObXDHVROSaVGLPGCLVOLSZVSZcVHLdaLOXTOXaWIMRIKOebXeVR|JMXTLPVSMQaVEJeaJNSJFMVSKOTKGNSJMFURFKZVAEcZHLWSCFbXKORNIMaWEIWTPWSbFJNEMRVMQAbW|JMWTEJTPLObWOTXOKTWSTXURAEfbMQRMIRVMEIbWIRZUQZdEBIYUGKSOKTWSFJPWHLURDGcZGKZUCFUQKOWTJMTKFObWMRUNOSVOLJXTIMfbMQaVGKTPJNVRNUYREJWTJNcYNUYRAETOKTPWEJWSHLbWCFdaLOSL|JNWTNRVMIRUNKRTOLSZURVaRGKUQHLdaLOaWDGWNFJeaJSbWSbXeEJcZAEfbCFaWOSWNJSYUEJZVSZUd|JNWTEJbWJMfbMRVMIRTPAEUQEIZULOWTFJdZGLPGCLTPOSPGSVZSNfUEfAGNAdcZdUYRBFXTFKQMKNRK|JNVREJWTJMaWMVZJFMWSLOSLGWbSMQSOKTXOQZcVDGfbGKOFBKYUAEUREJdZJNZUHLbWLOebCFbXFJUQ|JNWTNRVMIRUNKRTOLSZURVaRHLRMLOeaEJUQGKYUDGbWSbXeAEMIJNURNUQZKNfbNRbWEJWSOVZSRUaW|JMWTMRVMIRUNKRaWFKWSRVSNKRZSEJeaBEcZLPTOGLbWJNSJLbXeENZVAEVMEIdZIRZVCFVMHLfbLObX|JNUQNRVMIRWTEJbWLOTPJNWTAEZUOSfbSVTOKTPWFJdZGLZSLOSLHOQMJZcMEIWTIRTKNGaVRaeVCFYU|JMWTMRUNKRVMIRTOLSZURVaRHLRMLOeaEJUQGKbWSbXeDGfbAEMIJNcZGLZULPbWOSWTPWaTEJTPCGda|JNWTNRVMIRUNKRTPFKbWEI" +
        "WSLOSLHOfbAEbWEJWTJNZUBEaWCFcZFJdaJMUQGLQSOcPUEJURDGYUGKTP|JNUQEJWTAETPLOVRNUYRJNZVNUQZFJbWJMWTEJaWBFWSMRVMJQSLHOeaFJaVJNVSNWTaKNfbIMbWGKWT|JMWTLPUQPWQJENbJFMfbHLYUMQbWAEURLOebBFWSOTXOKTbXIMRKGWXOWbaWbLVSDGSOLSZUQZcOCFda|LOUQJMQJFMWSHLYUMRUNKRVMIRbWOVZSLPSOEJOLJNLHAEXTGKaVRaeVNRVMEIMJBFJEIBdaCGcZKNTO|JNWSNWaTLOdaEJbWJMUQMRVMIRaVRaWdAEZVEJYUGLTPKNPGDKfbHLbWLPdaCGURNUQZOTXOKTVRTXZV|JNVRFJZVJMUQNUQZMRVMIRXTLObXEJTPAEWTJNZVEIVMIRcZNSaWSbfWBEZVRaeVEJYUJNVRHLdaOSTO|JMWSKOaWGKWTLPSLPGTOKTXOEJbWMQURJMfbFKOFBKWTAEbXEJYUCFdaHLTOLSVOKTXOMVaRJMOKFOeb|JNWTNRUNKRVMIRTOLSZURVaRGKRMHLeaLOUQDGYUEJbWSbXeGLMILPaVJNURNUQZAEfbEJbWOTdaCGZU|JNVREJZVJMUQNUQZFJWSAEYUMQSOKTXOLSVOJNbWGLfbLSaVNRUNSJ|JMUQMRVMIRWSLOSLHObWEJWTDHTPJMQJFMfbAEbWEJWTJNZUBFUQOSQJNEaVSZcMEIdZIReaFJTOKTPW|JNWTEJbWAEUQNSVOLbfWHLTPLOWTJNaWFJZVNSWNJZcVEJeaBFaWJNYUOSVOFJOMIYQMNSWNGLPGDI|JNWTEJTPJMbWBEUQNRQJFMWTMQVMQJaVIMTOLSVFGLPGDBYUJNUQMRZVRaeVEJdZBFZUHLfbAEbWFKUR|JMWTEJbWMQWSAESOLSVOGLaVLSVOIMfbCGTPKTPWFKXTKNTPBFWTHLbXFKebDHdaMRZVQSTOKTXF|IMXTMRVMJQTPEJbXJNWTAEaVNRVMQJUQJNfbNRZVRaeVEJcZJNZUNSVOLSQMKOTKGNURNUYRHLPGDKbW|JNXTEJTPJMWSNWbSMQSOKTPWLPfbGKURHLWSAEbXKOYUFKcYBFRNKRUNEJNEIBZUQZVcOVaRLOYUDGRM|JNVREJaVLPeaGLVSLOSLPGXTJMZVMQcZAETOKTRKFOWPEJaWJMdaBFbXGLPGDKURFJYUJNWTCFTPOSVO|JMUQMRVMIRWTEJbWLOZUJNdZAEaVRaWdEJZVGLTPOSPGSZcVCLfbKOURNUQZJMbWMQWTOSVOLSeaDGYU|JNVREJZVJMUQNUQZMRVMIRWSFJZUBEUNKRXTRUYRJNSJEUbWAEfbUYdZGKTOKTWGDKbWEJebHLbXLOaV|JMWSEJSOKTXOLSVOMQbWAEfbJMURMVaREJRMIRZUQZdEBIYUGKeaKTWPCGURGLPGDKaVFJbWHLcZJNZU|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOeaFJMFCJbWSbXeJMfbMQUREJbWAEcZEIaVJMdaBFWSOTebTXbW|JNWTEJTPJMbWNRUNKRWSAEfbMQVMQJaVIMYUEIbWMQWTJMTOFKOFBKSOLSVFCJeaJNXTMRcYHLaWNSWN|JNWTEJTPJMXTNRUNKRZUFKUNKRbWMQVMQJfbIMaVAEdZJNZUEIVSMQSJQZcVLOTKGEYUEJWSBFURHLPG|IMURMQRMJNMINRVMQJYUJNUQLOWTEJaVGLTPAEPGCLeaDGbWOSVOLbXeHLZVLPfbKOVRNUQZJNbWNRWS|LOWTJNbWNRVMIRUNKRTKGNebFKWSNWbSHLXTKNSJENZVAEVMEIcZIRZVBEVMEIMJNEaVCGfbEJYULPbW|JNVSLOSJFMWTMQbWEJTPJMWTAEfbHLbWEJaVJNVRMVZJQZcVBFYUFMUQMRVMIRdaCFaVRaWdFJeaJNaV|JNVRFJWSNWbSJMSNMVaRBFXTLPeaPWaTEJNEIBTPKNRKFOfbAEUREJYUGLPGDKbWHLZVLPWSCFSLPGUQ|IMUQKNWTLPYUPWbSNWaTFKTOKTXOEIfbGLdaLSVODGaVGKOFBKURHLbWLPebCGbXKOZUAEcYPTWPGKVS|JMWTLPUQPWQJENbJFMXTAEfbMQVRCFTPEJbWJNZUQZdUHLaVLOUQNUYROTWSTXSNBEPLGPNGDKebXeVS|JNWTEJTPJMXTMQTOKTPWGKbXAEXTEJTPKOPGDKfbHLbXLPWTPWaTCGebGLbWLPVSOVZSQZdUIMUQBEcZ|KNVRGKZVJMUQNUQZMRVMIRWTKNTPDGXTEJbXAEfbGKPGKDTODGbWGLWTLSaVRaeONRZVRadWCGYUEIWS|JNXTLObXNRUNKRVMIRTKFOWSOVZSEJfbHLcZLOSLGPbWJNXTBFZVAEVMEIdZIRaVRaWdPWdaWUYB|JNWTEJbWJMfbMRVMIRTPAEUQLOWTEIZUFJaVRaeVNSVRKNRKOFdaSVaRJMQJFVbWGKUQBFYUFJcYDG|JNVREJZVJMUQNUQZAEWTEJTPJNVSNWbSLOSLHOfbFJbWBFYUMQURJNZVNUVSOVaYKOeaIMWTGKdZFJaV|JMWTKNVRMVaKGNbWEJTPIMPGDKXTMRfbAEbXKOTKFOeaHLWTCFTKNGUNJSYULOURGLZVSZcVEJaWFKWS|JNUQEJWTNRVMIRbWLOfbAETPOTXOKTPLHOWPGKbWKNYURYQMJQWTOXebXVZAFKAbQUbWKOWfBFdaFKfJ|JNWTNRUNKRVMIRTOLSZURVaRHLRMLOMIGKUQDGdZEJZUJNeaGLaWCGURNUYRLPWNFJNEAJbWBFRNJbXe|JMWSKOaWMQWTLPTKGWbSEJfbJMSOAEeaCGbWFJVSBFZVQZdUMQOKFOSCQbCQbeaWeVQUVOUN|KOWTJMTKFObWGKWTBFTPDGUQEJYUAEUROSVOMVZSKTXOIMaVEIdZMRVMIRZVRaeVJMQJFMcZCFfbFJbX|JNWTEJTPJMbWNRUNKRZULOUNFKPLGPNGDKYUAEWTPWaTEJURMQdaHLTPJNPGCLcYNUYRLPaWBFWSFJSL|JMWTMRUNKRVMIRTOLSZURVaRHLRMGKeaLOUQFJMFCJYUDGbWSbXeJMQJENdZAEZVBFfbEIcYNRUNKRVM|JMVSMQWTKOTKFVaRLObWHLeaCFWTLPTKFOfbBFbWFKWTPWaTOSTPKOdaGLPGDKaWSbXeOTRNKRUNEJNEJNWTNRUNKRVMIRTOLSZURVaRGKUQEJQMJQYUQZcOKTXOCGbWAEdZEJWSGKfbKTbXTWSbHLeaLObWFKaV|JMWSKOUQGKQJEWaTLPYUPWbLHOfbAEbWEJUQKNZUDHeaHLURNUQZ|JNWTEJTPJMbWNRUNKRZUFKUNKRdZMQVMQJYULOWSOVZSBEfbJNSJENbWHLXTGKPGCLTPLOURNUWSOVaY|JNVREJZVJMUQNUQZKNXTMQTOLSVOIMWSNWbSGKfbKTbXDGXOGKOLHVaIKOdaAEaWEJZUQZcVJNYUFKUQ|JNWTEJURNUZQAEYUJNVREJTPLOcYHLaVDHeaOSVOLSbWSbXeGLPGKDRKFOfbBFbWDGaVGKdaHLURJMQJ|JNWTEJbWJMTPMQURNUYRAEfbLOcYOTXOKTbXGKXOKTPLHOWPEJaWOTebTadWJMPLFJYUBFWTFKbXJNTO|JNWTEJTPJMbWNRUNKRZUFKUNKRdZBFWSLOSLHOfbAEbWMQVMQJYUGKURJNZUEJcYDGUQNUYRJNWTNUQZ|JNVREJZVJMUQNUQZAEXTLObXMRVMIRTPOTXOKTZVEJVMJQWSTXaVGLPGDKfbHLYUQZdUFJURCFbWLPcZ|JMWTMRUNKRVMIRTOLSZURVaRHLUQLOYUGKRMEJeaDGbWSbXeAEMIKNURNUQZJNfbNSZUGLUQLPQMPTcZ|LPWTPWbSKNaWGLXTFKTPKOPGCLURNUYRBFfbJMbXLPSLPGX" +
        "TEJWSMQcYIMRIAEIKGPVSHLZVLOSLPGVS|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMCFZVHLVRAEMIKNRKFOYUOTdaDHURJNRKEJQMJQIEBIKF|JMWSKOaWMQWTEJTKGWbSLPVRJMSNMVZSQZcVHLfbAEbWLOSLPGdaFKVRBFXTEJNEIBTOKTWPGLPGDKaV|JNVREJZVJMUQNUQZAEXTLObXEJfbMRVMIRZVJNVMNSWNKITKFOdZIMYUMQaVBFVSOVZSQZcVHLbWGKXT|JNWTEJTPJMXTNRUNKRZUFKUNKRbWBFWSFKTOKTPWAEdZMQVMQJfbGKSOKTWGDKbWJNYUEJZVHLUQLOcY|JNUQNRVMIRWSLOSLHObWKNfbGLWTLPTKNGZUFKUNKRbWBFcZDHWSFJSOCFaWJNQMRIWTPWdaWUYDEJXT|JNWTEJbWJMebMRVMIRTPAEUQEJWSNWaTRVZSKOTKFVbWVadZaTPWLPfbGKWSHLZVKOYUDHcYPTURTWXT|JNVREJZVJMUQNUQZKNXTMRVMIRTPLObXOSfbAEaVRTXVHLbWEJYULOVSOVZSFKdaBEaVGLPGCLVREIcY|JNWTLPUQPWbJFMQJENYUHLfbAEbWNRUNKRVMIRWSEJSOLSaVRadEBIZUIMcZGKZVMQURKNRKQUVSUZSN|JNWTEJTPJMUQNRQJFMbWAEWTMQVMQJYUJNfbNRUNKRbWLOTKGNPLHOXTOXebXVZAIMWT|JNVREJZVJMUQNUQZAEXTLObXEJWSHLTPMRVMOVaRJQfbKNRKGNPGCLbWLOdaIMWTFKTPDGebGLPGKDbW|JNXTLPUQNRVMIRZUKNTOGKbXKTXOEIebBEcZFKOFCJZVIMVSHLbXDHXTLOTKNGUNEINEIBQJBFJLHeWS|JNWTEJTPJMbWNRUNKRZUFKUNKRdZBFWSLOSLHOfbDHbWOTXOGLPGCbeXMQVMQJXTFKYUJNZVHLaWLOTP|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSEJfbDGRNCFNEAJYUGKURLPSLPGVSGLSNJSea|JNWTEJbWAEVRLPaVGLWSPWSbLOUQNUYRHLbWLPWTPWebWaVeCGZVJNVSOMQLDHbWHOWTEJTPBFfbIMbW|JNUQNRVMIRWSEJbWBEfbLOSLHOZUJMQJENWTAEUQGLTPDHPGKDaVRaeVHLcZLPVRNUYREIbWFJZVDGda|JNXTLPUQEJZUHLVSBEaVDHbXNRVMIRUNKRdZJNSJENZVRaWdPWdaWdcZdUYDFJDRLORI|LPWTPWbSJMXTMQTPIMSOKTPWFKVRMVZSQZcVHLfbEJbXKOWTAETKGWaTCGeaGKYULOVREIaVJNUQNUQZ|JNWTEJbWAEVRLPaVGLWSPWSbLOUQNUYRHLbWLPWTPWebWaVeCGZVJNbWNUQZOSWNKaeVEJfbFKbWGL|JNWTEJbWAEVRLPaVGLWSPWSbLOUQNUYRHLbWLPWTPWebWaVeCGbWJNZUEJcYGLebDHdZOSXTIMRISVZS|JNWTEJbWJMTPNRUNKRWSMQVMQJfbLOSLHObWJNaVNRVMIRWSOVZSAEdaEJaVRaeVGLPGCLXTFKTPLOSL|JNWTNRUNKRVMIRTOLSZURVaRGKUQHLYULOdaDGaVSZUdGLbWFJWTKNTKNGfbEIbWBFdZJMQJFVZSLOSL|JNVRLPZVHLVSDHSJFVaREJeaJMRNKRUNBFNKFOWTPWaD|JNVRLPZVHLVSDHSJFVaREJeaJMRNKRUNMQYUQZcVBFVSAEaVFJVRCFdZFKRMIRNUKOZVEIURGK|JNVRLPZVHLVSDHSJFVaREJeaJMRNKRUNMQYUQZcVBFVSAEaVFJVRCFdZFKZUJMNJMOJAOSWNKY|JNVRLPZVHLVSDHSJFVaREJeaJMRNKRUNMQYUQZcVBFVSAEaVFJXTCFTOIMdZEINEIBbXMRVMFJMFBa|JNVRLPZVHLVSDHSJFVaREJeaJMRNKRUNMQYUQZcVBFVSAEaVFJXTCFbXGKNGLCTOJMVRMVSZEJdaCGfb|JNVRLPZVHLVSDHSJFVaREJeaJMRNKRUNMQdZBFaVAEXTIMWSPWNKFOYUWNVRMVZAQZcV|JNVRLPZVHLVSDHSJFVaREJeaJMRNKRUNMQdZBFaVAEXTEJNEIBTOLSVOGKWSKTbXCGXOGKfbKTbXTWSb|JNVRLPZVHLVSDHSJFVaREJUQBFdaLOYUGLcYJNQMNSWGFKGNOTXOLZ|JNVRLPZVHLVSDHSJFVaREJUQBFdaLOYUGLcYJNaVFJeaAERMIRVFKB|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSOTQMEIMJDGRNBEVRLPYUGLdaLOSLPGfbTWaT|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSEJfbAEbWLPSLPG|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSEJYUAERMLPSLPGMFCJUREIdaJNRKGN|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSEJRMBEMFCJ|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSOTQMCFMIEJYUDGUQLPdZAEebXeSNJSVXeMQL|JNXTLPUQNRVMIRZURVaRKNRKFXcZGKURHLZVKOWTPWbSEIfbBFbWFJRNCGNEAJYUGKURDHdaLPSLHORM|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVKOWTPWbSEIfbBFbWFJdaAERMIRVFCJWTOVaRXORMJNMJ|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVEIWSLOSLPGbWKNRKGNYUCGURNUQZ|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVEIWSLOSLPGbWGLfbLPWSAERNKaeVXeVReMQA|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZHLZVEIWSLOSLPGbWGLfbLPWSKOSLPGbWGKda|JNXTLPUQNRVMIRZURVaRKNRKFXUREJcZAEZVHLVSDHSNJSWNEJNEBIRNLOYUGLURCGNJGKbWOTQMTadW|JNXTLPUQHLVSEJbXDHYUIMZVAETOKTXOGKcYKTURNUYI|JNXTLPUQHLVSEJbXDHYUIMZVAETOKTXOFKOFBKcYEIebKOURNUYRGKbXJNSJMFRNKRVMIRWTPWaBJNWTNRUNKRVMIRTOLSZURVaRGKUQHLdaSVRMEIaRKNRKIRcZFOZUDHUNOTXOLJ|JNWTNRVMIRUNKRTOLSZURVaRGKRMHLeaLOUQEJbWSbXeAEMIDGYUJNfbNRUNKR|JMWTMRUNKRVMIRTOLSZURVaRGKRMHLeaLOUQEJbWSbXeAEMIDGYUJNURNUQZKNfbNRbWEJWSOVZS|JNWTNRUNKRVMIRTOLSZURVaRGKRMHLeaLOUQEJbWSbXeAEMIDGYUJNURNUQZKNZUNSURGLcZFKfbLPbX|JNWTNRUNKRVMIRTOLSZURVaRGKRMHLeaLOUQEJbWSbXeAEMIDGYUJNURNUQZKNZUNSURGLcZFKaWSbfW|JNUQNRVMIRWSLOSLHObWGLZUKNWTLPTKFOfbRVaTPf|JNUQNRVMIRWSLOSLHObWGLWTKNTKFOfbCFbWFKWTLPaWEJWSPWSLRVZbKOLSNf|JNUQNRVMIRWSLOSLHObWGLWTKNTKFOfbCFbWFKWTLPZVPWaTRaeVNSQMSZcV|JNUQNRVMIRWSLOSLHObWGLWTKNTKFOfbCFbWFKWTLPZVPWaTRaeVEJYUAEURNUQZJNZUEJVRBEcYEIUQ|JMWTEJTOLSVOKTXOMQbWAEfbJMURMVZSEJdZJMYUGLURMVaRDGeaFJSNLSNEBFWNIBaWBEZVHL|JMWSLPSOKTXOMQaWEJWTPWbSJMfbAEbXGLURDGYUGKXTLPeaPNaWKaVeMVZAQZcV|J" +
        "MWSLPSOKTXOMQaWEJWTPWbSJMfbAEbXGLURDGYUEJRNBEOKFOURLPSLHOVSMVSLJSLHGLHOSLZS|JMWSLPSOKTXOMQaWEJWTPWbSJMfbAEbXGLURDGYUFJXTCFTPFKOFJCSOLSVOMVZSQZcVGKOFBKSOKTPW|JNWTEJbWJMURNUZJFMfbAEdZKOTKGNXTLPVSEJZUBFbXFKUQHLTOKTXHPTWPNdcZdUQZCGeaJN|JNWTNRUNKRVMIRaWGKTPLOPLOTXOKaeMHOMIFKbWCGZVEJdZGLfbAEYUKNVSOVZSDHcZLOSLHObXNRUN|JMWSKOaWMQWTEJTKGWbSLPURJMfbAEbWHLeaFJXTCGTODHZUQZdUMQcZBFRNIMWTPdOKFOURdURBUKVR|IMUQEIWTMRVMIRZVAEVMEIcZIRZVJMQJFMVSLOSLGWbSKOSLHOfbBFbWFKWSOVYURYaIYcIEKNEBNRXT|JNWTEJbWJMUQNRQJFMfbMQVMQJTOLSWEAJYUHLbWBFWSKOaWOVZSFKXTLPSOKNOLDHURHXRD|JNWTNRUNKRVMIRTOLSZURVaRHLUQLOYUGKdaDGaVSZUdFJbWJNWSOMQSKNSJEN|JNWTEJaWLPeaAEVRJMZVEJUQNUQZJNTOKTXONRWSMQVMQJYUFKOMIYZVGKbWCFfbHL|JNXTLObXHLUQNSWNKRTKGNVMIRfbFKbWLPZUCGcZDHWTPWaTHLZVRaeVLPTOKTXOGKOFBKdaEIaWKOVS|JNWTEJTPJMXTMRVMIRZVAEVMEIaWIRWSNWTaLOUNKRbWFJWSOVdZGKZSKOSLHOcZJNZVBEVMEIfbIRaV|JNWTEJbWJMfbMRVMIRTPAEUQEIZULOWTFJdZGLPGCLTPOSPGSVZSNfUEfAGNAdcZdUYRBFeaHLaVFJXT|JNVREJWTJMaWMVZJFMWSLOSLGWbSMQSOKTXOQZcVDGfbGKOFBKYUAEbWEJdaHL|JNUQNRVMIRWTEJbWLOTPJNWTAEZUOSfbSVTOKTPWFJdZGLZSLOSLHOQMJZcMEIWTIRTKNGaVRaeV|JMWSKOaWGKWTLPSLPGTOKTXOEJbWMQURJMfbFKOFBKWTAEbXEJYUCFdaHLTOLSVOKTXOMVaRDHebFKOM|JMWTEJbWMQWSAESOLSVOGLaVLSVOIMfbCGTPKTPWFKXTKNTPBFWTHLbXFKebDHdaMRZVQSTOKTXFGKPG|JNVREJZVJMUQNUQZMRVMIRWSFJZUBEUNKRXTRUYRJNSJEUbWAEWSLOTKGWaTHLfbEJbWJNcYNRWSLPTO|JMWSEJSOKTXOLSVOMQbWAEfbJMURMVaREJRMIRZUQZdEBIYUGKeaKTWPFJURHLPGDKbWJNcYNUYRKOaV|JNWTEJTPJMbWNRUNKRWSAEfbMQVMQJaVIMYUEIbWMQWTJNSJFMdaBEVSLOSLHOTKGNPLMRcYDHLGCLXT|JMWTKNVRMVaKGNbWEJTPIMPGDKXTMQfbAETPCGURNUYRJNcYNUYRHLWSFJbWKOZVBFdZQURYFKYUKNUQ|JMWSKOaWMQWTLPTKGWbSEJfbJMSOAEeaCGbWFJVSBFZVQZdUMQOKFOSCQbCQbfaVHLVRLOQCfS|JNVSEJaVKOUQGKZUDGURNUQZKNZUFKURNUYRBEcZJNSJEUZQKNWSNWbSCFVROMQCLPCLHOfbIMbWMQdZ|JMWSKOUQGKQJEWaTLPYUPWbLHOfbAEbWEJUQKNZUDHeaHLURNUQZLPWTPWaKFOVSOVZSJNSJBFXTFMTO|JNWTEJTPJMbWNRUNKRZUFKUNKRdZMQVMQJYULOWSOVZSBEaVJNSJENVRHLRKGNPGDK|JNVREJZVJMUQNUQZKNXTMQTOLSVOIMWSNWbSGKfbKTbXDGXOGKOLHVaIKOdaAEaWEJZUQZcVJNYUCGWT|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMCFZVHLVRAEMIKNRKFOYUOTURTadWJNRKEJKFBKQMJQIE|JNWTEJVRJMUQMVZJFMQJBEYUENUQAEdZIMQALOALGU|JNWTEJTPJMXTNRUNKRZUFKUNKRbWMQVMQJfbIMaVMQVSBFYUQZdUFKSOLSWEAJTOKTPWHLeaLOaVGKbX|JNWTEJbWJMebMRVMIRTPAEUQEJWSNWaTRVZSKOTKFVbWVadZaTPWLPfbGKWSHLZVKOYUDHbWCFURFKcZ|JNVREJZVJMUQNUQZKNXTMRVMIRTPLObXOSfbAEaVRTXVHLbWEJYULOVSOVZSFKdaBEaVEIVRGLPGCLcY|JNWTLPUQPWbJFMQJENYUHLfbAEbWNRUNKRVMIRWSEJcYLOSLGPaWDGeaCFZVJMWTPWaTRadWMRWSFJTP|JNWTEJTPJMUQNRQJFMbWAEWTMQVMQJYUJNfbNRUNKRbWLOTKGNPLHOXTOXebXVZABFWTFKTPKOAfCGfb|JNVREJZVJMUQNUQZAEXTLObXEJWSHLTPMRVMOVaRJQfbKNRKGNPGCLbWLOdaIMWTFKTPDGaVBFYUMRVM|JNXTLPUQEJVSAEbXIMZUEIaVGLebMRVMIRQMJZcMNRMVKOTKFOYUCFURFJdZDGRNBEZUEINEIBUQGKQM|IMWTMRUNKRVMJQTPEJbWLOWTAETKFOfbJNbWOTXOGLPGCbeXDGZUQZcVBFVRNUYRHLaVLORNFJXTJZTD|JNXTEJbXJMVSMQSJFMTPAEfbLOWTEJbWJNWSOVZJMFTOQZcVKTPWHLWSIMYUGKdZKOURMQaWDHRNLPSL|JNWTEJbWJMTPNRUNKRWSMQVMQJfbLOSLHObWJNaVNRVMIRWSOVZSAEda|JNWTNRUNKRVMIRTOLSZURVaRGKUQHLYULOdaDGaVSZUdGLbWFJWTKNTKNGfbEIdaBEcYJMQJEUYRAEbW|JMWSEJURKOaWFKWTKNTKNWbSGWebBFbSLOSLHOZUOSVOMVfbJNUQAEbWFJOLNSWNJSXTEJYUDHTOSWdZ|JNVREJWTJMUQMVZJFMQJBFYUFMUQMRTPAEdZLOXTOXaVRaeVXeVReMQA|JNVREJWTJMUQMVZJFMQJBFYUFMUQMRTPAEdZRUbWUdaVdTXFCJVS|JNVREJWTJMUQNUQJFMZJBFYUFMUQMRTPAEdZKNbWGKPGCLQMRUZQIRaVRTXF|JNVREJWTJMUQMVZJFMQJBFYUFMUQMRTPAEdZKNbWEJZVCFVMIRcZRUebUdQMJQWTdWbCJNVREJWTJMUQNUQJFMZJBFYUFMUQMRTPAEdZKNbWCFWTFKZVLOVMIRcZEIQMRUZQIRaVRaeVNSVRKNTK|JNVREJWTJMUQMVZJFMQJBFYUFMUQMRTPAEdZEJZVJNVMIRcZ|JNVREJWTJMUQMVZJFMQJBFYUFMUQMRTPAEdZKNbWRUebUdWTdWbA|JMUREJWTLObWMQTPJNWTNUYRAEfbEJRMIRVMJNMIFJZUQZdUOSbWSbTOKTPfHLfbLObWGKebCFcZDHWT|JNXTLPUQNRVMIRZURVaRKNRKFXcZEJURAERMJNMJEIJSIMQJCFJLHc|JMUREJWSKObWGKWTLPSLPWaTHOfbAEdaKNRKJNKRCGTKGf|JNVREJZVJMUQNUQZAEXTLObXMRVMIRTPFJWTEIZUJNdZOSfbIMUQBEQARVaRNdAWKOTKdB|JNWTNRUNKRVMIRTOLSZURVaRGKRMEJUQHLeaKOcZDGbWSbfWGKMILPZVJNYUOSVOKTXONRUNFKOFCb|JNUQNRVMIRWTEJZVAEVMEIcZIRZVJMQJFMVSKOTKGWbSLOSLHOfbBEaVRaeVDGbWEJYUJNdaNSWNOTXO|JNVREJZVJMUQNUQZLOWSGLYUMQbWAEWTEJURLPSLPWaTHOeaJNcYNUYRFJRMIRVFCJfbJMaVBEbWEJWS|JNVRLPZVHLUQNUQZIMWTPWbSKOYUMQaWEJWTAETKGWURFKRMCFMIDHcYKNVSQUYKFc|JNVRLPZVHLUQ" +
        "NUQZIMWTPWbSKOYUMQaWEJWTAETKGWURFKRMCFMIDHcYKNYUNSVOLSeaJNaTEJTPSWXT|JNVRLPZVHLUQNUQZIMYUMQWSKOUREJbWGKRMAEMICGcYKNWTNWTKGNaTPWYUFKeaLPaTPWVSDGSbNRUN|JNVREJWTJMaWMVZJFMWSMRUNKReaIMcZLPSOPWbSAEZUCFUNFKOFBRdZMQXTGLfbEJbWLOTKHLWTLOSL|JMVSMQURKOSNOSNKGUWNCGYRLOcYEJNEAJRMIRZUQZdEBIbWGKYUDGaVFJVRJMUQMVWSHLSZIMQJKNJS|JNWTNRUNKRVMIRTPEJbWAEWTJNaWEJWSNWTaLOfbGLPGDKbWHLZVJMWTLPcZPWaTRaeVMQdaFJVRBERM|JNVSEJaVKOUQGKZUDGURNUYRBEcYJMQJEUYRAEdZEJZULPSLHOWSJMSLMQLHQSHDSVRaKODBIMBTPd|JNVSEJaVKOUQGKZUBEURNUQZKNZUDGXTOXVRGKSOKaRBLOeVXeBXeMXeMaeFCJUR|JNWTEJTPJMXTNRUNKRZUFKUNKRbWAEfbMQVMQJYULOTKGNUQBFWTCGbWHLaVNRVMIRWSFKSNJSTOKTPU|JMWTMRUNKRVMIRZUFKUNKRTPLObWEJWTCFTKFOfbAEbWGLPGDKdZHLWSOVZSKOaVRaeVEIcZJMYUBEXT|JMWTLObWEJTPMQURJNfbNUYRAEcYHLWSEJXTOXSNJSVHBEbWFJRMIRPLGPZUQZdGCLHOJNYUEIUQDHaV|IMUQEIYUAEVSKNaVGKeaLPXTHLURNUTOKTSNJSQATXVHXVZSUYfbCGdZGKbXIMXTMRSO|KOWTJMTKFObWMRVMIRUNOSNKSbfWGNaVEJYUAEebDGUQGKZULOURNUQZBFZUJNVRHLcYFJUQNUYRJNda|KNWTLPVRPWRKGNaTIMTPFKXTHLPGCLZVMQTPQSPGSWbSNWGNJSeaEJaTSVTODGfbJMbXGKOFBK|JMUQMRVMIRWTEJZVAEVMEIcZIRZVJMQJFMVSMQTOKTXOGKOFCJaVRaeVLOSLHObWJMdZMRVMQJ|JNWTEJTPJMXTMRVMIRZVAEVMEIcZIRZVLOVMOXUQHLMIFJaVLOYUNSVRJNRMCFdaDHURNUQZKNZUFKaW|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNMIAEQMCFZVNRMJRTJAFJAGDKYUHLURTWbSBEIBKOBT|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNMIAEQMCFZVNRMJRTJAFJAGDKYUHLUQLOdaOSbWSbfW|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNdaKOZVOTVSBESJENMIDGQMGKMJNEIBCGBOTKaVHLYU|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNdaKOZVOTVSBESJENYUCFMIDGQMGKUQKOMJNEIKOFQM|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNZUDGMIAEQMCFUQEJdZHLZVKOVRNUYRGKRNKRMVOTIE|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNZUDGMIAEQMCFUQEJdZHLZVKOVRNUYRGKWTPWbSOVRa|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNZUDGMIAEQMCFUQEJdZHLZVKOWSNWbSGKVROVRaLOfb|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNZUDGMIAEQMCFUQEJdZGLZVLOWSNWbLHOfbKNbWNRea|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNZUDGMIAEQMCFUQEJdZGLZVLOWSNWbLHOfbPTYUKNVR|JNXTLPUQNRVMIRZURVaRKNRKFXURGKcZEJRMJNZUDGMIAEQMCFUQEJdZGLZVLOWSNWbLPGfbHLbWLOWT|KOVROS|LPVSHLaVKOXTOXSN|JMURKOWSEJbWFKeb|LPVRJMZVMQcZEJRM|JNURNUYREJWSLOSLHO|JNUQLOWTEJZUHLUR|LPWSKNbWGLebFKVRLOSL|LOXT|JNVSEJUQIMZUAEcZKO";

    function buildOpeningBook() {
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
            return { move: bookMove, score: 0, depth: 0, nodes: 0, pv: [bookMove], isBook: true };
        }

        if (moves.length === 1) {
            const res = { move: moves[0], score: state.eval(), depth: 1, nodes: 1, pv: [moves[0]], isBook: false };
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
            move: bestMove,
            score: bestScore,
            depth: reachedDepth,
            nodes,
            pv,
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
        if (cfgMode === MODE_TABLITA && !tablitaManager) {
            tablitaManager = new TablitaManager();
            tablitaManager.selectTablita();
            tablitaGameNum = 1;
            tablitaMatchScore = { w: 0, b: 0 };
            tablitaSubMode = parseInt(document.getElementById('tablita-submode').value);
            updateTablitaUI();
        }

        // ── Tablita mode: rebuild position from tablita moves ─────────────
        if (cfgMode === MODE_TABLITA && tablitaManager && tablitaManager.currentTablita) {
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
                             state: ns2, children: [], move: found };
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
        if (isCPU&&cfgMode!==MODE_SAND&&!isAnalysisOn) return;
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
        const n={ id:nextNodeId++, parent:currentNode, moveStr:move2Str(m), state:newState, children:[], move:m };
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
        stopClock(); gameStarted=false; gameEnded=false;
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

    // ── PDN: Conversão de Coordenadas ─────────────────────────────────────────
    // Numeração PDN padrão (FMJD/CBD): quadrado 1 = b1 (canto inferior-esquerdo
    //   escuro), quadrado 32 = g8 (canto superior-direito escuro).
    //   Esquerda→direita, baixo→cima, apenas casas escuras.
    // No mapeamento interno (rows 0=topo, rows 7=baixo):
    //   idxToNum: mapeia row 7→lins 1-4, row 6→5-8, ..., row 0→29-32.
    //   numToIdx: inverso correto (7-r).
    //   numToIdxAlt: mapeamento espelhado para compatibilidade com
    //   arquivos PDN de outras fontes (ex: lidraughts, international).
    function idxToNum(idx) {
        const r = idx >> 3, c = idx & 7;
        if ((r + c) % 2 !== 0) return -1;
        const offset = r % 2 === 0 ? c / 2 : (c - 1) / 2;
        return (7 - r) * 4 + offset + 1;
    }
    function numToIdx(num) {
        if (num < 1 || num > 32) return -1;
        const r = 7 - Math.floor((num - 1) / 4), offset = (num - 1) % 4;
        const c = r % 2 === 0 ? offset * 2 : offset * 2 + 1;
        return r * 8 + c;
    }
    function numToIdxAlt(num) {
        if (num < 1 || num > 32) return -1;
        return numToIdx(33 - num);
    }

    // ── PDN: Formatação de Lance ──────────────────────────────────────────────
    function move2PDN(m) {
        if (!m) return '?';
        const from = idxToNum(m.from);
        if (m.captured.length > 0) {
            const parts = [from];
            for (const p of m.path) parts.push(idxToNum(p));
            return parts.join('x');
        }
        return from + '-' + idxToNum(m.to);
    }

    // ── PDN: Geração do Texto ─────────────────────────────────────────────────
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
        txt += `\n`;
        txt += `{DraughtsMind Pro v${ENGINE_VERSION} | depth:${cfgDepth} | time:${timeLimit} | hash:${gameState.hash.toString(16).toUpperCase().slice(-8)}}\n\n`;
        txt += generatePDN(rootNode, 0).trim() + `\n${result}\n`;
        const name = `mind_game_${Date.now()}.pdn`;
        if (window.electronAPI?.saveFile) {
            try {
                const r = await window.electronAPI.saveFile({ content: txt, filename: name, filters: [{ name: 'PDN', extensions: ['pdn'] }] });
                if (r && r.success) { txtAnalysis.innerHTML = `<span style="color:#66bb6a;">✓ Exportado: ${r.path}</span>`; return; }
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
    function tryMatchMove(state, tk, useAlt) {
        const moves = state.getMoves();
        let found = moves.find(m => move2Str(m).toLowerCase() === tk.toLowerCase());
        if (found) return found;
        // 1st fallback: numeric PDN (num-num or numxnum)
        if (/^\d+([-x:]\d+)+$/i.test(tk)) {
            const pts = tk.split(/[-x:]/i).map(Number), isCapture = /[x:]/i.test(tk);
            const conv = useAlt ? numToIdxAlt : numToIdx;
            const sIdx = conv(pts[0]), eIdx = conv(pts[pts.length - 1]);
            if (sIdx >= 0 && eIdx >= 0) {
                let poss = moves.filter(m => m.from === sIdx && m.to === eIdx);
                if (poss.length > 1 && pts.length > 2) {
                    const ep = pts.slice(1).map(conv);
                    const nw = poss.filter(m => m.path.length === ep.length && m.path.every((sq, i) => sq === ep[i]));
                    if (nw.length > 0) poss = nw;
                }
                if (poss.length > 1 && isCapture) { const c = poss.filter(m => m.captured.length > 0); if (c.length > 0) poss = c; }
                if (poss.length > 0) return poss[0];
            }
        }
        // 2nd fallback: algebraic notation (e.g. a3-b4, c5xe7)
        if (/^[a-h][1-8]([-x:][a-h][1-8])+$/i.test(tk)) {
            const sqs = tk.split(/[-x:]/i);
            const sIdx = algToIdx(sqs[0]), eIdx = algToIdx(sqs[sqs.length - 1]);
            if (sIdx >= 0 && eIdx >= 0) {
                const poss = moves.filter(m => m.from === sIdx && m.to === eIdx);
                if (poss.length > 0) return poss[0];
            }
        }
        return null;
    }

    function parsePDNTokens(tokens, useAlt) {
        const ns = new State(); ns.timeW = timeLimit; ns.timeB = timeLimit;
        const rn = { id: 0, parent: null, moveStr: null, state: ns, children: [] };
        let nid = 1, curr = rn, skipped = [];
        // varDepthStack tracks variation nesting depth.
        // varDepth = 0 → main line, varDepth > 0 → inside variation.
        // Children created at varDepth > 0 are flagged _var:true so they
        // can be reordered after main‑line children at the end of parsing.
        const varDepthStack = [];
        let varDepth = 0;
        for (const tk of tokens) {
            if (tk === '(') {
                varDepthStack.push(varDepth);
                varDepth = 1; // next direct children are variation branches
            } else if (tk === ')') {
                if (varDepthStack.length > 0) {
                    varDepth = varDepthStack.pop();
                }
            } else {
                const found = tryMatchMove(curr.state, tk, useAlt);
                if (!found) { skipped.push(tk); continue; }
                const mStr = move2Str(found);
                const ex = curr.children.find(c => c.moveStr === mStr);
                if (ex) { curr = ex; }
                else {
                    const ns2 = curr.state.clone();
                    ns2.applyMove(found); ns2.timeW = timeLimit; ns2.timeB = timeLimit;
                    const nd = { id: nid++, parent: curr, moveStr: mStr,
                                 state: ns2, children: [], move: found,
                                 _var: varDepth > 0 };
                    curr.children.push(nd); allNodes[nd.id] = nd; curr = nd;
                }
            }
        }
        // Post‑process: reorder children so main‑line (non-var) come first
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
        str.replace(/^\[(\w+)\s+"([^"]*)"\]/gm, (_, key, val) => { headers[key.toLowerCase()] = val; });

        str = str.replace(/^%[^\r\n]*/gm, ' ');
        str = str.replace(/^\[[^\]]*\][ \t]*/gm, ' ');
        let prev;
        do { prev = str; str = str.replace(/\{[^{}]*\}/g, ' '); } while (str !== prev);
        str = str.replace(/\r?\n/g, ' ');
        str = str.replace(/\$\d{1,3}/g, ' ').replace(/[?!]+/g, ' ');
        str = str.replace(/\b(1\/2-1\/2|2-0|0-2|1-1|1-0|0-1)\b/g, ' ').replace(/\*/g, ' ');
        str = str.replace(/\d+\.+/g, ' ');
        str = str.replace(/\(/g, ' ( ').replace(/\)/g, ' ) ');

        const tokens = str.split(/\s+/).filter(t => t.length > 0);

        allNodes = {};
        let r1 = parsePDNTokens(tokens, false);
        let r2 = parsePDNTokens(tokens, true);
        let r;
        if (r2.nodeCount > r1.nodeCount && r2.skipped.length < r1.skipped.length) {
            r = r2;
        } else {
            r = r1;
        }

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

