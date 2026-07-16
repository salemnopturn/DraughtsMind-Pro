"use strict";

const {
    EMPTY, W_MAN, V_MAN, W_KING, V_KING,
    NO_CAPTURES, DIRS_ALL, DIRS_W, DIRS_B,
    M64, zp, zt, getPieceIdx, PST_M, PST_K,
    CENTER_BIG, CENTER_SM
} = require('./constants');

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

        // Returns 0 (not endgame), or N (endgame draw after N half-moves)
        // CBD Art.99: 2D×1D, 1D×1D, (1D+1P)×1D, etc = draw after 5 moves (10 half-moves)
        // CBD Art.100: 3D×1D, (2D+1P)×1D, (1D+2P)×1D with lone king on main diagonal = draw after 5 moves (10 half-moves)
        const { wP, bP, wK, bK } = this;
        const endgameLimit = (() => {
            if (wP === 0 && bP === 0) {
                // Art.99: 1D×1D — empate em 5 lances (10 meios-lances)
                if (wK === 1 && bK === 1) return 10;
                // Art.99: 2D×1D, 1D×2D — empate em 5 lances
                if (wK <= 2 && bK <= 2 && wK >= 1 && bK >= 1) return 10;
                if ((wK === 3 && bK === 1) || (bK === 3 && wK === 1)) {
                    const loneColor = wK === 1 ? W_KING : V_KING;
                    for (let i = 0; i < 64; i++)
                        if (this.board[i] === loneColor && (i >> 3) === (i & 7)) return 10;
                    return 0;
                }
            }
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
            if (wK === 1 && bK === 1 && wP === 1 && bP === 1) return 10;
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
            return "Empate: limite de 5 lances no final (CBD Art.99/100).";
        if (this.hashHist.length >= 9) {
            const cur = this.hash; let cnt = 0;
            for (const h of this.hashHist) if (h === cur) cnt++;
            if (cnt >= 3) return "Empate: mesma posição repetida 3 vezes (CBD Art.98).";
        }
        return false;
    }

    eval() {
        const { wP, bP, wK, bK, board, turn } = this;
        const totalPieces = wP + bP + wK + bK;
        if (totalPieces === 0) return 0;
        const ph = Math.min(totalPieces, 24);

        // Dynamic king value: more valuable in endgames
        const kv = 300 + (24 - ph) * 8;
        let sc = (wP - bP) * 100 + (wK - bK) * kv;

        // Count friendly pawns for adjacency checks
        const wPawnAt = new Uint8Array(64);
        const bPawnAt = new Uint8Array(64);
        const wKingAt = new Uint8Array(64);
        const bKingAt = new Uint8Array(64);

        for (let i = 0; i < 64; i++) {
            const p = board[i];
            if (p === W_MAN) wPawnAt[i] = 1;
            else if (p === V_MAN) bPawnAt[i] = 1;
            else if (p === W_KING) wKingAt[i] = 1;
            else if (p === V_KING) bKingAt[i] = 1;
        }

        let wMob = 0, bMob = 0;
        let wAdvanced = 0, bAdvanced = 0;
        let wConnected = 0, bConnected = 0;
        let wPassed = 0, bPassed = 0;
        let wKingSafety = 0, bKingSafety = 0;

        for (let i = 0; i < 64; i++) {
            const p = board[i];
            if (p === 0) continue;
            const r = i >> 3, c = i & 7;
            const isWhite = (p > 0);

            // ── PST bonuses ──
            if (p === W_MAN) sc += PST_M[i];
            else if (p === V_MAN) sc -= PST_M[63 - i];
            else if (p === W_KING) sc += PST_K[i];
            else if (p === V_KING) sc -= PST_K[63 - i];

            // ── Edge penalty (kings are worse on edges) ──
            if (c === 0 || c === 7) {
                const edgePen = 5 + ((24 - ph) >> 2);
                if (Math.abs(p) === 2) {
                    sc += isWhite ? -edgePen * 2 : edgePen * 2;
                } else {
                    sc += isWhite ? -edgePen : edgePen;
                }
            }

            // ── Center control ──
            const centerBonus = 8 + ((24 - ph) >> 2);
            if (CENTER_BIG.has(i)) sc += isWhite ? centerBonus + 3 : -(centerBonus + 3);
            else if (CENTER_SM.has(i)) sc += isWhite ? centerBonus : -centerBonus;

            // ── Advanced pawns (closer to promotion = more valuable) ──
            if (Math.abs(p) === 1) {
                const advance = isWhite ? r : (7 - r);
                const advBonus = [0, 0, 5, 12, 22, 35, 55, 0][advance];
                if (isWhite) wAdvanced += advBonus; else bAdvanced += advBonus;

                // Passed pawn detection: no enemy pawns blocking or ahead
                let passed = true;
                for (let pr = isWhite ? r + 1 : 0; pr <= (isWhite ? 7 : r - 1); pr++) {
                    const pi = pr * 8 + c;
                    if (pi >= 0 && pi < 64 && board[pi] === (isWhite ? V_MAN : W_MAN)) {
                        passed = false; break;
                    }
                }
                if (passed) {
                    const passBonus = 10 + advance * 8;
                    if (isWhite) wPassed += passBonus; else bPassed += passBonus;
                }

                // Connected pawns (adjacent friendly pawns protect each other)
                const adj = [[r-1,c-1],[r-1,c+1],[r,c-1],[r,c+1],[r+1,c-1],[r+1,c+1]];
                for (const [ar, ac] of adj) {
                    if (ar >= 0 && ar < 8 && ac >= 0 && ac < 8) {
                        const ai = ar * 8 + ac;
                        if (board[ai] === (isWhite ? W_MAN : V_MAN)) {
                            if (isWhite) wConnected += 4; else bConnected += 4;
                            break;
                        }
                    }
                }

                // Isolated pawn penalty (no friendly pawns on adjacent columns)
                let isolated = true;
                for (let dc = -1; dc <= 1; dc++) {
                    if (dc === 0) continue;
                    const nc = c + dc;
                    if (nc < 0 || nc > 7) continue;
                    for (let nr = 0; nr < 8; nr++) {
                        const ni = nr * 8 + nc;
                        if (board[ni] === (isWhite ? W_MAN : V_MAN)) {
                            isolated = false; break;
                        }
                    }
                    if (!isolated) break;
                }
                if (isolated) sc += isWhite ? -12 : 12;

                // Back rank defense: pawns on row 1 (white) or row 6 (black)
                if ((isWhite && r === 0) || (!isWhite && r === 7)) sc += isWhite ? 8 : -8;

            } else {
                // ── King evaluation ──
                if (Math.abs(p) === 2) {
                    // King centralization (more important in endgames)
                    const centerDist = Math.abs(r - 3.5) + Math.abs(c - 3.5);
                    const kingCenterBonus = Math.round((7 - centerDist) * (3 + (24 - ph) / 4));
                    if (isWhite) wKingSafety += kingCenterBonus; else bKingSafety += kingCenterBonus;

                    // King on edge is worse in endgames
                    if (c === 0 || c === 7) {
                        const edgePen = 3 + (24 - ph) / 3;
                        sc += isWhite ? -Math.round(edgePen) : Math.round(edgePen);
                    }

                    // Mobility: kings in opponent half contribute more
                    const inOppHalf = (isWhite && r >= 3) || (!isWhite && r <= 4);
                    if (inOppHalf) {
                        if (isWhite) wMob += 3; else bMob += 3;
                    } else {
                        if (isWhite) wMob += 1; else bMob += 1;
                    }

                    // King safety: avoid being close to opponent pawns
                    for (let dr = -2; dr <= 2; dr++) {
                        for (let dc = -2; dc <= 2; dc++) {
                            const nr = r + dr, nc = c + dc;
                            if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
                                const ni = nr * 8 + nc;
                                const ep = board[ni];
                                if (isWhite && ep === V_MAN) sc -= 5;
                                else if (!isWhite && ep === W_MAN) sc += 5;
                            }
                        }
                    }
                }
            }
        }

        // ── Combine positional terms ──
        sc += (wAdvanced - bAdvanced);
        sc += (wConnected - bConnected);
        sc += (wPassed - bPassed);
        sc += (wMob - bMob) * 3;
        sc += (wKingSafety - bKingSafety);

        // ── Mobility bonus (actual move count advantage) ──
        // This is a rough proxy: pieces in opponent half contribute more
        const wMobility = wMob;
        const bMobility = bMob;
        sc += (wMobility - bMobility) * 2;

        // ── Tempo bonus (having the move is worth ~15-25 centipawns) ──
        sc += 12;

        return turn === 1 ? sc : -sc;
    }

    setBoardFromArray(boardArray, turn) {
        for (let i = 0; i < 64; i++) this.board[i] = boardArray[i] || EMPTY;
        this.turn = turn || 1;
        this._rehash();
        this.hashHist = [this.hash];
        this.halfMoveClock = 0;
        this.endgameClock = 0;
        this.isEndgame = false;
        this.endgameLimit = 10;
        this.wP = this.bP = this.wK = this.bK = 0;
        for (let i = 0; i < 64; i++) {
            const p = this.board[i];
            if (p === W_MAN) this.wP++;
            else if (p === V_MAN) this.bP++;
            else if (p === W_KING) this.wK++;
            else if (p === V_KING) this.bK++;
        }
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
}

module.exports = { State, saveMP, restoreMP, allocMv, idx2Str, move2Str, moveSorter };
