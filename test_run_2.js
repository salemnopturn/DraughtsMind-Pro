
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

    

const s = new State();
const moves = s.getMoves();
const m1 = moves.find(m => move2Str(m) === 'c3-b4');
if (m1) {
    s.applyMove(m1);
    console.log("Applied c3-b4");
    const m2List = s.getMoves();
    console.log("Black moves after c3-b4:", m2List.map(move2Str));
}
