// ═══════════════════════════════════════════════════════════════════════════
// tablita.js — Official Tablita System for Brazilian Draughts
// Derived from the DraughtsMind Classic opening book
// ═══════════════════════════════════════════════════════════════════════════
//
// A "Tablita" is a preset sequence of opening moves used in tournament play
// to ensure fair, varied openings. In micromatch format (2 games), the
// player who had white in game 1 gets black in game 2, and both play the
// same Tablita from opposite sides.
//
// Rules reference (CBD/FMJD):
// - Tablitas are chosen randomly with uniform probability
// - Each Tablita leads to a position where the board is practically complete
// - The same Tablita is used for both games in a micromatch, with colors swapped
// - Match result: 2 wins = 2pts, 1-1 = 1pt each, 2 losses = 0pts
// ═══════════════════════════════════════════════════════════════════════════

// ── Tablita definitions ───────────────────────────────────────────────────
// Each tablita is a short sequence of moves (2-6 plies) derived from the
// opening book, leading to a realistic opening position.
// Moves are in algebraic notation: "from-square to-square" (e.g., "c3-d4")
// Captures use 'x' (e.g., "d4xf6")
// The sequences represent balanced, well-known opening positions.

const TABLITAS = [
    // ═══ CLÁSSICA (c3-d4 d6-c5) ═══
    { name: 'Clássica',    moves: ['c3-d4', 'd6-c5'] },

    // ═══ CRUZ (c3-d4 d6-e5) ═══
    { name: 'Cruz',    moves: ['c3-d4', 'd6-e5'] },
    { name: 'Cruz JV', moves: ['c3-d4', 'd6-e5', 'b2-c3', 'e7-d6'] },

    // ═══ PIONEIRO (c3-d4 b6-c5) ═══
    { name: 'Pioneiro',    moves: ['c3-d4', 'b6-c5'] },
    { name: 'Pioneiro NU', moves: ['c3-d4', 'b6-c5', 'd4xb6', 'a7xc5'] },

    // ═══ FLANK (c3-d4 f6-g5) ═══
    { name: 'Flank',    moves: ['c3-d4', 'f6-g5'] },
    { name: 'Flank NR', moves: ['c3-d4', 'f6-g5', 'd4-c5', 'd6xb4'] },

    // ═══ RUSSA (c3-b4) ═══
    { name: 'Russa',    moves: ['c3-b4'] },
    { name: 'Russa WS', moves: ['c3-b4', 'f6-e5'] },
    { name: 'Russa UR', moves: ['c3-b4', 'b6-c5'] },
    { name: 'Russa VS', moves: ['c3-b4', 'd6-e5'] },
    { name: 'Russa XT', moves: ['c3-b4', 'h6-g5'] },
    { name: 'Russa WT', moves: ['c3-b4', 'f6-g5'] },
    { name: 'Russa MQ', moves: ['c3-b4', 'b6-a5'] },

    // ═══ ABERTURAS ALTERNATIVAS ═══
    { name: 'g3-f4 VS', moves: ['g3-f4', 'd6-e5'] },
    { name: 'g3-f4 WT', moves: ['g3-f4', 'f6-g5'] },
    { name: 'g3-h4 VS', moves: ['g3-h4', 'd6-e5'] },

    // ═══ DEEPER BOOK LINES (4-6 moves) ═══
    { name: 'Cruz Profunda',   moves: ['c3-d4', 'd6-e5', 'b2-c3', 'e7-d6', 'e3-f4', 'b6-a5'] },
    { name: 'Pioneiro Prof.',  moves: ['c3-d4', 'b6-c5', 'd4xb6', 'a7xc5', 'b2-c3', 'f6-g5'] },
    { name: 'Russa Profunda',  moves: ['c3-b4', 'f6-e5', 'b4-a5', 'b6-c5', 'g3-h4', 'e5-f4'] },
    { name: 'Turca',           moves: ['c3-d4', 'd6-e5', 'b2-c3', 'b6-a5', 'a3-b4', 'c7-b6'] },
    { name: 'Americana',       moves: ['c3-d4', 'b6-c5', 'd4xb6', 'a7xc5', 'b2-c3', 'f6-e5'] },

    // ═══ ABERTURAS RARAS ═══
    { name: 'a3-b4',   moves: ['c3-d4', 'd6-e5', 'b2-c3', 'b6-a5', 'a3-b4'] },
];

// ═══ Tablita match manager ════════════════════════════════════════════════

class TablitaManager {
    constructor() {
        this.currentTablita = null;
        this.gameNumber = 0;       // 0 = not started, 1 = game 1, 2 = game 2
        this.matchResults = [];    // array of { game, result } for current match
        this.matchHistory = [];    // array of past match results
        this.playerColor = 1;      // 1 = white, -1 = black (player's color in game 1)
    }

    // ── Select a random Tablita with uniform probability ─────────────────
    selectTablita() {
        const idx = Math.floor(Math.random() * TABLITAS.length);
        this.currentTablita = TABLITAS[idx];
        this.gameNumber = 1;
        this.matchResults = [];
        this.playerColor = 1; // Player starts as white in game 1
        return this.currentTablita;
    }

    // ── Get the Tablita moves for the current game ───────────────────────
    // Returns moves as array of { from, to } objects (board indices)
    getTablitaMoves(algToIdx) {
        if (!this.currentTablita) return [];
        return this.currentTablita.moves.map(m => {
            const parts = m.split(/[-x]/);
            return { from: algToIdx(parts[0]), to: algToIdx(parts[parts.length - 1]) };
        });
    }

    // ── Get Tablita moves in algebraic notation ──────────────────────────
    getTablitaNotation() {
        if (!this.currentTablita) return [];
        return [...this.currentTablita.moves];
    }

    // ── Get the display string for the Tablita ──────────────────────────
    getTablitaDisplay() {
        if (!this.currentTablita) return '';
        const moves = this.currentTablita.moves;
        let display = '';
        for (let i = 0; i < moves.length; i++) {
            const moveNum = Math.floor(i / 2) + 1;
            if (i % 2 === 0) {
                display += `${moveNum}. ${moves[i]}`;
            } else {
                display += ` ${moves[i]}`;
            }
        }
        return display;
    }

    // ── Get the Tablita name ────────────────────────────────────────────
    getTablitaName() {
        return this.currentTablita ? this.currentTablita.name : '';
    }

    // ── Record a game result ────────────────────────────────────────────
    // result: 'win', 'loss', 'draw'
    recordResult(result) {
        this.matchResults.push({ game: this.gameNumber, result });
    }

    // ── Advance to game 2 (swap colors) ─────────────────────────────────
    startGame2() {
        if (this.gameNumber !== 1) return false;
        this.gameNumber = 2;
        this.playerColor = -1; // Swap: player is now black
        return true;
    }

    // ── Check if the match is complete ───────────────────────────────────
    isMatchComplete() {
        return this.matchResults.length >= 2;
    }

    // ── Get the match result ─────────────────────────────────────────────
    // Returns: { playerWins, opponentWins, draws, matchResult }
    getMatchResult() {
        let playerWins = 0, opponentWins = 0, draws = 0;
        for (const r of this.matchResults) {
            if (r.result === 'win') playerWins++;
            else if (r.result === 'loss') opponentWins++;
            else draws++;
        }
        let matchResult;
        if (playerWins > opponentWins) matchResult = 'win';
        else if (playerWins < opponentWins) matchResult = 'loss';
        else matchResult = 'draw';

        // Store in history only when match is complete
        if (this.matchResults.length >= 2) {
            this.matchHistory.push({
                tablita: this.currentTablita ? this.currentTablita.name : 'Unknown',
                games: [...this.matchResults],
                result: matchResult
            });
        }

        return { playerWins, opponentWins, draws, matchResult };
    }

    // ── Reset for a new match ────────────────────────────────────────────
    reset() {
        this.currentTablita = null;
        this.gameNumber = 0;
        this.matchResults = [];
        this.playerColor = 1;
    }

    // ── Get player color for the current game ────────────────────────────
    getPlayerColor() {
        return this.playerColor;
    }

    // ── Is player playing white in this game? ────────────────────────────
    isPlayerWhite() {
        return this.playerColor === 1;
    }

    // ── Get all available Tablita names ──────────────────────────────────
    static getTablitaNames() {
        return TABLITAS.map(t => t.name);
    }

    // ── Get a specific Tablita by name ───────────────────────────────────
    static getTablitaByName(name) {
        return TABLITAS.find(t => t.name === name) || null;
    }

    // ── Get total number of Tablitas ─────────────────────────────────────
    static getCount() {
        return TABLITAS.length;
    }
}

// ═══ Position reconstruction helper ═══════════════════════════════════════

function reconstructPositionFromTablita(State, algToIdx, tablitaMoves) {
    const state = new State();
    for (const moveStr of tablitaMoves) {
        const parts = moveStr.split(/[-x]/);
        const from = algToIdx(parts[0]);
        const to = algToIdx(parts[parts.length - 1]);
        const moves = state.getMoves();
        const found = moves.find(m => m.from === from && m.to === to);
        if (!found) {
            console.warn(`Tablita move ${moveStr} is not legal in current position`);
            return null;
        }
        state.applyMove(found);
    }
    return state;
}

// ═══ Exports ══════════════════════════════════════════════════════════════

if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
        TABLITAS,
        TablitaManager,
        reconstructPositionFromTablita
    };
}
