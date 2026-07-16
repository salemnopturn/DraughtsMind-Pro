"use strict";

const ENGINE_VERSION = "34.0.0";
const EMPTY = 0, W_MAN = 1, V_MAN = -1, W_KING = 2, V_KING = -2;
const NO_CAPTURES = [];
const DIRS_ALL = [[1,1],[1,-1],[-1,1],[-1,-1]];
const DIRS_W = [[1,1],[1,-1]];
const DIRS_B = [[-1,1],[-1,-1]];
const LMP_TABLE = [0, 5, 9, 15, 22, 30];
const MODE_HVH = 0, MODE_HVM = 1, MODE_MVH = 2, MODE_MVM = 3, MODE_SAND = 4;

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

// Piece-Square Tables for White (flip for Black via 63-i)
// Row 0 = rank 1 (white back rank), Row 7 = rank 8 (black back rank)
// Man PST: encourages advancement, central control, and avoids edges
const PST_M = [
    // Row 0 (back rank) — moderate value, defensive
     0,  5,  0,  8,  8,  0,  5,  0,
    // Row 1 — start of development
     5, 10,  5, 12, 12,  5, 10,  5,
    // Row 2 — early midgame
     8, 15, 12, 20, 20, 12, 15,  8,
    // Row 3 — center control zone
    10, 18, 15, 25, 25, 15, 18, 10,
    // Row 4 — advanced zone
    15, 22, 20, 30, 30, 20, 22, 15,
    // Row 5 — promotion threat zone
    20, 28, 25, 38, 38, 25, 28, 20,
    // Row 6 — one step from promotion
    25, 35, 30, 45, 45, 30, 35, 25,
    // Row 7 — promotion rank (pawn becomes king)
     0,  0,  0,  0,  0,  0,  0,  0,
];

// King PST: centralization is key, especially in endgames
const PST_K = [
    // Row 0
     5,  5,  5,  5,  5,  5,  5,  5,
    // Row 1
     5, 10, 10, 12, 12, 10, 10,  5,
    // Row 2
     5, 12, 16, 18, 18, 16, 12,  5,
    // Row 3
     5, 14, 18, 22, 22, 18, 14,  5,
    // Row 4
     5, 14, 18, 22, 22, 18, 14,  5,
    // Row 5
     5, 12, 16, 18, 18, 16, 12,  5,
    // Row 6
     5, 10, 10, 12, 12, 10, 10,  5,
    // Row 7
     5,  5,  5,  5,  5,  5,  5,  5,
];
const CENTER_BIG = new Set([27, 36, 34, 29]);
const CENTER_SM  = new Set([18, 20, 25, 38, 43, 45]);

module.exports = {
    ENGINE_VERSION, EMPTY, W_MAN, V_MAN, W_KING, V_KING,
    NO_CAPTURES, DIRS_ALL, DIRS_W, DIRS_B, LMP_TABLE,
    MODE_HVH, MODE_HVM, MODE_MVH, MODE_MVM, MODE_SAND,
    M64, ZS, zp, zt, getPieceIdx, PST_M, PST_K,
    CENTER_BIG, CENTER_SM
};
