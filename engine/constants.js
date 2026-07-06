"use strict";

const ENGINE_VERSION = "33.0.0";
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

module.exports = {
    ENGINE_VERSION, EMPTY, W_MAN, V_MAN, W_KING, V_KING,
    NO_CAPTURES, DIRS_ALL, DIRS_W, DIRS_B, LMP_TABLE,
    MODE_HVH, MODE_HVM, MODE_MVH, MODE_MVM, MODE_SAND,
    M64, ZS, zp, zt, getPieceIdx, PST_M, PST_K,
    CENTER_BIG, CENTER_SM
};
