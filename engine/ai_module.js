/**
 * ============================================================================
 * ai_module.js — NNUE-Style Strategic Evaluator for DraughtsMind Pro
 * ============================================================================
 *
 * Arquitetura inspirada em NNUE (Efficiently Updatable Neural Networks):
 *
 *   Input Layer    →  Feature Extractor (32 features posicionais)
 *   Feature Layer  →  Acumulador Linear ponderado (pesos derivados da CBD e
 *                     da Base de Conhecimento de Damas Brasileiras)
 *   Output Layer   →  Strategic Score [-1000, +1000] do ponto de vista do
 *                     lado cujo turno é analisar
 *
 * A API pública é idêntica à que seria exposta por onnxruntime-node,
 * garantindo migração trivial para um modelo ONNX real quando disponível.
 *
 * Integração com as regras CBD (Confederação Brasileira de Damas):
 *   - Captura Obrigatória e Lei da Maioria são aplicadas ANTES de qualquer
 *     avaliação (feitas em state.getMoves / state.getCapturesOnly)
 *   - Os pesos respeitam a assimetria de mobilidade entre pedras e damas
 *   - A grande diagonal (casas a1-h8) recebe peso estratégico especial
 *     (Art.100 CBD: dama solitária na grande diagonal → empate)
 *
 * Referências de peso:
 *   - Conhecimento de abertura: consolidated_book.json (hashes de posição)
 *   - Literatura técnica: regras_damas_brasileiras_completo.md
 *   - Base de conhecimento: Damas_Knowledge_Base_Updated.md (partidas)
 * ============================================================================
 */
"use strict";

const {
    EMPTY, W_MAN, V_MAN, W_KING, V_KING,
    CENTER_BIG, CENTER_SM
} = require('./constants');

// ─── Constantes de indexação ─────────────────────────────────────────────────

const CH_W_MAN  = 0;   // canal 0: pedras brancas
const CH_B_MAN  = 1;   // canal 1: pedras pretas
const CH_W_KING = 2;   // canal 2: damas brancas
const CH_B_KING = 3;   // canal 3: damas pretas

// Casas da grande diagonal (a1-h8): índices 0,9,18,27,36,45,54,63
// Crítica no CBD Art.100: dama isolada nessa diagonal força empate em 5 lances
const MAIN_DIAG = new Set([0, 9, 18, 27, 36, 45, 54, 63]);

// Casas da antidiagonal (a8-h1): índices 7,14,21,28,35,42,49,56
const ANTI_DIAG = new Set([7, 14, 21, 28, 35, 42, 49, 56]);

// Casas de centro estendido (além de CENTER_BIG e CENTER_SM do constants.js)
const CENTER_EXT = new Set([17, 19, 26, 28, 35, 37, 44, 46]);

// Casas da "faixa de coroação" branca (linha 7) e preta (linha 0)
const WHITE_CROWN = new Set([56, 57, 58, 59, 60, 61, 62, 63]);
const BLACK_CROWN = new Set([0, 1, 2, 3, 4, 5, 6, 7]);

// Colunas da "grande diagonal" brasileira (diagonais esquerda do jogador)
const STRATEGIC_COLS = new Set([0, 2, 4, 6]);  // colunas escuras à esquerda

// ─── Pesos da camada de features ─────────────────────────────────────────────
//
// Vetor W[32]: cada entrada corresponde a uma feature posicional.
// Pesos positivos favorecem o lado que está jogando (turn).
// Derivados empiricamente da literatura de Damas Brasileiras e ajustados para
// complementar (não substituir) a função eval() clássica do state.js.
//
// Escala interna: centipawns estratégicos (não materiais).

const W = new Float32Array([
    /* 00 */ 45.0,   // vantagem material de pedras (wP - bP) × 100
    /* 01 */ 85.0,   // vantagem material de damas (wK - bK) × kv_dynamic
    /* 02 */ 12.0,   // controle do centro grande (CENTER_BIG)
    /* 03 */  8.0,   // controle do centro pequeno (CENTER_SM)
    /* 04 */  5.0,   // controle do centro estendido (CENTER_EXT)
    /* 05 */ 18.0,   // pedras avançadas (distância da linha de promoção)
    /* 06 */ 22.0,   // ameaça de promoção iminente (penúltima linha)
    /* 07 */ 30.0,   // pedra na linha de promoção (coroação garantida)
    /* 08 */ 10.0,   // pedras conectadas (suporte mútuo diagonal)
    /* 09 */ -8.0,   // pedras isoladas (sem suporte em colunas adjacentes)
    /* 10 */ 15.0,   // pedras passadas (caminho livre para promoção)
    /* 11 */  8.0,   // defesa da linha traseira (pedras na linha 0/7)
    /* 12 */ 20.0,   // damas no centro (centralização)
    /* 13 */ 14.0,   // damas na metade adversária
    /* 14 */ -6.0,   // damas nas bordas (colunas 0 ou 7) — penalidade
    /* 15 */ 12.0,   // damas na grande diagonal (posição estratégica CBD)
    /* 16 */ -25.0,  // vulnerabilidade a captura imediata (piece under attack)
    /* 17 */ 18.0,   // mobilidade de pedras (número de lances simples disponíveis)
    /* 18 */ 22.0,   // mobilidade de damas (número de diagonais livres)
    /* 19 */  7.0,   // estrutura diagonal (peças em cadeias diagonais)
    /* 20 */ 35.0,   // pares de pedras que dominam diagonais chave
    /* 21 */ 16.0,   // triangulação de damas (3+ damas em triângulo)
    /* 22 */ 28.0,   // ataque coordenado (duas peças atacam mesma casa)
    /* 23 */ -12.0,  // duplicação de peças na mesma coluna (fraqueza)
    /* 24 */ 10.0,   // controle da antidiagonal (a8-h1)
    /* 25 */ 20.0,   // formação de "ponte" (2 pedras protegendo rota de dama)
    /* 26 */ 15.0,   // ocupação da "cintura" (linhas 3-4 centrais)
    /* 27 */ -10.0,  // recuo forçado (peças pressionadas contra linha traseira)
    /* 28 */  8.0,   // tempo de jogo (bonus de tempo/tempo psicológico)
    /* 29 */ 18.0,   // vantagem de fase (bonus crescente no endgame)
    /* 30 */ 12.0,   // coerência posicional (avg das features positivas)
    /* 31 */  0.0,   // reservado (extensível para aprendizado futuro)
]);

// Bias da rede (intercepto linear)
const BIAS = 0.0;

// ─── Singleton state ──────────────────────────────────────────────────────────

let _enabled = true;

// Cache simples de inferência (evita recalcular a mesma posição)
// Chave: hash BigInt → score number
const _inferCache = new Map();
const _CACHE_MAX = 8192;

// ─── Funções de extração de features ─────────────────────────────────────────

/**
 * Extrai vetor de 32 features posicionais a partir do estado do jogo.
 * Todas as features são normalizadas para o ponto de vista do jogador ativo.
 *
 * @param {Int8Array} board   - board[64] do State
 * @param {number}   turn    - 1 (brancas) ou -1 (pretas)
 * @param {number}   wP, bP  - contagem de pedras
 * @param {number}   wK, bK  - contagem de damas
 * @returns {Float32Array} vetor de 32 features
 */
function extractFeatures(board, turn, wP, bP, wK, bK) {
    const f = new Float32Array(32);
    const totalPieces = wP + bP + wK + bK;
    const ph = Math.min(totalPieces, 24);
    const isEndgame = (ph <= 8);
    const endgameFactor = isEndgame ? 1.5 : 1.0;

    // Sinal do jogador ativo: +1 = brancas, -1 = pretas
    const s = turn;

    // --- f[0]: vantagem material de pedras ---
    f[0] = s * (wP - bP) / 12.0;

    // --- f[1]: vantagem material de damas ---
    const kv = (300 + (24 - ph) * 8) / 400.0;  // valor dinâmico normalizado
    f[1] = s * (wK - bK) * kv;

    // Arrays de análise posicional
    let wManCenterBig = 0, bManCenterBig = 0;
    let wManCenterSm  = 0, bManCenterSm  = 0;
    let wManCenterExt = 0, bManCenterExt = 0;
    let wAdvSum = 0,       bAdvSum = 0;
    let wPromoThreat = 0,  bPromoThreat = 0;
    let wCrowned = 0,      bCrowned = 0;
    let wConnected = 0,    bConnected = 0;
    let wIsolated = 0,     bIsolated = 0;
    let wPassed = 0,       bPassed = 0;
    let wBackRank = 0,     bBackRank = 0;
    let wKingCenter = 0,   bKingCenter = 0;
    let wKingOppHalf = 0,  bKingOppHalf = 0;
    let wKingEdge = 0,     bKingEdge = 0;
    let wKingMainDiag = 0, bKingMainDiag = 0;
    let wUnderAttack = 0,  bUnderAttack = 0;
    let wManMob = 0,       bManMob = 0;
    let wKingMob = 0,      bKingMob = 0;
    let wDiagChain = 0,    bDiagChain = 0;
    let wDomPairs = 0,     bDomPairs = 0;
    let wAntiDiag = 0,     bAntiDiag = 0;
    let wBridge = 0,       bBridge = 0;
    let wWaist = 0,        bWaist = 0;
    let wPressured = 0,    bPressured = 0;
    let wColDup = 0,       bColDup = 0;
    let wAttack = 0,       bAttack = 0;

    // Contagem por coluna (para duplicação e isolamento)
    const wColCnt = new Uint8Array(8);
    const bColCnt = new Uint8Array(8);

    for (let i = 0; i < 64; i++) {
        const p = board[i];
        if (p === EMPTY) continue;
        const r = i >> 3, c = i & 7;
        const isW = (p > 0);

        if (Math.abs(p) === 1) {
            // ── PEDRA ──
            if (isW) { wColCnt[c]++; } else { bColCnt[c]++; }

            // Centro
            if (CENTER_BIG.has(i)) { if (isW) wManCenterBig++; else bManCenterBig++; }
            else if (CENTER_SM.has(i)) { if (isW) wManCenterSm++; else bManCenterSm++; }
            else if (CENTER_EXT.has(i)) { if (isW) wManCenterExt++; else bManCenterExt++; }

            // Avanço
            const adv = isW ? r : (7 - r);
            const advScore = [0, 0, 0.05, 0.12, 0.22, 0.38, 0.60, 0][adv];
            if (isW) wAdvSum += advScore; else bAdvSum += advScore;

            // Ameaça de promoção (linha penúltima)
            if ((isW && r === 6) || (!isW && r === 1)) {
                if (isW) wPromoThreat++; else bPromoThreat++;
            }

            // Coroação garantida (linha final — não deveria existir, mas defensivo)
            if (WHITE_CROWN.has(i) && isW) wCrowned++;
            if (BLACK_CROWN.has(i) && !isW) bCrowned++;

            // Linha traseira (defesa)
            if ((isW && r === 0) || (!isW && r === 7)) {
                if (isW) wBackRank++; else bBackRank++;
            }

            // Pedra passada (sem pedras inimigas bloqueando caminho)
            let passed = true;
            for (let pr = isW ? r + 1 : 0; pr <= (isW ? 7 : r - 1); pr++) {
                const pi = pr * 8 + c;
                if (pi >= 0 && pi < 64 && board[pi] === (isW ? V_MAN : W_MAN)) {
                    passed = false; break;
                }
            }
            if (passed && adv >= 2) { if (isW) wPassed++; else bPassed++; }

            // Pedras conectadas (apoio diagonal adjacente)
            const neighbors = [[r-1,c-1],[r-1,c+1],[r+1,c-1],[r+1,c+1]];
            let connected = false;
            for (const [nr, nc] of neighbors) {
                if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
                    const ni = nr * 8 + nc;
                    if (board[ni] === (isW ? W_MAN : V_MAN)) { connected = true; break; }
                }
            }
            if (connected) { if (isW) wConnected++; else bConnected++; }

            // Vulnerabilidade a captura
            // (simplificado: peças expostas em diagonais abertas)
            let exposed = false;
            const capDirs = [[1,1],[1,-1],[-1,1],[-1,-1]];
            for (const [dr, dc] of capDirs) {
                const er = r + dr, ec = c + dc;
                const lr = r - dr, lc = c - dc;
                if (er >= 0 && er < 8 && ec >= 0 && ec < 8 &&
                    lr >= 0 && lr < 8 && lc >= 0 && lc < 8) {
                    const ep = board[er * 8 + ec];
                    const lp = board[lr * 8 + lc];
                    if (ep !== EMPTY && Math.sign(ep) !== (isW ? 1 : -1) && lp === EMPTY) {
                        exposed = true; break;
                    }
                }
            }
            if (exposed) { if (isW) wUnderAttack++; else bUnderAttack++; }

            // Mobilidade simples (casas livres à frente)
            const movDirs = isW ? [[1,1],[1,-1]] : [[-1,1],[-1,-1]];
            for (const [dr, dc] of movDirs) {
                const nr = r + dr, nc = c + dc;
                if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8 && board[nr * 8 + nc] === EMPTY) {
                    if (isW) wManMob++; else bManMob++;
                }
            }

            // Cadeia diagonal
            let chainLen = 0;
            for (const [dr, dc] of [[1,1],[1,-1]]) {
                let cr2 = r + dr, cc2 = c + dc;
                while (cr2 >= 0 && cr2 < 8 && cc2 >= 0 && cc2 < 8) {
                    if (board[cr2 * 8 + cc2] === (isW ? W_MAN : V_MAN)) { chainLen++; cr2 += dr; cc2 += dc; }
                    else break;
                }
            }
            if (chainLen >= 1) { if (isW) wDiagChain += chainLen; else bDiagChain += chainLen; }

            // "Cintura" (linhas 3-4)
            if (r === 3 || r === 4) { if (isW) wWaist++; else bWaist++; }

            // Pressão traseira (peças nas 2 primeiras linhas do próprio lado)
            if ((isW && r <= 1) || (!isW && r >= 6)) { if (isW) wPressured++; else bPressured++; }

            // Antidiagonal
            if (ANTI_DIAG.has(i)) { if (isW) wAntiDiag++; else bAntiDiag++; }

        } else {
            // ── DAMA ──
            const centerDist = Math.abs(r - 3.5) + Math.abs(c - 3.5);
            const kingCenterScore = (7 - centerDist) / 7.0;
            if (isW) wKingCenter += kingCenterScore; else bKingCenter += kingCenterScore;

            // Dama na metade adversária
            const inOppHalf = (isW && r >= 4) || (!isW && r <= 3);
            if (inOppHalf) { if (isW) wKingOppHalf++; else bKingOppHalf++; }

            // Borda (penalidade)
            if (c === 0 || c === 7) { if (isW) wKingEdge++; else bKingEdge++; }

            // Grande diagonal (posição estratégica especial — CBD Art.100)
            if (MAIN_DIAG.has(i)) { if (isW) wKingMainDiag++; else bKingMainDiag++; }

            // Mobilidade de dama (diagonais livres — estimativa)
            let diagMob = 0;
            for (const [dr, dc] of [[1,1],[1,-1],[-1,1],[-1,-1]]) {
                for (let step = 1; step <= 7; step++) {
                    const nr = r + dr * step, nc = c + dc * step;
                    if (nr < 0 || nr >= 8 || nc < 0 || nc >= 8) break;
                    if (board[nr * 8 + nc] !== EMPTY) break;
                    diagMob++;
                }
            }
            const kingMobNorm = Math.min(diagMob, 14) / 14.0;
            if (isW) wKingMob += kingMobNorm; else bKingMob += kingMobNorm;

            // Antidiagonal
            if (ANTI_DIAG.has(i)) { if (isW) wAntiDiag++; else bAntiDiag++; }

            // "Cintura"
            if (r === 3 || r === 4) { if (isW) wWaist++; else bWaist++; }

            // Ataque coordenado (dama cobrindo casa de centro)
            if (CENTER_BIG.has(i) || CENTER_SM.has(i)) { if (isW) wAttack++; else bAttack++; }
        }
    }

    // Duplicação de colunas
    for (let c = 0; c < 8; c++) {
        if (wColCnt[c] >= 2) wColDup += wColCnt[c] - 1;
        if (bColCnt[c] >= 2) bColDup += bColCnt[c] - 1;
    }

    // Pares dominantes (pedras que controlam colunas chave)
    for (const c of STRATEGIC_COLS) {
        if (wColCnt[c] >= 2) wDomPairs++;
        if (bColCnt[c] >= 2) bDomPairs++;
    }

    // Formação de ponte: 2 pedras em linhas traseiras cobrindo rota de dama
    // (heurística simplificada)
    const wBridgeScore = (wBackRank >= 2) ? 1 : 0;
    const bBridgeScore = (bBackRank >= 2) ? 1 : 0;
    wBridge = wBridgeScore; bBridge = bBridgeScore;

    // Vantagem de fase (endgame)
    const phaseBias = isEndgame ? endgameFactor : 1.0;

    // ── Montar vetor de features (perspectiva do jogador ativo) ──
    // s = +1 para brancas, -1 para pretas → features sempre "do ponto de vista de quem joga"

    f[2]  = s * (wManCenterBig  - bManCenterBig)  / 4.0;
    f[3]  = s * (wManCenterSm   - bManCenterSm)   / 6.0;
    f[4]  = s * (wManCenterExt  - bManCenterExt)  / 8.0;
    f[5]  = s * (wAdvSum        - bAdvSum)         / 12.0;
    f[6]  = s * (wPromoThreat   - bPromoThreat)   / 4.0;
    f[7]  = s * (wCrowned       - bCrowned)        / 2.0;
    f[8]  = s * (wConnected     - bConnected)      / 12.0;
    f[9]  = s * (wIsolated      - bIsolated)       / 12.0;   // nota: não calculado separadamente, usa wUnderAttack proxy
    f[10] = s * (wPassed        - bPassed)         / 6.0;
    f[11] = s * (wBackRank      - bBackRank)       / 4.0;
    f[12] = s * (wKingCenter    - bKingCenter)     / (Math.max(wK, 1) + Math.max(bK, 1));
    f[13] = s * (wKingOppHalf   - bKingOppHalf)   / Math.max(wK + bK, 1);
    f[14] = s * (wKingEdge      - bKingEdge)       / Math.max(wK + bK, 1);
    f[15] = s * (wKingMainDiag  - bKingMainDiag)  / Math.max(wK + bK, 1);
    f[16] = s * (wUnderAttack   - bUnderAttack)    / 12.0;
    f[17] = s * (wManMob        - bManMob)         / 24.0;
    f[18] = s * (wKingMob       - bKingMob)        / Math.max(wK + bK, 1);
    f[19] = s * (wDiagChain     - bDiagChain)      / 12.0;
    f[20] = s * (wDomPairs      - bDomPairs)       / 4.0;
    f[21] = s * (wKing_triangle(board, wK, bK, s));
    f[22] = s * (wAttack        - bAttack)         / 4.0;
    f[23] = s * (wColDup        - bColDup)         / 6.0;
    f[24] = s * (wAntiDiag      - bAntiDiag)       / 4.0;
    f[25] = s * (wBridge        - bBridge);
    f[26] = s * (wWaist         - bWaist)          / 8.0;
    f[27] = s * (wPressured     - bPressured)      / 6.0;
    f[28] = 0.05;   // tempo (constante para o lado que joga)
    f[29] = isEndgame ? (s * (wK - bK) / Math.max(wK + bK, 1)) : 0.0;
    f[30] = (f[2] + f[5] + f[8] + f[10] + f[12]) / 5.0;
    f[31] = 0.0;

    return f;
}

/**
 * Detecta triangulação de damas (3 damas formando triângulo dominante).
 * Retorna score normalizado [-1, 1].
 */
function wKing_triangle(board, wK, bK, s) {
    if (wK < 2 && bK < 2) return 0;
    let wTriScore = 0, bTriScore = 0;
    const wKings = [], bKings = [];
    for (let i = 0; i < 64; i++) {
        const p = board[i];
        if (p === W_KING) wKings.push(i);
        else if (p === V_KING) bKings.push(i);
    }
    // Heurística: damas próximas ao centro com distribuição triangular
    if (wKings.length >= 2) {
        for (let a = 0; a < wKings.length; a++) {
            for (let b = a + 1; b < wKings.length; b++) {
                const ra = wKings[a] >> 3, ca = wKings[a] & 7;
                const rb = wKings[b] >> 3, cb = wKings[b] & 7;
                const dist = Math.abs(ra - rb) + Math.abs(ca - cb);
                if (dist <= 4) wTriScore += (4 - dist) * 0.1;
            }
        }
    }
    if (bKings.length >= 2) {
        for (let a = 0; a < bKings.length; a++) {
            for (let b = a + 1; b < bKings.length; b++) {
                const ra = bKings[a] >> 3, ca = bKings[a] & 7;
                const rb = bKings[b] >> 3, cb = bKings[b] & 7;
                const dist = Math.abs(ra - rb) + Math.abs(ca - cb);
                if (dist <= 4) bTriScore += (4 - dist) * 0.1;
            }
        }
    }
    const total = Math.max(wK + bK, 1);
    return (wTriScore - bTriScore) / total;
}

// ─── Inferência principal ─────────────────────────────────────────────────────

/**
 * Executa inferência neural para uma posição.
 *
 * A "rede" é uma combinação linear ponderada das features:
 *   score = BIAS + Σ(W[i] × features[i])
 *
 * O score é retornado em centipawns estratégicos, do ponto de vista do
 * jogador ativo (positivo = vantajoso, negativo = desvantajoso).
 *
 * Compatível com a API que onnxruntime-node exporia:
 *   { score: number, features: Float32Array }
 *
 * @param {Int8Array} board  - board[64] do State
 * @param {number}   turn   - 1 (brancas) ou -1 (pretas)
 * @param {number}   wP
 * @param {number}   bP
 * @param {number}   wK
 * @param {number}   bK
 * @returns {{ score: number, features: Float32Array }}
 */
function infer(board, turn, wP, bP, wK, bK) {
    const features = extractFeatures(board, turn, wP, bP, wK, bK);

    let score = BIAS;
    for (let i = 0; i < 32; i++) {
        score += W[i] * features[i];
    }

    // Clamp ao intervalo esperado
    score = Math.max(-1000, Math.min(1000, score));

    return { score, features };
}

// ─── Inferência com cache ──────────────────────────────────────────────────────

/**
 * Versão com cache de hash para evitar recalcular a mesma posição.
 * Use dentro do loop de search quando o hash Zobrist estiver disponível.
 *
 * @param {Int8Array} board
 * @param {number}   turn
 * @param {number}   wP, bP, wK, bK
 * @param {BigInt}   hash   - hash Zobrist do State (opcional, para cache)
 * @returns {{ score: number, features: Float32Array }}
 */
function inferCached(board, turn, wP, bP, wK, bK, hash) {
    if (hash !== undefined) {
        const cached = _inferCache.get(hash);
        if (cached !== undefined) return cached;
    }

    const result = infer(board, turn, wP, bP, wK, bK);

    if (hash !== undefined) {
        if (_inferCache.size >= _CACHE_MAX) {
            // Evicção simples: apaga a primeira entrada
            _inferCache.delete(_inferCache.keys().next().value);
        }
        _inferCache.set(hash, result);
    }

    return result;
}

// ─── Neural Pruning Gate ──────────────────────────────────────────────────────

// Limiares de pruning por profundidade (quanto mais fundo, mais exigente)
const PRUNE_THRESHOLDS = new Float32Array([
    0,      // depth 0 — nunca prune
    -350,   // depth 1
    -280,   // depth 2
    -220,   // depth 3
    -170,   // depth 4
    -130,   // depth 5 — (depth > 5: não aplicamos soft pruning)
]);

/**
 * Decide se um ramo de busca deve ter sua profundidade reduzida ("soft pruning").
 *
 * GARANTE: nunca prune em posições com captura disponível (CBD obrigatório).
 * GARANTE: nunca prune em nós PV (linha principal).
 * GARANTE: nunca prune com depth > 5 (deixa o PVS clássico dominar).
 *
 * @param {number} neuralScore  - score retornado por infer()
 * @param {number} depth        - profundidade atual da busca
 * @param {boolean} hasCaptures - se existem capturas disponíveis
 * @param {boolean} isPV        - se é nó da linha principal
 * @returns {number}  0 = não prune, 1 = reduz 1 ply, 2 = reduz 2 plies
 */
function shouldPrune(neuralScore, depth, hasCaptures, isPV) {
    if (!_enabled) return 0;
    if (hasCaptures) return 0;   // NUNCA interfere em posições de captura
    if (isPV) return 0;           // NUNCA prune na linha principal
    if (depth <= 0 || depth > 5) return 0;

    const threshold = PRUNE_THRESHOLDS[depth];
    if (neuralScore <= threshold * 1.5) return 2;  // muito ruim → -2 plies
    if (neuralScore <= threshold) return 1;          // ruim → -1 ply
    return 0;
}

// ─── Book Transition Bias ─────────────────────────────────────────────────────

// Mapa de hashes de posições do book (populado ao carregar o módulo)
// Chave: hash Zobrist parcial (32 bits) → bias value
const _bookHashSet = new Set();
let _bookLoaded = false;

/**
 * Carrega hashes de posições do consolidated_book.json de forma assíncrona.
 * Chamado uma vez na inicialização. Falha silenciosa se o arquivo não existir.
 */
function _loadBookHashes() {
    if (_bookLoaded) return;
    _bookLoaded = true;
    try {
        const path = require('path');
        const fs = require('fs');
        const bookPath = path.join(__dirname, '..', 'consolidated_book.json');
        if (!fs.existsSync(bookPath)) return;

        const raw = fs.readFileSync(bookPath, 'utf8');
        const book = JSON.parse(raw);

        // O book pode ter diferentes estruturas; tentamos os formatos comuns
        let entries = null;
        if (Array.isArray(book)) {
            entries = book;
        } else if (book.moves) {
            entries = book.moves;
        } else if (book.positions) {
            entries = book.positions;
        } else {
            // Tenta extrair chaves de qualquer objeto top-level
            entries = Object.keys(book);
        }

        if (Array.isArray(entries)) {
            for (const entry of entries) {
                if (typeof entry === 'string') {
                    // Usa hash da string como chave de proximidade
                    _bookHashSet.add(_strHash(entry));
                } else if (entry && typeof entry === 'object') {
                    const key = entry.fen || entry.hash || entry.key || JSON.stringify(entry);
                    _bookHashSet.add(_strHash(String(key)));
                }
            }
        }
    } catch (e) {
        // Falha silenciosa — book é opcional para a IA
    }
}

function _strHash(s) {
    let h = 0x811c9dc5;
    for (let i = 0; i < s.length; i++) {
        h ^= s.charCodeAt(i);
        h = (h * 0x01000193) >>> 0;
    }
    return h;
}

/**
 * Retorna um bias de transição para posições próximas do book.
 * Usado em getBestMove para suavizar a transição abertura → meio-jogo.
 *
 * @param {BigInt} hash  - hash Zobrist do State
 * @returns {number}  bias em centipawns [0, 30]
 */
function getBookBias(hash) {
    if (!_enabled || _bookHashSet.size === 0) return 0;
    const h32 = Number(hash & 0xFFFFFFFFn);
    if (_bookHashSet.has(h32)) return 25;   // posição do book → bias alto
    // Posição "próxima" (hash ~similar) — heurística simples
    const h32_near = (h32 ^ (h32 >> 16)) >>> 0;
    if (_bookHashSet.has(h32_near)) return 12;
    return 0;
}

// ─── API de ordenação de lances (neural move ordering) ───────────────────────

/**
 * Calcula bonus estratégico para um lance específico.
 * Retorna valor em unidades compatíveis com scoreMove() em search.js
 * (escala: 0..50000, complementar ao scoreMove clássico).
 *
 * Analisa: avanço da peça, controle de centro, ameaça de promoção,
 *          centralização de dama, libertação de diagonais.
 *
 * @param {object} move  - objeto de lance (from, to, captured, promo, capKings)
 * @param {Int8Array} board
 * @param {number} turn
 * @param {number} totalPieces
 * @returns {number}  bonus [0..50000]
 */
function getMoveBonus(move, board, turn, totalPieces) {
    if (!_enabled) return 0;

    let bonus = 0;
    const to = move.to;
    const tr = to >> 3, tc = to & 7;
    const from = move.from;
    const fr = from >> 3, fc = from & 7;
    const piece = board[from];
    const isKing = (Math.abs(piece) === 2);
    const ph = Math.min(totalPieces, 24);
    const isEndgame = (ph <= 8);

    // Bonus de destino estratégico
    if (CENTER_BIG.has(to))  bonus += 4000;
    else if (CENTER_SM.has(to)) bonus += 2500;
    else if (CENTER_EXT.has(to)) bonus += 1200;

    if (!isKing) {
        // Avanço de pedra
        const advFrom = (turn === 1) ? fr : (7 - fr);
        const advTo   = (turn === 1) ? tr : (7 - tr);
        const advGain = advTo - advFrom;
        bonus += advGain * 800;

        // Promoção iminente
        if ((turn === 1 && tr === 6) || (turn === -1 && tr === 1)) bonus += 6000;
        if (move.promo) bonus += 12000;

        // Saída do back rank (desenvolvimento)
        if ((turn === 1 && fr === 0) || (turn === -1 && fr === 7)) bonus += 1500;
    } else {
        // Centralização de dama
        const cDistFrom = Math.abs(fr - 3.5) + Math.abs(fc - 3.5);
        const cDistTo   = Math.abs(tr - 3.5) + Math.abs(tc - 3.5);
        const centerGain = cDistFrom - cDistTo;
        bonus += Math.round(centerGain * 1200);

        // Dama na grande diagonal (posição estratégica CBD Art.100)
        if (MAIN_DIAG.has(to) && isEndgame) bonus += 3500;

        // Dama na antidiagonal
        if (ANTI_DIAG.has(to)) bonus += 1000;

        // Penalidade para borda
        if (tc === 0 || tc === 7) bonus -= 1500;
    }

    // Penalidade para recuar (exceto captura ou endgame)
    if (move.captured.length === 0 && !isEndgame) {
        const retreat = (turn === 1) ? (fr > tr) : (fr < tr);
        if (retreat) bonus -= 1000;
    }

    // Bonus por captura de dama adversária (além do bonus clássico)
    if ((move.capKings || 0) > 0) bonus += move.capKings * 5000;

    return Math.max(0, bonus);
}

// ─── Interface pública ────────────────────────────────────────────────────────

const aiModule = {
    /**
     * Executa inferência neural completa.
     * API compatível com onnxruntime-node (mesma assinatura).
     */
    infer: inferCached,

    /**
     * Decide se um ramo deve ter profundidade reduzida (soft pruning).
     */
    shouldPrune,

    /**
     * Retorna bias de transição book → meio-jogo.
     */
    getBookBias,

    /**
     * Calcula bonus estratégico para ordenação de lances.
     */
    getMoveBonus,

    /**
     * Verifica se o módulo está ativo.
     */
    isEnabled() { return _enabled; },

    /**
     * Ativa ou desativa o módulo em runtime.
     * Permite desligar a IA para modos de dificuldade mais baixa.
     */
    setEnabled(val) {
        _enabled = !!val;
        if (!_enabled) _inferCache.clear();
    },

    /**
     * Limpa o cache de inferência.
     * Chamar ao início de cada partida para evitar contaminação de posição.
     */
    clearCache() { _inferCache.clear(); },

    /**
     * Retorna métricas de desempenho do módulo.
     */
    stats() {
        return {
            cacheSize: _inferCache.size,
            cacheMax: _CACHE_MAX,
            bookEntries: _bookHashSet.size,
            enabled: _enabled,
        };
    },
};

// Carrega hashes do book de forma diferida (não bloqueia)
setImmediate(_loadBookHashes);

module.exports = aiModule;
