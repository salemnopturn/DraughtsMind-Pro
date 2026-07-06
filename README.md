# DraughtsMind Pro

Elite Brazilian Draughts AI Engine — 100% Offline

![DraughtsMind Pro](icons/hicolor/256x256/apps/io.github.salemnopturn.DraughtsMindPro.png)

DraughtsMind Pro is a desktop application (Electron) that brings a championship-level Brazilian draughts (damas) engine to your computer, with a full opening book, official rule compliance, and dedicated modes for study, casual play, and competitive Tablita practice — all fully offline.

## Features

- **Advanced AI Engine**: Principal Variation Search (PVS) with Late Move Reductions (LMR), Null Move Pruning (NMP), Internal Iterative Deepening (IID), Aspiration Windows, and Quiescence Search
- **Zobrist Hashing**: 64-bit BigInt Zobrist hashing with a 262K-entry, 2-way clustered transposition table
- **3100+ Opening Lines**: Championship-tested opening book from Brazilian Championships, with adaptive softmax move selection
- **Full CBD Rule Compliance**: Forced capture (Art.13), majority rule, promotion only on the final square, endgame rules (Art.59/100), triple repetition draw (Art.98), 20-move draw rule, King vs King 2-move limit
- **Official Tablita Mode**: Competitive Tablita system using the 39 official openings, with match tracking and automatic color swapping between games
- **PDN Import/Export**: Full variation support, including nested parentheses
- **Real-time Analysis**: Live engine evaluation, principal variation, and move suggestions
- **Multiple Game Modes**: Human vs Human, Human vs CPU, CPU vs Human, CPU vs CPU, Sandbox (free board editor), Tablita
- **Chess Clock**: Multiple time controls, from Bullet to Classical
- **Board Editor**: Free piece placement for building and studying custom positions
- **100% Offline**: No internet connection required to play, analyze, or study

## Game Modes

| Mode | Description |
|------|-------------|
| Humano vs Humano | Two human players |
| Humano (B) vs CPU (P) | Human plays White, CPU plays Red |
| CPU (B) vs Humano (P) | CPU plays White, Human plays Red |
| CPU vs CPU | AI vs AI with statistics |
| Sandbox | Free board editor mode |
| Tablita | Official Tablita mode (2-game match) |

## Tablita Mode

The Tablita mode implements the official Brazilian draughts Tablita system:

1. A random Tablita position is selected from 39 official openings
2. The move sequence that creates the position is displayed
3. Both games use the same position
4. Colors are swapped for the second game
5. Match result: 2 wins = victory, 1-1 = draw, 2 losses = defeat

## Engine Specifications

- **Search**: Principal Variation Search (PVS) with Alpha-Beta pruning
- **Techniques**: Late Move Reductions (LMR), Null Move Pruning (NMP), Internal Iterative Deepening (IID), Aspiration Windows, Quiescence Search
- **Evaluation**: Material + Piece-Square Tables (PST) + Center Control + Edge Penalty + Mobility
- **Hashing**: Zobrist 64-bit BigInt with 262K-entry 2-way clustered transposition table
- **Opening Book**: 3100+ maximal lines from Brazilian Championships with adaptive softmax selection

## Rules Compliance

Full compliance with official Brazilian draughts rules (CBD — Confederação Brasileira de Damas):

- Forced capture (Art.13)
- Majority rule (Law of Majority)
- Promotion only on final square (not passing through)
- Endgame rules (Art.59/100)
- Triple repetition draw (Art.98)
- 20-move draw rule
- King vs King (2-move limit)

## Project Structure

```
DraughtsMind Pro/
├── main/                     # Electron main process
├── renderer/                 # Interface (HTML/CSS/JS)
│   ├── index.html
│   ├── styles/
│   └── scripts/
├── preload/                  # Secure IPC bridge
├── engine/                   # AI engine modules
│   ├── constants.js
│   ├── state.js
│   ├── search.js
│   ├── tt.js
│   ├── book.js
│   ├── tablita.js
│   └── test.js
├── books/                    # Opening books
├── rules/                    # Official rules (CBD)
├── assets/                   # Logo and icons
├── styles/                   # Shared CSS
├── scripts/                  # Auxiliary scripts
├── docs/                     # Documentation
├── build/                    # Build scripts and output
├── flatpak/                  # Flatpak configuration
├── .github/workflows/        # CI/CD workflows (build, test, release, flatpak)
├── package.json
├── electron-builder.json
├── io.github.salemnopturn.DraughtsMindPro.desktop
├── io.github.salemnopturn.DraughtsMindPro.appdata.xml
├── CHANGELOG.md
├── CONTRIBUTING.md
├── CODE_OF_CONDUCT.md
├── SECURITY.md
├── DraughtsMind Classic.html # Original reference (preserved)
└── README.md
```

## PDN (Portable Draughts Notation) — Ecossistema DraughtsMind

O formato PDN do DraughtsMind Pro utiliza a **mesma notação do DraughtsMind Classic**, garantindo interoperabilidade total entre os dois softwares. A implementação cobre importação e exportação com suporte completo a variações, capturas múltiplas e três estratégias de numeração.

### Convenção de Numeração (FMJD/CBD — Padrão)

```
  a  b  c  d  e  f  g  h
8 29 . 30 . 31 . 32 .     (linha 0 — topo interno)
7  . 25 . 26 . 27 . 28    (linha 1)
6 21 . 22 . 23 . 24 .     (linha 2)
5  . 17 . 18 . 19 . 20    (linha 3)
4 13 . 14 . 15 . 16 .     (linha 4)
3  .  9 . 10 . 11 . 12    (linha 5)
2  5 .  6 .  7 .  8 .     (linha 6)
1  .  1 .  2 .  3 .  4    (linha 7 — base)
```

- Quadrado **1** = b1 (canto inferior-esquerdo escuro, peças Vermelhas/Pretas)
- Quadrado **32** = g8 (canto superior-direito escuro, peças Brancas)
- Apenas casas **escuras** são numeradas

### Formato dos Lances

| Tipo | Exemplo | Significado |
|------|---------|-------------|
| Movimento simples | `21-17` | Peça da casa 21 move para casa 17 |
| Captura | `21x14` | Peça da casa 21 captura na casa 14 |
| Captura múltipla | `21x14x7` | Captura em cadeia: 21 → 14 → 7 |
| Notação algébrica | `c3-b4` | Movimento em notação de xadrez (fallback) |

### Exportação

O botão **Exportar** gera um arquivo `.pdn` completo com cabeçalhos padrão e a árvore de lances:

```
[Event "DraughtsMind Pro Match"]
[Site "DraughtsMind Pro vX.Y"]
[Date "2026.07.06"]
[White "Human"]
[Black "Engine (ply N)"]
[Result "2-0"]
[GameType "26"]
```

- Variações são aninhadas com parênteses: `1. 21-17 ( 12-16 ) 11-15`
- O resultado (2-0, 0-2, 1/2-1/2, \*) é inserido ao final
- Suporta salvamento via diálogo nativo (Electron), File System Access API (browsers modernos) ou fallback por download
- Compatível com o DraughtsMind Classic: arquivos exportados por um software podem ser importados pelo outro sem perda de dados

### Importação

O botão **Importar** (ou **Colar PDN**) processa arquivos `.pdn` e texto PDN com três estratégias automáticas de numeração, escolhendo a que produzir o maior número de acertos:

1. **Padrão FMJD/CBD** (1=b1, 32=g8) — usada nas exportações nativas do DraughtsMind Pro e Classic
2. **Espelhada** (`33 - num`) — compatível com fontes externas que usam numeração invertida
3. **Notação algébrica** (ex: `a3-b4`, `c5xe7`) — fallback para arquivos de outras origens

#### Tratamento de Variações

O importador utiliza uma pilha de restauração (`restoreStack`) para processar corretamente parênteses aninhados. Ao encontrar `(`, o parser volta ao nó pai para iniciar um ramo irmão (variação). Ao encontrar `)`, retorna ao ponto de restauração. Após o parsing, os filhos de cada nó são reordenados para que os lances da linha principal precedam as variações.

#### Pós-processamento

- Cabeçalhos `[Event]`, `[Site]`, `[Result]` etc. são extraídos e interpretados
- Comentários `{...}` e marcações `$N` / `?!` são removidos antes do parsing
- Resultados (`2-0`, `1/2-1/2`, `*`) são ignorados durante a leitura da árvore

### Arquitetura da Implementação

O código PDN reside em `renderer/scripts/app.js` e também possui uma suíte espelho em `engine/test_pdn.js` (132 testes, 100% aprovados). As funções principais são:

| Função | Responsabilidade |
|--------|------------------|
| `idxToNum` / `numToIdx` | Conversão entre índice interno (0-63) e numeração PDN (1-32) |
| `numToIdxAlt` | Mapeamento espelhado (`33 - num`) para compatibilidade externa |
| `move2PDN` | Formata um lance interno em string PDN (ex: `21-17` ou `21x14`) |
| `generatePDN` | Percorre a árvore de jogo e gera o texto PDN completo com variações |
| `tryMatchMove` | Tenta casar um token PDN com um lance legal no estado atual (numérico → algébrico) |
| `parsePDNTokens` | Constrói a árvore de nós a partir dos tokens, com suporte a variações aninhadas |
| `loadEBNF` | Função principal de importação: extrai cabeçalhos, limpa o texto, tenta ambas as numerações e escolhe a melhor |

### Testes

O arquivo `engine/test_pdn.js` contém 132 testes que cobrem:
- Mapeamento bidirecional de todas as 32 casas escuras (round-trip)
- Formatação de movimentos simples, capturas e capturas múltiplas
- Importação de notação numérica padrão e espelhada
- Importação de notação algébrica
- Parsing de variações com parênteses aninhados e reordenação linha principal/variação
- Cabeçalhos e extração de resultado
- Round-trip completo: texto PDN → árvore → texto PDN

Execute com:
```bash
node engine/test_pdn.js
```

### Compatibilidade

- **DraughtsMind Classic**: 100% compatível — mesmo formato de numeração e variações
- **Outros softwares**: O importador tenta automaticamente mapeamento espelhado e notação algébrica como fallback
- **Notação internacional FMJD**: Compatível quando usa a numeração padrão 1-32

## Quick Start

### Prerequisites

- Node.js 20+
- npm

### Development

```bash
npm install
npm start
```

### Build (native installers)

```bash
# Linux (AppImage, deb, rpm)
npm run build:linux

# Windows (nsis)
npm run build:win

# macOS (dmg)
npm run build:mac
```

### Flatpak

Before building, install the required runtimes/extensions from Flathub (the build will fail with `not installed` errors if these are missing):

```bash
flatpak install flathub org.freedesktop.Sdk//23.08
flatpak install flathub org.freedesktop.Platform//23.08
flatpak install flathub org.electronjs.Electron2.BaseApp//23.08
```

If Flathub isn't added as a remote yet:

```bash
flatpak remote-add --if-not-exists flathub https://flathub.org/repo/flathub.flatpakrepo
```

Install project dependencies (the build copies `node_modules`, including the bundled Electron binary, into the sandbox):

```bash
npm install
```

Then build and run:

```bash
flatpak-builder --force-clean --user --install build-dir flatpak/io.github.salemnopturn.DraughtsMindPro.yml
flatpak run io.github.salemnopturn.DraughtsMindPro
```

The Flatpak launcher wraps the bundled Electron binary via `zypak-wrapper`, which lets Electron's sandbox work correctly inside the Flatpak sandbox (falls back to `--no-sandbox` only if `zypak-wrapper` isn't available in the runtime).

## Testing

```bash
npm test
```

## Contributing

Contributions are welcome — see [CONTRIBUTING.md](CONTRIBUTING.md) and [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md).

## Security

To report a security issue, see [SECURITY.md](SECURITY.md).

## Changelog

See [CHANGELOG.md](CHANGELOG.md) for release history.

## License

GPL-3.0-or-later — see [LICENSE](LICENSE).

## Credits

- **Engine**: Based on DraughtsMind Classic by salemnopturn
- **Rules**: Confederação Brasileira de Damas (CBD)
- **Opening Books**: Brazilian Championships collections

---

🧠 **DraughtsMind Pro** — Think Deeper. Play Better.
