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

## PDN (Portable Draughts Notation) — Ecossistema DraughtsMind Pro

A funcionalidade de importação e exportação de arquivos `.pdn` no **DraughtsMind Pro** opera em duas frentes complementares: um **mecanismo universal de importação** e um **padrão exclusivo de exportação** por coordenadas.

> [!IMPORTANT]
> A exportação do **DraughtsMind Pro** utiliza **exclusivamente a notação por coordenadas** (`a3-b4`, `d4xb2`, etc.), sendo este o único padrão oficial de exportação do projeto, garantindo interoperabilidade absoluta entre diferentes versões do próprio software sem compromisso ou suporte oficial para softwares de terceiros.
>
> Contudo, para máxima facilidade de uso, o parser interno de importação é **universal**: ele é capaz de ler e decodificar tanto a notação oficial por coordenadas quanto os formatos clássicos baseados em numeração (FMJD/CBD de 1 a 32, ex: `21-17`, `11x18`), além de remover automaticamente metadados, comentários e numerações de lances, eliminando mensagens de *tokens desconhecidos*.

### Formato de Notação (Coordenadas)

A notação padrão do projeto baseia-se puramente nas coordenadas das casas no tabuleiro (colunas de `a` a `h`, linhas de `1` a `8`):

| Tipo de Lance | Exemplo | Significado |
|---|---|---|
| Movimento Simples | `a3-b4` | Peça move da casa a3 para a casa b4 |
| Captura Simples | `d4xb2` | Peça em d4 captura peça adversária e pousa em b2 |
| Captura Múltipla | `f6xd4xb2` | Peça em f6 realiza capturas sucessivas pousando em d4 e b2 |

### Exportação

Ao clicar em **Exportar .pdn**, o software gera um arquivo com cabeçalhos padrão e a árvore de lances completa em coordenadas:

```
[Event "DraughtsMind Pro Match"]
[Site "DraughtsMind Pro v33.0.0"]
[Date "2026.07.06"]
[Round "1"]
[White "Human"]
[Black "Engine (ply 4)"]
[Result "*"]
[GameType "26"]
```

- **Variações**: São aninhadas recursivamente com parênteses, ex: `1. a3-b4 b6-a5 ( d6-c5 ) 2. b2-a3`
- **Resultados**: Inseridos ao final da partida (`2-0`, `0-2`, `1/2-1/2`, `*`) e mapeados fielmente.

### Importação

Ao **Importar .pdn** ou **Colar Sequência PDN**, o parser realiza a leitura e reconstrução exata da árvore do jogo.

- **Importação Universal**: Suporta lances descritos em coordenadas ou em numeração clássica (1 a 32). A árvore é carregada com os movimentos traduzidos e validados.
- **Validação das Regras**: Todo lance importado é validado ativamente de acordo com as regras oficiais de Damas Brasileiras (como lei da maioria, movimentos de dama de longo alcance, promoções automáticas e capturas compulsórias).
- **Tratamento de Variações**: O importador utiliza uma pilha de restauração (`restoreStack`) para processar corretamente parênteses aninhados, reordenando as ramificações de modo que a linha principal venha antes das variações secundárias.

### Funções de Implementação

O código-fonte relevante reside no módulo de importação/exportação de `renderer/scripts/app.js` e possui sua correspondente suíte de testes em `engine/test_pdn.js`. As funções centrais são:

| Função | Responsabilidade |
|---|---|
| `move2PDN` | Converte um lance interno para o formato oficial de string de coordenadas (ex: `a3-b4` ou `d4xb2`). |
| `generatePDN` | Percorre a árvore de jogo recursivamente para gerar o texto do arquivo PDN com variações. |
| `tryMatchMove` | Analisa um token importado, casando-o de forma robusta e case-insensitive tanto em formato de coordenadas quanto em formato numérico (FMJD/CBD). |
| `parsePDNTokens` | Reconstrói a árvore de nós da partida a partir dos lances lidos e variações parentetizadas. |
| `loadEBNF` | Ponto de entrada da importação: remove cabeçalhos, comentários (incluindo comentários iniciados por `;`), números e caracteres de espaçamento redundantes. |

### Testes do Ecossistema

A suíte de testes em `engine/test_pdn.js` valida todo o ciclo de vida do formato de coordenadas e a importação universal, garantindo:
- Conversão round-trip de todas as casas do tabuleiro
- Suporte a importação universal de formato numérico de 1 a 32
- Parsing correto de lances simples, capturas simples e múltiplas
- Promoção a Dama e movimentos subsequentes de longo alcance
- Reconstrução íntegra de árvores com variações aninhadas

Execute a suíte com:
```bash
node engine/test_pdn.js
```

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
