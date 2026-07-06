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

## PDN (Portable Draughts Notation) — DraughtsMind Pro Ecosystem

The `.pdn` file import and export functionality in **DraughtsMind Pro** operates on two complementary fronts: a **universal import mechanism** and an **exclusive coordinate-based export standard**.

> [!IMPORTANT]
> **DraughtsMind Pro**'s export uses **exclusively coordinate notation** (`a3-b4`, `d4xb2`, etc.), which is the project's sole official export standard, guaranteeing absolute interoperability between different versions of the software itself, without commitment or official support for third-party software.
>
> However, for maximum ease of use, the internal import parser is **universal**: it is capable of reading and decoding both the official coordinate notation and the classic numbering-based formats (FMJD/CBD 1 to 32, e.g. `21-17`, `11x18`), as well as automatically removing metadata, comments, and move numbering, eliminating *unknown token* messages.

### Notation Format (Coordinates)

The project's standard notation is based purely on board square coordinates (columns from `a` to `h`, rows from `1` to `8`):

| Move Type | Example | Meaning |
|---|---|---|
| Simple Move | `a3-b4` | Piece moves from square a3 to square b4 |
| Simple Capture | `d4xb2` | Piece on d4 captures an opposing piece and lands on b2 |
| Multiple Capture | `f6xd4xb2` | Piece on f6 performs successive captures, landing on d4 and b2 |

### Export

When clicking **Export .pdn**, the software generates a file with standard headers and the complete move tree in coordinates:

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

- **Custom Positions**: If the game starts from a custom position (Sandbox/Editor mode), the exported file will automatically include the `[SetUp "1"]` and `[FEN "..."]` tags containing the starting position in FEN format.
- **Variations**: Nested recursively with parentheses, e.g. `1. a3-b4 b6-a5 ( d6-c5 ) 2. b2-a3`
- **Results**: Inserted at the end of the game (`2-0`, `0-2`, `1/2-1/2`, `*`) and mapped faithfully.

### Import

When **Importing .pdn** or **Pasting a PDN Sequence**, the parser performs an exact reading and reconstruction of the game tree.

- **Universal Import**: Supports moves described in coordinates or in classic numbering (1 to 32). The tree is loaded with the moves translated and validated.
- **Starting FEN Detection**: The importer detects the presence of a `[FEN "..."]` tag in the header and initializes the board with the corresponding position before replaying the move sequence.
- **Rule Validation**: Every imported move is actively validated according to the official Brazilian Draughts rules (such as the law of majority, long-range king moves, automatic promotions, and compulsory captures).
- **Variation Handling**: The importer uses a restoration stack (`restoreStack`) to correctly process nested parentheses, reordering branches so that the main line comes before secondary variations.

### Implementation Functions

The relevant source code resides in the import/export module of `renderer/scripts/app.js`, with its corresponding test suite in `engine/test_pdn.js`. The core functions are:

| Function | Responsibility |
|---|---|
| `move2PDN` | Converts an internal move to the official coordinate string format (e.g. `a3-b4` or `d4xb2`). |
| `generatePDN` | Recursively traverses the game tree to generate the PDN file text with variations. |
| `tryMatchMove` | Parses an imported token, robustly matching it case-insensitively in both coordinate format and numeric (FMJD/CBD) format. |
| `parsePDNTokens` | Reconstructs the game's node tree from the moves read and parenthesized variations. |
| `loadEBNF` | Import entry point: removes headers, comments (including comments starting with `;`), numbers, and redundant spacing characters. |

### Ecosystem Tests

The test suite in `engine/test_pdn.js` validates the entire lifecycle of the coordinate format and universal import, ensuring:
- Round-trip conversion of all board squares
- Support for universal import of numeric format 1 to 32
- Correct parsing of simple moves, simple captures, and multiple captures
- Promotion to King and subsequent long-range moves
- Faithful reconstruction of trees with nested variations

Run the suite with:
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
