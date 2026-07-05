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
