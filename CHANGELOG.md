# Changelog

## [1.0.0] - 2026-07-05

### Added
- Complete Electron application architecture
- Official Tablita mode with 39 official positions
- Tablita match tracking (2-game matches with color swapping)
- Desistir (resign) button for all game modes
- Modular engine architecture (State, Search, TT, Book, Tablita)
- Flatpak packaging configuration
- GitHub Actions CI/CD workflows (build, test, Flatpak, release)
- AppStream metadata for Flathub
- Desktop entry for Linux

### Changed
- Rebranded from "DraughtsMind Classic" to "DraughtsMind Pro"
- Separated CSS and JavaScript into external files
- Engine version upgraded to v33.0.0

### Preserved
- Original DraughtsMind Classic.html preserved as reference
- All original engine algorithms (PVS, LMR, NMP, IID, qsearch)
- All original evaluation features (material, PST, center, edge, mobility)
- All original opening book data (3100+ lines)
- All original CBD rule compliance
- All original PDN import/export functionality
- All original UI/UX design and dark theme
