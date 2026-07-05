# Antes de rodar este manifest

Este manifest foi reescrito para ser reprodutível offline (exigência do Flathub).
Só falta gerar **um arquivo**, na sua máquina, com internet, antes do primeiro build:
`generated-sources.json`. Ele não vem pronto porque depende de rede para baixar
o binário do Electron (do GitHub Releases) e conferir os checksums.

Os outros dois arquivos que o `generated-sources.json` usa como base já estão
prontos e commitados neste repositório:

- `flatpak/electron-package.json` — um `package.json` mínimo, só com o `electron`
  como dependência normal (não `devDependencies`). Existe só para o build do
  Flatpak; o `package.json` real do projeto continua com `electron` em
  `devDependencies`, como o `electron-builder` exige para os builds Windows/macOS/Linux.
- `flatpak/electron-package-lock.json` — o lockfile gerado a partir do arquivo acima.

## 1. Gerar `generated-sources.json`

```bash
pipx install "git+https://github.com/flatpak/flatpak-builder-tools.git#subdirectory=node"
cd flatpak
flatpak-node-generator npm electron-package-lock.json -o generated-sources.json
```

Isso baixa e registra o tarball do `electron` (com hash), permitindo que o
`flatpak-builder` rode `npm install --offline --production` sem precisar de rede
durante o build real — é assim que o Flathub constrói de verdade.

Faça commit do `generated-sources.json` gerado.

> Se um dia você atualizar a versão do Electron no `package.json` da raiz,
> lembre de atualizar também `flatpak/electron-package.json` (mesma versão) e
> regerar `electron-package-lock.json` (`npm install --package-lock-only` dentro
> da pasta `flatpak`) antes de rodar o `flatpak-node-generator` de novo.

## 2. Ajustar a tag do source git

No arquivo `io.github.salemnopturn.DraughtsMindPro.yml`, troque:

```yaml
tag: v1.0.0
```

pela tag que você realmente publicou no GitHub (`git tag vX.Y.Z && git push origin vX.Y.Z`).

## 3. Testar sem rede

```bash
flatpak-builder --force-clean --user --install builddir io.github.salemnopturn.DraughtsMindPro.yml
flatpak run io.github.salemnopturn.DraughtsMindPro
```

Se isso funcionar com o Wi-Fi desligado, o manifest está pronto para submissão.
