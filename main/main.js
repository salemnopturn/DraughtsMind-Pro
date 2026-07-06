const { app, BrowserWindow, ipcMain, dialog } = require('electron');
const path = require('path');

let mainWindow;

function createWindow() {
    mainWindow = new BrowserWindow({
        width: 1400,
        height: 900,
        minWidth: 900,
        minHeight: 600,
        title: 'DraughtsMind Pro',
        icon: path.join(__dirname, '..', 'icons', 'hicolor', '512x512', 'apps', 'io.github.salemnopturn.DraughtsMindPro.png'),
        webPreferences: {
            preload: path.join(__dirname, '..', 'preload', 'preload.js'),
            contextIsolation: true,
            nodeIntegration: false,
            sandbox: false
        },
        backgroundColor: '#0c0d11',
        show: false
    });

    mainWindow.webContents.on("console-message", (event, level, message, line, sourceId) => {
        console.log(`[Renderer] ${message} (${sourceId}:${line})`);
    });
    mainWindow.loadFile(path.join(__dirname, '..', 'renderer', 'index.html'));

    mainWindow.once('ready-to-show', () => {
        mainWindow.show();
    });

    mainWindow.on('closed', () => {
        mainWindow = null;
    });
}

app.whenReady().then(createWindow);

app.on('window-all-closed', () => {
    app.quit();
});

app.on('activate', () => {
    if (BrowserWindow.getAllWindows().length === 0) createWindow();
});

ipcMain.handle('save-file', async (event, { content, filename, filters }) => {
    const result = await dialog.showSaveDialog(mainWindow, {
        defaultPath: filename,
        filters: filters || [{ name: 'All Files', extensions: ['*'] }]
    });
    if (!result.canceled) {
        const fs = require('fs');
        fs.writeFileSync(result.filePath, content, 'utf8');
        return { success: true, path: result.filePath };
    }
    return { success: false };
});

ipcMain.handle('load-file', async (event, { filters }) => {
    const result = await dialog.showOpenDialog(mainWindow, {
        filters: filters || [{ name: 'All Files', extensions: ['*'] }],
        properties: ['openFile']
    });
    if (!result.canceled && result.filePaths.length > 0) {
        const fs = require('fs');
        const content = fs.readFileSync(result.filePaths[0], 'utf8');
        return { success: true, content, path: result.filePaths[0] };
    }
    return { success: false };
});
