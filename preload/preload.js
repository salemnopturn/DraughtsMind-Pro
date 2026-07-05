const { contextBridge, ipcRenderer } = require('electron');

contextBridge.exposeInMainWorld('electronAPI', {
    saveFile: (options) => ipcRenderer.invoke('save-file', options),
    loadFile: (options) => ipcRenderer.invoke('load-file', options),
    platform: process.platform,
    isElectron: true
});
