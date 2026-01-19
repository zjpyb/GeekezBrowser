const { app, BrowserWindow, ipcMain, dialog, screen, shell } = require('electron');
const path = require('path');
const fs = require('fs-extra');
const { spawn, exec } = require('child_process');
const getPort = require('get-port');
const puppeteer = require('puppeteer'); // 使用原生 puppeteer，不带 extra
const { v4: uuidv4 } = require('uuid');
const yaml = require('js-yaml');
const { SocksProxyAgent } = require('socks-proxy-agent');
const http = require('http');
const https = require('https');
const os = require('os');


// Hardware acceleration enabled for better UI performance
// Only disable if GPU compatibility issues occur

const { generateXrayConfig } = require('./utils');
const { generateFingerprint, getInjectScript } = require('./fingerprint');

const isDev = !app.isPackaged;
const RESOURCES_BIN = isDev ? path.join(__dirname, 'resources', 'bin') : path.join(process.resourcesPath, 'bin');
// Use platform+arch specific directory for xray binary
const PLATFORM_ARCH = `${process.platform}-${process.arch}`; // e.g., darwin-arm64, darwin-x64, win32-x64
const BIN_DIR = path.join(RESOURCES_BIN, PLATFORM_ARCH);
const BIN_PATH = path.join(BIN_DIR, process.platform === 'win32' ? 'xray.exe' : 'xray');
// Fallback to old location for backward compatibility
const BIN_DIR_LEGACY = RESOURCES_BIN;
const BIN_PATH_LEGACY = path.join(BIN_DIR_LEGACY, process.platform === 'win32' ? 'xray.exe' : 'xray');
const DATA_PATH = path.join(app.getPath('userData'), 'BrowserProfiles');
const TRASH_PATH = path.join(app.getPath('userData'), '_Trash_Bin');
const PROFILES_FILE = path.join(DATA_PATH, 'profiles.json');
const SETTINGS_FILE = path.join(DATA_PATH, 'settings.json');

fs.ensureDirSync(DATA_PATH);
fs.ensureDirSync(TRASH_PATH);

let activeProcesses = {};

function forceKill(pid) {
    return new Promise((resolve) => {
        if (!pid) return resolve();
        try {
            if (process.platform === 'win32') exec(`taskkill /pid ${pid} /T /F`, () => resolve());
            else { process.kill(pid, 'SIGKILL'); resolve(); }
        } catch (e) { resolve(); }
    });
}

/**
 * 获取 Chrome 可执行文件路径
 * @param {string} browserType - 'system' | 'builtin' | 'custom'
 * @param {string} customPath - 自定义路径（当 browserType 为 'custom' 时）
 * @returns {string|null} Chrome 路径
 */
function getChromiumPath(browserType = 'builtin', customPath = null) {
    const platform = process.platform;

    // 如果用户选择自定义路径
    if (browserType === 'custom') {
        if (customPath && fs.existsSync(customPath)) {
            console.log(`[Chrome] 使用自定义路径: ${customPath}`);
            return customPath;
        }
        console.error('[Chrome] 自定义路径无效或不存在:', customPath);
        // 降级到系统浏览器
        browserType = 'system';
    }

    // 如果用户选择系统浏览器，优先尝试系统路径
    if (browserType === 'system') {
        const systemPaths = getSystemChromePaths(platform);
        for (const chromePath of systemPaths) {
            if (fs.existsSync(chromePath)) {
                console.log(`[Chrome] 使用系统 Chrome: ${chromePath}`);
                return chromePath;
            }
        }
        console.warn('[Chrome] 未找到系统 Chrome，降级到内置版本');
    }

    // 降级或用户选择内置浏览器：查找本地下载版本
    const localChromePath = findLocalChromium();
    if (localChromePath) {
        console.log(`[Chrome] 使用${browserType === 'builtin' ? '内置' : '降级到内置'}版本: ${localChromePath}`);
        return localChromePath;
    }

    // 未找到任何 Chrome
    console.error('[Chrome] 未找到可用的 Chrome 浏览器');
    return null;
}

/**
 * 获取系统 Chrome 的标准安装路径
 */
function getSystemChromePaths(platform) {
    const paths = [];

    if (platform === 'darwin') {
        paths.push('/Applications/Google Chrome.app/Contents/MacOS/Google Chrome');
        paths.push(path.join(os.homedir(), 'Applications/Google Chrome.app/Contents/MacOS/Google Chrome'));
    } else if (platform === 'win32') {
        paths.push('C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe');
        paths.push('C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe');
        const localAppData = process.env.LOCALAPPDATA || path.join(os.homedir(), 'AppData', 'Local');
        paths.push(path.join(localAppData, 'Google', 'Chrome', 'Application', 'chrome.exe'));
    } else if (platform === 'linux') {
        paths.push('/usr/bin/google-chrome-stable');
        paths.push('/usr/bin/google-chrome');
        paths.push('/usr/bin/chromium-browser');
    }

    return paths;
}

/**
 * 查找本地下载的 Chrome for Testing
 */
function findLocalChromium() {
    const basePath = isDev
        ? path.join(__dirname, 'resources', 'puppeteer')
        : path.join(process.resourcesPath, 'puppeteer');

    if (!fs.existsSync(basePath)) return null;

    function findFile(dir, filename) {
        try {
            const files = fs.readdirSync(dir);
            for (const file of files) {
                const fullPath = path.join(dir, file);
                const stat = fs.statSync(fullPath);
                if (stat.isDirectory()) {
                    const res = findFile(fullPath, filename);
                    if (res) return res;
                } else if (file === filename) {
                    return fullPath;
                }
            }
        } catch (e) {
            console.warn(`[Chrome] 扫描目录失败: ${dir}`, e.message);
        }
        return null;
    }

    if (process.platform === 'darwin') {
        return findFile(basePath, 'Google Chrome for Testing');
    }
    return findFile(basePath, 'chrome.exe');
}

// Settings management
function loadSettings() {
    try {
        if (fs.existsSync(SETTINGS_FILE)) {
            return JSON.parse(fs.readFileSync(SETTINGS_FILE, 'utf8'));
        }
    } catch (e) {
        console.error('Failed to load settings:', e);
    }
    return { enableRemoteDebugging: false };
}

function saveSettings(settings) {
    try {
        fs.writeFileSync(SETTINGS_FILE, JSON.stringify(settings, null, 2));
        return true;
    } catch (e) {
        console.error('Failed to save settings:', e);
        return false;
    }
}

function createWindow() {
    const { width, height } = screen.getPrimaryDisplay().workAreaSize;
    const win = new BrowserWindow({
        width: Math.round(width * 0.5), height: Math.round(height * 0.601), minWidth: 900, minHeight: 600,
        title: "GeekEZ Browser", backgroundColor: '#1e1e2d',
        icon: path.join(__dirname, 'icon.png'),
        titleBarOverlay: { color: '#1e1e2d', symbolColor: '#ffffff', height: 35 },
        titleBarStyle: 'hidden',
        webPreferences: { preload: path.join(__dirname, 'preload.js'), contextIsolation: true, nodeIntegration: false, spellcheck: false }
    });
    win.setMenuBarVisibility(false);
    win.loadFile('index.html');
    return win;
}

async function generateExtension(profilePath, fingerprint, profileName, watermarkStyle) {
    const extDir = path.join(profilePath, 'extension');
    await fs.ensureDir(extDir);
    const manifest = {
        manifest_version: 3,
        name: "GeekEZ Guard",
        version: "1.0.0",
        description: "Privacy Protection",
        content_scripts: [{ matches: ["<all_urls>"], js: ["content.js"], run_at: "document_start", all_frames: true, world: "MAIN" }]
    };
    const style = watermarkStyle || 'enhanced'; // 默认使用增强水印
    const scriptContent = getInjectScript(fingerprint, profileName, style);
    await fs.writeJson(path.join(extDir, 'manifest.json'), manifest);
    await fs.writeFile(path.join(extDir, 'content.js'), scriptContent);
    return extDir;
}

app.whenReady().then(async () => {
    createWindow();
    setTimeout(() => { fs.emptyDir(TRASH_PATH).catch(() => { }); }, 10000);
});

// IPC Handles
ipcMain.handle('get-app-info', () => { return { name: app.getName(), version: app.getVersion() }; });
ipcMain.handle('fetch-url', async (e, url) => { try { const res = await fetch(url); if (!res.ok) throw new Error('HTTP ' + res.status); return await res.text(); } catch (e) { throw e.message; } });
ipcMain.handle('test-proxy-latency', async (e, proxyStr) => {
    const tempPort = await getPort();
    const tempConfigPath = path.join(app.getPath('userData'), `test_config_${tempPort}.json`);
    const tempLogPath = path.join(app.getPath('userData'), `test_log_${tempPort}.log`);

    try {
        let outbound;
        try {
            const { parseProxyLink } = require('./utils');
            outbound = parseProxyLink(proxyStr, "proxy_test");
        } catch (err) {
            console.error('[Test-Proxy] Parse error:', err.message);
            return { success: false, msg: "Format Err" };
        }

        // 配置xray，开启warning日志以便调试
        const config = {
            log: {
                loglevel: "warning",
                access: tempLogPath,
                error: tempLogPath
            },
            inbounds: [{
                port: tempPort,
                listen: "127.0.0.1",
                protocol: "socks",
                settings: { udp: true }
            }],
            outbounds: [
                outbound,
                { protocol: "freedom", tag: "direct" }
            ],
            routing: {
                rules: [{
                    type: "field",
                    outboundTag: "proxy_test",
                    port: "0-65535"
                }]
            }
        };

        await fs.writeJson(tempConfigPath, config);
        console.log(`[Test-Proxy] Starting xray on port ${tempPort} for proxy test`);

        const xrayProcess = spawn(BIN_PATH, ['-c', tempConfigPath], {
            cwd: BIN_DIR,
            env: { ...process.env, 'XRAY_LOCATION_ASSET': RESOURCES_BIN },
            stdio: 'ignore',
            windowsHide: true
        });

        // 增加等待时间，确保xray完全启动
        await new Promise(r => setTimeout(r, 1500));

        const start = Date.now();
        const agent = new SocksProxyAgent(`socks5://127.0.0.1:${tempPort}`);

        const result = await new Promise((resolve) => {
            const req = http.get('http://cp.cloudflare.com/generate_204', {
                agent,
                timeout: 10000 // 增加到10秒
            }, (res) => {
                const latency = Date.now() - start;
                console.log(`[Test-Proxy] Response status: ${res.statusCode}, latency: ${latency}ms`);

                if (res.statusCode === 204) {
                    resolve({ success: true, latency });
                } else {
                    resolve({ success: false, msg: `HTTP ${res.statusCode}` });
                }
            });

            req.on('error', (err) => {
                console.error('[Test-Proxy] Request error:', err.message);
                resolve({ success: false, msg: err.code || "Network Error" });
            });

            req.on('timeout', () => {
                console.warn('[Test-Proxy] Request timeout');
                req.destroy();
                resolve({ success: false, msg: "Timeout" });
            });
        });

        // 清理
        await forceKill(xrayProcess.pid);
        try {
            fs.unlinkSync(tempConfigPath);
            fs.unlinkSync(tempLogPath);
        } catch (e) {
            // 忽略删除错误
        }

        return result;
    } catch (err) {
        console.error('[Test-Proxy] Unexpected error:', err);
        return { success: false, msg: err.message };
    }
});
ipcMain.handle('set-title-bar-color', (e, colors) => { const win = BrowserWindow.fromWebContents(e.sender); if (win) { if (process.platform === 'win32') try { win.setTitleBarOverlay({ color: colors.bg, symbolColor: colors.symbol }); } catch (e) { } win.setBackgroundColor(colors.bg); } });
ipcMain.handle('check-app-update', async () => { try { const data = await fetchJson('https://api.github.com/repos/EchoHS/GeekezBrowser/releases/latest'); if (!data || !data.tag_name) return { update: false }; const remote = data.tag_name.replace('v', ''); if (compareVersions(remote, app.getVersion()) > 0) { return { update: true, remote, url: data.html_url }; } return { update: false }; } catch (e) { return { update: false, error: e.message }; } });
ipcMain.handle('check-xray-update', async () => { try { const data = await fetchJson('https://api.github.com/repos/XTLS/Xray-core/releases/latest'); if (!data || !data.tag_name) return { update: false }; const remoteVer = data.tag_name; const currentVer = await getLocalXrayVersion(); if (remoteVer !== currentVer) { let assetName = ''; const arch = os.arch(); const platform = os.platform(); if (platform === 'win32') assetName = `Xray-windows-${arch === 'x64' ? '64' : '32'}.zip`; else if (platform === 'darwin') assetName = `Xray-macos-${arch === 'arm64' ? 'arm64-v8a' : '64'}.zip`; else assetName = `Xray-linux-${arch === 'x64' ? '64' : '32'}.zip`; const downloadUrl = `https://gh-proxy.com/https://github.com/XTLS/Xray-core/releases/download/${remoteVer}/${assetName}`; return { update: true, remote: remoteVer.replace(/^v/, ''), downloadUrl }; } return { update: false }; } catch (e) { return { update: false }; } });
ipcMain.handle('download-xray-update', async (e, url) => {
    const exeName = process.platform === 'win32' ? 'xray.exe' : 'xray';
    const tempBase = os.tmpdir();
    const updateId = `xray_update_${Date.now()}`;
    const tempDir = path.join(tempBase, updateId);
    const zipPath = path.join(tempDir, 'xray.zip');
    try {
        fs.mkdirSync(tempDir, { recursive: true });
        await downloadFile(url, zipPath);
        if (process.platform === 'win32') await new Promise((resolve) => exec('taskkill /F /IM xray.exe', () => resolve()));
        activeProcesses = {};
        await new Promise(r => setTimeout(r, 3000));
        const extractDir = path.join(tempDir, 'extracted');
        fs.mkdirSync(extractDir, { recursive: true });
        await extractZip(zipPath, extractDir);
        function findXrayBinary(dir) {
            const files = fs.readdirSync(dir);
            for (const file of files) {
                const fullPath = path.join(dir, file);
                const stat = fs.statSync(fullPath);
                if (stat.isDirectory()) {
                    const found = findXrayBinary(fullPath);
                    if (found) return found;
                } else if (file === exeName) {
                    return fullPath;
                }
            }
            return null;
        }
        const xrayBinary = findXrayBinary(extractDir);
        console.log('[Update Debug] Searched in:', extractDir);
        console.log('[Update Debug] Found binary:', xrayBinary);
        if (!xrayBinary) {
            // 列出所有文件帮助调试
            const allFiles = [];
            function listAllFiles(dir, prefix = '') {
                const files = fs.readdirSync(dir);
                files.forEach(file => {
                    const fullPath = path.join(dir, file);
                    const stat = fs.statSync(fullPath);
                    if (stat.isDirectory()) {
                        allFiles.push(prefix + file + '/');
                        listAllFiles(fullPath, prefix + file + '/');
                    } else {
                        allFiles.push(prefix + file);
                    }
                });
            }
            listAllFiles(extractDir);
            console.log('[Update Debug] All extracted files:', allFiles);
            throw new Error('Xray binary not found in package');
        }

        // Windows文件锁规避：先重命名旧文件，再复制新文件
        const oldPath = BIN_PATH + '.old';
        if (fs.existsSync(BIN_PATH)) {
            try {
                if (fs.existsSync(oldPath)) fs.unlinkSync(oldPath);
            } catch (e) { }
            fs.renameSync(BIN_PATH, oldPath);
        }
        fs.copyFileSync(xrayBinary, BIN_PATH);
        // 删除旧文件
        try {
            if (fs.existsSync(oldPath)) fs.unlinkSync(oldPath);
        } catch (e) { }
        if (process.platform !== 'win32') fs.chmodSync(BIN_PATH, '755');
        // 清理临时目录（即使失败也不影响更新）
        try {
            fs.rmSync(tempDir, { recursive: true, force: true });
        } catch (cleanupErr) {
            console.warn('[Cleanup Warning] Failed to remove temp dir:', cleanupErr.message);
        }
        return true;
    } catch (e) {
        console.error('Xray update failed:', e);
        try {
            if (fs.existsSync(tempDir)) fs.rmSync(tempDir, { recursive: true, force: true });
        } catch (err) { }
        return false;
    }
});
ipcMain.handle('get-running-ids', () => Object.keys(activeProcesses));
ipcMain.handle('get-profiles', async () => {
    if (!fs.existsSync(PROFILES_FILE)) return [];
    const profiles = await fs.readJson(PROFILES_FILE);

    // 为现有配置添加默认 browserType
    return profiles.map(p => ({
        ...p,
        browserType: p.browserType || 'builtin'
    }));
});
ipcMain.handle('update-profile', async (event, updatedProfile) => { let profiles = await fs.readJson(PROFILES_FILE); const index = profiles.findIndex(p => p.id === updatedProfile.id); if (index > -1) { profiles[index] = updatedProfile; await fs.writeJson(PROFILES_FILE, profiles); return true; } return false; });
ipcMain.handle('save-profile', async (event, data) => {
    const profiles = fs.existsSync(PROFILES_FILE) ? await fs.readJson(PROFILES_FILE) : [];
    const fingerprint = data.fingerprint || generateFingerprint();

    // Apply timezone
    if (data.timezone) fingerprint.timezone = data.timezone;
    else fingerprint.timezone = "America/Los_Angeles";

    // Apply city and geolocation
    if (data.city) fingerprint.city = data.city;
    if (data.geolocation) fingerprint.geolocation = data.geolocation;

    // Apply language
    if (data.language && data.language !== 'auto') fingerprint.language = data.language;

    const newProfile = {
        id: uuidv4(),
        name: data.name,
        proxyStr: data.proxyStr,
        tags: data.tags || [],
        fingerprint: fingerprint,
        preProxyOverride: 'default',
        browserType: data.browserType || 'builtin',
        ...((data.browserType || 'builtin') === 'custom' ? { customBrowserPath: data.customBrowserPath } : {}),
        isSetup: false,
        createdAt: Date.now()
    };
    profiles.push(newProfile);
    await fs.writeJson(PROFILES_FILE, profiles);
    return newProfile;
});
ipcMain.handle('delete-profile', async (event, id) => {
    // 关闭正在运行的进程
    if (activeProcesses[id]) {
        await forceKill(activeProcesses[id].xrayPid);
        try {
            await activeProcesses[id].browser.close();
        } catch (e) { }

        // 关闭日志文件描述符（Windows 必须）
        if (activeProcesses[id].logFd !== undefined) {
            try {
                fs.closeSync(activeProcesses[id].logFd);
                console.log('Closed log file descriptor');
            } catch (e) {
                console.error('Failed to close log fd:', e.message);
            }
        }

        delete activeProcesses[id];
        // Windows 需要更长的等待时间让文件释放
        await new Promise(r => setTimeout(r, 1000));
    }

    // 从 profiles.json 中删除
    let profiles = await fs.readJson(PROFILES_FILE);
    profiles = profiles.filter(p => p.id !== id);
    await fs.writeJson(PROFILES_FILE, profiles);

    // 永久删除 profile 文件夹（带重试机制）
    const profileDir = path.join(DATA_PATH, id);
    let deleted = false;

    // 尝试删除 3 次
    for (let attempt = 1; attempt <= 3; attempt++) {
        try {
            if (fs.existsSync(profileDir)) {
                // 使用 fs-extra 的 remove，它会递归删除
                await fs.remove(profileDir);
                console.log(`Deleted profile folder: ${profileDir}`);
                deleted = true;
                break;
            } else {
                deleted = true;
                break;
            }
        } catch (err) {
            console.error(`Delete attempt ${attempt} failed:`, err.message);
            if (attempt < 3) {
                // 等待后重试
                await new Promise(r => setTimeout(r, 500 * attempt));
            }
        }
    }

    // 如果删除失败，移到回收站作为后备方案
    if (!deleted && fs.existsSync(profileDir)) {
        console.warn(`Failed to delete, moving to trash: ${profileDir}`);
        const trashDest = path.join(TRASH_PATH, `${id}_${Date.now()}`);
        try {
            await fs.move(profileDir, trashDest);
            console.log(`Moved to trash: ${trashDest}`);
        } catch (err) {
            console.error(`Failed to move to trash:`, err);
        }
    }

    return true;
});
ipcMain.handle('get-settings', async () => { if (fs.existsSync(SETTINGS_FILE)) return fs.readJson(SETTINGS_FILE); return { preProxies: [], mode: 'single', enablePreProxy: false, enableRemoteDebugging: false }; });
ipcMain.handle('save-settings', async (e, settings) => { await fs.writeJson(SETTINGS_FILE, settings); return true; });
ipcMain.handle('select-extension-folder', async () => {
    const { filePaths } = await dialog.showOpenDialog({
        properties: ['openDirectory'],
        title: 'Select Extension Folder'
    });
    return filePaths && filePaths.length > 0 ? filePaths[0] : null;
});
ipcMain.handle('add-user-extension', async (e, extPath) => {
    const settings = fs.existsSync(SETTINGS_FILE) ? await fs.readJson(SETTINGS_FILE) : {};
    if (!settings.userExtensions) settings.userExtensions = [];
    if (!settings.userExtensions.includes(extPath)) {
        settings.userExtensions.push(extPath);
        await fs.writeJson(SETTINGS_FILE, settings);
    }
    return true;
});
ipcMain.handle('remove-user-extension', async (e, extPath) => {
    if (!fs.existsSync(SETTINGS_FILE)) return true;
    const settings = await fs.readJson(SETTINGS_FILE);
    if (settings.userExtensions) {
        settings.userExtensions = settings.userExtensions.filter(p => p !== extPath);
        await fs.writeJson(SETTINGS_FILE, settings);
    }
    return true;
});
ipcMain.handle('get-user-extensions', async () => {
    if (!fs.existsSync(SETTINGS_FILE)) return [];
    const settings = await fs.readJson(SETTINGS_FILE);
    return settings.userExtensions || [];
});

// ============================================================================
// Xray Core Version Management
// ============================================================================

/**
 * 获取xray核心信息
 */
ipcMain.handle('get-xray-info', async () => {
    try {
        const xrayVersionsDir = path.join(app.getPath('userData'), 'xray-versions');
        await fs.ensureDir(xrayVersionsDir);

        // 读取版本配置文件
        const versionConfigPath = path.join(xrayVersionsDir, 'version-config.json');
        let versionConfig = { currentVersion: null, versions: [] };

        if (fs.existsSync(versionConfigPath)) {
            versionConfig = await fs.readJson(versionConfigPath);
        }

        // 如果没有当前版本，检查默认位置的xray
        if (!versionConfig.currentVersion) {
            if (fs.existsSync(BIN_PATH)) {
                versionConfig.currentVersion = 'default';
                versionConfig.versions = ['default'];
                await fs.writeJson(versionConfigPath, versionConfig);
            }
        }

        // 获取所有可用版本（扫描xray-versions目录）
        const availableVersions = [];
        if (fs.existsSync(xrayVersionsDir)) {
            const files = await fs.readdir(xrayVersionsDir);
            for (const file of files) {
                const versionDir = path.join(xrayVersionsDir, file);
                const stat = await fs.stat(versionDir);
                if (stat.isDirectory()) {
                    const exeName = process.platform === 'win32' ? 'xray.exe' : 'xray';
                    const xrayBinary = path.join(versionDir, exeName);
                    if (fs.existsSync(xrayBinary)) {
                        availableVersions.push(file);
                    }
                }
            }
        }

        // 如果有默认版本，添加到列表
        if (fs.existsSync(BIN_PATH) && !availableVersions.includes('default')) {
            availableVersions.unshift('default');
        }

        // 获取当前版本的实际版本号和最后更新时间
        let currentVersionDisplay = versionConfig.currentVersion || 'Unknown';
        let lastUpdate = '-';

        if (versionConfig.currentVersion) {
            try {
                const currentBinaryPath = await getXrayBinaryPath(versionConfig.currentVersion);
                if (currentBinaryPath && fs.existsSync(currentBinaryPath)) {
                    // 获取文件修改时间
                    const stats = await fs.stat(currentBinaryPath);
                    lastUpdate = new Date(stats.mtime).toLocaleString();

                    // 如果是default版本，获取实际版本号
                    if (versionConfig.currentVersion === 'default') {
                        const actualVersion = await getXrayVersion(currentBinaryPath);
                        if (actualVersion) {
                            currentVersionDisplay = `default (${actualVersion})`;
                        }
                    }
                }
            } catch (error) {
                console.error('Failed to get xray binary stats:', error);
            }
        }

        return {
            currentVersion: currentVersionDisplay,
            currentVersionKey: versionConfig.currentVersion, // 用于内部识别
            availableVersions: availableVersions,
            lastUpdate: lastUpdate
        };
    } catch (error) {
        console.error('Failed to get xray info:', error);
        return {
            currentVersion: 'Error',
            currentVersionKey: null,
            availableVersions: [],
            lastUpdate: '-'
        };
    }
});

/**
 * 获取xray版本号
 */
async function getXrayVersion(binaryPath) {
    return new Promise((resolve) => {
        exec(`"${binaryPath}" --version`, { timeout: 5000 }, (error, stdout, stderr) => {
            if (error) {
                console.error('Failed to get xray version:', error);
                resolve(null);
                return;
            }

            try {
                // 解析版本信息，xray输出格式如: "Xray 1.8.20 (Xray, Penetrates Everything.)"
                const output = stdout || stderr;
                const match = output.match(/Xray\s+([\d.]+)/i);
                if (match && match[1]) {
                    resolve('v' + match[1]);
                } else {
                    resolve(null);
                }
            } catch (e) {
                console.error('Failed to parse xray version:', e);
                resolve(null);
            }
        });
    });
}

/**
 * 获取GitHub上Xray-core的最新10个发布版本
 */
ipcMain.handle('get-github-xray-releases', async () => {
    try {
        const apiUrl = 'https://api.github.com/repos/XTLS/Xray-core/releases?per_page=10';
        const releases = await fetchJson(apiUrl);

        if (!releases || !Array.isArray(releases)) {
            console.error('Invalid releases data from GitHub');
            return [];
        }

        // 返回简化的版本信息
        return releases.map(release => ({
            tag_name: release.tag_name,
            name: release.name,
            published_at: release.published_at,
            prerelease: release.prerelease
        }));

    } catch (error) {
        console.error('Failed to get GitHub releases:', error);
        return [];
    }
});

/**
 * 获取版本的详细信息（包括default的实际版本号）
 */
ipcMain.handle('get-xray-version-details', async (e, versionKey) => {
    try {
        const binaryPath = await getXrayBinaryPath(versionKey);
        if (!binaryPath || !fs.existsSync(binaryPath)) {
            return { versionKey, displayName: versionKey, actualVersion: null };
        }

        // 如果是default，获取实际版本号
        if (versionKey === 'default') {
            const actualVersion = await getXrayVersion(binaryPath);
            return {
                versionKey: 'default',
                displayName: actualVersion ? `default (${actualVersion})` : 'default',
                actualVersion: actualVersion
            };
        }

        // 其他版本直接返回
        return {
            versionKey: versionKey,
            displayName: versionKey,
            actualVersion: versionKey
        };
    } catch (error) {
        console.error('Failed to get version details:', error);
        return { versionKey, displayName: versionKey, actualVersion: null };
    }
});

/**
 * 获取xray二进制文件路径
 */
async function getXrayBinaryPath(version) {
    const exeName = process.platform === 'win32' ? 'xray.exe' : 'xray';

    if (version === 'default') {
        return BIN_PATH;
    }

    const xrayVersionsDir = path.join(app.getPath('userData'), 'xray-versions');
    const versionPath = path.join(xrayVersionsDir, version, exeName);

    if (fs.existsSync(versionPath)) {
        return versionPath;
    }

    return null;
}

/**
 * 切换xray版本
 */
ipcMain.handle('switch-xray-version', async (e, version) => {
    try {
        const xrayVersionsDir = path.join(app.getPath('userData'), 'xray-versions');
        const versionConfigPath = path.join(xrayVersionsDir, 'version-config.json');

        // 验证版本是否存在
        const binaryPath = await getXrayBinaryPath(version);
        if (!binaryPath || !fs.existsSync(binaryPath)) {
            return { success: false, error: 'Version not found' };
        }

        // 读取或创建版本配置
        let versionConfig = { currentVersion: null, versions: [] };
        if (fs.existsSync(versionConfigPath)) {
            versionConfig = await fs.readJson(versionConfigPath);
        }

        // 更新当前版本
        versionConfig.currentVersion = version;

        // 将版本添加到列表（如果不存在）
        if (!versionConfig.versions.includes(version)) {
            versionConfig.versions.push(version);
        }

        // 保存配置
        await fs.writeJson(versionConfigPath, versionConfig);

        return { success: true };
    } catch (error) {
        console.error('Failed to switch xray version:', error);
        return { success: false, error: error.message };
    }
});

/**
 * 下载xray版本
 */
ipcMain.handle('download-xray-version', async (e, versionTag) => {
    try {
        // 如果是latest，先获取最新版本号
        let version = versionTag;
        if (versionTag === 'latest') {
            const apiUrl = 'https://api.github.com/repos/XTLS/Xray-core/releases/latest';
            const data = await fetchJson(apiUrl);
            version = data.tag_name;
        }

        // 确保版本号以v开头
        if (!version.startsWith('v')) {
            version = 'v' + version;
        }

        // 构建下载URL
        const platform = process.platform;
        const arch = process.arch;

        let osName, archName;

        // 映射平台和架构名称
        if (platform === 'darwin') {
            osName = 'macos';
        } else if (platform === 'win32') {
            osName = 'windows';
        } else if (platform === 'linux') {
            osName = 'linux';
        } else {
            return { success: false, error: 'Unsupported platform' };
        }

        if (arch === 'x64') {
            archName = '64';
        } else if (arch === 'arm64') {
            archName = 'arm64-v8a';
        } else {
            return { success: false, error: 'Unsupported architecture' };
        }

        const fileName = `Xray-${osName}-${archName}.zip`;
        const downloadUrl = `https://github.com/XTLS/Xray-core/releases/download/${version}/${fileName}`;

        console.log('Downloading from:', downloadUrl);

        // 准备下载目录
        const xrayVersionsDir = path.join(app.getPath('userData'), 'xray-versions');
        const versionDir = path.join(xrayVersionsDir, version);
        await fs.ensureDir(versionDir);

        // 下载文件到临时位置
        const tempBase = os.tmpdir();
        const downloadId = `xray_download_${Date.now()}`;
        const tempDir = path.join(tempBase, downloadId);
        const zipPath = path.join(tempDir, 'xray.zip');

        fs.mkdirSync(tempDir, { recursive: true });

        // 使用现有的downloadFile函数
        await downloadFile(downloadUrl, zipPath);

        // 解压文件
        const AdmZip = require('adm-zip');
        const zip = new AdmZip(zipPath);
        zip.extractAllTo(versionDir, true);

        // 设置执行权限（非Windows）
        if (process.platform !== 'win32') {
            const exePath = path.join(versionDir, 'xray');
            if (fs.existsSync(exePath)) {
                await fs.chmod(exePath, 0o755);
            }
        }

        // 清理临时文件
        try {
            fs.removeSync(tempDir);
        } catch (e) {
            console.warn('Failed to clean up temp dir:', e);
        }

        // 更新版本配置
        const versionConfigPath = path.join(xrayVersionsDir, 'version-config.json');
        let versionConfig = { currentVersion: null, versions: [] };
        if (fs.existsSync(versionConfigPath)) {
            versionConfig = await fs.readJson(versionConfigPath);
        }

        if (!versionConfig.versions.includes(version)) {
            versionConfig.versions.push(version);
        }

        await fs.writeJson(versionConfigPath, versionConfig);

        return { success: true, version: version };
    } catch (error) {
        console.error('Failed to download xray version:', error);
        return { success: false, error: error.message };
    }
});

// 选择 Chrome 可执行文件
ipcMain.handle('select-chrome-executable', async () => {
    try {
        const dialogProperties = ['openFile'];

        // macOS: 允许进入 .app 包内部选择文件
        if (process.platform === 'darwin') {
            dialogProperties.push('treatPackageAsDirectory');
        }

        const result = await dialog.showOpenDialog({
            title: '选择 Chrome 可执行文件',
            properties: dialogProperties,
            filters: process.platform === 'darwin'
                ? [
                    { name: 'Chrome 可执行文件', extensions: ['app', '*'] },
                    { name: '所有文件', extensions: ['*'] }
                ]
                : process.platform === 'win32'
                ? [
                    { name: 'Chrome 可执行文件', extensions: ['exe'] },
                    { name: '所有文件', extensions: ['*'] }
                ]
                : [
                    { name: '所有文件', extensions: ['*'] }
                ]
        });

        if (result.canceled || !result.filePaths || result.filePaths.length === 0) {
            console.log('[Chrome] 选择可执行文件已取消');
            return null;
        }

        let selectedPath = result.filePaths[0];

        // macOS: 如果选择了 .app，返回内部可执行文件路径
        if (process.platform === 'darwin' && selectedPath.endsWith('.app')) {
            const testingPath = path.join(selectedPath, 'Contents', 'MacOS', 'Google Chrome for Testing');
            const stablePath = path.join(selectedPath, 'Contents', 'MacOS', 'Google Chrome');
            if (fs.existsSync(testingPath)) {
                selectedPath = testingPath;
            } else if (fs.existsSync(stablePath)) {
                selectedPath = stablePath;
            } else {
                console.warn('[Chrome] 未找到 .app 内部可执行文件:', selectedPath);
                return null;
            }
        }

        if (!fs.existsSync(selectedPath)) {
            console.warn('[Chrome] 选择的路径不存在:', selectedPath);
            return null;
        }

        console.log('[Chrome] 选择自定义路径:', selectedPath);
        return selectedPath;
    } catch (err) {
        console.error('[Chrome] 选择 Chrome 可执行文件失败:', err);
        return null;
    }
});

// 检测浏览器路径
ipcMain.handle('detect-browser-path', async (event, browserType, customPath) => {
    try {
        if (browserType === 'custom') {
            if (customPath && fs.existsSync(customPath)) {
                return customPath;
            }
            console.warn('[Chrome] 自定义路径无效或不存在:', customPath);
            return null;
        }

        // 模拟 getChromiumPath 的检测逻辑
        if (browserType === 'system') {
            const systemPaths = getSystemChromePaths(process.platform);
            for (const chromePath of systemPaths) {
                if (fs.existsSync(chromePath)) {
                    return chromePath;
                }
            }
        }

        // 检测内置版本
        const localChromePath = findLocalChromium();
        return localChromePath || null;
    } catch (err) {
        console.error('[Chrome] 检测浏览器路径失败:', err);
        return null;
    }
});
ipcMain.handle('open-url', async (e, url) => { await shell.openExternal(url); });
ipcMain.handle('export-data', async (e, type) => { const profiles = fs.existsSync(PROFILES_FILE) ? await fs.readJson(PROFILES_FILE) : []; const settings = fs.existsSync(SETTINGS_FILE) ? await fs.readJson(SETTINGS_FILE) : { preProxies: [], subscriptions: [] }; let exportObj = {}; if (type === 'all' || type === 'profiles') exportObj.profiles = profiles; if (type === 'all' || type === 'proxies') { exportObj.preProxies = settings.preProxies || []; exportObj.subscriptions = settings.subscriptions || []; } if (Object.keys(exportObj).length === 0) return false; const { filePath } = await dialog.showSaveDialog({ title: 'Export Data', defaultPath: `GeekEZ_Backup_${type}_${Date.now()}.yaml`, filters: [{ name: 'YAML', extensions: ['yml', 'yaml'] }] }); if (filePath) { await fs.writeFile(filePath, yaml.dump(exportObj)); return true; } return false; });
ipcMain.handle('import-data', async () => { const { filePaths } = await dialog.showOpenDialog({ properties: ['openFile'], filters: [{ name: 'YAML', extensions: ['yml', 'yaml'] }] }); if (filePaths && filePaths.length > 0) { try { const content = await fs.readFile(filePaths[0], 'utf8'); const data = yaml.load(content); let updated = false; if (data.profiles || data.preProxies || data.subscriptions) { if (Array.isArray(data.profiles)) { const currentProfiles = fs.existsSync(PROFILES_FILE) ? await fs.readJson(PROFILES_FILE) : []; data.profiles.forEach(p => { const idx = currentProfiles.findIndex(cp => cp.id === p.id); if (idx > -1) currentProfiles[idx] = p; else { if (!p.id) p.id = uuidv4(); currentProfiles.push(p); } }); await fs.writeJson(PROFILES_FILE, currentProfiles); updated = true; } if (Array.isArray(data.preProxies) || Array.isArray(data.subscriptions)) { const currentSettings = fs.existsSync(SETTINGS_FILE) ? await fs.readJson(SETTINGS_FILE) : { preProxies: [], subscriptions: [] }; if (data.preProxies) { if (!currentSettings.preProxies) currentSettings.preProxies = []; data.preProxies.forEach(p => { if (!currentSettings.preProxies.find(cp => cp.id === p.id)) currentSettings.preProxies.push(p); }); } if (data.subscriptions) { if (!currentSettings.subscriptions) currentSettings.subscriptions = []; data.subscriptions.forEach(s => { if (!currentSettings.subscriptions.find(cs => cs.id === s.id)) currentSettings.subscriptions.push(s); }); } await fs.writeJson(SETTINGS_FILE, currentSettings); updated = true; } } else if (data.name && data.proxyStr && data.fingerprint) { const profiles = fs.existsSync(PROFILES_FILE) ? await fs.readJson(PROFILES_FILE) : []; const newProfile = { ...data, id: uuidv4(), isSetup: false, createdAt: Date.now() }; profiles.push(newProfile); await fs.writeJson(PROFILES_FILE, profiles); updated = true; } return updated; } catch (e) { console.error(e); throw e; } } return false; });

ipcMain.handle('close-profile', async (event, profileId) => {
    if (!activeProcesses[profileId]) {
        return { success: false, message: 'Profile not running' };
    }

    try {
        const { xrayPid, browser, logFd } = activeProcesses[profileId];

        // 关闭浏览器
        await browser.close();

        // 杀死 xray 进程
        await forceKill(xrayPid);

        // 关闭日志文件描述符
        if (logFd !== undefined) {
            try {
                fs.closeSync(logFd);
            } catch (e) {
                console.error('Failed to close log fd:', e.message);
            }
        }

        // 从 activeProcesses 中移除
        delete activeProcesses[profileId];

        // 发送状态更新
        event.sender.send('profile-status', { id: profileId, status: 'stopped' });

        return { success: true };
    } catch (err) {
        console.error('Close profile error:', err);
        return { success: false, message: err.message };
    }
});

// --- 核心启动逻辑 ---
ipcMain.handle('launch-profile', async (event, profileId, watermarkStyle) => {
    const sender = event.sender;

    if (activeProcesses[profileId]) {
        const proc = activeProcesses[profileId];
        if (proc.browser && proc.browser.isConnected()) {
            try {
                const targets = await proc.browser.targets();
                const pageTarget = targets.find(t => t.type() === 'page');
                if (pageTarget) {
                    const page = await pageTarget.page();
                    if (page) {
                        const session = await pageTarget.createCDPSession();
                        const { windowId } = await session.send('Browser.getWindowForTarget');
                        await session.send('Browser.setWindowBounds', { windowId, bounds: { windowState: 'minimized' } });
                        setTimeout(async () => {
                            try { await session.send('Browser.setWindowBounds', { windowId, bounds: { windowState: 'normal' } }); } catch (e) { }
                        }, 100);
                        await page.bringToFront();
                    }
                }
                return "环境已唤醒";
            } catch (e) {
                await forceKill(proc.xrayPid);
                delete activeProcesses[profileId];
            }
        } else {
            await forceKill(proc.xrayPid);
            delete activeProcesses[profileId];
        }
        if (activeProcesses[profileId]) return "环境已唤醒";
    }

    await new Promise(resolve => setTimeout(resolve, 500));

    // Load settings early for userExtensions and remote debugging
    const settings = await fs.readJson(SETTINGS_FILE).catch(() => ({
        enableRemoteDebugging: false,
        userExtensions: [],
        preProxies: [],
        mode: 'single',
        enablePreProxy: false
    }));

    const profiles = await fs.readJson(PROFILES_FILE);
    const profile = profiles.find(p => p.id === profileId);
    if (!profile) throw new Error('Profile not found');

    if (!profile.fingerprint) profile.fingerprint = generateFingerprint();
    if (!profile.fingerprint.languages) profile.fingerprint.languages = ['en-US', 'en'];

    // Pre-proxy settings (settings already loaded above)
    const override = profile.preProxyOverride || 'default';
    const shouldUsePreProxy = override === 'on' || (override === 'default' && settings.enablePreProxy);
    let finalPreProxyConfig = null;
    let switchMsg = null;
    if (shouldUsePreProxy && settings.preProxies && settings.preProxies.length > 0) {
        const active = settings.preProxies.filter(p => p.enable !== false);
        if (active.length > 0) {
            if (settings.mode === 'single') { const target = active.find(p => p.id === settings.selectedId) || active[0]; finalPreProxyConfig = { preProxies: [target] }; }
            else if (settings.mode === 'balance') { const target = active[Math.floor(Math.random() * active.length)]; finalPreProxyConfig = { preProxies: [target] }; if (settings.notify) switchMsg = `Balance: [${target.remark}]`; }
            else if (settings.mode === 'failover') { const target = active[0]; finalPreProxyConfig = { preProxies: [target] }; if (settings.notify) switchMsg = `Failover: [${target.remark}]`; }
        }
    }

    try {
        const localPort = await getPort();
        const profileDir = path.join(DATA_PATH, profileId);
        const userDataDir = path.join(profileDir, 'browser_data');
        const xrayConfigPath = path.join(profileDir, 'config.json');
        const xrayLogPath = path.join(profileDir, 'xray_run.log');
        fs.ensureDirSync(userDataDir);

        try {
            const defaultProfileDir = path.join(userDataDir, 'Default');
            fs.ensureDirSync(defaultProfileDir);
            const preferencesPath = path.join(defaultProfileDir, 'Preferences');
            let preferences = {};
            if (fs.existsSync(preferencesPath)) preferences = await fs.readJson(preferencesPath);
            if (!preferences.bookmark_bar) preferences.bookmark_bar = {};
            preferences.bookmark_bar.show_on_all_tabs = true;
            if (preferences.protection) delete preferences.protection;
            if (!preferences.profile) preferences.profile = {};
            preferences.profile.name = profile.name;
            if (!preferences.webrtc) preferences.webrtc = {};
            preferences.webrtc.ip_handling_policy = 'disable_non_proxied_udp';
            await fs.writeJson(preferencesPath, preferences);
        } catch (e) { }

        const config = generateXrayConfig(profile.proxyStr, localPort, finalPreProxyConfig);
        fs.writeJsonSync(xrayConfigPath, config);
        const logFd = fs.openSync(xrayLogPath, 'a');

        // 获取当前xray版本的路径
        let xrayBinPath = BIN_PATH;
        let xrayBinDir = BIN_DIR;
        try {
            const xrayVersionsDir = path.join(app.getPath('userData'), 'xray-versions');
            const versionConfigPath = path.join(xrayVersionsDir, 'version-config.json');
            if (fs.existsSync(versionConfigPath)) {
                const versionConfig = await fs.readJson(versionConfigPath);
                if (versionConfig.currentVersion && versionConfig.currentVersion !== 'default') {
                    const customBinaryPath = await getXrayBinaryPath(versionConfig.currentVersion);
                    if (customBinaryPath && fs.existsSync(customBinaryPath)) {
                        xrayBinPath = customBinaryPath;
                        xrayBinDir = path.dirname(customBinaryPath);
                        console.log(`Using xray version ${versionConfig.currentVersion} from ${xrayBinPath}`);
                    }
                }
            }
        } catch (error) {
            console.error('Failed to load xray version config, using default:', error);
        }

        const xrayProcess = spawn(xrayBinPath, ['-c', xrayConfigPath], { cwd: xrayBinDir, env: { ...process.env, 'XRAY_LOCATION_ASSET': RESOURCES_BIN }, stdio: ['ignore', logFd, logFd], windowsHide: true });

        // 优化：减少等待时间，Xray 通常 300ms 内就能启动
        await new Promise(resolve => setTimeout(resolve, 300));

        // 0. Resolve Language (Fix: Resolve 'auto' BEFORE generating extension so inject script gets explicit language)
        const targetLang = profile.fingerprint?.language && profile.fingerprint.language !== 'auto'
            ? profile.fingerprint.language
            : 'en-US';

        // Update in-memory profile to ensure generateExtension writes the correct language to inject script
        profile.fingerprint.language = targetLang;
        profile.fingerprint.languages = [targetLang, targetLang.split('-')[0]];

        // 1. 生成 GeekEZ Guard 扩展（使用传递的水印样式）
        const style = watermarkStyle || 'enhanced'; // 默认使用增强水印
        const extPath = await generateExtension(profileDir, profile.fingerprint, profile.name, style);

        // 2. 获取用户自定义扩展
        const userExts = settings.userExtensions || [];

        // 3. 合并所有扩展路径
        let extPaths = extPath; // GeekEZ Guard
        if (userExts.length > 0) {
            extPaths += ',' + userExts.join(',');
        }

        // 4. 构建启动参数（性能优化）

        const launchArgs = [
            `--proxy-server=socks5://127.0.0.1:${localPort}`,
            `--user-data-dir=${userDataDir}`,
            `--window-size=${profile.fingerprint?.window?.width || 1280},${profile.fingerprint?.window?.height || 800}`,
            '--restore-last-session',
            '--no-sandbox',
            '--disable-setuid-sandbox',
            '--disable-blink-features=AutomationControlled',
            '--disable-features=IsolateOrigins,site-per-process',
            '--force-webrtc-ip-handling-policy=disable_non_proxied_udp',
            `--lang=${targetLang}`,
            `--accept-lang=${targetLang}`,
            `--disable-extensions-except=${extPaths}`,
            `--load-extension=${extPaths}`,
            // 性能优化参数
            '--no-first-run',                    // 跳过首次运行向导
            '--no-default-browser-check',        // 跳过默认浏览器检查
            '--disable-background-timer-throttling', // 防止后台标签页被限速
            '--disable-backgrounding-occluded-windows',
            '--disable-renderer-backgrounding',
            '--disable-dev-shm-usage',           // 减少共享内存使用
            '--disk-cache-size=52428800',        // 限制磁盘缓存为 50MB
            '--media-cache-size=52428800'        // 限制媒体缓存为 50MB
        ];

        // 5. Remote Debugging Port (if enabled)
        if (settings.enableRemoteDebugging && profile.debugPort) {
            launchArgs.push(`--remote-debugging-port=${profile.debugPort}`);
            console.log('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━');
            console.log('⚠️  REMOTE DEBUGGING ENABLED');
            console.log(`📡 Port: ${profile.debugPort}`);
            console.log(`🔗 Connect: chrome://inspect or ws://localhost:${profile.debugPort}`);
            console.log('⚠️  WARNING: May increase automation detection risk!');
            console.log('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━');
        }


        // 5. 启动浏览器
        // 从 profile 读取浏览器类型配置
        const browserType = profile.browserType || 'builtin';
        const customPath = profile.customBrowserPath || null;
        const chromePath = getChromiumPath(browserType, customPath);

        if (!chromePath) {
            const { dialog } = require('electron');
            const errorMsg = browserType === 'custom'
                ? '未找到可用的 Chrome（自定义/系统/内置均不可用）。\n\n请重新选择有效的自定义路径，或安装 Chrome/运行 npm run setup。'
                : browserType === 'system'
                    ? '未找到系统 Chrome 浏览器。\n\n请安装 Google Chrome 或在配置中切换到"内置 Chrome"。'
                    : '未找到内置 Chrome。\n\n请运行 npm run setup 下载或切换到"系统 Chrome"。';

            dialog.showErrorBox('Chrome 未找到', errorMsg);
            await forceKill(xrayProcess.pid);
            return;
        }

        console.log(`[Puppeteer] 启动浏览器 (${browserType}): ${chromePath}`);

        // 时区设置
        const env = { ...process.env };
        if (profile.fingerprint?.timezone && profile.fingerprint.timezone !== 'Auto') {
            env.TZ = profile.fingerprint.timezone;
        }

        const browser = await puppeteer.launch({
            headless: false,
            executablePath: chromePath,
            userDataDir: userDataDir,
            args: launchArgs,
            defaultViewport: null,
            ignoreDefaultArgs: ['--enable-automation'],
            pipe: false,
            dumpio: false,
            env: env  // 注入环境变量
        });

        activeProcesses[profileId] = {
            xrayPid: xrayProcess.pid,
            browser,
            logFd: logFd  // 存储日志文件描述符，用于后续关闭
        };
        sender.send('profile-status', { id: profileId, status: 'running' });

        // CDP Geolocation Removed in favor of Stealth JS Hook
        // 由于 CDP 本身会被检测，我们移除所有 Emulation.Overrides
        // 地理位置将由 fingerprint.js 中的 Stealth Hook 接管

        browser.on('disconnected', async () => {
            if (activeProcesses[profileId]) {
                const pid = activeProcesses[profileId].xrayPid;
                const logFd = activeProcesses[profileId].logFd;

                // 关闭日志文件描述符
                if (logFd !== undefined) {
                    try {
                        fs.closeSync(logFd);
                    } catch (e) { }
                }

                delete activeProcesses[profileId];
                await forceKill(pid);

                // 性能优化：清理缓存文件，节省磁盘空间
                try {
                    const cacheDir = path.join(userDataDir, 'Default', 'Cache');
                    const codeCacheDir = path.join(userDataDir, 'Default', 'Code Cache');
                    if (fs.existsSync(cacheDir)) await fs.emptyDir(cacheDir);
                    if (fs.existsSync(codeCacheDir)) await fs.emptyDir(codeCacheDir);
                } catch (e) {
                    // 忽略清理错误
                }

                if (!sender.isDestroyed()) sender.send('profile-status', { id: profileId, status: 'stopped' });
            }
        });

        return switchMsg;
    } catch (err) {
        console.error(err);
        throw err;
    }
});

app.on('window-all-closed', () => {
    Object.values(activeProcesses).forEach(p => forceKill(p.xrayPid));
    if (process.platform !== 'darwin') app.quit();
});
// Helpers (Same)
function fetchJson(url) { return new Promise((resolve, reject) => { const req = https.get(url, { headers: { 'User-Agent': 'GeekEZ-Browser' } }, (res) => { let data = ''; res.on('data', c => data += c); res.on('end', () => { try { resolve(JSON.parse(data)); } catch (e) { reject(e); } }); }); req.on('error', reject); }); }
function getLocalXrayVersion() { return new Promise((resolve) => { if (!fs.existsSync(BIN_PATH)) return resolve('v0.0.0'); try { const proc = spawn(BIN_PATH, ['-version']); let output = ''; proc.stdout.on('data', d => output += d.toString()); proc.on('close', () => { const match = output.match(/Xray\s+v?(\d+\.\d+\.\d+)/i); resolve(match ? (match[1].startsWith('v') ? match[1] : 'v' + match[1]) : 'v0.0.0'); }); proc.on('error', () => resolve('v0.0.0')); } catch (e) { resolve('v0.0.0'); } }); }
function compareVersions(v1, v2) { const p1 = v1.split('.').map(Number); const p2 = v2.split('.').map(Number); for (let i = 0; i < 3; i++) { if ((p1[i] || 0) > (p2[i] || 0)) return 1; if ((p1[i] || 0) < (p2[i] || 0)) return -1; } return 0; }
function downloadFile(url, dest) { return new Promise((resolve, reject) => { const file = fs.createWriteStream(dest); https.get(url, (response) => { if (response.statusCode >= 300 && response.statusCode < 400 && response.headers.location) { downloadFile(response.headers.location, dest).then(resolve).catch(reject); return; } response.pipe(file); file.on('finish', () => file.close(resolve)); }).on('error', (err) => { fs.unlink(dest, () => { }); reject(err); }); }); }
function extractZip(zipPath, destDir) {
    return new Promise((resolve, reject) => {
        if (os.platform() === 'win32') {
            // Windows: 使用 adm-zip（可靠）
            try {
                const AdmZip = require('adm-zip');
                const zip = new AdmZip(zipPath);
                zip.extractAllTo(destDir, true);
                console.log('[Extract Success] Extracted to:', destDir);
                resolve();
            } catch (err) {
                console.error('[Extract Error]', err);
                reject(err);
            }
        } else {
            // macOS/Linux: 使用原生 unzip 命令
            exec(`unzip -o "${zipPath}" -d "${destDir}"`, (err, stdout, stderr) => {
                if (err) {
                    console.error('[Extract Error]', err);
                    console.error('[Extract stderr]', stderr);
                    reject(err);
                } else {
                    console.log('[Extract Success]', stdout);
                    resolve();
                }
            });
        }
    });
}
