const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const { v4: uuidv4 } = require('uuid');

const BOTS_FILE = path.join(__dirname, '../bots.json');
const BOTS_DIR = path.join(__dirname, '../bots');

if (!fs.existsSync(BOTS_FILE)) {
    fs.writeFileSync(BOTS_FILE, JSON.stringify([]));
}

let runningProcesses = {};

function getBots() {
    return JSON.parse(fs.readFileSync(BOTS_FILE));
}

function saveBots(bots) {
    fs.writeFileSync(BOTS_FILE, JSON.stringify(bots, null, 2));
}

function startBot(botId, io) {
    const bots = getBots();
    const bot = bots.find(b => b.id === botId);

    if (!bot) throw new Error('Bot not found');
    if (runningProcesses[botId]) throw new Error('Bot already running');

    // Security: Validate main file path
    const mainFile = bot.main || 'index.js';
    if (mainFile.includes('..') || path.isAbsolute(mainFile)) {
        throw new Error('Invalid main file path');
    }

    const botPath = path.join(BOTS_DIR, bot.id);
    const child = spawn('node', [mainFile], {
        cwd: botPath,
        env: { ...process.env, FORCE_COLOR: true }
    });

    runningProcesses[botId] = child;

    child.stdout.on('data', (data) => {
        io.to(botId).emit('console', data.toString());
    });

    child.stderr.on('data', (data) => {
        io.to(botId).emit('console', data.toString());
    });

    child.on('close', (code) => {
        io.to(botId).emit('console', `\n[System] Process exited with code ${code}\n`);
        delete runningProcesses[botId];
    });

    return child;
}

function stopBot(botId) {
    if (runningProcesses[botId]) {
        runningProcesses[botId].kill();
        delete runningProcesses[botId];
        return true;
    }
    return false;
}

function getBotStatus(botId) {
    return runningProcesses[botId] ? 'running' : 'stopped';
}

function stopAllBots() {
    for (const id in runningProcesses) {
        runningProcesses[id].kill();
        console.log(`Stopped bot: ${id}`);
    }
}

module.exports = {
    getBots,
    saveBots,
    startBot,
    stopBot,
    getBotStatus,
    stopAllBots
};
