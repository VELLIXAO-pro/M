const socket = io();
let currentBotId = null;
let authToken = localStorage.getItem('samurai_token');

const loginOverlay = document.getElementById('login-overlay');
const mainContainer = document.getElementById('main-container');
const botListSection = document.getElementById('bot-list-section');
const managementSection = document.getElementById('management-section');
const botList = document.getElementById('bot-list');
const currentBotName = document.getElementById('current-bot-name');
const consoleOutput = document.getElementById('console');
const uploadModal = document.getElementById('upload-modal');

// --- Navigation ---
function checkAuth() {
    if (authToken) {
        loginOverlay.classList.add('hidden');
        mainContainer.classList.remove('hidden');
        loadBots();
    } else {
        loginOverlay.classList.remove('hidden');
        mainContainer.classList.add('hidden');
    }
}

function showDashboard() {
    botListSection.classList.remove('hidden');
    managementSection.classList.add('hidden');
    currentBotId = null;
    loadBots();
}

function showManagement(bot) {
    botListSection.classList.add('hidden');
    managementSection.classList.remove('hidden');
    currentBotId = bot.id;
    currentBotName.innerText = bot.name;
    consoleOutput.innerHTML = '';
    socket.emit('join', bot.id);
}

// --- API Calls ---
async function fetchWithAuth(url, options = {}) {
    options.headers = {
        ...options.headers,
        'Authorization': authToken
    };
    const res = await fetch(url, options);
    if (res.status === 401) {
        authToken = null;
        localStorage.removeItem('samurai_token');
        checkAuth();
        throw new Error('Unauthorized');
    }
    return res;
}

async function loadBots() {
    try {
        const res = await fetchWithAuth('/api/bots');
        const bots = await res.json();
        renderBots(bots);
    } catch (err) {
        console.error('Failed to load bots:', err);
    }
}

function renderBots(bots) {
    botList.innerHTML = '';
    bots.forEach(bot => {
        const card = document.createElement('div');
        card.className = 'bot-card';
        card.innerHTML = `
            <h3>${bot.name}</h3>
            <p>Main: ${bot.main}</p>
            <span class="bot-status status-${bot.status}">${bot.status}</span>
        `;
        card.onclick = () => showManagement(bot);
        botList.appendChild(card);
    });
}

async function controlBot(action) {
    if (!currentBotId) return;
    try {
        const res = await fetchWithAuth(`/api/bot/${currentBotId}/${action}`, { method: 'POST' });
        const data = await res.json();
        if (data.success) {
            appendConsole(`\n[System] Command sent: ${action}\n`);
        } else {
            appendConsole(`\n[System] Error: ${data.error}\n`);
        }
    } catch (err) {
        appendConsole(`\n[System] Request failed: ${err.message}\n`);
    }
}

// --- Event Handlers ---
document.getElementById('login-form').onsubmit = async (e) => {
    e.preventDefault();
    const password = document.getElementById('panel-password').value;
    try {
        const res = await fetch('/api/login', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ password })
        });
        const data = await res.json();
        if (data.success) {
            authToken = data.token;
            localStorage.setItem('samurai_token', authToken);
            checkAuth();
        } else {
            alert('Access Denied');
        }
    } catch (err) {
        alert('Login failed');
    }
};

document.getElementById('show-upload-btn').onclick = () => uploadModal.classList.remove('hidden');
document.querySelector('.close-modal').onclick = () => uploadModal.classList.add('hidden');

document.getElementById('upload-form').onsubmit = async (e) => {
    e.preventDefault();
    const formData = new FormData(e.target);
    try {
        const res = await fetchWithAuth('/api/upload', {
            method: 'POST',
            body: formData
        });
        const data = await res.json();
        if (data.success) {
            uploadModal.classList.add('hidden');
            loadBots();
            e.target.reset();
        } else {
            alert('Upload failed: ' + data.error);
        }
    } catch (err) {
        alert('Upload error: ' + err.message);
    }
};

document.getElementById('start-btn').onclick = () => controlBot('start');
document.getElementById('stop-btn').onclick = () => controlBot('stop');
document.getElementById('restart-btn').onclick = () => controlBot('restart');
document.getElementById('back-btn').onclick = () => showDashboard();
document.getElementById('clear-console').onclick = () => consoleOutput.innerHTML = '';

// --- Socket.io ---
socket.on('console', (data) => {
    appendConsole(data);
});

function appendConsole(data) {
    const isAtBottom = consoleOutput.scrollHeight - consoleOutput.clientHeight <= consoleOutput.scrollTop + 1;
    consoleOutput.innerText += data;
    if (isAtBottom) {
        consoleOutput.scrollTop = consoleOutput.scrollHeight;
    }
}

// Initial Load
checkAuth();
