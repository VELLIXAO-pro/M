const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const cors = require('cors');
const path = require('path');
const fs = require('fs');
const multer = require('multer');
const { v4: uuidv4 } = require('uuid');
const AdmZip = require('adm-zip');
const botManager = require('./lib/botManager');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
    cors: {
        origin: "*",
        methods: ["GET", "POST"]
    }
});

app.use(cors());
app.use(express.json());
app.use(express.static('public'));

const PANEL_PASSWORD = process.env.PANEL_PASSWORD || 'samurai';

// Simple Auth Middleware
app.use((req, res, next) => {
    if (req.path === '/login' || req.path === '/api/login' || req.path.startsWith('/css/') || req.path.startsWith('/js/') || req.path.startsWith('/socket.io/')) {
        return next();
    }
    // Check for auth header or query for now to keep it simple
    const auth = req.headers['authorization'];
    if (auth === PANEL_PASSWORD) {
        return next();
    }
    res.status(401).send('Unauthorized');
});

const upload = multer({ dest: 'uploads/' });

// API Routes
app.get('/api/bots', (req, res) => {
    const bots = botManager.getBots().map(bot => ({
        ...bot,
        status: botManager.getBotStatus(bot.id)
    }));
    res.json(bots);
});

app.post('/api/upload', upload.single('file'), (req, res) => {
    const { name, main } = req.body;
    const file = req.file;

    if (!file) return res.status(400).send('No file uploaded');

    const botId = uuidv4();
    const botPath = path.join(__dirname, 'bots', botId);

    if (!fs.existsSync(botPath)) {
        fs.mkdirSync(botPath, { recursive: true });
    }

    try {
        if (file.originalname.endsWith('.zip')) {
            const zip = new AdmZip(file.path);
            zip.extractAllTo(botPath, true);
        } else {
            fs.copyFileSync(file.path, path.join(botPath, file.originalname));
        }

        const bots = botManager.getBots();
        bots.push({
            id: botId,
            name: name || 'Unnamed Bot',
            main: main || 'index.js',
            createdAt: new Date().toISOString()
        });
        botManager.saveBots(bots);

        // Clean up upload
        fs.unlinkSync(file.path);

        res.json({ success: true, botId });
    } catch (error) {
        console.error(error);
        res.status(500).json({ error: 'Failed to process upload' });
    }
});

app.post('/api/login', (req, res) => {
    const { password } = req.body;
    if (password === PANEL_PASSWORD) {
        res.json({ success: true, token: PANEL_PASSWORD });
    } else {
        res.status(401).json({ error: 'Invalid password' });
    }
});

app.post('/api/bot/:id/:action', (req, res) => {
    const { id, action } = req.params;
    try {
        if (action === 'start') {
            botManager.startBot(id, io);
        } else if (action === 'stop') {
            botManager.stopBot(id);
        } else if (action === 'restart') {
            botManager.stopBot(id);
            botManager.startBot(id, io);
        } else {
            return res.status(400).send('Invalid action');
        }
        res.json({ success: true });
    } catch (error) {
        res.status(500).json({ error: error.message });
    }
});

// Socket.io
io.on('connection', (socket) => {
    socket.on('join', (botId) => {
        socket.join(botId);
        console.log(`Socket joined room: ${botId}`);
    });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
    console.log(`Samurai Panel running on port ${PORT}`);
});

// Graceful shutdown
process.on('SIGTERM', () => {
    console.log('SIGTERM signal received: closing HTTP server');
    botManager.stopAllBots();
    server.close(() => {
        console.log('HTTP server closed');
        process.exit(0);
    });
});

process.on('SIGINT', () => {
    console.log('SIGINT signal received: closing HTTP server');
    botManager.stopAllBots();
    server.close(() => {
        console.log('HTTP server closed');
        process.exit(0);
    });
});
