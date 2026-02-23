/**
 * AGG Frida Kernel - Memory Monitor & Hook Tool
 * Target: dalvik-main (Java Heap)
 * Purpose: Display memory values and types during game events to help identify targets.
 */

const AGG_CONFIG = {
    DEBUG: true,
    WATCH_LIST: [], // Addresses to monitor, e.g., ["0x12345678"]
    AUTO_SCAN_DALVIK: true
};

function log(msg) {
    if (AGG_CONFIG.DEBUG) {
        console.log(`[AGG-Frida] ${msg}`);
    }
}

/**
 * Finds memory ranges associated with the Java Heap (dalvik-main).
 */
function getDalvikHeap() {
    let ranges = Process.enumerateRanges('rw-');
    let dalvikRanges = ranges.filter(r =>
        (r.file && (r.file.path.includes('dalvik-main') || r.file.path.includes('dalvik-alloc'))) ||
        (r.name && (r.name.includes('dalvik-main') || r.name.includes('dalvik-alloc')))
    );

    if (dalvikRanges.length === 0) {
        // Fallback: search for anonymous ranges that might be the heap (usually large)
        dalvikRanges = ranges.filter(r => !r.file && r.size > 1024 * 1024);
        log("No explicit dalvik-main found, using large anonymous ranges as fallback.");
    }

    return dalvikRanges;
}

/**
 * Analyzes memory at the given address to guess its data type.
 */
function analyzeValue(address) {
    try {
        const dword = address.readS32();
        const uDword = address.readU32();
        const float = address.readFloat();

        let result = {
            address: address.toString(),
            dword: dword,
            uDword: uDword,
            float: float.toFixed(4)
        };

        // Heuristic to guess type
        let type = "DWORD";
        if (!isNaN(float) && Math.abs(float) > 0.0001 && Math.abs(float) < 10000000) {
            // Check if it's a plausible float (not a tiny subnormal or huge value)
            if (float.toString().includes('.') && float.toString().length < 15) {
                type = "FLOAT";
            }
        } else if (uDword > 0x10000 && uDword < 0xFFFFFFFF) {
            // Might be a pointer or large DWORD
            type = "DWORD/PTR";
        }

        result.guessedType = type;
        return result;
    } catch (e) {
        return null;
    }
}

/**
 * Logs the current state of watched memory addresses.
 */
function logMemoryState(label) {
    log(`\n--- EVENT TRIGGERED: ${label} ---`);

    if (AGG_CONFIG.WATCH_LIST.length === 0) {
        log("Watch list is empty. Use rpc.exports.addWatch('addr') to add addresses.");
        return;
    }

    AGG_CONFIG.WATCH_LIST.forEach(addrStr => {
        try {
            const addr = ptr(addrStr);
            const analysis = analyzeValue(addr);
            if (analysis) {
                console.log(`[${addrStr}] Value: ${analysis.dword} | Float: ${analysis.float} | Likely Type: ${analysis.guessedType}`);
            } else {
                console.log(`[${addrStr}] Error: Memory not readable.`);
            }
        } catch (err) {
            console.log(`[${addrStr}] Invalid pointer format.`);
        }
    });
}

/**
 * Sets up hooks on common Android UI events to trigger memory logging.
 */
function setupHooks() {
    if (!Java.available) {
        log("Java environment not available. Skipping UI hooks.");
        return;
    }

    Java.perform(() => {
        log("Initializing Java hooks...");

        // 1. Hook Click Events
        try {
            const View = Java.use('android.view.View');
            View.onClick.implementation = function(v) {
                logMemoryState("View.onClick (" + v.toString() + ")");
                this.onClick(v);
            };
            log("Hooked: android.view.View.onClick");
        } catch (e) {
            log("Failed to hook View.onClick: " + e);
        }

        // 2. Hook TextView.setText (Useful for catching UI updates)
        try {
            const TextView = Java.use('android.widget.TextView');
            TextView.setText.overload('java.lang.CharSequence').implementation = function(text) {
                if (text) {
                    logMemoryState("TextView.setText: " + text.toString());
                }
                this.setText(text);
            };
        } catch (e) {
            log("Failed to hook TextView.setText: " + e);
        }

        log("Hooks active. Perform actions in the game to see logs.");
    });
}

// RPC Exports for interaction via Frida CLI or AndLua+
rpc.exports = {
    addWatch: function(address) {
        if (!AGG_CONFIG.WATCH_LIST.includes(address)) {
            AGG_CONFIG.WATCH_LIST.push(address);
            log(`Added ${address} to watch list.`);
        }
        return true;
    },
    removeWatch: function(address) {
        AGG_CONFIG.WATCH_LIST = AGG_CONFIG.WATCH_LIST.filter(a => a !== address);
        log(`Removed ${address} from watch list.`);
        return true;
    },
    listWatch: function() {
        return AGG_CONFIG.WATCH_LIST;
    },
    clearWatch: function() {
        AGG_CONFIG.WATCH_LIST = [];
        log("Watch list cleared.");
        return true;
    },
    scanHeap: function(pattern) {
        const heap = getDalvikHeap();
        log(`Scanning ${heap.length} heap ranges for pattern: ${pattern}`);
        heap.forEach(r => {
            Memory.scan(r.base, r.size, pattern, {
                onMatch: function(address, size) {
                    log(`Pattern match found at: ${address}`);
                },
                onError: function(reason) {
                    // log(`Scan error: ${reason}`);
                },
                onComplete: function() { }
            });
        });
    },
    trigger: function() {
        logMemoryState("Manual RPC Trigger");
    }
};

// Start the kernel
setupHooks();
log("AGG Frida Kernel Version 1.0 Loaded.");
log("Targeting dalvik-main for Java Heap monitoring.");
