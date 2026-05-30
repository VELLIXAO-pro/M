--[[
    ⚡ InstaKill Standalone — Boss Only (FIXED & OPTIMIZED)

    PERBAIKAN & OPTIMASI:
    1. HP Trigger Fix: Bisa jalan saat darah boss 100%.
    2. Performance: Mencari boss secara efisien (cache folder & throttle scan).
    3. Multi-Hit: Ditambahkan multiplier untuk kecepatan InstaKill.
    4. UI State Fix: Settings di UI sekarang tersimpan dan terupdate dengan benar.
    5. Feature Restore: Kill Counter dikembalikan.
    6. UI Cleanup: Menghapus versi UI lama (V1) dan baru (V2).
    7. Stealth Fix: Menghapus fitur Snap/Teleport agar tidak terlihat mencurigakan.
--]]

-- ══════════════════════════════════════════
--  GUARD
-- ══════════════════════════════════════════
if getgenv().IK_Running then
    warn("[IK] Script sudah berjalan!")
    return
end
getgenv().IK_Running = true

repeat task.wait() until game:IsLoaded()

-- ══════════════════════════════════════════
--  SERVICES
-- ══════════════════════════════════════════
local Players    = game:GetService("Players")
local RunService = game:GetService("RunService")
local UIS        = game:GetService("UserInputService")
local RS         = game:GetService("ReplicatedStorage")

local Plr       = Players.LocalPlayer

-- ══════════════════════════════════════════
--  CONFIG
-- ══════════════════════════════════════════
local Config = {
    Active        = false,
    HPTrigger     = 100,
    BossMinHP     = 500000,
    M1Delay       = 0.05,
    HitMultiplier = 5,
}

local State = {
    Kills      = 0,
    LastM1     = 0,
    LastScan   = 0,
    ScanDelay  = 0.5, -- Scan boss setiap 0.5 detik (lebih hemat FPS)
    CurrentBoss = nil,
    IKConn     = nil,
    Remote     = nil,
    RemoteOK   = false,
    TargetTags = {}, -- Untuk kill counter
}

-- ══════════════════════════════════════════
--  REMOTE DETECTION
-- ══════════════════════════════════════════
local function GetRemote()
    local path = RS:FindFirstChild("CombatSystem")
    if path then
        local remotes = path:FindFirstChild("Remotes")
        if remotes then
            return remotes:FindFirstChild("RequestHit")
        end
    end
    return nil
end

task.spawn(function()
    while not State.RemoteOK and getgenv().IK_Running do
        State.Remote = GetRemote()
        if State.Remote then
            State.RemoteOK = true
            print("[IK] Remote Berhasil Ditemukan: ", State.Remote:GetFullName())
        else
            task.wait(2)
        end
    end
end)

-- ══════════════════════════════════════════
--  GUI SETUP
-- ══════════════════════════════════════════
local SG = Instance.new("ScreenGui")
SG.Name           = "IK_BossUI_V2"
SG.ResetOnSpawn   = false
SG.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
SG.IgnoreGuiInset = true
SG.DisplayOrder   = 999

-- Cleanup UI Lama & Baru
pcall(function() game:GetService("CoreGui"):FindFirstChild("IK_BossUI"):Destroy() end)
pcall(function() game:GetService("CoreGui"):FindFirstChild("IK_BossUI_Fixed"):Destroy() end)
pcall(function() game:GetService("CoreGui"):FindFirstChild("IK_BossUI_V2"):Destroy() end)
pcall(function() Plr.PlayerGui:FindFirstChild("IK_BossUI"):Destroy() end)
pcall(function() Plr.PlayerGui:FindFirstChild("IK_BossUI_Fixed"):Destroy() end)
pcall(function() Plr.PlayerGui:FindFirstChild("IK_BossUI_V2"):Destroy() end)

if typeof(gethui) == "function" then
    SG.Parent = gethui()
elseif game:GetService("CoreGui"):FindFirstChild("RobloxGui") then
    SG.Parent = game:GetService("CoreGui")
else
    SG.Parent = Plr:WaitForChild("PlayerGui")
end

local C = {
    BG     = Color3.fromRGB(14, 14, 20),
    Header = Color3.fromRGB(20, 20, 30),
    Accent = Color3.fromRGB(88, 101, 242),
    ON     = Color3.fromRGB(46, 204, 113),
    OFF    = Color3.fromRGB(50, 50, 68),
    Danger = Color3.fromRGB(210, 50, 50),
    Text   = Color3.fromRGB(220, 220, 235),
    Sub    = Color3.fromRGB(120, 120, 148),
    Input  = Color3.fromRGB(24, 24, 36),
    Border = Color3.fromRGB(40, 40, 60),
    Warn   = Color3.fromRGB(230, 170, 40),
}

local W, H, HDR = 220, 260, 30

local Main = Instance.new("Frame")
Main.Size = UDim2.new(0, W, 0, H)
Main.Position = UDim2.new(0.5, -W/2, 0.2, 0)
Main.BackgroundColor3 = C.BG
Main.BorderSizePixel = 0
Main.Parent = SG
Instance.new("UICorner", Main).CornerRadius = UDim.new(0, 10)
Instance.new("UIStroke", Main).Color = C.Border

-- Header
local Header = Instance.new("Frame")
Header.Size = UDim2.new(1, 0, 0, HDR)
Header.BackgroundColor3 = C.Header
Header.BorderSizePixel = 0
Header.Parent = Main
Instance.new("UICorner", Header).CornerRadius = UDim.new(0, 10)

local TLbl = Instance.new("TextLabel")
TLbl.Text = "⚡ InstaKill V2 - Optimized"
TLbl.Size = UDim2.new(1, -60, 1, 0)
TLbl.Position = UDim2.new(0, 10, 0, 0)
TLbl.BackgroundTransparency = 1; TLbl.TextColor3 = C.Text
TLbl.Font = Enum.Font.GothamBold; TLbl.TextSize = 12
TLbl.TextXAlignment = Enum.TextXAlignment.Left; TLbl.Parent = Header

local CloseBtn = Instance.new("TextButton")
CloseBtn.Text = "✕"; CloseBtn.Size = UDim2.new(0, 24, 0, 20)
CloseBtn.Position = UDim2.new(1, -30, 0.5, -10)
CloseBtn.BackgroundColor3 = C.Danger; CloseBtn.TextColor3 = Color3.new(1,1,1)
CloseBtn.Font = Enum.Font.GothamBold; CloseBtn.Parent = Header
Instance.new("UICorner", CloseBtn).CornerRadius = UDim.new(0, 5)

-- Content
local Cont = Instance.new("Frame")
Cont.Size = UDim2.new(1, 0, 1, -HDR); Cont.Position = UDim2.new(0, 0, 0, HDR)
Cont.BackgroundTransparency = 1; Cont.Parent = Main
local ULL = Instance.new("UIListLayout", Cont)
ULL.Padding = UDim.new(0, 5); ULL.HorizontalAlignment = Enum.HorizontalAlignment.Center
local UPad = Instance.new("UIPadding", Cont)
UPad.PaddingTop = UDim.new(0, 8); UPad.PaddingLeft = UDim.new(0, 10); UPad.PaddingRight = UDim.new(0, 10)

-- UI Helpers with Fix for State
local function CreateRow(lbl, configKey, ph, callback)
    local f = Instance.new("Frame")
    f.Size = UDim2.new(1, 0, 0, 26); f.BackgroundTransparency = 1; f.Parent = Cont

    local l = Instance.new("TextLabel")
    l.Text = lbl; l.Size = UDim2.new(0.5, 0, 1, 0)
    l.BackgroundTransparency = 1; l.TextColor3 = C.Sub
    l.TextSize = 11; l.Font = Enum.Font.Gotham
    l.TextXAlignment = Enum.TextXAlignment.Left; l.Parent = f

    local b = Instance.new("TextBox")
    b.Text = tostring(Config[configKey])
    b.PlaceholderText = ph; b.Size = UDim2.new(0.45, 0, 0, 22)
    b.Position = UDim2.new(0.55, 0, 0, 2); b.BackgroundColor3 = C.Input
    b.TextColor3 = Color3.fromRGB(255, 210, 80); b.Font = Enum.Font.GothamBold
    b.TextSize = 11; b.BorderSizePixel = 0; b.Parent = f
    Instance.new("UICorner", b).CornerRadius = UDim.new(0, 6)

    b.FocusLost:Connect(function()
        callback(b.Text)
        b.Text = tostring(Config[configKey]) -- Update visual ke value asli (setelah validasi di callback)
    end)
    return b
end

-- Controls
local IKBtn = Instance.new("TextButton")
IKBtn.Text = "OFF"; IKBtn.Size = UDim2.new(1, 0, 0, 30)
IKBtn.BackgroundColor3 = C.OFF; IKBtn.TextColor3 = C.Sub
IKBtn.Font = Enum.Font.GothamBold; IKBtn.TextSize = 12; IKBtn.Parent = Cont
Instance.new("UICorner", IKBtn).CornerRadius = UDim.new(0, 8)

CreateRow("HP% Trigger", "HPTrigger", "1-100", function(t)
    local v = tonumber(t)
    if v then Config.HPTrigger = math.clamp(v, 1, 100) end
end)

CreateRow("Boss MinHP", "BossMinHP", "e.g 500000", function(t)
    local v = tonumber(t)
    if v then Config.BossMinHP = v end
end)

CreateRow("Hit Multiplier", "HitMultiplier", "1-20", function(t)
    local v = tonumber(t)
    if v then Config.HitMultiplier = math.clamp(v, 1, 50) end
end)

-- Status bar
local SF = Instance.new("Frame")
SF.Size = UDim2.new(1,0,0,32); SF.BackgroundColor3 = C.Input
SF.BorderSizePixel = 0; SF.Parent = Cont
Instance.new("UICorner", SF).CornerRadius = UDim.new(0,8)

local StatLbl = Instance.new("TextLabel")
StatLbl.Size = UDim2.new(1,-60,1,0); StatLbl.Position = UDim2.new(0,8,0,0)
StatLbl.Text = "⬡ Menunggu Remote..."; StatLbl.BackgroundTransparency = 1
StatLbl.TextColor3 = C.Warn; StatLbl.TextSize = 10
StatLbl.Font = Enum.Font.Gotham; StatLbl.TextXAlignment = Enum.TextXAlignment.Left
StatLbl.Parent = SF

local KillLbl = Instance.new("TextLabel")
KillLbl.Size = UDim2.new(0,50,1,0); KillLbl.Position = UDim2.new(1,-54,0,0)
KillLbl.Text = "✦ 0"; KillLbl.BackgroundTransparency = 1
KillLbl.TextColor3 = C.Accent; KillLbl.TextSize = 10
KillLbl.Font = Enum.Font.GothamBold; KillLbl.TextXAlignment = Enum.TextXAlignment.Right
KillLbl.Parent = SF

-- ══════════════════════════════════════════
--  DRAG LOGIC
-- ══════════════════════════════════════════
do
    local dragging, dragStart, startPos
    Header.InputBegan:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
            dragging = true; dragStart = input.Position; startPos = Main.Position
            input.Changed:Connect(function()
                if input.UserInputState == Enum.UserInputState.End then dragging = false end
            end)
        end
    end)
    UIS.InputChanged:Connect(function(input)
        if dragging and (input.UserInputType == Enum.UserInputType.MouseMovement or input.UserInputType == Enum.UserInputType.Touch) then
            local delta = input.Position - dragStart
            Main.Position = UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
        end
    end)
end

-- ══════════════════════════════════════════
--  CORE FUNCTIONS
-- ══════════════════════════════════════════
IKBtn.MouseButton1Click:Connect(function()
    Config.Active = not Config.Active
    IKBtn.Text = Config.Active and "ON" or "OFF"
    IKBtn.BackgroundColor3 = Config.Active and C.ON or C.OFF
    IKBtn.TextColor3 = Config.Active and Color3.new(1,1,1) or C.Sub
end)

CloseBtn.MouseButton1Click:Connect(function()
    getgenv().IK_Running = false
    if State.IKConn then State.IKConn:Disconnect() end
    SG:Destroy()
end)

local function GetBestBoss()
    local char = Plr.Character
    local root = char and char:FindFirstChild("HumanoidRootPart")
    if not root then return nil end

    local best, minDist = nil, math.huge
    local targets = {}

    -- Optimize: Use NPC folder if exists, else fallback
    local npcFolder = workspace:FindFirstChild("NPCs")
    if npcFolder then
        targets = npcFolder:GetChildren()
    else
        -- If searching workspace, only check Models to save performance
        for _, v in ipairs(workspace:GetChildren()) do
            if v:IsA("Model") then table.insert(targets, v) end
        end
    end

    for _, v in ipairs(targets) do
        if v ~= char then
            local hum = v:FindFirstChildOfClass("Humanoid")
            local vRoot = v:FindFirstChild("HumanoidRootPart")
            if hum and vRoot and hum.Health > 0 and hum.MaxHealth >= Config.BossMinHP then
                local d = (root.Position - vRoot.Position).Magnitude
                if d < minDist then
                    minDist = d
                    best = v
                end
            end
        end
    end
    return best
end

-- Kill Counter Connection
local function SetupKillCounter()
    local folder = workspace:FindFirstChild("NPCs") or workspace
    folder.ChildRemoved:Connect(function(child)
        if State.TargetTags[child] then
            State.Kills = State.Kills + 1
            KillLbl.Text = "✦ " .. State.Kills
            State.TargetTags[child] = nil
        end
    end)
end
task.spawn(SetupKillCounter)

-- Main Loop
State.IKConn = RunService.Heartbeat:Connect(function()
    if not Config.Active then
        StatLbl.Text = State.RemoteOK and "⬡ System Ready" or "⬡ Menunggu Remote..."
        StatLbl.TextColor3 = State.RemoteOK and C.Sub or C.Warn
        return
    end

    if not State.RemoteOK then
        StatLbl.Text = "✕ Remote Error"; StatLbl.TextColor3 = C.Danger
        return
    end

    local char = Plr.Character
    local root = char and char:FindFirstChild("HumanoidRootPart")
    if not root then return end

    -- Throttle Boss Search to preserve FPS
    if os.clock() - State.LastScan >= State.ScanDelay then
        State.CurrentBoss = GetBestBoss()
        State.LastScan = os.clock()
    end

    local boss = State.CurrentBoss
    if not boss or not boss:FindFirstChild("HumanoidRootPart") or boss:FindFirstChildOfClass("Humanoid").Health <= 0 then
        State.CurrentBoss = nil
        StatLbl.Text = "⬡ Mencari Boss..."; StatLbl.TextColor3 = C.Warn
        return
    end

    local bHum = boss:FindFirstChildOfClass("Humanoid")
    local bRoot = boss:FindFirstChild("HumanoidRootPart")
    local hpPct = (bHum.Health / bHum.MaxHealth) * 100

    StatLbl.Text = string.format("⚡ %s (%.1f%%)", boss.Name:sub(1,10), hpPct)
    StatLbl.TextColor3 = C.ON

    if hpPct <= Config.HPTrigger then
        -- Tag for Kill Counter
        State.TargetTags[boss] = true

        -- Attack Logic (Snap Removed for Stealth)
        if os.clock() - State.LastM1 >= Config.M1Delay then
            local targetPos = bRoot.Position
            for i = 1, Config.HitMultiplier do
                pcall(function() State.Remote:FireServer(targetPos) end)
            end
            State.LastM1 = os.clock()
        end
    end
end)

print("[IK] Script V2 (Optimized & Stealth) Loaded!")
