--[[
    ⚡ InstaKill Standalone — Boss Only (V10 - NEURAL DEATH SYNC)

    ANALYSIS & RULES:
    1. Zero Player Impact: Script tidak mengakses karakter/humanoid player (Mencegah kontrol terkunci).
    2. Zero Interaction Kill: Mematikan boss via sinyal sistem, bukan melalui HitBox atau Skill animasi.
    3. Server Claim: Mengirim pemicu kematian sah (RequestAbility:2) dan sinkronisasi UI (firesignal).
    4. No Rubberband: Menghapus total manipulasi CFrame (Boss tidak berkedip/teleport).
--]]

-- ══════════════════════════════════════════
--  GUARD & SERVICES
-- ══════════════════════════════════════════
if getgenv().IK_Running then
    warn("[IK] Script sudah berjalan!")
    return
end
getgenv().IK_Running = true

local Players    = game:GetService("Players")
local RunService = game:GetService("RunService")
local UIS        = game:GetService("UserInputService")
local RS         = game:GetService("ReplicatedStorage")
local Plr        = Players.LocalPlayer

-- ══════════════════════════════════════════
--  CLEANUP OLD UI
-- ══════════════════════════════════════════
local function CleanUI()
    local names = { "IK_BossUI", "IK_BossUI_Fixed", "IK_BossUI_V2", "IK_BossUI_V3", "IK_BossUI_V4", "IK_BossUI_V5", "IK_V6_Main", "IK_V7_Main", "IK_V8_Main", "IK_V9_Main", "IK_V10_Main" }
    for _, v in pairs(names) do
        pcall(function() game:GetService("CoreGui"):FindFirstChild(v):Destroy() end)
        pcall(function() Plr:WaitForChild("PlayerGui"):FindFirstChild(v):Destroy() end)
    end
end
CleanUI()

repeat task.wait() until game:IsLoaded()

-- ══════════════════════════════════════════
--  CONFIG
-- ══════════════════════════════════════════
local Config = {
    Active      = false,
    HPTrigger   = 80,
    BossMinHP   = 500000,
}

local State = {
    LastScan      = 0,
    ScanDelay     = 1,
    CurrentBoss   = nil,
    IKConn        = nil,
    Remotes       = {},
}

-- ══════════════════════════════════════════
--  REMOTE DETECTION (SYSTEM SYNC)
-- ══════════════════════════════════════════
local function FindRemotes()
    local r = RS:FindFirstChild("Remotes") or RS
    State.Remotes.UIUpdate = r:FindFirstChild("BossUIUpdate")
    State.Remotes.UIHide   = r:FindFirstChild("BossUIHide")

    local ab = RS:FindFirstChild("AbilitySystem") and RS.AbilitySystem:FindFirstChild("Remotes")
    State.Remotes.RequestAbility = ab and ab:FindFirstChild("RequestAbility")
end
task.spawn(FindRemotes)

-- ══════════════════════════════════════════
--  GUI SETUP (NEURAL SPLIT UI)
-- ══════════════════════════════════════════
local SG = Instance.new("ScreenGui")
SG.Name = "IK_V10_Main"; SG.ResetOnSpawn = false; SG.IgnoreGuiInset = true; SG.DisplayOrder = 999
if typeof(gethui) == "function" then SG.Parent = gethui() else SG.Parent = Plr:WaitForChild("PlayerGui") end

local C = {
    BG     = Color3.fromRGB(10, 10, 15),
    Accent = Color3.fromRGB(255, 0, 80), -- Neural Red
    Text   = Color3.fromRGB(255, 255, 255),
    Dark   = Color3.fromRGB(5, 5, 8),
}

-- FLOAT TRACKER
local Tracker = Instance.new("Frame")
Tracker.Size = UDim2.new(0, 160, 0, 30); Tracker.Position = UDim2.new(0.5, -80, 0.02, 0); Tracker.BackgroundColor3 = C.BG; Tracker.Parent = SG
Instance.new("UICorner", Tracker); Instance.new("UIStroke", Tracker).Color = C.Accent

local StatLbl = Instance.new("TextLabel")
StatLbl.Size = UDim2.new(1, 0, 1, 0); StatLbl.Text = "NEURAL SYNC: READY"; StatLbl.BackgroundTransparency = 1; StatLbl.TextColor3 = C.Accent; StatLbl.Font = Enum.Font.GothamBold; StatLbl.TextSize = 8; StatLbl.Parent = Tracker

-- SETTINGS PANEL
local Panel = Instance.new("Frame")
Panel.Size = UDim2.new(0, 140, 0, 80); Panel.Position = UDim2.new(0, 10, 0.4, 0); Panel.BackgroundColor3 = C.BG; Panel.Visible = true; Panel.Parent = SG
Instance.new("UICorner", Panel); Instance.new("UIStroke", Panel).Color = C.Accent

local ToggleBtn = Instance.new("TextButton")
ToggleBtn.Text = "SYSTEM: OFF"; ToggleBtn.Size = UDim2.new(0.9, 0, 0, 25); ToggleBtn.Position = UDim2.new(0.05, 0, 0.15, 0); ToggleBtn.BackgroundColor3 = C.Dark; ToggleBtn.TextColor3 = Color3.new(0.5, 0.5, 0.5); ToggleBtn.Font = Enum.Font.GothamBold; ToggleBtn.TextSize = 9; ToggleBtn.Parent = Panel
Instance.new("UICorner", ToggleBtn)

local HPBox = Instance.new("TextBox")
HPBox.Text = tostring(Config.HPTrigger); HPBox.Size = UDim2.new(0.9, 0, 0, 25); HPBox.Position = UDim2.new(0.05, 0, 0.55, 0); HPBox.BackgroundColor3 = C.Dark; HPBox.TextColor3 = C.Text; HPBox.Font = Enum.Font.GothamBold; HPBox.TextSize = 9; HPBox.Parent = Panel
Instance.new("UICorner", HPBox)

ToggleBtn.MouseButton1Click:Connect(function()
    Config.Active = not Config.Active
    ToggleBtn.Text = Config.Active and "NEURAL: ACTIVE" or "SYSTEM: OFF"
    ToggleBtn.TextColor3 = Config.Active and C.Accent or Color3.new(0.5,0.5,0.5)
end)
HPBox.FocusLost:Connect(function() Config.HPTrigger = tonumber(HPBox.Text) or Config.HPTrigger; HPBox.Text = tostring(Config.HPTrigger) end)

-- Dragging
local function Draggable(f)
    local d, s, p; f.InputBegan:Connect(function(i) if i.UserInputType == Enum.UserInputType.MouseButton1 then d = true; s = i.Position; p = f.Position; i.Changed:Connect(function() if i.UserInputState == Enum.UserInputState.End then d = false end end) end end)
    UIS.InputChanged:Connect(function(i) if d and i.UserInputType == Enum.UserInputType.MouseMovement then local delta = i.Position - s; f.Position = UDim2.new(p.X.Scale, p.X.Offset + delta.X, p.Y.Scale, p.Y.Offset + delta.Y) end end)
end
Draggable(Tracker); Draggable(Panel)

-- ══════════════════════════════════════════
--  NEURAL DEATH SYNC LOGIC
-- ══════════════════════════════════════════
local function GetBoss()
    local targets = (workspace:FindFirstChild("NPCs") and workspace.NPCs:GetChildren()) or workspace:GetChildren()
    for _, v in ipairs(targets) do
        -- ISOLASI TOTAL: Jangan pernah ambil Player Character
        if v:IsA("Model") and not Players:GetPlayerFromCharacter(v) then
            local hum = v:FindFirstChildOfClass("Humanoid")
            if hum and hum.Health > 0 and hum.MaxHealth >= Config.BossMinHP then
                return v
            end
        end
    end
    return nil
end

State.IKConn = RunService.Heartbeat:Connect(function()
    if not Config.Active then return end

    if os.clock() - State.LastScan >= State.ScanDelay then
        State.CurrentBoss = GetBoss()
        State.LastScan = os.clock()
    end

    local boss = State.CurrentBoss
    if not boss then StatLbl.Text = "WAITING BOSS..."; return end

    local bHum = boss:FindFirstChildOfClass("Humanoid")
    if not bHum then return end

    local hpPct = (bHum.Health / bHum.MaxHealth) * 100
    StatLbl.Text = string.format("%s: %.1f%%", boss.Name:upper(), hpPct)

    -- NEURAL EXECUTION
    if hpPct <= Config.HPTrigger then
        -- 1. STATE HIJACK (Inspirasi FH): Set HP ke 0 secara lokal untuk pemicu sinkronisasi death.
        pcall(function()
            bHum.Health = 0
        end)

        -- 2. SIGNAL SPOOFING (Berdasarkan Log): Memaksa UI internal mati & memutus link server
        if State.Remotes.UIUpdate then
            pcall(function()
                firesignal(State.Remotes.UIUpdate.OnClientEvent, "Health", { max = bHum.MaxHealth, current = 0 })
            end)
        end
        if State.Remotes.UIHide then
            pcall(function() firesignal(State.Remotes.UIHide.OnClientEvent) end)
        end

        -- 3. SERVER SYNC TRIGGER: Mengirim RequestAbility(2) sekali saja sebagai klaim status mati ke server.
        -- Ini tidak memicu animasi pukulan karena dikirim secara mentah (Raw Remote).
        if State.Remotes.RequestAbility then
            pcall(function()
                State.Remotes.RequestAbility:FireServer(2)
            end)
        end

        State.CurrentBoss = nil -- Hentikan pemantauan setelah eksekusi
    end
end)

print("[IK] V10 Neural Death Sync Loaded. Pure Ghost Execution.")
