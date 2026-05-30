--[[
    ⚡ InstaKill Standalone — Boss Only (V5 - NEXUS LOGIC)

    PERBAIKAN V5 (ULTIMATE FIX):
    1. Smart Remote Finder: Mencari jalur remote secara dinamis (Combat/Ability/Skills).
    2. Nexus Attack: Mengirimkan berbagai variasi argumen (Boss, Posisi, dan Slot).
    3. Reward Logic: Mode HitSpam otomatis berhenti di 5% HP untuk mencegah 'Zonk' (Opsional).
    4. Console Logger: Menampilkan proses penemuan remote di layar (Debug).
    5. Split UI V2: Status Bar transparan + Draggable Console.
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
for _, v in pairs({ "IK_BossUI", "IK_BossUI_Fixed", "IK_BossUI_V2", "IK_BossUI_V3", "IK_BossUI_V4", "IK_BossUI_V5" }) do
    pcall(function() game:GetService("CoreGui"):FindFirstChild(v):Destroy() end)
    pcall(function() Plr:WaitForChild("PlayerGui"):FindFirstChild(v):Destroy() end)
end

repeat task.wait() until game:IsLoaded()

-- ══════════════════════════════════════════
--  CONFIG
-- ══════════════════════════════════════════
local Config = {
    Active        = false,
    HPTrigger     = 80,
    BossMinHP     = 500000,
    HitMultiplier = 15,
    AttackDelay   = 0.03,
    StopAtHP      = 5, -- Berhenti di 5% agar tidak bug (Opsional)
}

local State = {
    LastAttack    = 0,
    LastScan      = 0,
    ScanDelay     = 0.5,
    CurrentBoss   = nil,
    IKConn        = nil,
    Remotes       = {}, -- { [Name] = RemoteInstance }
    TargetTags    = {},
    Logs          = {},
}

-- ══════════════════════════════════════════
--  UI HELPERS
-- ══════════════════════════════════════════
local SG = Instance.new("ScreenGui")
SG.Name = "IK_BossUI_V5"; SG.ResetOnSpawn = false; SG.ZIndexBehavior = Enum.ZIndexBehavior.Sibling; SG.IgnoreGuiInset = true; SG.DisplayOrder = 999
if typeof(gethui) == "function" then SG.Parent = gethui() else SG.Parent = Plr:WaitForChild("PlayerGui") end

local C = {
    BG     = Color3.fromRGB(12, 12, 18),
    Header = Color3.fromRGB(18, 18, 26),
    Accent = Color3.fromRGB(88, 101, 242),
    ON     = Color3.fromRGB(46, 204, 113),
    OFF    = Color3.fromRGB(45, 45, 60),
    Text   = Color3.fromRGB(230, 230, 245),
    Sub    = Color3.fromRGB(130, 130, 160),
    Border = Color3.fromRGB(35, 35, 50),
}

-- Console Logger UI
local Console = Instance.new("Frame")
Console.Size = UDim2.new(0, 220, 0, 120); Console.Position = UDim2.new(0, 10, 1, -130); Console.BackgroundColor3 = Color3.new(0,0,0); Console.BackgroundTransparency = 0.5; Console.Parent = SG
Instance.new("UICorner", Console).CornerRadius = UDim.new(0, 6); Instance.new("UIStroke", Console).Color = C.Border

local LogList = Instance.new("ScrollingFrame")
LogList.Size = UDim2.new(1, -10, 1, -10); LogList.Position = UDim2.new(0, 5, 0, 5); LogList.BackgroundTransparency = 1; LogList.ScrollBarThickness = 2; LogList.Parent = Console
local LogLayout = Instance.new("UIListLayout", LogList); LogLayout.SortOrder = Enum.SortOrder.LayoutOrder

local function Log(msg, col)
    local l = Instance.new("TextLabel")
    l.Text = "> " .. msg; l.Size = UDim2.new(1, 0, 0, 15); l.BackgroundTransparency = 1; l.TextColor3 = col or C.Text; l.TextSize = 9; l.Font = Enum.Font.Code; l.TextXAlignment = Enum.TextXAlignment.Left; l.Parent = LogList
    LogList.CanvasSize = UDim2.new(0, 0, 0, LogLayout.AbsoluteContentSize.Y)
    LogList.CanvasPosition = Vector2.new(0, LogList.CanvasSize.Y.Offset)
    if #LogList:GetChildren() > 20 then LogList:GetChildren()[2]:Destroy() end
end

-- Mini Status Bar
local Mini = Instance.new("Frame")
Mini.Size = UDim2.new(0, 180, 0, 40); Mini.Position = UDim2.new(0.5, -90, 0.05, 0); Mini.BackgroundColor3 = C.BG; Mini.Parent = SG
Instance.new("UICorner", Mini).CornerRadius = UDim.new(0, 8); Instance.new("UIStroke", Mini).Color = C.Accent

local StatLbl = Instance.new("TextLabel")
StatLbl.Size = UDim2.new(1, 0, 1, 0); StatLbl.Text = "Nexus System Scanning..."; StatLbl.BackgroundTransparency = 1; StatLbl.TextColor3 = C.Text; StatLbl.Font = Enum.Font.GothamBold; StatLbl.TextSize = 10; StatLbl.Parent = Mini

-- Settings Button
local SetBtn = Instance.new("TextButton")
SetBtn.Text = "⚙️"; SetBtn.Size = UDim2.new(0, 25, 0, 25); SetBtn.Position = UDim2.new(1, 5, 0, 0); SetBtn.BackgroundColor3 = C.Header; SetBtn.TextColor3 = C.Text; SetBtn.Parent = Mini
Instance.new("UICorner", SetBtn).CornerRadius = UDim.new(0, 5)

-- Main Frame (Hidden by Default)
local Main = Instance.new("Frame")
Main.Size = UDim2.new(0, 200, 0, 180); Main.Position = UDim2.new(0.5, -100, 0.2, 0); Main.BackgroundColor3 = C.BG; Main.Visible = false; Main.Parent = SG
Instance.new("UICorner", Main).CornerRadius = UDim.new(0, 8); Instance.new("UIStroke", Main).Color = C.Border

local MList = Instance.new("Frame"); MList.Size = UDim2.new(1, -20, 1, -20); MList.Position = UDim2.new(0, 10, 0, 10); MList.BackgroundTransparency = 1; MList.Parent = Main
local MULL = Instance.new("UIListLayout", MList); MULL.Padding = UDim.new(0, 5)

local function MkBtn(txt, callback)
    local b = Instance.new("TextButton"); b.Text = txt; b.Size = UDim2.new(1, 0, 0, 30); b.BackgroundColor3 = C.OFF; b.TextColor3 = C.Text; b.Font = Enum.Font.GothamBold; b.TextSize = 11; b.Parent = MList
    Instance.new("UICorner", b).CornerRadius = UDim.new(0, 6)
    b.MouseButton1Click:Connect(function() callback(b) end)
    return b
end

local function MkInput(lbl, key)
    local f = Instance.new("Frame"); f.Size = UDim2.new(1, 0, 0, 25); f.BackgroundTransparency = 1; f.Parent = MList
    local l = Instance.new("TextLabel"); l.Text = lbl; l.Size = UDim2.new(0.6, 0, 1, 0); l.BackgroundTransparency = 1; l.TextColor3 = C.Sub; l.TextSize = 10; l.Font = Enum.Font.Gotham; l.TextXAlignment = Enum.TextXAlignment.Left; l.Parent = f
    local i = Instance.new("TextBox"); i.Text = tostring(Config[key]); i.Size = UDim2.new(0.35, 0, 0, 20); i.Position = UDim2.new(0.65, 0, 0, 2); i.BackgroundColor3 = Color3.new(0,0,0); i.TextColor3 = Color3.new(1,1,1); i.Font = Enum.Font.GothamBold; i.TextSize = 10; i.Parent = f
    Instance.new("UICorner", i).CornerRadius = UDim.new(0, 5)
    i.FocusLost:Connect(function() Config[key] = tonumber(i.Text) or Config[key]; i.Text = tostring(Config[key]) end)
end

local SystemBtn = MkBtn("SYSTEM: OFF", function(b)
    Config.Active = not Config.Active
    b.Text = Config.Active and "SYSTEM: ON" or "SYSTEM: OFF"
    b.BackgroundColor3 = Config.Active and C.ON or C.OFF
end)

MkInput("HP Trigger %", "HPTrigger")
MkInput("Hit Multiplier", "HitMultiplier")

SetBtn.MouseButton1Click:Connect(function() Main.Visible = not Main.Visible end)

-- Drag Logic
local function Draggable(f)
    local d, s, p; f.InputBegan:Connect(function(i) if i.UserInputType == Enum.UserInputType.MouseButton1 then d = true; s = i.Position; p = f.Position; i.Changed:Connect(function() if i.UserInputState == Enum.UserInputState.End then d = false end end) end end)
    UIS.InputChanged:Connect(function(i) if d and i.UserInputType == Enum.UserInputType.MouseMovement then local delta = i.Position - s; f.Position = UDim2.new(p.X.Scale, p.X.Offset + delta.X, p.Y.Scale, p.Y.Offset + delta.Y) end end)
end
Draggable(Mini); Draggable(Main); Draggable(Console)

-- ══════════════════════════════════════════
--  SMART REMOTE FINDER
-- ══════════════════════════════════════════
local function ScanRemotes()
    State.Remotes = {}
    Log("Mencari Nexus Remotes...", Color3.new(1, 1, 0))

    local paths = { RS:FindFirstChild("CombatSystem"), RS:FindFirstChild("AbilitySystem"), RS }
    local targets = { "RequestHit", "RequestAbility", "Damage", "Attack", "Skill", "UseAbility" }

    for _, p in pairs(paths) do
        if p then
            for _, v in pairs(p:GetDescendants()) do
                if v:IsA("RemoteEvent") or v:IsA("RemoteFunction") then
                    for _, t in pairs(targets) do
                        if v.Name:find(t) then
                            State.Remotes[v.Name] = v
                            Log("Found: " .. v.Name, Color3.new(0, 1, 0))
                        end
                    end
                end
            end
        end
    end
    if not next(State.Remotes) then Log("Warning: No Remotes Found!", Color3.new(1, 0, 0)) end
end
task.spawn(ScanRemotes)

-- ══════════════════════════════════════════
--  CORE LOGIC
-- ══════════════════════════════════════════
local function GetBestBoss()
    local char = Plr.Character
    local root = char and char:FindFirstChild("HumanoidRootPart")
    if not root then return nil end
    local best, minDist = nil, math.huge
    local targets = (workspace:FindFirstChild("NPCs") and workspace.NPCs:GetChildren()) or workspace:GetChildren()
    for _, v in ipairs(targets) do
        if v:IsA("Model") and v ~= char then
            local hum = v:FindFirstChildOfClass("Humanoid")
            local vRoot = v:FindFirstChild("HumanoidRootPart")
            if hum and vRoot and hum.Health > 0 and hum.MaxHealth >= Config.BossMinHP then
                local d = (root.Position - vRoot.Position).Magnitude
                if d < minDist then minDist = d; best = v end
            end
        end
    end
    return best
end

State.IKConn = RunService.Heartbeat:Connect(function()
    if not Config.Active then
        StatLbl.Text = "Nexus System: Ready"; StatLbl.TextColor3 = C.Sub
        return
    end

    if os.clock() - State.LastScan >= State.ScanDelay then
        State.CurrentBoss = GetBestBoss()
        State.LastScan = os.clock()
    end

    local boss = State.CurrentBoss
    if not boss or not boss:FindFirstChild("HumanoidRootPart") then
        State.CurrentBoss = nil; StatLbl.Text = "Searching Boss..."; StatLbl.TextColor3 = Color3.new(1, 0.5, 0)
        return
    end

    local bHum = boss:FindFirstChildOfClass("Humanoid")
    local bRoot = boss:FindFirstChild("HumanoidRootPart")
    if not bHum or bHum.Health <= 0 then return end

    local hpPct = (bHum.Health / bHum.MaxHealth) * 100
    StatLbl.Text = string.format("%s: %.1f%%", boss.Name:sub(1,10), hpPct)
    StatLbl.TextColor3 = C.ON

    -- STOP LOGIC: Berhenti jika terlalu rendah agar tidak error/kick
    if hpPct <= Config.StopAtHP then return end

    if hpPct <= Config.HPTrigger then
        if os.clock() - State.LastAttack >= Config.AttackDelay then
            local pos = bRoot.Position

            for i = 1, Config.HitMultiplier do
                -- Pattern 1: Ability Spam (Based on User Log)
                if State.Remotes["RequestAbility"] then
                    pcall(function() State.Remotes["RequestAbility"]:FireServer(2) end)
                end

                -- Pattern 2: Multi-Argument Hit (Mencoba menebak format argumen server)
                if State.Remotes["RequestHit"] then
                    local r = State.Remotes["RequestHit"]
                    pcall(function() r:FireServer(pos) end) -- Vector3
                    pcall(function() r:FireServer(boss) end) -- Instance
                    pcall(function() r:FireServer(boss, pos) end) -- Mixed
                end

                -- Pattern 3: Dynamic Skill Fire
                for name, remote in pairs(State.Remotes) do
                    if name:find("Skill") or name:find("Attack") then
                        pcall(function() remote:FireServer(pos) end)
                    end
                end
            end
            State.LastAttack = os.clock()
        end
    end
end)

Log("V5 Nexus Logic Loaded.", C.ON)
Log("Auto-Scanner Active.", C.ON)
Log("Ability Slot 2 Prioritized.", C.Accent)
