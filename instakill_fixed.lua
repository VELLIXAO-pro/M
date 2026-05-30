--[[
    ⚡ InstaKill Standalone — Boss Only (V3 - PRO OPTIMIZED)

    PERBAIKAN & FITUR BARU:
    1. Ability Spam: Menggunakan RequestAbility (Slot 2) untuk damage masif.
    2. Split UI: Mode "Mini" agar tidak mengganggu pandangan.
    3. No-Proximity: Menembak langsung ke koordinat boss (Stealth & Zero Involvement).
    4. Multi-Remote: Mendukung M1 dan Ability System.
    5. UI Cleanup: Menghapus versi UI lama.
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
    AttackDelay   = 0.05,
    HitMultiplier = 10,
    UseAbility    = true, -- Pakai Skill 2 untuk InstaKill masif
    UseM1         = true,
}

local State = {
    Kills         = 0,
    LastAttack    = 0,
    LastScan      = 0,
    ScanDelay     = 0.5,
    CurrentBoss   = nil,
    IKConn        = nil,
    M1Remote      = nil,
    AbilityRemote = nil,
    TargetTags    = {},
    IsMini        = false,
}

-- ══════════════════════════════════════════
--  REMOTE DETECTION
-- ══════════════════════════════════════════
task.spawn(function()
    while getgenv().IK_Running do
        -- M1 Remote
        if not State.M1Remote then
            local cs = RS:FindFirstChild("CombatSystem")
            State.M1Remote = cs and cs:FindFirstChild("Remotes") and cs.Remotes:FindFirstChild("RequestHit")
        end
        -- Ability Remote
        if not State.AbilityRemote then
            local ab = RS:FindFirstChild("AbilitySystem")
            State.AbilityRemote = ab and ab:FindFirstChild("Remotes") and ab.Remotes:FindFirstChild("RequestAbility")
        end
        task.wait(2)
    end
end)

-- ══════════════════════════════════════════
--  GUI SETUP
-- ══════════════════════════════════════════
local SG = Instance.new("ScreenGui")
SG.Name           = "IK_BossUI_V3"
SG.ResetOnSpawn   = false
SG.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
SG.IgnoreGuiInset = true
SG.DisplayOrder   = 999

-- Cleanup
for _, v in pairs({ "IK_BossUI", "IK_BossUI_Fixed", "IK_BossUI_V2", "IK_BossUI_V3" }) do
    pcall(function() game:GetService("CoreGui"):FindFirstChild(v):Destroy() end)
    pcall(function() Plr.PlayerGui:FindFirstChild(v):Destroy() end)
end

if typeof(gethui) == "function" then
    SG.Parent = gethui()
elseif game:GetService("CoreGui"):FindFirstChild("RobloxGui") then
    SG.Parent = game:GetService("CoreGui")
else
    SG.Parent = Plr:WaitForChild("PlayerGui")
end

local C = {
    BG     = Color3.fromRGB(12, 12, 18),
    Header = Color3.fromRGB(18, 18, 26),
    Accent = Color3.fromRGB(88, 101, 242),
    ON     = Color3.fromRGB(46, 204, 113),
    OFF    = Color3.fromRGB(45, 45, 60),
    Danger = Color3.fromRGB(210, 50, 50),
    Text   = Color3.fromRGB(230, 230, 245),
    Sub    = Color3.fromRGB(130, 130, 160),
    Input  = Color3.fromRGB(22, 22, 32),
    Border = Color3.fromRGB(35, 35, 50),
}

local W, H, HDR = 210, 280, 30

local Main = Instance.new("Frame")
Main.Size = UDim2.new(0, W, 0, H)
Main.Position = UDim2.new(0.5, -W/2, 0.15, 0)
Main.BackgroundColor3 = C.BG
Main.BorderSizePixel = 0
Main.ClipsDescendants = true
Main.Parent = SG
Instance.new("UICorner", Main).CornerRadius = UDim.new(0, 8)
Instance.new("UIStroke", Main).Color = C.Border

-- Header
local Header = Instance.new("Frame")
Header.Size = UDim2.new(1, 0, 0, HDR)
Header.BackgroundColor3 = C.Header
Header.BorderSizePixel = 0
Header.Parent = Main
Instance.new("UICorner", Header).CornerRadius = UDim.new(0, 8)

local TLbl = Instance.new("TextLabel")
TLbl.Text = "⚡ InstaKill V3"
TLbl.Size = UDim2.new(1, -80, 1, 0)
TLbl.Position = UDim2.new(0, 10, 0, 0)
TLbl.BackgroundTransparency = 1; TLbl.TextColor3 = C.Text
TLbl.Font = Enum.Font.GothamBold; TLbl.TextSize = 11
TLbl.TextXAlignment = Enum.TextXAlignment.Left; TLbl.Parent = Header

-- Split/Mini Button
local MiniBtn = Instance.new("TextButton")
MiniBtn.Text = "❐"; MiniBtn.Size = UDim2.new(0, 24, 0, 20)
MiniBtn.Position = UDim2.new(1, -54, 0.5, -10)
MiniBtn.BackgroundColor3 = C.OFF; MiniBtn.TextColor3 = C.Text
MiniBtn.Font = Enum.Font.GothamBold; MiniBtn.Parent = Header
Instance.new("UICorner", MiniBtn).CornerRadius = UDim.new(0, 5)

local CloseBtn = Instance.new("TextButton")
CloseBtn.Text = "✕"; CloseBtn.Size = UDim2.new(0, 24, 0, 20)
CloseBtn.Position = UDim2.new(1, -27, 0.5, -10)
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

-- Toggle Ability & M1
local function MkToggle(lbl, key, order)
    local f = Instance.new("Frame")
    f.Size = UDim2.new(1, 0, 0, 26); f.BackgroundTransparency = 1; f.LayoutOrder = order; f.Parent = Cont
    local l = Instance.new("TextLabel")
    l.Text = lbl; l.Size = UDim2.new(0.6, 0, 1, 0); l.BackgroundTransparency = 1
    l.TextColor3 = C.Sub; l.TextSize = 10; l.Font = Enum.Font.Gotham; l.TextXAlignment = Enum.TextXAlignment.Left; l.Parent = f
    local b = Instance.new("TextButton")
    b.Text = Config[key] and "ON" or "OFF"; b.Size = UDim2.new(0.35, 0, 0, 20); b.Position = UDim2.new(0.65, 0, 0, 3)
    b.BackgroundColor3 = Config[key] and C.ON or C.OFF; b.TextColor3 = Color3.new(1,1,1); b.Font = Enum.Font.GothamBold; b.TextSize = 10; b.Parent = f
    Instance.new("UICorner", b).CornerRadius = UDim.new(0, 5)
    b.MouseButton1Click:Connect(function()
        Config[key] = not Config[key]
        b.Text = Config[key] and "ON" or "OFF"
        b.BackgroundColor3 = Config[key] and C.ON or C.OFF
    end)
end

-- UI Row for Config
local function MkRow(lbl, key, ph, order)
    local f = Instance.new("Frame")
    f.Size = UDim2.new(1, 0, 0, 26); f.BackgroundTransparency = 1; f.LayoutOrder = order; f.Parent = Cont
    local l = Instance.new("TextLabel")
    l.Text = lbl; l.Size = UDim2.new(0.5, 0, 1, 0); l.BackgroundTransparency = 1
    l.TextColor3 = C.Sub; l.TextSize = 10; l.Font = Enum.Font.Gotham; l.TextXAlignment = Enum.TextXAlignment.Left; l.Parent = f
    local b = Instance.new("TextBox")
    b.Text = tostring(Config[key]); b.PlaceholderText = ph; b.Size = UDim2.new(0.45, 0, 0, 20)
    b.Position = UDim2.new(0.55, 0, 0, 3); b.BackgroundColor3 = C.Input; b.TextColor3 = Color3.fromRGB(255, 210, 80)
    b.Font = Enum.Font.GothamBold; b.TextSize = 10; b.BorderSizePixel = 0; b.Parent = f
    Instance.new("UICorner", b).CornerRadius = UDim.new(0, 5)
    b.FocusLost:Connect(function()
        local v = tonumber(b.Text)
        if v then Config[key] = v end
        b.Text = tostring(Config[key])
    end)
end

-- Toggles
local IKBtn = Instance.new("TextButton")
IKBtn.Text = "SYSTEM OFF"; IKBtn.Size = UDim2.new(1, 0, 0, 32); IKBtn.LayoutOrder = 0
IKBtn.BackgroundColor3 = C.OFF; IKBtn.TextColor3 = C.Sub; IKBtn.Font = Enum.Font.GothamBold; IKBtn.TextSize = 11; IKBtn.Parent = Cont
Instance.new("UICorner", IKBtn).CornerRadius = UDim.new(0, 6)

MkToggle("Spam Ability (Slot 2)", "UseAbility", 1)
MkToggle("Spam M1 Click", "UseM1", 2)
MkRow("HP Trigger %", "HPTrigger", "1-100", 3)
MkRow("Boss MinHP", "BossMinHP", "HP", 4)
MkRow("Hit Multiplier", "HitMultiplier", "1-100", 5)

-- Status bar
local SF = Instance.new("Frame")
SF.Size = UDim2.new(1,0,0,32); SF.BackgroundColor3 = C.Input; SF.LayoutOrder = 6; SF.Parent = Cont
Instance.new("UICorner", SF).CornerRadius = UDim.new(0,6)

local StatLbl = Instance.new("TextLabel")
StatLbl.Size = UDim2.new(1,-60,1,0); StatLbl.Position = UDim2.new(0,8,0,0)
StatLbl.Text = "⬡ System Idle"; StatLbl.BackgroundTransparency = 1
StatLbl.TextColor3 = C.Sub; StatLbl.TextSize = 9; StatLbl.Font = Enum.Font.Gotham; StatLbl.TextXAlignment = Enum.TextXAlignment.Left; StatLbl.Parent = SF

local KillLbl = Instance.new("TextLabel")
KillLbl.Size = UDim2.new(0,50,1,0); KillLbl.Position = UDim2.new(1,-54,0,0)
KillLbl.Text = "✦ 0"; KillLbl.BackgroundTransparency = 1
KillLbl.TextColor3 = C.Accent; KillLbl.TextSize = 10; KillLbl.Font = Enum.Font.GothamBold; KillLbl.TextXAlignment = Enum.TextXAlignment.Right; KillLbl.Parent = SF

-- ══════════════════════════════════════════
--  UI LOGIC
-- ══════════════════════════════════════════
IKBtn.MouseButton1Click:Connect(function()
    Config.Active = not Config.Active
    IKBtn.Text = Config.Active and "SYSTEM ON" or "SYSTEM OFF"
    IKBtn.BackgroundColor3 = Config.Active and C.ON or C.OFF
    IKBtn.TextColor3 = Config.Active and Color3.new(1,1,1) or C.Sub
end)

MiniBtn.MouseButton1Click:Connect(function()
    State.IsMini = not State.IsMini
    if State.IsMini then
        Main:TweenSize(UDim2.new(0, W, 0, HDR + 40), "Out", "Quart", 0.3, true)
        SF.Parent = Main
        SF.Position = UDim2.new(0, 10, 0, HDR + 4)
        SF.Size = UDim2.new(1, -20, 0, 32)
        Cont.Visible = false
    else
        Main:TweenSize(UDim2.new(0, W, 0, H), "Out", "Quart", 0.3, true)
        SF.Parent = Cont
        SF.Size = UDim2.new(1, 0, 0, 32)
        Cont.Visible = true
    end
end)

CloseBtn.MouseButton1Click:Connect(function()
    getgenv().IK_Running = false
    if State.IKConn then State.IKConn:Disconnect() end
    SG:Destroy()
end)

-- Drag
do
    local drag, dStart, sPos
    Header.InputBegan:Connect(function(i)
        if i.UserInputType == Enum.UserInputType.MouseButton1 or i.UserInputType == Enum.UserInputType.Touch then
            drag = true; dStart = i.Position; sPos = Main.Position
            i.Changed:Connect(function() if i.UserInputState == Enum.UserInputState.End then drag = false end end)
        end
    end)
    UIS.InputChanged:Connect(function(i)
        if drag and (i.UserInputType == Enum.UserInputType.MouseMovement or i.UserInputType == Enum.UserInputType.Touch) then
            local delta = i.Position - dStart
            Main.Position = UDim2.new(sPos.X.Scale, sPos.X.Offset + delta.X, sPos.Y.Scale, sPos.Y.Offset + delta.Y)
        end
    end)
end

-- ══════════════════════════════════════════
--  CORE LOGIC
-- ══════════════════════════════════════════
local function GetBestBoss()
    local char = Plr.Character
    local root = char and char:FindFirstChild("HumanoidRootPart")
    if not root then return nil end

    local best, minDist = nil, math.huge
    local targets = {}

    local npcFolder = workspace:FindFirstChild("NPCs")
    if npcFolder then targets = npcFolder:GetChildren() else
        for _, v in ipairs(workspace:GetChildren()) do if v:IsA("Model") then table.insert(targets, v) end end
    end

    for _, v in ipairs(targets) do
        if v ~= char then
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

-- Kill Counter
task.spawn(function()
    local f = workspace:FindFirstChild("NPCs") or workspace
    f.ChildRemoved:Connect(function(c)
        if State.TargetTags[c] then
            State.Kills = State.Kills + 1
            KillLbl.Text = "✦ " .. State.Kills
            State.TargetTags[c] = nil
        end
    end)
end)

-- Main Loop
State.IKConn = RunService.Heartbeat:Connect(function()
    if not Config.Active then
        StatLbl.Text = "⬡ System Idle"; StatLbl.TextColor3 = C.Sub
        return
    end

    if os.clock() - State.LastScan >= State.ScanDelay then
        State.CurrentBoss = GetBestBoss()
        State.LastScan = os.clock()
    end

    local boss = State.CurrentBoss
    if not boss or not boss:FindFirstChild("HumanoidRootPart") or boss:FindFirstChildOfClass("Humanoid").Health <= 0 then
        State.CurrentBoss = nil
        StatLbl.Text = "⬡ Scanning Boss..."; StatLbl.TextColor3 = C.Warn
        return
    end

    local bHum = boss:FindFirstChildOfClass("Humanoid")
    local bRoot = boss:FindFirstChild("HumanoidRootPart")
    local hpPct = (bHum.Health / bHum.MaxHealth) * 100

    StatLbl.Text = string.format("⚡ %s (%.1f%%)", boss.Name:sub(1,10), hpPct)
    StatLbl.TextColor3 = C.ON

    if hpPct <= Config.HPTrigger then
        State.TargetTags[boss] = true

        if os.clock() - State.LastAttack >= Config.AttackDelay then
            local targetPos = bRoot.Position

            -- HIT LOOP
            for i = 1, Config.HitMultiplier do
                -- Spam Ability (Slot 2) - Discovery from provided log
                if Config.UseAbility and State.AbilityRemote then
                    pcall(function() State.AbilityRemote:FireServer(2) end)
                end

                -- Spam M1
                if Config.UseM1 and State.M1Remote then
                    pcall(function() State.M1Remote:FireServer(targetPos) end)
                end
            end

            State.LastAttack = os.clock()
        end
    end
end)

print("[IK] V3 PRO Optimized Loaded!")
