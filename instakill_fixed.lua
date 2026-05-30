--[[
    ⚡ InstaKill Standalone — Boss Only (V4 - ULTIMATE VOID EDITION)

    METODE BARU (PENTING):
    1. Void Kill: Memindahkan boss langsung ke Void (Y = -5000). Boss mati instan tanpa hit.
    2. Reward Mode: Gunakan "HitSpam" jika ingin hadiah/XP (Membutuhkan Hit).
    3. Split UI Pro: UI terpisah antara Setting dan Status Bar (Mini Mode).
    4. Ability Booster: Skill 2 otomatis terpakai di mode HitSpam.
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
    Method        = "HitSpam",   -- "HitSpam" (Bisa Reward) atau "VoidKill" (Sangat Cepat)
    HPTrigger     = 80,          -- Diatur ke 80% default agar player punya kesempatan hit
    BossMinHP     = 500000,
    HitMultiplier = 10,
    AttackDelay   = 0.05,
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
    UI_Mini       = false,
}

-- ══════════════════════════════════════════
--  REMOTE DETECTION
-- ══════════════════════════════════════════
task.spawn(function()
    while getgenv().IK_Running do
        if not State.M1Remote then
            local cs = RS:FindFirstChild("CombatSystem")
            State.M1Remote = cs and cs:FindFirstChild("Remotes") and cs.Remotes:FindFirstChild("RequestHit")
        end
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
SG.Name           = "IK_BossUI_V4"
SG.ResetOnSpawn   = false
SG.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
SG.IgnoreGuiInset = true
SG.DisplayOrder   = 999

-- Cleanup
for _, v in pairs({ "IK_BossUI", "IK_BossUI_Fixed", "IK_BossUI_V2", "IK_BossUI_V3", "IK_BossUI_V4" }) do
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

-- ────────────────────────────────
--  MAIN SETTINGS FRAME
-- ────────────────────────────────
local Main = Instance.new("Frame")
Main.Name = "SettingsFrame"
Main.Size = UDim2.new(0, 210, 0, 310)
Main.Position = UDim2.new(0.5, -105, 0.2, 0)
Main.BackgroundColor3 = C.BG; Main.BorderSizePixel = 0
Main.Parent = SG
Instance.new("UICorner", Main).CornerRadius = UDim.new(0, 8)
Instance.new("UIStroke", Main).Color = C.Border

-- Header
local Header = Instance.new("Frame")
Header.Size = UDim2.new(1, 0, 0, 30)
Header.BackgroundColor3 = C.Header; Header.BorderSizePixel = 0; Header.Parent = Main
Instance.new("UICorner", Header).CornerRadius = UDim.new(0, 8)

local TLbl = Instance.new("TextLabel")
TLbl.Text = "⚡ InstaKill V4 - Ultimate"
TLbl.Size = UDim2.new(1, -60, 1, 0); TLbl.Position = UDim2.new(0, 10, 0, 0)
TLbl.BackgroundTransparency = 1; TLbl.TextColor3 = C.Text; TLbl.Font = Enum.Font.GothamBold; TLbl.TextSize = 11; TLbl.TextXAlignment = Enum.TextXAlignment.Left; TLbl.Parent = Header

local CloseBtn = Instance.new("TextButton")
CloseBtn.Text = "✕"; CloseBtn.Size = UDim2.new(0, 24, 0, 20); CloseBtn.Position = UDim2.new(1, -27, 0.5, -10)
CloseBtn.BackgroundColor3 = C.Danger; CloseBtn.TextColor3 = Color3.new(1,1,1); CloseBtn.Font = Enum.Font.GothamBold; CloseBtn.Parent = Header
Instance.new("UICorner", CloseBtn).CornerRadius = UDim.new(0, 5)

local Cont = Instance.new("Frame")
Cont.Size = UDim2.new(1, 0, 1, -30); Cont.Position = UDim2.new(0, 0, 0, 30); Cont.BackgroundTransparency = 1; Cont.Parent = Main
local ULL = Instance.new("UIListLayout", Cont); ULL.Padding = UDim.new(0, 5); ULL.HorizontalAlignment = Enum.HorizontalAlignment.Center
local UPad = Instance.new("UIPadding", Cont); UPad.PaddingTop = UDim.new(0, 8); UPad.PaddingLeft = UDim.new(0, 10); UPad.PaddingRight = UDim.new(0, 10)

-- UI Rows
local function CreateRow(lbl, configKey, ph, order)
    local f = Instance.new("Frame"); f.Size = UDim2.new(1, 0, 0, 26); f.BackgroundTransparency = 1; f.LayoutOrder = order; f.Parent = Cont
    local l = Instance.new("TextLabel"); l.Text = lbl; l.Size = UDim2.new(0.5, 0, 1, 0); l.BackgroundTransparency = 1; l.TextColor3 = C.Sub; l.TextSize = 10; l.Font = Enum.Font.Gotham; l.TextXAlignment = Enum.TextXAlignment.Left; l.Parent = f
    local b = Instance.new("TextBox"); b.Text = tostring(Config[configKey]); b.PlaceholderText = ph; b.Size = UDim2.new(0.45, 0, 0, 20); b.Position = UDim2.new(0.55, 0, 0, 3); b.BackgroundColor3 = C.Input; b.TextColor3 = Color3.fromRGB(255, 210, 80); b.Font = Enum.Font.GothamBold; b.TextSize = 10; b.BorderSizePixel = 0; b.Parent = f
    Instance.new("UICorner", b).CornerRadius = UDim.new(0, 5)
    b.FocusLost:Connect(function() local v = tonumber(b.Text); if v then Config[configKey] = v end; b.Text = tostring(Config[configKey]) end)
end

-- Toggles
local IKBtn = Instance.new("TextButton")
IKBtn.Text = "SYSTEM OFF"; IKBtn.Size = UDim2.new(1, 0, 0, 32); IKBtn.BackgroundColor3 = C.OFF; IKBtn.TextColor3 = C.Sub; IKBtn.Font = Enum.Font.GothamBold; IKBtn.TextSize = 11; IKBtn.Parent = Cont
Instance.new("UICorner", IKBtn).CornerRadius = UDim.new(0, 6)

-- Method Selector
local MethodBtn = Instance.new("TextButton")
MethodBtn.Text = "MODE: HitSpam (Reward)"; MethodBtn.Size = UDim2.new(1, 0, 0, 26); MethodBtn.BackgroundColor3 = C.Accent; MethodBtn.TextColor3 = Color3.new(1,1,1); MethodBtn.Font = Enum.Font.GothamBold; MethodBtn.TextSize = 10; MethodBtn.Parent = Cont
Instance.new("UICorner", MethodBtn).CornerRadius = UDim.new(0, 5)

MethodBtn.MouseButton1Click:Connect(function()
    if Config.Method == "HitSpam" then
        Config.Method = "VoidKill"
        MethodBtn.Text = "MODE: VoidKill (Instan)"
        MethodBtn.BackgroundColor3 = C.Danger
    else
        Config.Method = "HitSpam"
        MethodBtn.Text = "MODE: HitSpam (Reward)"
        MethodBtn.BackgroundColor3 = C.Accent
    end
end)

CreateRow("HP Trigger %", "HPTrigger", "1-100", 1)
CreateRow("Boss MinHP", "BossMinHP", "HP", 2)
CreateRow("Hit Multiplier", "HitMultiplier", "Loop", 3)

local DescLbl = Instance.new("TextLabel")
DescLbl.Text = "VoidKill: Boss mati instan tapi pemain tidak dapat hadiah.\nHitSpam: Menyerang boss sampai mati (Bisa dapat hadiah)."; DescLbl.Size = UDim2.new(1, 0, 0, 45); DescLbl.BackgroundTransparency = 1; DescLbl.TextColor3 = C.Sub; DescLbl.TextSize = 8; DescLbl.Font = Enum.Font.Gotham; DescLbl.TextWrapped = true; DescLbl.Parent = Cont

-- ────────────────────────────────
--  SPLIT STATUS BAR (MINI MODE)
-- ────────────────────────────────
local MiniFrame = Instance.new("Frame")
MiniFrame.Name = "MiniStatusBar"
MiniFrame.Size = UDim2.new(0, 180, 0, 35)
MiniFrame.Position = UDim2.new(1, -190, 0.8, 0)
MiniFrame.BackgroundColor3 = C.Input; MiniFrame.BorderSizePixel = 0; MiniFrame.Parent = SG
Instance.new("UICorner", MiniFrame).CornerRadius = UDim.new(0, 8)
Instance.new("UIStroke", MiniFrame).Color = C.Accent

local StatLbl = Instance.new("TextLabel")
StatLbl.Size = UDim2.new(1, -10, 1, 0); StatLbl.Position = UDim2.new(0, 5, 0, 0)
StatLbl.Text = "⬡ Idle"; StatLbl.BackgroundTransparency = 1; StatLbl.TextColor3 = C.Sub; StatLbl.TextSize = 9; StatLbl.Font = Enum.Font.Gotham; StatLbl.Parent = MiniFrame

local MiniToggle = Instance.new("TextButton")
MiniToggle.Text = "❐ Settings"; MiniToggle.Size = UDim2.new(1, 0, 0, 20); MiniToggle.Position = UDim2.new(0, 0, -1, -5)
MiniToggle.BackgroundColor3 = C.Header; MiniToggle.TextColor3 = C.Text; MiniToggle.Font = Enum.Font.GothamBold; MiniToggle.TextSize = 10; MiniToggle.Parent = MiniFrame
Instance.new("UICorner", MiniToggle).CornerRadius = UDim.new(0, 5)

MiniToggle.MouseButton1Click:Connect(function()
    Main.Visible = not Main.Visible
end)

-- ══════════════════════════════════════════
--  UI LOGIC
-- ══════════════════════════════════════════
IKBtn.MouseButton1Click:Connect(function()
    Config.Active = not Config.Active
    IKBtn.Text = Config.Active and "SYSTEM ON" or "SYSTEM OFF"
    IKBtn.BackgroundColor3 = Config.Active and C.ON or C.OFF
    IKBtn.TextColor3 = Config.Active and Color3.new(1,1,1) or C.Sub
end)

CloseBtn.MouseButton1Click:Connect(function()
    getgenv().IK_Running = false
    if State.IKConn then State.IKConn:Disconnect() end
    SG:Destroy()
end)

-- Drag logic for Settings & Mini Frame
local function MakeDraggable(f)
    local drag, dStart, sPos
    f.InputBegan:Connect(function(i) if i.UserInputType == Enum.UserInputType.MouseButton1 or i.UserInputType == Enum.UserInputType.Touch then drag = true; dStart = i.Position; sPos = f.Position; i.Changed:Connect(function() if i.UserInputState == Enum.UserInputState.End then drag = false end end) end end)
    UIS.InputChanged:Connect(function(i) if drag and (i.UserInputType == Enum.UserInputType.MouseMovement or i.UserInputType == Enum.UserInputType.Touch) then local delta = i.Position - dStart; f.Position = UDim2.new(sPos.X.Scale, sPos.X.Offset + delta.X, sPos.Y.Scale, sPos.Y.Offset + delta.Y) end end)
end
MakeDraggable(Main); MakeDraggable(MiniFrame)

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
        State.CurrentBoss = nil; StatLbl.Text = "⬡ Scanning Boss..."; StatLbl.TextColor3 = C.Warn
        return
    end

    local bHum = boss:FindFirstChildOfClass("Humanoid")
    local bRoot = boss:FindFirstChild("HumanoidRootPart")
    local hpPct = (bHum.Health / bHum.MaxHealth) * 100

    StatLbl.Text = string.format("⚡ [%s] %s: %.1f%%", Config.Method, boss.Name:sub(1,8), hpPct)
    StatLbl.TextColor3 = C.ON

    if hpPct <= Config.HPTrigger then
        if Config.Method == "VoidKill" then
            -- METODE VOID: Sangat cepat, tapi server mungkin tidak mencatat reward
            pcall(function()
                bRoot.CFrame = CFrame.new(bRoot.Position.X, -5000, bRoot.Position.Z)
            end)
        else
            -- METODE HITSPAM: Menyerang lewat Remote agar server menganggap kamu pembunuhnya (Dapat Reward)
            if os.clock() - State.LastAttack >= Config.AttackDelay then
                local targetPos = bRoot.Position
                for i = 1, Config.HitMultiplier do
                    if State.AbilityRemote then pcall(function() State.AbilityRemote:FireServer(2) end) end
                    if State.M1Remote then pcall(function() State.M1Remote:FireServer(targetPos) end) end
                end
                State.LastAttack = os.clock()
            end
        end
    end
end)

print("[IK] V4 Ultimate Void Edition Loaded!")
