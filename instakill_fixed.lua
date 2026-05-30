--[[
    ⚡ InstaKill Standalone — Boss Only (V7 - GHOST EXECUTIONER)

    PERBAIKAN V7 (ZERO PLAYER IMPACT):
    1. Player Isolation: Script 100% tidak akan menyentuh atau memodifikasi karakter player.
    2. Clean Void: Memindahkan boss ke koordinat ekstrim tanpa mengubah Humanoid State (Mencegah karakter terkunci).
    3. Input Transparency: UI didesain agar tidak memblokir klik mouse (Bisa Hit M1 seperti biasa).
    4. Auto-Filter: Menjamin script hanya menargetkan NPC/Boss di folder NPCs atau Workspace.
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
    for _, v in pairs({ "IK_BossUI", "IK_BossUI_Fixed", "IK_BossUI_V2", "IK_BossUI_V3", "IK_BossUI_V4", "IK_BossUI_V5", "IK_V6_Main", "IK_V7_Main" }) do
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
    ScanDelay     = 0.5,
    CurrentBoss   = nil,
    IKConn        = nil,
}

-- ══════════════════════════════════════════
--  GUI SETUP (GHOST MODE)
-- ══════════════════════════════════════════
local SG = Instance.new("ScreenGui")
SG.Name = "IK_V7_Main"; SG.ResetOnSpawn = false; SG.IgnoreGuiInset = true; SG.DisplayOrder = 999
if typeof(gethui) == "function" then SG.Parent = gethui() else SG.Parent = Plr:WaitForChild("PlayerGui") end

local C = {
    BG     = Color3.fromRGB(12, 12, 12),
    Accent = Color3.fromRGB(0, 255, 180), -- Teal Ghost Color
    Text   = Color3.fromRGB(240, 240, 240),
    Dark   = Color3.fromRGB(5, 5, 5),
}

-- FLOATING TRACKER (Mini)
local Tracker = Instance.new("Frame")
Tracker.Size = UDim2.new(0, 160, 0, 35); Tracker.Position = UDim2.new(0.5, -80, 0.02, 0); Tracker.BackgroundColor3 = C.BG; Tracker.Parent = SG
Instance.new("UICorner", Tracker).CornerRadius = UDim.new(0, 6); Instance.new("UIStroke", Tracker).Color = C.Accent

local BossLbl = Instance.new("TextLabel")
BossLbl.Text = "SYSTEM IDLE"; BossLbl.Size = UDim2.new(1, 0, 1, 0); BossLbl.BackgroundTransparency = 1; BossLbl.TextColor3 = C.Accent; BossLbl.Font = Enum.Font.GothamBold; BossLbl.TextSize = 9; BossLbl.Parent = Tracker

-- SETTINGS PANEL (Small)
local Panel = Instance.new("Frame")
Panel.Size = UDim2.new(0, 150, 0, 110); Panel.Position = UDim2.new(0, 10, 0.4, 0); Panel.BackgroundColor3 = C.BG; Panel.Visible = true; Panel.Parent = SG
Instance.new("UICorner", Panel).CornerRadius = UDim.new(0, 6); Instance.new("UIStroke", Panel).Color = C.Accent

local ToggleBtn = Instance.new("TextButton")
ToggleBtn.Text = "GHOST: OFF"; ToggleBtn.Size = UDim2.new(0.85, 0, 0, 28); ToggleBtn.Position = UDim2.new(0.075, 0, 0.1, 0); ToggleBtn.BackgroundColor3 = C.Dark; ToggleBtn.TextColor3 = Color3.new(0.5, 0.5, 0.5); ToggleBtn.Font = Enum.Font.GothamBold; ToggleBtn.TextSize = 10; ToggleBtn.Parent = Panel
Instance.new("UICorner", ToggleBtn)

local HPBox = Instance.new("TextBox")
HPBox.Text = tostring(Config.HPTrigger); HPBox.PlaceholderText = "HP %"; HPBox.Size = UDim2.new(0.85, 0, 0, 25); HPBox.Position = UDim2.new(0.075, 0, 0.4, 0); HPBox.BackgroundColor3 = C.Dark; HPBox.TextColor3 = C.Text; HPBox.Font = Enum.Font.GothamBold; HPBox.TextSize = 10; HPBox.Parent = Panel
Instance.new("UICorner", HPBox)

local CloseBtn = Instance.new("TextButton")
CloseBtn.Text = "SHUTDOWN"; CloseBtn.Size = UDim2.new(0.85, 0, 0, 25); CloseBtn.Position = UDim2.new(0.075, 0, 0.7, 0); CloseBtn.BackgroundColor3 = Color3.fromRGB(30, 0, 0); CloseBtn.TextColor3 = C.Text; CloseBtn.Font = Enum.Font.GothamBold; CloseBtn.TextSize = 9; CloseBtn.Parent = Panel
Instance.new("UICorner", CloseBtn)

-- Functions UI
ToggleBtn.MouseButton1Click:Connect(function()
    Config.Active = not Config.Active
    ToggleBtn.Text = Config.Active and "GHOST: ACTIVE" or "GHOST: OFF"
    ToggleBtn.TextColor3 = Config.Active and C.Accent or Color3.new(0.5, 0.5, 0.5)
end)
HPBox.FocusLost:Connect(function() Config.HPTrigger = tonumber(HPBox.Text) or Config.HPTrigger; HPBox.Text = tostring(Config.HPTrigger) end)
CloseBtn.MouseButton1Click:Connect(function() getgenv().IK_Running = false; if State.IKConn then State.IKConn:Disconnect() end; SG:Destroy() end)

-- Draggable
local function MakeDraggable(f)
    local drag, dStart, sPos
    f.InputBegan:Connect(function(i) if i.UserInputType == Enum.UserInputType.MouseButton1 then drag = true; dStart = i.Position; sPos = f.Position; i.Changed:Connect(function() if i.UserInputState == Enum.UserInputState.End then drag = false end end) end end)
    UIS.InputChanged:Connect(function(i) if drag and i.UserInputType == Enum.UserInputType.MouseMovement then local delta = i.Position - dStart; f.Position = UDim2.new(sPos.X.Scale, sPos.X.Offset + delta.X, sPos.Y.Scale, sPos.Y.Offset + delta.Y) end end)
end
MakeDraggable(Tracker); MakeDraggable(Panel)

-- ══════════════════════════════════════════
--  CORE LOGIC (HITLESS & GHOST)
-- ══════════════════════════════════════════
local function GetBestBoss()
    local myChar = Plr.Character
    if not myChar then return nil end

    local root = myChar:FindFirstChild("HumanoidRootPart")
    if not root then return nil end

    local best, minDist = nil, math.huge
    local targets = (workspace:FindFirstChild("NPCs") and workspace.NPCs:GetChildren()) or workspace:GetChildren()

    for _, v in ipairs(targets) do
        -- ISOLASI: Pastikan target BUKAN player
        if v:IsA("Model") and v ~= myChar and not Players:GetPlayerFromCharacter(v) then
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
        BossLbl.Text = "GHOST SYSTEM: READY"; return
    end

    if os.clock() - State.LastScan >= State.ScanDelay then
        State.CurrentBoss = GetBestBoss()
        State.LastScan = os.clock()
    end

    local boss = State.CurrentBoss
    if not boss or not boss:FindFirstChild("HumanoidRootPart") then
        State.CurrentBoss = nil; BossLbl.Text = "WAITING BOSS..."; return
    end

    local bHum = boss:FindFirstChildOfClass("Humanoid")
    local bRoot = boss:FindFirstChild("HumanoidRootPart")
    if not bHum or bHum.Health <= 0 then
        State.CurrentBoss = nil; return
    end

    local hpPct = (bHum.Health / bHum.MaxHealth) * 100
    BossLbl.Text = string.format("%s: %.1f%%", boss.Name:sub(1,10):upper(), hpPct)

    -- EXECUTION: Hanya pada model boss
    if hpPct <= Config.HPTrigger then
        pcall(function()
            -- Metode Void yang tidak memodifikasi Humanoid (Agar karakter player tidak terkunci)
            bRoot.CFrame = CFrame.new(bRoot.Position.X, -100000, bRoot.Position.Z)
        end)
    end
end)

print("[IK] V7 Ghost Executioner Loaded. Zero Player Modification.")
