--[[
    ⚡ InstaKill Standalone — Boss Only (V6.1 - INVISIBLE EXECUTIONER)

    METODE PURE INSTAKILL (TANPA HIT/SKILL):
    1. Hitless Execution: Menggunakan Physics Manipulation & State Change.
    2. Zero Interaction: Karakter diam, tidak memukul, tidak pakai skill.
    3. Reward Friendly: Aktifkan di 80% HP agar Anda sempat hit manual untuk hadiah.
    4. Remote Sync: Menggunakan data 'BossUIUpdate' dari server untuk akurasi HP.
    5. True Split UI: Tracker mini yang elegan & Panel Setting terpisah.
--]]

-- ══════════════════════════════════════════
--  GUARD & SERVICES
-- ══════════════════════════════════════════
if getgenv().IK_Running then
    warn("[IK] Script V6 sudah berjalan!")
    return
end
getgenv().IK_Running = true

local Players    = game:GetService("Players")
local RunService = game:GetService("RunService")
local UIS        = game:GetService("UserInputService")
local RS         = game:GetService("ReplicatedStorage")
local Plr        = Players.LocalPlayer

-- ══════════════════════════════════════════
--  CLEANUP
-- ══════════════════════════════════════════
local function CleanUI()
    for _, v in pairs({ "IK_BossUI", "IK_BossUI_Fixed", "IK_BossUI_V2", "IK_BossUI_V3", "IK_BossUI_V4", "IK_BossUI_V5", "IK_V6_Tracker", "IK_V6_Panel", "IK_V6_Main" }) do
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
    ServerHP      = 100, -- HP dari Remote Server
    UsingServerHP = false,
}

-- ══════════════════════════════════════════
--  GUI SETUP (TRUE SPLIT MODE)
-- ══════════════════════════════════════════
local SG = Instance.new("ScreenGui")
SG.Name = "IK_V6_Main"; SG.ResetOnSpawn = false; SG.IgnoreGuiInset = true; SG.DisplayOrder = 999
if typeof(gethui) == "function" then SG.Parent = gethui() else SG.Parent = Plr:WaitForChild("PlayerGui") end

local C = {
    BG     = Color3.fromRGB(15, 15, 20),
    Accent = Color3.fromRGB(255, 60, 60),
    Text   = Color3.fromRGB(240, 240, 240),
    Dark   = Color3.fromRGB(10, 10, 15),
    Green  = Color3.fromRGB(50, 255, 120),
}

-- 1. FLOATING BOSS TRACKER
local Tracker = Instance.new("Frame")
Tracker.Name = "IK_V6_Tracker"; Tracker.Size = UDim2.new(0, 200, 0, 45); Tracker.Position = UDim2.new(0.5, -100, 0.05, 0); Tracker.BackgroundColor3 = C.BG; Tracker.Parent = SG
Instance.new("UICorner", Tracker).CornerRadius = UDim.new(0, 8); Instance.new("UIStroke", Tracker).Color = C.Accent

local BossNameLbl = Instance.new("TextLabel")
BossNameLbl.Text = "WAITING FOR BOSS..."; BossNameLbl.Size = UDim2.new(1, 0, 0.5, 0); BossNameLbl.BackgroundTransparency = 1; BossNameLbl.TextColor3 = C.Text; BossNameLbl.Font = Enum.Font.GothamBold; BossNameLbl.TextSize = 10; BossNameLbl.Parent = Tracker

local HPBarBG = Instance.new("Frame")
HPBarBG.Size = UDim2.new(0.85, 0, 0, 6); HPBarBG.Position = UDim2.new(0.075, 0, 0.7, 0); HPBarBG.BackgroundColor3 = C.Dark; HPBarBG.Parent = Tracker
Instance.new("UICorner", HPBarBG)

local HPFill = Instance.new("Frame")
HPFill.Size = UDim2.new(0, 0, 1, 0); HPFill.BackgroundColor3 = C.Accent; HPFill.Parent = HPBarBG
Instance.new("UICorner", HPFill)

-- 2. CONFIG PANEL
local Panel = Instance.new("Frame")
Panel.Name = "IK_V6_Panel"; Panel.Size = UDim2.new(0, 180, 0, 140); Panel.Position = UDim2.new(0, 20, 0.4, 0); Panel.BackgroundColor3 = C.BG; Panel.Visible = true; Panel.Parent = SG
Instance.new("UICorner", Panel).CornerRadius = UDim.new(0, 8); Instance.new("UIStroke", Panel).Color = C.Accent

local PHeader = Instance.new("TextLabel")
PHeader.Text = "EXECUTIONER SETTINGS"; PHeader.Size = UDim2.new(1, 0, 0, 25); PHeader.BackgroundTransparency = 1; PHeader.TextColor3 = C.Accent; PHeader.Font = Enum.Font.GothamBold; PHeader.TextSize = 9; PHeader.Parent = Panel

local ToggleBtn = Instance.new("TextButton")
ToggleBtn.Text = "SYSTEM: OFF"; ToggleBtn.Size = UDim2.new(0.9, 0, 0, 30); ToggleBtn.Position = UDim2.new(0.05, 0, 0.25, 0); ToggleBtn.BackgroundColor3 = C.Dark; ToggleBtn.TextColor3 = Color3.new(0.6, 0.6, 0.6); ToggleBtn.Font = Enum.Font.GothamBold; ToggleBtn.TextSize = 10; ToggleBtn.Parent = Panel
Instance.new("UICorner", ToggleBtn)

local HPInputF = Instance.new("Frame"); HPInputF.Size = UDim2.new(0.9, 0, 0, 25); HPInputF.Position = UDim2.new(0.05, 0, 0.55, 0); HPInputF.BackgroundTransparency = 1; HPInputF.Parent = Panel
local HPLbl = Instance.new("TextLabel"); HPLbl.Text = "HP Trigger %:"; HPLbl.Size = UDim2.new(0.6, 0, 1, 0); HPLbl.BackgroundTransparency = 1; HPLbl.TextColor3 = Color3.new(0.8,0.8,0.8); HPLbl.Font = Enum.Font.Gotham; HPLbl.TextSize = 10; HPLbl.TextXAlignment = Enum.TextXAlignment.Left; HPLbl.Parent = HPInputF
local HPBox = Instance.new("TextBox"); HPBox.Text = tostring(Config.HPTrigger); HPBox.Size = UDim2.new(0.35, 0, 1, 0); HPBox.Position = UDim2.new(0.65, 0, 0, 0); HPBox.BackgroundColor3 = C.Dark; HPBox.TextColor3 = C.Green; HPBox.Font = Enum.Font.GothamBold; HPBox.TextSize = 11; HPBox.Parent = HPInputF
Instance.new("UICorner", HPBox)

local CloseBtn = Instance.new("TextButton")
CloseBtn.Text = "CLOSE SCRIPT"; CloseBtn.Size = UDim2.new(0.9, 0, 0, 25); CloseBtn.Position = UDim2.new(0.05, 0, 0.8, 0); CloseBtn.BackgroundColor3 = Color3.fromRGB(40, 10, 10); CloseBtn.TextColor3 = C.Text; CloseBtn.Font = Enum.Font.GothamBold; CloseBtn.TextSize = 9; CloseBtn.Parent = Panel
Instance.new("UICorner", CloseBtn)

local SplitBtn = Instance.new("TextButton")
SplitBtn.Text = "⚙️"; SplitBtn.Size = UDim2.new(0, 25, 0, 25); SplitBtn.Position = UDim2.new(1, 5, 0, 0); SplitBtn.BackgroundColor3 = C.BG; SplitBtn.TextColor3 = C.Text; SplitBtn.Parent = Tracker
Instance.new("UICorner", SplitBtn); Instance.new("UIStroke", SplitBtn).Color = C.Accent

SplitBtn.MouseButton1Click:Connect(function() Panel.Visible = not Panel.Visible end)
CloseBtn.MouseButton1Click:Connect(function() getgenv().IK_Running = false; if State.IKConn then State.IKConn:Disconnect() end; SG:Destroy() end)
ToggleBtn.MouseButton1Click:Connect(function()
    Config.Active = not Config.Active
    ToggleBtn.Text = Config.Active and "SYSTEM: ACTIVE" or "SYSTEM: OFF"
    ToggleBtn.TextColor3 = Config.Active and C.Green or Color3.new(0.6, 0.6, 0.6)
end)
HPBox.FocusLost:Connect(function() Config.HPTrigger = tonumber(HPBox.Text) or Config.HPTrigger; HPBox.Text = tostring(Config.HPTrigger) end)

local function MakeDraggable(f)
    local dragStart, startPos, dragging
    f.InputBegan:Connect(function(input) if input.UserInputType == Enum.UserInputType.MouseButton1 then dragging = true; dragStart = input.Position; startPos = f.Position; input.Changed:Connect(function() if input.UserInputState == Enum.UserInputState.End then dragging = false end end) end end)
    UIS.InputChanged:Connect(function(input) if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then local delta = input.Position - dragStart; f.Position = UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y) end end)
end
MakeDraggable(Tracker); MakeDraggable(Panel)

-- ══════════════════════════════════════════
--  CORE LOGIC (HITLESS)
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

-- SYNC HP WITH SERVER (From your provided Log)
local function SyncBossStatus()
    local rem = RS:FindFirstChild("Remotes") and RS.Remotes:FindFirstChild("BossUIUpdate")
    if rem then
        rem.OnClientEvent:Connect(function(mode, data)
            if mode == "Health" and data and data.max and data.current then
                State.ServerHP = (data.current / data.max) * 100
                State.UsingServerHP = true
            end
        end)
    end
end
task.spawn(SyncBossStatus)

State.IKConn = RunService.Heartbeat:Connect(function()
    if not Config.Active then
        BossNameLbl.Text = "SYSTEM IDLE"; HPFill.Size = UDim2.new(0,0,1,0); State.UsingServerHP = false
        return
    end

    if os.clock() - State.LastScan >= State.ScanDelay then
        State.CurrentBoss = GetBestBoss()
        State.LastScan = os.clock()
    end

    local boss = State.CurrentBoss
    if not boss or not boss:FindFirstChild("HumanoidRootPart") then
        State.CurrentBoss = nil; BossNameLbl.Text = "SEARCHING BOSS..."; HPFill.Size = UDim2.new(0,0,1,0); State.UsingServerHP = false
        return
    end

    local bHum = boss:FindFirstChildOfClass("Humanoid")
    local bRoot = boss:FindFirstChild("HumanoidRootPart")

    local hpPct = State.UsingServerHP and State.ServerHP or (bHum and (bHum.Health / bHum.MaxHealth) * 100) or 0

    if hpPct <= 0 then
        State.CurrentBoss = nil; State.UsingServerHP = false; return
    end

    BossNameLbl.Text = string.format("%s (%.1f%%)", boss.Name:upper(), hpPct)
    HPFill.Size = UDim2.new(math.clamp(hpPct/100, 0, 1), 0, 1, 0)

    if hpPct <= Config.HPTrigger then
        -- EXECUTION (VOID METHOD)
        pcall(function()
            bRoot.CFrame = CFrame.new(bRoot.Position.X, -50000, bRoot.Position.Z)
            bRoot.Velocity = Vector3.new(0, -1000, 0)
        end)
        -- STATE KILL (CLIENT)
        pcall(function()
            if bHum then bHum.Health = 0; bHum:ChangeState(Enum.HumanoidStateType.Dead) end
        end)
    end
end)

print("[IK] V6.1 Executioner Loaded. Remote Sync Active.")
