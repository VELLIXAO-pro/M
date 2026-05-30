--[[
    ⚡ InstaKill Standalone — Boss Only (V8.1 - STABLE SPOOFER)

    PERBAIKAN V8.1 (FINAL & STABLE):
    1. Damage Spoofing Stable: Mengirim klaim damage masif via Remote Ability (Slot 2).
    2. Rate Limiting: Ditambahkan cooldown antar burst agar tidak terkena KICK (Remote Spam).
    3. No Rubberband: Menghapus manipulasi CFrame/Posisi (Boss tidak akan berkedip).
    4. Isolation: Menjamin Karakter Player tidak tersentuh (Bisa Hit & Respawn Normal).
    5. Split UI V3: Tracker Boss + Panel Control minimalis.
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
    for _, v in pairs({ "IK_BossUI", "IK_BossUI_Fixed", "IK_BossUI_V2", "IK_BossUI_V3", "IK_BossUI_V4", "IK_BossUI_V5", "IK_V6_Main", "IK_V7_Main", "IK_V8_Main" }) do
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
    Active        = false,
    HPTrigger     = 80,
    BossMinHP     = 500000,
    Multiplier    = 15,    -- Jumlah klaim damage per burst
    BurstCooldown = 0.1,   -- Jeda antar burst (detik) untuk menghindari kick
}

local State = {
    LastAttack    = 0,
    LastScan      = 0,
    ScanDelay     = 0.5,
    CurrentBoss   = nil,
    IKConn        = nil,
    AbilityRemote = nil,
}

-- ══════════════════════════════════════════
--  REMOTE DETECTION
-- ══════════════════════════════════════════
task.spawn(function()
    while getgenv().IK_Running do
        if not State.AbilityRemote then
            local ab = RS:FindFirstChild("AbilitySystem")
            State.AbilityRemote = ab and ab:FindFirstChild("Remotes") and ab.Remotes:FindFirstChild("RequestAbility")
        end
        task.wait(2)
    end
end)

-- ══════════════════════════════════════════
--  GUI SETUP (STABLE MODE)
-- ══════════════════════════════════════════
local SG = Instance.new("ScreenGui")
SG.Name = "IK_V8_Main"; SG.ResetOnSpawn = false; SG.IgnoreGuiInset = true; SG.DisplayOrder = 999
if typeof(gethui) == "function" then SG.Parent = gethui() else SG.Parent = Plr:WaitForChild("PlayerGui") end

local C = {
    BG     = Color3.fromRGB(10, 10, 15),
    Accent = Color3.fromRGB(255, 200, 0), -- Gold State
    Text   = Color3.fromRGB(255, 255, 255),
    Dark   = Color3.fromRGB(5, 5, 10),
}

-- MINI TRACKER
local Tracker = Instance.new("Frame")
Tracker.Size = UDim2.new(0, 180, 0, 35); Tracker.Position = UDim2.new(0.5, -90, 0.02, 0); Tracker.BackgroundColor3 = C.BG; Tracker.Parent = SG
Instance.new("UICorner", Tracker).CornerRadius = UDim.new(0, 4); Instance.new("UIStroke", Tracker).Color = C.Accent

local BossLbl = Instance.new("TextLabel")
BossLbl.Text = "READY TO SPOOF"; BossLbl.Size = UDim2.new(1, 0, 1, 0); BossLbl.BackgroundTransparency = 1; BossLbl.TextColor3 = C.Accent; BossLbl.Font = Enum.Font.GothamBold; BossLbl.TextSize = 9; BossLbl.Parent = Tracker

-- CONTROL PANEL
local Panel = Instance.new("Frame")
Panel.Size = UDim2.new(0, 160, 0, 120); Panel.Position = UDim2.new(0, 10, 0.4, 0); Panel.BackgroundColor3 = C.BG; Panel.Visible = true; Panel.Parent = SG
Instance.new("UICorner", Panel).CornerRadius = UDim.new(0, 4); Instance.new("UIStroke", Panel).Color = C.Accent

local ToggleBtn = Instance.new("TextButton")
ToggleBtn.Text = "SYSTEM: OFF"; ToggleBtn.Size = UDim2.new(0.9, 0, 0, 30); ToggleBtn.Position = UDim2.new(0.05, 0, 0.1, 0); ToggleBtn.BackgroundColor3 = C.Dark; ToggleBtn.TextColor3 = Color3.new(0.5, 0.5, 0.5); ToggleBtn.Font = Enum.Font.GothamBold; ToggleBtn.TextSize = 10; ToggleBtn.Parent = Panel
Instance.new("UICorner", ToggleBtn)

local HPBox = Instance.new("TextBox")
HPBox.Text = tostring(Config.HPTrigger); HPBox.PlaceholderText = "TRIGGER HP %"; HPBox.Size = UDim2.new(0.9, 0, 0, 25); HPBox.Position = UDim2.new(0.05, 0, 0.4, 0); HPBox.BackgroundColor3 = C.Dark; HPBox.TextColor3 = C.Text; HPBox.Font = Enum.Font.GothamBold; HPBox.TextSize = 10; HPBox.Parent = Panel
Instance.new("UICorner", HPBox)

local MultBox = Instance.new("TextBox")
MultBox.Text = tostring(Config.Multiplier); MultBox.PlaceholderText = "BURST SIZE"; MultBox.Size = UDim2.new(0.9, 0, 0, 25); MultBox.Position = UDim2.new(0.05, 0, 0.65, 0); MultBox.BackgroundColor3 = C.Dark; MultBox.TextColor3 = C.Text; MultBox.Font = Enum.Font.GothamBold; MultBox.TextSize = 9; MultBox.Parent = Panel
Instance.new("UICorner", MultBox)

-- Button Actions
ToggleBtn.MouseButton1Click:Connect(function()
    Config.Active = not Config.Active
    ToggleBtn.Text = Config.Active and "SPOOFING: ACTIVE" or "SYSTEM: OFF"
    ToggleBtn.TextColor3 = Config.Active and C.Accent or Color3.new(0.5, 0.5, 0.5)
end)
HPBox.FocusLost:Connect(function() Config.HPTrigger = tonumber(HPBox.Text) or Config.HPTrigger; HPBox.Text = tostring(Config.HPTrigger) end)
MultBox.FocusLost:Connect(function() Config.Multiplier = tonumber(MultBox.Text) or Config.Multiplier; MultBox.Text = tostring(Config.Multiplier) end)

-- Dragging
local function MakeDraggable(f)
    local drag, dStart, sPos
    f.InputBegan:Connect(function(i) if i.UserInputType == Enum.UserInputType.MouseButton1 then drag = true; dStart = i.Position; sPos = f.Position; i.Changed:Connect(function() if i.UserInputState == Enum.UserInputState.End then drag = false end end) end end)
    UIS.InputChanged:Connect(function(i) if drag and i.UserInputType == Enum.UserInputType.MouseMovement then local delta = i.Position - dStart; f.Position = UDim2.new(p.X.Scale, p.X.Offset + delta.X, p.Y.Scale, p.Y.Offset + delta.Y) end end)
end
MakeDraggable(Tracker); MakeDraggable(Panel)

-- ══════════════════════════════════════════
--  CORE LOGIC (SERVER STATE CLAIM)
-- ══════════════════════════════════════════
local function GetBestBoss()
    local char = Plr.Character
    if not char then return nil end
    local root = char:FindFirstChild("HumanoidRootPart")
    if not root then return nil end

    local best, minDist = nil, math.huge
    local targets = (workspace:FindFirstChild("NPCs") and workspace.NPCs:GetChildren()) or workspace:GetChildren()

    for _, v in ipairs(targets) do
        if v:IsA("Model") and v ~= char and not Players:GetPlayerFromCharacter(v) then
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
        BossLbl.Text = "SYSTEM READY"; return
    end

    if os.clock() - State.LastScan >= State.ScanDelay then
        State.CurrentBoss = GetBestBoss()
        State.LastScan = os.clock()
    end

    local boss = State.CurrentBoss
    if not boss or not boss:FindFirstChild("HumanoidRootPart") then
        State.CurrentBoss = nil; BossLbl.Text = "SEARCHING BOSS..."; return
    end

    local bHum = boss:FindFirstChildOfClass("Humanoid")
    if not bHum or bHum.Health <= 0 then
        State.CurrentBoss = nil; return
    end

    local hpPct = (bHum.Health / bHum.MaxHealth) * 100
    BossLbl.Text = string.format("%s: %.1f%%", boss.Name:sub(1,10):upper(), hpPct)

    -- EXECUTION: Mengirim Klaim Damage ke Server
    if hpPct <= Config.HPTrigger then
        if State.AbilityRemote and (os.clock() - State.LastAttack >= Config.BurstCooldown) then
            State.LastAttack = os.clock()
            task.spawn(function()
                for i = 1, Config.Multiplier do
                    pcall(function()
                        State.AbilityRemote:FireServer(2)
                    end)
                end
            end)
        end
    end
end)

print("[IK] V8.1 Stable Spoofer Loaded. Rate Limiting Active.")
