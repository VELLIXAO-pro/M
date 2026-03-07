if not gg then
  print("This script must run inside GameGuardian")
  os.exit()
end

---------- CONFIGURATION ----------
local CONFIG = {
  MONITOR_INTERVAL = 500, -- milliseconds
  MAX_RESULTS_TO_DISPLAY = 20
}

---------- UTILITIES ----------
local function hex(value)
  if value == nil then return "N/A" end
  return string.format("0x%X", value)
end

---------- MEMORY ANALYSIS FUNCTIONS ----------

-- 1. Select Memory Regions
local function selectMemoryRegions()
  local regions = {
    {name = "Java Heap (Jh)", flag = gg.REGION_JAVA_HEAP},
    {name = "Java (J)", flag = gg.REGION_JAVA},
    {name = "C++ Heap (Ch)", flag = gg.REGION_C_HEAP},
    {name = "Anonymous (A)", flag = gg.REGION_ANONYMOUS}
  }

  local names = {}
  for _, r in ipairs(regions) do
    table.insert(names, r.name)
  end

  local choice = gg.choice(names, nil, "Select Target Memory Region for Analysis")
  if not choice then return nil end

  gg.toast("Selected region: " .. regions[choice].name)
  return regions[choice].flag
end

-- 2. Display and Analyze Current Results
local function analyzeResults()
  local count = gg.getResultsCount()
  if count == 0 then
    gg.alert("No results in list. Please perform a search first.")
    return
  end

  local results = gg.getResults(CONFIG.MAX_RESULTS_TO_DISPLAY)
  results = gg.getValues(results)

  local report = "📊 CURRENT MEMORY RESULTS (First " .. #results .. ")\n"
  report = report .. "═" .. string.rep("═", 40) .. "\n"

  for i, res in ipairs(results) do
    report = report .. string.format("[%d] %s: %d (%s)\n", i, hex(res.address), res.value, hex(res.value))
  end

  gg.alert(report)
end

-- 3. Monitor Specific Addresses for Changes
local function startMonitoring()
  local count = gg.getResultsCount()
  if count == 0 then
    gg.alert("Nothing to monitor. Search and add items to the results list first.")
    return
  end

  local results = gg.getResults(gg.getResultsCount())
  local lastValues = {}

  -- Initialize last values
  local initial = gg.getValues(results)
  for _, res in ipairs(initial) do
    lastValues[res.address] = res.value
  end

  gg.toast("👁️ Monitoring started for " .. #results .. " addresses...")

  while true do
    if gg.isVisible() then
      gg.setVisible(false)
      local stop = gg.choice({"Continue Monitoring", "Stop Monitoring"}, nil, "Monitoring active...")
      if stop == 2 then break end
    end

    local current = gg.getValues(results)
    for _, res in ipairs(current) do
      if lastValues[res.address] ~= res.value then
        gg.toast(string.format("🔔 Change: %s -> %d", hex(res.address), res.value))
        lastValues[res.address] = res.value
      end
    end

    gg.sleep(CONFIG.MONITOR_INTERVAL)
  end

  gg.toast("🛑 Monitoring stopped.")
end

---------- MAIN MENU ----------
local function showMainMenu()
  local menu = {
    "🌐 Select Memory Regions",
    "🔍 Analyze Current Results",
    "👁️ Start Monitoring Changes",
    "🚪 Exit"
  }

  while true do
    local choice = gg.choice(menu, nil, "🔬 ADVANCED MEMORY ANALYZER TEMPLATE")

    if not choice or choice == 4 then break end

    if choice == 1 then
      selectMemoryRegions()
    elseif choice == 2 then
      analyzeResults()
    elseif choice == 3 then
      startMonitoring()
    end
  end
end

---------- INITIALIZATION ----------
gg.toast("🔬 Memory Analyzer Template Ready!")
showMainMenu()
