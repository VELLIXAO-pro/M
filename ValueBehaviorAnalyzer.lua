-- VALUE BEHAVIOR ANALYZER – JAVA HEAP EDITION
-- Author: Jules (AI Programmer)
-- Version: 1.0

if not gg then
  print("This script must run inside GameGuardian")
  os.exit()
end

---------- CONFIGURATION & STATE ----------
local STATE = {
  targetValue = nil,
  interval = 100,
  cycles = 20,
  onlyReal = false,
  results = {},
  monitoring = false
}

---------- UTILITIES ----------
local function hex(value)
  return string.format("0x%X", value)
end

---------- UI COMPONENTS ----------
local function showConfig()
  local input = gg.prompt({
    "Target Value (Number):",
    "Monitoring Interval (ms):",
    "Analysis Cycles (count):",
    "Show only REAL values?"
  }, {
    STATE.targetValue or "",
    tostring(STATE.interval),
    tostring(STATE.cycles),
    STATE.onlyReal
  }, {
    "number",
    "number",
    "number",
    "checkbox"
  })

  if not input then return false end

  STATE.targetValue = tonumber(input[1])
  STATE.interval = tonumber(input[2]) or 100
  STATE.cycles = tonumber(input[3]) or 20
  STATE.onlyReal = input[4]

  if not STATE.targetValue then
    gg.alert("⚠️ Target value is required!")
    return false
  end

  return true
end

local function classifyResults()
  if #STATE.results == 0 then return end

  local minCycle = 9999
  for _, data in ipairs(STATE.results) do
    if data.firstChangeCycle and data.firstChangeCycle < minCycle then
      minCycle = data.firstChangeCycle
    end
  end

  for _, data in ipairs(STATE.results) do
    if not data.firstChangeCycle then
      data.classification = "FAKE"
      data.label = "[FAKE]"
      data.description = "Value never changed"
    elseif data.firstChangeCycle == minCycle then
      data.classification = "REAL"
      data.label = "[REAL]"
      data.description = "Changed instantly"
    elseif data.firstChangeCycle <= minCycle + 2 then
      data.classification = "MIRROR"
      data.label = "[MIRROR]"
      data.description = string.format("Delayed by %d cycles", data.firstChangeCycle - minCycle)
    else
      data.classification = "MIRROR"
      data.label = "[MIRROR]"
      data.description = string.format("Significant delay (%d cycles)", data.firstChangeCycle - minCycle)
    end
  end
end

local function runAnalysis()
  local results = gg.getResults(gg.getResultsCount())
  if #results == 0 then
    gg.alert("⚠️ No addresses in the results list. Please search for a value first!")
    return
  end

  gg.toast("⏳ Initializing analysis for " .. #results .. " addresses...")

  local monitoringData = {}
  for i, r in ipairs(results) do
    monitoringData[i] = {
      address = r.address,
      flags = r.flags,
      initialValue = r.value,
      history = {},
      changeCount = 0,
      firstChangeCycle = nil,
      lastValue = r.value
    }
  end

  gg.toast("🚀 Monitoring started. Change the value in game NOW!")

  for cycle = 1, STATE.cycles do
    local values = gg.getValues(results)
    local anyChanged = false

    for i, v in ipairs(values) do
      local data = monitoringData[i]
      if v.value ~= data.lastValue then
        data.changeCount = data.changeCount + 1
        if not data.firstChangeCycle then
          data.firstChangeCycle = cycle
        end
        data.lastValue = v.value
        anyChanged = true
      end
      table.insert(data.history, v.value)
    end

    gg.toast(string.format("Monitoring: %d/%d cycles", cycle, STATE.cycles))
    gg.sleep(STATE.interval)
  end

  STATE.results = monitoringData
  classifyResults()
  gg.toast("✅ Classification complete!")
end

local function showResults()
  if #STATE.results == 0 then
    gg.alert("No results to display. Run analysis first!")
    return
  end

  local summary = "📊 ANALYSIS RESULTS\n"
  summary = summary .. string.rep("━", 30) .. "\n"

  local counts = {REAL = 0, MIRROR = 0, FAKE = 0}
  local details = ""

  for _, data in ipairs(STATE.results) do
    counts[data.classification] = counts[data.classification] + 1

    local shouldShow = true
    if STATE.onlyReal and data.classification ~= "REAL" then
      shouldShow = false
    end

    if shouldShow then
      details = details .. string.format("%s %s → %s\n",
        data.label, hex(data.address), data.description)
    end
  end

  summary = summary .. string.format("REAL: %d | MIRROR: %d | FAKE: %d\n",
    counts.REAL, counts.MIRROR, counts.FAKE)
  summary = summary .. string.format("Total Analyzed: %d\n", #STATE.results)
  summary = summary .. string.rep("━", 30) .. "\n\n"
  summary = summary .. (details ~= "" and details or "No values matched your filter.")

  gg.alert(summary)

  -- Result Management Options
  local options = {
    "📋 Copy Results to Clipboard",
    "🎯 Keep Only REAL Values in List",
    "💾 Save to File (/sdcard/ValueAnalysis.txt)",
    "🔙 Back to Menu"
  }
  local choice = gg.choice(options, nil, "RESULT MANAGEMENT")

  if choice == 1 then
    gg.copyText(summary)
    gg.toast("✅ Results copied to clipboard!")
  elseif choice == 2 then
    local realResults = {}
    for _, data in ipairs(STATE.results) do
      if data.classification == "REAL" then
        table.insert(realResults, {address = data.address, flags = data.flags})
      end
    end
    if #realResults > 0 then
      gg.clearResults()
      gg.addResults(realResults)
      gg.toast(string.format("✅ Kept %d REAL values in results list", #realResults))
    else
      gg.toast("⚠️ No REAL values found to keep.")
    end
  elseif choice == 3 then
    local file = io.open("/sdcard/ValueAnalysis.txt", "w")
    if file then
      file:write(summary)
      file:close()
      gg.toast("✅ Saved to /sdcard/ValueAnalysis.txt")
    else
      gg.toast("❌ Failed to save file.")
    end
  end

  return summary
end

local function showMainMenu()
  while true do
    local menu = {
      "⚙️ Configure Analyzer",
      "🚀 Run Behavior Analysis",
      "📋 View Last Results",
      "🚪 Exit"
    }
    local choice = gg.choice(menu, nil, "🔬 VALUE BEHAVIOR ANALYZER\nRegion: Java Heap (ART)")

    if not choice then break end

    if choice == 1 then
      showConfig()
    elseif choice == 2 then
      if STATE.targetValue then
        runAnalysis()
        showResults()
      else
        if showConfig() then
          runAnalysis()
          showResults()
        end
      end
    elseif choice == 3 then
      showResults()
    elseif choice == 4 then
      os.exit()
    end
  end
end

---------- INITIALIZATION ----------
gg.setVisible(false)
gg.setRanges(gg.REGION_JAVA_HEAP)
showMainMenu()
