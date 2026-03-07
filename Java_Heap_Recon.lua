if not gg then
  print("This script must run inside GameGuardian")
  os.exit()
end

---------- CONFIGURATION ----------
local CONFIG = {
  SEARCH_REGION = gg.REGION_JAVA_HEAP, -- Target: dalvik-main
  ALIGNMENT = 4, -- Standard 32-bit alignment for many Java objects
  SCAN_RANGE = 256, -- Scan 256 bytes around addresses
  MAX_SAMPLES = 10
}

---------- UTILITIES ----------
local function hex(value)
  if value == nil then return "N/A" end
  return string.format("0x%X", value)
end

---------- ADVANCED RECONNAISSANCE FUNCTIONS ----------

-- 1. Scan for Potential Object Headers (Aligned Addresses)
local function scanObjectHeaders(address)
  local start = address - (CONFIG.SCAN_RANGE / 2)
  local data = {}

  for i = 0, CONFIG.SCAN_RANGE, CONFIG.ALIGNMENT do
    table.insert(data, {address = start + i, flags = gg.TYPE_DWORD})
  end

  data = gg.getValues(data)
  local candidates = {}

  for _, v in ipairs(data) do
    -- Potential Class Pointer: 0x10000 - 0x7FFFFFFF range
    if v.value >= 0x10000 and v.value <= 0x7FFFFFFF then
      -- Simple heuristic: Class pointers are often reused across similar objects
      table.insert(candidates, v)
    end
  end

  return candidates
end

-- 2. Trace Pointer Chains (Pointer Chasing)
local function tracePointer(startAddress, levels)
  local current = startAddress
  local chain = {{address = current, value = nil}}

  for i = 1, levels do
    local val = gg.getValues({{address = current, flags = gg.TYPE_DWORD}})[1].value
    if val >= 0x10000 and val <= 0x7FFFFFFF then
      table.insert(chain, {address = val, from = current})
      current = val
    else
      break
    end
  end

  return chain
end

-- 3. Memory Snapshot & Comparison
local snapshot = nil
local function takeSnapshot()
  local results = gg.getResults(gg.getResultsCount())
  if #results == 0 then
    gg.alert("No results to snapshot. Search for values first.")
    return
  end

  snapshot = gg.getValues(results)
  gg.toast("📸 Snapshot taken for " .. #snapshot .. " addresses.")
end

local function compareSnapshot()
  if not snapshot then
    gg.alert("No snapshot found. Take a snapshot first.")
    return
  end

  local current = gg.getValues(snapshot)
  local changes = {}

  for i, res in ipairs(current) do
    if res.value ~= snapshot[i].value then
      table.insert(changes, {
        address = res.address,
        old = snapshot[i].value,
        new = res.value
      })
    end
  end

  local report = "🔄 SNAPSHOT COMPARISON\n"
  report = report .. "═" .. string.rep("═", 40) .. "\n"
  report = report .. "Changes detected: " .. #changes .. "\n\n"

  for i = 1, math.min(#changes, 10) do
    local c = changes[i]
    report = report .. string.format("[%s]: %d -> %d\n", hex(c.address), c.old, c.new)
  end

  gg.alert(report)
end

---------- MAIN MENU ----------
local function showMainMenu()
  local menu = {
    "🎯 Scan Headers near Address",
    "🔗 Trace Pointer Chain",
    "📸 Take Memory Snapshot",
    "🔄 Compare with Snapshot",
    "📖 Java Heap Recon Guide",
    "🚪 Exit"
  }

  while true do
    local choice = gg.choice(menu, nil, "🔍 JAVA HEAP RECON V1.0 (dalvik-main)")

    if not choice or choice == 6 then break end

    if choice == 1 then
      local results = gg.getResults(1)
      if #results > 0 then
        local candidates = scanObjectHeaders(results[1].address)
        local report = "Potential Headers Found:\n"
        for _, c in ipairs(candidates) do
          report = report .. hex(c.address) .. " -> " .. hex(c.value) .. "\n"
        end
        gg.alert(report)
      else
        gg.alert("Load an address into the results list first.")
      end
    elseif choice == 2 then
      local results = gg.getResults(1)
      if #results > 0 then
        local chain = tracePointer(results[1].address, 4)
        local report = "Pointer Chain:\n"
        for i, link in ipairs(chain) do
          report = report .. string.format("L%d: %s\n", i-1, hex(link.address))
        end
        gg.alert(report)
      else
        gg.alert("Load an address into the results list first.")
      end
    elseif choice == 3 then
      takeSnapshot()
    elseif choice == 4 then
      compareSnapshot()
    elseif choice == 5 then
      gg.alert([[📚 JAVA HEAP RECON GUIDE

Region 'dalvik-main' (Java Heap) berisi data mentah tanpa metadata biner (ELF/So).

TIPS ANALISIS:
1. HEADER SCANNING: Objek Java selalu rata (aligned) ke 4 atau 8 byte. Nilai pertama adalah class pointer.
2. POINTER CHASING: Data game sering kali bertingkat (nested). Cari alamat yang menunjuk ke alamat lain.
3. SNAPSHOT: Untuk menemukan bypass, bandingkan memori saat kondisi "Normal" vs "Detected" atau "Banned".
4. DYNAMIC OFFSETS: Karena Java menggunakan Garbage Collection, alamat objek sering berubah. Gunakan Pointer Chain untuk mendapatkan alamat yang stabil.]])
    end
  end
end

---------- INITIALIZATION ----------
gg.setVisible(false)
gg.setRanges(gg.REGION_JAVA_HEAP)
gg.toast("🎯 Java Heap Recon Active (dalvik-main focus)")
showMainMenu()
