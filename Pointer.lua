if not gg then
  print("This script must run inside GameGuardian")
  os.exit()
end

---------- CONFIGURATION ----------
local CONFIG = {
  MAX_POINTER_LEVEL = 4,
  SEARCH_DEPTH = 0x1000,
  DEFAULT_REGION = gg.REGION_JAVA_HEAP,
  ALLOWED_REGIONS = {
    gg.REGION_JAVA_HEAP,
    gg.REGION_JAVA,
    gg.REGION_C_HEAP,
    gg.REGION_ANONYMOUS
  },
  POINTER_SIZES = {
    [gg.TYPE_DWORD] = 4,
    [gg.TYPE_QWORD] = 8
  }
}

---------- UTILITIES ----------
local function hex(value)
  return string.format("0x%X", value)
end

local function formatMemory(value)
  if value < 1024 then
    return value .. " B"
  elseif value < 1024 * 1024 then
    return string.format("%.1f KB", value / 1024)
  else
    return string.format("%.1f MB", value / (1024 * 1024))
  end
end

local function getTypeName(type)
  local types = {
    [gg.TYPE_BYTE] = "BYTE",
    [gg.TYPE_WORD] = "WORD", 
    [gg.TYPE_DWORD] = "DWORD",
    [gg.TYPE_QWORD] = "QWORD",
    [gg.TYPE_FLOAT] = "FLOAT",
    [gg.TYPE_DOUBLE] = "DOUBLE"
  }
  return types[type] or "UNKNOWN"
end

---------- JAVA NATIVE ANALYSIS ----------
local JavaAnalyzer = {}

function JavaAnalyzer:new()
  local obj = {
    results = {},
    pointers = {},
    patterns = {},
    suggestions = {}
  }
  setmetatable(obj, {__index = self})
  return obj
end

-- Analyze memory structure around address
function JavaAnalyzer:analyzeAddress(address, depth)
  depth = depth or 3
  local analysis = {
    address = address,
    hexAddress = hex(address),
    nearbyPointers = {},
    valuePatterns = {},
    possibleOffsets = {},
    memoryContext = {}
  }
  
  -- Read memory around address
  local scanRange = 128
  local scanData = {}
  
  for i = -scanRange, scanRange, 4 do
    table.insert(scanData, {
      address = address + i,
      flags = gg.TYPE_DWORD
    })
  end
  
  if #scanData > 0 then
    scanData = gg.getValues(scanData)
    
    -- Find potential pointers (aligned addresses)
    for _, v in ipairs(scanData) do
      local offset = v.address - address
      local val = v.value
      
      -- Check if value looks like a pointer
      if val >= 0x10000 and val <= 0x7FFFFFFF then
        local isAligned = (val % 4 == 0 or val % 8 == 0)
        local distance = math.abs(val - address)
        
        if isAligned and distance < 0x1000000 then -- Within 16MB
          table.insert(analysis.nearbyPointers, {
            offset = offset,
            value = val,
            hexValue = hex(val),
            distance = distance,
            aligned = isAligned
          })
        end
      end
      
      -- Record value for pattern analysis
      if math.abs(offset) <= 64 then
        analysis.valuePatterns[offset] = {
          value = val,
          hex = hex(val)
        }
      end
    end
  end
  
  -- Detect memory region
  local success, region = pcall(function()
    local temp = {address = address, flags = gg.TYPE_DWORD}
    return gg.getValuesRange({temp})[1]
  end)
  
  if success and region then
    analysis.memoryContext.region = region
    
    if region == "Jh" or region == "J" then
      analysis.memoryContext.description = "Java Heap Region"
    elseif region == "Ch" or region == "Ca" then
      analysis.memoryContext.description = "C/C++ Heap Region"
    elseif region == "A" then
      analysis.memoryContext.description = "Anonymous Mapping"
    end
  end
  
  return analysis
end

-- Follow pointer chain
function JavaAnalyzer:followPointer(startAddress, maxLevel)
  maxLevel = maxLevel or CONFIG.MAX_POINTER_LEVEL
  local chain = {
    {address = startAddress, level = 0, value = nil}
  }
  
  local currentAddress = startAddress
  local visited = {}
  
  for level = 1, maxLevel do
    if visited[currentAddress] then break end
    visited[currentAddress] = true
    
    -- Try DWORD pointer first
    local ptrValue = gg.getValues({{address = currentAddress, flags = gg.TYPE_DWORD}})[1].value
    
    -- Check if it's a valid pointer
    if ptrValue >= 0x10000 and ptrValue <= 0x7FFFFFFF then
      -- Try to read at pointer address to verify
      local verify = pcall(function()
        local test = gg.getValues({{address = ptrValue, flags = gg.TYPE_DWORD}})
        return test[1]
      end)
      
      if verify then
        table.insert(chain, {
          address = ptrValue,
          level = level,
          from = currentAddress,
          offset = ptrValue - currentAddress,
          valid = true
        })
        currentAddress = ptrValue
      else
        break
      end
    else
      break
    end
  end
  
  return chain
end

-- Find common offsets from multiple addresses
function JavaAnalyzer:findCommonOffsets(addresses)
  if #addresses < 2 then return {} end
  
  local offsetMaps = {}
  
  -- Analyze each address
  for i, addr in ipairs(addresses) do
    offsetMaps[i] = {}
    local analysis = self:analyzeAddress(addr, 2)
    
    for offset, data in pairs(analysis.valuePatterns) do
      offsetMaps[i][offset] = data.value
    end
  end
  
  -- Find common offsets with same/similar values
  local commonOffsets = {}
  
  -- Compare first two to find base common offsets
  for offset, value1 in pairs(offsetMaps[1]) do
    local isCommon = true
    local values = {value1}
    
    for i = 2, #addresses do
      local value2 = offsetMaps[i][offset]
      if not value2 or math.abs(value1 - value2) > 100 then -- Allow small variations
        isCommon = false
        break
      end
      table.insert(values, value2)
    end
    
    if isCommon then
      -- Calculate average and check consistency
      local sum = 0
      for _, v in ipairs(values) do sum = sum + v end
      local avg = sum / #values
      
      local consistent = true
      for _, v in ipairs(values) do
        if math.abs(v - avg) > 10 then -- 10 unit tolerance
          consistent = false
          break
        end
      end
      
      if consistent then
        table.insert(commonOffsets, {
          offset = offset,
          averageValue = avg,
          hexValue = hex(avg),
          consistent = true,
          instanceCount = #addresses
        })
      end
    end
  end
  
  return commonOffsets
end

-- Generate code suggestions
function JavaAnalyzer:generateSuggestions(analysis)
  local suggestions = {}
  
  -- Suggestion 1: Direct offset from known pointer
  if #analysis.nearbyPointers > 0 then
    table.insert(suggestions, {
      type = "POINTER_OFFSET",
      confidence = "HIGH",
      description = "Use nearby pointer with offset",
      code = self:generatePointerCode(analysis.nearbyPointers[1], analysis.address)
    })
  end
  
  -- Suggestion 2: Multi-level pointer chain
  local chain = self:followPointer(analysis.address, 3)
  if #chain > 2 then
    table.insert(suggestions, {
      type = "POINTER_CHAIN",
      confidence = "MEDIUM",
      description = string.format("Multi-level pointer (%d levels)", #chain-1),
      code = self:generateChainCode(chain)
    })
  end
  
  -- Suggestion 3: Pattern-based offset
  local patterns = self:detectPatterns(analysis.valuePatterns)
  for _, pattern in ipairs(patterns) do
    table.insert(suggestions, {
      type = "PATTERN_OFFSET",
      confidence = pattern.confidence,
      description = pattern.description,
      code = self:generatePatternCode(pattern, analysis.address)
    })
  end
  
  return suggestions
end

function JavaAnalyzer:generatePointerCode(pointer, targetAddress)
  local offsetToTarget = targetAddress - pointer.value
  local offsetFromPointer = targetAddress - pointer.value
  
  return string.format([[
-- Pointer-based access
local basePointer = gg.getValues({{address = %s, flags = gg.TYPE_DWORD}})[1].value
local targetAddress = basePointer %s  -- Offset: %s
]], hex(pointer.value), 
   offsetToTarget >= 0 and ("+ " .. hex(offsetToTarget)) or ("- " .. hex(math.abs(offsetToTarget))),
   hex(offsetFromPointer))
end

function JavaAnalyzer:generateChainCode(chain)
  local code = "-- Multi-level pointer chain\n"
  code = code .. "local p0 = " .. hex(chain[1].address) .. "\n"
  
  for i = 2, #chain do
    local offset = chain[i].address - chain[i-1].address
    code = code .. string.format("local p%d = gg.getValues({{address = p%d, flags = gg.TYPE_DWORD}})[1].value\n", i-1, i-2)
    code = code .. string.format("-- Level %d -> %s (offset: %s)\n", i-1, hex(chain[i].address), 
           offset >= 0 and ("+" .. hex(offset)) : ("-" .. hex(math.abs(offset))))
  end
  
  return code
end

function JavaAnalyzer:detectPatterns(valuePatterns)
  local patterns = {}
  
  -- Look for common Java object patterns
  local commonJavaOffsets = {
    [-12] = "vtable pointer",
    [-8] = "class pointer", 
    [-4] = "hash/sync",
    [0] = "object header",
    [4] = "field 1",
    [8] = "field 2",
    [12] = "field 3",
    [16] = "field 4"
  }
  
  for offset, desc in pairs(commonJavaOffsets) do
    if valuePatterns[offset] then
      local val = valuePatterns[offset].value
      -- Check if value looks like pointer/object
      if val >= 0x10000 then
        table.insert(patterns, {
          offset = offset,
          description = "Java Object " .. desc,
          value = val,
          confidence = "MEDIUM",
          javaObject = true
        })
      end
    end
  end
  
  return patterns
end

function JavaAnalyzer:generatePatternCode(pattern, baseAddress)
  return string.format([[
-- Pattern-based access (Java Object)
local objectBase = %s  -- Base address
local fieldOffset = %s  -- %s
local fieldAddress = objectBase + fieldOffset
-- Expected value around: %s (%s)
]], hex(baseAddress + pattern.offset), 
   pattern.offset >= 0 and ("+" .. pattern.offset) : (tostring(pattern.offset)),
   pattern.description,
   pattern.value, hex(pattern.value))
end

---------- UI COMPONENTS ----------
local function showAnalysisDialog(analyzer, address)
  local analysis = analyzer:analyzeAddress(address)
  local suggestions = analyzer:generateSuggestions(analysis)
  
  local dialog = "📊 JAVA NATIVE ANALYSIS\n"
  dialog = dialog .. "═" .. string.rep("═", 50) .. "\n\n"
  dialog = dialog .. "📍 Target Address: " .. hex(address) .. "\n"
  
  if analysis.memoryContext.description then
    dialog = dialog .. "🏷️  Memory Region: " .. analysis.memoryContext.description .. "\n"
  end
  
  dialog = dialog .. "\n🔍 Nearby Pointers Found:\n"
  
  if #analysis.nearbyPointers > 0 then
    for i, ptr in ipairs(analysis.nearbyPointers) do
      if i <= 5 then -- Limit display
        dialog = dialog .. string.format("  • Offset %s → %s (distance: %s)\n", 
                 hex(ptr.offset), hex(ptr.value), formatMemory(ptr.distance))
      end
    end
  else
    dialog = dialog .. "  No clear pointers found nearby\n"
  end
  
  dialog = dialog .. "\n💡 Code Suggestions:\n"
  
  if #suggestions > 0 then
    for i, suggestion in ipairs(suggestions) do
      dialog = dialog .. string.format("\n[%d] %s (%s confidence)\n", 
               i, suggestion.description, suggestion.confidence)
      dialog = dialog .. "─" .. string.rep("─", 50) .. "\n"
      dialog = dialog .. suggestion.code .. "\n"
    end
  else
    dialog = dialog .. "  No automatic suggestions available\n"
  end
  
  -- Show raw values for manual analysis
  dialog = dialog .. "\n📋 Nearby Values (for manual analysis):\n"
  local count = 0
  for offset, data in pairs(analysis.valuePatterns) do
    if count < 10 then
      dialog = dialog .. string.format("  [%s]: %s (%d)\n", 
               hex(offset), data.hex, data.value)
      count = count + 1
    end
  end
  
  gg.alert(dialog)
  
  -- Offer to copy best suggestion
  if #suggestions > 0 then
    local choice = gg.choice({
      "📋 Copy Suggestion 1",
      "📋 Copy Suggestion 2",
      "📋 Copy Suggestion 3",
      "🔍 Analyze More Addresses",
      "🚫 Cancel"
    }, nil, "Select Action")
    
    if choice and choice <= 3 and suggestions[choice] then
      gg.copyText(suggestions[choice].code)
      gg.toast("✅ Code copied to clipboard!")
    elseif choice == 4 then
      return "analyze_more"
    end
  end
  
  return "done"
end

local function analyzeMultipleAddresses(analyzer)
  local results = gg.getResults(gg.getResultsCount())
  if #results == 0 then
    gg.alert("⚠️ No results in list.\n\nSearch for values first, then add them to results list.")
    return
  end
  
  local addresses = {}
  for _, r in ipairs(results) do
    table.insert(addresses, r.address)
  end
  
  gg.toast("🔍 Analyzing " .. #addresses .. " addresses...")
  
  -- Find common patterns
  local commonOffsets = analyzer:findCommonOffsets(addresses)
  
  local dialog = "🔗 MULTI-ADDRESS ANALYSIS\n"
  dialog = dialog .. "═" .. string.rep("═", 50) .. "\n\n"
  dialog = dialog .. "📊 Total Addresses: " .. #addresses .. "\n\n"
  
  if #commonOffsets > 0 then
    dialog = dialog .. "🎯 COMMON OFFSETS FOUND:\n"
    
    for _, offsetInfo in ipairs(commonOffsets) do
      dialog = dialog .. string.format("\nOffset: %s\n", hex(offsetInfo.offset))
      dialog = dialog .. string.format("Average Value: %s\n", offsetInfo.hexValue)
      dialog = dialog .. string.format("Consistent across: %d instances\n", offsetInfo.instanceCount)
      
      -- Generate code for this offset
      local sampleAddr = addresses[1]
      dialog = dialog .. "\nSample Code:\n"
      dialog = dialog .. string.format("local base = 0x%X\n", sampleAddr)
      dialog = dialog .. string.format("local commonValue = gg.getValues({{address = base %s, flags = gg.TYPE_DWORD}})[1].value\n",
               offsetInfo.offset >= 0 and ("+ " .. hex(offsetInfo.offset)) : ("- " .. hex(math.abs(offsetInfo.offset))))
      dialog = dialog .. string.format("-- Expected ~%s\n", offsetInfo.hexValue)
      dialog = dialog .. "─" .. string.rep("─", 30) .. "\n"
    end
  else
    dialog = dialog .. "⚠️ No common offsets found\n"
    dialog = dialog .. "Addresses may have different structures\n"
  end
  
  -- Show pointer chains for first few addresses
  dialog = dialog .. "\n🔗 POINTER CHAINS (first 3 addresses):\n"
  
  for i = 1, math.min(3, #addresses) do
    local chain = analyzer:followPointer(addresses[i], 3)
    if #chain > 1 then
      dialog = dialog .. string.format("\nAddress %d (%s):\n", i, hex(addresses[i]))
      for _, link in ipairs(chain) do
        if link.level == 0 then
          dialog = dialog .. string.format("  [L%d] BASE: %s\n", link.level, hex(link.address))
        else
          dialog = dialog .. string.format("  [L%d] → %s (from %s)\n", 
                   link.level, hex(link.address), hex(link.from))
        end
      end
    end
  end
  
  gg.alert(dialog)
  
  -- Offer to save analysis
  if #commonOffsets > 0 then
    local saveChoice = gg.choice({
      "💾 Save Common Offsets to File",
      "📋 Copy Best Code to Clipboard",
      "🔙 Back to Menu"
    }, nil, "Analysis Complete")
    
    if saveChoice == 1 then
      local timestamp = os.date("%Y%m%d_%H%M%S")
      local filename = "/sdcard/JavaAnalysis_" .. timestamp .. ".txt"
      local file = io.open(filename, "w")
      
      if file then
        file:write(dialog)
        file:close()
        gg.toast("✅ Analysis saved to: " .. filename)
      end
    elseif saveChoice == 2 and #commonOffsets > 0 then
      local code = string.format([[
-- Auto-generated Java Native Pointer Code
-- Generated: %s
-- Based on %d addresses

local targetAddress = 0x%X  -- Your target address

-- Common offset found: %s
local commonOffset = %s  -- %s

-- Access pattern:
local valueAtOffset = gg.getValues({
  {address = targetAddress + commonOffset, flags = gg.TYPE_DWORD}
})[1].value

-- Expected value around: %s
]], os.date("%Y-%m-%d %H:%M:%S"), #addresses, addresses[1],
       hex(commonOffsets[1].offset), 
       commonOffsets[1].offset >= 0 and ("0x" .. string.format("%X", commonOffsets[1].offset)) : ("-0x" .. string.format("%X", math.abs(commonOffsets[1].offset))),
       hex(commonOffsets[1].averageValue),
       hex(commonOffsets[1].averageValue))
      
      gg.copyText(code)
      gg.toast("✅ Code copied to clipboard!")
    end
  end
end

local function findPointerChains()
  local results = gg.getResults(gg.getResultsCount())
  if #results == 0 then
    gg.alert("Load some addresses first!")
    return
  end
  
  local analyzer = JavaAnalyzer:new()
  local allChains = {}
  
  gg.toast("🔗 Tracing pointer chains...")
  
  for i, r in ipairs(results) do
    if i <= 10 then -- Limit to first 10
      local chain = analyzer:followPointer(r.address, 4)
      if #chain > 1 then
        table.insert(allChains, {
          start = r.address,
          chain = chain,
          length = #chain
        })
      end
    end
  end
  
  if #allChains == 0 then
    gg.alert("No pointer chains found!")
    return
  end
  
  -- Display results
  local dialog = "🔗 POINTER CHAIN ANALYSIS\n"
  dialog = dialog .. "═" .. string.rep("═", 50) .. "\n\n"
  dialog = dialog .. "Found " .. #allChains .. " chains\n\n"
  
  for _, chainInfo in ipairs(allChains) do
    dialog = dialog .. string.format("Start: %s\n", hex(chainInfo.start))
    dialog = dialog .. string.format("Chain length: %d levels\n", chainInfo.length - 1)
    
    for _, link in ipairs(chainInfo.chain) do
      if link.level == 0 then
        dialog = dialog .. string.format("  [BASE] %s\n", hex(link.address))
      else
        local offset = link.address - link.from
        dialog = dialog .. string.format("  [L%d] %s ← %s (offset: %s)\n", 
                 link.level, hex(link.address), hex(link.from),
                 offset >= 0 and ("+" .. hex(offset)) : ("-" .. hex(math.abs(offset))))
      end
    end
    dialog = dialog .. "\n"
  end
  
  -- Find common chain patterns
  dialog = dialog .. "\n🎯 COMMON PATTERNS:\n"
  
  local offsetPatterns = {}
  for _, chainInfo in ipairs(allChains) do
    for i = 2, #chainInfo.chain do
      local offset = chainInfo.chain[i].address - chainInfo.chain[i-1].address
      offsetPatterns[offset] = (offsetPatterns[offset] or 0) + 1
    end
  end
  
  for offset, count in pairs(offsetPatterns) do
    if count > 1 then
      dialog = dialog .. string.format("Offset %s appears %d times\n", hex(offset), count)
    end
  end
  
  gg.alert(dialog)
end

local function generateAdvancedPointerCode()
  gg.alert([[🎯 ADVANCED POINTER CODE GENERATOR

This will help you create sophisticated pointer-chasing code for Java Native games.

Requirements:
1. Have multiple addresses loaded in results list
2. Addresses should be similar/related values
3. Game should be in same state for all addresses

The generator will:
1. Analyze memory patterns
2. Find common offsets
3. Generate verification code
4. Create multi-level pointer chains]])
  
  local results = gg.getResults(gg.getResultsCount())
  if #results < 2 then
    gg.alert("Need at least 2 addresses in results list!")
    return
  end
  
  local analyzer = JavaAnalyzer:new()
  
  -- Get user preferences
  local input = gg.prompt({
    "Max pointer levels (2-5):",
    "Include value verification?",
    "Generate error handling?"
  }, {"3", "✓", "✓"}, {"number", "checkbox", "checkbox"})
  
  if not input then return end
  
  local maxLevels = tonumber(input[1]) or 3
  local verifyValues = input[2]
  local errorHandling = input[3]
  
  -- Analyze first address as sample
  local sampleAddr = results[1].address
  local analysis = analyzer:analyzeAddress(sampleAddr)
  local chain = analyzer:followPointer(sampleAddr, maxLevels)
  
  -- Generate code
  local code = "-- Java Native Pointer Code Generator\n"
  code = code .. "-- Generated: " .. os.date("%Y-%m-%d %H:%M:%S") .. "\n"
  code = code .. string.format("-- Based on %d addresses\n", #results)
  code = code .. "\n"
  
  if errorHandling then
    code = code .. "local function safeRead(address, type)\n"
    code = code .. "  local success, result = pcall(function()\n"
    code = code .. "    return gg.getValues({{address = address, flags = type}})[1].value\n"
    code = code .. "  end)\n"
    code = code .. "  return success and result or nil\n"
    code = code .. "end\n\n"
  end
  
  code = code .. "-- Pointer chain structure\n"
  
  if #chain > 1 then
    code = code .. string.format("local baseAddress = 0x%X  -- Your target address\n\n", sampleAddr)
    code = code .. "-- Define pointer levels\n"
    
    for i, link in ipairs(chain) do
      if i == 1 then
        code = code .. string.format("local p%d = 0x%X  -- Base pointer\n", i-1, link.address)
      else
        local offset = link.address - link.from
        code = code .. string.format("-- Level %d (offset %s from p%d)\n", 
                 i-1, hex(offset), i-2)
        
        if errorHandling then
          code = code .. string.format("local p%d = safeRead(p%d, gg.TYPE_DWORD)\n", i-1, i-2)
          code = code .. string.format("if not p%d then\n", i-1)
          code = code .. string.format("  gg.toast('Failed at pointer level %d')\n", i-1)
          code = code .. "  return nil\n"
          code = code .. "end\n"
        else
          code = code .. string.format("local p%d = gg.getValues({{address = p%d, flags = gg.TYPE_DWORD}})[1].value\n", i-1, i-2)
        end
        
        if verifyValues and i < #chain then
          code = code .. string.format("-- Verify p%d is valid pointer\n", i-1)
          code = code .. string.format("if p%d < 0x10000 or p%d > 0x7FFFFFFF then\n", i-1, i-1)
          code = code .. string.format("  gg.toast('Invalid pointer at level %d')\n", i-1)
          code = code .. "  return nil\n"
          code = code .. "end\n"
        end
      end
    end
    
    code = code .. "\n-- Final target\n"
    code = code .. string.format("local finalPointer = p%d\n", #chain-1)
    code = code .. "gg.toast('Found pointer chain length: " .. (#chain-1) .. "')\n"
    
    -- Add nearby value checks
    if verifyValues then
      code = code .. "\n-- Verify with nearby values\n"
      local nearby = {}
      for offset, data in pairs(analysis.valuePatterns) do
        if math.abs(offset) <= 32 then
          table.insert(nearby, {offset = offset, value = data.value})
        end
      end
      
      if #nearby > 0 then
        code = code .. "local verificationPassed = true\n"
        for i = 1, math.min(3, #nearby) do
          local n = nearby[i]
          code = code .. string.format("local check%d = gg.getValues({{address = finalPointer %s, flags = gg.TYPE_DWORD}})[1].value\n",
                   i, n.offset >= 0 and ("+ " .. hex(n.offset)) : ("- " .. hex(math.abs(n.offset))))
          code = code .. string.format("if math.abs(check%d - %d) > 10 then\n", i, n.value)
          code = code .. string.format("  verificationPassed = false\n")
          code = code .. string.format("  gg.toast('Verification %d failed')\n", i)
          code = code .. "end\n"
        end
        code = code .. "\nif verificationPassed then\n"
        code = code .. "  gg.toast('✅ All verifications passed!')\n"
        code = code .. "else\n"
        code = code .. "  gg.toast('⚠️ Some verifications failed')\n"
        code = code .. "end\n"
      end
    end
    
  else
    code = code .. "-- No multi-level pointers found\n"
    code = code .. "-- Consider using offset-based approach instead\n"
  end
  
  -- Copy to clipboard
  gg.copyText(code)
  
  -- Show preview
  local preview = "✅ CODE GENERATED!\n\n"
  preview = preview .. "Code has been copied to clipboard.\n\n"
  preview = preview .. "Features included:\n"
  preview = preview .. "• " .. (#chain-1) .. "-level pointer chain\n"
  if errorHandling then preview = preview .. "• Error handling\n" end
  if verifyValues then preview = preview .. "• Value verification\n" end
  preview = preview .. "• Comments and structure\n\n"
  preview = preview .. "Paste into a new script to use."
  
  gg.alert(preview)
end

---------- MAIN MENU ----------
local function showMainMenu()
  local menu = {
    "🔍 Analyze Single Address",
    "📊 Analyze Multiple Addresses", 
    "🔗 Find Pointer Chains",
    "⚡ Generate Advanced Pointer Code",
    "📖 Java Native Memory Guide",
    "🚪 Exit"
  }
  
  while true do
    local choice = gg.choice(menu, nil, "🔬 JAVA NATIVE POINTER ANALYZER V1.0")
    
    if not choice then break end
    
    local analyzer = JavaAnalyzer:new()
    
    if choice == 1 then
      -- Analyze single address
      local results = gg.getResults(gg.getResultsCount())
      if #results == 0 then
        gg.alert("Load at least 1 address into results list!")
      else
        local addr = results[1].address
        showAnalysisDialog(analyzer, addr)
      end
      
    elseif choice == 2 then
      -- Analyze multiple addresses
      analyzeMultipleAddresses(analyzer)
      
    elseif choice == 3 then
      -- Find pointer chains
      findPointerChains()
      
    elseif choice == 4 then
      -- Generate advanced code
      generateAdvancedPointerCode()
      
    elseif choice == 5 then
      -- Show guide
      gg.alert([[📚 JAVA NATIVE MEMORY GUIDE

🎯 ABOUT JAVA NATIVE:
Java Native (JNI) games use a mix of:
• Java Heap Objects
• Native C/C++ memory
• JNI references and pointers

🔍 COMMON PATTERNS:
1. Object Headers (vtable pointers at -12 offset)
2. Class pointers at -8 offset  
3. Instance fields starting at +0 offset
4. Array length fields at -4 offset
5. String character arrays at +12 offset

💡 TIPS FOR ANALYSIS:
1. Java objects are usually in Jh (Java Heap) region
2. Look for aligned addresses (divisible by 4 or 8)
3. Pointer values are usually between 0x10000-0x7FFFFFFF
4. Object headers often contain vtable pointers

🎮 RECOMMENDED WORKFLOW:
1. Search for your value in GameGuardian
2. Add multiple instances to results list
3. Use "Analyze Multiple Addresses"
4. Look for common offsets
5. Generate pointer-chasing code
6. Test and refine

⚠️ CHALLENGES WITH JAVA NATIVE:
• Memory layout changes between runs
• Objects move in garbage collection
• Need pointer chains instead of fixed addresses
• Mix of Java and native pointers]])
      
    elseif choice == 6 then
      break
    end
  end
end

---------- SX BUTTON INTEGRATION ----------
local function setupSXButton()
  if gg.isVisible() then
    gg.setVisible(false)
  end
  
  -- Create SX button
  gg.setVisible(true)
  gg.clearResults()
  
  -- Show welcome message
  gg.alert([[
🚀 JAVA NATIVE POINTER ANALYZER V1.0

Designed specifically for Java Native games with:
• Dynamic memory layout
• Garbage collection
• Mixed Java/Native pointers
• Unstable addresses

Click the SX button to open the analyzer.
Add game addresses to results list first!]])
  
  -- Main loop with SX button
  local running = true
  
  while running do
    if gg.isClickedUiButton() then
      showMainMenu()
    end
    gg.sleep(100)
  end
end

---------- INITIALIZATION ----------
-- Check if we have results to analyze
gg.toast("🔬 Java Native Analyzer Loading...")

-- Auto-detect if we should analyze immediately
local resultCount = gg.getResultsCount()
if resultCount > 0 then
  local choice = gg.choice({
    "🎯 Analyze Current Results (" .. resultCount .. " addresses)",
    "📋 Open Main Menu",
    "🚫 Cancel"
  }, nil, "Java Native Analyzer Detected " .. resultCount .. " Addresses")
  
  if choice == 1 then
    local analyzer = JavaAnalyzer:new()
    if resultCount == 1 then
      local addr = gg.getResults(1)[1].address
      showAnalysisDialog(analyzer, addr)
    else
      analyzeMultipleAddresses(analyzer)
    end
  elseif choice == 2 then
    showMainMenu()
  end
else
  setupSXButton()
end

gg.toast("✅ Java Native Analyzer Ready!")