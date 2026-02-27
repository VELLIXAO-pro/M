if not gg then
  print("This script must run inside GameGuardian")
  os.exit()
end

---------- CONFIGURATION ----------
local CONFIG = {
  TITLE = "🧮 OFFSET CALCULATOR V1.0",
  AUTHOR = "SAMURAI TOOLS",
  REGION = gg.REGION_ANONYMOUS
}

---------- UI ----------
local function hex(value)
  return string.format("0x%X", value)
end

local function calculate()
  local input = gg.prompt({
    "Base Address (Hex):",
    "Target Address (Hex):"
  }, {"", ""}, {"text", "text"})

  if not input then return end

  local base = tonumber(input[1], 16)
  local target = tonumber(input[2], 16)

  if not base or not target then
    gg.alert("Invalid Hex input!")
    return
  end

  local offset = target - base
  local result = "📊 CALCULATION RESULT\n"
  result = result .. "═" .. string.rep("═", 30) .. "\n\n"
  result = result .. "Base: " .. hex(base) .. "\n"
  result = result .. "Target: " .. hex(target) .. "\n"
  result = result .. "Offset: " .. (offset >= 0 and "+" or "-") .. hex(math.abs(offset)) .. "\n\n"
  result = result .. "Lua Code:\n"
  result = result .. "local address = base + " .. hex(offset)

  gg.alert(result)
  gg.copyText(hex(offset))
  gg.toast("Offset copied to clipboard!")
end

---------- MAIN ----------
gg.alert("Welcome to " .. CONFIG.TITLE .. "\nBy " .. CONFIG.AUTHOR)
while true do
  local menu = gg.choice({
    "🧮 Calculate Offset",
    "📋 Copy Last Result",
    "🚪 Exit"
  }, nil, CONFIG.TITLE)

  if not menu then break end
  if menu == 1 then calculate() end
  if menu == 2 then gg.toast("Nothing to copy yet") end
  if menu == 3 then break end
end
