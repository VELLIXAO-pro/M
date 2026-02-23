require "import"
import "android.app.*"
import "android.os.*"
import "android.widget.*"
import "android.view.*"
import "android.content.*"
import "android.graphics.*"
import "android.graphics.drawable.*"
pcall(function() import "androidx.cardview.widget.CardView" end)
pcall(function() import "android.support.v7.widget.CardView" end)

local service = ...
local wm = service.getSystemService(Context.WINDOW_SERVICE)
local isConsoleVisible = false

math.randomseed(os.time())

-- Layouts
local float_layout = loadlayout(service.getLuaDir().."/float_layout.aly")
local console_layout = loadlayout(service.getLuaDir().."/console_layout.aly")

-- LayoutParams for Icon
local lp = WindowManager.LayoutParams()
if Build.VERSION.SDK_INT >= 26 then
  lp.type = WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY
else
  lp.type = WindowManager.LayoutParams.TYPE_PHONE
end
lp.format = PixelFormat.RGBA_8888
lp.flags = WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE
lp.gravity = Gravity.LEFT | Gravity.TOP
lp.width = WindowManager.LayoutParams.WRAP_CONTENT
lp.height = WindowManager.LayoutParams.WRAP_CONTENT
lp.x = 100
lp.y = 100

-- LayoutParams for Console
local clp = WindowManager.LayoutParams()
if Build.VERSION.SDK_INT >= 26 then
  clp.type = WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY
else
  clp.type = WindowManager.LayoutParams.TYPE_PHONE
end
clp.format = PixelFormat.RGBA_8888
clp.flags = WindowManager.LayoutParams.FLAG_NOT_TOUCH_MODAL
clp.gravity = Gravity.CENTER
clp.width = WindowManager.LayoutParams.MATCH_PARENT
clp.height = WindowManager.LayoutParams.MATCH_PARENT

-- Draggable Logic
local firstX, firstY, wmX, wmY
local isMoving = false

-- Assuming 'icon_image' is the ID in float_layout.aly
icon_image.onTouch = function(v, event)
  local action = event.getAction()
  if action == MotionEvent.ACTION_DOWN then
    firstX = event.getRawX()
    firstY = event.getRawY()
    wmX = lp.x
    wmY = lp.y
    isMoving = false
  elseif action == MotionEvent.ACTION_MOVE then
    if math.abs(event.getRawX() - firstX) > 10 or math.abs(event.getRawY() - firstY) > 10 then
      isMoving = true
      lp.x = wmX + (event.getRawX() - firstX)
      lp.y = wmY + (event.getRawY() - firstY)
      wm.updateViewLayout(float_layout, lp)
    end
  elseif action == MotionEvent.ACTION_UP then
    if not isMoving then
      toggleConsole()
    end
  end
  return true
end

function toggleConsole()
  if isConsoleVisible then
    wm.removeView(console_layout)
    isConsoleVisible = false
  else
    wm.addView(console_layout, clp)
    isConsoleVisible = true
  end
end

-- Close console logic (if there's a close button)
close_btn.onClick = function()
  toggleConsole()
end

-- Console Simulation Logic
function printToConsole(text, color)
  local textView = TextView(service)
  textView.setText(text)
  textView.setTextColor(color or Color.GREEN)
  textView.setTextSize(14)
  textView.setTypeface(Typeface.MONOSPACE)
  console_list.addView(textView)
  -- Auto scroll to bottom
  console_scroll.post(Runnable({
    run = function()
      console_scroll.fullScroll(ScrollView.FOCUS_DOWN)
    end
  }))
end

function randomString(length)
  local res = ""
  for i = 1, length do
    res = res .. string.char(math.random(65, 90))
  end
  return res
end

local isHacking = false

function startHacking()
  if isHacking then return end
  isHacking = true

  local sequence = {
    {text = "[*] Testing bug on target server...", delay = 1000},
    {text = "[+] Bug found! Vulnerability detected: CVE-2024-SAMURAI", delay = 1500, color = Color.YELLOW},
    {text = "[*] Checking authentication status...", delay = 1000},
    {text = "[+] Authenticated as: Administrator (root)", delay = 1200, color = Color.CYAN},
    {text = "[*] Sending exploit token...", delay = 800},
    {text = "[+] Token accepted by remote host.", delay = 1000, color = Color.GREEN},
    {text = "[*] Opening Paid Crack Tool v3.2...", delay = 1500},
    {text = "[!] Downloading resources...", delay = 500},
    {text = "[##########] 100% Download Complete", delay = 2000, color = Color.MAGENTA},
    {text = "[*] Hacking Platinum Status...", delay = 1500},
    {text = "[+] PAID TOKEN GENERATED: SAMURAI-" .. randomString(8) .. "-" .. randomString(4), delay = 1000, color = Color.parseColor("#FFD700")},
    {text = "[*] API Loading...", delay = 2000},
    {text = "[SUCCESS] Crack Paid Successful! Platinum Unlocked.", delay = 1000, color = Color.GREEN}
  }

  local index = 1
  local function runNext()
    if index <= #sequence then
      printToConsole(sequence[index].text, sequence[index].color)
      Handler().postDelayed(Runnable({
        run = function()
          index = index + 1
          runNext()
        end
      }), sequence[index].delay)
    else
      isHacking = false
      printToConsole("--------------------------------", Color.GRAY)
      printToConsole("Session completed.", Color.GRAY)
    end
  end

  runNext()
end

-- Console input handling
console_input.onEditorAction = function(v, actionId, event)
  if actionId == EditorInfo.IME_ACTION_DONE or actionId == EditorInfo.IME_ACTION_SEND then
    local cmd = tostring(console_input.getText())
    if cmd ~= "" then
      printToConsole("> " .. cmd, Color.WHITE)
      console_input.setText("")
      startHacking()
    end
    return true
  end
  return false
end

-- Start by showing the float icon
wm.addView(float_layout, lp)

-- Handle service destruction
function onDestroy()
  wm.removeView(float_layout)
  if isConsoleVisible then
    wm.removeView(console_layout)
  end
end
