require "import"
import "android.widget.*"
import "android.view.*"
import "android.graphics.*"
import "android.content.*"
import "android.app.*"
import "android.os.Build"

-- Layout for float
float_layout = import "float_layout"

-- Use service context if activity is nil
local ctx = activity or service
windowManager = ctx.getSystemService(Context.WINDOW_SERVICE)
params = WindowManager.LayoutParams()

if Build.VERSION.SDK_INT >= 26 then
  params.type = WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY
else
  params.type = WindowManager.LayoutParams.TYPE_PHONE
end

params.format = PixelFormat.RGBA_8888
params.flags = WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE
params.gravity = Gravity.LEFT | Gravity.TOP
params.width = WindowManager.LayoutParams.WRAP_CONTENT
params.height = WindowManager.LayoutParams.WRAP_CONTENT

-- Load the floating view
mainView = loadlayout(float_layout)
windowManager.addView(mainView, params)

-- Dragging logic
local startX, startY, startRawX, startRawY
mainView.onTouch = function(v, event)
  if event.action == MotionEvent.ACTION_DOWN then
    startX = params.x
    startY = params.y
    startRawX = event.getRawX()
    startRawY = event.getRawY()
  elseif event.action == MotionEvent.ACTION_MOVE then
    params.x = startX + (event.getRawX() - startRawX)
    params.y = startY + (event.getRawY() - startRawY)
    windowManager.updateViewLayout(mainView, params)
  end
  return false
end

-- Toggle Menu Visibility
local menuVisible = true
btn_icon.onClick = function()
  if menuVisible then
    menu_container.setVisibility(View.GONE)
    menuVisible = false
  else
    menu_container.setVisibility(View.VISIBLE)
    menuVisible = true
  end
end

-- Mod Logic Placeholder
-- Target: com.asobimo.aurcusonline.wx
-- Region: Java_Heap (dalvik-main)

function editMemory(name, hexSearch, offset, value)
  Toast.makeText(ctx, "Mencari " .. name .. " di dalvik-main...", Toast.LENGTH_SHORT).show()

  -- Skenario: Menggunakan shell (debug/run-as) atau libMemory internal
  -- Karena kita menggunakan metode shareuid/debug, kita bisa mengakses memory
  -- via /proc/[pid]/mem jika memiliki ijin yang tepat.

  -- IMPLEMENTASI NYATA DISINI:
  -- local pid = getPid("com.asobimo.aurcusonline.wx")
  -- searchAndWrite(pid, hexSearch, offset, value, "Jh")

  Toast.makeText(activity, "Berhasil Edit: " .. name, Toast.LENGTH_SHORT).show()
end

-- Menu Buttons
item1.onClick = function()
  -- Contoh penggunaan
  editMemory("Mod Damage", "h 08 00 00 00 ...", 28, 99999)
end

item2.onClick = function()
  editMemory("Mod Speed", "h 0C 00 00 00 ...", 32, 1000)
end

-- Close Button
btn_close.onClick = function()
  windowManager.removeView(mainView)
  service.stopSelf()
end
