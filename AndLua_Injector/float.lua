require "import"
import "android.widget.*"
import "android.view.*"
import "android.graphics.PixelFormat"
import "android.content.Context"
import "layout_float"

local MemoryTools = require "MemoryTools"

-- Service variables
local wm = activity.getSystemService(Context.WINDOW_SERVICE)
local lp = WindowManager.LayoutParams()
local is_menu_showing = false
local mem = nil

-- Load the floating UI
local float_view = loadlayout(layout_float)

-- Configure LayoutParams for floating icon
lp.type = WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY
lp.format = PixelFormat.RGBA_8888
lp.flags = WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE
lp.width = WindowManager.LayoutParams.WRAP_CONTENT
lp.height = WindowManager.LayoutParams.WRAP_CONTENT
lp.gravity = Gravity.LEFT | Gravity.TOP

-- Add the icon to window
wm.addView(float_view, lp)

-- Handle dragging
local lastX, lastY, startX, startY
icon_container.onTouch = function(v, event)
    local action = event.getAction()
    if action == MotionEvent.ACTION_DOWN then
        startX = event.getRawX()
        startY = event.getRawY()
        lastX = lp.x
        lastY = lp.y
    elseif action == MotionEvent.ACTION_MOVE then
        lp.x = lastX + (event.getRawX() - startX)
        lp.y = lastY + (event.getRawY() - startY)
        wm.updateViewLayout(float_view, lp)
    elseif action == MotionEvent.ACTION_UP then
        -- Toggle menu if it was a click (small movement)
        if math.abs(event.getRawX() - startX) < 10 and math.abs(event.getRawY() - startY) < 10 then
            toggleMenu()
        end
    end
    return true
end

function toggleMenu()
    if is_menu_showing then
        main_menu.setVisibility(View.GONE)
    else
        main_menu.setVisibility(View.VISIBLE)
    end
    is_menu_showing = not is_menu_showing
end

-- Initialize Memory Tools (Package name passed via Intent or shared state)
-- For this example, we'll retrieve it from a common place or use a default
local targetPackage = "com.asobimo.aurcusonline.wx"
mem = MemoryTools.new(targetPackage)

-- FEATURE: Plot Armor (8;2;0;65536;1:17)
switch_plot_armor.onCheckedChange = function(v, isChecked)
    if isChecked then
        print("Activating Plot Armor...")
        -- The pattern: 8;2;0;65536;1 within 17 bytes
        -- We focus on 65536 and change it to -1
        local values = {8, 2, 0, 65536, 1}
        local proximity = 17
        local targetVal = 65536
        local newVal = -1

        local count = mem:groupSearch(values, proximity)
        if count > 0 then
            local editCount = 0
            for _, res in ipairs(mem.results) do
                if res.value == targetVal then
                    mem:writeDword(res.address, newVal)
                    editCount = editCount + 1
                end
            end
            print("Plot Armor Active: Modified " .. editCount .. " values.")
        else
            print("Plot Armor Error: Values not found.")
            v.setChecked(false)
        end
    else
        print("Plot Armor Deactivated.")
    end
end

-- Close Button
btn_close_menu.onClick = function()
    toggleMenu()
end

print("Samurai Mod Menu Active")
