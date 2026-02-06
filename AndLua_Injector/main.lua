require "import"
import "android.widget.*"
import "android.view.*"
import "android.content.Intent"
import "android.net.Uri"
import "android.provider.Settings"
import "layout"

local MemoryTools = require "MemoryTools"

-- Set the main UI
activity.setContentView(loadlayout(layout))

local mem = nil
local results_data = {}
local adapter = nil

-- Initialize ListView adapter
adapter = ArrayAdapter(activity, android.R.layout.simple_list_item_1, results_data)
list_results.setAdapter(adapter)

-- Helper: Show Toast
function toast(msg)
    Toast.makeText(activity, msg, Toast.LENGTH_SHORT).show()
end

-- Check Overlay Permission
function checkOverlayPermission()
    if Build.VERSION.SDK_INT >= 23 then
        if not Settings.canDrawOverlays(activity) then
            local intent = Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION)
            intent.setData(Uri.parse("package:" .. activity.getPackageName()))
            activity.startActivityForResult(intent, 123)
            toast("Please allow overlay permission for Mod Menu")
            return false
        end
    end
    return true
end

-- Function: Start Game & Mod Menu
function startGame()
    local pkg = edit_pkg.Text

    -- Check permissions first
    if not checkOverlayPermission() then return end

    local intent = activity.getPackageManager().getLaunchIntentForPackage(pkg)
    if intent then
        -- Start Game
        activity.startActivity(intent)
        toast("Launching " .. pkg)

        -- Start Mod Menu Service
        -- In AndLua+, we use LuaService to run a script as a service
        -- Typically: activity.startService(Intent(activity, LuaService.byte).putExtra("luaPath", "float.lua"))
        -- But for simplicity in this script, we'll assume standard AndLua+ service call
        local serviceIntent = Intent()
        serviceIntent.setClassName(activity.getPackageName(), "com.androlua.LuaService")
        serviceIntent.putExtra("luaPath", activity.getLuaPath("float.lua"))
        activity.startService(serviceIntent)

        toast("Mod Menu Active")
    else
        toast("Package not found: " .. pkg)
    end
end

-- Button: Start
btn_start.onClick = function()
    startGame()
end

-- Button: Search
btn_search.onClick = function()
    if not mem then
        local pkg = edit_pkg.Text
        mem = MemoryTools.new(pkg)
    end

    local val = edit_search.Text
    if val == "" then
        toast("Please enter a value to search")
        return
    end

    toast("Searching in Java Heap...")
    local count = mem:search(val)

    results_data = {}
    for i, res in ipairs(mem.results) do
        table.insert(results_data, string.format("0x%X : %d", res.address, res.value))
    end

    adapter = ArrayAdapter(activity, android.R.layout.simple_list_item_1, results_data)
    list_results.setAdapter(adapter)

    toast("Found " .. count .. " results")
end

-- Button: Write All
btn_write.onClick = function()
    if not mem or #mem.results == 0 then
        toast("No results to write")
        return
    end

    local newVal = tonumber(edit_write.Text)
    if not newVal then
        toast("Enter a valid number to write")
        return
    end

    for _, res in ipairs(mem.results) do
        mem:writeDword(res.address, newVal)
    end
    toast("Wrote " .. #mem.results .. " values")
end

-- Button: Clear
btn_clear.onClick = function()
    if mem then mem.results = {} end
    results_data = {}
    adapter = ArrayAdapter(activity, android.R.layout.simple_list_item_1, results_data)
    list_results.setAdapter(adapter)
    toast("Results cleared")
end

-- Handle list item click
list_results.onItemClick = function(parent, view, position, id)
    local itemStr = results_data[position + 1]
    local addrStr = itemStr:match("(0x%x+)")
    edit_write.Text = itemStr:match(": (%d+)")
    toast("Selected address: " .. addrStr)
end

toast("Samurai Injector Loaded")
