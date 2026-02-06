require "import"
import "android.widget.*"
import "android.view.*"
import "android.content.Intent"
import "android.net.Uri"
import "layout" -- Import the layout.aly

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

-- Function: Start Game
function startGame()
    local pkg = edit_pkg.Text
    local intent = activity.getPackageManager().getLaunchIntentForPackage(pkg)
    if intent then
        activity.startActivity(intent)
        toast("Launching " .. pkg)
        -- Initialize memory tools for this package
        mem = MemoryTools.new(pkg)
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

    -- Update UI with results
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

-- Handle list item click (e.g. to edit single address)
list_results.onItemClick = function(parent, view, position, id)
    local itemStr = results_data[position + 1]
    local addrStr = itemStr:match("(0x%x+)")
    edit_write.Text = itemStr:match(": (%d+)")
    toast("Selected address: " .. addrStr)
end

toast("Samurai Injector Loaded")
