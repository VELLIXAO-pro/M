-- FilterOffset.lua
-- Script to find 10080 surrounded by pointer-like (encrypted) values at offsets -8, -4, 4, 8

function main()
    gg.clearResults()
    -- Set search range to Java Heap as seen in the screenshot
    gg.setRanges(gg.REGION_JAVA_HEAP)

    gg.toast("Searching for 10080...")
    gg.searchNumber("10080", gg.TYPE_DWORD)
    local count = gg.getResultCount()

    if count == 0 then
        gg.alert("Value 10080 not found in Java Heap!")
        return
    end

    local results = gg.getResults(count)
    local keep = {}

    gg.toast("Analyzing " .. count .. " results...")

    for i, res in ipairs(results) do
        local check_offsets = {-8, -4, 4, 8}
        local values_to_check = {}

        for _, offset in ipairs(check_offsets) do
            table.insert(values_to_check, {address = res.address + offset, flags = gg.TYPE_DWORD})
        end

        local values = gg.getValues(values_to_check)
        local is_match = true

        for _, v in ipairs(values) do
            -- Criteria for "encrypted" (pointer) based on Pointer.lua and visual analysis
            -- Pointer range: 0x10000 to 0x7FFFFFFF (65536 to 2147483647)
            local val = v.value
            if type(val) == "string" then
                val = tonumber(val:match("^-?%d+"))
            end

            if not val or val < 65536 or val > 2147483647 then
                is_match = false
                break
            end
        end

        if is_match then
            table.insert(keep, res)
        end
    end

    gg.clearResults()
    if #keep > 0 then
        -- Use loadResults instead of addResults for compatibility with some GG versions
        gg.loadResults(keep)
        gg.alert("Found " .. #keep .. " matching results.\nFiltered from " .. count .. " original results.")
    else
        gg.alert("No results matched the offset criteria.")
    end
end

main()
