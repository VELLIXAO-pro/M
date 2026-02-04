gg.setRanges(gg.REGION_JAVA_HEAP)

function perform_task(search_hex, refine_val, offsets, edit_val)
    gg.clearResults()
    gg.searchNumber(search_hex, gg.TYPE_BYTE)
    if gg.getResultsCount() == 0 then return end

    gg.refineNumber(tostring(refine_val), gg.TYPE_DWORD)
    local count = gg.getResultsCount()
    if count == 0 then return end

    local results = gg.getResults(count)
    local edits = {}
    for _, v in ipairs(results) do
        for _, offset in ipairs(offsets) do
            table.insert(edits, {
                address = v.address + offset,
                value = edit_val,
                flags = gg.TYPE_DWORD
            })
        end
    end
    gg.setValues(edits)
end

-- Task 1: Search hex ... refine 8, offsets +28, +32, +36, +40, edit 99999
perform_task("h08000000230000000100000004000000", 8, {28, 32, 36, 40}, 99999)

-- Task 2: Search hex ... refine 12, offsets +28, +32, +36, +40, edit 99999
perform_task("h0C000000270000000100000004000000", 12, {28, 32, 36, 40}, 99999)

-- Task 3: Search hex ... refine 16, offsets +44, +48, edit 1000
perform_task("h100000002B00000002000000040000000600000003000000", 16, {44, 48}, 1000)

-- Task 4: Search hex ... refine 20, offsets +44, +48, edit 99999
perform_task("h140000002F00000002000000040000000600000004000000", 20, {44, 48}, 99999)

gg.toast("Selesai!")
