gg.setRanges(gg.REGION_JAVA_HEAP)

local all_edits = {}

function perform_task(name, search_hex, refine_val, offsets, edit_val)
    gg.toast("Mencari " .. name .. "...")
    gg.clearResults()
    -- Format 'h' dengan spasi memastikan GG membaca sebagai urutan byte (byte sequence)
    gg.searchNumber(search_hex, gg.TYPE_BYTE)

    local count = gg.getResultsCount()
    if count == 0 then
        gg.toast(name .. ": Tidak ditemukan")
        return
    end

    gg.toast(name .. ": Menghaluskan (Refine) " .. refine_val .. "...")
    gg.refineNumber(tostring(refine_val), gg.TYPE_DWORD)

    count = gg.getResultsCount()
    if count == 0 then
        gg.toast(name .. ": Gagal refine " .. refine_val)
        return
    end

    local results = gg.getResults(count)
    local task_edits = {}
    for _, v in ipairs(results) do
        for _, offset in ipairs(offsets) do
            table.insert(task_edits, {
                address = v.address + offset,
                value = edit_val,
                flags = gg.TYPE_DWORD
            })
        end
    end

    if #task_edits > 0 then
        gg.setValues(task_edits)
        for _, edit in ipairs(task_edits) do
            table.insert(all_edits, edit)
        end
        gg.toast(name .. ": Berhasil mengedit " .. #task_edits .. " alamat")
    end
end

-- Task 1: h 08 00 00 00 23 00 00 00 01 00 00 00 04 00 00 00
perform_task("Tugas 1", "h 08 00 00 00 23 00 00 00 01 00 00 00 04 00 00 00", 8, {28, 32, 36, 40}, 99999)

-- Task 2: h 0C 00 00 00 27 00 00 00 01 00 00 00 04 00 00 00
perform_task("Tugas 2", "h 0C 00 00 00 27 00 00 00 01 00 00 00 04 00 00 00", 12, {28, 32, 36, 40}, 99999)

-- Task 3: h 10 00 00 00 2B 00 00 00 02 00 00 00 04 00 00 00 06 00 00 00 03 00 00 00
perform_task("Tugas 3", "h 10 00 00 00 2B 00 00 00 02 00 00 00 04 00 00 00 06 00 00 00 03 00 00 00", 16, {44, 48}, 1000)

-- Task 4: h 14 00 00 00 2F 00 00 00 02 00 00 00 04 00 00 00 06 00 00 00 04 00 00 00
perform_task("Tugas 4", "h 14 00 00 00 2F 00 00 00 02 00 00 00 04 00 00 00 06 00 00 00 04 00 00 00", 20, {44, 48}, 99999)

if #all_edits > 0 then
    gg.clearResults()
    gg.loadResults(all_edits)
    gg.toast("Selesai! " .. #all_edits .. " alamat diubah.")
    gg.setVisible(true)
else
    gg.toast("Selesai! Tidak ada alamat yang ditemukan atau diubah.")
end
