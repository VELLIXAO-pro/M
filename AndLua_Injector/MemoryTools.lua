local MemoryTools = {}
MemoryTools.__index = MemoryTools

function MemoryTools.new(packageName)
    local self = setmetatable({}, MemoryTools)
    self.packageName = packageName
    self.pid = nil
    self.results = {}
    return self
end

-- Executes a shell command and returns the output
function MemoryTools:exec(cmd)
    local p = io.popen(cmd)
    local s = p:read("*all")
    p:close()
    return s
end

-- Finds the PID of the target package
function MemoryTools:getPID()
    local output = self:exec("ps -A | grep " .. self.packageName)
    if output == "" then
        output = self:exec("ps | grep " .. self.packageName)
    end

    for line in output:gmatch("[^\r\n]+") do
        local parts = {}
        for part in line:gmatch("%S+") do
            table.insert(parts, part)
        end
        if parts[2] and tonumber(parts[2]) then
            self.pid = tonumber(parts[2])
            return self.pid
        end
    end
    return nil
end

-- Reads the memory maps and filters for Java Heap
function MemoryTools:getMaps()
    if not self.pid then self:getPID() end
    if not self.pid then return nil end

    local mapsPath = string.format("/proc/%d/maps", self.pid)
    local output = self:exec("cat " .. mapsPath)

    local ranges = {}
    for line in output:gmatch("[^\r\n]+") do
        if line:find("/dev/ashmem") or line:find("dalvik") then
            local startAddr, endAddr = line:match("(%x+)-(%x+)")
            if startAddr and endAddr then
                table.insert(ranges, {
                    start = tonumber(startAddr, 16),
                    ["end"] = tonumber(endAddr, 16),
                    label = line:match("%S+$") or "unknown"
                })
            end
        end
    end
    return ranges
end

-- Reads a DWORD (4 bytes) from a specific address
function MemoryTools:readDword(address)
    local cmd = string.format("run-as %s dd if=/proc/%d/mem bs=1 count=4 skip=%d 2>/dev/null",
                               self.packageName, self.pid, address)
    local p = io.popen(cmd)
    local data = p:read(4)
    p:close()
    if data and #data == 4 then
        local b1, b2, b3, b4 = data:byte(1, 4)
        return b1 + b2 * 256 + b3 * 65536 + b4 * 16777216
    end
    return nil
end

-- Writes a DWORD (4 bytes) to a specific address
function MemoryTools:writeDword(address, value)
    -- Handle negative values (signed to unsigned 32-bit)
    if value < 0 then value = value + 4294967296 end

    local b1 = value % 256
    local b2 = math.floor(value / 256) % 256
    local b3 = math.floor(value / 65536) % 256
    local b4 = math.floor(value / 16777216) % 256
    local hexStr = string.format("\\x%02x\\x%02x\\x%02x\\x%02x", b1, b2, b3, b4)

    local cmd = string.format("printf '%s' | run-as %s dd of=/proc/%d/mem bs=1 seek=%d count=4 conv=notrunc 2>/dev/null",
                               hexStr, self.packageName, self.pid, address)
    self:exec(cmd)
    return true
end

-- Helper to convert number to 4-byte little-endian string
function MemoryTools:toBin32(val)
    if val < 0 then val = val + 4294967296 end
    local b1 = val % 256
    local b2 = math.floor(val / 256) % 256
    local b3 = math.floor(val / 65536) % 256
    local b4 = math.floor(val / 16777216) % 256
    return string.char(b1, b2, b3, b4)
end

-- Group Search (values: table of numbers, proximity: max distance between values)
function MemoryTools:groupSearch(values, proximity)
    local ranges = self:getMaps()
    if not ranges or #values == 0 then return 0 end

    self.results = {}

    -- We focus on searching for the first value (or the largest one for better performance)
    -- Let's pick the largest value as the primary anchor
    local anchorIdx = 1
    local maxV = -1
    for i, v in ipairs(values) do
        if v > maxV then
            maxV = v
            anchorIdx = i
        end
    end

    local anchorValue = values[anchorIdx]
    local anchorPattern = self:toBin32(anchorValue)

    for _, range in ipairs(ranges) do
        local size = range["end"] - range.start
        local chunkSize = 512 * 1024
        for offset = 0, size - 4, chunkSize do
            local currentRead = math.min(chunkSize + 128, size - offset)
            local cmd = string.format("run-as %s dd if=/proc/%d/mem bs=1 count=%d skip=%d 2>/dev/null",
                                       self.packageName, self.pid, currentRead, range.start + offset)
            local p = io.popen(cmd)
            local data = p:read("*all")
            p:close()

            if data then
                local startPos = 1
                while true do
                    local foundPos = data:find(anchorPattern, startPos, true)
                    if not foundPos then break end

                    local absoluteAddr = range.start + offset + foundPos - 1

                    -- Now check proximity for other values
                    local allFound = true
                    for i, targetVal in ipairs(values) do
                        if i ~= anchorIdx then
                            local targetPattern = self:toBin32(targetVal)
                            -- Look in a window around the anchor
                            local windowStart = math.max(1, foundPos - proximity)
                            local windowEnd = math.min(#data, foundPos + 4 + proximity)
                            local windowData = data:sub(windowStart, windowEnd)

                            if not windowData:find(targetPattern, 1, true) then
                                allFound = false
                                break
                            end
                        end
                    end

                    if allFound then
                        -- Store all values in the group as results (or just the anchor/focus)
                        -- User wants to focus on 65536
                        table.insert(self.results, {
                            address = absoluteAddr,
                            value = anchorValue
                        })
                    end

                    startPos = foundPos + 1
                    if #self.results > 500 then return #self.results end
                end
            end
        end
    end

    return #self.results
end

-- Standard search
function MemoryTools:search(value)
    return self:groupSearch({tonumber(value)}, 0)
end

return MemoryTools
