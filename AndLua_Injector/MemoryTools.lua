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
        -- Standard ps output: USER PID PPID ...
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
        -- Filter for Java Heap / ashmem / dalvik
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
        -- Unpack little-endian 4-byte integer
        local b1, b2, b3, b4 = data:byte(1, 4)
        return b1 + b2 * 256 + b3 * 65536 + b4 * 16777216
    end
    return nil
end

-- Writes a DWORD (4 bytes) to a specific address
function MemoryTools:writeDword(address, value)
    -- Convert value to little-endian 4-byte string
    local b1 = value % 256
    local b2 = math.floor(value / 256) % 256
    local b3 = math.floor(value / 65536) % 256
    local b4 = math.floor(value / 16777216) % 256
    local hexStr = string.format("\\x%02x\\x%02x\\x%02x\\x%02x", b1, b2, b3, b4)

    -- Using printf to pipe binary data into dd
    local cmd = string.format("printf '%s' | run-as %s dd of=/proc/%d/mem bs=1 seek=%d count=4 conv=notrunc 2>/dev/null",
                               hexStr, self.packageName, self.pid, address)
    self:exec(cmd)
    return true
end

-- Searches for a DWORD in Java Heap
function MemoryTools:search(value)
    local ranges = self:getMaps()
    if not ranges then return 0 end

    self.results = {}
    local targetValue = tonumber(value)

    -- Little-endian pattern to look for in binary string
    local b1 = targetValue % 256
    local b2 = math.floor(targetValue / 256) % 256
    local b3 = math.floor(targetValue / 65536) % 256
    local b4 = math.floor(targetValue / 16777216) % 256
    local pattern = string.char(b1, b2, b3, b4)

    for _, range in ipairs(ranges) do
        local size = range["end"] - range.start
        -- Read in chunks of 512KB to avoid excessive memory usage in Lua
        local chunkSize = 512 * 1024
        for offset = 0, size - 4, chunkSize do
            local currentRead = math.min(chunkSize + 3, size - offset) -- overlap by 3 bytes to catch values across chunks
            local cmd = string.format("run-as %s dd if=/proc/%d/mem bs=1 count=%d skip=%d 2>/dev/null",
                                       self.packageName, self.pid, currentRead, range.start + offset)
            local p = io.popen(cmd)
            local data = p:read("*all")
            p:close()

            if data then
                local startPos = 1
                while true do
                    local foundPos = data:find(pattern, startPos, true)
                    if not foundPos then break end

                    table.insert(self.results, {
                        address = range.start + offset + foundPos - 1,
                        value = targetValue
                    })
                    startPos = foundPos + 1

                    -- Limit results to avoid crashing UI
                    if #self.results > 1000 then return #self.results end
                end
            end
        end
    end

    return #self.results
end

return MemoryTools
