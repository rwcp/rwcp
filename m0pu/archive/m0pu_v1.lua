-- m0pu Decompiler v1.0
-- Potassium-Optimized | Oracle Logic Core
-- Supports Luau Bytecode v3-v9 

local m0pu = {}
m0pu.__index = m0pu

local function getPotassiumEnv()
    local env = getgenv()
    if not env then
        error("Potassium environment not found. Ensure you're using Potassium v2.2.10+")
    end
    return env
end

local function getClosureSource(func)
    if not checkcaller() then
        return nil
    end
    return getscriptclosure(func)
end

local BytecodeReader = {}
BytecodeReader.__index = BytecodeReader

function BytecodeReader.new(data)
    local self = setmetatable({}, BytecodeReader)
    self.data = data
    self.position = 1
    return self
end

function BytecodeReader:readByte()
    local byte = string.byte(self.data, self.position)
    self.position = self.position + 1
    return byte
end

function BytecodeReader:readInt()
    local a = self:readByte()
    local b = self:readByte()
    local c = self:readByte()
    local d = self:readByte()
    return a + (b * 256) + (c * 65536) + (d * 16777216)
end

function BytecodeReader:readString()
    local length = self:readInt()
    if length == 0 then return "" end
    local str = string.sub(self.data, self.position, self.position + length - 1)
    self.position = self.position + length
    return str
end

local Opcodes = {
    [0] = "NOP",
    [1] = "BREAK",
    [2] = "LOADNIL",
    [3] = "LOADB",
    [4] = "LOADN",
    [5] = "LOADK",
    [6] = "LOADKX",
    [7] = "LOADF",
    [8] = "LOADT",
    [9] = "LOADFALSE",
    [10] = "LOADTRUE",
    [11] = "GETIMPORT",
    [12] = "GETTABLEN",
    [13] = "GETTABLE",
    [14] = "SETTABLEN",
    [15] = "SETTABLE",
    [16] = "NEWTABLE",
    [17] = "ADDN",
    [18] = "SUBBN",
    [19] = "MULBN",
    [20] = "DIVBN",
    [21] = "MODBN",
    [22] = "POWBN",
    [23] = "ADDN",
    [24] = "SUBBN",
    [25] = "MULBN",
    [26] = "DIVBN",
    [27] = "MODBN",
    [28] = "POWBN",
    [29] = "UNM",
    [30] = "NOT",
    [31] = "LEN",
    [32] = "CONCAT",
    [33] = "NEWCLOSURE",
    [34] = "DUPCLOSURE",
    [35] = "PREPVARARGS",
    [36] = "CALL",
    [37] = "CALLM",
    [38] = "RETURN",
    [39] = "RETURNM",
    [40] = "JUMP",
    [41] = "JUMPX",
    [42] = "JUMPBACK",
    [43] = "JUMPIF",
    [44] = "JUMPIFX",
    [45] = "JUMPIFEQ",
    [46] = "JUMPIFLE",
    [47] = "JUMPIFLT",
    [48] = "JUMPIFNOTEQ",
    [49] = "JUMPIFNOTLE",
    [50] = "JUMPIFNOTLT",
    [51] = "ADD",
    [52] = "SUB",
    [53] = "MUL",
    [54] = "DIV",
    [55] = "MOD",
    [56] = "POW",
    [57] = "ADDK",
    [58] = "SUBK",
    [59] = "MULK",
    [60] = "DIVK",
    [61] = "MODK",
    [62] = "POWK",
    [63] = "ADDN",
    [64] = "SUBBN",
    [65] = "MULBN",
    [66] = "DIVBN",
    [67] = "MODBN",
    [68] = "POWBN",
    [69] = "NANCHECK",
    [70] = "ASSERT",
    [71] = "GETUPVAL",
    [72] = "SETUPVAL",
    [73] = "GETTABLEN",
    [74] = "GETTABLEK",
    [75] = "SETTABLEN",
    [76] = "SETTABLEK",
    [77] = "GETGLOBAL",
    [78] = "SETGLOBAL",
    [79] = "GETFIELD",
    [80] = "SETFIELD",
    [81] = "CLOSEUPVALS",
    [82] = "NEWCLOSURE",
    [83] = "DUPCLOSURE",
    [84] = "FORGL",
    [85] = "FORGLPREP",
    [86] = "FORLOOP",
    [87] = "FORPREP",
    [88] = "TFORLOOP",
    [89] = "TFORPREP",
    [90] = "SETLIST",
    [91] = "GETLIST",
    [92] = "GETTABLEK",
    [93] = "SETTABLEK",
    [94] = "GETFIELDK",
    [95] = "SETFIELDK",
    [96] = "GETGLOBAL",
    [97] = "SETGLOBAL",
    [98] = "GETFIELD",
    [99] = "SETFIELD",
    [100] = "CLOSEUPVALS",
    [101] = "NAMECALL",
    [102] = "CALL",
    [103] = "CALLM",
    [104] = "RETURN",
    [105] = "RETURNM",
    [106] = "PREPVARARGS",
    [107] = "JUMPX",
    [108] = "JUMPBACK",
    [109] = "JUMPIFX",
    [110] = "JUMPIFEQK",
    [111] = "JUMPIFLEK",
    [112] = "JUMPIFLTK",
    [113] = "JUMPIFNOTEQK",
    [114] = "JUMPIFNOTLEK",
    [115] = "JUMPIFNOTLTK",
}

local function decompileProto(reader, depth)
    depth = depth or 0
    local indent = string.rep("    ", depth)
    local lines = {}
    
    local name = reader:readString()
    local lineDefined = reader:readInt()
    local lineLast = reader:readInt()
    local numParams = reader:readByte()
    local isVararg = reader:readByte()
    local maxStackSize = reader:readByte()
    local numUpvalues = reader:readByte()
    local numConstants = reader:readInt()
    local numInstructions = reader:readInt()
    local numFunctions = reader:readInt()
    local numDebugLines = reader:readInt()
    local numDebugLocals = reader:readInt()
    
    local constants = {}
    for i = 1, numConstants do
        local constType = reader:readByte()
        if constType == 0 then
            constants[i] = "nil"
        elseif constType == 1 then
            constants[i] = tostring(reader:readByte() == 1)
        elseif constType == 2 then
            constants[i] = tostring(reader:readInt())
        elseif constType == 3 then
            constants[i] = tostring(reader:readString())
        elseif constType == 4 then
            constants[i] = "..."
        elseif constType == 5 then
            constants[i] = "{}"
        elseif constType == 6 then
            constants[i] = "function() end"
        elseif constType == 7 then
            constants[i] = "Vector3.new()"
        elseif constType == 8 then
            constants[i] = "{}"
        elseif constType == 9 then
            constants[i] = tostring(reader:readInt())
        end
    end
    
    local instructions = {}
    for i = 1, numInstructions do
        local opcode = reader:readByte()
        local a = reader:readByte()
        local b = reader:readByte()
        local c = reader:readByte()
        local d = reader:readByte()
        local e = reader:readByte()
        instructions[i] = {
            opcode = opcode,
            opname = Opcodes[opcode] or "UNKNOWN",
            a = a, b = b, c = c, d = d, e = e
        }
    end
    
    local debugLines = {}
    for i = 1, numDebugLines do
        debugLines[i] = reader:readInt()
    end
    
    local debugLocals = {}
    for i = 1, numDebugLocals do
        debugLocals[i] = {
            name = reader:readString(),
            start = reader:readInt(),
            finish = reader:readInt()
        }
    end
    
    local functions = {}
    for i = 1, numFunctions do
        functions[i] = decompileProto(reader, depth + 1)
    end
    
    local function reconstructStatement(instr, idx)
        local op = instr.opname
        local a = instr.a
        local b = instr.b
        local c = instr.c
        
        if op == "LOADK" then
            return indent .. "local R" .. a .. " = " .. (constants[b] or "nil")
        elseif op == "LOADB" then
            return indent .. "local R" .. a .. " = " .. tostring(b ~= 0)
        elseif op == "LOADN" then
            return indent .. "local R" .. a .. " = " .. tostring(b)
        elseif op == "ADD" or op == "SUB" or op == "MUL" or op == "DIV" or op == "MOD" or op == "POW" then
            return indent .. "local R" .. a .. " = R" .. b .. " " .. op .. " R" .. c
        elseif op == "CALL" then
            return indent .. "R" .. a .. " = R" .. a .. "(" .. (b > 0 and "..." or "") .. ")"
        elseif op == "RETURN" then
            return indent .. "return R" .. a
        elseif op == "JUMP" then
            return indent .. "-- jump to " .. tostring(b)
        elseif op == "NEWTABLE" then
            return indent .. "local R" .. a .. " = {}"
        elseif op == "SETTABLE" then
            return indent .. "R" .. a .. "[R" .. b .. "] = R" .. c
        elseif op == "GETTABLE" then
            return indent .. "local R" .. a .. " = R" .. b .. "[R" .. c .. "]"
        elseif op == "GETUPVAL" then
            return indent .. "local R" .. a .. " = upvalue[" .. b .. "]"
        elseif op == "SETUPVAL" then
            return indent .. "upvalue[" .. b .. "] = R" .. a
        elseif op == "NEWCLOSURE" or op == "DUPCLOSURE" then
            return indent .. "local R" .. a .. " = function() --[[ nested ]] end"
        elseif op == "FORPREP" then
            return indent .. "for R" .. a .. " = R" .. a .. ", R" .. a + 1 .. " do"
        elseif op == "FORLOOP" then
            return indent .. "end"
        elseif op == "TFORPREP" then
            return indent .. "for R" .. a .. " in R" .. a + 1 .. " do"
        elseif op == "TFORLOOP" then
            return indent .. "end"
        elseif op == "NAMECALL" then
            return indent .. "R" .. a .. " = R" .. b .. "." .. (constants[c] or "method") .. "(R" .. b .. ")"
        else
            return indent .. "-- " .. op .. " R" .. a .. ", " .. b .. ", " .. c
        end
    end
    
    local funcHeader = indent .. "function " .. (name ~= "" and name or "anonymous")
    if numParams > 0 then
        local params = {}
        for i = 1, numParams do
            table.insert(params, "R" .. i)
        end
        funcHeader = funcHeader .. "(" .. table.concat(params, ", ") .. ")"
    else
        funcHeader = funcHeader .. "()"
    end
    funcHeader = funcHeader .. (isVararg == 1 and " ..." or "")
    
    table.insert(lines, funcHeader)
    
    for i, instr in ipairs(instructions) do
        local stmt = reconstructStatement(instr, i)
        table.insert(lines, stmt)
    end
    
    for _, func in ipairs(functions) do
        table.insert(lines, func)
    end
    
    table.insert(lines, indent .. "end")
    
    return table.concat(lines, "\n")
end

function m0pu.decompile(scriptInstance)
    local bytecode
    
    if type(scriptInstance) == "string" then
        bytecode = scriptInstance
    else
        local success, result = pcall(function()
            return getscriptbytecode(scriptInstance)
        end)
        if success then
            bytecode = result
        else
            local success, result = pcall(function()
                return getscriptclosure(scriptInstance)
            end)
            if success then
                bytecode = result
            else
                error("Failed to extract bytecode from script instance.")
            end
        end
    end
    
    local reader = BytecodeReader.new(bytecode)
    
    local hasRobloxEnvelope = false
    local trailerVersion = 0
    local dataLen = #bytecode
    if dataLen > 8 then
        local trailer = string.sub(bytecode, dataLen - 7, dataLen)
        if trailer == "RBX1" or trailer == "RBX2" then
            hasRobloxEnvelope = true
            trailerVersion = trailer == "RBX1" and 1 or 2
        end
    end
    
    local source = decompileProto(reader, 0)
    
    source = string.gsub(source, "R(%d+)", function(n)
        return "v" .. n
    end)
    
    return {
        source = source,
        hasRobloxEnvelope = hasRobloxEnvelope,
        trailerVersion = trailerVersion,
        bytecodeSize = dataLen
    }
end

function m0pu.saveInstance(instance, path)
    local source = m0pu.decompile(instance)
    local newScript = Instance.new("LocalScript")
    newScript.Name = instance.Name .. "_Decompiled"
    newScript.Source = source.source
    if path then
        local parent = game:FindFirstChild(path)
        if parent then
            newScript.Parent = parent
        else
            newScript.Parent = game:GetService("ReplicatedStorage")
        end
    else
        newScript.Parent = game:GetService("ReplicatedStorage")
    end
    return newScript
end

local originalDecompile = decompile or function() end

function decompile(script, useM0pu)
    if useM0pu == true then
        local result = m0pu.decompile(script)
        return result.source
    else
        return originalDecompile(script)
    end
end

getgenv().m0pu = m0pu
getgenv().m0puDecompile = m0pu.decompile
getgenv().m0puSave = m0pu.saveInstance

return m0pu