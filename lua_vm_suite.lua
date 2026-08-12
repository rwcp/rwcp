-- Lua/Luau CTF VM Deobfuscation Suite
-- Static-only: never executes target source.
-- Families: Luraph, Prometheus, IronBrew, MoonSec, luaobfuscator, generic VM.

local D = {}

local function inc(t, k, n)
    t[k] = (t[k] or 0) + (n or 1)
end

local function add(t, value)
    if value == nil or value == "" then
        return
    end
    for _, existing in ipairs(t) do
        if existing == value then
            return
        end
    end
    t[#t + 1] = value
end

local function normalize_numbers(source, report)
    source = source:gsub("%-?0[bB][01]+", function(token)
        local sign = ""
        local body = token
        if body:sub(1, 1) == "-" then
            sign = "-"
            body = body:sub(2)
        end
        local bits = body:match("^0[bB]([01]+)$")
        if not bits then
            return token
        end
        local value = 0
        for i = 1, #bits do
            value = value * 2
            if bits:sub(i, i) == "1" then
                value = value + 1
            end
        end
        inc(report, "binary")
        return sign .. tostring(value)
    end)

    source = source:gsub("0[xX][%da-fA-F]+", function(token)
        local value = tonumber(token)
        if value ~= nil then
            inc(report, "hex")
            return tostring(value)
        end
        return token
    end)

    return source
end

local function decode_strings(source, report)
    local function decode(body)
        body = body:gsub("\\x(%x%x)", function(hex)
            return string.char(tonumber(hex, 16))
        end)
        body = body:gsub("\\(%d%d?%d?)", function(decimal)
            local value = tonumber(decimal)
            if value and value <= 255 then
                return string.char(value)
            end
            return "\\" .. decimal
        end)
        body = body:gsub("\\n", "\n")
        body = body:gsub("\\r", "\r")
        body = body:gsub("\\t", "\t")
        body = body:gsub("\\\\", "\\")
        body = body:gsub('\\"', '"')
        body = body:gsub("\\'", "'")
        return body
    end

    source = source:gsub('"([^"\\]*(\\.[^"\\]*)*)"', function(body)
        local decoded = decode(body)
        if decoded ~= body then
            inc(report, "escaped_strings")
        end
        return string.format("%q", decoded)
    end)

    source = source:gsub("'([^'\\]*(\\.[^'\\]*)*)'", function(body)
        local decoded = decode(body)
        if decoded ~= body then
            inc(report, "escaped_strings")
        end
        return string.format("%q", decoded)
    end)

    return source
end

local function fold_string_char(source, report)
    return source:gsub("string%.char%s*%(([%d%s,%-]+)%)", function(args)
        local output = {}
        for number in args:gmatch("%-?%d+") do
            local value = tonumber(number)
            if not value or value < 0 or value > 255 then
                return "string.char(" .. args .. ")"
            end
            output[#output + 1] = string.char(value)
        end
        if #output == 0 then
            return "string.char(" .. args .. ")"
        end
        inc(report, "string_char")
        return string.format("%q", table.concat(output))
    end)
end

local function fold_reverse(source, report)
    return source:gsub("string%.reverse%s*%(%s*(['\"])(.-)%1%s*%)", function(_, value)
        inc(report, "string_reverse")
        return string.format("%q", value:reverse())
    end)
end

local function fold_concat(source, report)
    return source:gsub("table%.concat%s*%(%s*{%s*([^{}]-)%s*}%s*%)", function(items)
        local values = {}
        for value in items:gmatch('"([^"]*)"') do
            values[#values + 1] = value
        end
        if #values > 0 then
            inc(report, "table_concat")
            return string.format("%q", table.concat(values))
        end
        return "table.concat({" .. items .. "})"
    end)
end

local function fold_bit32(source, report)
    if not bit32 then
        return source
    end

    local functions = {
        bxor = bit32.bxor,
        band = bit32.band,
        bor = bit32.bor,
        lshift = bit32.lshift,
        rshift = bit32.rshift,
    }

    for name, fn in pairs(functions) do
        source = source:gsub("bit32%." .. name .. "%s*%(%s*(%d+)%s*,%s*(%d+)%s*%)", function(a, b)
            inc(report, "bit32_" .. name)
            return tostring(fn(tonumber(a), tonumber(b)))
        end)
    end

    return source
end

local function fold_arithmetic(source, report)
    local rules = {
        { "(%-?%d+)%s*%+%s*(%-?%d+)", function(a, b) return a + b end },
        { "(%-?%d+)%s*%-%s*(%-?%d+)", function(a, b) return a - b end },
        { "(%-?%d+)%s*%*%s*(%-?%d+)", function(a, b) return a * b end },
        { "(%-?%d+)%s*/%s*(%-?%d+)", function(a, b) if b == 0 then return nil end return a / b end },
    }

    for _, rule in ipairs(rules) do
        source = source:gsub(rule[1], function(a, b)
            local left = tonumber(a)
            local right = tonumber(b)
            local value = rule[2](left, right)
            if value == nil then
                return a .. " / " .. b
            end
            inc(report, "arithmetic")
            return tostring(value)
        end)
    end

    return source
end

local function detect(source)
    local signatures = {
        Luraph = {
            "Luraph Obfuscator", "LPH_ENCFUNC", "a%.F%[", "a:H%(", "a:G%(", "bit32%.bxor"
        },
        Prometheus = {
            "Prometheus", "AntiTamper", "Watermark", "Proxify"
        },
        IronBrew = {
            "IronBrew", "IronBrew2", "IronBrewObfuscator"
        },
        MoonSec = {
            "MoonSec", "MoonSecV3", "MoonSecV4", "MoonSec V3", "MoonSec V4"
        },
        LuaObfuscator = {
            "luaobfuscator", "LuaObfuscator"
        },
        GenericVM = {
            "while%s+true%s+do", "string%.byte", "table%.concat", "bit32%."
        },
    }

    local detections = {}
    local family = "Unknown"
    local best = 0

    for name, patterns in pairs(signatures) do
        local hits = 0
        for _, pattern in ipairs(patterns) do
            if source:find(pattern) then
                hits = hits + 1
            end
        end
        if hits > 0 then
            detections[name] = hits
        end
        if hits > best then
            best = hits
            family = name
        end
    end

    return detections, family, best
end

local function analyze_vm(source)
    local vm = {
        states = {},
        caches = {},
        handlers = {},
        opcodes = {},
        operations = {},
        score = 0,
    }

    for variable in source:gmatch("([%a_][%w_]*)%s*[<>=~]+%s*0x%x+") do
        add(vm.states, variable)
    end

    for variable in source:gmatch("([%a_][%w_]*)%s*=%s*0x%x+") do
        add(vm.states, variable)
    end

    for object in source:gmatch("([%a_][%w_]*)%.F%[") do
        add(vm.caches, object .. ".F")
    end

    for object in source:gmatch("([%a_][%w_]*)%s*:%s*[HG]%s*%(") do
        add(vm.caches, object .. ":H/G")
    end

    for variable, operator, number in source:gmatch("if%s+([%a_][%w_]*)%s*([<>=~]+)%s*(0x%x+)") do
        add(vm.handlers, variable .. " " .. operator .. " " .. number)
    end

    for variable, expression in source:gmatch("([%a_][%w_]*)%s*=%s*([^;\n]+)") do
        if expression:find("0x") or expression:find("0[bB]") then
            add(vm.opcodes, variable .. " = " .. expression)
        end
    end

    local operation_patterns = {
        CALL = "%w+%s*%(",
        BYTE = "string%.byte%s*%(",
        CHAR = "string%.char%s*%(",
        BIT = "bit32%.%w+%(",
        RETURN = "%f[%w]return%f[^%w_]",
    }

    for name, pattern in pairs(operation_patterns) do
        local amount = 0
        for _ in source:gmatch(pattern) do
            amount = amount + 1
        end
        if amount > 0 then
            vm.operations[name] = amount
        end
    end

    if #vm.caches > 0 then vm.score = vm.score + 2 end
    if #vm.handlers >= 3 then vm.score = vm.score + 2 end
    if #vm.opcodes >= 3 then vm.score = vm.score + 1 end
    if vm.operations.BIT then vm.score = vm.score + 1 end
    if vm.operations.BYTE then vm.score = vm.score + 1 end

    vm.probable = vm.score >= 4
    return vm
end

function D.deobfuscate(source, options)
    options = options or {}
    assert(type(source) == "string", "source must be a string")

    local report = {
        passes = 0,
        stats = {},
    }

    local output = source
    report.detections, report.family, report.score = detect(output)

    local max_passes = tonumber(options.MaxPasses) or 12
    if max_passes < 1 then max_passes = 1 end
    if max_passes > 50 then max_passes = 50 end

    for pass = 1, max_passes do
        local previous = output
        output = normalize_numbers(output, report.stats)
        output = decode_strings(output, report.stats)
        output = fold_string_char(output, report.stats)
        output = fold_reverse(output, report.stats)
        output = fold_concat(output, report.stats)
        output = fold_bit32(output, report.stats)
        output = fold_arithmetic(output, report.stats)
        output = output:gsub("[ \t]+\n", "\n")
        output = output:gsub("\n\n\n+", "\n\n")
        report.passes = pass

        if output == previous then
            break
        end
    end

    report.vm = analyze_vm(output)
    report.ir = {
        type = "LuaVMAnalysis",
        version = 1,
        family = report.family,
        score = report.vm.score,
        probable_vm = report.vm.probable,
        states = report.vm.states,
        caches = report.vm.caches,
        handlers = report.vm.handlers,
        opcodes = report.vm.opcodes,
        operations = report.vm.operations,
    }

    report.warning = "Static-only analysis. Target code is never executed."
    return output, report
end

function D.print_report(report)
    print("===== Lua VM Deobfuscator =====")
    print("Family: " .. tostring(report.family) .. " score=" .. tostring(report.score))
    print("Passes: " .. tostring(report.passes))
    for name, amount in pairs(report.detections or {}) do
        print(name .. ": " .. tostring(amount))
    end
    print("VM: " .. tostring(report.vm.probable) .. " score=" .. tostring(report.vm.score))
    for name, amount in pairs(report.stats or {}) do
        print(name .. ": " .. tostring(amount))
    end
    print(report.warning)
end

function D.print_vm_report(vm)
    if not vm then return end
    print("===== VM REPORT =====")
    print("Probable VM: " .. tostring(vm.probable) .. " score=" .. tostring(vm.score))
    for _, value in ipairs(vm.states) do print("STATE " .. value) end
    for _, value in ipairs(vm.caches) do print("CACHE " .. value) end
    for _, value in ipairs(vm.handlers) do print("HANDLER " .. value) end
    for _, value in ipairs(vm.opcodes) do print("OPCODE " .. value) end
end

function D.ir_to_text(ir)
    local output = {
        "-- Static VM IR",
        "family=" .. tostring(ir.family),
        "score=" .. tostring(ir.score),
        "probable_vm=" .. tostring(ir.probable_vm),
        "[STATES]",
    }

    for _, value in ipairs(ir.states or {}) do output[#output + 1] = value end
    output[#output + 1] = "[CACHES]"
    for _, value in ipairs(ir.caches or {}) do output[#output + 1] = value end
    output[#output + 1] = "[HANDLERS]"
    for _, value in ipairs(ir.handlers or {}) do output[#output + 1] = value end
    output[#output + 1] = "[OPCODES]"
    for _, value in ipairs(ir.opcodes or {}) do output[#output + 1] = value end

    return table.concat(output, "\n")
end

D.analyze_vm = analyze_vm
D.detect = detect

return D
