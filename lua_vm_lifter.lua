-- Lua/Luau static VM lifter
-- Companion to lua_vm_suite.lua.
-- STATIC ONLY: this module parses/analyzes source text and never executes target code.
-- Pipeline: lexer -> constants -> dispatcher -> handler extraction -> opcode mapping -> VM IR -> CFG -> Luau reconstruction.

local L = {}

local function add_unique(t, v)
    if v == nil then return end
    for _, x in ipairs(t) do if x == v then return end end
    t[#t + 1] = v
end

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

-- Tokenize enough Lua/Luau syntax to inspect obfuscated dispatchers without loading code.
function L.lex(source)
    assert(type(source) == "string", "source must be a string")
    local tokens, i, n = {}, 1, #source
    while i <= n do
        local c = source:sub(i, i)
        if c:match("%s") then
            i = i + 1
        elseif source:sub(i, i + 1) == "--" then
            if source:sub(i, i + 3) == "--[[" then
                local e = source:find("]]", i + 4, true)
                i = e and e + 2 or n + 1
            else
                local e = source:find("\n", i + 2, true)
                i = e or n + 1
            end
        elseif c == '"' or c == "'" then
            local q, j = c, i + 1
            while j <= n do
                local x = source:sub(j, j)
                if x == "\\" then j = j + 2
                elseif x == q then j = j + 1; break
                else j = j + 1 end
            end
            tokens[#tokens + 1] = { kind = "string", value = source:sub(i, j - 1), pos = i }
            i = j
        elseif c:match("[%a_]") then
            local j = i + 1
            while j <= n and source:sub(j, j):match("[%w_]") do j = j + 1 end
            local v = source:sub(i, j - 1)
            tokens[#tokens + 1] = { kind = "ident", value = v, pos = i }
            i = j
        elseif c:match("%d") then
            local j = i + 1
            while j <= n and source:sub(j, j):match("[%da-fA-FxXbB%.]") do j = j + 1 end
            tokens[#tokens + 1] = { kind = "number", value = source:sub(i, j - 1), pos = i }
            i = j
        else
            local two = source:sub(i, i + 1)
            if two == "==" or two == "~=" or two == "<=" or two == ">=" or two == ".." then
                tokens[#tokens + 1] = { kind = "symbol", value = two, pos = i }; i = i + 2
            else
                tokens[#tokens + 1] = { kind = "symbol", value = c, pos = i }; i = i + 1
            end
        end
    end
    return tokens
end

function L.extract_constants(source)
    local out = { strings = {}, numbers = {} }
    for q, body in source:gmatch('(["\'])(.-)%1') do add_unique(out.strings, body) end
    for token in source:gmatch("%-?0[xX][%da-fA-F]+") do add_unique(out.numbers, tonumber(token)) end
    for token in source:gmatch("%-?%d+") do add_unique(out.numbers, tonumber(token)) end
    return out
end

-- Find likely VM dispatchers. This deliberately records source evidence rather than evaluating it.
function L.find_dispatchers(source)
    local out = {}
    local patterns = {
        { "while", "while%s+[^\n]-do" },
        { "switch", "switch%s*[%(%[]" },
        { "opcode_if", "if%s+[%a_][%w_]*%s*[<>=~]+%s*[%w_]+%s+then" },
        { "opcode_index", "[%a_][%w_]*%s*%[%s*[%a_][%w_]*%s*%]" },
        { "handler_table", "[%a_][%w_]*%s*=%s*{%s*[^{}]-function" },
    }
    for _, p in ipairs(patterns) do
        local pos = 1
        while true do
            local a, b = source:find(p[2], pos)
            if not a then break end
            out[#out + 1] = { kind = p[1], start_pos = a, end_pos = b, text = source:sub(a, math.min(#source, b + 120)) }
            pos = b + 1
        end
    end
    return out
end

function L.extract_handlers(source)
    local handlers = {}
    local seen = {}
    local function record(op, body, pos)
        op = trim(op or "")
        if op == "" then return end
        local key = op .. "@" .. tostring(pos)
        if seen[key] then return end
        seen[key] = true
        handlers[#handlers + 1] = { opcode = op, body = trim(body or ""), pos = pos }
    end

    -- Numeric comparisons are the most common flattened dispatcher form.
    for var, op, value, body in source:gmatch("if%s+([%a_][%w_]*)%s*([<>=~]+)%s*(-?0[xX][%da-fA-F]+)%s+then(.-)end") do
        record(value, body, source:find("if%s+" .. var, 1) or 0)
    end
    for var, op, value, body in source:gmatch("if%s+([%a_][%w_]*)%s*([<>=~]+)%s*(-?%d+)%s+then(.-)end") do
        record(value, body, source:find("if%s+" .. var, 1) or 0)
    end
    -- Table-dispatch form: handlers[opcode] = function(...)
    for table_name, opcode, args, body in source:gmatch("([%a_][%w_]*)%s*%[%s*([^%]]+)%s*%]%s*=%s*function%s*%(([^)]*)%)%s*(.-)end") do
        record(trim(opcode), body, source:find(table_name, 1) or 0)
    end
    return handlers
end

local function op_name(body)
    if body:find("string%.byte") then return "BYTE" end
    if body:find("string%.char") then return "CHAR" end
    if body:find("bit32%.") then return "BIT" end
    if body:find("table%.concat") then return "CONCAT" end
    if body:find("[%a_][%w_]*%s*%(") then return "CALL" end
    if body:find("return") then return "RETURN" end
    if body:find("%+") or body:find("%-") or body:find("%*") or body:find("/") then return "ARITH" end
    return "UNKNOWN"
end

function L.map_opcodes(handlers)
    local map = {}
    for _, h in ipairs(handlers or {}) do
        local key = h.opcode
        map[key] = map[key] or { opcode = key, operations = {}, evidence = {} }
        add_unique(map[key].operations, op_name(h.body))
        map[key].evidence[#map[key].evidence + 1] = h.body
    end
    return map
end

function L.build_cfg(handlers)
    local nodes, edges = {}, {}
    for i, h in ipairs(handlers or {}) do
        nodes[#nodes + 1] = { id = i, opcode = h.opcode, operation = op_name(h.body) }
        if i > 1 then edges[#edges + 1] = { from = i - 1, to = i, kind = "fallthrough" } end
        if h.body:find("goto%s+") or h.body:find("continue") then
            edges[#edges + 1] = { from = i, to = i, kind = "loop_or_jump" }
        end
    end
    return { nodes = nodes, edges = edges }
end

function L.lift(source, options)
    options = options or {}
    local tokens = L.lex(source)
    local constants = L.extract_constants(source)
    local dispatchers = L.find_dispatchers(source)
    local handlers = L.extract_handlers(source)
    local opcodes = L.map_opcodes(handlers)
    local cfg = L.build_cfg(handlers)

    local ir = {
        version = 2,
        static_only = true,
        tokens = #tokens,
        constants = constants,
        dispatchers = dispatchers,
        handlers = handlers,
        opcodes = opcodes,
        cfg = cfg,
        reconstruction = nil,
    }

    if options.reconstruct ~= false then
        ir.reconstruction = L.reconstruct(ir)
    end
    return ir
end

function L.reconstruct(ir)
    local lines = {
        "-- Static Luau reconstruction generated from VM IR.",
        "-- This is an analysis artifact; it never executes the original VM.",
        "local function reconstructed_vm(stack, env)",
        "    local pc = 1",
        "    local opcode",
        "    while pc <= #stack do",
        "        opcode = stack[pc]",
        "        -- Handler bodies are represented symbolically below.",
        "        -- Replace only after opcode semantics have been independently verified.",
    }
    for _, node in ipairs(ir.cfg.nodes or {}) do
        lines[#lines + 1] = string.format("        -- pc=%d opcode=%s operation=%s", node.id, tostring(node.opcode), tostring(node.operation))
    end
    lines[#lines + 1] = "        pc = pc + 1"
    lines[#lines + 1] = "    end"
    lines[#lines + 1] = "    return stack"
    lines[#lines + 1] = "end"
    lines[#lines + 1] = "return reconstructed_vm"
    return table.concat(lines, "\n")
end

function L.ir_to_text(ir)
    local out = { "-- Lua VM IR v" .. tostring(ir.version), "static_only=true", "tokens=" .. tostring(ir.tokens), "[CONSTANTS]" }
    for _, s in ipairs(ir.constants.strings or {}) do out[#out + 1] = "STRING " .. string.format("%q", s) end
    for _, n in ipairs(ir.constants.numbers or {}) do out[#out + 1] = "NUMBER " .. tostring(n) end
    out[#out + 1] = "[DISPATCHERS]"
    for _, d in ipairs(ir.dispatchers or {}) do out[#out + 1] = d.kind .. " @" .. tostring(d.start_pos) end
    out[#out + 1] = "[HANDLERS]"
    for _, h in ipairs(ir.handlers or {}) do out[#out + 1] = "OPCODE " .. h.opcode .. " => " .. op_name(h.body) end
    out[#out + 1] = "[CFG]"
    for _, e in ipairs(ir.cfg.edges or {}) do out[#out + 1] = string.format("%d -> %d (%s)", e.from, e.to, e.kind) end
    return table.concat(out, "\n")
end

return L
