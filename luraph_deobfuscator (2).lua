-- Luraph Luau Static Deobfuscator
-- CTF / reverse-engineering helper.
-- This tool NEVER executes the input script. It performs source-level
-- normalization and common Luraph-wrapper reductions.
--
-- Usage:
--   local Deobfuscator = loadstring(game:HttpGet("URL_TO_THIS_FILE"))()
--   local clean, report = Deobfuscator.deobfuscate(source)
--   print(clean)
--
-- Or directly:
--   local clean = Deobfuscator.deobfuscate([[...]])

local M = {}

local function trim(s)
    return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

local function escpat(s)
    return (s:gsub("([^%w])", "%%%1"))
end

local function decode_numeric_escapes(s)
    -- Lua decimal escapes: \ddd
    s = s:gsub("\\(%d%d?%d?)", function(n)
        local v = tonumber(n)
        if v and v <= 255 then return string.char(v) end
        return "\\" .. n
    end)

    -- Hex escapes: \xHH
    s = s:gsub("\\x(%x%x)", function(h)
        return string.char(tonumber(h, 16))
    end)

    return s
end

local function decode_string_literal(q, body)
    -- Conservative: only decode escapes that are unambiguous.
    body = body:gsub("\\n", "\n")
    body = body:gsub("\\r", "\r")
    body = body:gsub("\\t", "\t")
    body = body:gsub("\\\\", "\\")
    body = body:gsub('\\"', '"')
    body = body:gsub("\\'", "'")
    body = decode_numeric_escapes(body)
    return body
end

local function decode_binary(n)
    local sign = ""
    if n:sub(1,1) == "-" then
        sign, n = "-", n:sub(2)
    end
    local bits = n:match("^0[bB]([01]+)$")
    if not bits then return nil end
    return sign .. tostring(tonumber(bits, 2))
end

local function normalize_numbers(src, stats)
    src = src:gsub("[-]?0[bB][01]+", function(x)
        local v = decode_binary(x)
        if v then stats.binary = stats.binary + 1; return v end
        return x
    end)

    src = src:gsub("0[xX][%da-fA-F]+", function(x)
        local v = tonumber(x)
        if v then stats.hex = stats.hex + 1; return tostring(v) end
        return x
    end)

    return src
end

local function decode_string_literals(src, stats)
    -- Handles ordinary quoted strings while deliberately avoiding long strings.
    src = src:gsub('"([^"\\]*(\\.[^"\\]*)*)"', function(body)
        local decoded = decode_string_literal('"', body)
        if decoded ~= body then stats.strings = stats.strings + 1 end
        return string.format("%q", decoded)
    end)

    src = src:gsub("'([^'\\]*(\\.[^'\\]*)*)'", function(body)
        local decoded = decode_string_literal("'", body)
        if decoded ~= body then stats.strings = stats.strings + 1 end
        return string.format("%q", decoded)
    end)

    return src
end

local function fold_string_char(src, stats)
    local changed = true
    local passes = 0

    while changed and passes < 12 do
        changed = false
        passes = passes + 1

        src = src:gsub("string%.char%s*%(([%d%s,%-]+)%)", function(args)
            local out = {}
            local ok = true
            for n in args:gmatch("%-?%d+") do
                local v = tonumber(n)
                if not v or v < 0 or v > 255 then ok = false break end
                out[#out+1] = string.char(v)
            end
            if ok and #out > 0 then
                stats.string_char = stats.string_char + 1
                changed = true
                return string.format("%q", table.concat(out))
            end
            return "string.char(" .. args .. ")"
        end)
    end

    return src
end

local function fold_reverse(src, stats)
    src = src:gsub("string%.reverse%s*%(%s*(['\"])(.-)%1%s*%)",
        function(q, body)
            local reversed = body:reverse()
            stats.reverse = stats.reverse + 1
            return string.format("%q", reversed)
        end)
    return src
end

local function fold_table_concat(src, stats)
    local changed = true
    local passes = 0

    while changed and passes < 8 do
        changed = false
        passes = passes + 1

        src = src:gsub("table%.concat%s*%(%s*{%s*([^{}]-)%s*}%s*%)",
            function(items)
                local vals = {}
                local ok = true

                for token in items:gmatch('"([^"]*)"') do
                    vals[#vals+1] = token
                end

                local count = 0
                for _ in items:gmatch('"') do count = count + 1 end

                if count % 2 ~= 0 then ok = false end
                if ok and #vals > 0 then
                    stats.table_concat = stats.table_concat + 1
                    changed = true
                    return string.format("%q", table.concat(vals))
                end

                return "table.concat({" .. items .. "})"
            end)
    end

    return src
end

local function fold_simple_arithmetic(src, stats)
    -- Safe, intentionally small constant folder. It only evaluates literals.
    local ops = {
        {"(%-?%d+)%s*%+%s*(%-?%d+)", function(a,b) return a+b end},
        {"(%-?%d+)%s*%-%s*(%-?%d+)", function(a,b) return a-b end},
        {"(%-?%d+)%s*%*%s*(%-?%d+)", function(a,b) return a*b end},
        {"(%-?%d+)%s*/%s*(%-?%d+)", function(a,b)
            if b == 0 then return nil end
            return a/b
        end},
    }

    local changed = true
    local rounds = 0

    while changed and rounds < 10 do
        changed = false
        rounds = rounds + 1

        for _, op in ipairs(ops) do
            src = src:gsub(op[1], function(a,b)
                a,b = tonumber(a), tonumber(b)
                local v = op[2](a,b)
                if v == nil or v ~= v or v == math.huge or v == -math.huge then
                    return tostring(a) .. " " .. " " .. tostring(b)
                end
                changed = true
                stats.arithmetic = stats.arithmetic + 1
                if math.floor(v) == v then return tostring(v) end
                return tostring(v)
            end)
        end
    end

    return src
end

local function simplify_booleans(src, stats)
    local replacements = {
        {"if%s+false%s+then%s+(.-)%s+end", ""},
        {"if%s+nil%s+then%s+(.-)%s+end", ""},
        {"while%s+false%s+do%s+(.-)%s+end", ""},
    }

    for _, r in ipairs(replacements) do
        src, n = src:gsub(r[1], r[2])
        stats.dead_blocks = stats.dead_blocks + n
    end

    src = src:gsub("(%f[%w]true%f[%W])%s+and%s+([^%s]+)%s+or%s+([^%s]+)",
        function(_, a, b)
            stats.boolean = stats.boolean + 1
            return a
        end)

    return src
end

local function simplify_luraph_alias_tables(src, stats)
    -- Luraph frequently creates:
    -- d={[0b10]=1,[1]=d}; d[0b11]=d
    -- These are accessor indirections. We only remove the exact harmless
    -- numeric-normalized form when it is provably self-referential.
    local before = src

    src = src:gsub(
        "([%a_][%w_]*)%s*=%s*{%s*%[%s*2%s*%]%s*=%s*1%s*,%s*%[%s*1%s*%]%s*=%s*%1%s*}%s*%1%[3%]%s*=%s*%1",
        function(v)
            stats.alias_tables = stats.alias_tables + 1
            return "-- [luraph accessor table removed: " .. v .. "]"
        end)

    return src
end

local function detect_luraph(src, report)
    local score = 0
    local markers = {
        "Luraph Obfuscator",
        "a%.F%[",
        "a:H%(",
        "a:G%(",
        "bit32%.bxor",
        "string%.byte",
        "table%.concat",
        "return%(%s*{%s*i%s*=",
    }

    for _, p in ipairs(markers) do
        if src:find(p) then
            score = score + 1
            report.markers[#report.markers+1] = p
        end
    end

    report.luraph_score = score
    report.likely_luraph = score >= 3
end

local function strip_comments(src, stats)
    -- Do not remove comments globally: comments can occur inside long strings.
    -- Only remove the common generated banner.
    src, n = src:gsub("%-%-%s*This file was protected using Luraph Obfuscator v[%d%.]+%s*%b[]", "")
    stats.banner = stats.banner + n
    return src
end

local function tidy(src)
    src = src:gsub("[ \t]+\n", "\n")
    src = src:gsub("\n\n\n+", "\n\n")
    src = src:gsub("^%s+", "")
    src = src:gsub("%s+$", "")
    return src
end

function M.deobfuscate(source, options)
    options = options or {}
    local report = {
        likely_luraph = false,
        luraph_score = 0,
        markers = {},
        passes = 0,
        binary = 0,
        hex = 0,
        strings = 0,
        string_char = 0,
        reverse = 0,
        table_concat = 0,
        arithmetic = 0,
        boolean = 0,
        dead_blocks = 0,
        alias_tables = 0,
        banner = 0,
    }

    assert(type(source) == "string", "source must be a string")

    local src = source
    detect_luraph(src, report)

    local maxpasses = tonumber(options.MaxPasses) or 8
    if maxpasses < 1 then maxpasses = 1 end
    if maxpasses > 50 then maxpasses = 50 end

    for pass = 1, maxpasses do
        local before = src

        src = normalize_numbers(src, report)
        src = decode_string_literals(src, report)
        src = fold_string_char(src, report)
        src = fold_reverse(src, report)
        src = fold_table_concat(src, report)
        src = fold_simple_arithmetic(src, report)
        src = simplify_booleans(src, report)
        src = simplify_luraph_alias_tables(src, report)
        src = strip_comments(src, report)
        src = tidy(src)

        report.passes = pass

        if src == before then
            break
        end
    end

    report.note =
        "Static-only pass. A full Luraph VM cannot be safely or reliably " ..
        "recovered from arbitrary source using pattern substitution alone. " ..
        "This output is intended as an intermediate artifact for CTF analysis."

    return src, report
end

function M.print_report(r)
    print("=== Luraph Deobfuscator ===")
    print("Likely Luraph: " .. tostring(r.likely_luraph))
    print("Detection score: " .. tostring(r.luraph_score))
    print("Passes: " .. tostring(r.passes))
    print("Binary literals: " .. tostring(r.binary))
    print("Hex literals: " .. tostring(r.hex))
    print("String escapes: " .. tostring(r.strings))
    print("string.char: " .. tostring(r.string_char))
    print("string.reverse: " .. tostring(r.reverse))
    print("table.concat: " .. tostring(r.table_concat))
    print("Arithmetic folds: " .. tostring(r.arithmetic))
    print("Boolean folds: " .. tostring(r.boolean))
    print("Dead blocks: " .. tostring(r.dead_blocks))
    print("Accessor tables: " .. tostring(r.alias_tables))
end

return M
