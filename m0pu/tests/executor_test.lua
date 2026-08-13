-- m0pu executor test
-- Replace TARGET with an actual LocalScript/ModuleScript available to the executor.
-- This reports failures instead of hiding them.

local RAW_URL = "https://raw.githubusercontent.com/rwcp/rwcp/main/m0pu/main.lua"

local function load_m0pu()
    local src = game:HttpGet(RAW_URL)
    local f, err = loadstring(src)
    assert(f, "m0pu compile error: " .. tostring(err))
    local ok, result = pcall(f)
    assert(ok, "m0pu load error: " .. tostring(result))
    assert(type(result) == "table", "m0pu returned " .. type(result))
    return result
end

local m0pu = load_m0pu()
print("m0pu version:", m0pu.VERSION)

local TARGET = nil
-- Example:
-- TARGET = game:GetService("Players").LocalPlayer.PlayerScripts:FindFirstChild("YourScript")

assert(TARGET, "Set TARGET to the script you want to test")

assert(type(getscriptbytecode) == "function", "getscripbytecode is unavailable")

local ok_bc, bytecode = pcall(getscriptbytecode, TARGET)
assert(ok_bc, "getscriptbytecode failed: " .. tostring(bytecode))
assert(type(bytecode) == "string" and #bytecode > 0, "empty bytecode")

local ok_result, result = pcall(function()
    return m0pu.decompile(bytecode, {
        diagnostics = true,
        validate = true,
    })
end)

if not ok_result then
    error("m0pu.decompile crashed:\n" .. tostring(result))
end

assert(type(result) == "table", "decompile did not return a result table")

print("source bytes:", #(result.source or ""))
print("warnings:", #(result.warnings or {}))
print("diagnostics:", #(result.diagnostics or {}))

if result.source then
    print("----- m0pu output -----")
    print(result.source)
    print("----- end output -----")
end

for _, d in ipairs(result.diagnostics or {}) do
    warn(("[%s] %s"):format(
        tostring(d.level or "info"),
        tostring(d.message or d)
    ))
end

print("m0pu executor test completed")
