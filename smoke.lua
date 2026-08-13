-- m0pu smoke test
-- This test checks that the module loads and its public API exists.
-- It deliberately does not fake a compiler or bytecode validation backend.

local RAW_URL = "https://raw.githubusercontent.com/rwcp/rwcp/main/m0pu/main.lua"

local source = game:HttpGet(RAW_URL)
assert(type(source) == "string" and #source > 1000, "m0pu source was not downloaded")

local chunk = loadstring(source)
assert(type(chunk) == "function", "m0pu source did not compile")

local m0pu = chunk()
assert(type(m0pu) == "table", "m0pu did not return its module table")
assert(type(m0pu.decompile) == "function", "missing m0pu.decompile")
assert(type(m0pu.disassemble) == "function", "missing m0pu.disassemble")
assert(type(m0pu.analyze) == "function", "missing m0pu.analyze")
assert(type(m0pu.VERSION) == "string", "missing m0pu.VERSION")

print(("m0pu smoke test passed: %s"):format(m0pu.VERSION))
