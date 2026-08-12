# Lua VM Deobfuscator Suite

Static CTF/reverse-engineering helper for Lua/Luau source. It never executes the target.

## Supported pattern families

- Luraph v13/v14.x (including v14.7/v14.8-style markers)
- Prometheus
- IronBrew / IronBrew2
- MoonSec V3/V4
- luaobfuscator
- generic Lua VM/state-machine patterns

## Roblox usage

Host `lua_vm_suite.lua` on a public repository and use its raw URL:

```lua
local D = loadstring(game:HttpGet("YOUR_RAW_URL/lua_vm_suite.lua"))()

local source = [[
-- obfuscated Luau
]]

local clean, report = D.deobfuscate(source, {
    MaxPasses = 20,
})

print(clean)
D.print_report(report)
D.print_vm_report(report.vm)
print(D.ir_to_text(report.ir))
```

To analyze a remote text file, fetch the text yourself and pass it to `deobfuscate`; the suite does not fetch or execute targets internally.

## What it does

- detects common obfuscator markers
- decodes safe numeric/string escapes
- folds literal `string.char`, `string.reverse`, `table.concat`
- folds selected literal `bit32` operations
- folds simple literal arithmetic
- identifies likely VM state variables
- identifies constant-cache and handler candidates
- identifies probable opcode/state assignments
- emits a small static VM IR
- produces a report with family/detection and transformation statistics

## Important limitation

A generic static script cannot guarantee reconstruction of arbitrary Luraph, MoonSec, Prometheus, or custom VM bytecode. Virtualized handlers, encrypted functions, native extensions, and environment-dependent behavior require target-specific research. The suite intentionally does not execute unknown code or bundle leaked/private implementations.
