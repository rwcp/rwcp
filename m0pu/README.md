# m0pu

Production-oriented Luau bytecode analysis and source-recovery library.

## Layout

```text
m0pu/
├── main.lua
└── tests/
    ├── smoke.lua
    └── executor_test.lua
```

`main.lua` is the complete runtime library. The test files contain only executable
tests; they do not claim bytecode/compiler validation that is not actually available.

## Roblox/executor smoke test

Load the library:

```lua
local m0pu = loadstring(game:HttpGet(
    "https://raw.githubusercontent.com/rwcp/rwcp/main/m0pu/main.lua"
))()

print("m0pu version:", m0pu.VERSION)
```

Then run `tests/executor_test.lua` after replacing its `RAW_URL` only if the
repository path is different.

## Testing a script

In an environment exposing `getscriptbytecode`:

```lua
local m0pu = loadstring(game:HttpGet(
    "https://raw.githubusercontent.com/rwcp/rwcp/main/m0pu/main.lua"
))()

local target = game:GetService("Players").LocalPlayer.PlayerScripts:FindFirstChild("YourScript")

assert(target, "target script not found")

local bytecode = getscriptbytecode(target)
local result = m0pu.decompile(bytecode, {
    diagnostics = true,
    validate = true,
})

print(result.source)

if result.diagnostics then
    for _, d in ipairs(result.diagnostics) do
        warn(("[%s] %s"):format(
            tostring(d.level or "info"),
            tostring(d.message or d)
        ))
    end
end
```

## Important

`validate=true` uses the validation adapter exposed by the implementation. A
real Luau compiler/runtime must be supplied by the host before recompilation or
differential execution can be claimed as successful.

Do not interpret a successful source print as proof of semantic equivalence.

## GitHub raw URL

After pushing `m0pu/main.lua` to the `main` branch:

```text
https://raw.githubusercontent.com/rwcp/rwcp/main/m0pu/main.lua
```
