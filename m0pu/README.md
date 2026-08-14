# m0pu

Production-oriented Luau bytecode analysis and source-recovery library.

## Layout

```text
m0pu/
├── main.lua
├── archive/
│   ├── README.md
│   ├── m0pu_v1.lua
│   ├── m0pu_v2.lua
│   ├── m0pu_v3.lua
│   ├── m0pu_v4.lua
│   └── m0pu_v5.lua
└── tests/
    ├── smoke.lua
    └── executor_test.lua
```

`main.lua` is the runtime entry point. The archive contains historical builds
for regression/reference comparison.

## Roblox/executor smoke test

```lua
local m0pu = loadstring(game:HttpGet(
    "https://raw.githubusercontent.com/rwcp/rwcp/main/m0pu/main.lua"
))()

print("m0pu version:", m0pu.VERSION)
```

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
```

`validate=true` only performs validation that the host adapter actually
provides; it must not be treated as proof of semantic equivalence unless a
real Luau compiler/runtime is supplied.
