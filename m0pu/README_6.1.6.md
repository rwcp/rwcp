# m0pu 6.1.6

This release fixes the semantic lifting bug exposed by the 495-byte Roblox Luau regression target.

## Main fix

`NAMECALL` is VM call preparation, not a source-level register assignment. m0pu now:

- preserves the receiver from `NAMECALL B`;
- resolves the method name from the NAMECALL AUX constant index;
- treats `CALL B` as including NAMECALL's implicit `self` argument;
- emits only the explicit source arguments;
- prevents NAMECALL from corrupting SSA state for register A;
- fuses the direct NAMECALL/CALL pair into a semantic `methodcall` value;
- suppresses NAMECALL from source emission.

The expected reconstruction moves from malformed expressions such as:

```lua
game:GetService()(t1, "ReplicatedStorage")
```

toward:

```lua
game:GetService("ReplicatedStorage")
```

This is a semantic-lifting fix, not a printer-only patch.
