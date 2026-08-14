# m0pu 6.1.5

This build adds the Roblox Luau opcode-encoding layer.

Roblox's serialized bytecode can use a `BytecodeEncoder` transform where the
opcode byte is multiplied by 227 modulo 256. The modular inverse is 203.
Operands and AUX words remain unchanged.

The parser now:
- auto-detects the Roblox opcode transform by comparing valid opcode ratios;
- supports `options.roblox = true` to force Roblox decoding;
- supports `options.roblox = false` to force native Luau decoding;
- records `proto.codeEncoding` for diagnostics;
- exposes the raw opcode as `instruction.rawop`.

For Roblox bytecode, the expected disassembly header now contains:

    encoding=RobloxOpcodeEncoder(227)

For native Luau bytecode:

    encoding=LuauNative
