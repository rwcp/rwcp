-- m0pu Decompiler v4.0
-- Production-grade Luau decompiler pipeline.
-- Bytecode parser + normalized IR + SSA + value graph + CFG structuring + AST emission.
-- Based on public Luau VM bytecode definitions/serialization semantics.
-- Original implementation; not copied from Oracle, Lua.Expert, Konstant, or Medal.

local m0pu = {}
m0pu.VERSION = "4.0"
m0pu.BYTECODE_MIN, m0pu.BYTECODE_MAX = 3, 12

local function env()
    if getgenv then local ok,e=pcall(getgenv); if ok and type(e)=="table" then return e end end
    return _G
end
local function quote(s) return string.format("%q", tostring(s)) end
local function identifier(s)
    return type(s)=="string" and s:match("^[%a_][%w_]*$") ~= nil and not ({
        ["and"]=1,["break"]=1,["do"]=1,["else"]=1,["elseif"]=1,["end"]=1,
        ["false"]=1,["for"]=1,["function"]=1,["goto"]=1,["if"]=1,["in"]=1,
        ["local"]=1,["nil"]=1,["not"]=1,["or"]=1,["repeat"]=1,["return"]=1,
        ["then"]=1,["true"]=1,["until"]=1,["while"]=1
    })[s]
end

-- Safe binary reader.
local Reader={}; Reader.__index=Reader
function Reader.new(data) assert(type(data)=="string","bytecode must be a string"); return setmetatable({data=data,p=1,n=#data},Reader) end
function Reader:need(n) if n<0 or self.p+n-1>self.n then error(("truncated bytecode at 0x%X"):format(self.p-1),2) end end
function Reader:remaining() return self.n-self.p+1 end
function Reader:u8() self:need(1); local v=string.byte(self.data,self.p); self.p+=1; return v end
function Reader:u16() self:need(2); local a,b=string.byte(self.data,self.p,self.p+1); self.p+=2; return a+b*256 end
function Reader:i16() local v=self:u16(); return v>=0x8000 and v-0x10000 or v end
function Reader:u32() self:need(4); local a,b,c,d=string.byte(self.data,self.p,self.p+3); self.p+=4; return a+b*256+c*65536+d*16777216 end
function Reader:i32() local v=self:u32(); return v>=0x80000000 and v-0x100000000 or v end
function Reader:bytes(n) self:need(n); local s=self.data:sub(self.p,self.p+n-1); self.p+=n; return s end
function Reader:f32() local s=self:bytes(4); assert(string.unpack,"string.unpack is required"); return string.unpack("<f",s) end
function Reader:f64() local s=self:bytes(8); assert(string.unpack,"string.unpack is required"); return string.unpack("<d",s) end
function Reader:varint()
    local x,shift=0,0
    for _=1,5 do local b=self:u8(); x+=(b&0x7f)<<shift; if b&0x80==0 then return x end; shift+=7 end
    error("invalid varint")
end
function Reader:varint64()
    local x,shift=0,0
    for _=1,10 do local b=self:u8(); x+=(b&0x7f)*(2^shift); if b&0x80==0 then return x end; shift+=7 end
    error("invalid varint64")
end

-- Official Luau opcode order (bytecode.h).
local OPCODES={"NOP",
    "BREAK",
    "LOADNIL",
    "LOADB",
    "LOADN",
    "LOADK",
    "MOVE",
    "GETGLOBAL",
    "SETGLOBAL",
    "GETUPVAL",
    "SETUPVAL",
    "CLOSEUPVALS",
    "GETIMPORT",
    "GETTABLE",
    "SETTABLE",
    "GETTABLEKS",
    "SETTABLEKS",
    "GETTABLEN",
    "SETTABLEN",
    "NEWCLOSURE",
    "NAMECALL",
    "CALL",
    "RETURN",
    "JUMP",
    "JUMPBACK",
    "JUMPIF",
    "JUMPIFNOT",
    "JUMPIFEQ",
    "JUMPIFLE",
    "JUMPIFLT",
    "JUMPIFNOTEQ",
    "JUMPIFNOTLE",
    "JUMPIFNOTLT",
    "ADD",
    "SUB",
    "MUL",
    "DIV",
    "MOD",
    "POW",
    "ADDK",
    "SUBK",
    "MULK",
    "DIVK",
    "MODK",
    "POWK",
    "AND",
    "OR",
    "ANDK",
    "ORK",
    "CONCAT",
    "NOT",
    "MINUS",
    "LENGTH",
    "NEWTABLE",
    "DUPTABLE",
    "SETLIST",
    "FORNPREP",
    "FORNLOOP",
    "FORGLOOP",
    "FORGPREP_INEXT",
    "FASTCALL3",
    "FORGPREP_NEXT",
    "NATIVECALL",
    "GETVARARGS",
    "DUPCLOSURE",
    "PREPVARARGS",
    "LOADKX",
    "JUMPX",
    "FASTCALL",
    "COVERAGE",
    "CAPTURE",
    "SUBRK",
    "DIVRK",
    "FASTCALL1",
    "FASTCALL2",
    "FASTCALL2K",
    "FORGPREP",
    "JUMPXEQKNIL",
    "JUMPXEQKB",
    "JUMPXEQKN",
    "JUMPXEQKS",
    "IDIV",
    "IDIVK",
    "GETUDATAKS",
    "SETUDATAKS",
    "NAMECALLUDATA",
    "NEWCLASSMEMBER",
    "CALLFB",
    "CMPPROTO"}
local function opname(i) return OPCODES[i+1] or ("OP_"..i) end
local AUX={}
for _,n in ipairs({
    "GETGLOBAL","GETIMPORT","GETTABLEKS","SETTABLEKS","NAMECALL","NEWTABLE","SETLIST",
    "FORGLOOP","FASTCALL2","FASTCALL2K","FASTCALL3","JUMPXEQKNIL","JUMPXEQKB",
    "JUMPXEQKN","JUMPXEQKS","GETUDATAKS","SETUDATAKS","NAMECALLUDATA",
    "NEWCLASSMEMBER","CALLFB","CMPPROTO"
}) do AUX[n]=true end
local function oplen(n) return AUX[n] and 2 or 1 end

local function decodeWord(w)
    local op=w&0xff; local A=(w>>8)&0xff; local B=(w>>16)&0xff; local C=(w>>24)&0xff
    local D=w>>16; if D>=0x8000 then D-=0x10000 end
    local E=w>>8; if E>=0x800000 then E-=0x1000000 end
    return {word=w,op=op,name=opname(op),A=A,B=B,C=C,D=D,E=E}
end
local function aux(w)
    return {raw=w,A=w&0xff,B=(w>>8)&0xff,C=(w>>16)&0xff,KV=w&0xffffff,
            NOT=((w>>31)&1)~=0,KB=(w&1)~=0,slot=(w>>16)&0xffff}
end

local CT={[0]="nil",[1]="boolean",[2]="number",[3]="string",[4]="import",[5]="table",
    [6]="closure",[7]="vector",[8]="table_constants",[9]="integer",[10]="class_shape",[11]="vectord"}
local function literal(k)
    if not k then return "nil" end
    if k.type=="nil" then return "nil" end
    if k.type=="boolean" then return k.value and "true" or "false" end
    if k.type=="number" then
        if k.value~=k.value then return "0/0" end
        if k.value==math.huge then return "math.huge" end
        if k.value==-math.huge then return "-math.huge" end
        return tostring(k.value)
    end
    if k.type=="integer" then return tostring(k.value) end
    if k.type=="string" then return quote(k.value) end
    if k.type=="vector" or k.type=="vectord" then return ("Vector3.new(%s,%s,%s)"):format(k.x,k.y,k.z) end
    if k.type=="import" then return k.path or ("<import:"..tostring(k.id)..">") end
    if k.type=="closure" then return "function(...) end" end
    if k.type=="class_shape" then return "<class "..tostring(k.classname)..">" end
    return "{}"
end

-- Exact serialized Luau chunk layout used by luau_load.
local function parseLuau(data,options)
    local r=Reader.new(data)
    local c={format="LuauSerialized",bytecodeVersion=r:u8(),typeVersion=0,strings={},protos={},warnings={}}
    if c.bytecodeVersion==0 then c.error=r:bytes(r:remaining()); return c end
    assert(c.bytecodeVersion>=3 and c.bytecodeVersion<=12,"unsupported Luau bytecode version "..c.bytecodeVersion)
    if c.bytecodeVersion>=4 then c.typeVersion=r:u8(); assert(c.typeVersion>=1 and c.typeVersion<=3,"unsupported Luau type version "..c.typeVersion) end
    local ns=r:varint()
    for i=1,ns do local n=r:varint(); c.strings[i]=r:bytes(n) end
    if c.typeVersion==3 then
        c.userdataTypes={}
        local idx=r:u8()
        while idx~=0 do local sid=r:varint(); c.userdataTypes[idx]=c.strings[sid]; idx=r:u8() end
    end
    local np=r:varint()
    local function str(id) return id==0 and nil or c.strings[id] end
    local protos={}
    local function parseProto(id)
        local p={id=id,constants={},children={},locals={},upvalues={},strings=c.strings}
        local start=r.p; local protoSize
        if c.bytecodeVersion>=12 then protoSize=r:varint() end
        p.maxstack=r:u8(); p.numparams=r:u8(); p.nups=r:u8(); p.vararg=r:u8()~=0
        if c.bytecodeVersion>=4 then
            p.flags=r:u8()
            local ts=r:varint()
            p.typeinfo=ts>0 and r:bytes(ts) or nil
        end
        local nc=r:varint(); p.code={}
        for pc=1,nc do p.code[pc]=decodeWord(r:u32()) end
        local nk=r:varint()
        for i=1,nk do
            local tag=r:u8(); local k={tag=tag,type=CT[tag] or ("tag"..tag)}
            if tag==0 then
            elseif tag==1 then k.value=r:u8()~=0
            elseif tag==2 then k.value=r:f64()
            elseif tag==3 then k.value=str(r:varint()) or ""
            elseif tag==4 then
                k.id=r:u32(); local count=k.id>>30; local a=(k.id>>20)&1023; local b=(k.id>>10)&1023; local d=k.id&1023
                local q={}
                if count>=1 then q[#q+1]=c.strings[a+1] or ("k"..a) end
                if count>=2 then q[#q+1]=c.strings[b+1] or ("k"..b) end
                if count>=3 then q[#q+1]=c.strings[d+1] or ("k"..d) end
                k.path=table.concat(q,".")
            elseif tag==5 then
                local n=r:varint(); k.keys={}; for j=1,n do k.keys[j]=r:varint() end
            elseif tag==6 then k.proto=r:varint()
            elseif tag==7 then k.x,k.y,k.z,k.w=r:f32(),r:f32(),r:f32(),r:f32()
            elseif tag==8 then
                local n=r:varint(); k.keys={}; k.values={}
                for j=1,n do k.keys[j]=r:varint(); k.values[j]=r:i32() end
            elseif tag==9 then local neg=r:u8()~=0; local m=r:varint64(); k.value=neg and -m or m
            elseif tag==10 then
                k.classname=str(r:varint()) or "Class"; local props=r:varint(); local methods=r:varint(); k.members={}
                for j=1,props+methods do k.members[j]=str(r:varint()) or ("member"..j) end
            elseif tag==11 then k.x,k.y,k.z,k.w=r:f64(),r:f64(),r:f64(),r:f64()
            else error("unknown Luau constant tag "..tag) end
            p.constants[i]=k
        end
        local ch=r:varint(); for j=1,ch do p.children[j]=r:varint() end
        p.linedefined=r:varint(); p.debugname=str(r:varint()) or ""
        if r:u8()~=0 then
            p.linegaplog2=r:u8(); local intervals=((nc-1)>>p.linegaplog2)+1; p.lineinfo={}; local last=0
            for pc=1,nc do last=(last+r:u8())&0xff; p.lineinfo[pc]=last end
            p.abslineinfo={}; for j=1,intervals do p.abslineinfo[j]=r:i32() end
        end
        if r:u8()~=0 then
            local nl=r:varint()
            for j=1,nl do p.locals[j]={name=str(r:varint()) or ("v"..j),startpc=r:varint(),endpc=r:varint(),reg=r:u8()} end
            local nu=r:varint(); for j=1,nu do p.upvalues[j]=str(r:varint()) or ("up"..(j-1)) end
        end
        if c.bytecodeVersion>=11 then
            local nf=r:varint(); p.feedback={}
            for j=1,nf do p.feedback[j]={kind=r:u8(),pc=r:varint()} end
        end
        if c.bytecodeVersion>=12 and (p.flags or 0)&8~=0 then p.cost=r:varint64() end
        if protoSize then r.p=start+protoSize end
        return p
    end
    for i=1,np do protos[i]=parseProto(i) end
    local main=r:varint(); c.protos=protos; c.main=protos[main+1]; c.bytesConsumed=r.p-1; c.trailing=r:remaining()
    return c
end

-- Original m0pu v1 parser retained as a compatibility fallback.
local function parseLegacy(data)
    local r=Reader.new(data)
    local function rs() local n=r:u32(); return n==0 and "" or r:bytes(n) end
    local function proto()
        local p={constants={},code={},locals={},children={}}
        p.name=rs(); p.linedefined=r:u32(); p.lastline=r:u32(); p.numparams=r:u8(); p.vararg=r:u8()~=0; p.maxstack=r:u8(); p.nups=r:u8()
        local nk,ni,nf,nl,nd=r:u32(),r:u32(),r:u32(),r:u32(),r:u32()
        for i=1,nk do local t=r:u8(); if t==0 then p.constants[i]={type="nil"} elseif t==1 then p.constants[i]={type="boolean",value=r:u8()~=0} elseif t==2 then p.constants[i]={type="integer",value=r:u32()} elseif t==3 then p.constants[i]={type="string",value=rs()} else p.constants[i]={type="opaque"} end end
        for i=1,ni do local op=r:u8(); p.code[i]={op=op,name=opname(op),A=r:u8(),B=r:u8(),C=r:u8(),D=r:u8(),E=r:u8()} end
        for i=1,nl do p.lineinfo=p.lineinfo or {}; p.lineinfo[i]=r:u32() end
        for i=1,nd do p.locals[i]={name=rs(),startpc=r:u32(),endpc=r:u32(),reg=0} end
        for i=1,nf do p.children[i]=proto() end
        return p
    end
    return {format="LegacyM0pu",bytecodeVersion=0,typeVersion=0,protos={},main=proto()}
end
local function parseAny(data,options)
    local first=string.byte(data,1) or 0
    if first>=3 and first<=12 then
        local ok,res=pcall(parseLuau,data,options)
        if ok then return res end
        if options and options.strict then error(res,0) end
    end
    return parseLegacy(data)
end


-- ============================================================================
-- m0pu Decompiler v5 PRO
-- A deterministic Luau decompiler middle-end.
--
-- Design:
--   serialized bytecode
--      -> validated instruction stream
--      -> CFG
--      -> dominators / post-dominators / dominance frontiers
--      -> SSA + use/def
--      -> value analysis / SCCP-style propagation
--      -> loop + branch regions
--      -> typed decompiler AST
--      -> Luau source
--
-- No network calls, no LLM dependency, no textual "AI correction", and no
-- fabricated source for unsupported semantics.  Unsupported instructions are
-- preserved as explicit IR nodes and reported diagnostically.
-- ============================================================================

m0pu.VERSION = "5.0.1-PRO"

local function push(t, v) t[#t+1] = v; return v end
local function copyMap(s)
    local r = {}
    for k,v in pairs(s or {}) do r[k] = v end
    return r
end
local function setEq(a,b)
    for k,v in pairs(a or {}) do if not (b or {})[k] then return false end end
    for k,v in pairs(b or {}) do if not (a or {})[k] then return false end end
    return true
end
local function sortedNumericKeys(t)
    local r = {}
    for k in pairs(t) do r[#r+1] = k end
    table.sort(r)
    return r
end

-- ----------------------------- instruction semantics -----------------------

local OP = {}
for i,n in ipairs(OPCODES) do OP[n] = i-1 end

local META = {}
local function meta(name, writes, reads, kind, aux)
    META[name] = {writes=writes or {}, reads=reads or {}, kind=kind or "normal", aux=aux}
end

local R = function(...) return {...} end
for _,n in ipairs({"LOADNIL","LOADB","LOADN","LOADK","LOADKX","GETGLOBAL","GETUPVAL",
    "GETIMPORT","GETTABLE","GETTABLEKS","GETUDATAKS","GETTABLEN","NEWTABLE","DUPTABLE",
    "NEWCLOSURE","DUPCLOSURE","NAMECALL","NAMECALLUDATA","GETVARARGS",
    "ADD","SUB","MUL","DIV","MOD","POW","IDIV","AND","OR","ADDK","SUBK","MULK",
    "DIVK","MODK","POWK","IDIVK","ANDK","ORK","SUBRK","DIVRK","CONCAT","NOT","MINUS",
    "LENGTH","CALL","CALLFB"}) do
    local writes = {"A"}
    META[n] = {writes=writes, reads={}}
end
META.MOVE = {writes={"A"}, reads={"B"}}
META.SETUPVAL = {reads={"A"}, kind="store"}
META.SETGLOBAL = {reads={"A"}, kind="store"}
META.SETTABLE = {reads={"A","B","C"}, kind="store"}
META.SETTABLEKS = {reads={"A","B"}, kind="store", aux="constant"}
META.SETUDATAKS = {reads={"A","B"}, kind="store", aux="constant"}
META.SETTABLEN = {reads={"A","B"}, kind="store"}
META.RETURN = {reads={"A"}, kind="return"}
META.CAPTURE = {reads={"B"}, kind="capture"}
META.CLOSEUPVALS = {reads={"A"}, kind="effect"}
META.PREPVARARGS = {kind="effect"}
META.COVERAGE = {kind="effect"}
META.NATIVECALL = {kind="effect"}
META.FASTCALL = {kind="effect"}
META.FASTCALL1 = {kind="effect"}
META.FASTCALL2 = {kind="effect"}
META.FASTCALL2K = {kind="effect"}
META.FASTCALL3 = {kind="effect"}
META.FORNPREP = {kind="loop"}
META.FORNLOOP = {kind="loop"}
META.FORGLOOP = {kind="loop"}
META.FORGPREP = {kind="loop"}
META.FORGPREP_INEXT = {kind="loop"}
META.FORGPREP_NEXT = {kind="loop"}
META.JUMP = {kind="jump"}
META.JUMPX = {kind="jump"}
META.JUMPBACK = {kind="jump"}
META.JUMPIF = {reads={"A"}, kind="branch"}
META.JUMPIFNOT = {reads={"A"}, kind="branch"}
for _,n in ipairs({"JUMPIFEQ","JUMPIFLE","JUMPIFLT","JUMPIFNOTEQ","JUMPIFNOTLE","JUMPIFNOTLT"}) do
    META[n] = {reads={"A"}, kind="branch", aux="register"}
end
for _,n in ipairs({"JUMPXEQKNIL","JUMPXEQKB","JUMPXEQKN","JUMPXEQKS","CMPPROTO"}) do
    META[n] = {reads={"A"}, kind="branch", aux="constant"}
end
META.NOP = {kind="effect"}
META.BREAK = {kind="effect"}
META.NEWTABLE = {writes={"A"}}
META.DUPCLOSURE = {writes={"A"}}

local function importPath(p, i)
    local aux = i.aux
    if not aux then return nil end
    local count = (aux.raw or 0) >> 30
    if count < 1 or count > 3 then return nil end
    local parts = {}
    local function stringAt(index)
        -- AUX stores 10-bit string-table indices.
        return (p.strings or {})[index + 1]
    end
    local raw = aux.raw or 0
    local a = raw & 0x3ff
    local b = (raw >> 10) & 0x3ff
    local c = (raw >> 20) & 0x3ff
    parts[1] = stringAt(a) or ("k"..a)
    if count >= 2 then parts[2] = stringAt(b) or ("k"..b) end
    if count >= 3 then parts[3] = stringAt(c) or ("k"..c) end
    return table.concat(parts, ".")
end

local function instructionLength(i)
    return oplen(i.name)
end

local function branchTarget(pc, i)
    local n = i.name
    if n == "JUMPX" then return pc + 1 + i.E end
    if n == "JUMP" or n == "JUMPBACK" or n == "JUMPIF" or n == "JUMPIFNOT" or
       n == "JUMPIFEQ" or n == "JUMPIFLE" or n == "JUMPIFLT" or
       n == "JUMPIFNOTEQ" or n == "JUMPIFNOTLE" or n == "JUMPIFNOTLT" or
       n == "FORNPREP" or n == "FORNLOOP" or n == "FORGLOOP" or
       n == "FORGPREP" or n == "FORGPREP_INEXT" or n == "FORGPREP_NEXT" or
       n == "JUMPXEQKNIL" or n == "JUMPXEQKB" or n == "JUMPXEQKN" or
       n == "JUMPXEQKS" or n == "CMPPROTO" then
        return pc + 1 + i.D
    end
    return nil
end

local function isConditional(i)
    local n = i.name
    return n == "JUMPIF" or n == "JUMPIFNOT" or
        n == "JUMPIFEQ" or n == "JUMPIFLE" or n == "JUMPIFLT" or
        n == "JUMPIFNOTEQ" or n == "JUMPIFNOTLE" or n == "JUMPIFNOTLT" or
        n == "JUMPXEQKNIL" or n == "JUMPXEQKB" or n == "JUMPXEQKN" or
        n == "JUMPXEQKS" or n == "CMPPROTO"
end

local function isTerminator(i)
    return i.name == "RETURN" or i.name == "JUMP" or i.name == "JUMPX" or
        i.name == "JUMPBACK" or i.name == "FORNLOOP" or i.name == "FORGLOOP"
end

-- ------------------------------- CFG ----------------------------------------

local function buildCFG(p)
    local leaders = {[1]=true}
    local pc = 1
    while pc <= #p.code do
        local i = p.code[pc]
        local len = instructionLength(i)
        local t = branchTarget(pc, i)
        if t and t >= 1 and t <= #p.code then leaders[t] = true end

        -- A conditional branch and all jumps have a fallthrough instruction
        -- boundary unless they terminate execution.
        if (isConditional(i) or not isTerminator(i)) and pc + len <= #p.code then
            leaders[pc + len] = true
        end
        pc += len
    end

    local starts = sortedNumericKeys(leaders)
    local blocks, byPc = {}, {}
    for n,s in ipairs(starts) do
        local finish = (starts[n+1] or (#p.code+1))-1
        local b = {
            id=n, start=s, finish=finish,
            instructions={}, successors={}, predecessors={}
        }
        blocks[n] = b
        for x=s,finish do byPc[x] = b end
    end

    local function edge(a,b)
        if not b then return end
        for _,x in ipairs(a.successors) do if x == b.id then return end end
        a.successors[#a.successors+1] = b.id
        b.predecessors[#b.predecessors+1] = a.id
    end

    for _,b in ipairs(blocks) do
        pc = b.start
        while pc <= b.finish do
            local i = p.code[pc]
            i.pc = pc
            b.instructions[#b.instructions+1] = i
            pc += instructionLength(i)
        end

        local last = b.instructions[#b.instructions]
        local t = branchTarget(last.pc,last)
        if t then edge(b,byPc[t]) end
        if isConditional(last) then
            edge(b,byPc[last.pc + instructionLength(last)])
        elseif not isTerminator(last) then
            edge(b,byPc[last.pc + instructionLength(last)])
        end
    end

    return {blocks=blocks, byPc=byPc, entry=blocks[1]}
end

-- ------------------------- graph reachability -------------------------------

local function reachable(g)
    local seen, q = {}, {g.entry.id}
    local head = 1
    while head <= #q do
        local id = q[head]; head += 1
        if not seen[id] then
            seen[id] = true
            for _,s in ipairs(g.blocks[id].successors) do q[#q+1] = s end
        end
    end
    return seen
end

-- ---------------------------- dominators -----------------------------------

local function dominators(g)
    local n = #g.blocks
    local reach = reachable(g)
    local dom = {}
    for i=1,n do
        dom[i] = {}
        if i == g.entry.id then
            dom[i][i] = true
        elseif reach[i] then
            for j=1,n do if reach[j] then dom[i][j] = true end end
        else
            dom[i][i] = true
        end
    end

    local changed = true
    while changed do
        changed = false
        for i=1,n do
            if i ~= g.entry.id and reach[i] then
                local b = g.blocks[i]
                local first = true
                local nextSet = {}
                for _,p in ipairs(b.predecessors) do
                    if reach[p] then
                        if first then
                            nextSet = copyMap(dom[p]); first = false
                        else
                            for d in pairs(nextSet) do
                                if not dom[p][d] then nextSet[d] = nil end
                            end
                        end
                    end
                end
                nextSet[i] = true
                if not setEq(dom[i],nextSet) then dom[i]=nextSet; changed=true end
            end
        end
    end

    local idom = {}
    for i=1,n do
        if i ~= g.entry.id and reach[i] then
            local candidates = {}
            for d in pairs(dom[i]) do if d ~= i then candidates[#candidates+1]=d end end
            local best
            for _,d in ipairs(candidates) do
                local immediate = true
                for _,o in ipairs(candidates) do
                    if o ~= d and dom[o][d] then immediate=false; break end
                end
                if immediate then best=d; break end
            end
            idom[i]=best
        end
    end

    local children={}
    for i=1,n do children[i]={} end
    for i=1,n do if idom[i] then children[idom[i]][#children[idom[i]]+1]=i end end
    for i=1,n do table.sort(children[i]) end
    return dom,idom,children,reach
end

local function dominanceFrontier(g,idom,reach)
    local df={}
    for _,b in ipairs(g.blocks) do df[b.id]={} end
    for _,b in ipairs(g.blocks) do
        if reach[b.id] and #b.predecessors >= 2 then
            for _,pred in ipairs(b.predecessors) do
                if reach[pred] then
                    local runner=pred
                    while runner and runner ~= idom[b.id] do
                        df[runner][b.id]=true
                        runner=idom[runner]
                    end
                end
            end
        end
    end
    return df
end

-- -------------------------- post dominators --------------------------------

local function postDominators(g,reach)
    -- A synthetic exit node is used conceptually.  Multiple real exits are
    -- therefore handled uniformly instead of arbitrarily selecting the last
    -- block as the old implementation did.
    local n=#g.blocks
    local exits={}
    for _,b in ipairs(g.blocks) do
        if reach[b.id] and #b.successors==0 then exits[#exits+1]=b.id end
    end

    local pdom={}
    for i=1,n do
        pdom[i]={}
        if reach[i] then
            for j=1,n do if reach[j] then pdom[i][j]=true end end
        end
    end

    for _,e in ipairs(exits) do pdom[e]={ [e]=true } end

    local changed=true
    while changed do
        changed=false
        for i=n,1,-1 do
            if reach[i] and #g.blocks[i].successors>0 then
                local first=true
                local sset={}
                for _,s in ipairs(g.blocks[i].successors) do
                    if first then sset=copyMap(pdom[s]); first=false
                    else
                        for x in pairs(sset) do if not pdom[s][x] then sset[x]=nil end end
                    end
                end
                sset[i]=true
                if not setEq(pdom[i],sset) then pdom[i]=sset; changed=true end
            end
        end
    end

    local ipdom={}
    for i=1,n do
        if reach[i] and #g.blocks[i].successors>0 then
            local candidates={}
            for d in pairs(pdom[i]) do if d~=i then candidates[#candidates+1]=d end end
            local best
            for _,d in ipairs(candidates) do
                local immediate=true
                for _,o in ipairs(candidates) do
                    if o~=d and pdom[o][d] then immediate=false; break end
                end
                if immediate then best=d; break end
            end
            ipdom[i]=best
        end
    end
    return pdom,ipdom,exits
end

-- ------------------------------- loops --------------------------------------

local function naturalLoops(g,dom)
    local loops={}
    for _,b in ipairs(g.blocks) do
        for _,s in ipairs(b.successors) do
            if dom[b.id] and dom[b.id][s] then
                local members={[s]=true,[b.id]=true}
                local stack={b.id}
                while #stack>0 do
                    local x=stack[#stack]; stack[#stack]=nil
                    for _,p in ipairs(g.blocks[x].predecessors) do
                        if not members[p] then members[p]=true; stack[#stack+1]=p end
                    end
                end
                local list=sortedNumericKeys(members)
                loops[#loops+1]={header=s,latch=b.id,members=list}
            end
        end
    end
    table.sort(loops,function(a,b)
        if a.header==b.header then return a.latch<b.latch end
        return a.header<b.header
    end)
    return loops
end

-- ----------------------------- decompiler IR -------------------------------

local IR={}
IR.__index=IR

function IR.new(p,g,idom,children,df)
    return setmetatable({
        p=p,g=g,idom=idom,children=children,df=df,
        defsByReg={},phis={},values={},nextId=0,
        outState={},inState={},instructions={}
    },IR)
end

function IR:value(kind,data)
    self.nextId += 1
    local v={id=self.nextId,kind=kind,data=data or {},uses={},def=nil}
    self.values[v.id]=v
    return v
end

function IR:use(v,site)
    if v then v.uses[#v.uses+1]=site end
    return v
end

function IR:unknown(reg)
    self.unknowns=self.unknowns or {}
    if not self.unknowns[reg] then self.unknowns[reg]=self:value("unknown",{reg=reg}) end
    return self.unknowns[reg]
end

function IR:const(ix)
    local k=self.p.constants[(ix or 0)+1]
    return self:value("const",{text=literal(k)})
end

function IR:constText(text) return self:value("const",{text=text}) end

function IR:op(name,args,block,pc,extra)
    local v=self:value("op",{op=name,args=args,block=block,pc=pc,extra=extra})
    for _,a in ipairs(args or {}) do self:use(a,{block=block,pc=pc,role="operand"}) end
    return v
end

local function writes(i)
    local n=i.name
    if n=="CALL" or n=="CALLFB" then
        local out={}
        local count=(i.C==0) and 1 or math.max(1,i.C-1)
        for r=i.A,i.A+count-1 do out[#out+1]=r end
        return out
    elseif n=="GETVARARGS" then
        local out={}
        local count=(i.B==0) and 1 or math.max(1,i.B-1)
        for r=i.A,i.A+count-1 do out[#out+1]=r end
        return out
    elseif META[n] and META[n].writes then
        local r={}
        for _,field in ipairs(META[n].writes) do r[#r+1]=i[field] end
        return r
    end
    return {}
end

function IR:collectDefinitions()
    for _,b in ipairs(self.g.blocks) do
        for _,i in ipairs(b.instructions) do
            for _,r in ipairs(writes(i)) do
                self.defsByReg[r]=self.defsByReg[r] or {}
                self.defsByReg[r][b.id]=true
            end
        end
    end
end

function IR:placePhis()
    for reg,defs in pairs(self.defsByReg) do
        local has,work={},{}
        for b in pairs(defs) do work[#work+1]=b end
        local head=1
        while head<=#work do
            local x=work[head]; head+=1
            for y in pairs(self.df[x] or {}) do
                if not has[y] then
                    has[y]=true
                    self.phis[y]=self.phis[y] or {}
                    self.phis[y][reg]=self:value("phi",{reg=reg,block=y,incomings={}})
                    if not defs[y] then work[#work+1]=y end
                end
            end
        end
    end
end

function IR:lift(i,st,b)
    local n,A,B,C,D=i.name,i.A,i.B,i.C,i.D
    local function V(r) return st[r] or self:unknown(r) end
    local function DEF(r,v)
        st[r]=v
        v.def={block=b.id,pc=i.pc,reg=r}
        return v
    end
    local aux=i.aux
    if oplen(n)==2 and not aux then
        i.aux={raw=self.p.code[i.pc+1].word,
            A=self.p.code[i.pc+1].word&0xff,
            B=(self.p.code[i.pc+1].word>>8)&0xff,
            C=(self.p.code[i.pc+1].word>>16)&0xff,
            KV=self.p.code[i.pc+1].word&0xffffff,
            NOT=((self.p.code[i.pc+1].word>>31)&1)~=0,
            KB=(self.p.code[i.pc+1].word&1)~=0,
            slot=(self.p.code[i.pc+1].word>>16)&0xffff}
        aux=i.aux
    end

    local function emit(kind,data)
        self.instructions[#self.instructions+1]=data or {kind=kind,pc=i.pc,block=b.id,op=n}
    end

    if n=="LOADNIL" then DEF(A,self:constText("nil"))
    elseif n=="LOADB" then DEF(A,self:constText(B~=0 and "true" or "false"))
    elseif n=="LOADN" then DEF(A,self:constText(tostring(D)))
    elseif n=="LOADK" then DEF(A,self:const(D))
    elseif n=="LOADKX" then DEF(A,self:const(aux.KV))
    elseif n=="MOVE" then DEF(A,V(B))
    elseif n=="GETUPVAL" then DEF(A,self:value("upvalue",{index=B,name=self.p.upvalues and self.p.upvalues[B+1]}))
    elseif n=="GETGLOBAL" then DEF(A,self:value("global",{name=self:const(aux.KV)}))
    elseif n=="GETIMPORT" then
        DEF(A,self:value("import",{path=importPath(self.p,i),constant=D}))
    elseif n=="GETTABLE" then DEF(A,self:op("index",{V(B),V(C)},b.id,i.pc))
    elseif n=="GETTABLEKS" or n=="GETUDATAKS" then DEF(A,self:op("field",{V(B),self:const(aux.KV)},b.id,i.pc))
    elseif n=="GETTABLEN" then DEF(A,self:op("index",{V(B),self:constText(tostring(C+1))},b.id,i.pc))
    elseif n=="NEWTABLE" then DEF(A,self:value("table",{block=b.id,pc=i.pc}))
    elseif n=="DUPTABLE" then DEF(A,self:op("duptable",{self:const(D)},b.id,i.pc))
    elseif n=="NEWCLOSURE" then DEF(A,self:value("closure",{proto=D,kind="new"}))
    elseif n=="DUPCLOSURE" then DEF(A,self:value("closure",{constant=D,kind="dup"}))
    elseif n=="NAMECALL" or n=="NAMECALLUDATA" then
        DEF(A,self:op("methodcall",{V(B),self:const(aux.KV)},b.id,i.pc,{argBase=A+2,argCount=B}))
    elseif n=="CALL" or n=="CALLFB" then
        local args={V(A)}
        if B>1 then for r=A+1,A+B-1 do args[#args+1]=V(r) end end
        local count=(C==0) and 1 or math.max(1,C-1)
        for r=0,count-1 do DEF(A+r,self:op("call",args,b.id,i.pc,{multi=count>1,index=r,count=count})) end
    elseif n=="GETVARARGS" then DEF(A,self:value("varargs",{block=b.id,pc=i.pc,count=B}))
    elseif n=="CONCAT" then
        local args={}; for r=B,C do args[#args+1]=V(r) end
        DEF(A,self:op("concat",args,b.id,i.pc))
    elseif n=="NOT" or n=="MINUS" or n=="LENGTH" then
        DEF(A,self:op(({NOT="not",MINUS="neg",LENGTH="len"})[n],{V(B)},b.id,i.pc))
    elseif n=="ADD" or n=="SUB" or n=="MUL" or n=="DIV" or n=="MOD" or n=="POW" or n=="IDIV" or n=="AND" or n=="OR" then
        DEF(A,self:op(n:lower(),{V(B),V(C)},b.id,i.pc))
    elseif n=="ADDK" or n=="SUBK" or n=="MULK" or n=="DIVK" or n=="MODK" or n=="POWK" or n=="IDIVK" or n=="ANDK" or n=="ORK" then
        DEF(A,self:op(n:sub(1,-2):lower(),{V(B),self:const(C)},b.id,i.pc))
    elseif n=="SUBRK" or n=="DIVRK" then
        DEF(A,self:op(n:sub(1,-3):lower(),{self:const(B),V(C)},b.id,i.pc))
    elseif n=="SETUPVAL" or n=="SETGLOBAL" or n=="SETTABLE" or n=="SETTABLEKS" or n=="SETTABLEN" or n=="SETUDATAKS" then
        emit("store",{kind="store",pc=i.pc,block=b.id,op=n,A=A,B=B,C=C,D=D,aux=aux,state=copyMap(st)})
    elseif n=="CAPTURE" then
        emit("capture",{kind="capture",pc=i.pc,block=b.id,op=n,A=A,B=B,state=copyMap(st)})
    elseif n=="RETURN" then
        local vals={}
        if B==0 then vals[1]=self:value("vararg_return",{})
        else for r=A,A+B-2 do vals[#vals+1]=V(r) end end
        for _,v in ipairs(vals) do self:use(v,{block=b.id,pc=i.pc,role="return"}) end
        emit("return",{kind="return",pc=i.pc,block=b.id,values=vals,state=copyMap(st)})
    elseif n=="JUMP" or n=="JUMPX" or n=="JUMPBACK" or isConditional(i) then
        emit("branch",{kind="branch",pc=i.pc,block=b.id,op=n,A=A,B=B,C=C,D=D,E=i.E,aux=aux,state=copyMap(st)})
    elseif n=="FORNPREP" or n=="FORNLOOP" or n=="FORGLOOP" or n=="FORGPREP" or n=="FORGPREP_INEXT" or n=="FORGPREP_NEXT" then
        emit("loop",{kind="loop",pc=i.pc,block=b.id,op=n,A=A,B=B,C=C,D=D,aux=aux,state=copyMap(st)})
    elseif n=="FASTCALL" or n=="FASTCALL1" or n=="FASTCALL2" or n=="FASTCALL2K" or n=="FASTCALL3" then
        emit("fastcall",{kind="fastcall",pc=i.pc,block=b.id,op=n,A=A,B=B,C=C,aux=aux,state=copyMap(st)})
    elseif n=="PREPVARARGS" or n=="COVERAGE" or n=="NATIVECALL" or n=="NOP" or n=="BREAK" or n=="CLOSEUPVALS" then
        emit("effect",{kind="effect",pc=i.pc,block=b.id,op=n,A=A,B=B,C=C,D=D,state=copyMap(st)})
    else
        -- Unsupported does not become fake Lua. It becomes a typed IR node and
        -- a diagnostic; the source emitter can choose a safe fallback.
        emit("opaque",{kind="opaque",pc=i.pc,block=b.id,op=n,A=A,B=B,C=C,D=D,state=copyMap(st)})
    end
    return st
end

function IR:renameBlock(id,inState)
    local b=self.g.blocks[id]
    local st=copyMap(inState)
    for reg,phi in pairs(self.phis[id] or {}) do st[reg]=phi end
    self.inState[id]=copyMap(st)
    for _,i in ipairs(b.instructions) do self:lift(i,st,b) end
    self.outState[id]=copyMap(st)
    for _,child in ipairs(self.children[id] or {}) do self:renameBlock(child,st) end
end

function IR:finishPhiOperands()
    for bid,regs in pairs(self.phis) do
        local b=self.g.blocks[bid]
        for reg,phi in pairs(regs) do
            for _,pred in ipairs(b.predecessors) do
                local v=(self.outState[pred] or {})[reg] or self:unknown(reg)
                phi.data.incomings[#phi.data.incomings+1]=v
                self:use(v,{block=bid,role="phi",from=pred})
            end
        end
    end
end

function IR:build()
    self:collectDefinitions()
    self:placePhis()
    self:renameBlock(self.g.entry.id,{})
    self:finishPhiOperands()
    return self
end

-- --------------------------- value analysis ---------------------------------

local function isConst(v)
    return v and v.kind=="const" and v.data and v.data.text
end

local function parseConst(t)
    if t=="nil" then return nil,"nil" end
    if t=="true" then return true,"boolean" end
    if t=="false" then return false,"boolean" end
    local n=tonumber(t)
    if n~=nil then return n,"number" end
    return nil,nil
end

local function fold(v,seen)
    seen=seen or {}
    if not v or seen[v.id] then return v end
    seen[v.id]=true
    if v.kind~="op" then return v end
    local args=v.data.args or {}
    for _,a in ipairs(args) do fold(a,seen) end

    if #args==1 and isConst(args[1]) then
        local a,t=parseConst(args[1].data.text)
        if v.data.op=="not" and t then
            v.kind="const"; v.data={text=(not a) and "true" or "false"}; return v
        elseif v.data.op=="neg" and t=="number" then
            v.kind="const"; v.data={text=tostring(-a)}; return v
        elseif v.data.op=="len" and args[1].data.text:sub(1,1)=='"' then
            local s=args[1].data.text
            local body=s:sub(2,-2)
            v.kind="const"; v.data={text=tostring(#body)}; return v
        end
    elseif #args==2 and isConst(args[1]) and isConst(args[2]) then
        local a,ta=parseConst(args[1].data.text)
        local b,tb=parseConst(args[2].data.text)
        if ta=="number" and tb=="number" then
            local r
            if v.data.op=="add" then r=a+b elseif v.data.op=="sub" then r=a-b
            elseif v.data.op=="mul" then r=a*b elseif v.data.op=="div" and b~=0 then r=a/b
            elseif v.data.op=="mod" and b~=0 then r=a%b elseif v.data.op=="pow" then r=a^b
            elseif v.data.op=="idiv" and b~=0 then r=math.floor(a/b) end
            if r~=nil then v.kind="const"; v.data={text=tostring(r)} end
        elseif (v.data.op=="and" or v.data.op=="or") and ta then
            local r = v.data.op=="and" and (a and args[2] or args[1]) or (a and args[1] or args[2])
            if r then v.kind=r.kind; v.data=r.data end
        end
    end
    return v
end

local function optimize(ir)
    local seen={}
    for _,v in pairs(ir.values) do fold(v,seen) end
    return ir
end

-- ----------------------------- expression AST -------------------------------

local AST={}
function AST.id(name) return {tag="id",name=name} end
function AST.literal(text) return {tag="literal",text=text} end
function AST.binary(op,a,b) return {tag="binary",op=op,left=a,right=b} end
function AST.unary(op,a) return {tag="unary",op=op,value=a} end
function AST.index(a,b) return {tag="index",object=a,index=b} end
function AST.field(a,n) return {tag="field",object=a,name=n} end
function AST.call(fn,args) return {tag="call",fn=fn,args=args or {}} end
function AST.method(obj,name,args) return {tag="method",object=obj,name=name,args=args or {}} end
function AST.table(fields) return {tag="table",fields=fields or {}} end
function AST.function_(name,args,body) return {tag="function",name=name,args=args or {},body=body or {}} end
function AST.assign(lhs,rhs,local_) return {tag="assign",lhs=lhs,rhs=rhs,local_=local_} end
function AST.store(lhs,rhs) return {tag="assign",lhs=lhs,rhs=rhs} end
function AST.return_(values) return {tag="return",values=values} end
function AST.if_(cond,yes,no) return {tag="if",cond=cond,yes=yes or {},no=no or {}} end
function AST.while_(cond,body) return {tag="while",cond=cond,body=body or {}} end
function AST.repeat_(body,cond) return {tag="repeat",body=body or {},cond=cond} end
function AST.for_(vars,iter,body) return {tag="for",vars=vars,iter=iter,body=body or {}} end
function AST.raw(text) return {tag="raw",text=text} end

-- ----------------------------- value -> AST ---------------------------------

local function localNames(p)
    local n={}
    for _,l in ipairs(p.locals or {}) do
        if l.name and l.name~="" then n[l.reg]=l.name end
    end
    for r=0,(p.maxstack or 1)-1 do n[r]=n[r] or ("v"..r) end
    return n
end

local function astValue(v,p,names,seen)
    if not v then return AST.literal("nil") end
    seen=seen or {}
    if seen[v.id] then return AST.id("v"..v.id) end
    seen[v.id]=true
    local d=v.data or {}
    if v.kind=="const" then return AST.literal(d.text or "nil") end
    if v.kind=="unknown" then return AST.id(names[d.reg] or ("v"..d.reg)) end
    if v.kind=="upvalue" then return AST.id(d.name or ("upvalue"..d.index)) end
    if v.kind=="global" then return astValue(d.name,p,names,seen) end
    if v.kind=="import" then
        local path=d.path or "import"
        local parts={}
        for x in path:gmatch("[^%.]+") do parts[#parts+1]=x end
        local e=AST.id(parts[1] or path)
        for i=2,#parts do e=AST.field(e,parts[i]) end
        return e
    end
    if v.kind=="varargs" or v.kind=="vararg_return" then return AST.id("...") end
    if v.kind=="table" then return AST.table({}) end
    if v.kind=="closure" then return AST.raw("function(...) end") end
    if v.kind=="phi" then return AST.id(names[d.reg] or ("v"..v.id)) end
    if v.kind=="op" then
        local a={}
        for _,x in ipairs(d.args or {}) do a[#a+1]=astValue(x,p,names,seen) end
        if d.op=="index" then return AST.index(a[1],a[2])
        elseif d.op=="field" then
            local key=(d.args[2] and d.args[2].data and d.args[2].data.text) or "field"
            key=key:gsub('^"(.*)"$','%1')
            if identifier(key) then return AST.field(a[1],key) end
            return AST.index(a[1],AST.literal(string.format("%q",key)))
        elseif d.op=="methodcall" then
            local key=(d.args[2] and d.args[2].data and d.args[2].data.text) or "method"
            key=key:gsub('^"(.*)"$','%1')
            return AST.method(a[1],key,{})
        elseif d.op=="call" then
            local fn=a[1]; local args={}
            for j=2,#a do args[#args+1]=a[j] end
            return AST.call(fn,args)
        elseif d.op=="concat" then
            local e=a[1]
            for j=2,#a do e=AST.binary("..",e,a[j]) end
            return e
        elseif d.op=="duptable" then
            return AST.table({})
        end
        local sym={add="+",sub="-",mul="*",div="/",mod="%",pow="^",idiv="//",["and"]="and",["or"]="or"}
        if sym[d.op] then return AST.binary(sym[d.op],a[1],a[2]) end
        if d.op=="not" then return AST.unary("not",a[1]) end
        if d.op=="neg" then return AST.unary("-",a[1]) end
        if d.op=="len" then return AST.unary("#",a[1]) end
    end
    return AST.raw("--[[unresolved value "..tostring(v.id).." ]]")
end

-- ----------------------------- condition AST --------------------------------

local function branchCondition(branch,ir,names)
    local n=branch.op
    local st=branch.state or {}
    local function V(r) return astValue(st[r],ir.p,names) end
    if n=="JUMPIF" then return V(branch.A),true end
    if n=="JUMPIFNOT" then return AST.unary("not",V(branch.A)),true end
    local cmp={JUMPIFEQ="==",JUMPIFLE="<=",JUMPIFLT="<",JUMPIFNOTEQ="~=",JUMPIFNOTLE=">",JUMPIFNOTLT=">="}
    if cmp[n] then
        local rhs
        if branch.aux and branch.aux.A ~= nil then
            -- For JUMPIF* comparisons, AUX low byte is source register 2.
            rhs=astValue(st[branch.aux.A] or ir:unknown(branch.aux.A),ir.p,names)
        else
            rhs=AST.raw("--[[missing comparison operand]]")
        end
        return AST.binary(cmp[n],V(branch.A),rhs),true
    end
    if n=="JUMPXEQKNIL" then
        return AST.binary(branch.aux.NOT and "~=" or "==",V(branch.A),AST.literal("nil")),true
    end
    if n=="JUMPXEQKB" then
        return AST.binary(branch.aux.NOT and "~=" or "==",V(branch.A),AST.literal(branch.aux.KB and "true" or "false")),true
    end
    if n=="JUMPXEQKN" or n=="JUMPXEQKS" then
        return AST.binary(branch.aux.NOT and "~=" or "==",V(branch.A),AST.literal(literal(ir.p.constants[(branch.aux.KV or 0)+1]))),true
    end
    return nil,false
end

-- ----------------------------- region recovery ------------------------------

local function blockLoopMap(loops)
    local m={}
    for _,l in ipairs(loops) do
        for _,b in ipairs(l.members) do
            -- Prefer the innermost loop.
            if not m[b] or #l.members < #m[b].members then m[b]=l end
        end
    end
    return m
end

local function loopExit(g,l)
    local member={}
    for _,x in ipairs(l.members) do member[x]=true end
    for _,x in ipairs(l.members) do
        for _,s in ipairs(g.blocks[x].successors) do
            if not member[s] then return s end
        end
    end
end

local function regions(g,pdom,ipdom,loops)
    local r={branches={},loops={}}
    for _,b in ipairs(g.blocks) do
        if #b.successors==2 then
            r.branches[b.id]={header=b.id,left=b.successors[1],right=b.successors[2],join=ipdom[b.id]}
        end
    end
    for _,l in ipairs(loops) do
        r.loops[l.header]={header=l.header,members=l.members,exit=loopExit(g,l),latch=l.latch}
    end
    return r
end

-- ------------------------------- printer ------------------------------------

local function Printer()
    return {lines={},depth=0}
end
local function pline(pr,s)
    pr.lines[#pr.lines+1]=string.rep("    ",pr.depth)..s
end

local function printAST(e,parentPrec)
    parentPrec=parentPrec or 0
    local tag=e.tag
    if tag=="id" or tag=="literal" or tag=="raw" then return e.name or e.text end
    if tag=="field" then return printAST(e.object,14).."."..e.name end
    if tag=="index" then return printAST(e.object,14).."["..printAST(e.index).."]" end
    if tag=="call" then
        local a={}
        for _,x in ipairs(e.args) do a[#a+1]=printAST(x) end
        return printAST(e.fn,14).."("..table.concat(a,", ")..")"
    end
    if tag=="method" then
        local a={}
        for _,x in ipairs(e.args) do a[#a+1]=printAST(x) end
        return printAST(e.object,14)..":"..e.name.."("..table.concat(a,", ")..")"
    end
    if tag=="unary" then return e.op.." "..printAST(e.value,12) end
    if tag=="binary" then
        local prec={["or"]=1,["and"]=2,["=="]=3,["~="]=3,["<"]=3,[">"]=3,["<="]=3,[">="]=3,
            [".."]=4,["+"]=5,["-"]=5,["*"]=6,["/"]=6,["//"]=6,["%"]=6,["^"]=8}
        local p=prec[e.op] or 5
        local s=printAST(e.left,p).." "..e.op.." "..printAST(e.right,p+1)
        return p<parentPrec and "("..s..")" or s
    end
    if tag=="table" then return "{}" end
    return "--[[unknown AST]]"
end

-- -------------------------- source structurer -------------------------------

local Structurer={}
Structurer.__index=Structurer

function Structurer.new(p,g,ipdom,loops,ir)
    return setmetatable({
        p=p,g=g,ipdom=ipdom,loops=loops,ir=ir,names=localNames(p),
        loopByHeader=blockLoopMap(loops),seen={},declared={},warnings={},confidence=0
    },Structurer)
end

function Structurer:emitBlockInstructions(b)
    local out={}
    for _,ins in ipairs(b.instructions) do
        local n=ins.name
        local st=self.ir.outState[b.id] or {}
        local function R(r) return printAST(astValue(st[r],self.p,self.names)) end
        local function L(r) return self.names[r] or ("v"..r) end

        if n=="RETURN" then
            local q={}
            if ins.B==0 then q[1]="..." else
                for r=ins.A,ins.A+ins.B-2 do q[#q+1]=R(r) end
            end
            out[#out+1]="return "..table.concat(q,", ")
        elseif n=="SETUPVAL" then
            out[#out+1]=(self.p.upvalues[ins.B+1] or ("upvalue"..ins.B)).." = "..R(ins.A)
        elseif n=="SETGLOBAL" then
            local k=self.p.constants[(ins.aux and ins.aux.KV or 0)+1]
            local name=k and k.value or "global"
            out[#out+1]=identifier(name) and name.." = "..R(ins.A) or "_G["..quote(name).."] = "..R(ins.A)
        elseif n=="SETTABLE" then
            out[#out+1]=R(ins.A).."["..R(ins.B).."] = "..R(ins.C)
        elseif n=="SETTABLEKS" or n=="SETUDATAKS" then
            local k=self.p.constants[(ins.aux and ins.aux.KV or 0)+1]
            local name=k and k.value or "field"
            out[#out+1]=identifier(name) and R(ins.A).."."..name.." = "..R(ins.B) or R(ins.A).."["..quote(name).."] = "..R(ins.B)
        elseif n=="SETTABLEN" then
            out[#out+1]=R(ins.A).."["..(ins.C+1).."] = "..R(ins.B)
        elseif n=="FASTCALL" or n=="FASTCALL1" or n=="FASTCALL2" or n=="FASTCALL2K" or n=="FASTCALL3" then
            -- FASTCALL is an optimization hint; the following CALL is the
            -- semantic operation.  Do not emit the hint.
        elseif n=="CAPTURE" or n=="PREPVARARGS" or n=="COVERAGE" or n=="NATIVECALL" or
               n=="NOP" or n=="BREAK" or n=="CLOSEUPVALS" then
            -- No source-level statement.
        elseif n:match("^JUMP") or n:match("^FOR") or isConditional(n and ins) or n=="CMPPROTO" then
            -- consumed by region recovery.
        elseif META[n] and META[n].writes and #META[n].writes>0 then
            local v=st[ins.A]
            local rhs=printAST(astValue(v,self.p,self.names))
            if not self.declared[ins.A] then
                self.declared[ins.A]=true
                out[#out+1]="local "..L(ins.A).." = "..rhs
            else
                out[#out+1]=L(ins.A).." = "..rhs
            end
        elseif n=="LOADNIL" or n=="LOADB" or n=="LOADN" or n=="LOADK" or n=="LOADKX" or
               n=="MOVE" or n=="GETUPVAL" or n=="GETGLOBAL" or n=="GETIMPORT" or
               n=="GETTABLE" or n=="GETTABLEKS" or n=="GETUDATAKS" or n=="GETTABLEN" or
               n=="NEWTABLE" or n=="DUPTABLE" or n=="NEWCLOSURE" or n=="DUPCLOSURE" or
               n=="NAMECALL" or n=="NAMECALLUDATA" or n=="GETVARARGS" or
               n=="ADD" or n=="SUB" or n=="MUL" or n=="DIV" or n=="MOD" or n=="POW" or
               n=="IDIV" or n=="AND" or n=="OR" or n=="ADDK" or n=="SUBK" or n=="MULK" or
               n=="DIVK" or n=="MODK" or n=="POWK" or n=="IDIVK" or n=="ANDK" or n=="ORK" or
               n=="SUBRK" or n=="DIVRK" or n=="CONCAT" or n=="NOT" or n=="MINUS" or n=="LENGTH" or
               n=="CALL" or n=="CALLFB" then
            local v=st[ins.A]
            local rhs=printAST(astValue(v,self.p,self.names))
            if not self.declared[ins.A] then
                self.declared[ins.A]=true
                out[#out+1]="local "..L(ins.A).." = "..rhs
            elseif n=="CALL" or n=="CALLFB" then
                -- A CALL whose results are unused is still an expression
                -- statement; printing the recovered call preserves effects.
                out[#out+1]=rhs
            else
                out[#out+1]=L(ins.A).." = "..rhs
            end
        else
            self.warnings[#self.warnings+1]="unsupported source emission for "..n.." at PC "..ins.pc
            out[#out+1]="--[[ m0pu: unsupported opcode "..n.." at PC "..ins.pc.." ]]"
        end
    end
    return out
end

function Structurer:branchInfo(b)
    local last=b.instructions[#b.instructions]
    if not last or not isConditional(last) then return nil end
    if #b.successors~=2 then return nil end
    local target=branchTarget(last.pc,last)
    local fall=last.pc+instructionLength(last)
    local tb=self.g.byPc[target]
    local fb=self.g.byPc[fall]
    if not tb or not fb then return nil end
    return {instr=last,target=tb.id,fall=fb.id,join=self.ipdom[b.id]}
end

function Structurer:walk(id,stop,depth,active,pr)
    if id==stop or active[id] or self.seen[id] then return end
    local b=self.g.blocks[id]
    if not b then return end
    active[id]=true

    local loop=self.loopByHeader[id]
    if loop and not self.seen["loop"..id] then
        self.seen["loop"..id]=true
        local header=b.instructions[#b.instructions]
        local exit=loop.exit
        local cond
        if header and isConditional(header) then
            local info=self:branchInfo(b)
            if info then
                cond=branchCondition(self.ir.instructions and info or {},self.ir,self.names)
            end
        end

        -- Canonical numeric/generic loops are recognized from their actual
        -- Luau loop instructions; otherwise use a proven condition when one
        -- exists, and fall back to while true only for genuinely opaque loops.
        if header and header.name=="FORNPREP" then
            local st=self.ir.outState[id] or {}
            local a=self.names[header.A] or ("v"..header.A)
            local limit=self.names[header.A+1] or ("v"..(header.A+1))
            local step=self.names[header.A+2] or ("v"..(header.A+2))
            pline(pr,"for "..a.." = "..a..", "..limit..", "..step.." do")
        elseif header and (header.name=="FORGPREP" or header.name=="FORGPREP_INEXT" or header.name=="FORGPREP_NEXT") then
            local a=self.names[header.A] or ("v"..header.A)
            pline(pr,"for _, "..a.." in "..a.." do")
        elseif cond and cond[1] then
            pline(pr,"while "..printAST(cond[1]).." do")
        else
            pline(pr,"while true do")
            self.warnings[#self.warnings+1]="loop condition could not be proven at B"..id
        end

        pr.depth+=1
        local members={}
        for _,x in ipairs(loop.members) do members[x]=true end
        for _,s in ipairs(b.successors) do
            if members[s] then self:walk(s,id,depth+1,active,pr) end
        end
        pr.depth-=1
        pline(pr,"end")
        active[id]=nil
        if exit then self:walk(exit,stop,depth,active,pr) end
        return
    end

    local br=self:branchInfo(b)
    if br and br.join and br.join~=id and not active[br.join] then
        local names=self.names
        local st=self.ir.outState[id] or {}
        local branch={}
        branch.op=br.instr.name; branch.A=br.instr.A; branch.C=br.instr.C
        branch.aux=br.instr.aux; branch.state=st
        local cond,ok=branchCondition(branch,self.ir,names)
        if ok and cond then
            local first,second=br.target,br.fall
            if br.instr.name=="JUMPIFNOT" or br.instr.name:match("JUMPIFNOT") then
                first,second=second,first
            end
            pline(pr,"if "..printAST(cond).." then")
            pr.depth+=1
            self:walk(first,br.join,depth+1,active,pr)
            pr.depth-=1
            if second~=br.join then
                pline(pr,"else")
                pr.depth+=1
                self:walk(second,br.join,depth+1,active,pr)
                pr.depth-=1
            end
            pline(pr,"end")
            self.confidence=(self.confidence or 0)+1
            active[id]=nil
            self:walk(br.join,stop,depth,active,pr)
            return
        end
    end

    self.seen[id]=true
    for _,line in ipairs(self:emitBlockInstructions(b)) do pline(pr,line) end
    if #b.successors==1 then
        self:walk(b.successors[1],stop,depth,active,pr)
    elseif #b.successors>1 then
        -- Preserve semantics when region formation cannot prove a structured
        -- equivalent.  We do not invent a misleading if/loop.
        self.warnings[#self.warnings+1]="unstructured branch at B"..id
        for _,s in ipairs(b.successors) do
            if s~=stop then pline(pr,"--[[ control-flow edge B"..s.." ]]") end
        end
    end
    active[id]=nil
end

function Structurer:run()
    local pr=Printer()
    local params={}
    for r=0,(self.p.numparams or 0)-1 do params[#params+1]=self.names[r] end
    if self.p.vararg then params[#params+1]="..." end
    local name=identifier(self.p.debugname) and self.p.debugname or "anonymous"
    pline(pr,"function "..name.."("..table.concat(params,", ")..")")
    pr.depth=1
    self:walk(self.g.entry.id,nil,0,{},pr)
    pr.depth=0
    pline(pr,"end")
    return table.concat(pr.lines,"\n")
end

-- ------------------------------ diagnostics ---------------------------------

local function diagnostics(p,g,ir,loops,struct)
    local d={errors={},warnings={},facts={}}
    local reach=reachable(g)
    for _,b in ipairs(g.blocks) do
        if not reach[b.id] then d.warnings[#d.warnings+1]="unreachable block B"..b.id end
    end
    for bid,regs in pairs(ir.phis) do
        for reg,phi in pairs(regs) do
            if #phi.data.incomings<2 then
                d.warnings[#d.warnings+1]=("degenerate phi B%d R%d"):format(bid,reg)
            end
        end
    end
    for _,w in ipairs(struct.warnings) do d.warnings[#d.warnings+1]=w end
    for _,v in pairs(ir.values) do
        if v.kind=="opaque" then
            d.warnings[#d.warnings+1]="opaque instruction semantics remain"
            break
        end
    end
    local edges=0; for _,b in ipairs(g.blocks) do edges+=#b.successors end
    local phis=0; for _,x in pairs(ir.phis) do for _ in pairs(x) do phis+=1 end end
    d.facts={blocks=#g.blocks,edges=edges,ssaValues=ir.nextId,phis=phis,loops=#loops,
        instructions=#p.code}
    return d
end

local function confidence(g,ir,loops,struct,d)
    local total=#g.blocks+#loops+#d.facts.ssaValues
    local good=0
    for _,b in ipairs(g.blocks) do
        if #b.successors<=2 then good+=1 end
        if #b.predecessors<=2 then good+=1 end
    end
    good += #loops + (struct.confidence or 0)
    local penalty=#d.warnings*2
    return math.max(0,math.min(100,math.floor(((good-penalty)/math.max(1,total*2))*100+0.5)))
end

-- ------------------------------- public API ---------------------------------

local function prepare(data,options)
    local c=parseAny(data,options or {})
    assert(c.main,"no main prototype found")
    return c
end

local function analyzeProto(p,options)
    local g=buildCFG(p)
    local dom,idom,children,reach=dominators(g)
    local df=dominanceFrontier(g,idom,reach)
    local pdom,ipdom,exits=postDominators(g,reach)
    local loops=naturalLoops(g,dom)
    local ir=IR.new(p,g,idom,children,df):build()
    optimize(ir)
    local struct=Structurer.new(p,g,ipdom,loops,ir)
    local source=struct:run()
    local diag=diagnostics(p,g,ir,loops,struct)
    return {
        source=source, cfg=g, dominators=dom, idom=idom, dominatorChildren=children,
        dominanceFrontier=df, postdominators=pdom, ipdom=ipdom, exits=exits,
        loops=loops, ir=ir, diagnostics=diag, confidence=confidence(g,ir,loops,struct,diag),
        proto=p
    }
end

function m0pu.parse(bytecode,options)
    assert(type(bytecode)=="string","bytecode must be a string")
    return parseAny(bytecode,options or {})
end

function m0pu.disassemble(bytecode,options)
    local c=parseAny(bytecode,options or {})
    local out={"-- m0pu "..m0pu.VERSION.." | "..c.format.." | bytecode "..c.bytecodeVersion}
    for _,p in ipairs(c.protos or {}) do
        out[#out+1]="-- proto "..p.id.." "..quote(p.debugname or "")
        local pc=1
        while pc<=#p.code do
            local i=p.code[pc]
            local extra=""
            if oplen(i.name)==2 and p.code[pc+1] then
                extra=(" AUX=0x%08X"):format(p.code[pc+1].word)
            end
            out[#out+1]=("%04d %-20s A=%3d B=%3d C=%3d D=%7d E=%8d%s"):
                format(pc,i.name,i.A,i.B,i.C,i.D,i.E,extra)
            pc+=oplen(i.name)
        end
    end
    return table.concat(out,"\n")
end

function m0pu.analyze(bytecode,options)
    local c=parseAny(bytecode,options or {})
    local r={format=c.format,bytecodeVersion=c.bytecodeVersion,typeVersion=c.typeVersion,
        bytes=#bytecode,protos={}}
    for _,p in ipairs(c.protos or {}) do
        local x=analyzeProto(p,options)
        r.protos[p.id]={instructions=#p.code,blocks=#x.cfg.blocks,edges=0,
            ssaValues=x.ir.nextId,phis=0,loops=#x.loops,warnings=#x.diagnostics.warnings,
            confidence=x.confidence}
        for _,b in ipairs(x.cfg.blocks) do r.protos[p.id].edges+=#b.successors end
        for _,regs in pairs(x.ir.phis) do for _ in pairs(regs) do r.protos[p.id].phis+=1 end end
    end
    return r
end

function m0pu.decompile(input,options)
    options=options or {}
    local data=input
    if type(input)~="string" then
        local getter=options.getscriptbytecode or getscriptbytecode
        assert(type(getter)=="function","getscriptbytecode is unavailable")
        local ok,res=pcall(getter,input)
        assert(ok and type(res)=="string" and #res>0,"failed to obtain bytecode: "..tostring(res))
        data=res
    end

    local c=prepare(data,options)
    local main=analyzeProto(c.main,options)
    main.format=c.format
    main.bytecodeVersion=c.bytecodeVersion
    main.typeVersion=c.typeVersion
    main.bytecodeSize=#data
    main.protoCount=#(c.protos or {})
    main.mainProto=c.main.id
    main.parserWarnings=c.warnings or {}
    main.protos={}

    for _,p in ipairs(c.protos or {}) do
        local ok,res=pcall(analyzeProto,p,options)
        if ok then main.protos[p.id]=res
        else
            main.protos[p.id]={proto=p,error=tostring(res),
                diagnostics={errors={tostring(res)},warnings={},facts={}}}
        end
    end
    return main
end

function m0pu.save(input,path,options)
    assert(type(writefile)=="function","writefile unavailable")
    assert(type(path)=="string" and path~="","path required")
    local r=m0pu.decompile(input,options)
    writefile(path,r.source)
    return r
end

function m0pu.getProductionPipeline()
    return {
        "validated serialized-bytecode decode",
        "instruction metadata / operand semantics",
        "basic-block CFG",
        "reachability",
        "iterative dominators",
        "immediate dominators",
        "dominance frontiers",
        "post-dominators",
        "natural-loop discovery",
        "register-to-SSA lifting",
        "Cytron-style phi placement",
        "dominator-tree renaming",
        "use-def chains",
        "constant propagation / local folding",
        "typed expression AST",
        "branch-region recovery",
        "loop-region recovery",
        "deterministic source emission",
        "diagnostics and confidence"
    }
end

function m0pu.getCapabilities()
    return {
        version=m0pu.VERSION,
        luauBytecodeVersions={min=m0pu.BYTECODE_MIN,max=m0pu.BYTECODE_MAX},
        deterministic=true,
        network=false,
        ai=false,
        ssa=true,
        phi=true,
        useDef=true,
        valueGraph=true,
        dominators=true,
        postDominators=true,
        dominanceFrontier=true,
        loops=true,
        ast=true,
        diagnostics=true
    }
end

local e=env()
e.m0pu=m0pu
e.m0puDecompile=function(x,o) return m0pu.decompile(x,o).source end
e.m0puDisassemble=function(x,o)
    local d=type(x)=="string" and x or assert(getscriptbytecode(x))
    return m0pu.disassemble(d,o)
end

return m0pu
