-- m0pu Decompiler v2.0
-- Real Luau bytecode parser + CFG + conservative source recovery.
-- Based on public Luau VM bytecode definitions/serialization semantics.
-- Original implementation; not copied from Oracle, Lua.Expert, Konstant, or Medal.

local m0pu = {}
m0pu.VERSION = "2.0"
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
        local p={id=id,constants={},children={},locals={},upvalues={}}
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

-- Control-flow graph.
local function target(pc,i)
    local n=i.name
    if n=="JUMP" or n=="JUMPBACK" or n=="JUMPIF" or n=="JUMPIFNOT"
      or n=="JUMPIFEQ" or n=="JUMPIFLE" or n=="JUMPIFLT" or n=="JUMPIFNOTEQ"
      or n=="JUMPIFNOTLE" or n=="JUMPIFNOTLT" or n=="FORNPREP" or n=="FORNLOOP"
      or n=="FORGLOOP" or n=="FORGPREP" or n=="FORGPREP_INEXT" or n=="FORGPREP_NEXT"
      or n=="JUMPXEQKNIL" or n=="JUMPXEQKB" or n=="JUMPXEQKN" or n=="JUMPXEQKS" or n=="CMPPROTO" then
        return pc+1+i.D
    elseif n=="JUMPX" then return pc+1+i.E end
end
local function cfg(p)
    local leaders={[1]=true}; local pc=1
    while pc<=#p.code do
        local i=p.code[pc]; local t=target(pc,i)
        if t and t>=1 and t<=#p.code then leaders[t]=true end
        local n=i.name
        if t and pc+oplen(n)<=#p.code then leaders[pc+oplen(n)]=true end
        if n=="RETURN" or n=="JUMP" or n=="JUMPX" or n=="JUMPBACK" then if pc+oplen(n)<=#p.code then leaders[pc+oplen(n)]=true end end
        pc+=oplen(n)
    end
    local starts={}; for s in pairs(leaders) do starts[#starts+1]=s end; table.sort(starts)
    local blocks,byPc={},{}
    for i,s in ipairs(starts) do local e=(starts[i+1] or #p.code+1)-1; local b={id=i,start=s,finish=e,successors={},predecessors={}}; blocks[i]=b; for x=s,e do byPc[x]=b end end
    for _,b in ipairs(blocks) do
        local pc=b.finish; local i=p.code[pc]; local t=target(pc,i)
        local function add(x) local z=byPc[x]; if z then b.successors[#b.successors+1]=z.id; z.predecessors[#z.predecessors+1]=b.id end end
        if t then add(t) end
        local n=i.name; local cond=n=="JUMPIF" or n=="JUMPIFNOT" or n:match("^JUMPIF") or n:match("^JUMPXEQ")
        if cond then add(pc+oplen(n)) end
        if not t and n~="RETURN" and n~="JUMP" and n~="JUMPX" and n~="JUMPBACK" then add(pc+oplen(n)) end
    end
    return blocks,byPc
end

-- Conservative source recovery. It intentionally prefers valid control flow over fake
-- high-level constructs when loop/if structure cannot be proven.
local Analyzer={}; Analyzer.__index=Analyzer
function Analyzer.new(p,opt)
    local s=setmetatable({p=p,opt=opt or {},expr={},names={},labels={}},Analyzer)
    s.blocks,s.byPc=cfg(p)
    for _,v in ipairs(p.locals or {}) do s.names[v.reg]=v.name end
    for r=0,(p.maxstack or 1)-1 do s.names[r]=s.names[r] or ("v"..r) end
    for pc,i in ipairs(p.code) do local t=target(pc,i); if t then s.labels[t]=true end end
    return s
end
function Analyzer:n(r) return self.names[r] or ("v"..r) end
function Analyzer:r(r) return self.expr[r] or self:n(r) end
function Analyzer:set(r,x) self.expr[r]=x end
function Analyzer:K(i) return literal(self.p.constants[(i or 0)+1]) end
function Analyzer:KS(i) local k=self.p.constants[(i or 0)+1]; return k and k.value or ("k"..tostring(i)) end
function Analyzer:cond(i)
    local n=i.name; local a=self:r(i.A); local c=self:r(i.C)
    local cmp={JUMPIFEQ="==",JUMPIFLE="<=",JUMPIFLT="<",JUMPIFNOTEQ="~=",JUMPIFNOTLE=">",JUMPIFNOTLT=">="}
    if n=="JUMPIF" then return a end
    if n=="JUMPIFNOT" then return "not ("..a..")" end
    if cmp[n] then return "("..a.." "..cmp[n].." "..c..")" end
    if n=="JUMPXEQKNIL" then return "("..a.." "..(i.aux.NOT and "~=" or "==").." nil)" end
    if n=="JUMPXEQKB" then return "("..a.." "..(i.aux.NOT and "~=" or "==").." "..(i.aux.KB and "true" or "false")..")" end
    if n=="JUMPXEQKN" or n=="JUMPXEQKS" then return "("..a.." "..(i.aux.NOT and "~=" or "==").." "..self:K(i.aux.KV)..")" end
    return "true"
end

function Analyzer:emit(pc,i)
    local n,A,B,C,D=i.name,i.A,i.B,i.C,i.D
    if oplen(n)==2 and self.p.code[pc+1] then i.aux=aux(self.p.code[pc+1].word) end
    local r=self.r; local nm=self.n
    if n=="NOP" or n=="BREAK" then return "-- "..n end
    if n=="LOADNIL" then self:set(A,"nil"); return nm(A).." = nil" end
    if n=="LOADB" then self:set(A,B~=0 and "true" or "false"); return nm(A).." = "..self:r(A) end
    if n=="LOADN" then self:set(A,tostring(D)); return nm(A).." = "..self:r(A) end
    if n=="LOADK" then self:set(A,self:K(D)); return nm(A).." = "..self:r(A) end
    if n=="LOADKX" then self:set(A,self:K(i.aux.KV)); return nm(A).." = "..self:r(A) end
    if n=="MOVE" then self:set(A,r(B)); return nm(A).." = "..self:r(A) end
    if n=="GETUPVAL" then local x=self.p.upvalues[B+1] or ("upvalue"..B); self:set(A,x); return nm(A).." = "..x end
    if n=="SETUPVAL" then return (self.p.upvalues[B+1] or ("upvalue"..B)).." = "..r(A) end
    if n=="GETGLOBAL" then local k=self:KS(i.aux.KV); local x=identifier(k) and k or ("_G["..quote(k).."]"); self:set(A,x); return nm(A).." = "..x end
    if n=="SETGLOBAL" then local k=self:KS(i.aux.KV); return (identifier(k) and k or ("_G["..quote(k).."]")).." = "..r(A) end
    if n=="GETIMPORT" then local k=self.p.constants[(i.aux.KV or D)+1]; local x=k and k.path or ("import_"..D); self:set(A,x); return nm(A).." = "..x end
    if n=="GETTABLE" then self:set(A,r(B).."["..r(C).."]"); return nm(A).." = "..self:r(A) end
    if n=="SETTABLE" then return r(A).."["..r(B).."] = "..r(C) end
    if n=="GETTABLEKS" or n=="GETUDATAKS" then local k=self:KS(i.aux.KV); local x=identifier(k) and r(B).."."..k or r(B).."["..quote(k).."]"; self:set(A,x); return nm(A).." = "..x end
    if n=="SETTABLEKS" or n=="SETUDATAKS" then local k=self:KS(i.aux.KV); return identifier(k) and (r(A).."."..k.." = "..r(B)) or (r(A).."["..quote(k).."] = "..r(B)) end
    if n=="GETTABLEN" then self:set(A,r(B).."["..(C+1).."]"); return nm(A).." = "..self:r(A) end
    if n=="SETTABLEN" then return r(A).."["..(C+1).."] = "..r(B) end
    if n=="NEWTABLE" then self:set(A,"{}"); return nm(A).." = {}" end
    if n=="DUPTABLE" then self:set(A,self:K(D)); return nm(A).." = "..self:r(A) end
    local ops={ADD="+",SUB="-",MUL="*",DIV="/",MOD="%",POW="^",IDIV="//",AND="and",OR="or"}
    if ops[n] then local x=r(B).." "..ops[n].." "..r(C); self:set(A,x); return nm(A).." = "..x end
    local kop={ADDK="+",SUBK="-",MULK="*",DIVK="/",MODK="%",POWK="^",IDIVK="//",ANDK="and",ORK="or"}
    if kop[n] then local x=r(B).." "..kop[n].." "..self:K(C); self:set(A,x); return nm(A).." = "..x end
    if n=="SUBRK" or n=="DIVRK" then local x=self:K(B).." "..(n=="SUBRK" and "-" or "/").." "..r(C); self:set(A,x); return nm(A).." = "..x end
    if n=="CONCAT" then local q={}; for x=B,C do q[#q+1]=r(x) end; local z=table.concat(q," .. "); self:set(A,z); return nm(A).." = "..z end
    if n=="NOT" or n=="MINUS" or n=="LENGTH" then local z=(n=="NOT" and "not " or n=="MINUS" and "-" or "#")..r(B); self:set(A,z); return nm(A).." = "..z end
    if n=="CALL" or n=="CALLFB" then
        local q={}; local count=B==0 and 0 or B-1; for x=A+1,A+count do q[#q+1]=r(x) end
        local call=r(A).."("..table.concat(q,", ")..")"
        if C==1 then return call end
        local out={}; if C==0 then return nm(A).." = "..call end
        for x=A,A+C-2 do out[#out+1]=nm(x) end
        return table.concat(out,", ").." = "..call
    end
    if n=="NAMECALL" or n=="NAMECALLUDATA" then
        local k=self:KS(i.aux.KV); local q={}; for x=A+2,A+(B-1) do q[#q+1]=r(x) end
        local call=r(B)..":"..(identifier(k) and k or ("__namecall_"..tostring(k))).."("..table.concat(q,", ")..")"
        self:set(A,call); return nm(A).." = "..call
    end
    if n=="RETURN" then if B==0 then return "return ..." end local q={}; for x=A,A+B-2 do q[#q+1]=r(x) end; return "return "..table.concat(q,", ") end
    if n=="GETVARARGS" then return nm(A).." = ..." end
    if n=="PREPVARARGS" then return "-- prepare varargs" end
    if n=="NEWCLOSURE" or n=="DUPCLOSURE" then self:set(A,"function(...) end"); return nm(A).." = "..self:r(A) end
    if n=="CAPTURE" then return "-- capture" end
    if n=="FORNPREP" or n=="FORNLOOP" or n=="FORGLOOP" or n=="FORGPREP" or n=="FORGPREP_INEXT" or n=="FORGPREP_NEXT" then return "-- "..n end
    if n:match("^FASTCALL") then return "-- "..n.." builtin "..A end
    if n=="COVERAGE" or n=="NATIVECALL" then return "-- "..n end
    if n=="JUMP" or n=="JUMPX" or n=="JUMPBACK" then return "goto L"..target(pc,i) end
    if n:match("^JUMPIF") or n:match("^JUMPXEQ") then return "if "..self:cond(i).." then goto L"..target(pc,i).." end" end
    if n=="CMPPROTO" then return "-- compare proto "..tostring(i.aux.KV) end
    if n=="NEWCLASSMEMBER" then return "-- class member" end
    return "-- "..n.." A="..A.." B="..B.." C="..C.." D="..D
end

function Analyzer:run()
    local p=self.p; local out={}; local ind=0
    local function put(s) out[#out+1]=string.rep("    ",ind)..s end
    local params={}; for i=0,(p.numparams or 0)-1 do params[#params+1]=self:n(i) end; if p.vararg then params[#params+1]="..." end
    local name=identifier(p.debugname) and p.debugname or "anonymous"
    put("function "..name.."("..table.concat(params,", ")..")"); ind=1
    local declared={}
    for i=0,(p.numparams or 0)-1 do declared[i]=true end
    local pc=1
    while pc<=#p.code do
        if self.labels[pc] then put("::L"..pc.."::") end
        local i=p.code[pc]; local s=self:emit(pc,i)
        local localHere=false
        for _,v in ipairs(p.locals or {}) do if v.reg==i.A and v.startpc==pc then localHere=true; break end end
        if localHere and not declared[i.A] and s and not s:match("^%-%-") then s="local "..s; declared[i.A]=true end
        if s then put(s) end
        pc+=oplen(i.name)
    end
    ind=0; put("end")
    return table.concat(out,"\n")
end

-- Human-readable disassembly and CFG report.
local function dis(p)
    local out={"-- proto "..tostring(p.id).." "..quote(p.debugname or "")}
    out[#out+1]="-- stack="..tostring(p.maxstack).." params="..tostring(p.numparams).." upvalues="..tostring(p.nups)
    out[#out+1]="constants:"
    for i,k in ipairs(p.constants or {}) do out[#out+1]=("  K%d %-16s %s"):format(i-1,k.type,literal(k)) end
    out[#out+1]="instructions:"
    local pc=1
    while pc<=#p.code do
        local i=p.code[pc]; local a=""
        if oplen(i.name)==2 and p.code[pc+1] then a=(" AUX=0x%08X"):format(p.code[pc+1].word) end
        out[#out+1]=("%04d %-18s A=%3d B=%3d C=%3d D=%6d E=%8d%s"):format(pc,i.name,i.A,i.B,i.C,i.D,i.E,a)
        pc+=oplen(i.name)
    end
    return table.concat(out,"\n")
end
local function metrics(p)
    local b=cfg(p); local e=0; for _,x in ipairs(b) do e+=#x.successors end
    return {blocks=#b,edges=e,instructions=#p.code,constants=#p.constants,locals=#(p.locals or {}),upvalues=#(p.upvalues or {}),children=#(p.children or {})}
end

function m0pu.parse(bytecode,options) return parseAny(bytecode,options) end
function m0pu.disassemble(bytecode,options)
    local c=parseAny(bytecode,options); local out={"-- m0pu "..m0pu.VERSION.." | "..c.format.." | version "..c.bytecodeVersion}
    for _,p in ipairs(c.protos or {}) do out[#out+1]=dis(p) end
    return table.concat(out,"\n\n")
end
function m0pu.analyze(bytecode,options)
    local c=parseAny(bytecode,options); local r={format=c.format,bytecodeVersion=c.bytecodeVersion,typeVersion=c.typeVersion,bytes=#bytecode,protos={}}
    for i,p in ipairs(c.protos or {}) do r.protos[i]=metrics(p) end
    return r
end
function m0pu.decompile(input,options)
    options=options or {}; local data=input
    if type(input)~="string" then
        local getter=options.getscriptbytecode or getscriptbytecode
        assert(type(getter)=="function","getscriptbytecode is unavailable")
        local ok,res=pcall(getter,input); assert(ok and type(res)=="string" and #res>0,"failed to obtain bytecode: "..tostring(res)); data=res
    end
    local c=parseAny(data,options); assert(c.main,"no main prototype found")
    local a=Analyzer.new(c.main,options); local source=a:run()
    return {source=source,format=c.format,bytecodeVersion=c.bytecodeVersion,typeVersion=c.typeVersion,
        bytecodeSize=#data,protoCount=#(c.protos or {}),mainProto=c.main.id,warnings=c.warnings or {},
        analysis=metrics(c.main),chunk=options.returnChunk and c or nil}
end
function m0pu.save(input,path,options)
    local r=m0pu.decompile(input,options); assert(type(writefile)=="function","writefile unavailable"); assert(path,"path required"); writefile(path,r.source); return r
end
function m0pu.getCapabilities()
    local e=env()
    return {getscriptbytecode=type(getscriptbytecode)=="function",writefile=type(writefile)=="function",
        readfile=type(readfile)=="function",string_unpack=type(string.unpack)=="function",environment=type(e)=="table"}
end

local e=env(); e.m0pu=m0pu
e.m0puDecompile=function(x,o) return m0pu.decompile(x,o).source end
e.m0puDisassemble=function(x,o)
    local d=type(x)=="string" and x or assert(getscriptbytecode(x))
    return m0pu.disassemble(d,o)
end
return m0pu
