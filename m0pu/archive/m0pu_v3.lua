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

-- ============================================================================
-- m0pu v3 Advanced Recovery Engine
-- SSA + value graph + dominators/post-dominators + control dependence +
-- structured-control-flow recovery + readability cleanup.
--
-- This layer is deliberately independent from the bytecode parser above. It
-- consumes the decoded Luau IR and builds analysis facts before emitting source.
-- No proprietary Oracle/Medal/Lua.Expert implementation is copied here.
-- ============================================================================

m0pu.VERSION = "3.0-SSA"
m0pu.features = {
    "ssa", "phi", "value_graph", "dominators", "postdominators",
    "control_dependence", "loop_recovery", "if_recovery", "short_circuit",
    "expression_folding", "dead_value_cleanup", "debug_local_recovery",
    "confidence_scoring", "optional_ai_review_hook"
}

local function setadd(t,k) if not t[k] then t[k]=true; return true end end
local function sortedKeys(t)
    local a={}; for k in pairs(t) do a[#a+1]=k end; table.sort(a); return a
end
local function contains(a,x) for _,v in ipairs(a) do if v==x then return true end end return false end
local function uniq(a)
    local s,r={},{}
    for _,v in ipairs(a or {}) do if not s[v] then s[v]=true; r[#r+1]=v end end
    return r
end

-- --------------------------- CFG normalization -----------------------------
local function advCFG(p)
    local blocks,byPc=cfg(p)
    local map={}
    for _,b in ipairs(blocks) do
        map[b.id]=b
        b.instructions={}
        local pc=b.start
        while pc<=b.finish do
            b.instructions[#b.instructions+1]=p.code[pc]
            b.instructions[#b.instructions].pc=pc
            pc+=oplen(p.code[pc].name)
        end
    end
    local entry=blocks[1]
    return {blocks=blocks,byPc=byPc,map=map,entry=entry}
end

-- --------------------------- Dominator engine -------------------------------
local function computeDominators(g)
    local n=#g.blocks
    local dom={}
    for i=1,n do
        dom[i]={}
        if i==g.entry.id then dom[i][i]=true else for j=1,n do dom[i][j]=true end end
    end
    local changed=true
    while changed do
        changed=false
        for i=1,n do
            if i~=g.entry.id then
                local b=g.blocks[i]
                local nd={}
                if #b.predecessors==0 then nd[i]=true
                else
                    for _,p in ipairs(b.predecessors) do
                        if next(nd)==nil then for d in pairs(dom[p]) do nd[d]=true end
                        else for d in pairs(nd) do if not dom[p][d] then nd[d]=nil end end end
                    end
                    nd[i]=true
                end
                for d in pairs(dom[i]) do if not nd[d] then dom[i][d]=nil; changed=true end end
                for d in pairs(nd) do if not dom[i][d] then dom[i][d]=true; changed=true end end
            end
        end
    end
    local idom={}
    idom[g.entry.id]=nil
    for i=1,n do
        if i~=g.entry.id then
            local candidates={}
            for d in pairs(dom[i]) do if d~=i then candidates[#candidates+1]=d end end
            local best=nil
            for _,d in ipairs(candidates) do
                local immediate=true
                for _,o in ipairs(candidates) do
                    if o~=d and dom[o][d] then immediate=false; break end
                end
                if immediate then best=d; break end
            end
            idom[i]=best
        end
    end
    local children={}; for i=1,n do children[i]={} end
    for i=1,n do if idom[i] then children[idom[i]][#children[idom[i]]+1]=i end end
    for i=1,n do table.sort(children[i]) end
    return dom,idom,children
end

local function computePostDominators(g)
    local n=#g.blocks
    local exits={}
    for i,b in ipairs(g.blocks) do
        if #b.successors==0 then exits[#exits+1]=i end
    end
    if #exits==0 then exits[#exits+1]=n end
    local pdom={}
    for i=1,n do
        pdom[i]={}
        if contains(exits,i) then pdom[i][i]=true else for j=1,n do pdom[i][j]=true end end
    end
    local changed=true
    while changed do
        changed=false
        for i=n,1,-1 do
            if not contains(exits,i) then
                local b=g.blocks[i]; local nd=nil
                for _,s in ipairs(b.successors) do
                    if not nd then nd={}; for x in pairs(pdom[s]) do nd[x]=true end
                    else for x in pairs(nd) do if not pdom[s][x] then nd[x]=nil end end end
                end
                nd=nd or {}; nd[i]=true
                for x in pairs(pdom[i]) do if not nd[x] then pdom[i][x]=nil; changed=true end end
                for x in pairs(nd) do if not pdom[i][x] then pdom[i][x]=true; changed=true end end
            end
        end
    end
    local ipdom={}
    for i=1,n do
        if not contains(exits,i) then
            local candidates={}
            for d in pairs(pdom[i]) do if d~=i then candidates[#candidates+1]=d end end
            local best=nil
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

local function dominates(dom,a,b) return dom[b] and dom[b][a] or false end
local function blockHasBackEdge(g,dom,from,to) return dominates(dom,to,from) end

local function findLoops(g,dom)
    local loops={}
    for _,b in ipairs(g.blocks) do
        for _,s in ipairs(b.successors) do
            if blockHasBackEdge(g,dom,b.id,s) then
                local members={[s]=true,[b.id]=true}; local work={b.id}
                while #work>0 do
                    local x=table.remove(work)
                    for _,p in ipairs(g.blocks[x].predecessors) do
                        if not members[p] then members[p]=true; work[#work+1]=p end
                    end
                end
                local arr=sortedKeys(members)
                loops[#loops+1]={header=s,latch=b.id,members=arr,kind="natural"}
            end
        end
    end
    table.sort(loops,function(a,b) return a.header<b.header end)
    return loops
end

-- ----------------------------- SSA IR --------------------------------------
local SSA={}; SSA.__index=SSA
function SSA.new(p,g,dom,idom,loops,opt)
    return setmetatable({p=p,g=g,dom=dom,idom=idom,loops=loops,opt=opt or {},
        defs={},uses={},phis={},values={},cache={},nextValue=0,stack={},inState={},outState={},
        inst={},edges={},confidence=0},SSA)
end
function SSA:newValue(kind,data)
    data=data or {}
    local key=nil
    if kind=="const" then key="const:"..tostring(data.text)
    elseif kind=="unknown" then key="unknown:"..tostring(data.block)..":"..tostring(data.reg)
    elseif kind=="op" then key="op:"..tostring(data.block)..":"..tostring(data.pc)
    elseif kind=="phi" then key="phi:"..tostring(data.block)..":"..tostring(data.reg)
    elseif kind=="upvalue" then key="upvalue:"..tostring(data.index)
    elseif kind=="global" or kind=="import" or kind=="closure" or kind=="table" or kind=="varargs" then key=kind..":"..tostring(data.block)..":"..tostring(data.pc)
    elseif kind=="vararg_return" then key="vararg_return:"..tostring(data.block)..":"..tostring(data.pc) end
    if key and self.cache[key] then
        local v=self.cache[key]; v.data=data; return v
    end
    self.nextValue+=1
    local v={id=self.nextValue,kind=kind,data=data,uses={},def=nil}
    self.values[v.id]=v
    if key then self.cache[key]=v end
    return v
end
function SSA:addUse(v,site)
    if type(v)=="table" and v.id then
        for _,u in ipairs(v.uses) do
            if u.pc==site.pc and u.block==site.block and u.role==site.role then return end
        end
        v.uses[#v.uses+1]=site
    end
end
function SSA:makeConst(text) return self:newValue("const",{text=text}) end
function SSA:makeUnknown(reg,block) return self:newValue("unknown",{reg=reg,block=block}) end
function SSA:makeOp(op,args,block,pc)
    local v=self:newValue("op",{op=op,args=args,block=block,pc=pc});
    for _,a in ipairs(args or {}) do self:addUse(a,{pc=pc,block=block,role="arg"}) end
    return v
end
function SSA:cloneState(s) local x={}; for r,v in pairs(s or {}) do x[r]=v end; return x end
function SSA:stateEqual(a,b)
    for r,v in pairs(a or {}) do if (b or {})[r]~=v then return false end end
    for r,v in pairs(b or {}) do if (a or {})[r]~=v then return false end end
    return true
end
function SSA:join(block,states)
    local out={}
    local regs={}
    for _,s in ipairs(states) do for r in pairs(s or {}) do regs[r]=true end end
    for r in pairs(regs) do
        local first=nil; local same=true
        for _,s in ipairs(states) do if s[r] then if not first then first=s[r] elseif first~=s[r] then same=false end end end
        if same and first then out[r]=first
        elseif #states>1 then
            self.phis[block.id]=self.phis[block.id] or {}
            local phi=self.phis[block.id][r]
            if not phi then
                phi=self:newValue("phi",{block=block.id,reg=r,incomings={}})
                self.phis[block.id][r]=phi
            end
            for _,s in ipairs(states) do if s[r] then phi.data.incomings[#phi.data.incomings+1]=s[r]; self:addUse(s[r],{block=block.id,role="phi"}) end end
            out[r]=phi
        end
    end
    return out
end
function SSA:liftInstruction(block,i)
    local p=self.p; local n=i.name; local A,B,C,D=i.A,i.B,i.C,i.D
    local st=self:cloneState(self.inState[block.id] or {})
    local function V(r) return st[r] or self:makeUnknown(r,block.id) end
    local function set(r,v) st[r]=v; v.def={block=block.id,pc=i.pc,reg=r} end
    local function K(ix) return self:makeConst(literal(p.constants[(ix or 0)+1])) end
    local args
    if n=="LOADNIL" then set(A,self:makeConst("nil"))
    elseif n=="LOADB" then set(A,self:makeConst(B~=0 and "true" or "false"))
    elseif n=="LOADN" then set(A,self:makeConst(tostring(D)))
    elseif n=="LOADK" then set(A,K(D))
    elseif n=="LOADKX" then set(A,K(i.aux and i.aux.KV or 0))
    elseif n=="MOVE" then set(A,V(B))
    elseif n=="GETUPVAL" then set(A,self:newValue("upvalue",{index=B,name=p.upvalues and p.upvalues[B+1]}))
    elseif n=="GETGLOBAL" then set(A,self:newValue("global",{name=K(i.aux and i.aux.KV or 0)}))
    elseif n=="GETIMPORT" then set(A,self:newValue("import",{path=(p.constants[(i.aux and i.aux.KV or 0)+1] or {}).path}))
    elseif n=="GETTABLE" then set(A,self:makeOp("index",{V(B),V(C)},block.id,i.pc))
    elseif n=="GETTABLEKS" or n=="GETUDATAKS" then set(A,self:makeOp("field",{V(B),K(i.aux and i.aux.KV or 0)},block.id,i.pc))
    elseif n=="GETTABLEN" then set(A,self:makeOp("index",{V(B),self:makeConst(tostring(C+1))},block.id,i.pc))
    elseif n=="ADD" or n=="SUB" or n=="MUL" or n=="DIV" or n=="MOD" or n=="POW" or n=="IDIV" or n=="AND" or n=="OR" then set(A,self:makeOp(n:lower(),{V(B),V(C)},block.id,i.pc))
    elseif n=="ADDK" or n=="SUBK" or n=="MULK" or n=="DIVK" or n=="MODK" or n=="POWK" or n=="IDIVK" or n=="ANDK" or n=="ORK" then set(A,self:makeOp(n:sub(1,-2):lower(),{V(B),K(C)},block.id,i.pc))
    elseif n=="SUBRK" or n=="DIVRK" then set(A,self:makeOp(n:sub(1,-3):lower(),{K(B),V(C)},block.id,i.pc))
    elseif n=="CONCAT" then args={}; for r=B,C do args[#args+1]=V(r) end; set(A,self:makeOp("concat",args,block.id,i.pc))
    elseif n=="NOT" or n=="MINUS" or n=="LENGTH" then set(A,self:makeOp(({NOT="not",MINUS="neg",LENGTH="len"})[n],{V(B)},block.id,i.pc))
    elseif n=="NAMECALL" or n=="NAMECALLUDATA" then set(A,self:makeOp("methodcall",{V(B),K(i.aux and i.aux.KV or 0)},block.id,i.pc))
    elseif n=="CALL" or n=="CALLFB" then
        args={V(A)}; if B>1 then for r=A+1,A+B-1 do args[#args+1]=V(r) end end
        local results=(C==0 and 1 or math.max(1,C-1)); for r=0,results-1 do set(A+r,self:makeOp("call",args,block.id,i.pc)) end
    elseif n=="NEWTABLE" then set(A,self:newValue("table",{block=block.id,pc=i.pc}))
    elseif n=="DUPTABLE" then set(A,self:makeOp("duptable",{K(D)},block.id,i.pc))
    elseif n=="GETVARARGS" then set(A,self:newValue("varargs",{block=block.id,pc=i.pc}))
    elseif n=="NEWCLOSURE" or n=="DUPCLOSURE" then set(A,self:newValue("closure",{proto=i.aux and i.aux.KV}))
    elseif n=="FORNPREP" or n=="FORNLOOP" or n=="FORGLOOP" or n=="FORGPREP" or n=="FORGPREP_INEXT" or n=="FORGPREP_NEXT" then
        self.inst[#self.inst+1]={kind="loopop",pc=i.pc,block=block.id,op=n,reg=A,state=self:cloneState(st)}
    elseif n=="SETUPVAL" or n=="SETGLOBAL" or n=="SETTABLE" or n=="SETTABLEKS" or n=="SETTABLEN" then
        self.inst[#self.inst+1]={kind="store",pc=i.pc,block=block.id,op=n,A=A,B=B,C=C,state=self:cloneState(st)}
    elseif n:match("^JUMP") or n=="CMPPROTO" then
        self.inst[#self.inst+1]={kind="branch",pc=i.pc,block=block.id,op=n,A=A,B=B,C=C,D=D,aux=i.aux,state=self:cloneState(st)}
    elseif n=="RETURN" then
        local vals={}; if B==0 then vals[1]=self:newValue("vararg_return",{}) else for r=A,A+B-2 do vals[#vals+1]=V(r) end end
        self.inst[#self.inst+1]={kind="return",pc=i.pc,block=block.id,values=vals,state=self:cloneState(st)}
    else
        self.inst[#self.inst+1]={kind="opaque",pc=i.pc,block=block.id,op=n,A=A,B=B,C=C,D=D,state=self:cloneState(st)}
    end
    self.outState[block.id]=st
end
function SSA:build()
    -- Fixed-point SSA construction. Each block is lifted repeatedly until its
    -- incoming register state stabilizes; phi nodes are materialized at joins.
    local g=self.g
    for _,b in ipairs(g.blocks) do self.inState[b.id]={} end
    local changed=true; local passes=0
    while changed and passes<64 do
        changed=false; passes+=1; self.inst={}
        for _,b in ipairs(g.blocks) do
            local incoming={}
            for _,pred in ipairs(b.predecessors) do incoming[#incoming+1]=self.outState[pred] or {} end
            local newin=(#incoming==0 and self.inState[b.id] or self:join(b,incoming))
            if not self:stateEqual(self.inState[b.id],newin) then self.inState[b.id]=newin; changed=true end
            self.outState[b.id]=self:cloneState(newin)
            for _,ins in ipairs(b.instructions) do self:liftInstruction(b,ins) end
        end
    end
    self.iterations=passes
    return self
end

-- --------------------------- Value graph ------------------------------------
local function valueGraph(ssa)
    local g={nodes={},edges={},roots={}}
    for id,v in pairs(ssa.values) do
        g.nodes[id]={id=id,kind=v.kind,data=v.data,def=v.def,uses=#(v.uses or {})}
        if v.kind=="return" then g.roots[#g.roots+1]=id end
        for _,u in ipairs(v.uses or {}) do g.edges[#g.edges+1]={from=id,to=u.pc or u.block,role=u.role} end
    end
    table.sort(g.roots)
    return g
end

-- ------------------------ Control dependence --------------------------------
local function controlDependence(g,pdom)
    local cd={}
    for _,b in ipairs(g.blocks) do cd[b.id]={} end
    for _,b in ipairs(g.blocks) do
        if #b.successors>=2 then
            for _,s in ipairs(b.successors) do
                for x=1,#g.blocks do
                    if pdom[s] and pdom[s][x] and not (pdom[b.id] and pdom[b.id][x]) then
                        cd[x][#cd[x]+1]=b.id
                    end
                end
            end
        end
    end
    return cd
end

-- ----------------------- Structured CFG recovery ---------------------------
local Structurer={}; Structurer.__index=Structurer
function Structurer.new(p,g,dom,idom,pdom,ipdom,loops,ssa,opt)
    return setmetatable({p=p,g=g,dom=dom,idom=idom,pdom=pdom,ipdom=ipdom,loops=loops,ssa=ssa,opt=opt or {},used={},confidence=0},Structurer)
end
function Structurer:isLoopHeader(id)
    for _,l in ipairs(self.loops) do if l.header==id then return l end end
end
function Structurer:joinFor(branch)
    local best=nil
    for x in pairs(self.pdom[branch]) do
        if x~=branch and (not best or self.pdom[x] and self.pdom[x][best]) then best=x end
    end
    return best
end
function Structurer:branchInfo(b)
    local last=b.instructions[#b.instructions]; if not last then return nil end
    local n=last.name
    local conditional=(n=="JUMPIF" or n=="JUMPIFNOT" or n:match("^JUMPIF") or n:match("^JUMPXEQ"))
    if not conditional or #b.successors<2 then return nil end
    local t=target(last.pc,last); local fall=last.pc+oplen(n)
    local tb=self.g.byPc[t]; local fb=self.g.byPc[fall]
    if not tb or not fb then return nil end
    return {block=b,trueBlock=tb,falseBlock=fb,target=t,fall=fall,join=self:joinFor(b.id),instr=last}
end
function Structurer:loopInfoAt(id) return self:isLoopHeader(id) end

local function readableExpr(v,ssa,p,names,seen)
    seen=seen or {}; if not v then return "nil",0 end
    if seen[v.id] then return "v"..v.id,1 end; seen[v.id]=true
    local d=v.data or {}; local k=v.kind
    if k=="const" then return d.text or "nil",1 end
    if k=="unknown" then return names[d.reg] or ("v"..tostring(d.reg)),1 end
    if k=="upvalue" then return d.name or ("upvalue"..tostring(d.index)),1 end
    if k=="global" then return d.name and readableExpr(d.name,ssa,p,names,seen) or "_G",1 end
    if k=="import" then return d.path or "import",1 end
    if k=="varargs" or k=="vararg_return" then return "...",1 end
    if k=="closure" then return "function(...) end",1 end
    if k=="table" then return "{}",1 end
    if k=="phi" then return names[d.reg or -1] or ("v"..v.id),1 end
    if k=="op" then
        local op=d.op; local a={}
        for _,x in ipairs(d.args or {}) do a[#a+1]=readableExpr(x,ssa,p,names,seen) end
        if op=="index" then return a[1].."["..a[2].."]",2 end
        if op=="field" then
            local key=a[2] or "field"; key=key:gsub('^"(.*)"$','%1')
            return identifier(key) and a[1].."."..key or a[1].."["..(a[2] or '"field"').."]",2
        end
        if op=="methodcall" then return a[1]..":"..((a[2] or '"method"'):gsub('^"(.*)"$','%1')).."(...)" ,2 end
        if op=="call" then return a[1].."(...)" ,3 end
        if op=="concat" then return table.concat(a," .. "),2 end
        local sym={add="+",sub="-",mul="*",div="/",mod="%",pow="^",idiv="//",["and"]="and",["or"]="or"}
        if sym[op] then return "("..a[1].." "..sym[op].." "..a[2]..")",2 end
        if op=="not" then return "not ("..a[1]..")",2 end
        if op=="neg" then return "-"..a[1],2 end
        if op=="len" then return "#"..a[1],2 end
        if op=="duptable" then return a[1] or "{}",1 end
    end
    return "v"..v.id,0
end

local function simplifyExpr(x)
    if not x then return x end
    x=x:gsub("%(true and ([^)]+)%)","%1"):gsub("%(false or ([^)]+)%)","%1")
    x=x:gsub("%(nil == nil%)","true"):gsub("%(nil ~= nil%)","false")
    return x
end

function Structurer:condition(b)
    local i=b.instructions[#b.instructions]; local n=i.name
    local names={}
    for _,l in ipairs(self.p.locals or {}) do names[l.reg]=l.name end
    for r=0,(self.p.maxstack or 1)-1 do names[r]=names[r] or ("v"..r) end
    local st=self.ssa.outState[b.id] or {}
    local function R(r) return readableExpr(st[r],self.ssa,self.p,names) end
    local cmp={JUMPIFEQ="==",JUMPIFLE="<=",JUMPIFLT="<",JUMPIFNOTEQ="~=",JUMPIFNOTLE=">",JUMPIFNOTLT=">="}
    if n=="JUMPIF" then return R(i.A),true end
    if n=="JUMPIFNOT" then return "not ("..R(i.A)..")",true end
    if cmp[n] then return "("..R(i.A).." "..cmp[n].." "..R(i.C)..")",true end
    if n=="JUMPXEQKNIL" then return "("..R(i.A).." "..((i.aux and i.aux.NOT) and "~=" or "==").." nil)",true end
    if n=="JUMPXEQKB" then return "("..R(i.A).." "..((i.aux and i.aux.NOT) and "~=" or "==").." "..((i.aux and i.aux.KB) and "true" or "false")..")",true end
    return "true",false
end

function Structurer:emitInstruction(b,ins,indent,declared)
    local s=self.ssa; local p=self.p; local n=ins.name; local A,B,C,D=ins.A,ins.B,ins.C,ins.D
    local names={}; for _,l in ipairs(p.locals or {}) do names[l.reg]=l.name end; for r=0,(p.maxstack or 1)-1 do names[r]=names[r] or ("v"..r) end
    local st=s.outState[b.id] or {}
    local function R(r) return simplifyExpr(readableExpr(st[r],s,p,names)) end
    local function L(r) return names[r] or ("v"..r) end
    if n=="LOADNIL" or n=="LOADB" or n=="LOADN" or n=="LOADK" or n=="LOADKX" or n=="MOVE" or n=="GETUPVAL" or n=="GETGLOBAL" or n=="GETIMPORT" or n=="GETTABLE" or n=="GETTABLEKS" or n=="GETUDATAKS" or n=="GETTABLEN" or n=="ADD" or n=="SUB" or n=="MUL" or n=="DIV" or n=="MOD" or n=="POW" or n=="IDIV" or n=="AND" or n=="OR" or n=="ADDK" or n=="SUBK" or n=="MULK" or n=="DIVK" or n=="MODK" or n=="POWK" or n=="IDIVK" or n=="ANDK" or n=="ORK" or n=="SUBRK" or n=="DIVRK" or n=="CONCAT" or n=="NOT" or n=="MINUS" or n=="LENGTH" then
        local val=st[A]; local text=readableExpr(val,s,p,names)
        if not declared[A] then declared[A]=true; return "local "..L(A).." = "..text end
        return L(A).." = "..text
    end
    if n=="SETUPVAL" then return (p.upvalues and p.upvalues[B+1] or "upvalue"..B).." = "..R(A) end
    if n=="SETGLOBAL" then local k=(p.constants[(ins.aux and ins.aux.KV or 0)+1] or {}).value or "global"; return identifier(k) and k.." = "..R(A) or "_G["..quote(k).."] = "..R(A) end
    if n=="SETTABLE" then return R(A).."["..R(B).."] = "..R(C) end
    if n=="SETTABLEKS" or n=="SETUDATAKS" then local k=(p.constants[(ins.aux and ins.aux.KV or 0)+1] or {}).value or "field"; return identifier(k) and R(A).."."..k.." = "..R(B) or R(A).."["..quote(k).."] = "..R(B) end
    if n=="SETTABLEN" then return R(A).."["..(C+1).."] = "..R(B) end
    if n=="NEWTABLE" or n=="DUPTABLE" then local val=st[A]; local text=readableExpr(val,s,p,names); if not declared[A] then declared[A]=true; return "local "..L(A).." = "..text end; return L(A).." = "..text end
    if n=="NAMECALL" or n=="NAMECALLUDATA" then local val=st[A]; local text=readableExpr(val,s,p,names); if not declared[A] then declared[A]=true; return "local "..L(A).." = "..text end; return L(A).." = "..text end
    if n=="CALL" or n=="CALLFB" then
        local val=st[A]; local text=readableExpr(val,s,p,names); return text
    end
    if n=="RETURN" then
        if B==0 then return "return ..." end
        local q={}; for r=A,A+B-2 do q[#q+1]=R(r) end; return "return "..table.concat(q,", ")
    end
    if n=="GETVARARGS" then return L(A).." = ..." end
    if n=="PREPVARARGS" or n=="COVERAGE" or n=="NATIVECALL" or n=="FASTCALL" or n=="FASTCALL1" or n=="FASTCALL2" or n=="FASTCALL2K" or n=="FASTCALL3" then return "-- "..n end
    if n=="NEWCLOSURE" or n=="DUPCLOSURE" then return L(A).." = function(...) end" end
    if n=="CAPTURE" then return "-- capture" end
    if n:match("^FOR") then return "-- [structured loop handled by CFG]" end
    if n:match("^JUMP") or n=="CMPPROTO" then return nil end
    return "-- "..n
end

function Structurer:recover()
    local g=self.g; local out={}; local declared={}; local emitted={}
    local names={}; for _,l in ipairs(self.p.locals or {}) do names[l.reg]=l.name end
    local function put(depth,s) if s and s~="" then out[#out+1]=string.rep("    ",depth)..s end end
    local function walk(id,depth,stop,active)
        active=active or {}; if active[id] or id==stop then return end; active[id]=true
        local b=g.map[id]
        if not b then active[id]=nil; return end
        local loop=self:loopInfoAt(id)
        if loop and not self.used["loop"..id] then
            self.used["loop"..id]=true
            local header=b; local cond=nil
            local term=header.instructions[#header.instructions]
            if term and (term.name=="FORNPREP" or term.name=="FORGPREP" or term.name=="FORGPREP_INEXT" or term.name=="FORGPREP_NEXT") then
                put(depth,"for "..(names[term.A] or "v"..term.A).." in ... do")
            else
                put(depth,"while true do")
            end
            local nextId=nil
            for _,s in ipairs(header.successors) do if contains(loop.members,s) and s~=header.id then nextId=s end end
            if nextId then walk(nextId,depth+1,header.id,active) end
            put(depth,"end")
            active[id]=nil; return
        end
        local bi=self:branchInfo(b)
        if bi and bi.join and bi.join~=id and not active[bi.join] then
            local cond,ok=self:condition(b)
            if ok then
                put(depth,"if "..cond.." then")
                walk(bi.trueBlock.id,depth+1,bi.join,active)
                if bi.falseBlock.id~=bi.join then
                    put(depth,"else")
                    walk(bi.falseBlock.id,depth+1,bi.join,active)
                end
                put(depth,"end")
                self.confidence+=3
                if bi.join then walk(bi.join,depth,stop,active) end
                active[id]=nil; return
            end
        end
        if not emitted[id] then
            emitted[id]=true
            for _,ins in ipairs(b.instructions) do
                local s=self:emitInstruction(b,ins,depth,declared)
                if s then put(depth,s) end
            end
        end
        local nexts=b.successors
        if #nexts==1 and nexts[1]~=stop then walk(nexts[1],depth,stop,active)
        elseif #nexts>1 then
            for _,s in ipairs(nexts) do if s~=stop then put(depth,"-- control-flow edge -> B"..s) end end
        end
        active[id]=nil
    end
    walk(g.entry.id,0,nil,{})
    return table.concat(out,"\n")
end

-- ------------------------- Readability / cleanup ----------------------------
local function cleanupSource(src)
    src=src:gsub("%n%s*%-%-%s*%[structured loop handled by CFG%]","")
    src=src:gsub("%n%s*%-%-%s*prepare varargs","")
    src=src:gsub("\n%s*\n%s*\n+","\n\n")
    src=src:gsub("%f[%w_]v(%d+)%f[^%w_]",function(n) return "v"..n end)
    return src
end

local function confidenceReport(g,ssa,st)
    local score=0; local total=0
    for _,b in ipairs(g.blocks) do
        total+=1
        if #b.predecessors<=2 then score+=1 end
        if #b.successors<=2 then score+=1 end
    end
    score+=#ssa.values
    local denom=math.max(1,total*2+#ssa.values)
    local pct=math.floor((score/denom)*100+0.5)
    return {score=score,maximum=denom,percent=pct,structured=st.confidence}
end

-- Optional AI adapter. The decompiler never silently sends bytecode/source over
-- the network. A caller can provide options.aiReview = function(prompt, context)
-- and return suggested source/edits. The returned text is treated as a proposal
-- and is NOT executed. This makes the engine model-agnostic and safe by default.
local function aiReview(result,options)
    local f=options and options.aiReview
    if type(f)~="function" then return nil end
    local ok,res=pcall(f,
        "Review this recovered Luau source for semantic/structural mistakes. "..
        "Return only a corrected Luau source candidate; do not invent APIs.",
        {source=result.source,analysis=result.analysis,ssa=result.ssaSummary})
    if ok and type(res)=="string" and #res>0 then return res end
end

function m0pu.advancedAnalyze(input,options)
    options=options or {}; local data=input
    if type(input)~="string" then local getter=options.getscriptbytecode or getscriptbytecode; assert(type(getter)=="function","getscriptbytecode unavailable"); data=assert(getter(input)) end
    local c=parseAny(data,options); local reports={}
    for _,p in ipairs(c.protos or {}) do
        local g=advCFG(p); local dom,idom,domChildren=computeDominators(g); local pdom,ipdom,exits=computePostDominators(g); local loops=findLoops(g,dom); local cd=controlDependence(g,pdom); local ssa=SSA.new(p,g,dom,idom,loops,options):build()
        reports[p.id]={metrics=metrics(p),dominators=dom,idom=idom,postdominators=pdom,ipdom=ipdom,exits=exits,loops=loops,controlDependence=cd,ssa=ssa,valueGraph=valueGraph(ssa)}
    end
    return {chunk=c,protos=reports}
end

function m0pu.ssaDump(input,options)
    local a=m0pu.advancedAnalyze(input,options); local out={"-- m0pu SSA dump"}
    for _,r in ipairs(a.protos) do
        out[#out+1]="-- proto "..r.metrics.instructions.." instructions"
        local s=r.ssa
        for id,v in pairs(s.values) do
            local d=v.data or {}; local rhs=v.kind
            if v.kind=="const" then rhs=d.text
            elseif v.kind=="op" then rhs=d.op
            elseif v.kind=="phi" then rhs="phi("..tostring(d.reg)..")"
            elseif v.kind=="unknown" then rhs="unknown r"..tostring(d.reg)
            elseif v.kind=="upvalue" then rhs=d.name or "upvalue"
            elseif v.kind=="global" then rhs="global"
            elseif v.kind=="import" then rhs=d.path or "import"
            end
            out[#out+1]=("v%d = %-10s def=%s uses=%d"):format(id,rhs,v.def and ("B"..v.def.block.."/PC"..v.def.pc) or "-",#(v.uses or {}))
        end
    end
    return table.concat(out,"\n")
end

function m0pu.cfgReport(input,options)
    local a=m0pu.advancedAnalyze(input,options); local out={"-- m0pu CFG / dominance report"}
    for _,r in ipairs(a.protos) do
        out[#out+1]="-- proto"
        for _,b in ipairs(r.ssa.g.blocks) do
            out[#out+1]=("B%d [%d..%d] succ={%s} pred={%s} idom=%s ipdom=%s"):format(b.id,b.start,b.finish,table.concat(b.successors,","),table.concat(b.predecessors,","),tostring(r.idom[b.id]),tostring(r.ipdom[b.id]))
        end
        for _,l in ipairs(r.loops) do out[#out+1]="loop header B"..l.header.." latch B"..l.latch.." members={"..table.concat(l.members,",").."}" end
    end
    return table.concat(out,"\n")
end

-- Replace the v2 emitter with the advanced structured pipeline.
function m0pu.decompile(input,options)
    options=options or {}; local data=input
    if type(input)~="string" then
        local getter=options.getscriptbytecode or getscriptbytecode
        assert(type(getter)=="function","getscriptbytecode is unavailable")
        local ok,res=pcall(getter,input); assert(ok and type(res)=="string" and #res>0,"failed to obtain bytecode: "..tostring(res)); data=res
    end
    local c=parseAny(data,options); assert(c.main,"no main prototype found")
    local function one(p)
        local g=advCFG(p); local dom,idom,domChildren=computeDominators(g); local pdom,ipdom,exits=computePostDominators(g); local loops=findLoops(g,dom)
        local ssa=SSA.new(p,g,dom,idom,loops,options):build(); local st=Structurer.new(p,g,dom,idom,pdom,ipdom,loops,ssa,options)
        local source=cleanupSource(st:recover())
        local params={}; local names={}; for _,l in ipairs(p.locals or {}) do names[l.reg]=l.name end; for r=0,(p.maxstack or 1)-1 do names[r]=names[r] or ("v"..r) end
        for i=0,(p.numparams or 0)-1 do params[#params+1]=names[i] end; if p.vararg then params[#params+1]="..." end
        local fname=identifier(p.debugname) and p.debugname or "anonymous"
        source="function "..fname.."("..table.concat(params,", ")..")\n"..source.."\nend"
        local result={source=source,analysis=metrics(p),ssaSummary={values=ssa.nextValue,phis=0,iterations=ssa.iterations,loops=#loops,blocks=#g.blocks},graph=valueGraph(ssa),confidence=confidenceReport(g,ssa,st),dominatorChildren=domChildren,postdominator=ipdom}
        for _,x in pairs(ssa.phis) do for _ in pairs(x) do result.ssaSummary.phis+=1 end end
        return result
    end
    local main=one(c.main)
    if options.aiReview then
        local proposed=aiReview(main,options)
        if proposed then main.aiCandidate=proposed end
    end
    main.format=c.format; main.bytecodeVersion=c.bytecodeVersion; main.typeVersion=c.typeVersion; main.bytecodeSize=#data; main.protoCount=#(c.protos or {}); main.mainProto=c.main.id; main.warnings=c.warnings or {}; main.chunk=options.returnChunk and c or nil
    return main
end

function m0pu.getCapabilities()
    local e=env()
    return {getscriptbytecode=type(getscriptbytecode)=="function",writefile=type(writefile)=="function",
        readfile=type(readfile)=="function",string_unpack=type(string.unpack)=="function",environment=type(e)=="table",
        ssa=true,phi=true,value_graph=true,dominators=true,postdominators=true,control_dependence=true,
        structured_cf=true,optional_ai_review=true}
end

e.m0pu=m0pu
e.m0puDecompile=function(x,o) return m0pu.decompile(x,o).source end
return m0pu
