--[=[ Lua/Luau CTF VM Deobfuscation Suite
Static-only: never executes target source.
Families: Luraph v13/v14.x, Prometheus, IronBrew/IronBrew2,
MoonSec V3/V4, luaobfuscator, generic Lua VM patterns.
]=]
local D={}
local function inc(t,k,n)t[k]=(t[k]or 0)+(n or 1)end
local function add(t,x)if not x or x==""then return end for _,v in ipairs(t)do if v==x then return end end t[#t+1]=x end
local function esc(x)return(x:gsub("([^%w])","%%%1"))end
local function nums(s,r)
 s=s:gsub("%-?0[bB][01]+",function(x)local sg=""if x:sub(1,1)=="-"then sg="-"x=x:sub(2)end local b=x:match("^0[bB]([01]+)$")if not b then return sg..x end local n=0 for i=1,#b do n=n*2+(b:sub(i,i)=="1"and 1 or 0)end inc(r,"binary")return sg..n end)
 s=s:gsub("0[xX][%da-fA-F]+",function(x)local n=tonumber(x)if n then inc(r,"hex")return tostring(n)end return x end)return s end
local function strings(s,r)
 local function dec(x)x=x:gsub("\\x(%x%x)",function(h)return string.char(tonumber(h,16))end)x=x:gsub("\\(%d%d?%d?)",function(n)local v=tonumber(n)if v and v<=255 then return string.char(v)end return"\\"..n end)return x:gsub("\\n","\n"):gsub("\\r","\r"):gsub("\\t","\t"):gsub("\\\\","\\"):gsub('\\"','"'):gsub("\\'","'")end
 s=s:gsub('"([^"\\]*(\\.[^"\\]*)*)"',function(x)local y=dec(x)if y~=x then inc(r,"escaped_strings")end return string.format("%q",y)end)
 s=s:gsub("'([^'\\]*(\\.[^'\\]*)*)'",function(x)local y=dec(x)if y~=x then inc(r,"escaped_strings")end return string.format("%q",y)end)return s end
local function char(s,r)return s:gsub("string%.char%s*%(([%d%s,%-]+)%)",function(a)local o={}for n in a:gmatch("%-?%d+")do n=tonumber(n)if not n or n<0 or n>255 then return"string.char("..a..")end o[#o+1]=string.char(n)end inc(r,"string_char")return string.format("%q",table.concat(o))end)end
local function rev(s,r)return s:gsub("string%.reverse%s*%(%s*(['\"])(.-)%1%s*%)",function(_,x)inc(r,"string_reverse")return string.format("%q",x:reverse())end)end
local function concat(s,r)return s:gsub("table%.concat%s*%(%s*{%s*([^{}]-)%s*}%s*%)",function(a)local o={}for x in a:gmatch('"([^"]*)"')do o[#o+1]=x end if#o>0 then inc(r,"table_concat")return string.format("%q",table.concat(o))end return"table.concat({"..a.."})"end)end
local function bits(s,r)
 if not bit32 then return s end local f={bxor=bit32.bxor,band=bit32.band,bor=bit32.bor,lshift=bit32.lshift,rshift=bit32.rshift}
 for k,fn in pairs(f)do s=s:gsub("bit32%."..k.."%s*%(%s*(%d+)%s*,%s*(%d+)%s*%)",function(a,b)inc(r,"bit32_"..k)return tostring(fn(tonumber(a),tonumber(b)))end)end return s end
local function arith(s,r)
 local q={{"(%-?%d+)%s*%+%s*(%-?%d+)",function(a,b)return a+b end},{"(%-?%d+)%s*%-%s*(%-?%d+)",function(a,b)return a-b end},{"(%-?%d+)%s*%*%s*(%-?%d+)",function(a,b)return a*b end},{"(%-?%d+)%s*/%s*(%-?%d+)",function(a,b)if b==0 then return nil end return a/b end}}
 for _,z in ipairs(q)do s=s:gsub(z[1],function(a,b)a,b=tonumber(a),tonumber(b)local v=z[2](a,b)if not v then return tostring(a)end inc(r,"arithmetic")return tostring(v)end)end return s end
local function detect(s)
 local defs={Luraph={"Luraph Obfuscator","LPH_ENCFUNC","a%.F%[","a:H%(","a:G%(","bit32%.bxor"},Prometheus={"Prometheus","AntiTamper","Watermark","Proxify"},IronBrew={"IronBrew","IronBrew2","IronBrewObfuscator"},MoonSec={"MoonSec","MoonSecV3","MoonSecV4","MoonSec V3","MoonSec V4"},LuaObfuscator={"luaobfuscator","LuaObfuscator"},GenericVM={"while%s+true%s+do","string%.byte","table%.concat","bit32%."}}
 local out={}local best="Unknown"local score=0
 for k,p in pairs(defs)do local n=0 for _,x in ipairs(p)do if s:find(x)then n=n+1 end end if n>0 then out[k]=n end if n>score then score=n best=k end end return out,best,score end
local function vm(s)
 local v={states={},caches={},handlers={},opcodes={},ops={},score=0}
 for x in s:gmatch("([%a_][%w_]*)%s*[%<%>]=?%s*0x%x+")do add(v.states,x)end
 for x in s:gmatch("([%a_][%w_]*)%s*=%s*0x%x+")do add(v.states,x)end
 for x in s:gmatch("([%a_][%w_]*)%.F%[")do add(v.caches,x..".F")end
 for x in s:gmatch("([%a_][%w_]*)%s*:%s*[HG]%s*%(")do add(v.caches,x..":H/G")end
 for a,b,c in s:gmatch("if%s+([%a_][%w_]*)%s*([<>=~]+)%s*(0x%x+)")do add(v.handlers,a.." "..b.." "..c)end
 for a,x in s:gmatch("([%a_][%w_]*)%s*=%s*([^;\n]+)")do if x:find("0x")or x:find("0[bB]")then add(v.opcodes,a.." = "..x:match("^%s*(.-)%s*$"))end end
 local p={CALL="%w+%s*%(",BYTE="string%.byte%s*%(",CHAR="string%.char%s*%(",BIT="bit32%.%w+%(",RET="%f[%w]return%f[^%w_]"}
 for k,x in pairs(p)do local n=0 for _ in s:gmatch(x)do n=n+1 end if n>0 then v.ops[k]=n end end
 if#v.caches>0 then v.score=v.score+2 end if#v.handlers>=3 then v.score=v.score+2 end if#v.opcodes>=3 then v.score=v.score+1 end if v.ops.BIT then v.score=v.score+1 end if v.ops.BYTE then v.score=v.score+1 end v.probable=v.score>=4 return v end
function D.deobfuscate(source,opt)
 opt=opt or{}assert(type(source)=="string","source must be a string")local r={passes=0,stats={}}local s=source
 r.detections,r.family,r.score=detect(s)local max=math.clamp(tonumber(opt.MaxPasses)or 12,1,50)
 for i=1,max do local old=s;s=nums(s,r.stats);s=strings(s,r.stats);s=char(s,r.stats);s=rev(s,r.stats);s=concat(s,r.stats);s=bits(s,r.stats);s=arith(s,r.stats);s=s:gsub("[ \t]+\n","\n"):gsub("\n\n\n+","\n\n");r.passes=i if s==old then break end end
 r.vm=vm(s);r.ir={type="LuaVMAnalysis",version=1,family=r.family,score=r.vm.score,probable_vm=r.vm.probable,states=r.vm.states,caches=r.vm.caches,handlers=r.vm.handlers,opcodes=r.vm.opcodes,operations=r.vm.ops}
 r.warning="Static-only. This tool does not execute target code or claim to recover arbitrary encrypted/virtualized functions."
 return s,r end
function D.print_report(r)
 print("===== Lua VM Deobfuscator =====")print("Family: "..tostring(r.family).." score="..tostring(r.score))print("Passes: "..r.passes)for k,v in pairs(r.detections or{})do print(k..": "..v)end print("VM: "..tostring(r.vm.probable).." score="..r.vm.score)for k,v in pairs(r.stats or{})do print(k..": "..v)end print(r.warning)end
function D.print_vm_report(v)if not v then return end print("===== VM REPORT =====")print("probable="..tostring(v.probable).." score="..v.score)for _,x in ipairs(v.states)do print("STATE "..x)end for _,x in ipairs(v.caches)do print("CACHE "..x)end for _,x in ipairs(v.handlers)do print("HANDLER "..x)end for _,x in ipairs(v.opcodes)do print("OPCODE "..x)end end
function D.ir_to_text(ir)local o={"-- Static VM IR","family="..tostring(ir.family),"score="..tostring(ir.score),"probable_vm="..tostring(ir.probable_vm),"[STATES]"}for _,x in ipairs(ir.states or{})do o[#o+1]=x end o[#o+1]="[CACHES]"for _,x in ipairs(ir.caches or{})do o[#o+1]=x end o[#o+1]="[HANDLERS]"for _,x in ipairs(ir.handlers or{})do o[#o+1]=x end o[#o+1]="[OPCODES]"for _,x in ipairs(ir.opcodes or{})do o[#o+1]=x end return table.concat(o,"\n")end
D.analyze_vm=vm;D.detect=detect;return D
