-- ironbrew1 capture runtime (loaded through --cfg plugin_rt, see envlog.luau).
-- The instrumented VM source (instrument.py) calls:
--   __IBF(f, loc)              every helper closure outside the interpreters:
--                              closure -> AST location of its function
--   __IBC(mk, params, vars)    in a closure maker, right before it returns the
--                              interpreter: its parameters and every visible
--                              local ({[declaration location] = value})
-- At the end of the run, protos that never got a closure are pushed through
-- the maker too (it decodes them and captures), then everything reachable is
-- written as one JSON line: "\0IBDUMP {...}".
local A = ...
local E, CHAIN, R, isP = A.E, A.CHAIN, A.R, A.isP

local REG = setmetatable({}, { __mode = "k" })   -- closure -> AST location
local FIRST = {}                                 -- AST location -> first closure
local CAPS = {}
local SEEN = {}                                  -- maker's first argument -> true

local function IBF(f, loc)
	if REG[f] == nil then
		REG[f] = loc
		if FIRST[loc] == nil then FIRST[loc] = f end
	end
	return f
end
local function IBC(mk, params, vars)
	local p = params[1]
	if type(p) == "table" then
		if SEEN[p] then return end
		SEEN[p] = true
	end
	CAPS[#CAPS + 1] = { mk = mk, params = params, vars = vars }
end
rawset(E, "__IBF", IBF)
rawset(E, "__IBC", IBC)

-- library functions by name (the VM gets them as arguments of its wrapper)
local NAME = {}
local function nameLib(prefix, t)
	for k, v in next, t do
		if type(v) == "function" and NAME[v] == nil and type(k) == "string" then NAME[v] = prefix .. k end
	end
end

local function sig(t)
	local ks = {}
	for k in next, t do
		if type(k) ~= "number" and type(k) ~= "string" then return nil end
		ks[#ks + 1] = tostring(k)
	end
	table.sort(ks)
	return table.concat(ks, ",")
end

-- protos that never got a closure: tables shaped like a captured maker
-- argument, reachable from the captures, are passed to the maker (it
-- decodes them; __IBC captures)
local function force()
	local sigs = {}
	for _, c in CAPS do
		local p = c.params[1]
		if type(p) == "table" then
			local s = sig(p)
			if s and s ~= "" then sigs[s] = c end
		end
	end
	local calls = 0
	local round = 0
	-- the run is over: no budget, no spin watchdog while the makers decode
	CHAIN.unlimited = true
	local sw = rawget(E, "__SPIN")
	if type(sw) == "table" then sw.step = math.huge end
	repeat
		round += 1
		local before = #CAPS
		local seen = {}
		local todo = {}
		for _, c in CAPS do
			for _, v in next, c.vars do
				if type(v) == "table" and not seen[v] and v ~= E then
					seen[v] = true
					todo[#todo + 1] = v
				end
			end
		end
		local i = 1
		while i <= #todo and i < 400000 do
			local t = todo[i]
			i += 1
			if not SEEN[t] then
				local s = sig(t)
				local c = s and sigs[s]
				if c and calls < 20000 then
					local maker = FIRST[c.mk]
					if maker then
						calls += 1
						local args = table.clone(c.params)
						args[1] = t
						args[2] = nil
						local co = coroutine.create(maker)
						pcall(coroutine.resume, co, table.unpack(args, 1, math.max(3, #c.params)))
					end
				end
			end
			for k, v in next, t do
				if type(v) == "table" and not seen[v] and v ~= E and not isP(v) then
					seen[v] = true
					todo[#todo + 1] = v
				end
			end
		end
	until #CAPS == before or round > 20
	return calls
end

-- lazily decoded arrays (instructions, constants: a metatable __index
-- decodes slot k on first use): read every slot up to past the highest
-- one decoded so far, so code that never ran is in the dump too
local function materialize()
	local done = {}
	local n = 0
	for _, c in CAPS do
		for _, v in next, c.vars do
			if type(v) == "table" and not done[v] and v ~= E and not isP(v) then
				done[v] = true
				local mt = getmetatable(v)
				if type(mt) == "table" and rawget(mt, "__index") ~= nil then
					local hi = 0
					for k in next, v do
						if type(k) == "number" and k > hi and k < 1e7 then hi = k end
					end
					local miss = 0
					local k = 1
					while k <= hi or miss < 64 do
						if rawget(v, k) == nil then
							local ok, x = pcall(function() return v[k] end)
							if ok and x ~= nil then
								pcall(rawset, v, k, x)
								n += 1
								miss = 0
							elseif k > hi then
								miss += 1
							end
						end
						k += 1
					end
				end
			end
		end
	end
	return n
end

-- self-modifying code: a maker local P whose P[pc] is a proxy of instruction
-- pc (metatable __index makes it; its __newindex writes the operand arrays):
-- `P[pc][key] = x` changes an operand. Probe which operand array each key
-- writes (a sentinel through P[1][key]; the array's slot 1 is restored).
local function proxies(c)
	local tabs, keys = {}, {}
	for _, v in next, c.vars do
		if type(v) == "table" and v ~= E and not isP(v) then
			tabs[#tabs + 1] = v
			local n = 0
			for _, x in next, v do
				n += 1
				if n > 32 then break end
			end
			if n <= 32 then
				for _, x in next, v do
					if type(x) == "string" or type(x) == "number" then keys[x] = true end
				end
			end
		end
	end
	local out = {}
	for _, P in tabs do
		local mt = getmetatable(P)
		if type(mt) == "table" and type(rawget(mt, "__index")) == "function" then
			local ok, px = pcall(function() return P[1] end)
			local pmt = ok and type(px) == "table" and getmetatable(px)
			if type(pmt) == "table" and rawget(pmt, "__newindex") ~= nil then
				local map = {}
				for key in next, keys do
					local before = {}
					for i, T in tabs do before[i] = rawget(T, 1) end
					local SENT = {}
					if pcall(function() px[key] = SENT end) then
						for i, T in tabs do
							if rawget(T, 1) == SENT then
								map[#map + 1] = { key, T }
								rawset(T, 1, before[i])
							end
						end
					end
				end
				if #map > 0 then out[#out + 1] = { P, map } end
			end
		end
	end
	return out
end

local function hex(s)
	return (string.gsub(s, ".", function(ch) return string.format("%02x", string.byte(ch)) end))
end
local function num(x)
	if x ~= x then return '{"n":"nan"}' end
	if x == math.huge then return '{"n":"inf"}' end
	if x == -math.huge then return '{"n":"-inf"}' end
	if x == math.floor(x) and math.abs(x) < 2 ^ 53 then return string.format("%d", x) end
	return string.format("%.17g", x)
end

local function dump()
	for _, lib in { "string", "table", "math", "bit32", "coroutine", "buffer", "utf8", "os", "debug", "task" } do
		local t = rawget(E, lib)
		if type(t) == "table" then nameLib(lib .. ".", t) end
		local rt = R[lib] or _G[lib]
		if type(rt) == "table" then nameLib(lib .. ".", rt) end
	end
	nameLib("", E)
	-- global tables and engine objects by name (a VM cache holding `math`
	-- or `game` must lift as that global, not as its contents)
	local GNAME = {}
	for k, v in next, E do
		if type(k) == "string" and (type(v) == "table" or type(v) == "userdata") and GNAME[v] == nil
			and not string.find(k, "^__") then
			GNAME[v] = k
		end
	end
	local t0 = os.clock()
	local forced = force()
	local lazy = materialize()
	local PX = {}
	for i, c in CAPS do
		local ok, r = pcall(proxies, c)
		PX[i] = ok and r or {}
	end
	local ids = {}
	local order = {}
	local sids, slist = {}, {}
	local function val(v)
		local t = type(v)
		if v == nil then return "null" end
		if t == "boolean" then return v and "true" or "false" end
		if t == "number" then return num(v) end
		if t == "string" then
			if #v <= 48 then return '{"s":"' .. hex(v) .. '"}' end
			-- long strings (bytecode blobs) once, by id
			local sid = sids[v]
			if sid == nil then
				sid = #slist + 1
				sids[v] = sid
				slist[sid] = v
			end
			return '{"S":' .. sid .. "}"
		end
		if v == E then return '{"env":true}' end
		if (t == "table" or t == "userdata") and GNAME[v] ~= nil then return '{"g":"' .. GNAME[v] .. '"}' end
		if t == "table" and not isP(v) then
			local id = ids[v]
			if id == nil then
				id = #order + 1
				ids[v] = id
				order[id] = v
			end
			return '{"t":' .. id .. "}"
		end
		if t == "function" then
			if REG[v] ~= nil then return '{"f":"' .. REG[v] .. '"}' end
			if NAME[v] ~= nil then return '{"c":"' .. NAME[v] .. '"}' end
			return '{"c":"?"}'
		end
		if t == "vector" then return '{"v":[' .. num(v.x) .. "," .. num(v.y) .. "," .. num(v.z) .. "]}" end
		if t == "buffer" then return '{"b":"' .. hex(buffer.tostring(v)) .. '"}' end
		local ok, s = pcall(tostring, v)
		return '{"u":"' .. typeof(v) .. '","x":"' .. hex(ok and s or "?") .. '"}'
	end
	local caps = {}
	for i, c in CAPS do
		local vars = {}
		for k, v in next, c.vars do vars[#vars + 1] = '"' .. k .. '":' .. val(v) end
		local ps = {}
		for j = 1, math.max(#c.params, 3) do ps[j] = val(c.params[j]) end
		local px = {}
		for j, e in PX[i] do
			local m = {}
			for k, kv in e[2] do m[k] = "[" .. val(kv[1]) .. "," .. val(kv[2]) .. "]" end
			px[j] = '{"t":' .. val(e[1]) .. ',"map":[' .. table.concat(m, ",") .. "]}"
		end
		caps[i] = '{"mk":"' .. c.mk .. '","params":[' .. table.concat(ps, ",") .. '],"vars":{'
			.. table.concat(vars, ",") .. '},"proxies":[' .. table.concat(px, ",") .. "]}"
	end
	-- tables (grow while serializing)
	local tabs = {}
	local i = 1
	while i <= #order do
		local tb = order[i]
		local items = {}
		for k, v in next, tb do items[#items + 1] = "[" .. val(k) .. "," .. val(v) .. "]" end
		local mt = getmetatable(tb)
		tabs[i] = '"' .. i .. '":{"e":[' .. table.concat(items, ",") .. "]"
			.. (mt ~= nil and (',"mt":' .. val(mt)) or "") .. "}"
		i += 1
	end
	local strs = {}
	for k, v in slist do strs[k] = '"' .. hex(v) .. '"' end
	return "\0IBDUMP " .. string.format('{"forced":%d,"lazy":%d,"secs":%.2f,', forced, lazy, os.clock() - t0)
		.. '"caps":[' .. table.concat(caps, ",") .. '],"tables":{' .. table.concat(tabs, ",")
		.. '},"strings":[' .. table.concat(strs, ",") .. "]}"
end
CHAIN.endHooks = CHAIN.endHooks or {}
table.insert(CHAIN.endHooks, dump)
