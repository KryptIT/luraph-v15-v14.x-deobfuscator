--!nocheck
-- Behaviour check for fold.py: runs a deobfuscated output against a logging
-- proxy environment and prints every observable operation (property writes,
-- calls with their arguments), invoking each function value it sees once.
-- Run it on the output with and without folding (--no-fold) and diff:
--   python research/fold_check.py <script>
-- Locals, helpers and loops leave no trace in the log, so equal logs mean the
-- folded code does the same things in the same order.
local SRC = ...
local out = {}
local ncall = 0
local seen = setmetatable({}, { __mode = "k" })
local depth = 0
local NAME = setmetatable({}, { __mode = "k" })
local P, show, invoke

function show(v, d)
	d = d or 0
	local t = type(v)
	if t == "string" then return string.format("%q", v) end
	if t == "number" then return string.format("%.17g", v) end
	if t == "userdata" and NAME[v] then return NAME[v] end
	if t == "function" then
		invoke(v)
		return "fn"
	end
	if t == "table" then
		if d > 4 then return "{...}" end
		local keys = {}
		for k in pairs(v) do table.insert(keys, k) end
		table.sort(keys, function(a, b) return tostring(a) < tostring(b) end)
		local parts = {}
		for _, k in ipairs(keys) do
			table.insert(parts, tostring(k) .. "=" .. show(v[k], d + 1))
		end
		return "{" .. table.concat(parts, ",") .. "}"
	end
	return tostring(v)
end

local function args(...)
	local parts = {}
	for i = 1, select("#", ...) do parts[i] = show((select(i, ...))) end
	return table.concat(parts, ", ")
end

function invoke(f)
	if seen[f] or depth > 12 then return end
	seen[f] = true
	depth += 1
	table.insert(out, "enter fn")
	local ok, err = pcall(f, P("a1"), P("a2"), P("a3"))
	if not ok then table.insert(out, "error " .. tostring(err):gsub("^.-:%d+: ", "")) end
	table.insert(out, "leave fn")
	depth -= 1
end

local function bin(op)
	return function(a, b)
		return P("(" .. show(a) .. op .. show(b) .. ")")
	end
end

function P(name)
	local p = newproxy(true)
	local m = getmetatable(p)
	NAME[p] = name
	m.__index = function(_, k) return P(name .. "." .. tostring(k)) end
	m.__newindex = function(_, k, v) table.insert(out, name .. "." .. tostring(k) .. " = " .. show(v)) end
	m.__call = function(_, ...)
		-- pure functions: a value named by its expression (tidy may hoist or
		-- inline them, which changes how often they run but not the behaviour)
		if name:match("^math%.") or name:match("^string%.") or name == "tonumber" or name == "tostring" then
			return P(name .. "(" .. args(...) .. ")")
		end
		ncall += 1
		local r = "r" .. ncall
		table.insert(out, r .. " = " .. name .. "(" .. args(...) .. ")")
		return P(r)
	end
	m.__add, m.__sub, m.__mul, m.__div = bin("+"), bin("-"), bin("*"), bin("/")
	m.__mod, m.__pow, m.__idiv, m.__concat = bin("%"), bin("^"), bin("//"), bin("..")
	m.__unm = function(a) return P("(-" .. show(a) .. ")") end
	m.__len = function() return 0 end
	m.__lt = function() return true end
	m.__le = function() return true end
	m.__tostring = function() return name end
	return p
end

local function iter(t)
	if type(t) == "table" then return ipairs(t) end
	local i = 0
	return function()
		i += 1
		if i > 1 then return nil end
		return P(show(t) .. "#k"), P(show(t) .. "#v")
	end
end
local ENV = setmetatable({
	ipairs = iter, pairs = function(t) if type(t) == "table" then return pairs(t) end return iter(t) end,
	type = type, typeof = typeof, select = select, next = next, unpack = table.unpack,
}, { __index = function(_, k) return P(k) end, __newindex = function(t, k, v)
	show(v) -- a function value still gets run
	rawset(t, k, v)
end })

local f, err = loadstring(SRC, "=out")
if not f then
	print("COMPILE ERROR " .. tostring(err))
	return
end
setfenv(f, ENV)
local ok, e = pcall(f)
if not ok then table.insert(out, "top error " .. tostring(e):gsub("^.-:%d+: ", "")) end
print(table.concat(out, "\n"))
