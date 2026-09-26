-- Deobfuscated by ccjvwsod on Discord
-- Detected obfuscation: Luraph v15
-- Local names are inferred from use (the original names are not in the bytecode)

local tbl = { { "PUSH", 7 }, { "PUSH", 6 }, { "MUL" }, { "PUSH", 10 }, { "SUB" }, { "PUSH", 2 }, { "ADD" } }
local tbl2 = {}
local n = 0

local handlers = {
	PUSH = function(arg)
		n += 1
		tbl2[n] = arg[2]
	end,
	ADD = function()
		local v = tbl2[n]
		n -= 1
		tbl2[n] = tbl2[n] + v
	end,
	SUB = function()
		local v = tbl2[n]
		n -= 1
		tbl2[n] = tbl2[n] - v
	end,
	MUL = function()
		local v = tbl2[n]
		n -= 1
		tbl2[n] = tbl2[n] * v
	end,
}

for i = 1, #tbl do
	handlers[tbl[i][1]](tbl[i])
end

assert(n == 1 and tbl2[1] == 34)
return tbl2[1]
