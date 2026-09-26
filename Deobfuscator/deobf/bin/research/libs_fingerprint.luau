-- Lists the standard libraries' contents; compare local luau.exe with Studio.
local out = {}
for _, lib in {"string", "table", "math", "bit32", "buffer", "coroutine", "utf8", "os", "debug", "vector"} do
	local t = getfenv(0)[lib]
	local k = {}
	if type(t) == "table" then
		for n in pairs(t) do k[#k + 1] = n end
	end
	table.sort(k)
	out[#out + 1] = lib .. ": " .. table.concat(k, ",")
end
local g = {}
for n in pairs(getfenv(0)) do g[#g + 1] = n end
table.sort(g)
out[#out + 1] = "_G: " .. table.concat(g, ",")
out[#out + 1] = "_VERSION " .. tostring(_VERSION)
local text = table.concat(out, "\n")
print(text)
return text
