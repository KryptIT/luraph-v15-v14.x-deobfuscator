-- Reconstructed automatically by deobfuscate.py (LuaObfuscator.com VM)
-- Original local names are not recoverable; locals are named v1, v2, ...

local v1 = 1203456
local v2 = 1230471
local v3 = 8023481

if v1 < v2 then
    print("true")
end

if v2 < 1 + v3 then
    print("obfuscate the conditions!")
end

print("Clicking [Strings] will completely hide this string!")
local v4 = 0
local v5

while true do
    if v4 == 1 then
        for v6, v7 in pairs(v5) do
            if v7 then
                print("Prime found: " .. v6)
            end
        end
        break
    end
    if v4 == 0 then
        local v8 = 0
        while true do
            if v8 == 0 then
                function sieve_of_eratosthenes(v9)
                    local v10 = {}
                    for v11 = 1, v9 do
                        v10[v11] = (v11 ~= 1)
                    end
                    for v12 = 2, math.floor(math.sqrt(v9)) do
                        if v10[v12] then
                            for v13 = v12 * v12, v9, v12 do
                                v10[v13] = false
                            end
                        end
                    end
                    return v10
                end
                v5 = sieve_of_eratosthenes(420)
                v8 = 1
            end
            if v8 == 1 then
                v4 = 1
                break
            end
        end
    end
end

print("How to obfuscate best?")
