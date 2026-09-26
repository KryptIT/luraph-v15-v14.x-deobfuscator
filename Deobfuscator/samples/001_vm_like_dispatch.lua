local program = {
 {"PUSH", 7}, {"PUSH", 6}, {"MUL"}, {"PUSH", 10}, {"SUB"}, {"PUSH", 2}, {"ADD"}
}
local stack = {}
local sp = 0
local handlers = {}
handlers.PUSH = function(ins) sp=sp+1; stack[sp]=ins[2] end
handlers.ADD = function() local b=stack[sp]; sp=sp-1; stack[sp]=stack[sp]+b end
handlers.SUB = function() local b=stack[sp]; sp=sp-1; stack[sp]=stack[sp]-b end
handlers.MUL = function() local b=stack[sp]; sp=sp-1; stack[sp]=stack[sp]*b end
for pc=1,#program do handlers[program[pc][1]](program[pc]) end
assert(sp==1 and stack[1]==34)
return stack[1]