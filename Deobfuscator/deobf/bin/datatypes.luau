--!nocheck
-- Offline models of Roblox datatypes that are pure math (bundled into the
-- harness as __ROBLOX.datatypes). envlog.luau attaches a model value as the
-- "real twin" (REALV) of a datatype proxy built from constant arguments, so
-- members, methods and operators give the engine's numbers instead of
-- symbolic expressions (scripts and obfuscators derive values from them).
--
-- Anything a model doesn't implement, or arguments it can't take, raise
-- UNSUPPORTED: envlog then falls back to the symbolic proxy. Real Roblox
-- errors are only raised where Studio was checked.
--
-- CFrame: position + 3x3 rotation, float32 like the engine (stored as native
-- vectors, so the math is float32 per component). Verified against Studio:
-- constructors, tostring, GetComponents, * / + / -, Inverse, the space
-- conversions, Euler/axis-angle getters, Lerp.
local UNSUPPORTED = setmetatable({}, { __tostring = function() return "<datatypes: unsupported>" end })
local function unsupported() error(UNSUPPORTED, 0) end

local vec = vector.create
local vdot, vcross, vnorm, vmag = vector.dot, vector.cross, vector.normalize, vector.magnitude
local fbuf = buffer.create(4)
local function f32(x)
	buffer.writef32(fbuf, 0, x)
	return buffer.readf32(fbuf, 0)
end
local function isVec(v) return type(v) == "vector" end
local function num(v)
	if type(v) == "number" then return v end
	if type(v) == "string" and tonumber(v) then return tonumber(v) end
	return unsupported()
end

-- CFrame values: userdata -> { p = pos, x = col0, y = col1, z = col2 }
local CF = setmetatable({}, { __mode = "k" })
local CFMT = {}
local function make(p, cx, cy, cz)
	local u = newproxy(true)
	local mt = getmetatable(u)
	for k, v in CFMT do mt[k] = v end
	CF[u] = { p = p, x = cx, y = cy, z = cz }
	return u
end
local function get(v)
	local c = CF[v]
	if not c then unsupported() end
	return c
end
local X, Y, Z, O = vec(1, 0, 0), vec(0, 1, 0), vec(0, 0, 1), vec(0, 0, 0)
local IDENTITY = { p = O, x = X, y = Y, z = Z }

-- rotation from rows (row-major components as in GetComponents)
local function fromRows(p, r00, r01, r02, r10, r11, r12, r20, r21, r22)
	return make(p, vec(r00, r10, r20), vec(r01, r11, r21), vec(r02, r12, r22))
end
local function rot(c, v) return c.x * v.x + c.y * v.y + c.z * v.z end
local function rotT(c, v) return vec(vdot(c.x, v), vdot(c.y, v), vdot(c.z, v)) end
local function mul(a, b) return { p = rot(a, b.p) + a.p, x = rot(a, b.x), y = rot(a, b.y), z = rot(a, b.z) } end
local function inverse(c)
	local x = vec(c.x.x, c.y.x, c.z.x)
	local y = vec(c.x.y, c.y.y, c.z.y)
	local z = vec(c.x.z, c.y.z, c.z.z)
	local r = { p = O, x = x, y = y, z = z }
	r.p = -rot(r, c.p)
	return r
end
local function wrap(c) return make(c.p, c.x, c.y, c.z) end

-- rotation matrices (double math, rounded once per component)
local function rx(a)
	local s, c = math.sin(a), math.cos(a)
	return { 1, 0, 0, 0, c, -s, 0, s, c }
end
local function ry(a)
	local s, c = math.sin(a), math.cos(a)
	return { c, 0, s, 0, 1, 0, -s, 0, c }
end
local function rz(a)
	local s, c = math.sin(a), math.cos(a)
	return { c, -s, 0, s, c, 0, 0, 0, 1 }
end
local function mm(a, b)
	local r = {}
	for i = 0, 2 do
		for j = 0, 2 do
			r[i * 3 + j + 1] = a[i * 3 + 1] * b[j + 1] + a[i * 3 + 2] * b[j + 4] + a[i * 3 + 3] * b[j + 7]
		end
	end
	return r
end
local function fromMat(p, m)
	return fromRows(p, m[1], m[2], m[3], m[4], m[5], m[6], m[7], m[8], m[9])
end
local function fromQuat(p, qx, qy, qz, qw)
	local n = qx * qx + qy * qy + qz * qz + qw * qw
	if n == 0 then unsupported() end
	local s = 2 / n
	return fromRows(p,
		1 - s * (qy * qy + qz * qz), s * (qx * qy - qz * qw), s * (qx * qz + qy * qw),
		s * (qx * qy + qz * qw), 1 - s * (qx * qx + qz * qz), s * (qy * qz - qx * qw),
		s * (qx * qz - qy * qw), s * (qy * qz + qx * qw), 1 - s * (qx * qx + qy * qy))
end
local function toQuat(c)
	local m00, m01, m02 = c.x.x, c.y.x, c.z.x
	local m10, m11, m12 = c.x.y, c.y.y, c.z.y
	local m20, m21, m22 = c.x.z, c.y.z, c.z.z
	local tr = m00 + m11 + m22
	if tr > 0 then
		local s = math.sqrt(tr + 1) * 2
		return (m21 - m12) / s, (m02 - m20) / s, (m10 - m01) / s, s / 4
	elseif m00 > m11 and m00 > m22 then
		local s = math.sqrt(1 + m00 - m11 - m22) * 2
		return s / 4, (m01 + m10) / s, (m02 + m20) / s, (m21 - m12) / s
	elseif m11 > m22 then
		local s = math.sqrt(1 + m11 - m00 - m22) * 2
		return (m01 + m10) / s, s / 4, (m12 + m21) / s, (m02 - m20) / s
	end
	local s = math.sqrt(1 + m22 - m00 - m11) * 2
	return (m02 + m20) / s, (m12 + m21) / s, s / 4, (m10 - m01) / s
end
local function lookAt(at, target, up)
	local look = vnorm(target - at)
	local right = vcross(look, up)
	if vmag(right) < 1e-6 then unsupported() end -- the engine's degenerate case isn't modelled
	right = vnorm(right)
	local up2 = vcross(right, look)
	return make(at, right, up2, -look)
end

local lib = {}
function lib.new(...)
	local n = select("#", ...)
	local a = { ... }
	if n == 0 then return wrap(IDENTITY) end
	if n == 1 and isVec(a[1]) then return make(a[1], X, Y, Z) end
	if n == 2 and isVec(a[1]) and isVec(a[2]) then return lookAt(a[1], a[2], Y) end
	if n == 3 then return make(vec(num(a[1]), num(a[2]), num(a[3])), X, Y, Z) end
	if n == 7 then
		return fromQuat(vec(num(a[1]), num(a[2]), num(a[3])), num(a[4]), num(a[5]), num(a[6]), num(a[7]))
	end
	if n == 12 then
		for i = 1, 12 do a[i] = num(a[i]) end
		return fromRows(vec(a[1], a[2], a[3]), a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12])
	end
	return unsupported()
end
function lib.Angles(a, b, c)
	return fromMat(O, mm(mm(rx(num(a or 0)), ry(num(b or 0))), rz(num(c or 0))))
end
lib.fromEulerAnglesXYZ = lib.Angles
function lib.fromEulerAnglesYXZ(a, b, c)
	return fromMat(O, mm(mm(ry(num(b or 0)), rx(num(a or 0))), rz(num(c or 0))))
end
lib.fromOrientation = lib.fromEulerAnglesYXZ
function lib.fromAxisAngle(axis, angle)
	if not isVec(axis) then unsupported() end
	local u = vnorm(axis)
	local h = num(angle) / 2
	local s = math.sin(h)
	return fromQuat(O, u.x * s, u.y * s, u.z * s, math.cos(h))
end
function lib.lookAt(at, target, up)
	if not isVec(at) or not isVec(target) or (up ~= nil and not isVec(up)) then unsupported() end
	return lookAt(at, target, up or Y)
end
function lib.fromMatrix(p, vx, vy, vz)
	if not isVec(p) or not isVec(vx) or not isVec(vy) or (vz ~= nil and not isVec(vz)) then unsupported() end
	return make(p, vx, vy, vz or vnorm(vcross(vx, vy)))
end
lib.identity = wrap(IDENTITY)

local function components(c)
	return c.p.x, c.p.y, c.p.z, c.x.x, c.y.x, c.z.x, c.x.y, c.y.y, c.z.y, c.x.z, c.y.z, c.z.z
end
local function eulerXYZ(c)
	local r02 = math.clamp(c.z.x, -1, 1)
	return f32(math.atan2(-c.z.y, c.z.z)), f32(math.asin(r02)), f32(math.atan2(-c.y.x, c.x.x))
end
local function eulerYXZ(c)
	local r12 = math.clamp(c.z.y, -1, 1)
	return f32(math.asin(-r12)), f32(math.atan2(c.z.x, c.z.z)), f32(math.atan2(c.x.y, c.y.y))
end
local function each(f)
	-- methods taking one or more values and returning one result each
	return function(self, ...)
		local c = get(self)
		local n = select("#", ...)
		if n == 0 then unsupported() end
		local out = { ... }
		for i = 1, n do out[i] = f(c, out[i]) end
		return table.unpack(out, 1, n)
	end
end
local function vecArg(v)
	if not isVec(v) then unsupported() end
	return v
end
local METHODS = {
	Inverse = function(self) return wrap(inverse(get(self))) end,
	GetComponents = function(self) return components(get(self)) end,
	ToWorldSpace = each(function(c, o) return wrap(mul(c, get(o))) end),
	ToObjectSpace = each(function(c, o) return wrap(mul(inverse(c), get(o))) end),
	PointToWorldSpace = each(function(c, v) return rot(c, vecArg(v)) + c.p end),
	PointToObjectSpace = each(function(c, v) return rotT(c, vecArg(v) - c.p) end),
	VectorToWorldSpace = each(function(c, v) return rot(c, vecArg(v)) end),
	VectorToObjectSpace = each(function(c, v) return rotT(c, vecArg(v)) end),
	ToEulerAnglesXYZ = function(self) return eulerXYZ(get(self)) end,
	ToEulerAnglesYXZ = function(self) return eulerYXZ(get(self)) end,
	ToOrientation = function(self) return eulerYXZ(get(self)) end,
	ToAxisAngle = function(self)
		local qx, qy, qz, qw = toQuat(get(self))
		if qw < 0 then qx, qy, qz, qw = -qx, -qy, -qz, -qw end
		local s = math.sqrt(math.max(0, 1 - qw * qw))
		if s < 1e-9 then return X, 0 end
		return vec(qx / s, qy / s, qz / s), f32(2 * math.acos(math.clamp(qw, -1, 1)))
	end,
	Lerp = function(self, other, t)
		local a, b = get(self), get(other)
		t = num(t)
		local ax, ay, az, aw = toQuat(a)
		local bx, by, bz, bw = toQuat(b)
		local d = ax * bx + ay * by + az * bz + aw * bw
		if d < 0 then bx, by, bz, bw, d = -bx, -by, -bz, -bw, -d end
		local wa, wb
		if d > 0.9995 then
			wa, wb = 1 - t, t
		else
			local th = math.acos(d)
			local s = math.sin(th)
			wa, wb = math.sin((1 - t) * th) / s, math.sin(t * th) / s
		end
		local p = a.p + (b.p - a.p) * t
		return fromQuat(p, ax * wa + bx * wb, ay * wa + by * wb, az * wa + bz * wb, aw * wa + bw * wb)
	end,
}
METHODS.components = METHODS.GetComponents
METHODS.inverse = METHODS.Inverse
METHODS.lerp = METHODS.Lerp
METHODS.toWorldSpace = METHODS.ToWorldSpace
METHODS.toObjectSpace = METHODS.ToObjectSpace
METHODS.pointToWorldSpace = METHODS.PointToWorldSpace
METHODS.pointToObjectSpace = METHODS.PointToObjectSpace
METHODS.vectorToWorldSpace = METHODS.VectorToWorldSpace
METHODS.vectorToObjectSpace = METHODS.VectorToObjectSpace
METHODS.toEulerAnglesXYZ = METHODS.ToEulerAnglesXYZ
METHODS.toAxisAngle = METHODS.ToAxisAngle

local PROPS = {
	Position = function(c) return c.p end,
	X = function(c) return c.p.x end,
	Y = function(c) return c.p.y end,
	Z = function(c) return c.p.z end,
	LookVector = function(c) return -c.z end,
	RightVector = function(c) return c.x end,
	UpVector = function(c) return c.y end,
	XVector = function(c) return c.x end,
	YVector = function(c) return c.y end,
	ZVector = function(c) return c.z end,
	Rotation = function(c) return make(O, c.x, c.y, c.z) end,
}
PROPS.p, PROPS.x, PROPS.y, PROPS.z = PROPS.Position, PROPS.X, PROPS.Y, PROPS.Z
PROPS.lookVector, PROPS.rightVector, PROPS.upVector = PROPS.LookVector, PROPS.RightVector, PROPS.UpVector

CFMT.__index = function(self, k)
	local c = get(self)
	local prop = PROPS[k]
	if prop then return prop(c) end
	local m = METHODS[k]
	if m then return m end
	if type(k) == "string" then error(k .. " is not a valid member of CFrame", 0) end
	return unsupported()
end
CFMT.__newindex = function() unsupported() end
CFMT.__mul = function(a, b)
	local c = get(a)
	if isVec(b) then return rot(c, b) + c.p end
	return wrap(mul(c, get(b)))
end
CFMT.__add = function(a, b)
	if not isVec(b) then unsupported() end
	local c = get(a)
	return make(c.p + b, c.x, c.y, c.z)
end
CFMT.__sub = function(a, b)
	if not isVec(b) then unsupported() end
	local c = get(a)
	return make(c.p - b, c.x, c.y, c.z)
end
CFMT.__eq = function(a, b)
	local x, y = CF[a], CF[b]
	return x ~= nil and y ~= nil and x.p == y.p and x.x == y.x and x.y == y.y and x.z == y.z
end
CFMT.__tostring = function(self)
	local t = { components(get(self)) }
	for i = 1, 12 do t[i] = string.format("%.9g", t[i]) end
	return table.concat(t, ", ")
end
CFMT.__metatable = "The metatable is locked"

-- UDim / UDim2 / Path2DControlPoint (verified against Studio: tostring,
-- int32 offsets truncated toward zero, float32 scales, + - unary -, ==,
-- Lerp rounding offsets, the control point's 0/1/3-argument constructor)
local TYPE = setmetatable({}, { __mode = "k" }) -- value -> type name
local VAL = setmetatable({}, { __mode = "k" }) -- value -> fields
local function valueType(name, index, ops)
	local mt = { __metatable = "The metatable is locked" }
	for k, v in ops do mt[k] = v end
	mt.__index = function(self, k)
		local r = index(VAL[self], k)
		if r ~= nil then return r end
		if type(k) == "string" then error(k .. " is not a valid member of " .. name, 0) end
		return unsupported()
	end
	mt.__newindex = function() unsupported() end
	return function(fields)
		local u = newproxy(true)
		local m = getmetatable(u)
		for k, v in mt do m[k] = v end
		TYPE[u], VAL[u] = name, fields
		return u
	end
end
local function field(v, name)
	if TYPE[v] ~= name then unsupported() end
	return VAL[v]
end
local function int32(x)
	x = num(x)
	if x ~= x or x >= 2147483648 or x < -2147483648 then return -2147483648 end
	return x < 0 and math.ceil(x) or math.floor(x)
end

local newUDim
newUDim = valueType("UDim", function(f, k)
	if k == "Scale" then return f.s end
	if k == "Offset" then return f.o end
	return nil
end, {
	__add = function(a, b) local x, y = field(a, "UDim"), field(b, "UDim") return newUDim({ s = f32(x.s + y.s), o = int32(x.o + y.o) }) end,
	__sub = function(a, b) local x, y = field(a, "UDim"), field(b, "UDim") return newUDim({ s = f32(x.s - y.s), o = int32(x.o - y.o) }) end,
	__unm = function(a) local x = field(a, "UDim") return newUDim({ s = -x.s, o = int32(-x.o) }) end,
	__eq = function(a, b) local x, y = VAL[a], VAL[b] return TYPE[a] == TYPE[b] and x.s == y.s and x.o == y.o end,
	__tostring = function(a) local x = VAL[a] return string.format("%.9g, %d", x.s, x.o) end,
})
local function udim(s, o) return newUDim({ s = f32(num(s or 0)), o = int32(o or 0) }) end

local newUDim2
local function udim2Str(f)
	local x, y = VAL[f.x], VAL[f.y]
	return string.format("{%.9g, %d}, {%.9g, %d}", x.s, x.o, y.s, y.o)
end
local function lerpUDim(a, b, t)
	local x, y = VAL[a], VAL[b]
	return newUDim({ s = f32(x.s + (y.s - x.s) * t), o = int32(math.floor(x.o + (y.o - x.o) * t + 0.5)) })
end
newUDim2 = valueType("UDim2", function(f, k)
	if k == "X" or k == "Width" then return f.x end
	if k == "Y" or k == "Height" then return f.y end
	if k == "Lerp" or k == "lerp" then
		return function(self, other, t)
			local a, b = field(self, "UDim2"), field(other, "UDim2")
			t = num(t)
			return newUDim2({ x = lerpUDim(a.x, b.x, t), y = lerpUDim(a.y, b.y, t) })
		end
	end
	return nil
end, {
	__add = function(a, b) local x, y = field(a, "UDim2"), field(b, "UDim2") return newUDim2({ x = x.x + y.x, y = x.y + y.y }) end,
	__sub = function(a, b) local x, y = field(a, "UDim2"), field(b, "UDim2") return newUDim2({ x = x.x - y.x, y = x.y - y.y }) end,
	__unm = function(a) local x = field(a, "UDim2") return newUDim2({ x = -x.x, y = -x.y }) end,
	__eq = function(a, b) return TYPE[a] == TYPE[b] and VAL[a].x == VAL[b].x and VAL[a].y == VAL[b].y end,
	__tostring = function(a) return udim2Str(VAL[a]) end,
})
local UDimLib = { new = function(s, o) return udim(s, o) end }
local UDim2Lib = {}
function UDim2Lib.new(...)
	local n = select("#", ...)
	local a, b, c, d = ...
	if n == 2 and TYPE[a] == "UDim" and TYPE[b] == "UDim" then return newUDim2({ x = a, y = b }) end
	for i = 1, n do
		local v = select(i, ...)
		if v ~= nil and type(v) ~= "number" and not (type(v) == "string" and tonumber(v)) then unsupported() end
	end
	return newUDim2({ x = udim(a, b), y = udim(c, d) })
end
function UDim2Lib.fromScale(x, y) return newUDim2({ x = udim(x, 0), y = udim(y, 0) }) end
function UDim2Lib.fromOffset(x, y) return newUDim2({ x = udim(0, x), y = udim(0, y) }) end

local newCP = valueType("Path2DControlPoint", function(f, k)
	if k == "Position" then return f.p end
	if k == "LeftTangent" then return f.l end
	if k == "RightTangent" then return f.r end
	return nil
end, {
	__eq = function(a, b)
		local x, y = VAL[a], VAL[b]
		return TYPE[a] == TYPE[b] and x.p == y.p and x.l == y.l and x.r == y.r
	end,
	__tostring = function(a)
		local f = VAL[a]
		return string.format("Path2DControlPoint { Position = %s, LeftTangent = %s, RightTangent = %s }",
			udim2Str(VAL[f.p]), udim2Str(VAL[f.l]), udim2Str(VAL[f.r]))
	end,
})
local CPLib = {}
function CPLib.new(...)
	local n = select("#", ...)
	local p, l, r = ...
	local zero = UDim2Lib.new()
	if n == 0 then return newCP({ p = zero, l = zero, r = zero }) end
	if n ~= 1 and n ~= 3 then error("Trying to create a Path2DControlPoint with wrong number of arguments", 0) end
	for i = 1, n do
		if TYPE[(select(i, ...))] ~= "UDim2" then unsupported() end
	end
	return newCP({ p = p, l = l or zero, r = r or zero })
end

-- Vector2 (userdata in Roblox, float32 components: kept as a native vector
-- with z = 0 so the arithmetic is float32), Rect (corners sorted), Ray.
-- Verified against Studio: tostring, operators, members, the methods below.
local newV2
local function v2(v) return newV2({ v = v }) end
local function v2val(v)
	if TYPE[v] ~= "Vector2" then unsupported() end
	return VAL[v].v
end
local function v2arith(op)
	return function(a, b)
		local x = TYPE[a] == "Vector2" and VAL[a].v or (type(a) == "number" and vec(a, a, 0)) or unsupported()
		local y = TYPE[b] == "Vector2" and VAL[b].v or (type(b) == "number" and vec(b, b, 0)) or unsupported()
		local r = op(x, y)
		return v2(vec(r.x, r.y, 0))
	end
end
local V2METHODS = {
	Dot = function(a, b) return vdot(v2val(a), v2val(b)) end,
	Cross = function(a, b) local x, y = v2val(a), v2val(b) return f32(f32(x.x * y.y) - f32(x.y * y.x)) end,
	Lerp = function(a, b, t) local x, y = v2val(a), v2val(b) return v2(x + (y - x) * num(t)) end,
	Abs = function(a) return v2(vector.abs(v2val(a))) end,
	Floor = function(a) return v2(vector.floor(v2val(a))) end,
	Ceil = function(a) return v2(vector.ceil(v2val(a))) end,
	Sign = function(a) return v2(vector.sign(v2val(a))) end,
	Max = function(a, b) return v2(vector.max(v2val(a), v2val(b))) end,
	Min = function(a, b) return v2(vector.min(v2val(a), v2val(b))) end,
	Angle = function(a, b, signed)
		local x, y = v2val(a), v2val(b)
		local ang = math.atan2(math.abs(x.x * y.y - x.y * y.x), x.x * y.x + x.y * y.y)
		if signed and x.x * y.y - x.y * y.x < 0 then ang = -ang end
		return f32(ang)
	end,
}
V2METHODS.lerp = V2METHODS.Lerp
newV2 = valueType("Vector2", function(f, k)
	local v = f.v
	if k == "X" or k == "x" then return v.x end
	if k == "Y" or k == "y" then return v.y end
	if k == "Magnitude" or k == "magnitude" then return vmag(v) end
	if k == "Unit" or k == "unit" then return v2(vnorm(v)) end
	return V2METHODS[k]
end, {
	__add = v2arith(function(a, b) return a + b end),
	__sub = v2arith(function(a, b) return a - b end),
	__mul = v2arith(function(a, b) return a * b end),
	__div = v2arith(function(a, b) return a / b end),
	__idiv = v2arith(function(a, b) return a // b end),
	__unm = function(a) return v2(-v2val(a)) end,
	__eq = function(a, b) return TYPE[a] == TYPE[b] and VAL[a].v == VAL[b].v end,
	__tostring = function(a) local v = VAL[a].v return string.format("%.9g, %.9g", v.x, v.y) end,
})
local V2Lib = {
	new = function(x, y) return v2(vec(num(x or 0), num(y or 0), 0)) end,
	zero = v2(vec(0, 0, 0)),
	one = v2(vec(1, 1, 0)),
	xAxis = v2(vec(1, 0, 0)),
	yAxis = v2(vec(0, 1, 0)),
}

local newRect = valueType("Rect", function(f, k)
	if k == "Min" then return v2(f.lo) end
	if k == "Max" then return v2(f.hi) end
	if k == "Width" then return f.hi.x - f.lo.x end
	if k == "Height" then return f.hi.y - f.lo.y end
	return nil
end, {
	__eq = function(a, b) return TYPE[a] == TYPE[b] and VAL[a].lo == VAL[b].lo and VAL[a].hi == VAL[b].hi end,
	__tostring = function(a)
		local f = VAL[a]
		return string.format("%.9g, %.9g, %.9g, %.9g", f.lo.x, f.lo.y, f.hi.x, f.hi.y)
	end,
})
local RectLib = {}
function RectLib.new(...)
	local n = select("#", ...)
	local a, b, c, d = ...
	local p, q
	if n == 2 then
		p, q = v2val(a), v2val(b)
	elseif n == 0 or n == 4 then
		p, q = vec(num(a or 0), num(b or 0), 0), vec(num(c or 0), num(d or 0), 0)
	else
		return unsupported()
	end
	return newRect({ lo = vector.min(p, q), hi = vector.max(p, q) })
end

local newRay
local function closest(f, p)
	if not isVec(p) then unsupported() end
	local u = vnorm(f.d)
	local t = math.max(0, vdot(p - f.o, u))
	return f.o + u * t
end
newRay = valueType("Ray", function(f, k)
	if k == "Origin" then return f.o end
	if k == "Direction" then return f.d end
	if k == "Unit" then return newRay({ o = f.o, d = vnorm(f.d) }) end
	if k == "ClosestPoint" then return function(self, p) return closest(field(self, "Ray"), p) end end
	if k == "Distance" then return function(self, p) return vmag(p - closest(field(self, "Ray"), p)) end end
	return nil
end, {
	__eq = function(a, b) return TYPE[a] == TYPE[b] and VAL[a].o == VAL[b].o and VAL[a].d == VAL[b].d end,
	__tostring = function(a)
		local f = VAL[a]
		return string.format("{%s}, {%s}", tostring(f.o), tostring(f.d))
	end,
})
local RayLib = {
	new = function(o, d)
		if (o ~= nil and not isVec(o)) or (d ~= nil and not isVec(d)) then unsupported() end
		return newRay({ o = o or O, d = d or O })
	end,
}

-- NumberRange, Color3, Vector3int16/Vector2int16, Number/ColorSequence(Keypoint).
-- tostring uses C++ stream formatting (%g, 6 digits), keypoints and ranges
-- end in a space; float32 fields; int16 wraps around (all as in Studio).
local function g(x) return string.format("%g", x) end
local newNR = valueType("NumberRange", function(f, k)
	if k == "Min" then return f.lo end
	if k == "Max" then return f.hi end
	return nil
end, {
	__eq = function(a, b) return TYPE[a] == TYPE[b] and VAL[a].lo == VAL[b].lo and VAL[a].hi == VAL[b].hi end,
	__tostring = function(a) return g(VAL[a].lo) .. " " .. g(VAL[a].hi) .. " " end,
})
local NRLib = {
	new = function(lo, hi)
		lo = f32(num(lo))
		hi = hi == nil and lo or f32(num(hi))
		if lo > hi then error("NumberRange: invalid range", 0) end
		return newNR({ lo = lo, hi = hi })
	end,
}

local newC3
local function c3(r, g_, b) return newC3({ v = vec(r, g_, b) }) end
local function c3val(c)
	if TYPE[c] ~= "Color3" then unsupported() end
	return VAL[c].v
end
local function toHSV(v)
	local r, gg, b = math.clamp(v.x, 0, 1), math.clamp(v.y, 0, 1), math.clamp(v.z, 0, 1) -- the engine clamps first
	local mx, mn = math.max(r, gg, b), math.min(r, gg, b)
	local d = mx - mn
	local h = 0
	if d ~= 0 then
		if mx == r then
			h = ((gg - b) / d) % 6
		elseif mx == gg then
			h = (b - r) / d + 2
		else
			h = (r - gg) / d + 4
		end
		h /= 6
	end
	return f32(h), f32(mx == 0 and 0 or d / mx), f32(mx)
end
local function byte(x) return math.clamp(math.floor(x * 255 + 0.5), 0, 255) end
local C3METHODS = {
	Lerp = function(a, b, t) local x, y = c3val(a), c3val(b) return newC3({ v = x + (y - x) * num(t) }) end,
	ToHSV = function(a) return toHSV(c3val(a)) end,
	ToHex = function(a) local v = c3val(a) return string.format("%02x%02x%02x", byte(v.x), byte(v.y), byte(v.z)) end,
}
C3METHODS.lerp = C3METHODS.Lerp
newC3 = valueType("Color3", function(f, k)
	if k == "R" or k == "r" then return f.v.x end
	if k == "G" or k == "g" then return f.v.y end
	if k == "B" or k == "b" then return f.v.z end
	return C3METHODS[k]
end, {
	__eq = function(a, b) return TYPE[a] == TYPE[b] and VAL[a].v == VAL[b].v end,
	__tostring = function(a) local v = VAL[a].v return g(v.x) .. ", " .. g(v.y) .. ", " .. g(v.z) end,
})
local function hsv(h, s, v)
	h, s, v = num(h), num(s), num(v)
	h = (h % 1) * 6
	local i = math.floor(h)
	local f = h - i
	local p, q, t = v * (1 - s), v * (1 - s * f), v * (1 - s * (1 - f))
	if i == 0 then return c3(v, t, p) elseif i == 1 then return c3(q, v, p) elseif i == 2 then return c3(p, v, t)
	elseif i == 3 then return c3(p, q, v) elseif i == 4 then return c3(t, p, v) end
	return c3(v, p, q)
end
local C3Lib = {
	new = function(r, g_, b) return c3(num(r or 0), num(g_ or 0), num(b or 0)) end,
	fromRGB = function(r, g_, b) return c3(num(r or 0) / 255, num(g_ or 0) / 255, num(b or 0) / 255) end,
	fromHSV = hsv,
	fromHex = function(s)
		if type(s) ~= "string" then unsupported() end
		local h = string.match(s, "^#?(%x%x%x%x%x%x)$")
		if not h then
			local r, g_, b = string.match(s, "^#?(%x)(%x)(%x)$")
			if not r then unsupported() end
			h = r .. r .. g_ .. g_ .. b .. b
		end
		return c3(tonumber(string.sub(h, 1, 2), 16) / 255, tonumber(string.sub(h, 3, 4), 16) / 255,
			tonumber(string.sub(h, 5, 6), 16) / 255)
	end,
	toHSV = function(c) return toHSV(c3val(c)) end,
}

local function int16(x)
	x = num(x or 0)
	x = x < 0 and math.ceil(x) or math.floor(x)
	return (x + 32768) % 65536 - 32768
end
local function intVector(name, n)
	local new
	local function make(...)
		local t = { ... }
		for i = 1, n do t[i] = int16(t[i]) end
		return new({ c = t })
	end
	local function arith(op)
		return function(a, b)
			if TYPE[a] ~= name or TYPE[b] ~= name then unsupported() end
			local x, y, r = VAL[a].c, VAL[b].c, {}
			for i = 1, n do r[i] = op(x[i], y[i]) end
			return make(table.unpack(r, 1, n))
		end
	end
	local KEYS = { X = 1, Y = 2, Z = n == 3 and 3 or nil, x = 1, y = 2, z = n == 3 and 3 or nil }
	new = valueType(name, function(f, k)
		local i = KEYS[k]
		return i and f.c[i] or nil
	end, {
		__add = arith(function(a, b) return a + b end),
		__sub = arith(function(a, b) return a - b end),
		__mul = arith(function(a, b) return a * b end),
		__div = arith(function(a, b) return a / b end),
		__unm = function(a) local c = VAL[a].c return make(-c[1], -c[2], -(c[3] or 0)) end,
		__eq = function(a, b)
			if TYPE[a] ~= TYPE[b] then return false end
			for i = 1, n do if VAL[a].c[i] ~= VAL[b].c[i] then return false end end
			return true
		end,
		__tostring = function(a) return table.concat(VAL[a].c, ", ", 1, n) end,
	})
	return { new = make }
end

local newNSK = valueType("NumberSequenceKeypoint", function(f, k)
	if k == "Time" then return f.t end
	if k == "Value" then return f.v end
	if k == "Envelope" then return f.e end
	return nil
end, {
	__eq = function(a, b) local x, y = VAL[a], VAL[b] return TYPE[a] == TYPE[b] and x.t == y.t and x.v == y.v and x.e == y.e end,
	__tostring = function(a) local f = VAL[a] return g(f.t) .. " " .. g(f.v) .. " " .. g(f.e) .. " " end,
})
local NSKLib = {
	new = function(t, v, e) return newNSK({ t = f32(num(t)), v = f32(num(v)), e = f32(num(e or 0)) }) end,
}
local newCSK = valueType("ColorSequenceKeypoint", function(f, k)
	if k == "Time" then return f.t end
	if k == "Value" then return f.c end
	return nil
end, {
	__eq = function(a, b) return TYPE[a] == TYPE[b] and VAL[a].t == VAL[b].t and VAL[a].c == VAL[b].c end,
	__tostring = function(a)
		local f = VAL[a]
		local v = VAL[f.c].v
		return g(f.t) .. " " .. g(v.x) .. " " .. g(v.y) .. " " .. g(v.z) .. " 0 "
	end,
})
local CSKLib = {
	new = function(t, c)
		c3val(c)
		return newCSK({ t = f32(num(t)), c = c })
	end,
}
local function sequence(name, kpType, fromValues)
	local new
	new = valueType(name, function(f, k)
		if k == "Keypoints" then return table.clone(f.k) end
		return nil
	end, {
		__eq = function(a, b)
			if TYPE[a] ~= TYPE[b] or #VAL[a].k ~= #VAL[b].k then return false end
			for i, kp in VAL[a].k do if not (kp == VAL[b].k[i]) then return false end end
			return true
		end,
		__tostring = function(a)
			local parts = {}
			for i, kp in VAL[a].k do parts[i] = tostring(kp) end
			return table.concat(parts)
		end,
	})
	return {
		new = function(...)
			local a = ...
			if type(a) == "table" then
				for _, kp in a do if TYPE[kp] ~= kpType then unsupported() end end
				if #a < 2 then unsupported() end
				return new({ k = table.clone(a) })
			end
			return new({ k = fromValues(...) })
		end,
	}
end
local NSLib = sequence("NumberSequence", "NumberSequenceKeypoint", function(a, b)
	b = b == nil and a or b
	return { NSKLib.new(0, a), NSKLib.new(1, b) }
end)
local CSLib = sequence("ColorSequence", "ColorSequenceKeypoint", function(a, b)
	b = b == nil and a or b
	return { CSKLib.new(0, a), CSKLib.new(1, b) }
end)

-- typeof() ignores __type on newproxy userdata: envlog asks here instead
local function typeOf(v)
	if CF[v] then return "CFrame" end
	return TYPE[v]
end

return {
	UNSUPPORTED = UNSUPPORTED,
	typeOf = typeOf,
	CFrame = lib,
	UDim = UDimLib,
	UDim2 = UDim2Lib,
	Path2DControlPoint = CPLib,
	Vector2 = V2Lib,
	Rect = RectLib,
	Ray = RayLib,
	NumberRange = NRLib,
	Color3 = C3Lib,
	Vector3int16 = intVector("Vector3int16", 3),
	Vector2int16 = intVector("Vector2int16", 2),
	NumberSequenceKeypoint = NSKLib,
	ColorSequenceKeypoint = CSKLib,
	NumberSequence = NSLib,
	ColorSequence = CSLib,
}
