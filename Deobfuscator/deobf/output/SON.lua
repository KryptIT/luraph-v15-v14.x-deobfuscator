-- Why do i love gpt 5.6 sol high the reason is below.
-- dsc.gg/oxyenv 

if not getgenv().SCRIPT_KEY then
	if not SCRIPT_KEY then
		r = "No script key provided, please pass a SCRIPT_KEY!"
		loadstring(game:HttpGet("https://jnkie.com/sdk/love.lua"))()
		return
	end

	local v = SCRIPT_KEY
	getgenv().SCRIPT_KEY = v
elseif getgenv().EXECUTING == "true" then
	warn("There is already an execution in progress. Please wait before executing another script.")
	return
end

error("devirt: index b'debug' (at 96:18855)")
