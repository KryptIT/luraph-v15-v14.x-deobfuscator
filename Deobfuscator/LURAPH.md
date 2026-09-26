# Luraph v15 (`deobf/obfuscators/luraph_v15/`)

> Obfuscator notes for the Luraph v15 plugin. Same rules as CLAUDE.md: a
> reference, not a changelog; **hard limit 500 lines**.

The plugin devirtualizes: the VM bytecode is lifted back to real Luau with
control flow, locals, closures and untaken branches. When lifting fails (or
with `--no-devirt`) the result is the behaviour trace.

- `__init__.py`: `LuraphV15` (detect: the `Luraph Obfuscator v15` header,
  else the `return setmetatable({[n]=bit32.x,...` VM-object shape = 0.8;
  options `--no-hooks`, `--max-runs`, `--devirt-rounds`).
- `driver.py`: pipeline (`patch_entries`, trap/chunk reruns, `devirtualize`
  constant rounds, long-lived harness).
- `devirt.py` (front end: VMModel, ProtoLifter, Stepper, `Program._walk`,
  Dump, requests; uses `ir.py` + `backend.lower`), `vmmap.py` (static VM map).
- `optrace.py`, `probes/_*.py`: VM-level research helpers.
- `options.txt` (in this plugin's folder): Luraph's obfuscation options with their
  descriptions (to guess which option produced an unfamiliar VM shape).

## Samples (regression reference)

All in `samples/` (sources next to their obfuscated files).

With sources (ground truth for devirt readability).

| Sample | Trace | Devirtualized |
|---|---|---|
| `001_vm_like_dispatch-obfuscated.lua` (`001_vm_like_dispatch.lua`, options unknown) | Only Luraph's probes: the script is pure math + `assert`. | Stack machine (program table, PUSH/ADD/SUB/MUL handlers, `assert(sp==1 and stack[1]==34)`, returns 34). 5 functions, fully lifted, same structure as the source; only names differ (`tbl`/`tbl2`/`n` for program/stack/sp). Dispatch goes through VM-object methods (`K:A(...)`) and handlers load script globals directly (`R[a] = assert`, what Hardcode Globals describes). devirt_check can't compare it (no traced effects); run the lifted file instead (prints 34). |

## Usage notes

- Devirtualization asks the harness for new constants up to `--devirt-rounds`
  times (stops when none turn up) to decode code that never ran. The
  payload is written as top-level code; Luraph's loader VM is skipped
  (`DEVIRT_LOADERS=1` lifts every VM as `vm_root_<pid>` functions). Devirt exceptions fall back to the trace.
- Devirt debug CLI: `python obfuscators/luraph_v15/devirt.py <src>
  <protos.json> [--chunk FILE]` with `--all OUT` (no runtime), `--raw KEY`
  (instructions), `--op KEY MODE:PC` (handler + operands), `--lift KEY` (KEY =
  pid or "t<tableid>"). `DEVIRT_DEBUG=1`: `-- proto KEY` per function, each
  unstructured jump explained (`DEVIRT_BLOCKS=1`: + block graph);
  `DEVIRT_NO_NAMES=1` keeps register names.
- Env vars: `DEVIRT_REQS=1` each round's new request paths,
  `DEVIRT_ERRS=1` walk errors, `DEVIRT_TIMING=1`, `DEOB_NO_SERVE=1` (fresh
  run per round), `DEOB_NO_FETCH=1` (no live requests),
  `DEVIRT_TB=1`, `DEVIRT_FULL_ROUNDS=1`.
- `--debug` files: `*.deobf.luau` (trace), `*.devirt.luau`, `*.protos.json`,
  `*.chunk_<key>.luau`, `*.strings.txt` (`research/regress.py` and
  `research/devirt_check.py` need these).

## Pipeline (`driver.py`)

- Adds VM entry hooks to the source (`patch_entries`, via `vmmap.py` + `bin/luau-ast.exe`).
- Reruns when a loadstring'd VM chunk shows up (`\0CHUNK`, instrumented and
  passed back via `__CHUNKS`), or when an anti-tamper trap is attributed
  (`\0TRIGGER n`, that proto is skipped via `__SKIPP`).
- A trap that is the script's own `LPH_CRASH()` (license/hook checks):
  skipping it makes the rerun record fewer statements, so the driver keeps
  the trapped run and un-skips the pid.
- **Proto attribution** (feeds the trace's fold pass): `patch_entries`
  inserts `__PF[h]=x` after each `S,h=n,function(...)...end` in the closure
  maker (closure -> proto); the entry hook sets `__PLAST[pid]=__ENT.n`.
  envlog's `emit` turns them into `stmt.chain` / `--@` markers (CLAUDE.md, Folding).

## Devirtualizer

The script's main proto becomes top-level code: the proto the bootstrap root
(pid 1) called last, unless the root emitted statements itself after it (a
probe helper) (`CHAIN.rootCallee` -> `root_callee` in the dump,
`devirt._vm_roots`). Fallback: root of the VM whose first closure was made
**last**. The IR and everything after the walk are shared (`ir.py`,
`backend.lower`, CLAUDE.md).

- **Capture** (`driver.patch_entries` + `envlog.luau` `CHAIN.dumpProtos`):
  at the closure maker, `__PA[proto]` records (once per proto, table ops only)
  the maker-level locals the VM closure uses, plus `__seq` and `__maker`
  (`<chunk_key of the unpatched source>@line,col`). The dumper serializes
  everything reachable (JSON line `\0PROTOS`). For loadstring'd chunks
  the driver writes the original source to `<out>.chunk_<key>.luau` (needed to lift).
- **Closure makers differ** (`vmmap._maker_params`): `function(e, proto,
  upvals)`, `function(g, d, d, d, d, j)` (repeated names, only the last is
  visible) or `function(v,R,R,R,g,g)`. The proto is the parameter indexed
  through itself (`P[P[k]]`), else the one with the most constant-key indexes;
  the upvalue list is the first other visible parameter used (`maker_info`).
  Hooks and `__PF` are keyed by the proto parameter (`pf_key`), never param 1
  (can be the upvalue list: all protos in one pid).
  The VM object's capture name varies (`e`, `V`, `g`): use `maker.args[0]`.
  Positional functions in the VM object constructor must be bound too.
- **Several VM implementations**: a closure op picks the child's maker via
  the VM object (`g[C[C[4]]](g, upvals, C)`), so script protos can run on
  different interpreters (fetched.lua: A = bootstrap + main script, B/C for
  some functions). `VMModel.siblings`; `ClosureExpr.vm` carries the child's
  VM (walks: `ent["child_vms"]`). Each closure then gets `setfenv(f, getfenv())`.
- **Frame captures**: `s[k]=s` puts the register frame in a register
  (`jvals[k] = FRAME`, no statement); closures capture it by value and read
  `upv[i][r]` (`FrameProxy` -> `Upval((i, r))`). `FunctionLifter.frame_regs`
  pre-walks the child to find which parent registers it uses (`frame_regs`
  count as captured/open registers).
- **Luraph macros in the script source** (not options):
  - `LPH_CRASH()` expands to code that stores the VM's own proto table in a
    register, scrambles it with bit32 ops and spins forever. The lifter
    raises `VMCrash` when `value_of` sees `self.proto`; the path ends as
    `Crash` -> block kind `crash` -> `SCrash` (terminal, renders
    `LPH_CRASH()`). The scrambled arrays are those of the proto it ran in:
    the harness copies every proto's number arrays when its first closure is
    made (`__PA` `__newindex`), and `CHAIN.unscramble` puts them back before
    the dump ("N function(s) scrambled") when every entry changed, or ≥90%
    with ≥80% of the new values random words ≥ 2^24 (Script42: 37 of 31792
    entries equal by chance; a proto that ran to the end has ~all entries
    legitimately decoded, but to small values).
    - A restored proto's lazy constants decoded at run time stay valid for
      the operand the lifter decodes (each instruction decodes once): the
      dump lists them as `"late"` keys, `Dump.late` answers them.
    - VM-wide data held by a proto field (Script42: `n = {[5] = buffer,
      [6] = offsets}`, regions XOR-decrypted by an op that then becomes a
      no-op) no longer matches restored protos. Restored protos ≥ live ran
      protos (by size, per holding table): the whole VM goes back to its
      pre-run state; else each restored proto gets a private pristine copy
      (fetched.lua: its `LPH_JIT` code needs the live data).
  - `LPH_ENCSTR` strings: each use makes a closure of one decryptor proto and
    calls it with constants and the caller's register frame (`FrameArg`); it
    stores the plaintext into a caller register. `frame_call` (SCCP) has the
    runtime run it (request `!<proto path>!<args>`, envlog `callPath`, closure
    `__PK[proto]`); `apply_frame_calls` puts in the register writes.
  - `LPH_ENCFUNC`: the payload calls a Luraph runtime closure from the VM
    object (dump `{"lf":n,"pf":proto}`) with the server's key and the
    encrypted function (`buffer.fromstring`), then wraps the returned proto
    (`vmobj[P[P[4]]]` -> `RuntimeMaker`). Stub `luraph_runtimeN` (`SharedFn`).
  - `LPH_ENCNUM(n)`: constant arithmetic/bit32 ops assembling an IEEE double.
    `call_builtin` emits real `bit32.*` calls for symbolic arguments;
    `codegen.fold_constants` folds arithmetic, `bit32.*` on constant ints and
    `table.pack(c)[1]` (extra `simplify_blocks` rounds while it progresses).
  - `LPH_JIT` functions are VM-object methods `function(g,ups,P) local
    W=P[P[8]]; return function(...) <prologue> while c do <if tree on a state
    variable> end end`: plain Lua. `JitModel` (a sibling maker) + `JitStepper`
    lift it as a one-mode VM: a step is one pass of the loop, the pc is the
    state variable, locals live across steps are registers (`_jit_live_in`;
    fixed values like the env stay values). The loop stack local
    (`N = {..., N, ...}`, link slot varies) is a `JitFrame` chain in the
    state, slots `Pseudo("JIT<slot>", depth)`; `_jit_forloop` rewrites the
    header into the VM's FORLOOP shape for `loops.try_numeric`. Closures made
    inside are nested `JitModel`s (`JitProto`: env + outer locals as
    upvalues). Multiple assignments snapshot values (`parallel_values`),
    table constructors stay one expression (`S.NewTable(items)`).
  - Trivial functions compiled to plain Lua (Script42: a closure op whose
    maker is `function() return function() return {} end end`): a
    self-contained `LuaFunc` becomes its source text
    (`ProtoLifter.plain_function_text`, `Opaque`).
  - A lift with ≥50 `(nil)(` calls (≥1% of lines) misread the VM: the driver
    writes the trace instead.
- **Globals in handlers** (Hardcode Globals: diaz.txt, 001): `global_value`
  resolves the VM's library globals (bit32, string, table, ...) to builtins;
  any other global a handler reads (`R[a] = assert`) lifts as `Global(name)`,
  a store (`deepcopy = R[a]`) via `set_global`. A library table/builtin as a
  register value (`R[a] = string`) renders as its name (`library_name`, `as_expr`).
- **Constant rounds** (`driver.devirtualize`): lift, collect requests, get a
  new dump for `force_req` (+ `force_buf`), repeat until no new requests.
  Each round reveals the next nesting level of never-run closures.
  - **Live requests** (`Dump.fetch` -> envlog `CHAIN.fetch`): while the
    long-lived harness made the current dump, a walk gets a missing constant
    right away, so a chain (each constant needed to find the next) takes one
    round. The session keeps the dump's table ids (answers: value + new
    tables only; a new `Dump`'s first request is prefixed `*` and gets every
    table made since the dump, else the final lift misses those sent to the
    round's reader: `KeyError`); decoder side effects stay until the next dump restores the
    snapshot (`CHAIN.fetchEnd`). String patches stay applied: only new ones
    are sent (`PatchLog`, `"+..."`); small requests go inline (~1 ms).
  - **Long-lived harness** (`harness.HarnessServer`, envlog `CHAIN.serve`):
    luau.exe's REPL `require`s the harness once, `__S("", "", "start")` runs
    the script (not inside `require`: a C call deeper, which a coroutine
    inherits; Script42's 197 nested `coroutine.wrap`s then overflow), then
    each round sends a one-line call (`req_N.luau`) to redo the dump. Stdout is block-buffered:
    16 KB padding follows `\0ENVLOG-END`; read raw chunks, never lines, and
    synchronously (a reader thread cost ~12 ms per round trip under PyPy). The
    served trace must match the main run's (`same_trace`), else a fresh run
    per round (`DEOB_SERVE_DIFF=1` writes both).
  - Intermediate rounds only walk (`devirt.collect_requests`, no
    structuring) and reuse unchanged protos' walks (`WalkCache`, keyed by
    table path, resolved by `PathResolver`: shortest paths flip on ties). One
    full `lift_program` at the fixed point; new requests or patches there make
    the remaining rounds full lifts (`devirt.same_patches` compares patches).
  - Request paths: `seq,name,key,...`; a step `slot@v` decodes that lazy slot
    as if its operand (`arr[0][slot]`) were `v` (decrypted by the lifter).
    `@` may appear at any step: child protos of never-run code exist only as
    such results, and their constants are requested through them
    (`105,U,13@2578,25,12@1`).
  - Request walks (`lf.walk_only`, `_walk_one`) don't stop at a constant that
    isn't decoded yet: closure op / index / call through one give a
    `Missing(None)`; a branch on one stops the path (forking walks into junk).
    They stop after `WALK_MAX_ERRORS` (100) error nodes.
  - `Dump.same_operand`: operand `v` indexes the constant pool of the table's
    decoder (`__index`, shared per VM implementation; dumped as `"mtf"`). A
    scalar or flat table (upvalue descriptor `{3, 184}`) decoded for `v` by a
    table with the same decoder answers a request without a round. Keying by
    `__maker` is wrong (fetched.lua: 225 conflicts). Don't enumerate the pool
    in the harness: some `v` hang the decoder.
- **Harness side of requests** (envlog dumper): snapshot every table/buffer
  reachable from the captures, apply `force_buf`, decode (memoizing every `@`
  prefix: a second decode of a child proto gives garbage), restore the
  snapshot and re-insert only the requested constants (else decoder side
  effects reach the dump and the next round decrypts twice).
- Long constants: Luraph's decoder builds them in VM code (a 200 KB
  string is well over the spin watchdog's 24 x 2^20 steps), so request
  decoding runs under a time limit instead (CLAUDE.md, Spin watchdog). Symptom
  before that: `nil --[[ constant not decoded ]]`; `--cfg force_debug=true`
  prints failing `@` steps.
- **String decryption patches** (`force_buf`): string-decrypt instructions XOR
  the shared offset table and string pool (proto `self`[k] -> {[5]=buffer,
  [6]=offsets}); for never-run code the lifter sends its decrypted bytes
  (`devirt.buffer_patches`). Long values go via `--cfg KEY=@file:PATH`.
- Speed: `devirt.analyze_source` caches the per-source analysis (luau-ast
  parse, dispatchers, makers, VMModels) by text, so constant rounds only
  re-read the dump. `iter_nodes` must stay iterative (a recursive generator
  costs half the lift time). Avoid nested whole-VM `iter_nodes` scans
  (quadratic).

## Environment facts specific to Luraph

Luraph mixes much more than Path2D into its stage keys. **Any** divergence
from real Roblox gives a wrong key. Symptoms: `invalid argument #1 to 'band'`,
`buffer.create size out of range`, or "anti-tamper triggered" right after the
Path2D block (after `ScreenGui:Destroy()`). The shared rules this imposes on
envlog.luau (entry hooks without locals, never wrap `getfenv`/`pcall`, ...)
are in CLAUDE.md, Environment fidelity. The trace's `tidy.strip_preamble`
removes Luraph's Path2D/Folder probe block at the top.

## Luraph v15 VM
- **Luraph drops a boolean local's store** when the local is compared and then
  only branched on: `local x = a == true; if x then` becomes a bare compare-and-jump
  (no `x = ...` anywhere), so a closure capturing `x` sees whatever its register
  held before (soundabuse: `Enum.TextXAlignment.Left`). Checked at runtime (forced
  `MuteSounds = false` config: the obfuscated script still mutes). A faithful lift
  shows the same; don't "fix" it in the lifter.
- Usually two VM implementations: the payload and Luraph's bootstrap (~28
  protos; computed jumps `pc = r9 + 1`); fetched.lua has three, bootstrap and
  main script sharing one. With a loadstring'd chunk the VMs live in the
  chunk (`__maker` tag is `chunk_key@line,col`).
- Usually 4 dispatch loops per VM, one per mode (`if k==93 then while ...`,
  or a boolean local `local a = Yd==95`, `Stepper.conds`), each with its own
  opcode array and randomized handlers; modes only switch forward. Loop heads
  `(local )op(,x)*=ARR[pc];`: regexes patching heads must accept all forms
  (a missed head leaves whole modes unmodelled).
- Luraph emits only the opcodes a script uses: a tiny payload can have a
  single mode, and then the dispatch `while` sits directly in the loop
  function without a mode `if` (`Stepper`: `mode_decl = None`, mode 0).
- Handlers can be VM-object methods called from a comparison tree
  (`V,J,i,... = K:A(B,u,e,...); continue`, 001_vm_like_dispatch).
- **Stack VM** (Script42's third VM): the registers are an operand stack,
  `R[M]` with the stack pointer `M` a local of the loop function (`local
  M,O=G` in the prologue, G = frame size), reset by every step unless carried:
  `Stepper.carry` = prologue locals a handler reads before writing, some
  handler writes, and handlers use directly as a register index
  (`_stack_pointer_candidates`); their values are part of the state
  (`State.locs`), `lf.stack_base` = the initial value. Jumps and mode
  switches pop a pushed target (`push 4411; jmp hub; hub: c=R[M]; M-=1`):
  such slots become jump registers when first seen (all found in one walk,
  one restart; `WALK_RESTARTS`), but their assignments stay (the slots hold
  data too) and a value leaves the state once read or above the stack top.
  Guards: ≤ `MAX_STACK_DEPTHS` depths per pc except at pop-and-jump hubs (a
  path whose stack grows each round is infeasible); a function past
  `STACK_WALK_MAX` states falls back to the old walk (proto 350: subroutine
  returns inlined per call site). Registers < 1 are rejected (`Unsupported`).
- **Register-resident arrays**: Luraph can keep a local array in registers
  and index it as `R[base + R[x]]` (fetched.lua's RC4: two 256-entry S-boxes
  at registers 6 and 262). `ProtoLifter.reg_array` lifts each base as a table
  `Reg(REG_ARRAY + base)`, declared `{}` at the proto's entry.
- Lazy instruction decoders: a handler may rewrite its own operands/opcode and
  `pc -= 1` (re-dispatch); the lifter's Stepper re-steps such instructions.
- **Layered in-place decryption**: per mode two decryptor kinds (range XOR of
  the next N instructions' operands; string decrypt in a buffer), NOPs after
  running. Up to 16 XOR layers per slot; they commute and dominate the slot,
  so ONE overlay per proto (visiting order) is correct. Junk code must never
  run (it would corrupt layers) -> SCCP.
- Control flow is flattened through a jump register (`r135 = target; goto
  dispatcher; pc = r135 + 1`): handled as "jump registers" carried in the
  state and dropped once consumed (their assignments are marked `.jump`).
- Opaque predicates: `if r9` repeated inside the else of `if r9`, `if 110 <
  r55` with constant registers, compares of never-assigned registers.
- Multret values live in registers as `table.pack(...)` ("packs"), shifted in
  place by call ops; tracked like jump registers.
- Upvalues: boxes `{[4]=registers,[7]=index}` (read as `box[a][box[b]]`),
  by-value entries, parent pass-through, frame captures. Open boxes table
  `N` ("sink": `MaybeBox`), op 92 closes; the VM iterates it via an alias or
  directly (`for q in next, S`, fetched.lua). A missed sink makes open
  captures look like live frame slots: the local merges with later uses of
  its register. The for-loop state stack (`K={...,[7]=K}`) may link
  through a copy (`ad=K; K={[7]=ad,...}`, `_find_state_vars` alias).
- Ground truth: `python obfuscators/luraph_v15/optrace.py <script> --last N
  [--cfg ...]` prints the last N executed instructions (`loop:arr:pc:op`);
  compare with `DEVIRT_TB=1 python obfuscators/luraph_v15/devirt.py <src>
  <protos> --raw KEY` (the opcode the lifter executed per pc, tracebacks,
  overlay values). `--op KEY MODE:PC:OP` shows the handler of a decrypted opcode.

## Checks (in addition to CLAUDE.md's)

- `python research/regress.py OUTDIR` runs compile/scope/active_locals/
  devirt_check at once (lifts from the saved `*.protos.json` in
  `research/samples/` if present, `samples/` and `output/`, no constant rounds). Needs
  `--debug` runs first.
- `research/devirt_check.py <script> <script>.devirt.luau [--keep DIR]`:
  runs the lifted file (`--obfuscator luraph_v15 --no-hooks`) and the
  obfuscated script (`--no-devirt`) in the same harness and diffs the traces
  (names/numbers/error positions/GetService order normalized, blank lines
  ignored). Covers executed paths only; Luraph's probes show up as
  obfuscated-only lines.
- Readability: compare `output/sourceN-obfuscated.lua` with `samples/sourceN.lua`.

## Debugging a sample that fails

1. `--cfg ptrace=true --raw out.txt` (add `--max-runs 1` to see the trapped
   run) gives a safe proxy-level trace (`[index]`, `[call]` with a string 2nd
   argument, `[eq]`, `[typeof]`, `[tostring]`, `[debug.info]`,
   `[unknown-global]`). Look at the last lines before the failure. `--strings
   --debug` shows the script's decrypted strings (error messages reveal its
   own checks).
   - `--cfg getlog=true` logs global reads but **changes the key**: orientation only.
   - `trace=true` / `probe=true` wrap library functions, which also perturbs the key.
2. Suspect a global? Write a fingerprint script like
   `research/fingerprint_random.luau` (plain Luau, prints probe results). Run
   it through `deob.py` offline and with `--studio`, then diff the `print(...)` lines.
3. Wrong trap attribution (skipping #N kills the script at statement 1): the
   trap isn't really that function. Find the real environment divergence instead of skipping.
4. Unfamiliar VM shape? Check `options.txt` for the option that could cause it.
5. Other `--cfg` options: `debug_loops`, `debug_stack`, `debug_tamper`,
   `print_tail=N` (Studio output size), `fake_random=true` (emulated Random
   in Studio), `random_probe`, `inline_probe`/`oplog` (+
   `probes/_probe_inline.py`, `vmmap.py` for VM-level work).

## Limitations

- **Luraph options:** confirmed: none, Intense VM Structure (same VM shape, more jump-hub flattening, same output). Hardcode Globals is handled; VM Compression
  (double-obfuscated) is out of scope. A script that fails the same way in
  real Studio without the harness is not an environment problem.
- Other Luraph versions: detect() gives them 0.3 (below the 0.5 threshold,
  so they get the generic trace); nothing has been tested.
- Without the long-lived harness, constant rounds converge one nesting
  level per round. Loader VM roots can't be lifted (`storing a non-empty VM
  table into a register`).
