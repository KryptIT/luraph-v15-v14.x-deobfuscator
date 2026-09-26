# deobf: multi-obfuscator Luau deobfuscator (`deobf/`)

> This file is a reference, not a changelog. Keep it clean and lean: record
> only what a future session needs (how things work, facts that are hard to
> rediscover, rules). Replace or delete outdated text; don't append history.
> **Hard limit: 500 lines.** If an edit leaves it 5+ lines over, cut the
> least important part; if under 5 lines over, trimming wording is enough.

Goal: **any protected Roblox script in → its obfuscator detected → readable
deobfuscated Luau out.** Planned front end: a Discord bot (upload a file, get
the deobfuscated file back). The output follows standard Luau conventions,
not the original author's formatting (the bytecode doesn't keep it). It is a
*dynamic* deobfuscator: the protected script runs in the real Luau VM against
a fake Roblox/executor environment. Two kinds of output:

- **Devirtualized**: VM bytecode lifted back to real Luau with control flow,
  locals, closures and untaken branches (needs a per-obfuscator front end).
- **Trace** (`--no-devirt`, the fallback when lifting fails, and the only
  output for unrecognized obfuscators): everything the script does to the
  environment, rendered back as Luau and folded into helpers and loops. Only
  the branches that ran.

## Obfuscators and their notes files

Every obfuscator has a plugin in `deobf/obfuscators/` and its own notes file
in the main folder (samples: `samples/`). **Read that file before working on its plugin or its
samples.** Notes files follow the same rules as this one (reference, not
changelog; **hard limit 500 lines each**). Obfuscator-specific facts go
there, never here; this file only holds what all plugins share.

| Plugin (`--obfuscator`) | Notes | Status |
|---|---|---|
| `luraph_v15` | `LURAPH.md` | Devirtualizer + trace |
| `ironbrew1` | `IRONBREW1.md` | Devirtualizer + trace. Samples: `*-ib1.lua` (all with sources). |
| `generic` | (none) | Fallback for undetected inputs: behaviour trace only. |

## Folder layout

The main folder holds `CLAUDE.md`, one notes file per obfuscator
(`LURAPH.md`, ...), `samples/` and `deobf/`. **All samples live in `samples/`**
(`sourceN.lua` originals + `sourceN-obfuscated.lua`, other test scripts);
sample names in the docs mean `samples/<name>`. Obfuscator-specific extras
sit in the plugin's folder (Luraph's `options.txt`).

- `deobf/deob.py`: CLI. Detects the obfuscator, runs its plugin, writes
  `<input folder>/output/<input file name>` (samples: `samples/output/`).
  Intermediate files go to a temp folder that is deleted; `--debug` writes
  them all to that output folder instead (no result copy).
- Shared, obfuscator-independent modules (`deobf/`):
  - `harness.py`: builds and runs harnesses (luau.exe, long-lived REPL
    `HarnessServer`, Studio `StudioBridge`/`Runner`), Path2D cache, chunks, `same_trace`.
  - `envlog.luau` (+ `roblox_api.luau`, `unicode_data.luau`, `datatypes.luau`): the fake
    environment runtime. Also holds Luraph's capture code (`CHAIN.*`,
    `__PA`/`__PF`/`__SKIPP`), inert unless a plugin's instrumentation uses it.
  - `traceout.py` (header, control-line helpers, `render`), `tidy.py`, `fold.py`,
    `spacing.py`, `lexer.py`: trace output.
  - `ir.py` + `backend.py` + `luasym.py`, `structure.py`, `loops.py`,
    `codegen.py`, `variables.py`, `idioms.py`, `names.py`, `localfuncs.py`:
    the lifter back end (see Lifter back end).
- `deobf/obfuscators/`: `__init__.py` (registry `PLUGINS`, `detect`),
  `base.py` (`Obfuscator`, `Job`), `generic.py`, one package per obfuscator.
- `deobf/research/`: shared check scripts, fingerprint scripts, Path2D data.
- `deobf/bin/`: `luau.exe`, `luau-ast.exe` (downloaded if missing). `luau.exe`
  is **built by `build_luau.py`** (Luau 0.739, vector metatable left writable,
  see Environment fidelity); a downloaded stock one lacks the Vector3 members.
  gcc build uses `-march=native` (faster than the official binary): rebuild
  per machine, or `--portable` for a copy that runs elsewhere (the bot server).

## Usage

```
# from the Decompiler folder
python deobf/deob.py samples/source1-obfuscated.lua  # -> samples/output/source1-obfuscated.lua
python deobf/deob.py <script> --detect           # prints NAME<tab>confidence<tab>label
python deobf/deob.py <script> --obfuscator NAME  # skip detection
python deobf/deob.py <script> --no-devirt        # fast: behaviour trace only
python deobf/deob.py <script> --debug            # all intermediate files in <input folder>/output/
```

- Exit status 0 with a result file, 1 on failure. For the bot: run one
  `deob.py` subprocess per upload (with a timeout, `-o` into a temp folder);
  modules keep global state (Path2D cache, `LAST_RAW`), so don't import and
  call it in a long-lived process.
- Scripts that read settings from `_G`/`getgenv()` or check game state stop
  early (e.g. `kick("You didn't add username or webhook")`). Drive them further
  with `--cfg "prelude=rawset(G,'webhook','x') setprop(game,'PlaceId',123)"`
  (Luau run before the script, untraced; `G`, `genv`, `shared`, `game`, `env`,
  `setprop(proxy, key, value)`) and `--cfg falsy=name1,name2` (calls of those
  method/function names return `false`).
- Path2D answers come from the offline engine model (`envlog.luau`
  `CHAIN.p2d`, bit-exact; `research/path2d/README.md`); "N Path2D answers
  computed by the offline engine model".
- `--studio` (rarely needed) serves each harness on `127.0.0.1:34889` via a
  `*.studio_loader.luau` (MCP `execute_luau`); engine Path2D answers go to
  `<script>.path2d` (preferred offline). **Danger:** an endless-loop tamper
  response freezes Studio: evaluate just the Path2D calls instead.
- Other options (`--raw FILE`, `--keep-harness`, `--input-text`, `--strings`,
  plugin options, ...): `deob.py --help`.
- **PyPy**: inputs over `PYPY_MIN_SIZE` (350 KB) re-exec under PyPy (`pypy3`
  on PATH or winget's `PyPy.PyPy.3.11`). Lifting ~2x faster warm, but JIT
  warmup costs ~4 s: pays off only on big scripts.
- The trace's tidy/fold pass only runs when the trace is written (`--debug`,
  `--no-devirt`, or lifting failed); on a 250k-statement trace it takes
  minutes. `DEOB_PRETIDY=FILE` saves its input.
- `python deobf/names.py file` renames locals in any lifted file.

## Adding an obfuscator

1. Collect samples, ideally with sources (obfuscate your own scripts). Add
   the notes file `<NAME>.md` (samples table, how its VM works, checks) and a
   row in the table above.
2. `deobf/obfuscators/<name>.py` or `<name>/__init__.py`: an `Obfuscator`
   subclass with `name`, `label`, `doc`, `detect(source)` (0..1; cheap:
   header comment, signature strings, VM shape regex; ≥ 0.5 wins over the
   fallback), optional `add_arguments(ap)` (an argparse group; option names
   must not clash with other plugins) and `deobfuscate(job)` returning the
   result file's path. A result file starts with `job.credit_header()`
   (credit line + "-- Detected obfuscation: <label>"). Register it in `obfuscators/__init__.py` `PLUGINS`
   (before `Generic`). Check `deob.py <sample> --detect` on every sample of
   every plugin: no false positives.
3. Start with the trace (copy `generic.py`): `harness.Runner(job).run(source,
   cfg)` gives the rendered trace; `traceout.render` makes it readable. Most
   obfuscators are far less sensitive to the environment than Luraph.
4. Non-VM obfuscators (renaming, string encryption, control-flow mangling):
   trace plus a source-level cleanup pass; no lifter.
5. VM obfuscators: a front end that walks each VM function into
   `[(state key, ir.Node)]` (statements, branch or `ir.Next`/`ir.Ret`
   outcome per instruction) and calls `backend.lower`, then `backend.polish`
   and `backend.finish_text` on the program text. Luraph's `devirt.py` is the
   reference. Instrument closures only with table operations if the VM
   probes stack depth (see Environment fidelity).
6. Plugin-private modules: import them as `obfuscators.<name>.<module>`
   (flat module names would clash between plugins); shared ones flat
   (`import harness`). Scripts inside a plugin put `deobf/` on `sys.path`.
7. **Never drop an existing plugin's speed-up (or fix) to support a new
   obfuscator.** If a shared optimization breaks the new one (e.g. the
   spin watchdog from run 1, the stall timeout, live constant requests),
   make it per-plugin instead: move it into the plugin that needs it, or
   put it behind an option/hook that plugin keeps enabling. Check that the
   old plugin's samples keep their timings (notes file "Timing reference").

## Architecture (shared)

### Trace
- `envlog.luau` is the runtime. Everything Roblox is a proxy (`newP`,
  `INFO[p]`); statements go into blocks (`emit`, `STACK`), callbacks are
  captured (`captureFunction`), the result is rendered at the end.
- `roblox_api.luau` (`gen_roblox.py`, from the Roblox API dump): enums, class
  tree, member kinds with value types (`Health:float`, `Position:Vector3`).
- Loadstring'd code of 4 KB+ is reported (`\0CHUNK`, `harness.take_chunks`);
  a plugin can instrument it and pass it back (`chunks`, `__CHUNKS`) for a rerun.
- UI `Callback` functions in tables run twice: with a truthy stand-in and with
  `false`. The two traces render as `if state then ... else ... end`, shared
  prefix/suffix outside the `if` (`captureFunction`, `rec.alt` in `resolve`).
  The `false` run is kept only when it finishes without errors.
- Caps: 250k statements, 25k per block. Budget abort keeps partial `task.spawn` bodies.

### Folding (helpers and loops)
- Needs proto attribution: `emit` walks the Lua stack (`CHAIN.get`) into
  `stmt.chain = "pid:inv,..."` from hooks a plugin inserted (`__PF` closure ->
  proto, `__PLAST`; Luraph: `LURAPH.md`); `renderBlock` writes `--@<nlines>
  <chain>` markers (not in toggle callbacks). Without hooks there are no
  markers and nothing folds. `--cfg fold=false`: off.
- `fold.py` (called from `tidy`) parses the markers into a statement tree and
  groups runs by chain entry into invocations (`Inv`). Two passes:
  - **helpers**, innermost first: invocations of one proto with the same token
    shape (literals and non-local names may differ) become
    `local function name(params)`. Differing tokens and locals not visible at
    the definition become params; locals used after the call are returned.
    Definitions go at top level before the first top-level statement that
    contains a call, in creation order.
  - **loops**: consecutive same-shape statement groups inside any block become
    `for _, v in ipairs({ rows }) do body end` (most statements covered wins,
    then the shorter period; only when clearly shorter). A local that one
    iteration reads from the previous one (a "selected"/"last" state in the
    original) becomes `local lastX` before the loop, `local previousX = lastX`
    in the body and `lastX = X` at its end.
  - Names: `createX`/`setupX`/`tweenX`/`onX`/`getX`/`destroyX`/`setXProp`;
    params from the property or argument they feed (`fromRGB` -> r, g, b) or
    the shared class of differing instances.
- `tidy.py`: text-only readability pass (preamble strip (Luraph's probe
  block, `traceout.render(preamble=...)`), instance names, fold, parens,
  hoisting, params); folding needs a fresh run's markers.
  Check with `bin/luau-ast.exe file | grep "Parse errors"` (exit code is 0).

### Lifter back end
Front ends produce the IR in `ir.py` (statements `Assign`/`CallStmt`/
`SetList`/`ForPrep`/`Close`, per-instruction `Node` trees, outcomes
`Next`/`Ret`/`Crash`; expressions from `luasym.py`). The back end takes the
IR module as parameter `D`. `backend.lower`: `structure.build_cfg` ->
`merge_equivalent` -> `loops.recognize` -> `codegen.simplify_blocks` ->
`variables.rename` -> child closures -> `structure.structure` -> idioms ->
`variables.declare` -> `codegen.Renderer`. Then `backend.polish` (`names.py`,
`localfuncs.py`) and `backend.finish_text` (`spacing.py`).

- `names.py` (luau-ast based, scope-safe renaming: a generated name is never
  given to a local whose scope overlaps another one with that name, so no
  shadowing; `local f = function` counts from its statement start since
  localfuncs turns it into `local function f`; numbered in declaration
  order; globals are never reused) names from use: `x or default` after `x`,
  `f("RouterClient")` after the string, `require(x:WaitForChild("M"))` ->
  `M`, `t[k](...)` -> `handlers`. `localfuncs.py`: `local f = function` ->
  `local function f`.
- `spacing.py` (last step, final text only): blank lines around multi-line
  statements; guard clauses stay tight. Check scripts must ignore blank lines.
- luau-ast prints decoded string constants as raw bytes: always
  `json.loads(out.decode("latin-1"))`. Its columns are **byte** offsets: text
  rewrites by location (names, localfuncs) must edit the UTF-8 bytes.
- `codegen.quote`: valid UTF-8 is written literally (emoji), invisible code
  points as `\u{XXXX}`, other bytes as `\ddd`. Multi-line printable text
  (2+ newlines, 60+ bytes) becomes a long string `[==[...]==]`; its newlines
  are `codegen.LONG_NL` (U+E000) until `backend.polish`, because nested
  function lines get re-indented. Never write such characters literally
  into repo source (the Edit tool turned `"\u200d"` into a real ZWJ).
- Table constructors: one line if it fits (`TABLE_WIDTH` + indent), else one
  field per line with trailing commas (also any table with a multi-line
  item, except a lone function: `{ function() ... end }`); items render
  with `cur_ind` one tab deeper.
- `idioms.py` passes: `and_or` (also and/or results written over an
  operand's register: Luraph reuses registers), `fold_single_use` (a temp is
  inlined into the next statement when no call runs there before its read,
  its value is dead afterwards (textual order + an in-iteration kill inside
  loops) and no closure names it; runs of temps fold one after another:
  `o:M(g(), {...})`; never function values; `t = {...}; t.k = V` folds into
  the constructor, for V that only became one expression in `and_or`;
  `a, x = f(); y = x` -> `a, y = f()` when x's value is read only there;
  also into `return`, except a call as the last value: it would return all),
  `drop_blank_branches` (branches of blank-line markers only), `while_cond`
  (again after `conditions`), `conditions`, `loop_vars`,
  `strip_trailing_return`; opt-in `inline_const_locals` (IR module flag
  `INLINE_CONST_LOCALS`: literals in registers written once are hoisted
  temps in Luau bytecode). `loops.join_preps`: one prep block when a loop
  header has identical preps in several predecessors.
- Renderer: `0 < x` -> `x > 0`, `x = x + y` -> `x += y` (plain variables),
  `getfenv().name` -> `name`,
  vector constants as float32 shortest decimals / `Vector3.zero`, `1e9`.
- `names.py` also names callback parameters from the signal
  (`SIGNAL_PARAMS`, mirrors envlog's), parameters from the property they set
  (`btn.Text = arg` -> `text`), `"Speed: " .. n` -> `speed`, helpers'
  results from a label argument (`mk(page, "Save Position")` ->
  `savePosition`), `toggleX` / `createX` functions.
- codegen: a value used as a method receiver is inlined even if it contains
  calls (NAMECALL evaluates the object once); the renderer detects the method
  form by rendered text. A closure is never inlined as a callee (no IIFEs).
  A call result is not inlined where it would need truncation parens
  (`f((g()))`: last argument / array item / return value), it stays a local.
  `drop_redundant_stores`: `r = K` when r holds K on every path (not captured).
- `backend.run_big_stack`: a thread with a 256 MB stack for deep recursion.
  Use it for ad-hoc scripts that lift whole programs too.

## Hard-won facts (don't rediscover these)

### Environment fidelity
Luraph keys its decryption on the environment (LURAPH.md), so these rules
hold for every change to the shared runtime:

- **Path2D.** Lengths, positions and tangents are float32 bits. Emulated bit-exactly offline (`CHAIN.p2d` in envlog; the full model is in `research/path2d/README.md`). Constructors record their arguments (`INFO[p].ctor`); `--cfg p2d_check=true` compares the model with recorded answers.
- **Random** is Roblox's real generator (PCG32 XSH-RR, stream increment
  **105**), emulated bit-exactly offline incl. seeding edge cases, userdata
  objects and error messages (see envlog; only range = 2^32−1 differs).
- **Library contents must equal Roblox's** (obfuscators fingerprint them; check with `research/libs_fingerprint.luau`):
  - the local `luau.exe` is newer: `buffer.readinteger/writeinteger` are filtered out;
  - `debug` must include profilebegin/profileend/set/reset/getmemorycategory.
- **Instrumentation must not declare `local`s.** Bigger frames change a stack-overflow depth probe (Luraph mixes the depth into its key). Hooks are table operations only. Verified safe: `__PLAST[...]=__ENT.n` in the entry hook, `__PF[h]=x` and (first closure per proto) `__PK[x]=h` plus the `__PA` `__newindex` array copy in the closure maker, the `debug.info` stack walk in `emit` (harness code on top of the VM frames).
- **Never wrap `getfenv`, `pcall`, `setmetatable`,** or anything a VM calls per instruction: the extra frame breaks the depth probe.
- **Fake C functions** (`nativeFn`) are trampolines whose env is set to the script's globals, because `getfenv(cfunc)` must equal `getfenv(0)`. Keep `debug.info`/`setfenv` out of the trampolines (their stack-level math depends on it).
- **Checks the environment already satisfies:** game/service Name/Parent,
  `tostring(instance)`; a new signal object per index (`==` true, `rawequal`
  false); fresh signal/connection method closures with typed errors; one
  shared Instance method per type and name; `connection.Connected`;
  destroyed instances have `.Parent == nil`; `typeof(Vector3)` is "Vector3".
  - **Vector3 members** (`v:Dot`, `.Magnitude`, `.Unit`, `Lerp`, ...): Roblox's
    engine puts them on the native vector type's metatable. Stock Luau freezes
    that metatable, so `bin/luau.exe` is patched (`build_luau.py`) and envlog
    fills it (Studio-checked errors, fresh `[C]` closure per method index,
    `getmetatable` -> "The metatable is locked"). On a stock build it is skipped.
  - **Datatype models** (`datatypes.luau`): CFrame, Vector2, UDim/UDim2, Rect,
    Ray, NumberRange, Color3, Vector3int16/2int16, Number/ColorSequence(+Keypoint),
    Path2DControlPoint. A datatype proxy built from constant arguments gets a
    model value as its `REALV` twin (`attachReal`), so members, methods,
    operators, `==` and `tostring` give the engine's values (the twin paths
    formerly only ran in Studio). Models raise `UNSUPPORTED` for what they
    don't cover: the proxy stays symbolic. Verified in Studio; rotations from
    angles are ~1 float32 ulp off (engine formula unknown). New type: add it
    there, check values in Studio.
  - Path2D without a curve: `GetControlPoints` (fresh table), `GetMaxControlPoints`
    (100); curve queries on an unparented Path2D raise "Attempting to use
    Path2D with invalid parent".
  - Unknown globals are proxies, except hash-like names (`_<12+ hex digits>`):
    nil (obfuscators' run-once keys).
  - `getgenv()/_G/shared` are real tables (first writes logged via a hidden `__newindex`, `getmetatable` returns nil). Writes to keys that already exist bypass `__newindex`: `CHAIN.syncGenv` diffs a shadow copy before every emitted statement (and at the end) and logs them (`_G.x = false` ... `_G.x = true`).
- **Script-level checks** (not the obfuscator's; diaz.txt, Script42.lua): `isfunctionhooked` must
  return false (a truthy stand-in runs the script's `LPH_CRASH()` spin),
  except for functions the script `hookfunction`ed itself;
  `LogService:GetLogHistory()` returns `{}` (a stand-in entry makes HTTP-spy
  scans `msg:lower():find("http")` fire). A failed check usually ends in a
  silent busy loop, so any stand-in that is "wrong but truthy" shows up as a
  timeout. Values that must be real: `Faces`/`Axes` members, `GetService`
  of an unknown name errors, frame-signal `:Wait()` returns a number,
  `GetSecret` errors, `request(nil)` raises a typed error (probe for "C stack
  overflow"), `Get/SetTeleportSetting` store values, `getrenv()` is Roblox's
  globals (not genv), library tables are frozen (`isreadonly(math)`), `ypcall`.
- **Spin watchdog:** a pure-VM endless loop never returns to the runtime.
  Luraph's driver runs with `--cfg spin=N` from run 1 (`DEOB_SPIN_LATE=1`:
  only after a timeout): dispatch heads count steps (`__SPIN`, table ops + a
  rare call; chunks nobody reported yet are patched in `loadstring`) and N
  idle checks end the run like a budget abort, keeping the trace. While
  a requested constant is decoded (dumpProtos) it applies a time limit
  instead (`CHAIN.decodeUntil`, `--cfg decode_limit`, 10 s): a 200 KB
  loadstring source takes more steps than N checks. A failed decode resets
  `ABORT_REASON`, so it only fails that request.
- **Stall timeout** (`harness.run_once`, all plugins): `checkBudget` and the
  spin watchdog print `\0HB` + 16 KB padding every `CFG.heartbeat` s (stdout
  is block-buffered); no output for `harness.STALL` (20 s) kills the run as
  timed out. Never print inside the `ENVLOG-BEGIN`..`END` block (heartbeat
  is switched off before it). Regexes over the raw output must not crawl the
  one-line `\0PROTOS` JSON (a backtracking `[^\s]*x` pattern hung the driver).
- **Loops around `pcall`** swallow the budget abort; `checkBudget` then yields
  the thread out (`coroutine.yield(ABORT)`, treated as the abort by
  `runInBlock` / the main runner). Else such a loop spins until the timeout.
- **Event handlers run after the main script.** Tamper responses get connected to `DescendantRemoving` etc.; running them at Connect time trips the tamper.

### Payload tracing
- Numeric properties and datatype components (from API types) are plain numbers, because Luau won't compare userdata < number.
- Unknown `.Parent` chains end at workspace → game → nil.
- `next(proxy)` acts like an empty table.
- `pairs()` over a table keyed by proxies runs in address order, which
  differs between processes: `harness.same_trace` (last resort: sorted lines,
  traced local names masked) and `devirt_check` accept the same lines reordered.
- Loops are detected on a flat per-thread statement tape. That handles `for` over proxies left open by `break`: generated loop names and call results are normalized by order, named/indexed proxies by path.

### Lifting (back end, and rules any front end's walk must keep)
- SCCP facts need a real lattice meet: const(true) ⊓ truthy = truthy (an
  equality-only meet leaves opaque predicates undecided, i.e. junk like
  `(nil)(nil)` in the output). Change detection must compare the facts, not
  their count.
- luasym reuses a run's decision for the same condition object or its `not`
  (`c and x or y` tests `c` twice; forking again walks infeasible paths).
- A closure capturing a register by reference reads it through its box when it
  runs: while a register is open (captured, not yet closed by the VM's close
  op), assignments to it must not be inlined away or copy-propagated
  (`codegen.open_registers`, forward dataflow).
- Inlining a call into a later statement must keep evaluation order inside
  that statement too (`call_before`) and must not cross a redefinition of a
  register the call reads.
- A call or `...` used as a single value in the last position of an argument
  list / return / table constructor must be parenthesized (`g((f()))`).
- `for` header expressions are evaluated once, at the loop prep (`ForPrep`
  holding a `LoopExprs` list shared with the header); as header uses they
  would merge the iterator registers with the loop variables. Pure register
  moves in the loop header (`r2 = nil`) run before every header evaluation:
  copy them after the prep and onto every back edge (`_moves_to_latches`).
- Dead multret packs are dropped before folding (`drop_dead_packs`); a pack
  read after it is no longer tracked becomes a real `table.unpack`/`table.move`.
  A long-lived unread pack (entry `r = pack(...)`) killed in a loop splits it into
  two latch copies (raw `C_1()`, `exitTo`): Luraph's `_walk` drops it (`pack_unstable`), restarts.
- Walk nodes are keyed by the state key, so one pc can have copies.
  `structure.merge_equivalent` merges bisimilar raw per-instruction blocks
  (same pc and branch path, same statements as text: IR objects need a
  stable `__repr__`, same successors). Never merge across pcs or twin
  sub-blocks of one instruction.
- Structuring: when a branch has no join (one side returns), both sides keep
  the region's `stop` (else the outer join is emitted inside the branch too).
- A numeric `for` whose body always returns has no back edge: its prep and
  header are one block. It runs at most once, so `loops._run_once_for`
  substitutes the prep values into the header compares (constant bounds:
  a plain jump). Never make it a `for`: the structurer copied a latch-less
  loop ~100k times (27 MB); left alone, the header reads the VM's hidden
  loop slots (`M_1 <= 0`, undefined names).
- Luau's 200-active-locals limit: `variables.limit_locals` -> `fit_locals`:
  small closed `do ... end` segments (`wrap_segments`) when their estimate
  (`dry=True`) fits, else `split_block` (one closed prefix, e.g. a loader and
  the script it runs, with the locals crossing the cut declared in front).
- Structuring heuristics (before any goto rewrite): `break` paths to another
  exit via tail duplication / return-only regions / "same statements as the
  exit"; endless loops join at the first block both branches reach (RPO);
  `stub_follow`, `breaking_region`; ipdom = loop header: `common_join`, else
  `if c then continue end`; `cleanup` drops code after an `if` that always leaves
  and turns `else if c then continue end; R` at a loop body's tail into `elseif not c then R`.
- Goto elimination (`structure.structure`), CFG rewrites then structure
  again: irreducible loops -> node splitting (`make_reducible`); a jump out of
  a loop to another exit -> `exitTo = k break` + dispatch after the loop
  (`unify_exits`); a block reached again -> its region (up to the fork's join)
  copied per extra pred (`split_node`). Last resort: a `state` dispatch loop.
- A register table (`t = {}` + stores) folds into a constructor across pure
  moves; integer keys 1..n become positional items. `fold_tables` repeats
  with copy propagation/simplify until nothing changes: an inner constructor
  sits in a temp register until simplify inlines it into the outer store
  (nested `{ {"PUSH", 7}, ... }`, webhook `embeds = { { ... } }`).
- Nested constructors whose items contain calls can come out split
  (`local t5 = {...}; ... t[1] = t5`): moving an item past a call isn't safe.

## Checks

- **Samples without sources: only when necessary**, i.e. the change can
  plausibly alter them (the feature they exercise, e.g. fetched.lua for
  `LPH_CRASH`/`LPH_JIT`), and only those. A runtime change: trace-only first
  (`--no-devirt`, seconds each). Full runs of the big ones cost minutes each
  (timings in the notes files).
- **After a structure.py change:** `python research/structure_fuzz.py 0 3000`
  (random CFGs: the structured AST must trace like the CFG, no goto left).
- **After a fold.py/tidy.py change:** `python research/fold_check.py <script>
  [deob options]`: one trace with and without folding, both run against a
  logging proxy environment; the logs must be identical (script3: DIFFERENT,
  known).
- **After any lifter change** (back end or a front end):
  - `research/compile_check.py file` (real compiler);
  - `research/scope_check.py file` (lifted locals read as globals; must be 0);
  - `research/active_locals.py file` (must stay < 200);
  - the obfuscator's trace comparison (Luraph: `research/devirt_check.py`,
    `research/regress.py`; LURAPH.md).
- **After a detection/registry change:** `deob.py <file> --detect` on every sample.
- **Last step of every deobfuscator change (mandatory):** run the plain
  `python .\deobf\deob.py samples\<file>` (no flags) on the samples that
  have a source (`001_vm_like_dispatch-obfuscated.lua`;
  ironbrew1: the six `*-ib1.lua`, ~3 min together; and future obfuscators' ones)
  and compare each `samples/output/<file>` with
  its source in `samples/`. This also keeps those outputs up to date for the user.

## Limitations (shared)

- **Trace output lacks untaken branches** (devirtualized output has them).
  Conditions on unknown values follow default guesses: proxies are
  truthy, `<` assumed true, numeric properties 0 or typical values.
- **Remote code isn't followed:** `HttpGet` + `loadstring` is recorded, never fetched.
- Layered protection (one obfuscator's output obfuscated again, or a
  loader that loadstrings another obfuscator's chunk) isn't detected per layer.
- **Path2D model:** assumes an offset-only parent Frame Size (every probe seen);
  a Scale size or unmodelled method prints a warning: then `--studio` once.
- `setmetatable(randomObj, {})` says "got userdata" (Roblox: "got Random"); wrapping `setmetatable` is unsafe.

## Workflow gotchas (for Claude Code in this repo)

- **Known shortcoming + known fix = fix it now.** If you notice a bug, gap or
  missing piece while working and you know how to fix it, fix it in the same
  session (then verify) instead of listing it as "still open" in the final
  answer and waiting to be asked. Only report what genuinely needs the
  user's decision or is too big for the session, and say why.

- **Only general improvements, never fitted to one output.** A new sample
  shows what to fix; the fix must target the underlying pattern (a VM,
  compiler or Luau behaviour, a common scripting idiom), not that file's
  text. Before adding a rule (idioms, renderer, naming, tidy/fold):
  - it must key on structure or semantics, never on the sample's strings,
    names, constants or API choices;
  - it must be correct for every input, or safe when it guesses wrong: a
    naming heuristic that can pick a bad name for other scripts needs a
    tight trigger (e.g. label-like strings only);
  - check it on the other samples, not only the one that prompted it
    (diff old vs new outputs); a rule that helps one file and changes
    nothing or worsens others doesn't stay;
  - if it only helps one kind of script (UI hubs, trade stealers), say so
    in the final answer instead of presenting it as universal.
- **The target is standard, idiomatic Luau, not the original source's
  style.** The samples with sources are ground truth for *behaviour and
  structure* (same logic, control flow, no leftover VM artifacts), not for
  style. Where the author's code is unusual (odd formatting, needless
  parentheses, cramped one-liners, inconsistent naming or casing), the
  output should follow common Luau conventions instead; never add a rule
  just to reproduce such a choice. A diff against the source that is only
  style is not a bug.
- **Patch scripts: always use the Write tool**, never Bash heredocs. Heredocs
  mangle `\\0`/`\\1`/`\\n` (e.g. `\\0` became a NUL byte), turn `\n` inside
  Python string literals into real newlines, and join backslash-continued lines.
- Long devirt runs: run a scratch copy of the code, so repo edits can't change
  modules mid-run (plugins import their lifter lazily, after the trace).
- **Time budget: don't sit waiting on full pipeline runs.** A full run of a
  big script costs 5-15 min (timings: LURAPH.md). Iterate on the smallest
  thing that shows the bug:
  - one `--debug` run saves `*.protos.json` + chunks; then lift offline
    (`devirt.py <src> <protos> --chunk C --raw KEY` / `--lift KEY` / `--all
    OUT`, seconds to ~2 min) as often as needed, no rerun of the script;
  - runtime questions: a kept harness (`--keep-harness`, or build one with
    `harness.build_harness`) run directly under `luau.exe` with a short
    `timeout`, plus table-op hooks in a patched copy of the chunk
    (`__TR` ring, see optrace.py) for ground truth;
  - `--timeout 20` when a first run is known to hang (default 90 s is lost).
  - A full run only to confirm a fix, in the background; do other work
    (docs, next fix) meanwhile and batch the confirmations into one run.
  - If a change makes a run much slower than the notes' timings, find out
    why before going on (e.g. a quadratic resend once turned 94 s into 630 s).
- The Studio harness must not add top-level locals: the run section is the
  function `runMain()` (Studio enforces the 200-local limit, luau.exe does not).
- In `envlog.luau`:
  - `local E = ENV` is defined around line 1500. Functions defined earlier must not reference `E` (use forward locals like `GAMEP`, `WORKSPACEP`, `RANDOM_STATE`). A nil-`E` error inside a traced call gets swallowed by the script's `pcall` and silently changes behaviour.
  - The top-level chunk is at Luau's 200-local limit. Wrap new sections in `do ... end`.
