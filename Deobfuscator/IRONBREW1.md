# ironbrew1 (`deobf/obfuscators/ironbrew1/`)

> Reference, not changelog (same rules as CLAUDE.md). **Hard limit: 500 lines.**

Header `-- this file was generated using ironbrew1`. A modern Luau VM
obfuscator (not the old Lua 5.1 IronBrew). Status: **devirtualizer + trace**.
Build options (all samples: none of them, "level 1" optimization):
Aggressive optimization (SSA optimizer), Intense VM scrambling, VM compression.
Untested: those options (expect new handler shapes; see "Adding support").

## Samples (all with sources; `samples/<name>-ib1.lua`)

| Sample | Source | Result (plain run) |
|---|---|---|
| `001_vm_like_dispatch-ib1.lua` | `001_vm_like_dispatch.lua` | same code as the source, ~8 s |

Check outputs with `research/compile_check.py`, `scope_check.py`,
`active_locals.py` (CLAUDE.md "Checks") and read them against the source.
Behaviour check: trace the obfuscated file and the lifted file (as a plain
script: `--obfuscator generic`), both `--no-fold --no-devirt`, and diff the
statements (numbers/names normalized); `pairs()` order and trace naming
(`v` vs `player`) may differ. A missing callback or loop in the lifted trace is a
lifter bug (found this way: captured locals mixed up with reused registers).

## Pipeline (`__init__.py`)

1. `instrument.py`: the wrapper's closure makers (a function returning the
   interpreter `function(...)` with a `while true do op = code[pc] ...`
   loop, `find_vms`) get `__IBC(mk, params, {[decl location] = local})`
   before the return; every other function expression `__IBF(f, loc)`;
   dispatch loops the spin watchdog hook. Calls only, no locals.
2. One run in the fake environment (`capture.luau` as `--cfg plugin_rt`):
   records each maker call's locals; at the end forces protos that never got
   a closure through the maker, materializes lazily decoded arrays, probes
   the instruction proxies (below) and writes `\0IBDUMP {json}`.
3. `devirt.py` lifts every captured proto (`lift_program`) with the shared
   back end; `forloops.py` rewrites loop shapes and orders branches first. Falls back to the
   trace when there is no dump or lifting raises.

Debug: `deob.py x --debug` keeps `*.ibdump.json`; then offline:
`python -m obfuscators.ironbrew1.devirt <src> <dump> [--raw N | --out F]`
(from `deobf/`, seconds). `DEVIRT_STATS=1` prints walk sizes per function,
`DEVIRT_FACTS=<pc>` the facts at a pc, `DEVIRT_TB=1` tracebacks of
unlifted instructions. `handler.py <src> OP...` prints a handler,
`listing.py <src> <dump> CAP` a proto's instructions.

## How the VM looks

- Outer `return(function(a,...,bg,...) local bh={ints} ...)` called with ~33
  library values; its body is control-flow flattened
  (`while/repeat ... if S == k then ... S, K = f(S, K)`); the VM's helper
  functions too. The interpreter loop itself is **not** flattened: an
  `if op <= N` tree over ~300-1300 opcode numbers.
- Instructions are struct-of-arrays: `code[pc]` (opcode) plus 4-8 operand
  arrays (`qe[pc]`, `qg[pc]`, ...; table-valued operands for fused ops).
  Opcode numbers, operand roles and handler bodies are randomized per build:
  **never key on an opcode number**; everything works on handler source.
- Registers `R = table.create(n)`; argument stack table + top counter
  (`qo`, `qs`); call results through a helper `f(t, ...)` (sets `t`, the
  top local and returns the count: `VMModel.results_fns/results_top`).
- Captured locals are boxes `{v}` made by `R[a] = {R[a]}` (also before the
  local has a value); closures get box refs or plain values.
- Constants decoded at run time by VM bytecode protos (`bn[id](consts, ...)`);
  the dump holds the decoded tables (end of run).
- Micro-op sequences: one source instruction split over several VM
  instructions communicating through interpreter locals (`dd = cl[pc];
  dc[dd] = {dc[dd]}`...): they are the "carried" state.

### Obfuscation inside the bytecode (all handled)

- **Opaque predicates** on fresh tables and VM tables: `t = {}; t[k] = k;
  x = t[k]; if x ~= nil`, VM tables as keys. Resolved by the walk's facts.
- **Junk calls** into VM-runtime protos (`bn[28323168](bz[pc], 4, K)`) and
  VM-table stores. Calls with VM objects are dropped (`call_symbolic`).
- **Environment check** prepended to the main function:
  `ok, a, b = pcall(check)`; the flag it sets corrupts the script
  (`handlers[flag and false or "PUSH"]`). The check proto is the only one
  with **2147483629** among its constants (`CHECK_MODULUS`,
  `Program.check_protos`); the call is dropped and its results taken as
  passing (`CheckResult`): SCCP removes the check and the corruption.
- **Self-modifying jump targets**: a maker local `P` whose `P[pc]` is a
  per-instruction proxy; `P[pc][field] = x` writes an operand array
  (`__newindex`). Used as return addresses: store the continuation into a
  shared jump's operand, jump there. `capture.luau proxies()` probes each
  field key with a sentinel (`"proxies"` in the dump); `InsProxy` redirects
  loads/stores to the operand arrays as path-sensitive facts.
- **Self-modifying opcodes** (`code[pc] = f(pc, op)`) are ordinary VM-table
  stores (facts).
- **Fused instructions**: one handler holds a whole loop
  (`for k, v in R[a], R[a+1], R[a+2] do R[a+3], R[a+4] = k, v; <op> end`,
  counting `while i <= n do ... i = i + s end`) or several ops (closure +
  call). See "Fused loops".
- Constant hoisting: literals loaded into registers once (also passed to
  closures as upvalues). See "Output shaping".

## The lifter (`devirt.py`)

Symbolic execution of the interpreter's own source (luasym) per
instruction, with the dump's values concrete and registers symbolic, as
SCCP over the instruction graph (`Program.walk`): each state is stepped
with the register facts true on all incoming edges (`meet_facts`); a
branch on a symbolic value forks (`Stepper.step`, decision replay).

State (`State`) = pc, carried interpreter locals, carried VM-table contents
(argument stack, results table), boxes, pending multiple result, generic-for
iterators, fused-loop sub-position (`sub`) and VM memory (`_vm_memory`).
Keys must not contain junk that differs per path, or loops never converge:

- **Liveness** (`liveness`, second walk): per pc, carried locals / VM-table
  slots / iterators read before written (`step_reads`) and always written;
  keys keep only what is live at the state's pc. Without it micro-op
  temporaries and dead argument-stack slots split states (rotated loops,
  duplicated code after loops, unstructured jumps).
- Pending call results are keyed by shape (`_multikey`), not temp name.
- Scalars stored in VM tables (`("ovl", tid, key)` facts) are in the key:
  the return-address stores above must stay path-sensitive.
- Carried-local discovery restarts the walk (`new_carry`); the carry sets
  are shared per VM (`Program.carry_of`) so later protos rarely restart.

Values: `Stored` (value parked in a table + its constant), `BoxRef`,
`BoxTable` (`{R[a]}`), `InsProxy`, `CheckResult`, `_Lost` (a register whose
VM value died at a merge: fine to move/park, an error when script code
needs it), `Lin` (count = c + #tail), `Spread`/`SpreadIdx` (a multiple
result in one slot). A known scalar read from a VM table is returned as the
scalar (operands, jump targets must be concrete).

Registers: script `r1..`; `LOC_BASE` 900000 interpreter locals,
`OVL_BASE` 800000 values parked in VM tables, `HLOC_BASE` 700000 handler
locals, `LV_BASE` 600000 fused-loop locals, `BOX_BASE` 500000 captured
locals (boxes), `STACK_BASE*n` stack copies.

### Captured locals (boxes)

`R[a] = {R[a]}` makes a box; the box is an IR variable of its own
(`BOX_BASE + n`, one per creation site (pc, register), `boxvars`), never the
register it was made in: the VM moves boxes between registers and reuses
the register while the box lives on (`R[b] = R[a]; R[a] = self; ...;
R[a] = R[b]` around a method call). Naming a box after its register merged
the reused register into the captured variable (`sig.Connect(flag, ...)`).
Each creation emits `Close(box var)` first: the next loop iteration's local
is a new variable. Box reads/writes (`R[a][1]`) and closure captures
(`MaybeBox`) use the box variable.

### Handler locals (copy on write)

A handler local keeps its value's expression; right before a statement
writes something that expression reads (register, table, upvalue, global;
a call writes tables/globals/upvalues), it is copied into an HLOC register
(`hold`, `_materialize`). Copies nothing reads afterwards are dropped at the
end of the run (`prune_copies`, adjusting decision positions). Big
expressions (loops in handlers) are copied at once (`_mutable_refs` limit).
Without this, `local x = R[a] + R[c]; R[a] = x; if x <= R[b]` compares the
wrong value.

### Fused loops

A `while`/`for`/`for-in` inside a handler whose control depends on script
values (an `Expr`, not operand numbers) is a loop of the output
(`fused_loop`): the run ends at the loop (`LoopSig`) with a state whose
`sub` is the loop's AST location; its runs replay the handler up to the
loop with the output dropped (`loop_head`) and run one iteration. Handler
locals holding script values live in LV registers meanwhile; generic loops
emit the GenIter prep / `ga` call shape directly.

### Other rules worth knowing

- Parameters: the prologue's `R[1..n] = ...` copy is kept as an entry block
  `("E", 0)` (`entry_out`).
- `{R[a]}` with a nil/known table inside is still a box (`BoxTable`).
- The trace run's spin limit grows with the input size (`SPIN_PER_BYTES`):
  the VM decodes string constants with VM bytecode before the script
  starts (reef-ib1's 200 KB constant needed ~48 checks, not 24).
- `(x ~= nil) and (x ~= false)` (the VM's truth test) evaluates to
  `not not x`, conditions decide on `x` (`_truthy_test`).
- `select(SpreadIdx, ...)`, `#extra varargs < 0` clamps (decided "no"),
  results helper persisted into its table (`call_lua_hook`), spread copies
  onto the argument stack get their own `Multi`.
- `#t` of a script table in a register stays `#t` (`IBInterp.unop`).
- By-value captures of known literals: the child gets the literal
  (`UpList.kinds[i] = ("const", v)`); such upvalues are no captures.
- Registers holding a global (`("glob", r)` fact) identify `pcall`.
- Tables built here copy per run with one memo for facts, carried locals
  and VM tables (identity matters: `home_of`).

## `forloops.py` (before `backend.lower`)

Rewrites the walk's loop shapes into what `loops.try_numeric/try_generic`
know (Luraph's pseudo-slot form); matched on IR structure, never opcodes;
all-or-nothing per loop. Back edges by dominance (`Graph.idom`).

- FORPREP/FORLOOP: `R[a] = R[a] - R[a+2]` ... `x = R[a] + R[a+2]; R[a] = x;
  if x <= R[a+1] then R[v] = x`.
- TFORLOOP: `t = R[a](R[a+1], R[a+2]); if t[1] ~= nil then R[a+2..] = t...`.
- Counting `while` (fused numeric loops): `while x <= y do ...; x = x + z end`,
  split into synthetic body/exit nodes.
- `_call_iterators`: a prep whose f, s, ctl are results 1..3 of one call
  (through registers, along a straight path) takes the call
  (`for k in s:gmatch(p)`), dropping the iterator register copies.

## Output shaping (shared back end, opt-in or general)

- `INLINE_CONST_LOCALS` (devirt module flag): `idioms.inline_const_locals`
  inlines locals written once with a number/boolean/short-string literal
  (Luau folds real constant locals itself, so such registers are hoisted
  temps).
- General (all front ends): `getfenv().x` renders as `x`;
  `drop_blank_branches`, `while_cond` again after `conditions`,
  `loops.join_preps` (a loop header reached with identical preps from
  several blocks).
- `forloops.order_branches`: a branch between two instructions puts the
  lower target pc in `then` (the compiler's layout is source order), so
  guard clauses and `if ok then ... return r end return d` come out as
  written. A "short block first" heuristic got reef/soundabuse/something
  wrong; layout is the signal.

## Environment probes (the trace run)

Before the payload the VM checks engine behaviour (a wrong answer ends in
`attempt to index nil with nil`): Path2D (unparented, control points),
`Ray`, `CFrame:PointToWorldSpace`, vector `:Dot`, `Rect`, `NumberRange`, a
hash-like global that must be nil. All answered by the shared runtime
(CLAUDE.md "Environment fidelity"). Other builds may probe datatypes
without a model yet (TweenInfo, Region3, ...): the symptom is a proxy where
a number is expected; add a model in `datatypes.luau`.

## Known gaps

- A few loops stay `while true` + `table.pack(f(s, c))` (a TFORLOOP whose
  entry has two different preps, or iterator copies across branches).
- `localPlayer.WaitForChild(copy, "x")`: a namecall whose receiver copy is
  a separate local is not rendered as a method call.
- Options "Intense VM scrambling" / "VM compression" / "Aggressive
  optimization" are untested (no samples).

## Adding support for a new build

1. `--debug` run; `devirt ... --out` and grep `devirt:` errors (they name
   the function: `function N`); `DEVIRT_TB=1` for the traceback.
2. `handler.py` / `listing.py` (or a disassembler printing operand arrays)
   to see the handler; compare the lifted function with the source.
3. For behaviour questions, log the real pc sequence: patch each dispatch
   loop after its first statement with a table append
   (`__PCL[#__PCL+1] = pc*100000+op`, `instrument.insert_at`), run it with a
   `plugin_rt` that creates `__PCL` and returns it from a `CHAIN.endHooks`
   function, and look for the proto's opcode signature in the sequence
   (protos that never ran don't appear).
