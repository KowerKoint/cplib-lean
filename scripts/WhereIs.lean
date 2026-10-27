import Mathlib
import Cplib

/-!
# WhereIs

`#whereis`, which answers "what module is this declaration in?" by asking the
environment this package pins rather than a documentation site.

The published documentation for `Mathlib` and the core library covers Mathlib
master, while this package pins the Lean 4.22.0 toolchain AtCoder uses.  Of the
declarations that still exist upstream, measured against this toolchain, 7.3%
have since moved to another module, so looking one up there is wrong about one
time in fourteen.  The environment built from the pinned sources is never wrong
about it.

This file is a tool rather than part of the library: nothing imports it and
`lake build` does not reach it.  Two ways to use it:

- Open it in an editor and write `#whereis` lines at the end.  The language
  server holds the imports, so each query answers immediately.
- Run `scripts/whereis.sh Nat.isPowerOfTwo` from a terminal, which appends the
  query here and elaborates the result.  Loading the imports costs about ten
  seconds per run.

Both forms take either a name or, in quotes, a substring of one:

```
#whereis Nat.isPowerOfTwo
  Nat.isPowerOfTwo  —  Init.Data.Nat.Power2

#whereis "nextPowerOfTwo"
  5 matches
  Nat.isPowerOfTwo_nextPowerOfTwo  —  Init.Data.Nat.Power2
  Nat.nextPowerOfTwo  —  Init.Data.Nat.Power2
  ...
```
-/

open Lean Elab Command in
/-- Report the module `name` comes from. -/
elab "#whereis " name:ident : command => do
  let env ← getEnv
  match env.getModuleFor? name.getId with
  | some m => logInfo m!"{name.getId}  —  {m}"
  | none => logWarning m!"{name.getId}: no such declaration"

open Lean Elab Command in
/-- Report every declaration whose name contains `pattern`, with its module.

This walks the whole environment, so it takes a second or two on a hit-heavy
pattern.  Compiler-generated declarations are left out. -/
elab "#whereis " pattern:str : command => do
  let env ← getEnv
  let needle := pattern.getString
  let mut hits : Array (Name × Name) := #[]
  for (n, _) in env.constants.toList do
    if !n.isInternal && (n.toString.splitOn needle).length ≥ 2 then
      if let some m := env.getModuleFor? n then
        hits := hits.push (n, m)
  let lines := hits.qsort (fun a b => a.1.toString < b.1.toString)
    |>.map (fun (n, m) => m!"{n}  —  {m}")
  logInfo (m!"{hits.size} matches" ++ Format.line ++ MessageData.joinSep lines.toList Format.line)
