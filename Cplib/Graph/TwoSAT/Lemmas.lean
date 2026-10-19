import Cplib.Graph.TwoSAT.Basic
import Mathlib.Tactic

namespace Cplib

namespace TwoSAT

@[simp] theorem solve_empty_zero : (empty 0).solve = some #v[] := by
  native_decide

example :
    let problem := (empty 3)
      |>.addClause 0 true 1 true
      |>.addClause 0 false 2 true
      |>.addClause 1 false 2 false
    problem.solve = some #v[false, true, false] := by
  native_decide

example :
    let problem := (empty 1)
      |>.addClause 0 true 0 true
      |>.addClause 0 false 0 false
    problem.solve = none := by
  native_decide

end TwoSAT

end Cplib
