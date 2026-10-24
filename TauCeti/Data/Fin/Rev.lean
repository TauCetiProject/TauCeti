/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Rev

/-!
# Reversal on `Fin 2`

On `Fin 2` the reversal `Fin.rev` exchanges the two elements, so every index is either a given
index or its reverse: `Fin.fin_two_eq_or_eq_rev`. This is how the two branches of an edge of a
graph, indexed by `Fin 2`, are told apart.
-/

public section

namespace Fin

/-- An index of `Fin 2` is either a given index or its reverse. -/
theorem fin_two_eq_or_eq_rev (i j : Fin 2) : j = i ∨ j = i.rev := by
  revert i j
  decide

end Fin
