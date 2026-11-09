/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Basic counting lemmas for Dyck steps
-/

public section

namespace List

/-- The numbers of `U` and `D` steps in a list sum to its length. -/
theorem count_U_add_count_D (l : List DyckStep) :
    l.count DyckStep.U + l.count DyckStep.D = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases a <;> simp <;> omega

end List
