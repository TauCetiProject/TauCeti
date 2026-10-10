/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# The unit interval inside the nonnegative reals

Two facts about `unitInterval.toNNReal : I → ℝ≥0`, the inclusion of the unit interval into the
nonnegative reals: its values are at most one, and clamping a nonnegative real `t` to the unit
interval with `Set.projIcc` and reading it back in `ℝ≥0` gives `min t 1`.  They let paths
parametrized by the unit interval be reparametrized by a nonnegative time, as in
`TauCeti.Topology.PathSpace.Moore.Comparison`.
-/

public section

open scoped NNReal
open Set

namespace unitInterval

theorem toNNReal_le_one (s : I) : toNNReal s ≤ 1 :=
  NNReal.coe_le_coe.1 s.2.2

/-- Clamping a nonnegative real to the unit interval, read back in `ℝ≥0`, is `min t 1`. -/
theorem toNNReal_projIcc (t : ℝ≥0) : toNNReal (projIcc 0 1 zero_le_one t) = min t 1 := by
  rcases le_total t 1 with ht | ht
  · rw [min_eq_left ht, projIcc_of_mem zero_le_one ⟨NNReal.coe_nonneg t, by exact_mod_cast ht⟩]
    rfl
  · rw [min_eq_right ht, projIcc_of_right_le zero_le_one (by exact_mod_cast ht)]
    rfl

end unitInterval
