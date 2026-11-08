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
nonnegative reals: its values are at most one, and clamping a real `t` to the unit interval with
`Set.projIcc` and reading it back in `ℝ≥0` gives `min t.toNNReal 1` (so `min t 1` for `t : ℝ≥0`).
They let paths parametrized by the unit interval be reparametrized by a nonnegative time, as in
`TauCeti.Topology.PathSpace.Moore.Comparison.Basic`.
-/

public section

open scoped NNReal
open Set

namespace unitInterval

/-- The inclusion of the unit interval into `ℝ≥0` takes values at most one. -/
theorem toNNReal_le_one (s : I) : toNNReal s ≤ 1 :=
  NNReal.coe_le_one.1 (le_one s)

/-- Clamping a real `t` to the unit interval, read back in `ℝ≥0`, is `min t.toNNReal 1`. -/
theorem toNNReal_projIcc (t : ℝ) :
    toNNReal (projIcc 0 1 zero_le_one t) = min t.toNNReal 1 := by
  ext
  simp only [coe_toNNReal, coe_projIcc, NNReal.coe_min, Real.coe_toNNReal', NNReal.coe_one]
  grind

end unitInterval
