/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Elements of infinite order on a circle

On the circle `AddCircle p = ℝ / pℤ`, `p > 0`, the class of `t : ℝ` has infinite additive order
exactly when `t / p` is irrational. This combines Mathlib's two characterizations of dense
multiples, `AddCircle.denseRange_zsmul_iff` (by infinite order) and
`AddCircle.denseRange_zsmul_coe_iff` (by irrationality).

## Main results

* `AddCircle.addOrderOf_coe_eq_zero_iff`: the class of `t` has infinite order exactly when `t / p`
  is irrational.
-/

public section

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

/-- The class of `t : ℝ` in `AddCircle p` has infinite additive order exactly when `t / p` is
irrational. -/
theorem addOrderOf_coe_eq_zero_iff {t : ℝ} :
    addOrderOf (t : AddCircle p) = 0 ↔ Irrational (t / p) := by
  rw [← denseRange_zsmul_iff, denseRange_zsmul_coe_iff]

end AddCircle
