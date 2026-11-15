/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.FundamentalGroupCircle

/-!
# Pointwise form of the winding loops of an additive circle

Mathlib's `AddCircle.zsmulLoop p 0 n` is the loop winding `n` times around `AddCircle p`. This file
gives its value at a time `t` as the image of the real number `n * p * t`.
-/

public noncomputable section

namespace AddCircle

variable (p : ℝ)

/-- The loop winding `n` times around `AddCircle p` at time `t` is the image of the real number
`n * p * t`. -/
theorem zsmulLoop_zero_apply_eq_coe (n : ℤ) (t : unitInterval) :
    zsmulLoop p 0 n t = (((n : ℝ) * p * t : ℝ) : AddCircle p) := by
  rw [zsmulLoop_apply, ← coe_zsmul, coe_zero, add_zero, zsmul_eq_mul]
  congr 1
  ring

end AddCircle
