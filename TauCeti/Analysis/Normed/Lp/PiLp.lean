/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Comparing the `ℓ^p` and sup distances on a finite product

The coordinate map `WithLp.ofLp : PiLp p β → (Π i, β i)` to the product with the sup distance is
`1`-Lipschitz for every exponent `1 ≤ p ≤ ∞`, and for `p = 2` its inverse is `√n`-Lipschitz, where
`n` is the number of factors. These are Mathlib's `PiLp.lipschitzWith_ofLp` and
`PiLp.lipschitzWith_toLp` written as inequalities between distances, with the constant
`n ^ (1 / 2)` of the second simplified to `√n`.

## Main statements

* `PiLp.dist_ofLp_le` — `dist (ofLp x) (ofLp y) ≤ dist x y`.
* `PiLp.dist_le_sqrt_card_mul_dist_ofLp` — `dist x y ≤ √n * dist (ofLp x) (ofLp y)` for `p = 2`.
-/

public section

open WithLp

namespace PiLp

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)]

/-- The coordinate map from `PiLp p β` to the product with the sup distance is `1`-Lipschitz. -/
theorem dist_ofLp_le {p : ENNReal} [Fact (1 ≤ p)] (x y : PiLp p β) :
    dist (ofLp x) (ofLp y) ≤ dist x y := by
  simpa using (lipschitzWith_ofLp p β).dist_le_mul x y

/-- The inverse of the coordinate map from `PiLp 2 β` to the product with the sup distance is
`√n`-Lipschitz, where `n` is the number of factors. -/
theorem dist_le_sqrt_card_mul_dist_ofLp (x y : PiLp 2 β) :
    dist x y ≤ √(Fintype.card ι) * dist (ofLp x) (ofLp y) := by
  have h := (lipschitzWith_toLp 2 β).dist_le_mul (ofLp x) (ofLp y)
  simp only [toLp_ofLp, NNReal.coe_rpow, NNReal.coe_natCast] at h
  convert h using 2
  rw [Real.sqrt_eq_rpow]
  norm_num

end PiLp
