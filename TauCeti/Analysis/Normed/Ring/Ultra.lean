/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Ultra

/-!
# Products of elements close to one in ultrametric normed rings

In an ultrametric seminormed ring with `‖1‖ = 1`, a finite product of elements each within
`ε ≤ 1` of `1` is again within `ε` of `1`. This is how one compares a product of conjugates
with the product of their approximations, for instance a norm `N_{K/ℚ}(Y) = ∏ φ(Y)` in `ℚ̄_p`.

## Main results

* `TauCeti.norm_mul_sub_one_lt` and `TauCeti.norm_prod_sub_one_lt`
-/

public section

namespace TauCeti

/-- In an ultrametric seminormed ring with `‖1‖ = 1`, if `a` and `b` are both within `ε ≤ 1` of
`1`, so is `a * b`. -/
theorem norm_mul_sub_one_lt {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {a b : R} {ε : ℝ} (hε : ε ≤ 1) (ha : ‖a - 1‖ < ε)
    (hb : ‖b - 1‖ < ε) : ‖a * b - 1‖ < ε := by
  have hnorm : ‖a‖ ≤ 1 := by
    calc ‖a‖ = ‖(a - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ max ‖a - 1‖ ‖(1 : R)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (by linarith) norm_one.le
  calc ‖a * b - 1‖ = ‖a * (b - 1) + (a - 1)‖ := by rw [mul_sub, mul_one, sub_add_sub_cancel]
    _ ≤ max ‖a * (b - 1)‖ ‖a - 1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ < ε := by
      refine max_lt ?_ ha
      calc ‖a * (b - 1)‖ ≤ ‖a‖ * ‖b - 1‖ := norm_mul_le _ _
        _ ≤ 1 * ‖b - 1‖ := by gcongr
        _ < ε := by rwa [one_mul]

/-- In an ultrametric seminormed commutative ring with `‖1‖ = 1`, a finite product of elements
each within `ε ≤ 1` of `1` is again within `ε` of `1` (for `0 < ε`). -/
theorem norm_prod_sub_one_lt {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] (s : Finset ι) (f : ι → R) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hf : ∀ i ∈ s, ‖f i - 1‖ < ε) : ‖∏ i ∈ s, f i - 1‖ < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hε0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact norm_mul_sub_one_lt hε (hf j (Finset.mem_insert_self j s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

end TauCeti
