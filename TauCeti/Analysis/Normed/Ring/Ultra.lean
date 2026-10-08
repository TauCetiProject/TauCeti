/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Products of elements close to one in ultrametric normed rings

In an ultrametric normed commutative ring, a finite product of elements each within `ε ≤ 1` of
`1` is again within `ε` of `1`.

## Main results

* `TauCeti.norm_mul_sub_one_lt` and `TauCeti.norm_prod_sub_one_lt`
-/

public section

namespace TauCeti

/-- In an ultrametric normed ring, if `a` and `b` are both within `ε ≤ 1` of `1`, so is
`a * b`. -/
theorem norm_mul_sub_one_lt {F : Type*} [SeminormedRing F] [IsUltrametricDist F] {a b : F}
    {ε : ℝ} (hε : ε ≤ 1) (ha : ‖a - 1‖ < ε) (hb : ‖b - 1‖ < ε) : ‖a * b - 1‖ < ε := by
  have hab : ‖(a - 1) * (b - 1)‖ < ε :=
    (norm_mul_le _ _).trans_lt (by nlinarith [norm_nonneg (a - 1), norm_nonneg (b - 1)])
  calc ‖a * b - 1‖ = ‖((a - 1) * (b - 1) + (a - 1)) + (b - 1)‖ := by
        simp only [sub_mul, mul_sub, one_mul, mul_one]; abel_nf
    _ ≤ max ‖(a - 1) * (b - 1) + (a - 1)‖ ‖b - 1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max (max ‖(a - 1) * (b - 1)‖ ‖a - 1‖) ‖b - 1‖ :=
      max_le_max_right _ (IsUltrametricDist.norm_add_le_max _ _)
    _ < ε := max_lt (max_lt hab ha) hb

/-- In an ultrametric normed commutative ring, a finite product of elements each within `ε ≤ 1`
of `1` is again within `ε` of `1` (for `0 < ε`). -/
theorem norm_prod_sub_one_lt {ι F : Type*} [SeminormedCommRing F] [IsUltrametricDist F]
    (s : Finset ι) (f : ι → F) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hf : ∀ i ∈ s, ‖f i - 1‖ < ε) : ‖∏ i ∈ s, f i - 1‖ < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hε0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact norm_mul_sub_one_lt hε (hf j (Finset.mem_insert_self j s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

end TauCeti
