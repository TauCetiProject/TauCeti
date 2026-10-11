/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Ultra

/-!
# The closed unit ball and products of elements close to one in ultrametric normed rings

In an ultrametric seminormed ring with `‖1‖ = 1`, the closed unit ball is an open subring. In an
ultrametric normed ring, a finite product of elements each within `ε ≤ 1` of `1` is again
within `ε` of `1`.

## Main results

* `Subring.unitClosedBall`: the closed unit ball of an ultrametric seminormed ring with
  `‖1‖ = 1`, an open subring.
* `TauCeti.norm_mul_sub_one_lt` and `TauCeti.norm_prod_sub_one_lt`
-/

public section

section UnitClosedBall

variable (R : Type*) [SeminormedRing R] [IsUltrametricDist R] [NormOneClass R]

/-- **The closed unit ball of an ultrametric seminormed ring with `‖1‖ = 1` is a subring**: it is
the submonoid `Submonoid.unitClosedBall` and the open additive subgroup
`IsUltrametricDist.closedBall_openAddSubgroup`. -/
def Subring.unitClosedBall : Subring R :=
  { Submonoid.unitClosedBall R,
    (IsUltrametricDist.closedBall_openAddSubgroup R one_pos : AddSubgroup R) with }

variable {R} in
/-- An element lies in the closed unit ball exactly when its norm is at most one. -/
@[simp]
theorem Subring.mem_unitClosedBall {x : R} : x ∈ Subring.unitClosedBall R ↔ ‖x‖ ≤ 1 :=
  Submonoid.mem_unitClosedBall R

/-- The carrier of `Subring.unitClosedBall R` is `Metric.closedBall 0 1`. -/
@[simp]
theorem Subring.coe_unitClosedBall :
    (Subring.unitClosedBall R : Set R) = Metric.closedBall 0 1 := by
  ext
  simp

/-- The closed unit ball of an ultrametric seminormed ring is open. -/
theorem Subring.isOpen_unitClosedBall : IsOpen (Subring.unitClosedBall R : Set R) :=
  (IsUltrametricDist.closedBall_openAddSubgroup R one_pos).isOpen'

end UnitClosedBall

namespace TauCeti

/-- In an ultrametric normed ring, if `a` and `b` are both within `ε ≤ 1` of `1`, so is
`a * b`. -/
theorem norm_mul_sub_one_lt {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {a b : R} {ε : ℝ} (hε : ε ≤ 1) (ha : ‖a - 1‖ < ε)
    (hb : ‖b - 1‖ < ε) : ‖a * b - 1‖ < ε := by
  have hnorm : ‖a‖ ≤ 1 := by
    simpa [ha.le.trans hε] using IsUltrametricDist.norm_add_one_le_max_norm_one (a - 1)
  calc ‖a * b - 1‖ = ‖a * (b - 1) + (a - 1)‖ := by
        rw [mul_sub, mul_one, sub_add_sub_cancel]
    _ ≤ max ‖a * (b - 1)‖ ‖a - 1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ < ε := max_lt ((norm_mul_le _ _).trans_lt
      ((mul_le_of_le_one_left (norm_nonneg _) hnorm).trans_lt hb)) ha

/-- In an ultrametric normed commutative ring, a finite product of elements each within
`ε ≤ 1` of `1` is again within `ε` of `1` (for `0 < ε`). -/
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
