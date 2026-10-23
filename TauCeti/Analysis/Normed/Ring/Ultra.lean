/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Ultra
public import TauCeti.Algebra.Order.BigOperators.ProdSubProd

/-!
# The closed unit ball and products of elements close to one in ultrametric normed rings

An ultrametric seminormed ring is a nonarchimedean topological ring: its open balls about zero
are open additive subgroups. In an ultrametric seminormed ring with `‖1‖ = 1`, the closed unit
ball is an open subring. In an ultrametric normed ring, a finite product of elements each within
`ε ≤ 1` of `1` is again within `ε` of `1`.

Integer casts have norm at most `‖1‖`, without requiring the seminorm to be normalized.

## Main results

* `IsUltrametricDist.nonarchimedeanRing`: an ultrametric seminormed ring is a nonarchimedean
  ring.
* `Subring.unitClosedBall`: the closed unit ball of an ultrametric seminormed ring with
  `‖1‖ = 1`, an open subring.
* `TauCeti.norm_one_sub_of_norm_lt_one`: subtracting an element of norm less than one from one
  leaves the norm equal to one.
* `TauCeti.norm_mul_sub_one_lt` and `TauCeti.norm_prod_sub_one_lt`
* `TauCeti.norm_prod_sub_prod_le`: a uniform perturbation bound for finite products.
-/

public section

/-- Integer casts in an ultrametric seminormed ring have norm at most the norm of one. -/
theorem IsUltrametricDist.norm_intCast_le_norm_one {R : Type*} [SeminormedRing R]
    [IsUltrametricDist R] (z : ℤ) : ‖(z : R)‖ ≤ ‖(1 : R)‖ := by
  simpa using IsUltrametricDist.norm_zsmul_le (1 : R) z

/-- **An ultrametric seminormed ring is a nonarchimedean ring.** This is the ring form of
Mathlib's `IsUltrametricDist.nonarchimedeanAddGroup`: every neighbourhood of zero contains an open
additive subgroup, namely a small open ball. -/
instance IsUltrametricDist.nonarchimedeanRing {R : Type*} [SeminormedRing R]
    [IsUltrametricDist R] : NonarchimedeanRing R where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

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

/-- An element strictly smaller than one does not change the norm of one when subtracted. -/
@[simp]
theorem norm_one_sub_of_norm_lt_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖x‖ < 1) : ‖1 - x‖ = 1 := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
  · simp [hx.le]
  · exact ne_of_gt (by simpa using hx)

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

/-- If two finite families are bounded by `M` and differ by at most `ε` in each coordinate,
their products differ by at most `ε * M ^ (s.card - 1)`. The exponent uses natural subtraction,
so the statement includes the empty product and `M = 0`. -/
theorem norm_prod_sub_prod_le {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] {s : Finset ι} {f g : ι → R} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ M) (hg : ∀ i ∈ s, ‖g i‖ ≤ M)
    (hfg : ∀ i ∈ s, ‖f i - g i‖ ≤ ε) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ε * M ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hε]
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using hfg a (by simp)
    have hprod : ‖∏ i ∈ s, f i‖ ≤ M ^ s.card := by
      calc ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := norm_prod_le_prod_norm s f
        _ ≤ ∏ _i ∈ s, M := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
        _ = M ^ s.card := Finset.prod_const _
    have htail := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      Nat.add_sub_cancel]
    calc ‖f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i‖ =
          ‖(f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)‖ := by
            congr 1
            ring
      _ ≤ max (‖f a - g a‖ * ‖∏ i ∈ s, f i‖)
          (‖g a‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖) :=
        (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le_max (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ max (ε * M ^ s.card) (M * (ε * M ^ (s.card - 1))) :=
        max_le_max (mul_le_mul (hfg a (by simp)) hprod (norm_nonneg _) hε)
          (mul_le_mul (hg a (by simp)) htail (norm_nonneg _) hM)
      _ = ε * M ^ s.card := by
        have hcard : s.card - 1 + 1 = s.card := Nat.sub_add_cancel (Finset.card_pos.mpr hs)
        rw [mul_left_comm M ε, ← pow_succ', hcard, max_self]

end TauCeti
