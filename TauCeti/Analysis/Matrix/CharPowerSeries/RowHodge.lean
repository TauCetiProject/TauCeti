/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Face
public import TauCeti.Analysis.Matrix.CharPowerSeries.Rearrangement
public import TauCeti.NumberTheory.NewtonPolygon.GaussNorm
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Row Hodge lower polygons of principal-minor series

Let `r : ι → ℝ` be a bounded row majorant of a square matrix `A`, with
`‖A i j‖ ≤ r i`, and let `r*` be its decreasing rearrangement
(`TauCeti.decreasingRearrangement`). For a base `b > 1`, the *row Hodge polygon*
`TauCeti.rowHodgePolygon b r` is the height sequence

`H n = ∑ k < n, -logb b (r* k)`

on the integers `n` for which `r* 0, …, r* (n - 1)` are positive, and `⊤` elsewhere. Its
finite domain is `[0, m]`, where `m` is the number of positive entries of `r`, possibly
infinite (`TauCeti.rowHodgePolygon_ne_top_iff`), and its slopes `-logb b (r* k)` are
nondecreasing, so it is convex (`TauCeti.isConvexSeq_rowHodgePolygon`).

Fix a real additive valuation `v` on a normed field with `‖x‖ = b ^ (-v x)` for `x ≠ 0`; a
normalisation `‖x‖ = b ^ (-e w x)` with `e > 0` is the case `v = e w`. The coefficient estimate
`‖cₙ‖ ≤ ∏ k < n, r* k` of `Matrix.norm_charCoeff_le_prod_decreasingRearrangement` then says
that the row Hodge polygon lies below every coefficient height of the principal-minor series
`A.charPowerSeries = ∑ cₙ Tⁿ`, and hence below its Newton polygon
(`Matrix.rowHodgePolygon_le_newtonPolygon_charPowerSeries`). Here `cₙ` is `(-1) ^ n` times the
unconditional sum of the size-`n` principal minors (`Matrix.charCoeff`), and the estimates need
no summability. When these families are summable, for instance when `r` tends to zero and the
field is complete (`Matrix.summable_principalMinor`), the series is the Fredholm determinant
`det (1 - T A)`. Beyond `m` the coefficients vanish: for finite `m` the principal-minor series
is a polynomial of degree at most `m`, possibly less. The row
Hodge polygon depends on the chosen coordinates and majorant: it need not have the same right
endpoint as the Newton polygon, and it is not the intrinsic Hodge polygon of a lattice.

A uniform bound `‖A i j‖ ≤ C` gives the line of slope `-logb b C` through the origin below the
Newton polygon (`Matrix.isSupportingLine_newtonPolygon_charPowerSeries`): every finite slope of
the principal-minor series is at least `-logb b C`.

## Main definitions

* `TauCeti.rowHodgePolygon b r`: the row Hodge polygon of the majorant `r` in base `b`.

## Main results

* `TauCeti.isConvexSeq_rowHodgePolygon`, `TauCeti.unitSlope_rowHodgePolygon`: the polygon is
  convex with unit slopes `-logb b (r* k)`.
* `TauCeti.rowHodgePolygon_ne_top_iff`: its finite domain is bounded by the number of positive
  entries of `r`.
* `Matrix.rowHodgePolygon_le_addValuation_charCoeff`,
  `Matrix.rowHodgePolygon_le_newtonPolygon_charPowerSeries`: it lies below the coefficient
  heights and the Newton polygon of the principal-minor series.
* `Matrix.isSupportingLine_newtonPolygon_charPowerSeries`: the slope bound from a uniform bound
  on the entries.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
* K. S. Kedlaya, [*A little p-adic numerical analysis*](https://kskedlaya.org/18.787/numerical.pdf),
  MIT 18.787 notes (2007), §3.
-/

public section

open Finset

namespace TauCeti

variable {ι : Type*} {b : ℝ} {r : ι → ℝ} {n : ℕ}

/-- The **row Hodge polygon** of a row majorant `r` in base `b`: the height
`∑ k < n, -logb b (r* k)` at `n` when the first `n` terms of the decreasing rearrangement `r*`
of `r` are positive, and `⊤` otherwise. -/
noncomputable def rowHodgePolygon (b : ℝ) (r : ι → ℝ) (n : ℕ) : WithTop ℝ :=
  open Classical in
  if ∀ k < n, 0 < decreasingRearrangement r k then
    ((∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k) : ℝ) : WithTop ℝ)
  else ⊤

/-- Where the first `n` rearranged terms are positive, the row Hodge polygon is the sum of the
first `n` slopes `-logb b (r* k)`. -/
theorem rowHodgePolygon_of_forall_lt (h : ∀ k < n, 0 < decreasingRearrangement r k) :
    rowHodgePolygon b r n =
      ((∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k) : ℝ) : WithTop ℝ) := by
  rw [rowHodgePolygon, ite_eq_left h]

/-- The row Hodge polygon is infinite at `n` exactly when one of the first `n` rearranged terms
is not positive. -/
theorem rowHodgePolygon_eq_top_iff :
    rowHodgePolygon b r n = ⊤ ↔ ∃ k < n, decreasingRearrangement r k ≤ 0 := by
  rw [rowHodgePolygon]
  split_ifs with h
  · simpa only [WithTop.coe_ne_top, false_iff, not_exists, not_and, not_le] using h
  · push Not at h
    simpa only [true_iff] using h

@[simp]
theorem rowHodgePolygon_apply_zero : rowHodgePolygon b r 0 = 0 := by
  simp [rowHodgePolygon]

/-- The row Hodge polygon is finite at `n` exactly when `r` has `n` positive entries. Its finite
domain is therefore `[0, m]`, where `m` is the number of positive entries, or all of `ℕ` when
there are infinitely many. -/
theorem rowHodgePolygon_ne_top_iff (hr : BddAbove (Set.range r)) :
    rowHodgePolygon b r n ≠ ⊤ ↔ ∃ s : Finset ι, s.card = n ∧ ∀ i ∈ s, 0 < r i := by
  rw [ne_eq, rowHodgePolygon_eq_top_iff]
  push Not
  rcases n with _ | m
  · exact ⟨fun _ ↦ ⟨∅, by simp⟩, fun _ k hk ↦ absurd hk (Nat.not_lt_zero k)⟩
  rw [← lt_decreasingRearrangement_iff hr le_rfl]
  exact ⟨fun h ↦ h m (Nat.lt_succ_self m), fun h k hk ↦
    h.trans_le (antitone_decreasingRearrangement hr (Nat.le_of_lt_succ hk))⟩

/-- The row Hodge polygon is convex: its slopes `-logb b (r* k)` are nondecreasing because the
rearrangement `r*` is antitone. -/
theorem isConvexSeq_rowHodgePolygon (hb : 1 < b) (hr : BddAbove (Set.range r)) :
    IsConvexSeq (rowHodgePolygon b r) := by
  classical
  set s : Set ℕ := {n | ∀ k < n, 0 < decreasingRearrangement r k}
  have hs : s.OrdConnected := ⟨fun _ _ _ hj _ hl k hk ↦ hj k (hk.trans_le hl.2)⟩
  have heq : rowHodgePolygon b r = fun n ↦ if n ∈ s then
      ((∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k) : ℝ) : WithTop ℝ) else ⊤ := by
    ext1 n
    by_cases h : n ∈ s
    · rw [ite_eq_left h, rowHodgePolygon_of_forall_lt h]
    · rw [ite_eq_right h, rowHodgePolygon_eq_top_iff]
      simpa [s] using h
  rw [heq]
  refine isConvexSeq_ite hs ?_
  intro i hi j hj hij
  simp only [sum_range_succ, add_sub_cancel_left]
  have hpos : 0 < decreasingRearrangement r j := hj.2 j (Nat.lt_succ_self j)
  exact neg_le_neg (Real.logb_le_logb_of_le hb hpos (antitone_decreasingRearrangement hr hij))

/-- The unit slope of the row Hodge polygon at a positive rearranged term `r* n` is
`-logb b (r* n)`. -/
theorem unitSlope_rowHodgePolygon (hr : BddAbove (Set.range r))
    (hn : 0 < decreasingRearrangement r n) :
    unitSlope (rowHodgePolygon b r) n = -Real.logb b (decreasingRearrangement r n) := by
  have h (m : ℕ) (hm : m ≤ n + 1) : ∀ k < m, 0 < decreasingRearrangement r k := fun k hk ↦
    hn.trans_le (antitone_decreasingRearrangement hr (by omega))
  rw [unitSlope_def, rowHodgePolygon_of_forall_lt (h _ le_rfl),
    rowHodgePolygon_of_forall_lt (h _ (Nat.le_succ n)), WithTop.untop₀_coe, WithTop.untop₀_coe,
    sum_range_succ, add_sub_cancel_left]

/-- If every entry of `r` is at most `C`, the line of slope `-logb b C` through the origin lies
below the row Hodge polygon. -/
theorem isSupportingLine_rowHodgePolygon (hb : 1 < b) {C : ℝ} (hC : ∀ i, r i ≤ C) :
    IsSupportingLine (rowHodgePolygon b r) (-Real.logb b C) 0 := by
  rw [isSupportingLine_iff_forall]
  intro n
  by_cases h : ∀ k < n, 0 < decreasingRearrangement r k
  · rw [rowHodgePolygon_of_forall_lt h, zero_add, WithTop.coe_le_coe]
    have hr : BddAbove (Set.range r) := ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩
    have hle (k : ℕ) (hk : k ∈ range n) :
        -Real.logb b C ≤ -Real.logb b (decreasingRearrangement r k) := by
      have hpos := h k (mem_range.mp hk)
      -- a positive rearranged term is witnessed by a positive entry, so `C` is positive too
      obtain ⟨s, hs, hsr⟩ := (lt_decreasingRearrangement_iff hr le_rfl k).mp hpos
      obtain ⟨i, hi⟩ : s.Nonempty := card_pos.mp (by omega)
      exact neg_le_neg (Real.logb_le_logb_of_le hb hpos
        (decreasingRearrangement_le_of_card_le ((hsr i hi).le.trans (hC i)) (s := ∅) (by simp)
          fun i _ ↦ hC i))
    simpa [mul_comm] using card_nsmul_le_sum (range n) _ _ hle
  · push Not at h
    rw [rowHodgePolygon_eq_top_iff.mpr h]
    exact le_top

end TauCeti

namespace Matrix

open TauCeti

variable {ι K : Type*} [DecidableEq ι] [NormedField K] [IsUltrametricDist K]
  {v : AddValuation K (WithTop ℝ)} {b : ℝ} {A : Matrix ι ι K} {r : ι → ℝ}

/-- **The row Hodge polygon lies below the principal-minor coefficients.** Let `v` be a real
additive valuation with `‖x‖ = b ^ (-v x)` for `x ≠ 0`, where `b > 1`. For a bounded row majorant
`‖A i j‖ ≤ r i`, the height of the `n`-th coefficient `A.charCoeff n` of the principal-minor
series, no summability assumed, is at least the row
Hodge polygon at `n`. In particular the coefficient vanishes when `r` has fewer than `n`
positive entries. -/
theorem rowHodgePolygon_le_addValuation_charCoeff (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (hr : BddAbove (Set.range r))
    (hA : ∀ i j, ‖A i j‖ ≤ r i) (n : ℕ) :
    rowHodgePolygon b r n ≤ v (A.charCoeff n) := by
  have hcoeff := norm_charCoeff_le_prod_decreasingRearrangement hr hA n
  by_cases h : ∀ k < n, 0 < decreasingRearrangement r k
  · have key := (PowerSeries.norm_coeff_mul_rpow_pow_le_iff A.charPowerSeries v hb hv n 0
      (∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k))).mp <| by
      rw [Real.rpow_zero, one_pow, mul_one, coeff_charPowerSeries, sum_neg_distrib, neg_neg,
        ← Real.logb_prod _ _ fun k hk ↦ (h k (mem_range.mp hk)).ne',
        Real.rpow_logb (zero_lt_one.trans hb) hb.ne' (prod_pos fun k hk ↦ h k (mem_range.mp hk))]
      exact hcoeff
    rwa [rowHodgePolygon_of_forall_lt h, ← coeff_charPowerSeries, ← add_zero (∑ k ∈ range n, _),
      ← zero_mul (n : ℝ)]
  · obtain ⟨k, hk, hk0⟩ : ∃ k < n, decreasingRearrangement r k = 0 := by
      push Not at h
      obtain ⟨k, hk, hk0⟩ := h
      exact ⟨k, hk, le_antisymm hk0 (decreasingRearrangement_nonneg hr k)⟩
    have hzero : A.charCoeff n = 0 := norm_le_zero_iff.mp <| hcoeff.trans_eq <|
      prod_eq_zero (mem_range.mpr hk) hk0
    simp [hzero]

/-- **Row Hodge lower bound for the principal-minor series.** Let `v` be a real additive
valuation with `‖x‖ = b ^ (-v x)` for `x ≠ 0`, where `b > 1`. For a bounded row majorant
`‖A i j‖ ≤ r i`, the row Hodge polygon of `r` lies below the Newton polygon of the principal-minor
series `A.charPowerSeries`, which is the Fredholm determinant `det (1 - T A)` when its
principal-minor families are summable. -/
theorem rowHodgePolygon_le_newtonPolygon_charPowerSeries (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (hr : BddAbove (Set.range r))
    (hA : ∀ i j, ‖A i j‖ ≤ r i) :
    rowHodgePolygon b r ≤ A.charPowerSeries.newtonPolygon v :=
  PowerSeries.le_newtonPolygon (isConvexSeq_rowHodgePolygon hb hr) fun n ↦ by
    simpa only [coeff_charPowerSeries] using
      rowHodgePolygon_le_addValuation_charCoeff hb hv hr hA n

/-- **Slope bound for the principal-minor series.** Let `v` be a real additive valuation with
`‖x‖ = b ^ (-v x)` for `x ≠ 0`, where `b > 1`. If every entry of `A` has norm at most `C`, the
line of slope `-logb b C` through the origin lies below the Newton polygon of the principal-minor
series `A.charPowerSeries`, which is the Fredholm determinant `det (1 - T A)` when its
principal-minor families are summable. Since that polygon starts at the origin, every finite
slope is at least `-logb b C`. -/
theorem isSupportingLine_newtonPolygon_charPowerSeries (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {C : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ C) :
    IsSupportingLine (A.charPowerSeries.newtonPolygon v) (-Real.logb b C) 0 :=
  isSupportingLine_iff_forall.mpr fun n ↦
    (isSupportingLine_iff_forall.mp (isSupportingLine_rowHodgePolygon hb (r := fun _ : ι ↦ C)
      fun _ ↦ le_rfl) n).trans
    (rowHodgePolygon_le_newtonPolygon_charPowerSeries hb hv
      ⟨C, by rintro _ ⟨i, rfl⟩; exact le_rfl⟩ hA n)

end Matrix
