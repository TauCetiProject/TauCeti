/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.Rearrangement
public import TauCeti.NumberTheory.NewtonPolygon.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The row Hodge lower polygon of a Fredholm series

Let `A` be a matrix over an ultrametric seminormed commutative ring, on an arbitrary index type,
with a bounded row majorant `‖A i j‖ ≤ r i`, and let `r*` be the decreasing rearrangement of `r`
(`TauCeti.decreasingRearrangement`). Fix a real additive valuation `v` and a base `b > 1` with
`‖x‖ = b ^ (-v x)` for `x ≠ 0`. The **row Hodge heights** of `r` (`TauCeti.rowHodgeHeights`) are

`H n = ∑_{k < n} -logb b r*ₖ` if `r*ₖ > 0` for every `k < n`, and `H n = ⊤` otherwise.

Their weights `-logb b r*ₖ` are nondecreasing, so `H` is a convex height sequence. If exactly `m`
entries of `r` are positive, `H` is finite exactly on `[0, m]`; with infinitely many positive
entries it is finite everywhere.

The coefficient estimate `‖cₙ‖ ≤ ∏_{k < n} r*ₖ` for `det (1 - T A) = ∑ cₙ Tⁿ`
(`Matrix.norm_charCoeff_le_prod_decreasingRearrangement`) says exactly that `H n ≤ v cₙ`, so `H`
lies below the Newton polygon of `det (1 - T A)`. The finite domain of the Newton polygon is then
contained in that of `H`, but need not equal it: the determinant may have fewer finite slopes
than there are positive row bounds. The polygon `H` depends on the chosen coordinates and
majorant, and it is not the Hodge polygon of a lattice. Since every weight is at least
`-logb b r*₀`, a uniform bound `‖A i j‖ ≤ B` forces every finite slope of the Newton polygon to be
at least `-logb b B`.

## Main definitions

* `TauCeti.rowHodgeHeights b r`: the row Hodge heights of a row majorant `r` in base `b`.

## Main results

* `TauCeti.isConvexSeq_rowHodgeHeights`: the row Hodge heights are convex.
* `TauCeti.rowHodgeHeights_ne_top_iff_le_card`, `TauCeti.rowHodgeHeights_ne_top_of_infinite`:
  their finite domain is `[0, m]` for `m` positive entries, and everything for infinitely many.
* `Matrix.rowHodgeHeights_le_addValuation_charCoeff`: `H n ≤ v cₙ`.
* `Matrix.rowHodgeHeights_le_newtonPolygon_charPowerSeries`: the row Hodge heights lie below the
  Newton polygon of `det (1 - T A)`.
* `Matrix.neg_logb_le_unitSlope_newtonPolygon_charPowerSeries`: for `‖A i j‖ ≤ B`, every finite
  slope of that Newton polygon is at least `-logb b B`.

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

/-- The **row Hodge heights** of a row majorant `r` in base `b`. With `r*` the decreasing
rearrangement of `r`, the height at `n` is `∑_{k < n} -logb b r*ₖ` when the first `n` rearranged
terms are positive, and `⊤` otherwise. -/
noncomputable def rowHodgeHeights (b : ℝ) (r : ι → ℝ) (n : ℕ) : WithTop ℝ :=
  if ∀ k < n, 0 < decreasingRearrangement r k then
    ((∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k) : ℝ) : WithTop ℝ)
  else ⊤

/-- The row Hodge height at `n` when the first `n` rearranged terms are positive. -/
theorem rowHodgeHeights_of_forall_pos (h : ∀ k < n, 0 < decreasingRearrangement r k) :
    rowHodgeHeights b r n =
      ((∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k) : ℝ) : WithTop ℝ) :=
  ite_eq_left h

/-- A row Hodge height is finite exactly when the first `n` rearranged terms are positive. -/
theorem rowHodgeHeights_ne_top_iff :
    rowHodgeHeights b r n ≠ ⊤ ↔ ∀ k < n, 0 < decreasingRearrangement r k := by
  by_cases h : ∀ k < n, 0 < decreasingRearrangement r k
  · simpa [rowHodgeHeights_of_forall_pos h] using h
  · simp [rowHodgeHeights, h]

/-- The row Hodge heights start at `(0, 0)`. -/
@[simp]
theorem rowHodgeHeights_zero : rowHodgeHeights b r 0 = 0 := by
  simp [rowHodgeHeights_of_forall_pos (fun k hk ↦ absurd hk (Nat.not_lt_zero k))]

/-- If exactly `m` entries of `r` are positive, the row Hodge heights are finite exactly on
`[0, m]`. -/
theorem rowHodgeHeights_ne_top_iff_le_card (hfin : {i | 0 < r i}.Finite) :
    rowHodgeHeights b r n ≠ ⊤ ↔ n ≤ hfin.toFinset.card := by
  have hset := setOf_lt_decreasingRearrangement le_rfl hfin
  rw [rowHodgeHeights_ne_top_iff]
  refine ⟨fun h ↦ not_lt.mp fun hlt ↦ ?_, fun h k hk ↦ ?_⟩
  · have hmem : hfin.toFinset.card ∈ {k | 0 < decreasingRearrangement r k} := h _ hlt
    simp [hset] at hmem
  · have hmem : k ∈ Set.Iio hfin.toFinset.card := Set.mem_Iio.mpr (hk.trans_le h)
    rw [← hset] at hmem
    exact hmem

/-- If infinitely many entries of a bounded `r` are positive, every row Hodge height is finite. -/
theorem rowHodgeHeights_ne_top_of_infinite (hr : BddAbove (Set.range r))
    (hinf : {i | 0 < r i}.Infinite) (n : ℕ) : rowHodgeHeights b r n ≠ ⊤ := by
  refine rowHodgeHeights_ne_top_iff.mpr fun k _ ↦ ?_
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq (k + 1)
  exact (lt_decreasingRearrangement_iff hr le_rfl k).mpr ⟨s, hcard, fun i hi ↦ hs hi⟩

/-- On a finite unit edge `[n, n + 1]`, the row Hodge slope is `-logb b r*ₙ`. -/
theorem unitSlope_rowHodgeHeights (hr : BddAbove (Set.range r))
    (hn : 0 < decreasingRearrangement r n) :
    unitSlope (rowHodgeHeights b r) n = -Real.logb b (decreasingRearrangement r n) := by
  have hpos : ∀ k < n + 1, 0 < decreasingRearrangement r k := fun k hk ↦
    hn.trans_le (antitone_decreasingRearrangement hr (Nat.le_of_lt_succ hk))
  rw [unitSlope_def, rowHodgeHeights_of_forall_pos hpos,
    rowHodgeHeights_of_forall_pos fun k hk ↦ hpos k (hk.trans n.lt_succ_self),
    WithTop.untop₀_coe, WithTop.untop₀_coe, sum_range_succ, add_sub_cancel_left]

/-- For a base `b > 1`, the row Hodge heights of a bounded majorant form a convex sequence: their
weights `-logb b r*ₖ` are nondecreasing because `r*` is antitone. -/
theorem isConvexSeq_rowHodgeHeights (hb : 1 < b) (hr : BddAbove (Set.range r)) :
    IsConvexSeq (rowHodgeHeights b r) := by
  refine isConvexSeq_ite (s := {n | ∀ k < n, 0 < decreasingRearrangement r k})
    (f := fun n ↦ ∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k))
    ⟨fun _ _ _ hj _ hn k hk ↦ hj k (hk.trans_le hn.2)⟩ ?_
  rintro i ⟨-, -⟩ j ⟨-, hj⟩ hij
  simp only [sum_range_succ, add_sub_cancel_left]
  exact neg_le_neg (Real.logb_le_logb_of_le hb (hj j j.lt_succ_self)
    (antitone_decreasingRearrangement hr hij))

/-- For a base `b > 1`, the row Hodge heights of a bounded majorant lie above the line of slope
`-logb b r*₀` through the origin; in particular they are admissible. -/
theorem isAdmissible_rowHodgeHeights (hb : 1 < b) (hr : BddAbove (Set.range r)) :
    IsAdmissible (rowHodgeHeights b r) := by
  refine isAdmissible_iff.mpr ⟨0, -Real.logb b (decreasingRearrangement r 0), fun n ↦ ?_⟩
  by_cases h : ∀ k < n, 0 < decreasingRearrangement r k
  · rw [rowHodgeHeights_of_forall_pos h, WithTop.coe_le_coe, zero_add]
    calc -Real.logb b (decreasingRearrangement r 0) * n
        = ∑ _k ∈ range n, -Real.logb b (decreasingRearrangement r 0) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun k hk ↦ neg_le_neg (Real.logb_le_logb_of_le hb
          (h k (mem_range.mp hk)) (antitone_decreasingRearrangement hr k.zero_le))
  · simp [rowHodgeHeights, h]

end TauCeti

namespace Matrix

open TauCeti

variable {ι R : Type*} [DecidableEq ι] [SeminormedCommRing R] [NormOneClass R]
  [IsUltrametricDist R] {A : Matrix ι ι R} {r : ι → ℝ} {b : ℝ}
  {v : AddValuation R (WithTop ℝ)}

/-- **Row Hodge bound for Fredholm coefficients.** If `‖x‖ = b ^ (-v x)` for `x ≠ 0` with
`b > 1`, and `r` is a bounded row majorant of `A`, then the `n`-th coefficient of
`det (1 - T A)` has valuation at least the row Hodge height of `r` at `n`. In particular the
coefficient vanishes when one of the first `n` rearranged row bounds does. -/
theorem rowHodgeHeights_le_addValuation_charCoeff (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (hr : BddAbove (Set.range r))
    (hA : ∀ i j, ‖A i j‖ ≤ r i) (n : ℕ) :
    rowHodgeHeights b r n ≤ v (A.charCoeff n) := by
  have hbound := norm_charCoeff_le_prod_decreasingRearrangement hr hA n
  by_cases hc : A.charCoeff n = 0
  · simp [hc]
  by_cases htop : v (A.charCoeff n) = ⊤
  · simp [htop]
  have hnorm : 0 < ‖A.charCoeff n‖ := by
    rw [hv _ hc]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans hb) _
  -- A vanishing rearranged bound among the first `n` would force the coefficient to vanish.
  have hpos : ∀ k < n, 0 < decreasingRearrangement r k := fun k hk ↦
    (decreasingRearrangement_nonneg hr k).lt_of_ne fun h0 ↦
      hnorm.not_ge (hbound.trans_eq (prod_eq_zero (mem_range.mpr hk) h0.symm))
  have hlog := Real.logb_le_logb_of_le hb hnorm hbound
  rw [hv _ hc, Real.logb_rpow (zero_lt_one.trans hb) hb.ne',
    Real.logb_prod _ _ fun k hk ↦ (hpos k (mem_range.mp hk)).ne'] at hlog
  rw [rowHodgeHeights_of_forall_pos hpos, ← WithTop.coe_untop₀_of_ne_top htop,
    WithTop.coe_le_coe, sum_neg_distrib]
  linarith

/-- **Row Hodge lower polygon.** If `‖x‖ = b ^ (-v x)` for `x ≠ 0` with `b > 1`, and `r` is a
bounded row majorant of `A`, then the row Hodge heights of `r` lie below the Newton polygon of
`det (1 - T A)`. -/
theorem rowHodgeHeights_le_newtonPolygon_charPowerSeries (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (hr : BddAbove (Set.range r))
    (hA : ∀ i j, ‖A i j‖ ≤ r i) :
    rowHodgeHeights b r ≤ A.charPowerSeries.newtonPolygon v :=
  PowerSeries.le_newtonPolygon (isConvexSeq_rowHodgeHeights hb hr) fun n ↦ by
    rw [coeff_charPowerSeries]
    exact rowHodgeHeights_le_addValuation_charCoeff hb hv hr hA n

/-- **Lower bound for Fredholm slopes.** If `‖x‖ = b ^ (-v x)` for `x ≠ 0` with `b > 1`, and
every entry of `A` has norm at most `B`, then every finite slope of the Newton polygon of
`det (1 - T A)` is at least `-logb b B`. -/
theorem neg_logb_le_unitSlope_newtonPolygon_charPowerSeries (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {B : ℝ} (hB : ∀ i j, ‖A i j‖ ≤ B) {n : ℕ}
    (hn : n ∈ finiteEdges (A.charPowerSeries.newtonPolygon v)) :
    -Real.logb b B ≤ unitSlope (A.charPowerSeries.newtonPolygon v) n := by
  have hP := PowerSeries.isConvexSeq_newtonPolygon A.charPowerSeries v
  have hn' := mem_finiteEdges.mp hn
  have hr : BddAbove (Set.range fun _ : ι ↦ B) := ⟨B, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  have hHP := rowHodgeHeights_le_newtonPolygon_charPowerSeries hb hv hr hB
  -- Finiteness at `n + 1` forces the first rearranged bound, and hence `B`, to be positive.
  have hpos : 0 < decreasingRearrangement (fun _ : ι ↦ B) 0 :=
    rowHodgeHeights_ne_top_iff.mp (ne_top_of_le_ne_top hn'.2 (hHP (n + 1))) 0 n.succ_pos
  obtain ⟨s, hs, hsB⟩ := (lt_decreasingRearrangement_iff hr le_rfl 0).mp hpos
  obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < s.card)
  have hle : decreasingRearrangement (fun _ : ι ↦ B) 0 ≤ B :=
    decreasingRearrangement_le_of_card_le (hsB i hi).le (s := ∅) (Nat.zero_le _) fun _ _ ↦ le_rfl
  -- The Newton polygon starts at `(0, 0)`, so its first slope is its height at `1`.
  have hadm : IsAdmissible fun k ↦ v (PowerSeries.coeff k A.charPowerSeries) :=
    (isAdmissible_rowHodgeHeights hb hr).mono fun k ↦ by
      rw [coeff_charPowerSeries]
      exact rowHodgeHeights_le_addValuation_charCoeff hb hv hr hB k
  have hP0 : A.charPowerSeries.newtonPolygon v 0 = 0 := le_antisymm
    (by simpa using PowerSeries.newtonPolygon_le hadm 0) (by simpa using hHP 0)
  have hP1 : A.charPowerSeries.newtonPolygon v 1 ≠ ⊤ :=
    hP.ordConnected.out (by simp [hP0]) hn'.2 ⟨zero_le_one, by omega⟩
  have hH1 := hHP 1
  rw [rowHodgeHeights_of_forall_pos fun k hk ↦ by rwa [Nat.lt_one_iff.mp hk],
    ← WithTop.coe_untop₀_of_ne_top hP1, WithTop.coe_le_coe, sum_range_one] at hH1
  refine le_trans ?_ (hP.monotoneOn (mem_finiteEdges.mpr ⟨by simp [hP0], hP1⟩) hn n.zero_le)
  rw [unitSlope_def, zero_add, hP0, WithTop.untop₀_zero, sub_zero]
  exact (neg_le_neg (Real.logb_le_logb_of_le hb hpos hle)).trans hH1

end Matrix
