/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import TauCeti.Analysis.Matrix.CharPowerSeries.Rearrangement
public import TauCeti.NumberTheory.NewtonPolygon.Basic

/-!
# Row Hodge lower polygons of Fredholm series

Let `r` be a bounded row majorant of a matrix `A`, so `‖A i j‖ ≤ r i`, and let `r*` be its
decreasing rearrangement. Fix a real additive valuation `v` and a base `b > 1` with
`b ^ (-v x) ≤ ‖x‖` for nonzero `x`, as for the normalisation `‖x‖ = b ^ (-v x)`. The
*row Hodge polygon* of `r` has nondecreasing weights `-logb b r*ₖ`: its height at `n` is
`∑ k < n, -logb b r*ₖ` while the first `n` rearranged terms are positive, and `⊤` once a
rearranged term vanishes. When `r` has only `m` positive values, the polygon is finite exactly
on `[0, m]`, even if the Fredholm series has smaller degree. It is thus the polygon of finite or
of infinite slope data, according to the number of positive row bounds; the definition treats
both cases uniformly.

Since the `n`-th Fredholm coefficient has norm at most `∏ k < n, r*ₖ`, the row Hodge polygon
lies below the Newton polygon of `det (1 - X A)`
(`Matrix.rowHodgePolygon_le_newtonPolygon_charPowerSeries`). The finite domain of the Newton
polygon is therefore contained in that of the row Hodge polygon; no equality of domains or
endpoints is asserted. The polygon depends on the specified coordinates and majorant: it is not
an invariant of `det (1 - X A)`, and it need not be sharp. In particular, if all entries have
norm at most `C`, every finite slope of the Newton polygon is at least `-logb b C`
(`Matrix.neg_logb_le_unitSlope_newtonPolygon_charPowerSeries`).

## Main definitions

* `TauCeti.rowHodgePolygon b r`: the row Hodge polygon of a row majorant `r` in base `b`.

## Main results

* `TauCeti.isConvexSeq_rowHodgePolygon`, `TauCeti.unitSlope_rowHodgePolygon`: the row Hodge
  polygon is convex, with slopes `-logb b r*ₙ`.
* `Matrix.rowHodgePolygon_le_addValuation_charCoeff`: the valuations of the Fredholm
  coefficients are bounded below by the row Hodge polygon.
* `Matrix.rowHodgePolygon_le_newtonPolygon_charPowerSeries`: it lies below the Newton polygon
  of the Fredholm series.
* `Matrix.neg_logb_le_unitSlope_newtonPolygon_charPowerSeries`: a uniform entry bound `C`
  bounds every finite Newton slope below by `-logb b C`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
* K. S. Kedlaya, [*A little p-adic numerical analysis*](https://kskedlaya.org/18.787/numerical.pdf),
  MIT 18.787 notes (2007), §3.
-/

public section

open Finset

namespace TauCeti

variable {ι : Type*} {b : ℝ} {r : ι → ℝ}

open Classical in
/-- The row Hodge polygon of a row majorant `r` in base `b`. With `r*` the decreasing
rearrangement of `r`, its height at `n` is `∑ k < n, -logb b r*ₖ` when the first `n` terms of
`r*` are positive, and `⊤` otherwise. -/
noncomputable def rowHodgePolygon (b : ℝ) (r : ι → ℝ) (n : ℕ) : WithTop ℝ :=
  if ∀ k < n, 0 < decreasingRearrangement r k then
    ((∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k) : ℝ) : WithTop ℝ)
  else ⊤

open Classical in
theorem rowHodgePolygon_def (b : ℝ) (r : ι → ℝ) (n : ℕ) :
    rowHodgePolygon b r n =
      if ∀ k < n, 0 < decreasingRearrangement r k then
        ((∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k) : ℝ) : WithTop ℝ)
      else ⊤ := (rfl)

/-- On its finite domain the row Hodge polygon is the sum of the first weights. -/
theorem rowHodgePolygon_of_forall_pos {n : ℕ} (hn : ∀ k < n, 0 < decreasingRearrangement r k) :
    rowHodgePolygon b r n =
      ((∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k) : ℝ) : WithTop ℝ) := by
  rw [rowHodgePolygon_def, ite_eq_left hn]

/-- The row Hodge polygon is finite exactly while the rearranged row bounds are positive. -/
theorem rowHodgePolygon_ne_top_iff {n : ℕ} :
    rowHodgePolygon b r n ≠ ⊤ ↔ ∀ k < n, 0 < decreasingRearrangement r k := by
  rw [rowHodgePolygon_def]
  split_ifs with hn
  · simpa using hn
  · simpa using hn

/-- The row Hodge polygon starts at `(0, 0)`. -/
@[simp]
theorem rowHodgePolygon_zero : rowHodgePolygon b r 0 = 0 := by
  simp [rowHodgePolygon_def]

/-- The row Hodge polygon is convex: its weights `-logb b r*ₖ` are nondecreasing on its finite
domain, which is an initial segment of `ℕ`. -/
theorem isConvexSeq_rowHodgePolygon (hb : 1 < b) (hr : BddAbove (Set.range r)) :
    IsConvexSeq (rowHodgePolygon b r) := by
  classical
  set s : Set ℕ := {n | ∀ k < n, 0 < decreasingRearrangement r k}
  have hs : s.OrdConnected := ⟨fun _ _ n hn m hm k hk ↦ hn k (hk.trans_le hm.2)⟩
  have h := isConvexSeq_ite (f := fun n ↦ ∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k))
    hs fun i hi j hj hij ↦ by
      simp only [sum_range_succ, add_sub_cancel_left, neg_le_neg_iff]
      exact Real.logb_le_logb_of_le hb (hj.2 j (Nat.lt_succ_self j))
        (antitone_decreasingRearrangement hr hij)
  have heq : rowHodgePolygon b r = fun n ↦ if n ∈ s then
      ((∑ k ∈ range n, -Real.logb b (decreasingRearrangement r k) : ℝ) : WithTop ℝ) else ⊤ :=
    funext fun n ↦ by simp only [rowHodgePolygon_def, s, Set.mem_ofPred_eq]
  rw [heq]
  exact h

/-- On its finite edges, the slopes of the row Hodge polygon are the weights `-logb b r*ₙ`. -/
theorem unitSlope_rowHodgePolygon {n : ℕ} (hn : n ∈ finiteEdges (rowHodgePolygon b r)) :
    unitSlope (rowHodgePolygon b r) n = -Real.logb b (decreasingRearrangement r n) := by
  rw [mem_finiteEdges, rowHodgePolygon_ne_top_iff, rowHodgePolygon_ne_top_iff] at hn
  rw [unitSlope_def, rowHodgePolygon_of_forall_pos hn.1, rowHodgePolygon_of_forall_pos hn.2,
    WithTop.untop₀_coe, WithTop.untop₀_coe, sum_range_succ, add_sub_cancel_left]

end TauCeti

namespace Matrix

open TauCeti

variable {ι R : Type*} [DecidableEq ι] [SeminormedCommRing R] [NormOneClass R]
  [IsUltrametricDist R] {A : Matrix ι ι R} {v : AddValuation R (WithTop ℝ)} {b : ℝ}

/-- **Row Hodge coefficient bound.** If `‖x‖ ≥ b ^ (-v x)` for nonzero `x` and `r` is a bounded
row majorant of `A`, the `n`-th Fredholm coefficient of `A` has valuation at least the height of
the row Hodge polygon of `r` at `n`. In particular it has infinite valuation beyond the finite
domain. -/
theorem rowHodgePolygon_le_addValuation_charCoeff (hb : 1 < b)
    (hv : ∀ x ≠ 0, b ^ (-(v x).untop₀) ≤ ‖x‖) {r : ι → ℝ} (hr : BddAbove (Set.range r))
    (hA : ∀ i j, ‖A i j‖ ≤ r i) (n : ℕ) :
    rowHodgePolygon b r n ≤ v (A.charCoeff n) := by
  set c := A.charCoeff n
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, AddValuation.map_zero]
    exact le_top
  rcases eq_or_ne (v c) ⊤ with hvc | hvc
  · rw [hvc]
    exact le_top
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hvc
  have hbt := hv c hc
  rw [← ht, WithTop.untop₀_coe] at hbt
  have hprod := hbt.trans (norm_charCoeff_le_prod_decreasingRearrangement hr hA n)
  have hpos : 0 < ∏ k ∈ range n, decreasingRearrangement r k :=
    (Real.rpow_pos_of_pos (by linarith) _).trans_le hprod
  have hn : ∀ k < n, 0 < decreasingRearrangement r k := fun k hk ↦
    (decreasingRearrangement_nonneg hr k).lt_of_ne fun h0 ↦ hpos.ne'
      (prod_eq_zero (mem_range.mpr hk) h0.symm)
  have hlog := (Real.le_logb_iff_rpow_le hb hpos).mpr hprod
  rw [Real.logb_prod _ _ fun k hk ↦ (hn k (mem_range.mp hk)).ne'] at hlog
  rw [rowHodgePolygon_of_forall_pos hn, ← ht, WithTop.coe_le_coe, sum_neg_distrib]
  linarith

/-- **Row Hodge lower bound.** If `‖x‖ ≥ b ^ (-v x)` for nonzero `x` and `r` is a bounded row
majorant of `A`, the row Hodge polygon of `r` lies below the Newton polygon of the Fredholm
series `det (1 - X A)`. Neither completeness nor null row bounds are needed. -/
theorem rowHodgePolygon_le_newtonPolygon_charPowerSeries (hb : 1 < b)
    (hv : ∀ x ≠ 0, b ^ (-(v x).untop₀) ≤ ‖x‖) {r : ι → ℝ} (hr : BddAbove (Set.range r))
    (hA : ∀ i j, ‖A i j‖ ≤ r i) :
    rowHodgePolygon b r ≤ A.charPowerSeries.newtonPolygon v :=
  PowerSeries.le_newtonPolygon (isConvexSeq_rowHodgePolygon hb hr) fun n ↦ by
    rw [coeff_charPowerSeries]
    exact rowHodgePolygon_le_addValuation_charCoeff hb hv hr hA n

/-- **Lower bound for Fredholm slopes.** If `‖x‖ ≥ b ^ (-v x)` for nonzero `x` and every entry
of `A` has norm at most `C`, every finite slope of the Newton polygon of `det (1 - X A)` is at
least `-logb b C`. -/
theorem neg_logb_le_unitSlope_newtonPolygon_charPowerSeries (hb : 1 < b)
    (hv : ∀ x ≠ 0, b ^ (-(v x).untop₀) ≤ ‖x‖) {C : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ C) {n : ℕ}
    (hn : n ∈ finiteEdges (A.charPowerSeries.newtonPolygon v)) :
    -Real.logb b C ≤ unitSlope (A.charPowerSeries.newtonPolygon v) n := by
  have hr : BddAbove (Set.range fun _ : ι ↦ C) := ⟨C, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  have hH := isConvexSeq_rowHodgePolygon hb hr
  have hHP := rowHodgePolygon_le_newtonPolygon_charPowerSeries hb hv hr hA
  have hP := A.charPowerSeries.isConvexSeq_newtonPolygon v
  -- The Newton polygon starts at height at most `v 1 = 0`, so its domain contains `0` and `1`.
  have hP0 : A.charPowerSeries.newtonPolygon v 0 ≤ 0 := by
    have hadm : IsAdmissible fun n ↦ v (PowerSeries.coeff n A.charPowerSeries) :=
      hH.isAdmissible.mono fun n ↦ by
        rw [coeff_charPowerSeries]
        exact rowHodgePolygon_le_addValuation_charCoeff hb hv hr hA n
    have := PowerSeries.newtonPolygon_le hadm 0
    rwa [coeff_charPowerSeries, charCoeff_zero, AddValuation.map_one] at this
  set P := A.charPowerSeries.newtonPolygon v
  obtain ⟨-, hn₁⟩ := mem_finiteEdges.mp hn
  have hP0' : P 0 ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hP0
  have hP1 : P 1 ≠ ⊤ := hP.ordConnected.out hP0' hn₁ ⟨zero_le_one, by omega⟩
  have hslope := hP.monotoneOn (mem_finiteEdges.mpr ⟨hP0', hP1⟩) hn (Nat.zero_le n)
  -- The first rearranged bound is positive and at most `C`.
  have hpos : 0 < decreasingRearrangement (fun _ : ι ↦ C) 0 :=
    rowHodgePolygon_ne_top_iff.mp (ne_top_of_le_ne_top hP1 (hHP 1)) 0 zero_lt_one
  have hC : 0 ≤ C := by
    obtain ⟨s, hs, hsC⟩ := (lt_decreasingRearrangement_iff hr le_rfl 0).mp hpos
    obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < s.card)
    exact (hsC i hi).le
  have hle : decreasingRearrangement (fun _ : ι ↦ C) 0 ≤ C :=
    decreasingRearrangement_le_of_card_le hC (s := ∅) le_rfl fun _ _ ↦ le_rfl
  have h1 := hHP 1
  rw [rowHodgePolygon_of_forall_pos fun k hk ↦ by rwa [Nat.lt_one_iff.mp hk]] at h1
  obtain ⟨p₀, hp₀⟩ := WithTop.ne_top_iff_exists.mp hP0'
  obtain ⟨p₁, hp₁⟩ := WithTop.ne_top_iff_exists.mp hP1
  rw [← hp₀, ← WithTop.coe_zero, WithTop.coe_le_coe] at hP0
  rw [← hp₁] at h1
  rw [unitSlope_def, ← hp₀, ← hp₁, WithTop.untop₀_coe, WithTop.untop₀_coe] at hslope
  simp only [sum_range_one, WithTop.coe_le_coe] at h1
  have := Real.logb_le_logb_of_le hb hpos hle
  linarith

end Matrix
