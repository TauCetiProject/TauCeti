/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Turning
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Global turning of the Schwarz--Christoffel boundary

For strictly ordered prevertices, the direction angle on the interval following the `i`-th
prevertex is `π` times the sum of the exponents at all later prevertices.  Consequently negative
exponents make these angles strictly increase as the boundary is traversed from left to right.

Under the classical closing condition `∑ i, e i = -2`, the angle increase between distinct
indexed finite prevertices `i < j` lies strictly between zero and `2π`.  All finite edge directions
are therefore distinct, while the angles on the two unbounded intervals differ by exactly `2π`.
This is the global turning-order input for separating nonadjacent sides of the
Schwarz--Christoffel polygon; the local fact that consecutive sides form genuine corners is proved
in `SchwarzChristoffel.Turning`.

## Main results

* `TauCeti.strictMono_schwarzChristoffelEdgeAngle_comp` -- negative exponents make the edge angles
  at successive prevertices strictly increase.
* `TauCeti.schwarzChristoffelEdgeAngle_sub_mem_Ioo_two_pi` -- the angle increase between distinct
  indexed finite prevertices `i < j` lies in `(0, 2π)` when the total exponent is `-2`.
* `TauCeti.injective_exp_schwarzChristoffelEdgeAngle_prevertex` -- the finite edge directions are
  pairwise distinct.
* `TauCeti.schwarzChristoffelEdgeAngle_eq_neg_two_pi_of_lt_first` and
  `TauCeti.schwarzChristoffelEdgeAngle_eq_zero_of_last_le` -- the two unbounded edge angles are
  `-2π` and zero.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set

namespace TauCeti

variable {n : ℕ}

/-- The Schwarz--Christoffel edge angle is zero to the right of every prevertex. -/
theorem schwarzChristoffelEdgeAngle_eq_zero_of_forall_le {ι : Type*} [Fintype ι]
    (a e : ι → ℝ) {c : ℝ} (hc : ∀ i, a i ≤ c) :
    schwarzChristoffelEdgeAngle a e c = 0 := by
  rw [schwarzChristoffelEdgeAngle_eq_sum_filter]
  simp [not_lt.mpr (hc _)]

/-- To the left of every prevertex, the Schwarz--Christoffel edge angle is `π` times the total
exponent. -/
theorem schwarzChristoffelEdgeAngle_eq_pi_mul_sum_of_forall_lt {ι : Type*} [Fintype ι]
    (a e : ι → ℝ) {c : ℝ} (hc : ∀ i, c < a i) :
    schwarzChristoffelEdgeAngle a e c = Real.pi * ∑ i, e i := by
  rw [schwarzChristoffelEdgeAngle_eq_sum_filter]
  simp only [hc, Finset.filter_true]

section FiniteLinearOrder

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

local instance : LocallyFiniteOrder ι := Fintype.toLocallyFiniteOrder

local instance : LocallyFiniteOrderTop ι where
  finsetIci i := Finset.univ.filter (i ≤ ·)
  finsetIoi i := Finset.univ.filter (i < ·)
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

/-- For strictly ordered prevertices, the edge angle following the `i`-th prevertex is `π` times
the sum of the exponents at the later prevertices. -/
theorem schwarzChristoffelEdgeAngle_eq_pi_mul_sum_Ioi (a e : ι → ℝ)
    (ha : StrictMono a) (i : ι) :
    schwarzChristoffelEdgeAngle a e (a i) =
      Real.pi * ∑ k ∈ Finset.Ioi i, e k := by
  rw [schwarzChristoffelEdgeAngle_eq_sum_filter]
  apply congrArg (fun x : ℝ ↦ Real.pi * x)
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
    exact ha.lt_iff_lt
  · simp

/-- The increase in edge angle between two indexed prevertices is `-π` times the sum of the
exponents in the corresponding right-closed index interval. -/
theorem schwarzChristoffelEdgeAngle_sub_eq_neg_pi_mul_sum_Ioc
    (a e : ι → ℝ) (ha : StrictMono a) {i j : ι} (hij : i < j) :
    schwarzChristoffelEdgeAngle a e (a j) - schwarzChristoffelEdgeAngle a e (a i) =
      -Real.pi * ∑ k ∈ Finset.Ioc i j, e k := by
  calc
    _ = -(schwarzChristoffelEdgeAngle a e (a i) -
        schwarzChristoffelEdgeAngle a e (a j)) := by ring
    _ = -(Real.pi * ∑ k ∈ Finset.univ.filter
        (fun k ↦ a k ∈ Ioc (a i) (a j)), e k) := by
      rw [schwarzChristoffelEdgeAngle_sub a e (ha.monotone hij.le)]
    _ = -Real.pi * ∑ k ∈ Finset.Ioc i j, e k := by
      rw [neg_mul]
      congr 1
      apply congrArg (fun x : ℝ ↦ Real.pi * x)
      apply Finset.sum_congr
      · ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc, mem_Ioc]
        exact and_congr (ha.lt_iff_lt) (ha.le_iff_le)
      · simp

/-- Strictly ordered prevertices carrying negative exponents have strictly increasing
Schwarz--Christoffel edge angles. -/
theorem strictMono_schwarzChristoffelEdgeAngle_comp (a e : ι → ℝ)
    (ha : StrictMono a) (he : ∀ i, e i < 0) :
    StrictMono (fun i ↦ schwarzChristoffelEdgeAngle a e (a i)) := by
  intro i j hij
  have hdiff := schwarzChristoffelEdgeAngle_sub_eq_neg_pi_mul_sum_Ioc a e ha hij
  have hsum : ∑ k ∈ Finset.Ioc i j, e k < 0 := by
    apply Finset.sum_neg
    · exact fun k _ ↦ he k
    · exact ⟨j, Finset.mem_Ioc.mpr ⟨hij, le_rfl⟩⟩
  nlinarith [Real.pi_pos]

private theorem sum_gt_neg_two_of_not_mem {κ : Type*} [Fintype κ] (e : κ → ℝ)
    (he : ∀ i, e i < 0) (hsum : ∑ i, e i = -2) (s : Finset κ) {i : κ}
    (hi : i ∉ s) : -2 < ∑ k ∈ s, e k := by
  classical
  have hproper : ∑ k ∈ s, -e k < ∑ k, -e k := by
    apply Finset.sum_lt_sum_of_subset (Finset.subset_univ s) (Finset.mem_univ i) hi
    · exact neg_pos.mpr (he i)
    · exact fun k _ _ ↦ (neg_pos.mpr (he k)).le
  have hfull : ∑ k, -e k = 2 := by
    rw [Finset.sum_neg_distrib, hsum]
    norm_num
  have := hproper.trans_eq hfull
  rw [Finset.sum_neg_distrib] at this
  linarith

/-- Under the closing condition `∑ i, e i = -2`, the edge-angle increase along any nonempty
proper index interval lies strictly between zero and `2π`.

The upper bound is strict because the interval omits its left endpoint, whose negative exponent
accounts for a positive part of the complementary turn. -/
theorem schwarzChristoffelEdgeAngle_sub_mem_Ioo_two_pi
    (a e : ι → ℝ) (ha : StrictMono a) (he : ∀ i, e i < 0)
    (hsum : ∑ i, e i = -2) {i j : ι} (hij : i < j) :
    schwarzChristoffelEdgeAngle a e (a j) - schwarzChristoffelEdgeAngle a e (a i) ∈
      Ioo 0 (2 * Real.pi) := by
  have hpositive : 0 < schwarzChristoffelEdgeAngle a e (a j) -
      schwarzChristoffelEdgeAngle a e (a i) :=
    sub_pos.mpr (strictMono_schwarzChristoffelEdgeAngle_comp a e ha he hij)
  rw [schwarzChristoffelEdgeAngle_sub_eq_neg_pi_mul_sum_Ioc a e ha hij] at hpositive ⊢
  have hpartial :=
    sum_gt_neg_two_of_not_mem e he hsum (Finset.Ioc i j) (i := i) (by simp)
  exact ⟨hpositive, by nlinarith [Real.pi_pos]⟩

/-- Under negative exponents summing to `-2`, every indexed-prevertex edge angle lies in the
half-open fundamental interval `(-2π, 0]`.  The angle can equal zero when no prevertex lies
strictly to its right, while `-2π` occurs only before every prevertex. -/
theorem schwarzChristoffelEdgeAngle_mem_Ioc {ι : Type*} [Fintype ι] (a e : ι → ℝ)
    (he : ∀ i, e i < 0) (hsum : ∑ i, e i = -2) (i : ι) :
    schwarzChristoffelEdgeAngle a e (a i) ∈ Ioc (-2 * Real.pi) 0 := by
  classical
  rw [schwarzChristoffelEdgeAngle_eq_sum_filter]
  let s := Finset.univ.filter fun k ↦ a i < a k
  have hnonpos : ∑ k ∈ s, e k ≤ 0 :=
    Finset.sum_nonpos fun k _ ↦ (he k).le
  have hlower := sum_gt_neg_two_of_not_mem e he hsum s (i := i) (by simp [s])
  constructor <;> nlinarith [Real.pi_pos]

/-- Under negative exponents summing to `-2`, the direction constants on the intervals following
distinct finite prevertices are distinct.  Thus no two of those directed sides have the same
orientation; the repeated direction occurs only across the two ends of the compactified real
line. -/
theorem injective_exp_schwarzChristoffelEdgeAngle_prevertex
    (a e : ι → ℝ) (ha : StrictMono a) (he : ∀ i, e i < 0)
    (hsum : ∑ i, e i = -2) :
    Function.Injective (fun i ↦
      Complex.exp (schwarzChristoffelEdgeAngle a e (a i) * Complex.I)) := by
  intro i j hij
  have hcircle : Circle.exp (schwarzChristoffelEdgeAngle a e (a i)) =
      Circle.exp (schwarzChristoffelEdgeAngle a e (a j)) := by
    apply Subtype.ext
    simpa only [Circle.coe_exp] using hij
  have hangle :=
    (Circle.exp_injOn_Ioc (a := -2 * Real.pi) (b := 0) (by linarith [Real.pi_pos]))
      (schwarzChristoffelEdgeAngle_mem_Ioc a e he hsum i)
      (schwarzChristoffelEdgeAngle_mem_Ioc a e he hsum j) hcircle
  exact (strictMono_schwarzChristoffelEdgeAngle_comp a e ha he).injective hangle

end FiniteLinearOrder

/-- With total exponent `-2`, the Schwarz--Christoffel edge angle before the first ordered
prevertex is `-2π`. -/
theorem schwarzChristoffelEdgeAngle_eq_neg_two_pi_of_lt_first
    (a e : Fin (n + 1) → ℝ) (ha : Monotone a) (hsum : ∑ i, e i = -2)
    {c : ℝ} (hc : c < a 0) :
    schwarzChristoffelEdgeAngle a e c = -2 * Real.pi := by
  rw [schwarzChristoffelEdgeAngle_eq_pi_mul_sum_of_forall_lt a e
    (fun i ↦ hc.trans_le (ha i.zero_le)), hsum]
  ring

/-- The Schwarz--Christoffel edge angle at or beyond the last ordered prevertex is
zero. -/
theorem schwarzChristoffelEdgeAngle_eq_zero_of_last_le
    (a e : Fin (n + 1) → ℝ) (ha : Monotone a) {c : ℝ}
    (hc : a (Fin.last n) ≤ c) :
    schwarzChristoffelEdgeAngle a e c = 0 :=
  schwarzChristoffelEdgeAngle_eq_zero_of_forall_le a e fun i ↦
    (ha i.le_last).trans hc

end TauCeti
