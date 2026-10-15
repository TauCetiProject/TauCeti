/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Inv
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor

/-!
# Weighted indices of multivariate polynomials

The index at a point with natural weights `r` is the infimum of `∑ j, d j / r j` over
nonzero Hasse jets. Thus an index lower bound specifies exactly which jets must vanish.
For a nonzero polynomial over a ring the infimum is attained, and positive weights make
it finite. The reciprocal weights distinguish this index from a weighted total degree.

Division takes place in `ℝ≥0∞`: a positive exponent in a coordinate of weight zero has
infinite cost. The constant jet has cost zero, even when some weights vanish.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §2.6, Definition 2.6.2 and Example 2.6.3.
-/

public section

namespace MvPolynomial

open scoped ENNReal NNReal

variable {σ R : Type*}

section Semiring

variable [CommSemiring R]

/-- The weighted index is the least reciprocal-weighted order of a nonzero Hasse jet;
the infimum of the empty set is `⊤`. -/
noncomputable def weightedIndex (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R) : ℝ≥0∞ :=
  ⨅ (d : σ →₀ ℕ) (_ : eval a (hasseDeriv d P) ≠ 0),
    d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹)

/-- The defining infimum, expressed as a sum of ratios over the derivative's support. -/
theorem weightedIndex_def (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R) :
    weightedIndex r a P = ⨅ (d : σ →₀ ℕ) (_ : eval a (hasseDeriv d P) ≠ 0),
      ∑ j ∈ d.support, (d j : ℝ≥0∞) / (r j : ℝ≥0∞) := by
  simp only [weightedIndex, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
    div_eq_mul_inv]

/-- A nonzero jet bounds the index from above by its weight. -/
theorem weightedIndex_le {r : σ → ℕ} {a : σ → R} {P : MvPolynomial σ R}
    {d : σ →₀ ℕ} (hd : eval a (hasseDeriv d P) ≠ 0) :
    weightedIndex r a P ≤ d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) :=
  iInf_le_of_le d (iInf_le_of_le hd le_rfl)

/-- An index lower bound is equivalent to the vanishing of all jets of strictly smaller
weight. The strict inequality also covers the threshold `⊤`. -/
theorem le_weightedIndex_iff (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R)
    (t : ℝ≥0∞) :
    t ≤ weightedIndex r a P ↔ ∀ d : σ →₀ ℕ,
      (∑ j ∈ d.support, (d j : ℝ≥0∞) / (r j : ℝ≥0∞)) < t →
        eval a (hasseDeriv d P) = 0 := by
  rw [weightedIndex_def]
  constructor
  · intro h d hd
    by_contra hn
    exact (not_lt_of_ge (h.trans (iInf_le_of_le d (iInf_le_of_le hn le_rfl)))) hd
  · intro h
    refine le_iInf fun d ↦ le_iInf fun hd ↦ ?_
    exact le_of_not_gt fun ht ↦ hd (h d ht)

@[simp]
theorem weightedIndex_zero (r : σ → ℕ) (a : σ → R) :
    weightedIndex r a (0 : MvPolynomial σ R) = ⊤ := by
  simp [weightedIndex]

/-- The index of a sum is at least the smaller index. -/
theorem min_weightedIndex_le_add (r : σ → ℕ) (a : σ → R) (P Q : MvPolynomial σ R) :
    min (weightedIndex r a P) (weightedIndex r a Q) ≤ weightedIndex r a (P + Q) := by
  rw [le_weightedIndex_iff]
  intro d hd
  have hP := (le_weightedIndex_iff r a P _).mp le_rfl d (hd.trans_le (min_le_left _ _))
  have hQ := (le_weightedIndex_iff r a Q _).mp le_rfl d (hd.trans_le (min_le_right _ _))
  simp [hP, hQ]

/-- Injective coefficient maps preserve the index when the center is mapped as well. -/
theorem weightedIndex_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (hf : Function.Injective f) (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R) :
    weightedIndex r (fun j ↦ f (a j)) (map f P) = weightedIndex r a P := by
  apply eq_of_forall_le_iff
  intro t
  simp only [le_weightedIndex_iff, ← coeff_taylor, ← map_taylor, coeff_map,
    map_eq_zero_iff f hf]

/-- Taylor translation of the polynomial translates the center of its index. -/
theorem weightedIndex_taylor (r : σ → ℕ) (a b : σ → R) (P : MvPolynomial σ R) :
    weightedIndex r b (taylor a P) = weightedIndex r (b + a) P := by
  apply eq_of_forall_le_iff
  intro t
  simp only [le_weightedIndex_iff, ← coeff_taylor, taylor_taylor]

/-- The index is attained by a nonzero Taylor coefficient whenever the Taylor shift is
nonzero. This statement also permits zero weights and infinite index. -/
theorem exists_weightedIndex_eq_weight {r : σ → ℕ} {a : σ → R}
    {P : MvPolynomial σ R} (hP : taylor a P ≠ 0) :
    ∃ d : σ →₀ ℕ, eval a (hasseDeriv d P) ≠ 0 ∧
      weightedIndex r a P = d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) := by
  classical
  obtain ⟨d, hd, hmin⟩ := (taylor a P).support.exists_min_image
    (fun d ↦ d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹)) (support_nonempty.mpr hP)
  have hjet : eval a (hasseDeriv d P) ≠ 0 := by
    simpa only [mem_support_iff, coeff_taylor] using hd
  refine ⟨d, hjet, (weightedIndex_le hjet).antisymm ?_⟩
  refine le_iInf fun e ↦ le_iInf fun he ↦ hmin e ?_
  simpa only [mem_support_iff, coeff_taylor] using he

/-- Index zero detects nonvanishing at the center, without a positivity condition on the
weights. -/
@[simp]
theorem weightedIndex_eq_zero_iff (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R) :
    weightedIndex r a P = 0 ↔ eval a P ≠ 0 := by
  constructor
  · intro h
    have ht : taylor a P ≠ 0 := by
      intro ht
      have htop : weightedIndex r a P = ⊤ := by
        apply top_le_iff.mp
        rw [le_weightedIndex_iff]
        intro d _
        simp [← coeff_taylor, ht]
      simp [h] at htop
    obtain ⟨d, hd, he⟩ := exists_weightedIndex_eq_weight (r := r) ht
    let : Finsupp.NonTorsionWeight ℕ (fun j ↦ (r j : ℝ≥0∞)⁻¹) :=
      ⟨by intro n j h; simpa [nsmul_eq_mul] using h⟩
    have hz : d = 0 := (Finsupp.weight_eq_zero_iff_eq_zero _).mp (he.symm.trans h)
    simpa [hz] using hd
  · intro hP
    apply le_antisymm _ zero_le
    simpa using (weightedIndex_le (r := r) (d := 0) (by simpa using hP))

@[simp]
theorem weightedIndex_one [Nontrivial R] (r : σ → ℕ) (a : σ → R) :
    weightedIndex r a (1 : MvPolynomial σ R) = 0 :=
  (weightedIndex_eq_zero_iff r a 1).mpr (by simp)

/-- At the origin a monomial has exactly the reciprocal-weighted degree of its exponent. -/
theorem weightedIndex_monomial_zero (r : σ → ℕ) (d : σ →₀ ℕ) {c : R} (hc : c ≠ 0) :
    weightedIndex r 0 (monomial d c) = d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) := by
  classical
  apply le_antisymm
  · apply weightedIndex_le
    rw [← coeff_taylor, taylor_zero, coeff_monomial, ite_eq_left rfl]
    exact hc
  · rw [le_weightedIndex_iff]
    intro e he
    rw [← coeff_taylor, taylor_zero, coeff_monomial, ite_eq_right]
    rintro rfl
    have he' : d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) <
        d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, div_eq_mul_inv] using he
    exact lt_irrefl _ he'

example : weightedIndex ![1, 2] 0
    (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) = 3 / 2 := by
  have hm : (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [monomial_add_single, ← X_pow_eq_monomial, pow_one, pow_one]
  rw [hm, weightedIndex_monomial_zero _ _ one_ne_zero, map_add,
    Finsupp.weight_single, Finsupp.weight_single]
  norm_num
  calc
    (1 : ℝ≥0∞) + 2⁻¹ = 2 / 2 + 1 / 2 := by
      rw [ENNReal.div_self (by norm_num) (by norm_num), one_div]
    _ = (2 + 1) / 2 := (ENNReal.add_div).symm
    _ = 3 / 2 := by norm_num

end Semiring

section Ring

variable [CommRing R]

/-- A power of a centered coordinate has its exponent divided by the coordinate's weight
as index. This includes exponent zero and zero weights. -/
theorem weightedIndex_X_sub_C_pow [Nontrivial R] (r : σ → ℕ) (a : σ → R) (i : σ)
    (m : ℕ) : weightedIndex r a ((X i - C (a i)) ^ m) =
      (m : ℝ≥0∞) / (r i : ℝ≥0∞) := by
  have ht : taylor a ((X i - C (a i)) ^ m) = monomial (Finsupp.single i m) (1 : R) := by
    simp [X_pow_eq_monomial]
  calc
    weightedIndex r a ((X i - C (a i)) ^ m) =
        weightedIndex r 0 (taylor a ((X i - C (a i)) ^ m)) := by
      rw [weightedIndex_taylor, zero_add]
    _ = (m : ℝ≥0∞) / (r i : ℝ≥0∞) := by
      rw [ht, weightedIndex_monomial_zero _ _ one_ne_zero, Finsupp.weight_single]
      simp [nsmul_eq_mul, div_eq_mul_inv]

/-- Positive weights make the index of every nonzero polynomial finite. -/
theorem weightedIndex_ne_top {r : σ → ℕ} (hr : ∀ j, r j ≠ 0) (a : σ → R)
    {P : MvPolynomial σ R} (hP : P ≠ 0) : weightedIndex r a P ≠ ⊤ := by
  obtain ⟨d, hd⟩ := ne_zero_iff.mp (taylor_eq_zero.not.mpr hP : taylor a P ≠ 0)
  apply ne_top_of_le_ne_top _ (weightedIndex_le (r := r) (by simpa [coeff_taylor] using hd))
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact ENNReal.sum_ne_top.mpr fun j _ ↦ by
    simpa [nsmul_eq_mul, ← div_eq_mul_inv] using
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simpa using hr j)

/-- With positive natural weights, the finite index is a nonnegative rational number. -/
theorem exists_weightedIndex_eq_nnrat {r : σ → ℕ} (hr : ∀ j, r j ≠ 0) (a : σ → R)
    {P : MvPolynomial σ R} (hP : P ≠ 0) :
    ∃ q : ℚ≥0, weightedIndex r a P = ((q : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨d, hd, he⟩ := exists_weightedIndex_eq_weight (r := r) (taylor_eq_zero.not.mpr hP)
  refine ⟨∑ j ∈ d.support, (d j : ℚ≥0) / (r j : ℚ≥0), ?_⟩
  rw [he, Finsupp.weight_apply, Finsupp.sum, NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    ENNReal.coe_div (by simpa using hr j)]
  simp [nsmul_eq_mul, div_eq_mul_inv]

/-- With positive weights, infinite index characterizes the zero polynomial. -/
@[simp]
theorem weightedIndex_eq_top_iff {r : σ → ℕ} (hr : ∀ j, r j ≠ 0) (a : σ → R)
    (P : MvPolynomial σ R) : weightedIndex r a P = ⊤ ↔ P = 0 := by
  constructor
  · exact fun h ↦ by_contra fun hP ↦ weightedIndex_ne_top hr a hP h
  · rintro rfl
    exact weightedIndex_zero r a

/-- A nonzero polynomial's index is bounded by the sum of its partial degrees divided
by the corresponding weights. -/
theorem weightedIndex_le_sum_degreeOf [Fintype σ] (r : σ → ℕ) (a : σ → R)
    {P : MvPolynomial σ R} (hP : P ≠ 0) :
    weightedIndex r a P ≤ ∑ j, (P.degreeOf j : ℝ≥0∞) / (r j : ℝ≥0∞) := by
  obtain ⟨d, hd, he⟩ := exists_weightedIndex_eq_weight (r := r) (taylor_eq_zero.not.mpr hP)
  rw [he, Finsupp.weight_eq_sum]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hj : d j ≤ P.degreeOf j :=
    (monomial_le_degreeOf j (mem_support_iff.mpr (by simpa [coeff_taylor] using hd))).trans
      (degreeOf_taylor_le a j P)
  simpa [nsmul_eq_mul, ← div_eq_mul_inv] using
    ENNReal.div_le_div_right (by exact_mod_cast hj) (r j)

end Ring

end MvPolynomial
