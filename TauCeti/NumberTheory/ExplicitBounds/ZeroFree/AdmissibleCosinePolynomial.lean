/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.ThreeFourOne
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Admissible cosine polynomials

A cosine polynomial `P(θ) = Σ_{k ≤ n} a_k cos (k θ)` is *admissible* when its coefficients are
nonnegative, `a₀ < a₁`, and `P(θ) ≥ 0` for every real `θ`. This is Mossinghoff and Trudgian's
class `P_n` of nonnegative even cosine polynomials of degree `n`, the input of the classical
de la Vallée Poussin argument for zero-free regions; the polynomial `3 + 4 cos θ + cos 2θ` is the
basic example.

The nonnegativity clause is stated through Tau Ceti's
`TauCeti.IsNonnegativeTrigonometricCombination`, with frequencies `k` and weights `a k`, so the
transfer lemmas proved there for the closed unit disk and for logarithms of Euler factors apply
directly.

## Main declarations

* `TauCeti.ExplicitBounds.IsAdmissibleCosinePolynomial n a`: the coefficient vector `a`, supported
  on `k ≤ n`, defines an admissible cosine polynomial of degree at most `n`.
* `TauCeti.ExplicitBounds.cosinePolynomial n a θ`: the value `Σ_{k ≤ n} a k * cos (k * θ)`.
* `IsAdmissibleCosinePolynomial.cosinePolynomial_nonneg`, `.cosinePolynomial_pi_nonneg`: `P ≥ 0`,
  in particular `P(π) = Σ_{k ≤ n} (-1)^k a k ≥ 0`.
* `IsAdmissibleCosinePolynomial.smul` and `.mono`: scaling by a positive constant and appending
  zero coefficients preserve admissibility.
* `IsAdmissibleCosinePolynomial.one_le`: an admissible polynomial has degree `n ≥ 1`.
* `IsAdmissibleCosinePolynomial.re_sum_nonneg` and `.sum_re_neg_log_one_sub_nonneg`: positivity
  on the closed unit disk and its Euler-product form.
* `isAdmissibleCosinePolynomial_threeFourOne`: `(3, 4, 1)` is admissible.

## References

* M. J. Mossinghoff and T. S. Trudgian, *Nonnegative trigonometric polynomials and a zero-free
  region for the Riemann zeta-function*, J. Number Theory 157 (2015), 329–349.

This file implements §0.5 of the `ExplicitZetaBounds` roadmap of TauCetiRoadmap.
-/

public section

namespace TauCeti.ExplicitBounds

open Complex Finset

noncomputable section

/-- The coefficient vector `a`, supported on `k ≤ n`, defines an *admissible cosine polynomial*
`P(θ) = Σ_{k ≤ n} a k * cos (k * θ)`: the coefficients are nonnegative, `a 0 < a 1`, and `P` is
nonnegative, stated as nonnegativity of the trigonometric combination with frequencies `k` and
weights `a k` on the unit circle. -/
structure IsAdmissibleCosinePolynomial (n : ℕ) (a : ℕ → ℝ) : Prop where
  /-- The coefficients of degree at most `n` are nonnegative. -/
  nonneg : ∀ k ≤ n, 0 ≤ a k
  /-- The coefficients of degree greater than `n` vanish. -/
  eq_zero : ∀ k, n < k → a k = 0
  /-- The constant coefficient is smaller than the first one. -/
  lt : a 0 < a 1
  /-- The cosine polynomial is nonnegative on the unit circle. -/
  isNonnegativeTrigonometricCombination :
    IsNonnegativeTrigonometricCombination (range (n + 1)) (fun k ↦ (a k : ℂ)) id

/-- The cosine polynomial `Σ_{k ≤ n} a k * cos (k * θ)`. -/
def cosinePolynomial (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), a k * Real.cos (k * θ)

/-- The defining formula for `cosinePolynomial`. -/
theorem cosinePolynomial_def (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    cosinePolynomial n a θ = ∑ k ∈ range (n + 1), a k * Real.cos (k * θ) := (rfl)

/-- At `z = exp (θ * I)` the trigonometric combination with real weights `a k` and frequencies
`k` is the cosine polynomial. -/
theorem trigonometricCombination_exp_mul_I (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    trigonometricCombination (range (n + 1)) (fun k ↦ (a k : ℂ)) id (exp (θ * I)) =
      cosinePolynomial n a θ := by
  rw [trigonometricCombination_def, cosinePolynomial_def]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [id, ← Complex.exp_natCast_mul, re_ofReal_mul, ← mul_assoc, ← ofReal_natCast, ← ofReal_mul,
    exp_ofReal_mul_I_re]

/-- The trigonometric combination with real weights `a k` and frequencies `k` is the real part
of the polynomial `Σ_{k ≤ n} a k z^k`. -/
theorem trigonometricCombination_eq_re_sum (n : ℕ) (a : ℕ → ℝ) (z : ℂ) :
    trigonometricCombination (range (n + 1)) (fun k ↦ (a k : ℂ)) id z =
      (∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k).re := by
  simp [trigonometricCombination_def, re_sum]

/-- The value of a cosine polynomial at `0` is the sum of its coefficients. -/
@[simp]
theorem cosinePolynomial_zero (n : ℕ) (a : ℕ → ℝ) :
    cosinePolynomial n a 0 = ∑ k ∈ range (n + 1), a k := by
  simp [cosinePolynomial_def]

/-- The value of a cosine polynomial at `π` is the alternating sum of its coefficients. -/
theorem cosinePolynomial_pi (n : ℕ) (a : ℕ → ℝ) :
    cosinePolynomial n a Real.pi = ∑ k ∈ range (n + 1), (-1) ^ k * a k := by
  rw [cosinePolynomial_def]
  exact sum_congr rfl fun k _ ↦ by rw [Real.cos_nat_mul_pi, mul_comm]

namespace IsAdmissibleCosinePolynomial

variable {n : ℕ} {a : ℕ → ℝ}

/-- An admissible cosine polynomial is nonnegative at every real `θ`. -/
theorem cosinePolynomial_nonneg (h : IsAdmissibleCosinePolynomial n a) (θ : ℝ) :
    0 ≤ cosinePolynomial n a θ := by
  rw [← trigonometricCombination_exp_mul_I]
  exact h.isNonnegativeTrigonometricCombination _ (norm_exp_ofReal_mul_I θ)

/-- An admissible cosine polynomial has a nonnegative alternating coefficient sum, its value at
`π`. -/
theorem cosinePolynomial_pi_nonneg (h : IsAdmissibleCosinePolynomial n a) :
    0 ≤ ∑ k ∈ range (n + 1), (-1) ^ k * a k :=
  cosinePolynomial_pi n a ▸ h.cosinePolynomial_nonneg Real.pi

/-- An admissible cosine polynomial has degree at least one: for `n = 0` the vanishing clause
forces `a 1 = 0`, against `0 ≤ a 0 < a 1`. -/
theorem one_le (h : IsAdmissibleCosinePolynomial n a) : 1 ≤ n := by
  by_contra! hn
  have h₀ := h.nonneg 0 (Nat.zero_le n)
  have h₁ := h.eq_zero 1 (by omega)
  linarith [h.lt]

/-- Scaling by a positive constant preserves admissibility. -/
theorem smul (h : IsAdmissibleCosinePolynomial n a) {c : ℝ} (hc : 0 < c) :
    IsAdmissibleCosinePolynomial n (c • a) where
  nonneg k hk := mul_nonneg hc.le (h.nonneg k hk)
  eq_zero k hk := by simp [h.eq_zero k hk]
  lt := mul_lt_mul_of_pos_left h.lt hc
  isNonnegativeTrigonometricCombination z hz := by
    have := h.isNonnegativeTrigonometricCombination z hz
    rw [trigonometricCombination_eq_re_sum] at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul, ofReal_mul, mul_assoc, ← mul_sum, re_ofReal_mul]
    exact mul_nonneg hc.le this

/-- Appending zero coefficients preserves admissibility. -/
theorem mono (h : IsAdmissibleCosinePolynomial n a) {m : ℕ} (hnm : n ≤ m) :
    IsAdmissibleCosinePolynomial m a where
  nonneg k _ := by
    rcases le_or_gt k n with hk | hk
    · exact h.nonneg k hk
    · exact (h.eq_zero k hk).ge
  eq_zero k hk := h.eq_zero k (hnm.trans_lt hk)
  lt := h.lt
  isNonnegativeTrigonometricCombination z hz := by
    have := h.isNonnegativeTrigonometricCombination z hz
    have hsum : ∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k =
        ∑ k ∈ range (m + 1), (a k : ℂ) * z ^ k :=
      sum_subset (range_subset_range.2 (by omega)) fun k _ hk ↦ by
        simp [h.eq_zero k (by simpa using hk)]
    rw [trigonometricCombination_eq_re_sum] at this ⊢
    rwa [← hsum]

/-- The polynomial `Σ_{k ≤ n} a k z^k` of an admissible cosine polynomial has nonnegative real
part on the closed unit disk. -/
theorem re_sum_nonneg (h : IsAdmissibleCosinePolynomial n a) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ (∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k).re :=
  trigonometricCombination_eq_re_sum n a z ▸
    trigonometricCombination_nonneg_of_boundary h.isNonnegativeTrigonometricCombination hz

/-- The Euler-product form of positivity: for `0 ≤ r < 1` and `‖z‖ ≤ 1`,
`Σ_{k ≤ n} a k Re (-log (1 - r z^k)) ≥ 0`. -/
theorem sum_re_neg_log_one_sub_nonneg (h : IsAdmissibleCosinePolynomial n a) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ ∑ k ∈ range (n + 1), a k * (-log (1 - r * z ^ k)).re := by
  simpa [re_ofReal_mul] using
    TauCeti.sum_re_neg_log_one_sub_nonneg h.isNonnegativeTrigonometricCombination hr₀ hr₁ hz

end IsAdmissibleCosinePolynomial

/-! ### Examples -/

/-- The coefficient vector `(3, 4, 1)`, extended by zeros. -/
def threeFourOneCoeff : ℕ → ℝ
  | 0 => 3
  | 1 => 4
  | 2 => 1
  | _ + 3 => 0

/-- `3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)²` is admissible. -/
theorem isAdmissibleCosinePolynomial_threeFourOne :
    IsAdmissibleCosinePolynomial 2 threeFourOneCoeff where
  nonneg k hk := by interval_cases k <;> norm_num [threeFourOneCoeff]
  eq_zero k hk := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    rfl
  lt := by norm_num [threeFourOneCoeff]
  isNonnegativeTrigonometricCombination z hz := by
    have := LSeries.isNonnegativeTrigonometricCombination_threeFourOne z hz
    simp only [LSeries.trigonometricCombination_threeFourOne,
      LSeries.threeFourOneCombination_def] at this
    simpa [trigonometricCombination_def, sum_range_succ, threeFourOneCoeff] using this

/-- The coefficients `(1, 2)` satisfy `a₀ < a₁` but give `1 + 2 cos θ`, negative at `π`: the
coefficient conditions do not imply nonnegativity. -/
theorem not_isAdmissibleCosinePolynomial_one_two :
    ¬ IsAdmissibleCosinePolynomial 1 (fun k ↦ [1, 2].getD k 0) := fun h ↦ by
  have := h.cosinePolynomial_pi_nonneg
  norm_num [sum_range_succ] at this

/-- The coefficients `(1, 1)` give the nonnegative `1 + cos θ` but fail `a₀ < a₁`. -/
theorem not_isAdmissibleCosinePolynomial_one_one :
    ¬ IsAdmissibleCosinePolynomial 1 (fun k ↦ [1, 1].getD k 0) := fun h ↦ by
  simpa using h.lt

end

end TauCeti.ExplicitBounds
