/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.ThreeFourOne

/-!
# Admissible cosine polynomials

A cosine polynomial `P(θ) = Σ_{k ≤ n} a_k cos (k θ)` is *admissible* when its coefficients are
nonnegative, `a₀ < a₁`, and `P(θ) ≥ 0` for every real `θ`. This is the degree-at-most-`n`
variant of Mossinghoff and Trudgian's class `P_n` of nonnegative cosine polynomials of degree
`n`: the index `n` bounds the degree, and `a n` may vanish. These polynomials are the input of
the classical de la Vallée Poussin argument for zero-free regions; `3 + 4 cos θ + cos 2θ` is the
basic example.

The nonnegativity clause is stated through `TauCeti.IsNonnegativeTrigonometricCombination`, with
frequencies `k` and weights `a k`, so the transfer lemmas proved there for the closed unit disk
and for logarithms of Euler factors apply directly. The cosine-polynomial API itself lives next
to that predicate, as `TauCeti.cosinePolynomial`.

## Main declarations

* `TauCeti.ExplicitBounds.IsAdmissibleCosinePolynomial n a`: the coefficient vector `a`, supported
  on `k ≤ n`, defines an admissible cosine polynomial of degree at most `n`.
* `isAdmissibleCosinePolynomial_iff`: admissibility in terms of real-angle nonnegativity.
* `IsAdmissibleCosinePolynomial.cosinePolynomial_nonneg`, `.alternating_sum_nonneg`: `P ≥ 0`,
  in particular `P(π) = Σ_{k ≤ n} (-1)^k a k ≥ 0`.
* `IsAdmissibleCosinePolynomial.smul` and `.mono`: scaling by a positive constant and raising the
  index bound preserve admissibility.
* `IsAdmissibleCosinePolynomial.one_le`: the index bound of an admissible polynomial satisfies
  `1 ≤ n`.
* `isAdmissibleCosinePolynomial_threeFourOne`: the `3-4-1` coefficients
  `TauCeti.LSeries.threeFourOneCoeff` are admissible.

Positivity on the closed unit disk and its Euler-product form need only nonnegativity of the
cosine polynomial: apply `TauCeti.re_sum_nonneg_of_cosinePolynomial_nonneg` and
`TauCeti.sum_re_neg_log_one_sub_nonneg_of_cosinePolynomial_nonneg` to
`IsAdmissibleCosinePolynomial.cosinePolynomial_nonneg`.

## References

* M. J. Mossinghoff and T. S. Trudgian, *Nonnegative trigonometric polynomials and a zero-free
  region for the Riemann zeta-function*, J. Number Theory 157 (2015), 329–349.
-/

public section

namespace TauCeti.ExplicitBounds

open Complex Finset

noncomputable section

/-- The coefficient vector `a`, supported on `k ≤ n`, defines an *admissible cosine polynomial*
`P(θ) = Σ_{k ≤ n} a k * cos (k * θ)` of degree at most `n`: the coefficients are nonnegative,
`a 0 < a 1`, and `P` is nonnegative, stated as nonnegativity of the trigonometric combination
with frequencies `k` and weights `a k` on the unit circle. -/
structure IsAdmissibleCosinePolynomial (n : ℕ) (a : ℕ → ℝ) : Prop where
  /-- The coefficients of index at most `n` are nonnegative. -/
  nonneg : ∀ k ≤ n, 0 ≤ a k
  /-- The coefficients of index greater than `n` vanish. -/
  eq_zero : ∀ k, n < k → a k = 0
  /-- The constant coefficient is smaller than the first one. -/
  lt : a 0 < a 1
  /-- The cosine polynomial is nonnegative on the unit circle. -/
  isNonnegativeTrigonometricCombination :
    IsNonnegativeTrigonometricCombination (range (n + 1)) (fun k ↦ (a k : ℂ)) id

/-- Admissibility in terms of the coefficient conditions and nonnegativity of the cosine
polynomial at every real `θ`. -/
theorem isAdmissibleCosinePolynomial_iff {n : ℕ} {a : ℕ → ℝ} :
    IsAdmissibleCosinePolynomial n a ↔
      (∀ k ≤ n, 0 ≤ a k) ∧ (∀ k, n < k → a k = 0) ∧ a 0 < a 1 ∧
        ∀ θ : ℝ, 0 ≤ cosinePolynomial n a θ :=
  ⟨fun h ↦ ⟨h.nonneg, h.eq_zero, h.lt,
      isNonnegativeTrigonometricCombination_range_iff.1 h.isNonnegativeTrigonometricCombination⟩,
    fun ⟨h₀, h₁, h₂, h₃⟩ ↦ ⟨h₀, h₁, h₂, isNonnegativeTrigonometricCombination_range_iff.2 h₃⟩⟩

namespace IsAdmissibleCosinePolynomial

variable {n : ℕ} {a : ℕ → ℝ}

/-- An admissible cosine polynomial is nonnegative at every real `θ`. -/
theorem cosinePolynomial_nonneg (h : IsAdmissibleCosinePolynomial n a) (θ : ℝ) :
    0 ≤ cosinePolynomial n a θ :=
  isNonnegativeTrigonometricCombination_range_iff.1 h.isNonnegativeTrigonometricCombination θ

/-- An admissible cosine polynomial has a nonnegative alternating coefficient sum, its value at
`π`. -/
theorem alternating_sum_nonneg (h : IsAdmissibleCosinePolynomial n a) :
    0 ≤ ∑ k ∈ range (n + 1), (-1) ^ k * a k := by
  simpa only [cosinePolynomial_apply_pi] using h.cosinePolynomial_nonneg Real.pi

/-- The index bound of an admissible cosine polynomial satisfies `1 ≤ n`: for `n = 0` the
vanishing clause forces `a 1 = 0`, against `0 ≤ a 0 < a 1`. -/
theorem one_le (h : IsAdmissibleCosinePolynomial n a) : 1 ≤ n := by
  by_contra! hn
  have h₀ := h.nonneg 0 (Nat.zero_le n)
  have h₁ := h.eq_zero 1 (by omega)
  linarith [h.lt]

/-- Scaling by a positive constant preserves admissibility. -/
theorem smul (h : IsAdmissibleCosinePolynomial n a) {c : ℝ} (hc : 0 < c) :
    IsAdmissibleCosinePolynomial n (c • a) := by
  refine isAdmissibleCosinePolynomial_iff.2 ⟨fun k hk ↦ ?_, fun k hk ↦ ?_, ?_, fun θ ↦ ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using mul_nonneg hc.le (h.nonneg k hk)
  · simp only [Pi.smul_apply, smul_eq_mul, h.eq_zero k hk, mul_zero]
  · simpa only [Pi.smul_apply, smul_eq_mul] using mul_lt_mul_of_pos_left h.lt hc
  · rw [cosinePolynomial_smul]
    exact mul_nonneg hc.le (h.cosinePolynomial_nonneg θ)

/-- Raising the index bound preserves admissibility. -/
theorem mono (h : IsAdmissibleCosinePolynomial n a) {m : ℕ} (hnm : n ≤ m) :
    IsAdmissibleCosinePolynomial m a := by
  refine isAdmissibleCosinePolynomial_iff.2
    ⟨fun k _ ↦ ?_, fun k hk ↦ h.eq_zero k (hnm.trans_lt hk), h.lt, fun θ ↦ ?_⟩
  · rcases le_or_gt k n with hk | hk
    · exact h.nonneg k hk
    · exact (h.eq_zero k hk).ge
  · rw [cosinePolynomial_eq_of_le hnm fun k hk _ ↦ h.eq_zero k hk]
    exact h.cosinePolynomial_nonneg θ

end IsAdmissibleCosinePolynomial

/-! ### Examples -/

/-- `3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)²` is admissible. -/
theorem isAdmissibleCosinePolynomial_threeFourOne :
    IsAdmissibleCosinePolynomial 2 LSeries.threeFourOneCoeff where
  nonneg k hk := by interval_cases k <;> norm_num
  eq_zero _ hk := LSeries.threeFourOneCoeff_eq_zero hk
  lt := by norm_num
  isNonnegativeTrigonometricCombination z hz := by
    have h := LSeries.isNonnegativeTrigonometricCombination_threeFourOne z hz
    simp only [trigonometricCombination_def, LSeries.threeFourOneWeight_apply] at h
    rwa [trigonometricCombination_def, ← Fin.sum_univ_eq_sum_range
      (fun k ↦ ((LSeries.threeFourOneCoeff k : ℂ) * z ^ id k).re)]

/-- The coefficients `(1, 2)` satisfy `a₀ < a₁` but give `1 + 2 cos θ`, negative at `π`: the
coefficient conditions do not imply nonnegativity. -/
theorem not_isAdmissibleCosinePolynomial_one_two :
    ¬ IsAdmissibleCosinePolynomial 1 (fun k ↦ [1, 2].getD k 0) := fun h ↦ by
  have := h.alternating_sum_nonneg
  norm_num [sum_range_succ] at this

/-- The coefficients `(1, 1)` give the nonnegative `1 + cos θ` but fail `a₀ < a₁`. -/
theorem not_isAdmissibleCosinePolynomial_one_one :
    ¬ IsAdmissibleCosinePolynomial 1 (fun k ↦ [1, 1].getD k 0) := fun h ↦ by
  simpa using h.lt

end

end TauCeti.ExplicitBounds
