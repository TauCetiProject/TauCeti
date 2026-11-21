/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.AbsMax

/-!
# Nonnegative trigonometric combinations

This file packages finite trigonometric combinations that are nonnegative on the complex unit
circle. It also transfers their pointwise nonnegativity to the closed unit disk and the Taylor
series of `-log (1 - z)`, giving a reusable logarithmic inequality.

## Main declarations

* `TauCeti.trigonometricCombination` is the real part of a finite weighted sum of powers.
* `TauCeti.trigonometricCombination_eq_re_sum` rewrites it as the real part of one sum.
* `TauCeti.IsNonnegativeTrigonometricCombination` asserts nonnegativity on the unit circle.
* `TauCeti.isNonnegativeTrigonometricCombination_ofReal_iff`: for real weights, this is
  nonnegativity of the cosine sum `θ ↦ Σ_i a_i cos (m_i θ)` at every real `θ`.
* `TauCeti.cosinePolynomial n a θ` is the cosine polynomial `Σ_{k ≤ n} a_k cos (k θ)`, with
  recursion in `n`, its values at `0` and `π`, its behaviour under scaling and zero padding, and
  `TauCeti.isNonnegativeTrigonometricCombination_range_iff`.
* `TauCeti.re_sum_nonneg_of_cosinePolynomial_nonneg` and
  `TauCeti.sum_re_neg_log_one_sub_nonneg_of_cosinePolynomial_nonneg` transfer nonnegativity of a
  cosine polynomial to the closed unit disk and to logarithms.
* `TauCeti.trigonometricCombination_nonneg_of_boundary` extends this nonnegativity to the closed
  unit disk.
* `TauCeti.sum_re_neg_log_one_sub_nonneg` transfers boundary nonnegativity to logarithms in the
  open unit disk.

## Provenance

The logarithmic transfer generalizes the private lemma `re_log_comb_nonneg'` in the
`DirichletCharacter` namespace of Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, due to Michael Stoll and David Loeffler, from
the fixed `3-4-1` weights to an arbitrary finite nonnegative combination.
-/

public section

namespace TauCeti

open Complex

noncomputable section

variable {ι : Type*}

/-- The real trigonometric combination with complex weights `c` and frequencies `m`, evaluated at
a complex phase `z`. On the unit circle `z = exp (θ * I)`, each term `(c i * z ^ m i).re` is a
linear combination of `cos (m i * θ)` and `sin (m i * θ)`. -/
def trigonometricCombination
    (s : Finset ι) (c : ι → ℂ) (m : ι → ℕ) (z : ℂ) : ℝ :=
  ∑ i ∈ s, (c i * z ^ m i).re

/-- The defining finite-sum formula for `trigonometricCombination`. -/
theorem trigonometricCombination_def (s : Finset ι) (c : ι → ℂ) (m : ι → ℕ) (z : ℂ) :
    trigonometricCombination s c m z = ∑ i ∈ s, (c i * z ^ m i).re := (rfl)

/-- A trigonometric combination is the real part of the weighted sum of powers. -/
theorem trigonometricCombination_eq_re_sum (s : Finset ι) (c : ι → ℂ) (m : ι → ℕ) (z : ℂ) :
    trigonometricCombination s c m z = (∑ i ∈ s, c i * z ^ m i).re := by
  rw [trigonometricCombination_def, re_sum]

/-- At `z = exp (θ * I)`, a trigonometric combination with real weights `a` is the cosine sum
`Σ_i a i * cos (m i * θ)`. -/
theorem trigonometricCombination_ofReal_exp_mul_I
    (s : Finset ι) (a : ι → ℝ) (m : ι → ℕ) (θ : ℝ) :
    trigonometricCombination s (fun i ↦ (a i : ℂ)) m (exp (θ * I)) =
      ∑ i ∈ s, a i * Real.cos (m i * θ) := by
  rw [trigonometricCombination_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hexp : exp (θ * I) ^ m i = exp (((m i * θ : ℝ) : ℂ) * I) := by
    simpa [circleMap_zero] using circleMap_zero_pow (m i) 1 θ
  rw [hexp, re_ofReal_mul, exp_ofReal_mul_I_re]

/-- The assertion that a finite trigonometric combination is nonnegative at every complex phase
on the unit circle. -/
abbrev IsNonnegativeTrigonometricCombination
    (s : Finset ι) (c : ι → ℂ) (m : ι → ℕ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ trigonometricCombination s c m z

/-- A trigonometric combination with real weights is nonnegative on the unit circle if and only
if the cosine sum `Σ_i a i * cos (m i * θ)` is nonnegative at every real `θ`. -/
theorem isNonnegativeTrigonometricCombination_ofReal_iff
    {s : Finset ι} {a : ι → ℝ} {m : ι → ℕ} :
    IsNonnegativeTrigonometricCombination s (fun i ↦ (a i : ℂ)) m ↔
      ∀ θ : ℝ, 0 ≤ ∑ i ∈ s, a i * Real.cos (m i * θ) := by
  refine ⟨fun h θ ↦ ?_, fun h z hz ↦ ?_⟩
  · rw [← trigonometricCombination_ofReal_exp_mul_I]
    exact h _ (norm_exp_ofReal_mul_I θ)
  · obtain ⟨θ, rfl⟩ := (Complex.norm_eq_one_iff z).1 hz
    rw [trigonometricCombination_ofReal_exp_mul_I]
    exact h θ

variable {s : Finset ι} {c : ι → ℂ} {m : ι → ℕ}

/-- Nonnegativity of a trigonometric combination on the unit circle extends to the closed unit
disk. -/
theorem trigonometricCombination_nonneg_of_boundary
    (h : IsNonnegativeTrigonometricCombination s c m) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ trigonometricCombination s c m z := by
  -- Apply the maximum modulus principle on the unit disk to `exp (-∑ i ∈ s, c i * w ^ m i)`,
  -- whose norm is `Real.exp (-trigonometricCombination s c m w)`.
  let f : ℂ → ℂ := fun w ↦ exp (-∑ i ∈ s, c i * w ^ m i)
  have hf (w : ℂ) : ‖f w‖ ≤ 1 ↔ 0 ≤ trigonometricCombination s c m w := by
    simp [f, Complex.norm_exp, trigonometricCombination_eq_re_sum]
  refine (hf z).1 <| Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball (x := 0) (r := 1))
    (by fun_prop : Differentiable ℂ f).diffContOnCl (fun w hw ↦ (hf w).2 (h w ?_)) ?_
  · rwa [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hw
  · rwa [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall_zero_iff]

/-- Unit-circle nonnegativity of a trigonometric combination transfers to the Taylor series of
`-log (1 - w)` at the points `w = a * z ^ m i`, for `0 ≤ a < 1` and `z` in the closed unit
disk. -/
theorem sum_re_neg_log_one_sub_nonneg
    (h : IsNonnegativeTrigonometricCombination s c m)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ ∑ i ∈ s, (c i * -log (1 - a * z ^ m i)).re := by
  have haz (i : ι) : ‖(a : ℂ) * z ^ m i‖ < 1 := by
    rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg ha₀]
    exact (mul_le_of_le_one_right ha₀ (pow_le_one₀ (norm_nonneg z) hz)).trans_lt ha₁
  have hsum : HasSum
      (fun n : ℕ ↦ ∑ i ∈ s, (c i * (((a : ℂ) * z ^ m i) ^ n / n)).re)
      (∑ i ∈ s, (c i * -log (1 - a * z ^ m i)).re) :=
    hasSum_sum fun i _ ↦ Complex.hasSum_re ((hasSum_taylorSeries_neg_log (haz i)).mul_left (c i))
  rw [← hsum.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  have hrewrite : ∑ i ∈ s, (c i * (((a : ℂ) * z ^ m i) ^ n / n)).re =
      (a ^ n / n) * trigonometricCombination s c m (z ^ n) := by
    simp only [trigonometricCombination_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← re_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [hrewrite]
  exact mul_nonneg (by positivity) <| trigonometricCombination_nonneg_of_boundary h <| by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) hz

/-! ### Cosine polynomials -/

/-- The cosine polynomial `Σ_{k ≤ n} a k * cos (k * θ)`. -/
def cosinePolynomial (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k * Real.cos (k * θ)

/-- The defining formula for `cosinePolynomial`. -/
theorem cosinePolynomial_def (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    cosinePolynomial n a θ = ∑ k ∈ Finset.range (n + 1), a k * Real.cos (k * θ) := (rfl)

/-- The trigonometric combination with weights `a k` and frequencies `k` is nonnegative on the
unit circle if and only if the cosine polynomial is nonnegative at every real `θ`. -/
theorem isNonnegativeTrigonometricCombination_range_iff {n : ℕ} {a : ℕ → ℝ} :
    IsNonnegativeTrigonometricCombination (Finset.range (n + 1)) (fun k ↦ (a k : ℂ)) id ↔
      ∀ θ : ℝ, 0 ≤ cosinePolynomial n a θ := by
  simp only [cosinePolynomial_def]
  exact isNonnegativeTrigonometricCombination_ofReal_iff

/-- The cosine polynomial with index bound `0` is its constant coefficient. -/
@[simp]
theorem cosinePolynomial_zero (a : ℕ → ℝ) (θ : ℝ) : cosinePolynomial 0 a θ = a 0 := by
  simp [cosinePolynomial_def]

/-- Raising the index bound by one adds the top-frequency term. -/
theorem cosinePolynomial_succ (n : ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    cosinePolynomial (n + 1) a θ =
      cosinePolynomial n a θ + a (n + 1) * Real.cos ((n + 1 : ℕ) * θ) := by
  rw [cosinePolynomial_def, cosinePolynomial_def]
  exact Finset.sum_range_succ _ _

/-- The value of a cosine polynomial at `0` is the sum of its coefficients. -/
@[simp]
theorem cosinePolynomial_apply_zero (n : ℕ) (a : ℕ → ℝ) :
    cosinePolynomial n a 0 = ∑ k ∈ Finset.range (n + 1), a k := by
  simp [cosinePolynomial_def]

/-- The value of a cosine polynomial at `π` is the alternating sum of its coefficients. -/
@[simp]
theorem cosinePolynomial_apply_pi (n : ℕ) (a : ℕ → ℝ) :
    cosinePolynomial n a Real.pi = ∑ k ∈ Finset.range (n + 1), (-1) ^ k * a k := by
  rw [cosinePolynomial_def]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [Real.cos_nat_mul_pi, mul_comm]

/-- Scaling the coefficients scales the cosine polynomial. -/
@[simp]
theorem cosinePolynomial_smul (n : ℕ) (c : ℝ) (a : ℕ → ℝ) (θ : ℝ) :
    cosinePolynomial n (c • a) θ = c * cosinePolynomial n a θ := by
  simp only [cosinePolynomial_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Raising the index bound from `n` to `m` does not change the cosine polynomial when the added
coefficients vanish. -/
theorem cosinePolynomial_eq_of_le {n m : ℕ} {a : ℕ → ℝ} (hnm : n ≤ m)
    (ha : ∀ k, n < k → k ≤ m → a k = 0) (θ : ℝ) :
    cosinePolynomial m a θ = cosinePolynomial n a θ := by
  rw [cosinePolynomial_def, cosinePolynomial_def]
  refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k hkm hkn ↦ ?_).symm
  rw [Finset.mem_range] at hkm hkn
  rw [ha k (by omega) (by omega), zero_mul]

/-- If the cosine polynomial is nonnegative, the polynomial `Σ_{k ≤ n} a k z^k` has nonnegative
real part on the closed unit disk. -/
theorem re_sum_nonneg_of_cosinePolynomial_nonneg {n : ℕ} {a : ℕ → ℝ}
    (h : ∀ θ : ℝ, 0 ≤ cosinePolynomial n a θ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ (∑ k ∈ Finset.range (n + 1), (a k : ℂ) * z ^ k).re :=
  trigonometricCombination_eq_re_sum _ _ _ z ▸ trigonometricCombination_nonneg_of_boundary
    (isNonnegativeTrigonometricCombination_range_iff.2 h) hz

/-- The Euler-product form of cosine-polynomial nonnegativity: for `0 ≤ r < 1` and `‖z‖ ≤ 1`,
`Σ_{k ≤ n} a k Re (-log (1 - r z^k)) ≥ 0`. -/
theorem sum_re_neg_log_one_sub_nonneg_of_cosinePolynomial_nonneg {n : ℕ} {a : ℕ → ℝ}
    (h : ∀ θ : ℝ, 0 ≤ cosinePolynomial n a θ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) {z : ℂ}
    (hz : ‖z‖ ≤ 1) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), a k * (-log (1 - r * z ^ k)).re := by
  simpa [re_ofReal_mul] using
    sum_re_neg_log_one_sub_nonneg (isNonnegativeTrigonometricCombination_range_iff.2 h) hr₀ hr₁ hz

end

end TauCeti
