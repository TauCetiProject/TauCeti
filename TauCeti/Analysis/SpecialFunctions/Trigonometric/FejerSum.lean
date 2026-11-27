/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Complex.Trigonometric
import TauCeti.Algebra.BigOperators.Field
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.NonnegCombination

/-!
# Fejér sums on the closed unit disc

For `‖u‖ = 1`, **Fejér's identity**
`‖∑_{k=0}^J u ^ k‖² = J + 1 + 2 ∑_{j=1}^J (J + 1 - j) re (u ^ j)` shows that the trigonometric
combination `1 + 2 ∑_{j=1}^J (1 - j/(J+1)) re (w ^ j)` is nonnegative on the unit circle, and
`TauCeti.trigonometricCombination_nonneg_of_boundary` extends this to the closed unit disc:
`∑_{j=1}^J (1 - j/(J+1)) re (w ^ j) ≥ -1/2` there (**Fejér positivity**).

Writing `cos jθ re (w ^ j)` as the mean of `re ((w e^{± iθ}) ^ j)`, the sums with the weights
`c_j = (1 - j/(J+1)) (1 + cos jθ)`, `1 ≤ j ≤ J`, satisfy `∑_j c_j re (w ^ j) ≥ -1` on the closed
disc and `∑_j c_j cos jθ ≥ J/4 - 3/4`, the value at `w = e^{iθ}`. These two bounds, with
`0 ≤ c_j ≤ 2`, are what the power-sum inequality with a dominant term in
`TauCeti.Analysis.Complex.DominantPowerSum` takes from Fejér's kernel.

## Main results

* `Complex.sq_norm_sum_range_pow_of_norm_eq_one`: Fejér's identity on the unit circle.
* `Complex.neg_one_div_two_le_sum_one_sub_div_mul_re_pow`: Fejér positivity on the closed disc.
* `Complex.re_mul_exp_pow_add_re_mul_exp_neg_pow`: `re ((w e^{iθ}) ^ j) + re ((w e^{-iθ}) ^ j)`
  is `2 cos (j θ) re (w ^ j)`.
* `Real.one_sub_div_mul_one_add_cos_nonneg`, `Real.one_sub_div_mul_one_add_cos_le_two`: the
  weights `c_j` lie in `[0, 2]`.
* `Complex.neg_one_le_sum_one_sub_div_mul_one_add_cos_mul_re_pow`,
  `Real.div_four_sub_le_sum_one_sub_div_mul_one_add_cos_mul_cos`: the two bounds for the
  weighted sums.

The Fejér kernel on the circle, `TauCeti.fejerKernel` in `TauCeti.Analysis.Fourier.Fejer`, is
the normalized squared norm of a sum of Fourier monomials on `AddCircle T`, expanded there as a
double sum. Fejér's identity is stated here for a complex number of modulus one, with the
triangular weights and real parts that the nonnegativity criterion
`TauCeti.IsNonnegativeTrigonometricCombination` takes.

## References

* L. Alpöge's Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis>, is the source of the two bounds
  for the weights `c_j`.
* L. Fejér, *Untersuchungen über Fouriersche Reihen*, Math. Ann. 58 (1904), 51–69.
-/

public section

open Finset Complex

/-- The Fejér weight `(1 - j/(J+1)) (1 + cos jθ)` is nonnegative for `j ≤ J + 1`. -/
theorem Real.one_sub_div_mul_one_add_cos_nonneg {j J : ℕ} (hj : j ≤ J + 1) (θ : ℝ) :
    0 ≤ (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * θ)) := by
  have : (j : ℝ) / (J + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hj
  exact mul_nonneg (by linarith) (by linarith [Real.neg_one_le_cos (j * θ)])

/-- The Fejér weight `(1 - j/(J+1)) (1 + cos jθ)` is at most `2`. -/
theorem Real.one_sub_div_mul_one_add_cos_le_two (j J : ℕ) (θ : ℝ) :
    (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * θ)) ≤ 2 := by
  have h₀ : 0 ≤ 1 + Real.cos (j * θ) := by linarith [Real.neg_one_le_cos (j * θ)]
  have h₂ : 1 + Real.cos (j * θ) ≤ 2 := by linarith [Real.cos_le_one (j * θ)]
  have h₁ : 1 - j / (J + 1 : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ j / (J + 1) := by positivity
    linarith
  simpa using mul_le_mul h₁ h₂ h₀ zero_le_one

namespace Complex

/-- The real part of `∑_{k<n} u ^ (k + 1)` is `∑_{j=1}^n re (u ^ j)`. -/
private theorem re_sum_range_pow_succ (u : ℂ) (n : ℕ) :
    (∑ k ∈ range n, u ^ (k + 1)).re = ∑ j ∈ Icc 1 n, (u ^ j).re := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_re, ih, sum_Icc_succ_top (by omega)]

/-- **Fejér's identity.** For `‖u‖ = 1`, the squared norm of `1 + u + ⋯ + u ^ J` is
`J + 1 + 2 ∑_{j=1}^J (J + 1 - j) re (u ^ j)`. -/
theorem sq_norm_sum_range_pow_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) (J : ℕ) :
    ‖∑ k ∈ range (J + 1), u ^ k‖ ^ 2 =
      J + 1 + 2 * ∑ j ∈ Icc 1 J, ((J : ℝ) + 1 - j) * (u ^ j).re := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hS : ∑ k ∈ range (J + 1 + 1), u ^ k = u * ∑ k ∈ range (J + 1), u ^ k + 1 := by
      simp [sum_range_succ' _ (J + 1), mul_sum, pow_succ']
    have hT : ∑ j ∈ Icc 1 (J + 1), (((J + 1 : ℕ) : ℝ) + 1 - j) * (u ^ j).re =
        ∑ j ∈ Icc 1 J, ((J : ℝ) + 1 - j) * (u ^ j).re + ∑ j ∈ Icc 1 (J + 1), (u ^ j).re := by
      rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega) (fun j ↦ (u ^ j).re),
        ← add_assoc, ← sum_add_distrib]
      push_cast
      congr 1
      · exact sum_congr rfl fun j _ ↦ by ring
      · ring
    have hu' : u * ∑ k ∈ range (J + 1), u ^ k = ∑ k ∈ range (J + 1), u ^ (k + 1) := by
      simp [mul_sum, pow_succ']
    -- Expand `‖v + 1‖² = ‖v‖² + 2 re v + 1` for `v = u * ∑_{k ≤ J} u ^ k`, of norm `‖∑ u ^ k‖`.
    have hv (v : ℂ) : ‖v + 1‖ ^ 2 = ‖v‖ ^ 2 + 1 + 2 * v.re := by
      simp only [Complex.sq_norm, normSq_add, map_one, mul_one]
    calc ‖∑ k ∈ range (J + 1 + 1), u ^ k‖ ^ 2
        = ‖∑ k ∈ range (J + 1), u ^ k‖ ^ 2 + 1 + 2 * (∑ k ∈ range (J + 1), u ^ (k + 1)).re := by
          rw [hS, hv, norm_mul, hu, one_mul, hu']
      _ = _ := by
          rw [ih, re_sum_range_pow_succ, hT]
          push_cast
          ring

/-- **Fejér positivity on the closed disc.** For `‖w‖ ≤ 1`,
`∑_{j=1}^J (1 - j/(J+1)) re (w ^ j) ≥ -1/2`. -/
theorem neg_one_div_two_le_sum_one_sub_div_mul_re_pow (J : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    -1 / 2 ≤ ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * (w ^ j).re := by
  -- `1 + 2 ∑_j (1 - j/(J+1)) re (z ^ j)` is a trigonometric combination of frequencies `0, …, J`.
  let c : ℕ → ℂ := fun k ↦ if k = 0 then 1 else ((2 * (1 - k / (J + 1 : ℝ)) : ℝ) : ℂ)
  have hc (z : ℂ) : TauCeti.trigonometricCombination (insert 0 (Icc 1 J)) c id z =
      1 + 2 * ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * (z ^ j).re := by
    rw [TauCeti.trigonometricCombination_def, sum_insert (by simp), mul_sum]
    refine congrArg₂ (· + ·) (by simp [c]) (sum_congr rfl fun j hj ↦ ?_)
    have hj₀ : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
    simp only [c, id, hj₀, ↓reduceIte, re_ofReal_mul, mul_assoc]
  -- It is nonnegative on the unit circle, where `(J + 1)` times it is `‖1 + u + ⋯ + u ^ J‖²`,
  -- hence on the closed disc.
  have key := TauCeti.trigonometricCombination_nonneg_of_boundary (s := insert 0 (Icc 1 J))
    (c := c) (m := id) (fun u hu ↦ ?_) hw
  · rw [hc] at key
    linarith
  have hmul : (J + 1 : ℝ) * TauCeti.trigonometricCombination (insert 0 (Icc 1 J)) c id u =
      ‖∑ k ∈ range (J + 1), u ^ k‖ ^ 2 := by
    rw [hc, sq_norm_sum_range_pow_of_norm_eq_one hu, mul_add, mul_one, mul_left_comm, mul_sum]
    congr 2
    exact sum_congr rfl fun j _ ↦ by field_simp
  exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < J + 1)).mp (by rw [hmul]; positivity)

/-- The real parts of `(w e^{iθ}) ^ j` and `(w e^{-iθ}) ^ j` add up to `2 cos (j θ) re (w ^ j)`. -/
theorem re_mul_exp_pow_add_re_mul_exp_neg_pow (θ : ℝ) (w : ℂ) (j : ℕ) :
    ((w * exp (θ * I)) ^ j).re + ((w * exp (-θ * I)) ^ j).re =
      2 * Real.cos (j * θ) * (w ^ j).re := by
  have h : (w * exp (θ * I)) ^ j + (w * exp (-θ * I)) ^ j =
      w ^ j * ((2 * Real.cos (j * θ) : ℝ) : ℂ) := by
    rw [mul_pow, mul_pow, ← mul_add, ← exp_natCast_mul, ← exp_natCast_mul]
    push_cast
    rw [two_cos]
    ring_nf
  rw [← add_re, h, re_mul_ofReal, mul_comm]

/-- The Fejér-weighted cosine sum is the Fejér sum at `w` plus half the Fejér sums at
`w e^{± iθ}`. -/
private theorem sum_fejer_cos_eq (J : ℕ) (θ : ℝ) (w : ℂ) :
    ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * θ)) * (w ^ j).re =
      ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * (w ^ j).re +
        (∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * ((w * exp (θ * I)) ^ j).re) / 2 +
        (∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * ((w * exp (-θ * I)) ^ j).re) / 2 := by
  simp only [sum_div, ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  linear_combination -(1 - j / (J + 1 : ℝ)) / 2 * re_mul_exp_pow_add_re_mul_exp_neg_pow θ w j

/-- **Fejér weights, the disc bound.** For `‖w‖ ≤ 1` and real `θ`,
`∑_{j=1}^J (1 - j/(J+1)) (1 + cos jθ) re (w ^ j) ≥ -1`. -/
theorem neg_one_le_sum_one_sub_div_mul_one_add_cos_mul_re_pow (J : ℕ) (θ : ℝ) {w : ℂ}
    (hw : ‖w‖ ≤ 1) :
    -1 ≤ ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * θ)) * (w ^ j).re := by
  have h₁ : ‖w * exp (θ * I)‖ ≤ 1 := by rwa [norm_mul, norm_exp_ofReal_mul_I, mul_one]
  have h₂ : ‖w * exp (-θ * I)‖ ≤ 1 := by
    rwa [norm_mul, ← ofReal_neg, norm_exp_ofReal_mul_I, mul_one]
  rw [sum_fejer_cos_eq]
  linarith [neg_one_div_two_le_sum_one_sub_div_mul_re_pow J hw,
    neg_one_div_two_le_sum_one_sub_div_mul_re_pow J h₁,
    neg_one_div_two_le_sum_one_sub_div_mul_re_pow J h₂]

/-- The Fejér weights `1 - j/(J+1)`, `1 ≤ j ≤ J`, sum to `J/2`. -/
private theorem sum_Icc_one_sub_div (J : ℕ) :
    ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) = J / 2 := by
  -- Gauss's sum `Finset.sum_range_natCast` over `range (J + 1) = Icc 0 J`, whose term at `0`
  -- vanishes.
  have h := sum_range_natCast (K := ℝ) (J + 1)
  rw [Nat.range_succ_eq_Icc_zero, ← add_sum_Ioc_eq_sum_Icc J.zero_le,
    ← Icc_add_one_left_eq_Ioc] at h
  simp only [Nat.cast_zero, zero_add] at h
  rw [sum_sub_distrib, ← sum_div, h, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  field_simp
  push_cast
  ring

/-- **Fejér weights, the value at `e^{iθ}`.**
`∑_{j=1}^J (1 - j/(J+1)) (1 + cos jθ) cos jθ ≥ J/4 - 3/4`. -/
theorem _root_.Real.div_four_sub_le_sum_one_sub_div_mul_one_add_cos_mul_cos (J : ℕ) (θ : ℝ) :
    (J : ℝ) / 4 - 3 / 4 ≤
      ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * θ)) * Real.cos (j * θ) := by
  have h₁ : ‖exp (θ * I) * exp (θ * I)‖ ≤ 1 := by rw [norm_mul, norm_exp_ofReal_mul_I]; simp
  have h₀ : exp (θ * I) * exp (-θ * I) = 1 := by rw [← exp_add]; simp
  have hsum : ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * θ)) * Real.cos (j * θ) =
      ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * θ)) * (exp (θ * I) ^ j).re :=
    sum_congr rfl fun j _ ↦ by rw [re_exp_ofReal_mul_I_pow]
  rw [hsum, sum_fejer_cos_eq, h₀]
  simp only [one_pow, one_re, mul_one, sum_Icc_one_sub_div]
  linarith [neg_one_div_two_le_sum_one_sub_div_mul_re_pow J (norm_exp_ofReal_mul_I θ).le,
    neg_one_div_two_le_sum_one_sub_div_mul_re_pow J h₁]

end Complex
