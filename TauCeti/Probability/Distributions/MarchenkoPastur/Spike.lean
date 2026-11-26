/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MarchenkoPastur.Companion

/-!
# The secular equation of a spike above the Marchenko–Pastur edge

Let `s = marchenkoPasturCompanion y` be the companion transform of the Marchenko–Pastur law
`MP_y`, from `TauCeti.Probability.Distributions.MarchenkoPastur.Companion`. This file proves the
deterministic facts behind the outlier of the rank-one spiked sample covariance
`T^{1/2} X Xᴴ T^{1/2} / n` with `T = diag(ℓ, 1, …, 1)`. The nonzero eigenvalues of this matrix are
those of a rank-one perturbation, with weight `ℓ`, of the companion matrix of the other rows, and
eigenvalues above the bulk solve a secular equation whose limit is `1 + ℓ s(x) = 0`. Above the
edge `(1 + √y)²` this limiting equation has a solution exactly when `ℓ > 1 + √y`, and the solution
is then `ψ(ℓ) = ℓ (1 + y / (ℓ - 1))`; the sign of `1 + ℓ s(x)` changes there and nowhere else. At
`ψ(ℓ)` the derivative of `s` is `(ℓ - 1)² / (ℓ² ((ℓ - 1)² - y))`, so
`(ℓ ψ(ℓ) s'(ψ(ℓ)))⁻¹ = (1 - y / (ℓ - 1)²) / (1 + y / (ℓ - 1))`, the limiting squared overlap
of the leading sample eigenvector with the spike.

## Main results

* `TauCeti.Probability.one_add_sqrt_sq_lt_mul_one_add_div_sub_one`: the outlier location lies
  above the upper edge.
* `TauCeti.Probability.one_add_mul_marchenkoPasturCompanion_eq_zero_iff`,
  `TauCeti.Probability.one_add_mul_marchenkoPasturCompanion_pos_iff`,
  `TauCeti.Probability.one_add_mul_marchenkoPasturCompanion_neg_iff`: the limiting secular
  equation of a spike and its sign.
* `TauCeti.Probability.marchenkoPasturCompanion_mul_one_add_div_sub_one`: the value `-ℓ⁻¹` of the
  companion transform at the outlier location.
* `TauCeti.Probability.deriv_marchenkoPasturCompanion_mul_one_add_div_sub_one`,
  `TauCeti.Probability.inv_mul_mul_deriv_marchenkoPasturCompanion_mul_one_add_div_sub_one`: the
  derivative at the outlier location and the limiting squared overlap.

## References

* J. Baik, J. W. Silverstein, *Eigenvalues of large sample covariance matrices of spiked
  population models*, J. Multivariate Anal. 97 (2006), 1382–1408.
* F. Benaych-Georges, R. R. Nadakuditi, *The eigenvalues and eigenvectors of finite, low rank
  perturbations of large random matrices*, Adv. Math. 227 (2011), 494–521, §3.1.
* J. Yao, S. Zheng, Z. Bai, *Large Sample Covariance Matrices and High-Dimensional Data Analysis*,
  Cambridge University Press, 2015, Theorems 11.3 and 11.5.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.Probability

variable {y : ℝ≥0} {x : ℝ}

/-- For `ℓ > 1 + √y`, the outlier location `ℓ (1 + y / (ℓ - 1))` lies above the upper edge
`(1 + √y)²` of `MP_y`; the two agree at `ℓ = 1 + √y`. -/
theorem one_add_sqrt_sq_lt_mul_one_add_div_sub_one {ℓ : ℝ} (hℓ : 1 + √(y : ℝ) < ℓ) :
    (1 + √(y : ℝ)) ^ 2 < ℓ * (1 + y / (ℓ - 1)) := by
  have hr := Real.sq_sqrt y.coe_nonneg
  have hu : 0 < ℓ - 1 := by linarith [Real.sqrt_nonneg (y : ℝ)]
  have key : ℓ * (1 + y / (ℓ - 1)) - (1 + √(y : ℝ)) ^ 2 = (ℓ - 1 - √(y : ℝ)) ^ 2 / (ℓ - 1) := by
    field_simp
    linear_combination (-ℓ) * hr
  have : 0 < (ℓ - 1 - √(y : ℝ)) ^ 2 / (ℓ - 1) := div_pos (pow_pos (by linarith) 2) hu
  linarith

/-- For `ℓ > 1 + √y`, the quantity `(ℓ - 1)² - y` is positive. -/
private lemma sub_one_sq_sub_pos {ℓ : ℝ} (hℓ : 1 + √(y : ℝ) < ℓ) : 0 < (ℓ - 1) ^ 2 - y := by
  have hr := Real.sq_sqrt y.coe_nonneg
  nlinarith [Real.sqrt_nonneg (y : ℝ)]

/-- At `s = -ℓ⁻¹` and the outlier location `ψ = ℓ (1 + y / (ℓ - 1))`, the quantity
`2 ψ s + (ψ + 1 - y)` is `((ℓ - 1)² - y) / (ℓ - 1)`. -/
private lemma two_mul_mul_neg_inv_add {ℓ : ℝ} (hℓ0 : ℓ ≠ 0) (hℓ1 : ℓ - 1 ≠ 0) :
    2 * (ℓ * (1 + y / (ℓ - 1))) * -ℓ⁻¹ + (ℓ * (1 + y / (ℓ - 1)) + 1 - y) =
      ((ℓ - 1) ^ 2 - y) / (ℓ - 1) := by
  field_simp
  ring

/-- **The limiting secular equation of a spike.** Above the upper edge of `MP_y`, the equation
`1 + ℓ s(x) = 0` in the companion transform `s` holds exactly when `ℓ > 1 + √y` and
`x = ℓ (1 + y / (ℓ - 1))`. -/
theorem one_add_mul_marchenkoPasturCompanion_eq_zero_iff {ℓ : ℝ}
    (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    1 + ℓ * marchenkoPasturCompanion y x = 0 ↔ 1 + √(y : ℝ) < ℓ ∧ x = ℓ * (1 + y / (ℓ - 1)) := by
  have hq := marchenkoPasturCompanion_quadratic_eq_zero (notMem_support_marchenkoPastur_of_lt hx)
    ((sq_nonneg _).trans_lt hx).ne'
  have hP := two_mul_mul_marchenkoPasturCompanion_add_pos hx
  have hs := marchenkoPasturCompanion_neg hx
  have hlow := neg_inv_one_add_sqrt_lt_marchenkoPasturCompanion hx
  have hr0 := Real.sqrt_nonneg (y : ℝ)
  set s := marchenkoPasturCompanion y x
  constructor
  · intro h
    have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at h
    have hsℓ : s = -ℓ⁻¹ := by field_simp; linear_combination h
    have hℓ : 1 + √(y : ℝ) < ℓ := by
      rw [hsℓ, neg_lt_neg_iff] at hlow
      have hℓpos : 0 < ℓ := by
        by_contra! hℓ'
        have : 0 ≤ -ℓ⁻¹ := neg_nonneg.2 (inv_nonpos.2 hℓ')
        linarith
      exact (inv_lt_inv₀ hℓpos (by positivity)).1 hlow
    have hℓ1 : ℓ - 1 ≠ 0 := by linarith
    refine ⟨hℓ, ?_⟩
    rw [hsℓ] at hq
    field_simp at hq ⊢
    linear_combination -hq
  · rintro ⟨hℓ, rfl⟩
    have hℓ1 : 0 < ℓ - 1 := by linarith
    have hℓ0 : ℓ ≠ 0 := by linarith
    have ht : (ℓ * (1 + y / (ℓ - 1))) * (-ℓ⁻¹ * -ℓ⁻¹) +
        (ℓ * (1 + y / (ℓ - 1)) + 1 - y) * -ℓ⁻¹ + 1 = 0 := by
      field_simp
      ring
    have ht' : 0 < 2 * (ℓ * (1 + y / (ℓ - 1))) * -ℓ⁻¹ + (ℓ * (1 + y / (ℓ - 1)) + 1 - y) := by
      rw [two_mul_mul_neg_inv_add hℓ0 hℓ1.ne']
      exact div_pos (sub_one_sq_sub_pos hℓ) hℓ1
    -- Both `s` and `-ℓ⁻¹` are roots to the right of the midpoint, so they coincide.
    have h : (s - -ℓ⁻¹) * (ℓ * (1 + y / (ℓ - 1)) * (s + -ℓ⁻¹) + (ℓ * (1 + y / (ℓ - 1)) + 1 - y)) =
        0 := by
      linear_combination hq - ht
    rw [sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (by linarith))]
    field_simp
    ring

/-- **The sign of the limiting secular function of a spike.** Above the upper edge of `MP_y`,
`1 + ℓ s(x) > 0` for the companion transform `s` exactly when `ℓ ≤ 1 + √y` or
`x > ℓ (1 + y / (ℓ - 1))`. -/
theorem one_add_mul_marchenkoPasturCompanion_pos_iff {ℓ : ℝ} (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    0 < 1 + ℓ * marchenkoPasturCompanion y x ↔
      ℓ ≤ 1 + √(y : ℝ) ∨ ℓ * (1 + y / (ℓ - 1)) < x := by
  have hs := marchenkoPasturCompanion_neg hx
  have hlow : -1 < (1 + √(y : ℝ)) * marchenkoPasturCompanion y x := by
    have h1 : 0 < 1 + √(y : ℝ) := by positivity
    have h := mul_lt_mul_of_pos_left (neg_inv_one_add_sqrt_lt_marchenkoPasturCompanion hx) h1
    rwa [mul_neg, mul_inv_cancel₀ h1.ne'] at h
  rcases le_or_gt ℓ (1 + √(y : ℝ)) with hℓ | hℓ
  · simp only [hℓ, true_or, iff_true]
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hℓ) hs.le]
  -- Above the threshold, compare with the value `-ℓ⁻¹` at the outlier location.
  have hψ := one_add_sqrt_sq_lt_mul_one_add_div_sub_one hℓ
  have hℓ0 : 0 < ℓ := by linarith [Real.sqrt_nonneg (y : ℝ)]
  have h0 := ((one_add_mul_marchenkoPasturCompanion_eq_zero_iff hψ).2 ⟨hℓ, rfl⟩)
  simp only [not_le.2 hℓ, false_or]
  rw [← strictMonoOn_marchenkoPasturCompanion.lt_iff_lt hψ hx]
  constructor <;> intro h <;> nlinarith

/-- Above the upper edge of `MP_y`, `1 + ℓ s(x) < 0` for the companion transform `s` exactly
when `ℓ > 1 + √y` and `x < ℓ (1 + y / (ℓ - 1))`. -/
theorem one_add_mul_marchenkoPasturCompanion_neg_iff {ℓ : ℝ} (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    1 + ℓ * marchenkoPasturCompanion y x < 0 ↔
      1 + √(y : ℝ) < ℓ ∧ x < ℓ * (1 + y / (ℓ - 1)) := by
  have hpos := one_add_mul_marchenkoPasturCompanion_pos_iff (ℓ := ℓ) hx
  have heq := one_add_mul_marchenkoPasturCompanion_eq_zero_iff (ℓ := ℓ) hx
  constructor
  · intro h
    have h1 : ¬ 0 < 1 + ℓ * marchenkoPasturCompanion y x := by linarith
    have h2 : ¬ 1 + ℓ * marchenkoPasturCompanion y x = 0 := h.ne
    rw [hpos] at h1
    rw [heq] at h2
    push Not at h1
    exact ⟨h1.1, lt_of_le_of_ne h1.2 fun h' ↦ h2 ⟨h1.1, h'⟩⟩
  · rintro ⟨hℓ, hlt⟩
    rcases lt_trichotomy (1 + ℓ * marchenkoPasturCompanion y x) 0 with h | h | h
    · exact h
    · exact absurd (heq.1 h).2 hlt.ne
    · rcases hpos.1 h with h' | h' <;> linarith

/-- For `ℓ > 1 + √y`, the companion transform of `MP_y` takes the value `-ℓ⁻¹` at the outlier
location `ℓ (1 + y / (ℓ - 1))`. -/
theorem marchenkoPasturCompanion_mul_one_add_div_sub_one {ℓ : ℝ} (hℓ : 1 + √(y : ℝ) < ℓ) :
    marchenkoPasturCompanion y (ℓ * (1 + y / (ℓ - 1))) = -ℓ⁻¹ := by
  have h := (one_add_mul_marchenkoPasturCompanion_eq_zero_iff
    (one_add_sqrt_sq_lt_mul_one_add_div_sub_one hℓ)).2 ⟨hℓ, rfl⟩
  have hℓ0 : ℓ ≠ 0 := by linarith [Real.sqrt_nonneg (y : ℝ)]
  field_simp
  linear_combination h

/-- For `ℓ > 1 + √y`, the derivative of the companion transform of `MP_y` at the outlier location
`ψ = ℓ (1 + y / (ℓ - 1))` is `(ℓ - 1)² / (ℓ² ((ℓ - 1)² - y))`. -/
theorem deriv_marchenkoPasturCompanion_mul_one_add_div_sub_one {ℓ : ℝ}
    (hℓ : 1 + √(y : ℝ) < ℓ) :
    deriv (marchenkoPasturCompanion y) (ℓ * (1 + y / (ℓ - 1))) =
      (ℓ - 1) ^ 2 / (ℓ ^ 2 * ((ℓ - 1) ^ 2 - y)) := by
  have hψ := one_add_sqrt_sq_lt_mul_one_add_div_sub_one hℓ
  have hd := deriv_marchenkoPasturCompanion_mul_two_mul_mul_marchenkoPasturCompanion_add
    (notMem_support_marchenkoPastur_of_lt hψ) ((sq_nonneg _).trans_lt hψ).ne'
  have hℓ1 : 0 < ℓ - 1 := by linarith [Real.sqrt_nonneg (y : ℝ)]
  have hℓ0 : ℓ ≠ 0 := by linarith
  have hD := sub_one_sq_sub_pos hℓ
  rw [marchenkoPasturCompanion_mul_one_add_div_sub_one hℓ, two_mul_mul_neg_inv_add hℓ0 hℓ1.ne']
    at hd
  set d := deriv (marchenkoPasturCompanion y) (ℓ * (1 + y / (ℓ - 1)))
  rw [eq_div_iff (by positivity)]
  field_simp at hd
  linear_combination hd

/-- For `ℓ > 1 + √y` and the outlier location `ψ = ℓ (1 + y / (ℓ - 1))`, the companion transform
`s` of `MP_y` satisfies `(ℓ ψ s'(ψ))⁻¹ = (1 - y / (ℓ - 1)²) / (1 + y / (ℓ - 1))`; this is the
limiting squared overlap of the leading sample eigenvector of a spiked sample covariance with the
spike. -/
theorem inv_mul_mul_deriv_marchenkoPasturCompanion_mul_one_add_div_sub_one {ℓ : ℝ}
    (hℓ : 1 + √(y : ℝ) < ℓ) :
    (ℓ * (ℓ * (1 + y / (ℓ - 1))) *
        deriv (marchenkoPasturCompanion y) (ℓ * (1 + y / (ℓ - 1))))⁻¹ =
      (1 - y / (ℓ - 1) ^ 2) / (1 + y / (ℓ - 1)) := by
  have hℓ1 : 0 < ℓ - 1 := by linarith [Real.sqrt_nonneg (y : ℝ)]
  have hℓ0 : ℓ ≠ 0 := by linarith
  have hD := sub_one_sq_sub_pos hℓ
  rw [deriv_marchenkoPasturCompanion_mul_one_add_div_sub_one hℓ]
  field_simp

end TauCeti.Probability
