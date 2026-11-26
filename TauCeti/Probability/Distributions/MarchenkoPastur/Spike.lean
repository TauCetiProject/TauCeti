/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.MeasureTheory.Measure.ResolventTransform.Real
import TauCeti.Probability.Distributions.MarchenkoPastur.ResolventTransform

/-!
# The secular equation of a spike above the Marchenko–Pastur edge

Let `m(x) = ∫ (t - x)⁻¹ d(marchenkoPastur y)(t)` be the real resolvent transform of the
Marchenko–Pastur law at a real point `x` outside its support. Its companion
transform is `s(x) = y m(x) - (1 - y) / x`
(`TauCeti.Probability.marchenkoPasturCompanion`): it is the limit of the resolvent transforms
of the companion matrices `XᴴX/n` of sample covariance matrices `XXᴴ/n` with aspect ratio `y`.

Off the support and away from `0`, `s` solves `x s² + (x + 1 - y) s + 1 = 0`. Above the upper
edge `(1 + √y)²` it is the root to the right of the midpoint of the two roots,
`2 x s + (x + 1 - y) = √((x + 1 - y)² - 4x)`, and it takes values in `(-(1 + √y)⁻¹, 0)`.
There `x = -s⁻¹ + y / (1 + s)`, and `s` is strictly increasing.

These are the deterministic facts behind the outlier of the rank-one spiked sample covariance
`T^{1/2} X Xᴴ T^{1/2} / n` with `T = diag(ℓ, 1, …, 1)`. The nonzero eigenvalues of this matrix are
those of a rank-one perturbation, with weight `ℓ`, of the companion matrix of the other rows, and
eigenvalues above the bulk solve a secular equation whose limit is `1 + ℓ s(x) = 0`. Above the
edge this limiting equation has a solution exactly when `ℓ > 1 + √y`, and the solution is then
`ψ(ℓ) = ℓ (1 + y / (ℓ - 1))`; the sign of `1 + ℓ s(x)` changes there and nowhere else. At `ψ(ℓ)`
the derivative of `s` is `(ℓ - 1)² / (ℓ² ((ℓ - 1)² - y))`, so
`(ℓ ψ(ℓ) s'(ψ(ℓ)))⁻¹ = (1 - y / (ℓ - 1)²) / (1 + y / (ℓ - 1))`, the limiting squared overlap
of the leading sample eigenvector with the spike.

## Main results

* `TauCeti.Probability.marchenkoPasturCompanion_quadratic_eq_zero`: the quadratic equation of
  the companion transform at real points off the support.
* `TauCeti.Probability.two_mul_mul_marchenkoPasturCompanion_add_eq_sqrt`: the choice of root
  above the edge, which gives the closed form of the companion transform there.
* `TauCeti.Probability.neg_inv_one_add_sqrt_lt_marchenkoPasturCompanion`,
  `TauCeti.Probability.marchenkoPasturCompanion_neg`,
  `TauCeti.Probability.neg_inv_add_div_one_add_marchenkoPasturCompanion`,
  `TauCeti.Probability.strictMonoOn_marchenkoPasturCompanion`: range, inversion and monotonicity
  above the edge.
* `TauCeti.Probability.one_add_mul_marchenkoPasturCompanion_eq_zero_iff`,
  `TauCeti.Probability.one_add_mul_marchenkoPasturCompanion_pos_iff`,
  `TauCeti.Probability.one_add_mul_marchenkoPasturCompanion_neg_iff`: the limiting secular
  equation of a spike and its sign.
* `TauCeti.Probability.marchenkoPasturCompanion_mul_one_add_div_sub_one`: the value `-ℓ⁻¹` of the
  companion transform at the outlier location.
* `TauCeti.Probability.hasDerivAt_marchenkoPasturCompanion`,
  `TauCeti.Probability.deriv_marchenkoPasturCompanion_mul_two_mul_mul_marchenkoPasturCompanion_add`,
  `TauCeti.Probability.deriv_marchenkoPasturCompanion_mul_one_add_div_sub_one`,
  `TauCeti.Probability.inv_mul_mul_deriv_marchenkoPasturCompanion_mul_one_add_div_sub_one`: the
  derivative, its value at the outlier location and the limiting squared overlap.

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

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace TauCeti.Probability

/-- The companion transform `y m(z) - (1 - y) z⁻¹` of the Marchenko–Pastur law `MP_y`, where `m`
is its resolvent transform, with values in `ℝ` or `ℂ`. It is the limit of the resolvent transforms
of the companion matrices `XᴴX/n` of sample covariance matrices `XXᴴ/n` with aspect ratio `y`. -/
def marchenkoPasturCompanion {A : Type*} [RCLike A] (y : ℝ≥0) (z : A) : A :=
  ((y : ℝ) : A) * resolventTransform (marchenkoPastur y) z - (1 - ((y : ℝ) : A)) * z⁻¹

/-- The defining formula of `marchenkoPasturCompanion`. -/
theorem marchenkoPasturCompanion_def {A : Type*} [RCLike A] (y : ℝ≥0) (z : A) :
    marchenkoPasturCompanion y z =
      ((y : ℝ) : A) * resolventTransform (marchenkoPastur y) z - (1 - ((y : ℝ) : A)) * z⁻¹ :=
  (rfl)

/-- At a real point, the complex companion transform of `MP_y` is the real one. -/
@[simp, norm_cast]
theorem marchenkoPasturCompanion_ofReal (y : ℝ≥0) (x : ℝ) :
    marchenkoPasturCompanion y (x : ℂ) = ((marchenkoPasturCompanion y x : ℝ) : ℂ) := by
  simp [marchenkoPasturCompanion_def]

variable {y : ℝ≥0} {x : ℝ}

/-- A real point above the upper edge of `MP_y` is positive. -/
private lemma pos_of_one_add_sqrt_sq_lt (hx : (1 + √(y : ℝ)) ^ 2 < x) : 0 < x :=
  (sq_nonneg _).trans_lt hx

/-- Off the support of `MP_y` and away from `0`, the companion transform `s` satisfies the
quadratic equation `x * (s * s) + (x + 1 - y) * s + 1 = 0`. -/
theorem marchenkoPasturCompanion_quadratic_eq_zero (hx : x ∉ (marchenkoPastur y).support)
    (hx0 : x ≠ 0) :
    x * (marchenkoPasturCompanion y x * marchenkoPasturCompanion y x) +
      (x + 1 - y) * marchenkoPasturCompanion y x + 1 = 0 := by
  have hxi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hq := resolventTransform_marchenkoPastur_real_quadratic_eq_zero hx
  simp only [marchenkoPasturCompanion_def, RCLike.ofReal_real_eq_id, id]
  set m := resolventTransform (marchenkoPastur y) x
  linear_combination (y : ℝ) * hq +
    (-2 * y * (1 - y) * m + (1 - y) ^ 2 * x⁻¹ - (1 - y)) * hxi

/-- The companion quadratic equation above the upper edge of `MP_y`. -/
private lemma marchenkoPasturCompanion_quadratic_eq_zero_of_lt (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    x * (marchenkoPasturCompanion y x * marchenkoPasturCompanion y x) +
      (x + 1 - y) * marchenkoPasturCompanion y x + 1 = 0 :=
  marchenkoPasturCompanion_quadratic_eq_zero (notMem_support_marchenkoPastur_of_lt hx)
    (pos_of_one_add_sqrt_sq_lt hx).ne'

/-- Away from `0`, `2 x s + (x + 1 - y)` for the companion transform `s` of `MP_y` is
`2 y x m + (x + y - 1)` for its real resolvent transform `m`. -/
private lemma two_mul_mul_marchenkoPasturCompanion_add_eq (hx0 : x ≠ 0) :
    2 * x * marchenkoPasturCompanion y x + (x + 1 - y) =
      2 * y * x * resolventTransform (marchenkoPastur y) x + (x + y - 1) := by
  simp only [marchenkoPasturCompanion_def, RCLike.ofReal_real_eq_id, id]
  field_simp
  ring

/-- Above the upper edge of `MP_y`, the companion transform `s` is the root of its quadratic
equation given by `2 x s + (x + 1 - y) = √((x + 1 - y)² - 4 x)`. -/
theorem two_mul_mul_marchenkoPasturCompanion_add_eq_sqrt (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    2 * x * marchenkoPasturCompanion y x + (x + 1 - y) = √((x + 1 - y) ^ 2 - 4 * x) := by
  rw [two_mul_mul_marchenkoPasturCompanion_add_eq (pos_of_one_add_sqrt_sq_lt hx).ne',
    two_mul_mul_resolventTransform_marchenkoPastur_add_eq_sqrt hx]
  congr 1
  ring

/-- Above the upper edge of `MP_y`, the companion transform lies strictly to the right of the
midpoint `-(x + 1 - y) / (2 x)` of the two roots of its quadratic equation. -/
private lemma two_mul_mul_marchenkoPasturCompanion_add_pos (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    0 < 2 * x * marchenkoPasturCompanion y x + (x + 1 - y) := by
  rw [two_mul_mul_marchenkoPasturCompanion_add_eq (pos_of_one_add_sqrt_sq_lt hx).ne']
  exact two_mul_mul_resolventTransform_marchenkoPastur_add_pos hx

/-- Above the upper edge of `MP_y`, the companion transform is negative. -/
theorem marchenkoPasturCompanion_neg (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    marchenkoPasturCompanion y x < 0 := by
  have hq := marchenkoPasturCompanion_quadratic_eq_zero_of_lt hx
  have hr0 := Real.sqrt_nonneg (y : ℝ)
  have hr := Real.sq_sqrt y.coe_nonneg
  have hx1 : 0 < x + 1 - y := by nlinarith
  set s := marchenkoPasturCompanion y x
  by_contra! hs
  nlinarith [mul_nonneg (mul_nonneg (pos_of_one_add_sqrt_sq_lt hx).le hs) hs, mul_nonneg hx1.le hs]

/-- Above the upper edge of `MP_y`, the companion transform `s` satisfies `-1 < (1 + √y) s`. -/
private lemma neg_one_lt_mul_marchenkoPasturCompanion (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    -1 < (1 + √(y : ℝ)) * marchenkoPasturCompanion y x := by
  have hq := marchenkoPasturCompanion_quadratic_eq_zero_of_lt hx
  have hP := two_mul_mul_marchenkoPasturCompanion_add_pos hx
  have hs := marchenkoPasturCompanion_neg hx
  set s := marchenkoPasturCompanion y x
  -- From the choice of root, `x s² < 1`, and `(1 + √y)² < x`.
  have hxs : x * (s * s) < 1 := by nlinarith
  have h1 : ((1 + √(y : ℝ)) * s) ^ 2 < 1 := by nlinarith [mul_pos_of_neg_of_neg hs hs]
  nlinarith

/-- Above the upper edge of `MP_y`, the companion transform exceeds `-(1 + √y)⁻¹`. -/
theorem neg_inv_one_add_sqrt_lt_marchenkoPasturCompanion (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    -(1 + √(y : ℝ))⁻¹ < marchenkoPasturCompanion y x := by
  rw [show -(1 + √(y : ℝ))⁻¹ = -1 / (1 + √(y : ℝ)) by ring, div_lt_iff₀ (by positivity)]
  linarith [neg_one_lt_mul_marchenkoPasturCompanion hx]

/-- Above the upper edge of `MP_y`, the companion transform `s` inverts the map
`s ↦ -s⁻¹ + y / (1 + s)`. -/
theorem neg_inv_add_div_one_add_marchenkoPasturCompanion (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    -(marchenkoPasturCompanion y x)⁻¹ + y / (1 + marchenkoPasturCompanion y x) = x := by
  have hq := marchenkoPasturCompanion_quadratic_eq_zero_of_lt hx
  have hs := marchenkoPasturCompanion_neg hx
  have hs1 : 0 < 1 + marchenkoPasturCompanion y x := by
    have h := neg_inv_one_add_sqrt_lt_marchenkoPasturCompanion hx
    have : (1 + √(y : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by simp)
    linarith
  set s := marchenkoPasturCompanion y x
  have hs0 : s ≠ 0 := hs.ne
  have hs1' : 1 + s ≠ 0 := hs1.ne'
  field_simp
  linear_combination -hq

/-- The map `s ↦ -s⁻¹ + r² / (1 + s)` is monotone on `(-(1 + r)⁻¹, 0)` for `r ≥ 0`. -/
private lemma neg_inv_add_sq_div_one_add_le {r a b : ℝ} (hr : 0 ≤ r) (ha : -1 < (1 + r) * a)
    (hab : a ≤ b) (hb : b < 0) : -a⁻¹ + r ^ 2 / (1 + a) ≤ -b⁻¹ + r ^ 2 / (1 + b) := by
  have ha0 : a < 0 := hab.trans_lt hb
  have ha1 : -(r * a) < 1 + a := by linarith
  have hb1 : -(r * b) < 1 + b := by nlinarith
  have hra : 0 ≤ -(r * a) := by nlinarith
  have hrb : 0 ≤ -(r * b) := by nlinarith
  have hnum : 0 ≤ (1 + a) * (1 + b) - r ^ 2 * a * b := by
    nlinarith [mul_le_mul ha1.le hb1.le hrb (hra.trans ha1.le)]
  have hden : 0 < a * b * (1 + a) * (1 + b) := by
    have := mul_pos_of_neg_of_neg ha0 hb
    have := hra.trans_lt ha1
    have := hrb.trans_lt hb1
    positivity
  have ha0' : a ≠ 0 := ha0.ne
  have hb0 : b ≠ 0 := hb.ne
  have ha1' : 1 + a ≠ 0 := (hra.trans_lt ha1).ne'
  have hb1' : 1 + b ≠ 0 := (hrb.trans_lt hb1).ne'
  rw [← sub_nonneg]
  have key : -b⁻¹ + r ^ 2 / (1 + b) - (-a⁻¹ + r ^ 2 / (1 + a)) =
      (b - a) * ((1 + a) * (1 + b) - r ^ 2 * a * b) / (a * b * (1 + a) * (1 + b)) := by
    field_simp
    ring
  rw [key]
  exact div_nonneg (mul_nonneg (sub_nonneg.2 hab) hnum) hden.le

/-- The companion transform of `MP_y` is strictly increasing above the upper edge. -/
theorem strictMonoOn_marchenkoPasturCompanion :
    StrictMonoOn (marchenkoPasturCompanion y : ℝ → ℝ) (Ioi ((1 + √(y : ℝ)) ^ 2)) := by
  intro x₁ hx₁ x₂ hx₂ h
  by_contra! hle
  have := neg_inv_add_sq_div_one_add_le (Real.sqrt_nonneg _)
    (neg_one_lt_mul_marchenkoPasturCompanion hx₂) hle
    (marchenkoPasturCompanion_neg hx₁)
  rw [Real.sq_sqrt y.coe_nonneg, neg_inv_add_div_one_add_marchenkoPasturCompanion hx₂,
    neg_inv_add_div_one_add_marchenkoPasturCompanion hx₁] at this
  linarith

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
  have hq := marchenkoPasturCompanion_quadratic_eq_zero_of_lt hx
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
      have hr := Real.sq_sqrt y.coe_nonneg
      rw [two_mul_mul_neg_inv_add hℓ0 hℓ1.ne']
      exact div_pos (by nlinarith) hℓ1
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
  have hlow := neg_one_lt_mul_marchenkoPasturCompanion hx
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

/-- Off the support of `MP_y` and away from `0`, the companion transform has derivative
`y ∫ (t - z)⁻² dMP_y(t) + (1 - y) z⁻²`. -/
theorem hasDerivAt_marchenkoPasturCompanion {A : Type*} [RCLike A] {z : A}
    (hz : z ∉ algebraMap ℝ A '' (marchenkoPastur y).support) (hz0 : z ≠ 0) :
    HasDerivAt (marchenkoPasturCompanion y)
      (((y : ℝ) : A) * ∫ t, resolvent z t ^ 2 ∂marchenkoPastur y +
        (1 - ((y : ℝ) : A)) * (z ^ 2)⁻¹) z := by
  have h := ((hasDerivAt_resolventTransform z hz).const_mul ((y : ℝ) : A)).sub
    ((hasDerivAt_inv hz0).const_mul (1 - ((y : ℝ) : A)))
  have hf : marchenkoPasturCompanion y = fun w : A ↦
      ((y : ℝ) : A) * resolventTransform (marchenkoPastur y) w - (1 - ((y : ℝ) : A)) * w⁻¹ :=
    funext fun w ↦ marchenkoPasturCompanion_def y w
  rw [hf]
  convert h using 1
  ring

/-- Off the support of `MP_y` and away from `0`, the derivative of the companion transform `s`
satisfies `s' (2 x s + (x + 1 - y)) = -s (1 + s)`, obtained by differentiating the quadratic
equation. -/
theorem deriv_marchenkoPasturCompanion_mul_two_mul_mul_marchenkoPasturCompanion_add
    (hx : x ∉ (marchenkoPastur y).support) (hx0 : x ≠ 0) :
    deriv (marchenkoPasturCompanion y) x *
        (2 * x * marchenkoPasturCompanion y x + (x + 1 - y)) =
      -(marchenkoPasturCompanion y x * (1 + marchenkoPasturCompanion y x)) := by
  obtain ⟨s', hs'⟩ : ∃ s', HasDerivAt (marchenkoPasturCompanion y : ℝ → ℝ) s' x :=
    ⟨_, hasDerivAt_marchenkoPasturCompanion (by simpa using hx) hx0⟩
  rw [hs'.deriv]
  set S : ℝ → ℝ := marchenkoPasturCompanion y
  -- The quadratic expression vanishes near `x`, so its derivative there is `0`.
  have hF : HasDerivAt (fun w : ℝ ↦ w * (S w * S w) + (w + 1 - y) * S w + 1)
      (S x * S x + x * (s' * S x + S x * s') + (S x + (x + 1 - y) * s')) x := by
    convert (((hasDerivAt_id' x).mul (hs'.mul hs')).add
      ((((hasDerivAt_id' x).add_const 1).sub_const (y : ℝ)).mul hs')).add_const 1 using 1
    simp only [Pi.mul_apply]
    ring
  have hF0 : HasDerivAt (fun w : ℝ ↦ w * (S w * S w) + (w + 1 - y) * S w + 1) 0 x := by
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Measure.isClosed_support.isOpen_compl.mem_nhds hx,
      isOpen_ne.mem_nhds hx0] with w hw hw0
    exact marchenkoPasturCompanion_quadratic_eq_zero hw hw0
  linear_combination hF.unique hF0

/-- For `ℓ > 1 + √y`, the derivative of the companion transform of `MP_y` at the outlier location
`ψ = ℓ (1 + y / (ℓ - 1))` is `(ℓ - 1)² / (ℓ² ((ℓ - 1)² - y))`. -/
theorem deriv_marchenkoPasturCompanion_mul_one_add_div_sub_one {ℓ : ℝ}
    (hℓ : 1 + √(y : ℝ) < ℓ) :
    deriv (marchenkoPasturCompanion y) (ℓ * (1 + y / (ℓ - 1))) =
      (ℓ - 1) ^ 2 / (ℓ ^ 2 * ((ℓ - 1) ^ 2 - y)) := by
  have hψ := one_add_sqrt_sq_lt_mul_one_add_div_sub_one hℓ
  have hd := deriv_marchenkoPasturCompanion_mul_two_mul_mul_marchenkoPasturCompanion_add
    (notMem_support_marchenkoPastur_of_lt hψ) (pos_of_one_add_sqrt_sq_lt hψ).ne'
  have hr := Real.sq_sqrt y.coe_nonneg
  have hℓ1 : 0 < ℓ - 1 := by linarith [Real.sqrt_nonneg (y : ℝ)]
  have hℓ0 : ℓ ≠ 0 := by linarith
  have hD : 0 < (ℓ - 1) ^ 2 - y := by nlinarith [Real.sqrt_nonneg (y : ℝ)]
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
  have hr := Real.sq_sqrt y.coe_nonneg
  have hℓ1 : 0 < ℓ - 1 := by linarith [Real.sqrt_nonneg (y : ℝ)]
  have hℓ0 : ℓ ≠ 0 := by linarith
  have hD : 0 < (ℓ - 1) ^ 2 - y := by nlinarith [Real.sqrt_nonneg (y : ℝ)]
  rw [deriv_marchenkoPasturCompanion_mul_one_add_div_sub_one hℓ]
  field_simp

end TauCeti.Probability
