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
import Mathlib.Topology.Order.IntermediateValue
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

* `TauCeti.Probability.resolventTransform_marchenkoPastur_real_quadratic_eq_zero`,
  `TauCeti.Probability.marchenkoPasturCompanion_quadratic_eq_zero`: the quadratic equations of
  the real transform and of the companion transform at real points off the support.
* `TauCeti.Probability.two_mul_mul_resolventTransform_marchenkoPastur_add_eq_sqrt`,
  `TauCeti.Probability.two_mul_mul_marchenkoPasturCompanion_add_eq_sqrt`: the choice of root
  above the edge, which gives the closed form of both transforms there.
* `TauCeti.Probability.neg_inv_one_add_sqrt_lt_marchenkoPasturCompanion`,
  `TauCeti.Probability.marchenkoPasturCompanion_neg`,
  `TauCeti.Probability.neg_inv_add_div_one_add_marchenkoPasturCompanion`,
  `TauCeti.Probability.strictMonoOn_marchenkoPasturCompanion`: range, inversion and monotonicity
  above the edge.
* `TauCeti.Probability.one_add_mul_marchenkoPasturCompanion_eq_zero_iff`,
  `TauCeti.Probability.one_add_mul_marchenkoPasturCompanion_pos_iff`,
  `TauCeti.Probability.one_add_mul_marchenkoPasturCompanion_neg_iff`: the limiting secular
  equation of a spike and its sign.
* `TauCeti.Probability.hasDerivAt_marchenkoPasturCompanion`,
  `TauCeti.Probability.deriv_marchenkoPasturCompanion_mul`,
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

/-- A real point above the upper edge of `MP_y` is outside its support. -/
private lemma notMem_support_marchenkoPastur (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    x ∉ (marchenkoPastur y).support := fun ht ↦ by
  have := (support_marchenkoPastur_subset_Icc y ht).2
  linarith

/-- A real point outside the support of `MP_y` is outside its image in `ℝ` under `algebraMap`. -/
private lemma notMem_image_algebraMap_support (hx : x ∉ (marchenkoPastur y).support) :
    x ∉ algebraMap ℝ ℝ '' (marchenkoPastur y).support := by
  simpa using hx

/-- Off the support of `MP_y`, its real resolvent transform `m` satisfies the quadratic equation
`y * x * (m * m) + (x + y - 1) * m + 1 = 0`. -/
theorem resolventTransform_marchenkoPastur_real_quadratic_eq_zero
    (hx : x ∉ (marchenkoPastur y).support) :
    y * x * (resolventTransform (marchenkoPastur y) x * resolventTransform (marchenkoPastur y) x) +
      (x + y - 1) * resolventTransform (marchenkoPastur y) x + 1 = 0 := by
  have hz : (x : ℂ) ∉ ((↑) : ℝ → ℂ) '' (marchenkoPastur y).support := by
    rintro ⟨t, ht, htx⟩
    exact hx (Complex.ofReal_injective htx ▸ ht)
  have h := resolventTransform_marchenkoPastur_quadratic_eq_zero hz
  rw [Measure.resolventTransform_ofReal] at h
  exact_mod_cast h

/-- The discriminant `(x + y - 1)² - 4 y x` is positive above the upper edge of `MP_y`. -/
private lemma discr_pos (hx : (1 + √(y : ℝ)) ^ 2 < x) : 0 < (x + y - 1) ^ 2 - 4 * y * x := by
  have hr := Real.sq_sqrt y.coe_nonneg
  have hr0 := Real.sqrt_nonneg (y : ℝ)
  have hfac : (x + y - 1) ^ 2 - 4 * y * x =
      (x - (1 + √(y : ℝ)) ^ 2) * (x - (1 - √(y : ℝ)) ^ 2) := by
    linear_combination (2 * x + 2 - y - √(y : ℝ) ^ 2) * hr
  rw [hfac]
  exact mul_pos (by linarith) (by nlinarith)

/-- Far above the edge, `2 y x m(x) + (x + y - 1)` is positive. -/
private lemma two_mul_mul_resolventTransform_add_pos_of_far :
    let x₀ : ℝ := 2 * (1 + √(y : ℝ)) ^ 2 + 3 * y + 1
    0 < 2 * y * x₀ * resolventTransform (marchenkoPastur y) x₀ + (x₀ + y - 1) := by
  intro x₀
  set e := (1 + √(y : ℝ)) ^ 2
  have he : 1 ≤ e := by nlinarith [Real.sqrt_nonneg (y : ℝ)]
  have hy := y.coe_nonneg
  have hb : ∀ᵐ t ∂marchenkoPastur y, t ≤ e := by
    filter_upwards [ae_mem_Icc_zero_marchenkoPastur y] with t ht using ht.2
  have hex : e < x₀ := by simp only [x₀]; linarith
  set m := resolventTransform (marchenkoPastur y) x₀
  have hm0 : m ≤ 0 := resolventTransform_nonpos_of_ae_le hb hex
  have hlow : -(x₀ - e)⁻¹ ≤ m := by
    simpa [div_eq_mul_inv] using neg_div_sub_le_resolventTransform_of_ae_le hb hex
  have hd : 0 < x₀ - e := sub_pos.2 hex
  have hmd : -1 ≤ m * (x₀ - e) := by
    have := mul_le_mul_of_nonneg_right hlow hd.le
    rwa [neg_mul, inv_mul_cancel₀ hd.ne'] at this
  have hx₀d : x₀ - 2 * (x₀ - e) ≤ 0 := by simp only [x₀]; linarith
  nlinarith [mul_nonneg hy (mul_nonneg_of_nonpos_of_nonpos hx₀d hm0),
    mul_le_mul_of_nonneg_left hmd hy]

/-- Above the upper edge of `MP_y`, its real resolvent transform `m` is the root of
`y x m² + (x + y - 1) m + 1 = 0` given by `2 y x m + (x + y - 1) = √((x + y - 1)² - 4 y x)`: for
`y > 0` this is `m(x) = (√((x + y - 1)² - 4 y x) - (x + y - 1)) / (2 y x)`, and for `y = 0` it is
`m(x) = (1 - x)⁻¹`. -/
theorem two_mul_mul_resolventTransform_marchenkoPastur_add_eq_sqrt
    (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    2 * y * x * resolventTransform (marchenkoPastur y) x + (x + y - 1) =
      √((x + y - 1) ^ 2 - 4 * y * x) := by
  set e := (1 + √(y : ℝ)) ^ 2
  set φ : ℝ → ℝ := fun x ↦ 2 * y * x * resolventTransform (marchenkoPastur y) x + (x + y - 1)
  -- `φ` squares to the discriminant, so it does not vanish above the edge.
  have hsq : ∀ x, e < x → φ x ^ 2 = (x + y - 1) ^ 2 - 4 * y * x := fun x hx ↦ by
    linear_combination (4 * y * x) * resolventTransform_marchenkoPastur_real_quadratic_eq_zero
      (notMem_support_marchenkoPastur hx)
  have hcont : ContinuousOn φ (Ioi e) := by
    have hm : ContinuousOn (resolventTransform (marchenkoPastur y) : ℝ → ℝ) (Ioi e) :=
      fun x hx ↦ (hasDerivAt_resolventTransform x (notMem_image_algebraMap_support
        (notMem_support_marchenkoPastur hx))).continuousAt.continuousWithinAt
    fun_prop
  -- `φ` is positive far above the edge, hence everywhere above it.
  have hpos : 0 < φ x := by
    by_contra! hneg
    have hne : φ x ≠ 0 := fun h ↦ by
      have := hsq x hx
      rw [h] at this
      linarith [discr_pos hx]
    have hx₀ : e < 2 * e + 3 * y + 1 := by
      have : 0 ≤ e := sq_nonneg _
      linarith [y.coe_nonneg]
    obtain ⟨x', hx', h0⟩ := isPreconnected_Ioi.intermediate_value hx hx₀ hcont
      ⟨lt_of_le_of_ne hneg hne |>.le, (two_mul_mul_resolventTransform_add_pos_of_far (y := y)).le⟩
    have := hsq x' hx'
    rw [h0] at this
    linarith [discr_pos (y := y) hx']
  rw [← hsq x hx, Real.sqrt_sq hpos.le]

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
  marchenkoPasturCompanion_quadratic_eq_zero (notMem_support_marchenkoPastur hx)
    (by nlinarith [Real.sqrt_nonneg (y : ℝ)])

/-- Above the upper edge of `MP_y`, the companion transform `s` is the root of its quadratic
equation given by `2 x s + (x + 1 - y) = √((x + 1 - y)² - 4 x)`. -/
theorem two_mul_mul_marchenkoPasturCompanion_add_eq_sqrt (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    2 * x * marchenkoPasturCompanion y x + (x + 1 - y) = √((x + 1 - y) ^ 2 - 4 * x) := by
  have hx0 : x ≠ 0 := by nlinarith [Real.sqrt_nonneg (y : ℝ)]
  have h := two_mul_mul_resolventTransform_marchenkoPastur_add_eq_sqrt hx
  have hD : (x + 1 - y) ^ 2 - 4 * x = (x + y - 1) ^ 2 - 4 * y * x := by ring
  rw [hD, ← h]
  simp only [marchenkoPasturCompanion_def, RCLike.ofReal_real_eq_id, id]
  field_simp
  ring

/-- Above the upper edge of `MP_y`, the companion transform lies strictly to the right of the
midpoint `-(x + 1 - y) / (2 x)` of the two roots of its quadratic equation. -/
private lemma two_mul_mul_marchenkoPasturCompanion_add_pos (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    0 < 2 * x * marchenkoPasturCompanion y x + (x + 1 - y) := by
  rw [two_mul_mul_marchenkoPasturCompanion_add_eq_sqrt hx]
  apply Real.sqrt_pos.2
  have := discr_pos hx
  linarith [show (x + 1 - y) ^ 2 - 4 * x = (x + y - 1) ^ 2 - 4 * y * x by ring]

/-- Above the upper edge of `MP_y`, the companion transform is negative. -/
theorem marchenkoPasturCompanion_neg (hx : (1 + √(y : ℝ)) ^ 2 < x) :
    marchenkoPasturCompanion y x < 0 := by
  have hq := marchenkoPasturCompanion_quadratic_eq_zero_of_lt hx
  have hr0 := Real.sqrt_nonneg (y : ℝ)
  have hr := Real.sq_sqrt y.coe_nonneg
  have hx1 : 0 < x + 1 - y := by nlinarith
  set s := marchenkoPasturCompanion y x
  by_contra! hs
  nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ x by nlinarith) hs) hs, mul_nonneg hx1.le hs]

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

/-- Two roots of `a t² + b t + 1 = 0` that both lie to the right of the midpoint `-b / (2a)` are
equal. -/
private lemma eq_of_quadratic_eq_zero {a b s t : ℝ} (hs : a * (s * s) + b * s + 1 = 0)
    (ht : a * (t * t) + b * t + 1 = 0) (hs' : 0 < 2 * a * s + b) (ht' : 0 < 2 * a * t + b) :
    s = t := by
  have h : (s - t) * (a * (s + t) + b) = 0 := by linear_combination hs - ht
  have hpos : 0 < a * (s + t) + b := by linarith
  linarith [(mul_eq_zero.1 h).resolve_right hpos.ne']

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
      have key : 2 * (ℓ * (1 + y / (ℓ - 1))) * -ℓ⁻¹ + (ℓ * (1 + y / (ℓ - 1)) + 1 - y) =
          ((ℓ - 1) ^ 2 - y) / (ℓ - 1) := by
        field_simp
        ring
      rw [key]
      exact div_pos (by nlinarith) hℓ1
    rw [eq_of_quadratic_eq_zero hq ht hP ht']
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
theorem deriv_marchenkoPasturCompanion_mul (hx : x ∉ (marchenkoPastur y).support)
    (hx0 : x ≠ 0) :
    deriv (marchenkoPasturCompanion y) x *
        (2 * x * marchenkoPasturCompanion y x + (x + 1 - y)) =
      -(marchenkoPasturCompanion y x * (1 + marchenkoPasturCompanion y x)) := by
  obtain ⟨s', hs'⟩ : ∃ s', HasDerivAt (marchenkoPasturCompanion y : ℝ → ℝ) s' x :=
    ⟨_, hasDerivAt_marchenkoPasturCompanion (notMem_image_algebraMap_support hx) hx0⟩
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
  have h0 := (one_add_mul_marchenkoPasturCompanion_eq_zero_iff hψ).2 ⟨hℓ, rfl⟩
  have hd := deriv_marchenkoPasturCompanion_mul (notMem_support_marchenkoPastur hψ)
    (by nlinarith [Real.sqrt_nonneg (y : ℝ)])
  have hr := Real.sq_sqrt y.coe_nonneg
  have hℓ1 : 0 < ℓ - 1 := by linarith [Real.sqrt_nonneg (y : ℝ)]
  have hℓ0 : ℓ ≠ 0 := by linarith
  have hD : 0 < (ℓ - 1) ^ 2 - y := by nlinarith [Real.sqrt_nonneg (y : ℝ)]
  have hP : 2 * (ℓ * (1 + y / (ℓ - 1))) * -ℓ⁻¹ + (ℓ * (1 + y / (ℓ - 1)) + 1 - y) =
      ((ℓ - 1) ^ 2 - y) / (ℓ - 1) := by
    field_simp
    ring
  generalize ℓ * (1 + y / (ℓ - 1)) = ψ at h0 hd hP ⊢
  have hs : marchenkoPasturCompanion y ψ = -ℓ⁻¹ := by
    field_simp
    linear_combination h0
  rw [hs, hP] at hd
  set d := deriv (marchenkoPasturCompanion y) ψ
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
