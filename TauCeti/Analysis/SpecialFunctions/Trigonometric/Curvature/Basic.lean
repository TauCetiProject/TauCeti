/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.ODE.Wronskian

/-!
# The sine and cosine of a constant-curvature model

`TauCeti.curvatureSine κ` and `TauCeti.curvatureCosine κ` are the fundamental solutions of
`y'' + κ y = 0`, with initial data `(0, 1)` and `(1, 0)`, respectively. They give the radial
Jacobi coefficients in the constant-curvature models, including the flat model. The sine is
positive at positive times before the first spherical zero `π / √κ`, and at every positive time
in nonpositive curvature, where it vanishes only at the origin; the cosine is positive before the
spherical half-radius. Near the origin the sine has unit first-order scale,
`curvatureSine κ t / t → 1`. Rescaling time by `c` rescales the curvature parameter by `c⁻²`:
`curvatureSine (κ / c ^ 2) (c * t) = c * curvatureSine κ t`.

The parameter is the coefficient in the scalar ODE; for a geodesic of speed `c` in curvature
`κ`, use the parameter `κ * c ^ 2`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 10.
-/

public section

noncomputable section

namespace TauCeti

open Filter Real
open scoped ContDiff Topology

/-- The solution of `y'' + κ y = 0` with `y(0) = 0` and `y'(0) = 1`. -/
def curvatureSine (κ t : ℝ) : ℝ :=
  if 0 < κ then sin (√κ * t) / √κ
  else if κ = 0 then t else sinh (√(-κ) * t) / √(-κ)

/-- The solution of `y'' + κ y = 0` with `y(0) = 1` and `y'(0) = 0`. -/
def curvatureCosine (κ t : ℝ) : ℝ :=
  if 0 < κ then cos (√κ * t)
  else if κ = 0 then 1 else cosh (√(-κ) * t)

/-- In positive curvature the model sine is a rescaled sine. -/
theorem curvatureSine_of_pos {κ : ℝ} (hκ : 0 < κ) (t : ℝ) :
    curvatureSine κ t = sin (√κ * t) / √κ := by
  simp [curvatureSine, hκ]

/-- In positive curvature the model cosine is a rescaled cosine. -/
theorem curvatureCosine_of_pos {κ : ℝ} (hκ : 0 < κ) (t : ℝ) :
    curvatureCosine κ t = cos (√κ * t) := by
  simp [curvatureCosine, hκ]

@[simp] theorem curvatureSine_zero_left (t : ℝ) : curvatureSine 0 t = t := by
  simp [curvatureSine]

@[simp] theorem curvatureCosine_zero_left (t : ℝ) : curvatureCosine 0 t = 1 := by
  simp [curvatureCosine]

/-- In negative curvature the model sine is a rescaled hyperbolic sine. -/
theorem curvatureSine_of_neg {κ : ℝ} (hκ : κ < 0) (t : ℝ) :
    curvatureSine κ t = sinh (√(-κ) * t) / √(-κ) := by
  simp [curvatureSine, hκ.not_gt, hκ.ne]

/-- In negative curvature the model cosine is a rescaled hyperbolic cosine. -/
theorem curvatureCosine_of_neg {κ : ℝ} (hκ : κ < 0) (t : ℝ) :
    curvatureCosine κ t = cosh (√(-κ) * t) := by
  simp [curvatureCosine, hκ.not_gt, hκ.ne]

@[simp] theorem curvatureSine_zero_right (κ : ℝ) : curvatureSine κ 0 = 0 := by
  simp [curvatureSine]

@[simp] theorem curvatureCosine_zero_right (κ : ℝ) : curvatureCosine κ 0 = 1 := by
  simp [curvatureCosine]

@[simp] theorem curvatureSine_neg (κ t : ℝ) : curvatureSine κ (-t) = -curvatureSine κ t := by
  unfold curvatureSine
  split_ifs <;> simp [mul_neg, neg_div]

@[simp] theorem curvatureCosine_neg (κ t : ℝ) : curvatureCosine κ (-t) = curvatureCosine κ t := by
  simp [curvatureCosine, mul_neg]

/-- The derivative of the model sine is the model cosine, for every curvature parameter. -/
theorem hasDerivAt_curvatureSine (κ t : ℝ) :
    HasDerivAt (curvatureSine κ) (curvatureCosine κ t) t := by
  rcases lt_trichotomy 0 κ with hκ | rfl | hκ
  · unfold curvatureSine curvatureCosine
    simp only [ite_eq_left hκ]
    convert (((hasDerivAt_id' t).const_mul (√κ)).sin.div_const (√κ)) using 1
    simp [(sqrt_pos.2 hκ).ne']
  · unfold curvatureSine curvatureCosine
    simpa using hasDerivAt_id' t
  · unfold curvatureSine curvatureCosine
    simp only [ite_eq_right hκ.not_gt, ite_eq_right hκ.ne]
    convert (((hasDerivAt_id' t).const_mul (√(-κ))).sinh.div_const (√(-κ))) using 1
    simp [(sqrt_pos.2 (neg_pos.2 hκ)).ne']

/-- The derivative of the model cosine is `-κ` times the model sine. -/
theorem hasDerivAt_curvatureCosine (κ t : ℝ) :
    HasDerivAt (curvatureCosine κ) (-κ * curvatureSine κ t) t := by
  rcases lt_trichotomy 0 κ with hκ | rfl | hκ
  · unfold curvatureSine curvatureCosine
    simp only [ite_eq_left hκ]
    refine (((hasDerivAt_id' t).const_mul (√κ)).cos).congr_deriv ?_
    have hsq := sq_sqrt hκ.le
    simp only [mul_one]
    field_simp [(sqrt_pos.2 hκ).ne']
    rw [hsq]
    ring
  · unfold curvatureSine curvatureCosine
    simpa using hasDerivAt_const t (1 : ℝ)
  · unfold curvatureSine curvatureCosine
    simp only [ite_eq_right hκ.not_gt, ite_eq_right hκ.ne]
    refine (((hasDerivAt_id' t).const_mul (√(-κ))).cosh).congr_deriv ?_
    have hsq := sq_sqrt (neg_nonneg.2 hκ.le)
    simp only [mul_one]
    field_simp [(sqrt_pos.2 (neg_pos.2 hκ)).ne']
    rw [hsq]
    ring

@[simp] theorem deriv_curvatureSine (κ t : ℝ) :
    deriv (curvatureSine κ) t = curvatureCosine κ t :=
  (hasDerivAt_curvatureSine κ t).deriv

@[simp] theorem deriv_curvatureCosine (κ t : ℝ) :
    deriv (curvatureCosine κ) t = -κ * curvatureSine κ t :=
  (hasDerivAt_curvatureCosine κ t).deriv

/-- The model sine is smooth in time for every fixed curvature parameter. -/
theorem contDiff_curvatureSine (κ : ℝ) : ContDiff ℝ ∞ (curvatureSine κ) := by
  rcases lt_trichotomy 0 κ with hκ | rfl | hκ
  · unfold curvatureSine
    simp only [ite_eq_left hκ]
    exact
      (contDiff_sin.comp (contDiff_const.mul contDiff_id (E := ℝ))).div_const (√κ)
  · unfold curvatureSine
    simp only [lt_self_iff_false]
    exact contDiff_id
  · unfold curvatureSine
    simp only [ite_eq_right hκ.not_gt, ite_eq_right hκ.ne]
    exact
      (contDiff_sinh.comp (contDiff_const.mul contDiff_id (E := ℝ))).div_const (√(-κ))

/-- The model cosine is smooth in time for every fixed curvature parameter. -/
theorem contDiff_curvatureCosine (κ : ℝ) : ContDiff ℝ ∞ (curvatureCosine κ) := by
  rcases lt_trichotomy 0 κ with hκ | rfl | hκ
  · unfold curvatureCosine
    simp only [ite_eq_left hκ]
    exact
      contDiff_cos.comp (contDiff_const.mul contDiff_id (E := ℝ))
  · unfold curvatureCosine
    simpa using contDiff_const (𝕜 := ℝ) (n := ∞) (c := (1 : ℝ))
  · unfold curvatureCosine
    simp only [ite_eq_right hκ.not_gt, ite_eq_right hκ.ne]
    exact
      contDiff_cosh.comp (contDiff_const.mul contDiff_id (E := ℝ))

/-- The fundamental-solution identity `cκ² + κ sκ² = 1`. -/
theorem curvatureCosine_sq_add_mul_curvatureSine_sq (κ t : ℝ) :
    curvatureCosine κ t ^ 2 + κ * curvatureSine κ t ^ 2 = 1 := by
  have h := wronskian_eq_one_of_hasDerivAt (hasDerivAt_curvatureSine κ)
    (hasDerivAt_curvatureCosine κ) (hasDerivAt_curvatureCosine κ)
    (fun r ↦ ((hasDerivAt_curvatureSine κ r).const_mul (-κ)).congr_deriv (by ring))
    (a := 0) (by simp) (by simp) (by simp) t
  nlinarith

/-- The model sine is positive before the first positive spherical zero. -/
theorem curvatureSine_pos {κ t : ℝ} (ht : 0 < t)
    (hbound : 0 < κ → t < π / √κ) : 0 < curvatureSine κ t := by
  rcases lt_trichotomy 0 κ with hκ | rfl | hκ
  · rw [curvatureSine_of_pos hκ]
    exact div_pos (sin_pos_of_pos_of_lt_pi (mul_pos (sqrt_pos.2 hκ) ht)
      ((lt_div_iff₀' (sqrt_pos.2 hκ)).1 (hbound hκ))) (sqrt_pos.2 hκ)
  · simpa using ht
  · rw [curvatureSine_of_neg hκ]
    exact div_pos (sinh_pos_iff.2 (mul_pos (sqrt_pos.2 (neg_pos.2 hκ)) ht))
      (sqrt_pos.2 (neg_pos.2 hκ))

/-- The model sine is nonnegative up to and including the first positive spherical zero. -/
theorem curvatureSine_nonneg {κ t : ℝ} (ht : 0 ≤ t)
    (hbound : 0 < κ → t ≤ π / √κ) : 0 ≤ curvatureSine κ t := by
  rcases lt_trichotomy 0 κ with hκ | rfl | hκ
  · rw [curvatureSine_of_pos hκ]
    exact div_nonneg (sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (sqrt_nonneg κ) ht)
      ((le_div_iff₀' (sqrt_pos.2 hκ)).1 (hbound hκ))) (sqrt_nonneg κ)
  · simpa using ht
  · rw [curvatureSine_of_neg hκ]
    exact div_nonneg (sinh_nonneg_iff.2 (mul_nonneg (sqrt_nonneg _) ht)) (sqrt_nonneg _)

/-- In nonpositive curvature the model sine vanishes only at the origin. -/
@[simp]
theorem curvatureSine_eq_zero_iff_of_nonpos {κ t : ℝ} (hκ : κ ≤ 0) :
    curvatureSine κ t = 0 ↔ t = 0 := by
  rcases hκ.lt_or_eq with hκ | rfl
  · have hs := (sqrt_pos.2 (neg_pos.2 hκ)).ne'
    rw [curvatureSine_of_neg hκ, div_eq_zero_iff, or_iff_left hs, sinh_eq_zero, mul_eq_zero,
      or_iff_right hs]
  · simp

/-- The zeros of the model sine are the integer multiples of `π / √κ`. In nonpositive curvature
`√κ = 0`, so these all collapse to the origin. -/
theorem curvatureSine_eq_zero_iff {κ t : ℝ} :
    curvatureSine κ t = 0 ↔ ∃ n : ℤ, n * π / √κ = t := by
  rcases lt_or_ge 0 κ with hκ | hκ
  · have hs := (sqrt_pos.2 hκ).ne'
    rw [curvatureSine_of_pos hκ, div_eq_zero_iff, or_iff_left hs, sin_eq_zero_iff]
    exact exists_congr fun n ↦ by rw [div_eq_iff hs, mul_comm t]
  · simp [curvatureSine_eq_zero_iff_of_nonpos hκ, sqrt_eq_zero_of_nonpos hκ, eq_comm]

/-- The model sine vanishes at `π / √κ`, its first positive zero in positive curvature and the
origin otherwise. -/
@[simp]
theorem curvatureSine_pi_div_sqrt (κ : ℝ) : curvatureSine κ (π / √κ) = 0 :=
  curvatureSine_eq_zero_iff.2 ⟨1, by simp⟩

private theorem curvatureSine_div_sq_mul_and_curvatureCosine_div_sq_mul_of_pos {κ c : ℝ}
    (hc : 0 < c) (t : ℝ) :
    curvatureSine (κ / c ^ 2) (c * t) = c * curvatureSine κ t ∧
      curvatureCosine (κ / c ^ 2) (c * t) = curvatureCosine κ t := by
  have hc2 : 0 < c ^ 2 := by positivity
  have h₃ (x : ℝ) : x / c * (c * t) = x * t := by field_simp
  rcases lt_trichotomy 0 κ with hκ | rfl | hκ
  · have hs := (sqrt_pos.2 hκ).ne'
    have h₁ : √(κ / c ^ 2) = √κ / c := by rw [sqrt_div' κ hc2.le, sqrt_sq hc.le]
    rw [curvatureSine_of_pos (div_pos hκ hc2), curvatureCosine_of_pos (div_pos hκ hc2),
      curvatureSine_of_pos hκ, curvatureCosine_of_pos hκ, h₁, h₃]
    exact ⟨by field_simp, rfl⟩
  · simp
  · have hs := (sqrt_pos.2 (neg_pos.2 hκ)).ne'
    have h₂ : √(-(κ / c ^ 2)) = √(-κ) / c := by rw [← neg_div, sqrt_div' _ hc2.le, sqrt_sq hc.le]
    rw [curvatureSine_of_neg (div_neg_of_neg_of_pos hκ hc2),
      curvatureCosine_of_neg (div_neg_of_neg_of_pos hκ hc2), curvatureSine_of_neg hκ,
      curvatureCosine_of_neg hκ, h₂, h₃]
    exact ⟨by field_simp, rfl⟩

/-- **Scaling law** of the model sine: `s_(κ/c²)(c t) = c s_κ(t)`. At `c = 0` both sides
vanish. -/
theorem curvatureSine_div_sq_mul (κ c t : ℝ) :
    curvatureSine (κ / c ^ 2) (c * t) = c * curvatureSine κ t := by
  rcases lt_trichotomy 0 c with hc | rfl | hc
  · exact (curvatureSine_div_sq_mul_and_curvatureCosine_div_sq_mul_of_pos hc t).1
  · simp
  · have h := (curvatureSine_div_sq_mul_and_curvatureCosine_div_sq_mul_of_pos (κ := κ)
      (neg_pos.2 hc) (-t)).1
    rwa [neg_sq, neg_mul_neg, curvatureSine_neg, neg_mul_neg] at h

/-- **Scaling law** of the model cosine: `c_(κ/c²)(c t) = c_κ(t)` for `c ≠ 0`. -/
theorem curvatureCosine_div_sq_mul (κ : ℝ) {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    curvatureCosine (κ / c ^ 2) (c * t) = curvatureCosine κ t := by
  rcases hc.lt_or_gt with hc | hc
  · have h := (curvatureSine_div_sq_mul_and_curvatureCosine_div_sq_mul_of_pos (κ := κ)
      (neg_pos.2 hc) (-t)).2
    rwa [neg_sq, neg_mul_neg, curvatureCosine_neg] at h
  · exact (curvatureSine_div_sq_mul_and_curvatureCosine_div_sq_mul_of_pos hc t).2

/-- The curvature sine has unit first-order scale at its origin. -/
theorem tendsto_curvatureSine_div_zero (κ : ℝ) :
    Tendsto (fun t ↦ curvatureSine κ t / t) (𝓝[≠] 0) (𝓝 1) := by
  have heq : (fun t ↦ curvatureSine κ t / t) = slope (curvatureSine κ) 0 := by
    ext t
    simp only [slope_def_field, curvatureSine_zero_right, sub_zero]
  rw [heq]
  simpa only [curvatureCosine_zero_right] using (hasDerivAt_curvatureSine κ 0).tendsto_slope

/-- The model cosine is positive before the spherical half-radius. -/
theorem curvatureCosine_pos {κ t : ℝ} (ht : 0 ≤ t)
    (hbound : 0 < κ → t < π / (2 * √κ)) : 0 < curvatureCosine κ t := by
  rcases lt_trichotomy 0 κ with hκ | rfl | hκ
  · rw [curvatureCosine_of_pos hκ]
    apply cos_pos_of_mem_Ioo
    have hs : 0 < √κ := sqrt_pos.mpr hκ
    have hb := (lt_div_iff₀ (mul_pos (by norm_num) hs)).mp (hbound hκ)
    constructor
    · have := mul_nonneg hs.le ht
      linarith [pi_pos]
    · nlinarith
  · simp
  · rw [curvatureCosine_of_neg hκ]
    exact cosh_pos _

end TauCeti
