/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Analysis.Calculus.Morse.ShearedTorus
import TauCeti.Analysis.ODE.ScalarLinear
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.HalfAngle

/-!
# Standard profiles for the sheared torus

The sheared metric `g = h(θ) dθ² + (dφ - a(θ) dθ)²` on the torus with angular coordinates
`(θ, φ)` (`TauCeti.shearedTorusMetric`) depends on two profiles: the coefficient `h > 0` of `dθ²`
and the shear `a`. This file constructs explicit smooth `2π`-periodic profiles for which `g` is
standard near the two critical circles of the Morse–Bott function `f = cos θ`, the maximum circle
`C₁ = {θ = 0}` and the minimum circle `C₀ = {θ = π}`, and for which the shear rotates the
trajectories crossing the upper semicircle by a prescribed angle `A`.

* **The shear** `TauCeti.shearedTorusShear A` is the bump `θ ↦ expNegInvGlue (sin θ - 1/2)`,
  normalized so that `∫₀^π a = A` (`TauCeti.integral_shearedTorusShear`). It is smooth,
  `2π`-periodic and, for `A > 0`, positive exactly where `sin θ > 1/2`
  (`TauCeti.shearedTorusShear_pos_iff`), that is on `(π/6, 5π/6)` modulo `2π`. So it vanishes on
  the lower semicircle and wherever `|cos θ| ≥ 9/10`, a neighbourhood of both critical circles.
* **The coefficient** `TauCeti.shearedTorusCoeff` interpolates, through a smooth cutoff in
  `cos θ`, between `cos² (θ/2) / 2` where `cos θ ≥ 9/10` and `sin² (θ/2) / 2` where
  `cos θ ≤ -9/10`. It is smooth, `2π`-periodic, even and positive
  (`TauCeti.shearedTorusCoeff_pos`); by `TauCeti.det_toMatrix_shearedTorusMetric` it is the
  Gram determinant of `g` in the coordinates `(θ, φ)`.
* **Signed Morse coordinates.** Near `C₁` the coordinate `x = √2 sin (θ/2)`
  (`TauCeti.shearedTorusMaxCoord`) writes `f = 1 - x²`, and near `C₀` the coordinate
  `y = √2 cos (θ/2)` (`TauCeti.shearedTorusMinCoord`) writes `f = y² - 1`. Where `cos θ ≥ 9/10`
  and `a θ = 0`, the metric for the coefficient `TauCeti.shearedTorusCoeff` is the Euclidean
  metric `dx² + dφ²` (`TauCeti.shearedTorusMetric_shearedTorusCoeff_of_le_cos`), and the negative
  gradient of `f` is the linear field `2 x ∂_x`
  (`TauCeti.shearedTorusField_shearedTorusCoeff_of_le_cos`); along its trajectories
  `x(t) = e^{2t} x(0)` (`TauCeti.shearedTorusMaxCoord_eq_exp_mul_of_hasDerivAt`). Symmetrically,
  where `cos θ ≤ -9/10` the metric is `dy² + dφ²` and the field is `-2 y ∂_y`, with
  `y(t) = e^{-2t} y(0)`. Since the shear vanishes there, `φ` stays constant
  (`TauCeti.snd_eq_of_hasDerivAt_shearedTorusField`). These are the normal forms `f = 1 - x²`
  and `f = -1 + y²` with the Euclidean metric, in which the local negative flow fixes the point
  of the critical circle and is linear on the normal line.
* **The endpoint maps.** For these profiles a trajectory leaving the maximum circle at angle `c`
  through the upper semicircle arrives at `(π, c + A)`
  (`tendsto_atTop_of_hasDerivAt_shearedTorusField_shearedTorusShear_of_mem_Ioo_zero_pi`, in the
  namespace `TauCeti`), while one through the lower semicircle arrives at `(-π, c)`, the same
  point of `C₀` as `(π, c)`
  (`tendsto_atTop_of_hasDerivAt_shearedTorusField_shearedTorusShear_of_mem_Ioo_neg_pi_zero`).
  The two endpoint maps are the rotation `R_A` and the identity, whose difference is the Bott
  trajectory correspondence of the sheared torus.

## Main declarations

* `TauCeti.shearedTorusShear`: the shear profile, with `TauCeti.integral_shearedTorusShear`.
* `TauCeti.shearedTorusCoeff`: the coefficient of `dθ²`, with `TauCeti.shearedTorusCoeff_pos`,
  `TauCeti.shearedTorusCoeff_of_le_cos` and `TauCeti.shearedTorusCoeff_of_cos_le`.
* `TauCeti.shearedTorusMaxCoord`, `TauCeti.shearedTorusMinCoord`: the signed Morse coordinates.
* `TauCeti.shearedTorusMetric_shearedTorusCoeff_of_le_cos`,
  `TauCeti.shearedTorusMetric_shearedTorusCoeff_of_cos_le`: the metric is Euclidean in them.
* `TauCeti.shearedTorusField_shearedTorusCoeff_of_le_cos`,
  `TauCeti.shearedTorusField_shearedTorusCoeff_of_cos_le`: the negative gradient is linear in them.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2 (Morse–Bott homology via trajectory correspondences
  between critical submanifolds).
-/

public section

noncomputable section

open Real Set Filter Topology Function
open scoped ContDiff

namespace TauCeti

/-! ### The shear profile -/

/-- The bump `θ ↦ expNegInvGlue (sin θ - 1/2)` is continuous. -/
private theorem continuous_shearBump : Continuous fun θ ↦ expNegInvGlue (sin θ - 2⁻¹) :=
  (expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_sin.sub continuous_const)

/-- The bump `θ ↦ expNegInvGlue (sin θ - 1/2)` has positive integral over `[0, π]`. -/
private theorem integral_shearBump_pos : 0 < ∫ θ in (0 : ℝ)..π, expNegInvGlue (sin θ - 2⁻¹) :=
  calc (0 : ℝ) < ∫ θ in (π / 6)..(5 * π / 6), expNegInvGlue (sin θ - 2⁻¹) :=
        intervalIntegral.intervalIntegral_pos_of_pos_on
          (continuous_shearBump.intervalIntegrable _ _)
          (fun _ hθ ↦ expNegInvGlue.pos_of_pos (sub_pos.2 (two_inv_lt_sin_of_mem_Ioo hθ)))
          (by linarith [pi_pos])
    _ ≤ ∫ θ in (0 : ℝ)..π, expNegInvGlue (sin θ - 2⁻¹) :=
        intervalIntegral.integral_mono_interval (by positivity) (by linarith [pi_pos])
          (by linarith [pi_pos]) (MeasureTheory.ae_of_all _ fun _ ↦ expNegInvGlue.nonneg _)
          (continuous_shearBump.intervalIntegrable _ _)

/-- The shear profile with total twist `A` over the upper semicircle: the bump
`expNegInvGlue (sin θ - 1/2)`, supported where `sin θ ≥ 1/2`, normalized to have integral `A`
over `[0, π]`. -/
def shearedTorusShear (A θ : ℝ) : ℝ :=
  A * (expNegInvGlue (sin θ - 2⁻¹) / ∫ s in (0 : ℝ)..π, expNegInvGlue (sin s - 2⁻¹))

/-- The value of the shear profile: the normalized bump `expNegInvGlue (sin θ - 1/2)`. -/
theorem shearedTorusShear_apply (A θ : ℝ) : shearedTorusShear A θ =
    A * (expNegInvGlue (sin θ - 2⁻¹) / ∫ s in (0 : ℝ)..π, expNegInvGlue (sin s - 2⁻¹)) := by
  rw [shearedTorusShear]

/-- The shear profile is smooth. -/
theorem contDiff_shearedTorusShear (A : ℝ) : ContDiff ℝ ∞ (shearedTorusShear A) :=
  contDiff_const.mul ((expNegInvGlue.contDiff.comp (contDiff_sin.sub contDiff_const)).div_const _)

/-- The shear profile is `2π`-periodic. -/
theorem periodic_shearedTorusShear (A : ℝ) : Periodic (shearedTorusShear A) (2 * π) :=
  fun θ ↦ by simp [shearedTorusShear]

/-- The shear profile with a nonnegative twist is nonnegative. -/
theorem shearedTorusShear_nonneg {A : ℝ} (hA : 0 ≤ A) (θ : ℝ) : 0 ≤ shearedTorusShear A θ :=
  mul_nonneg hA (div_nonneg (expNegInvGlue.nonneg _) integral_shearBump_pos.le)

/-- The shear profile vanishes where `sin θ ≤ 1/2`. -/
theorem shearedTorusShear_eq_zero_of_sin_le {A θ : ℝ} (hθ : sin θ ≤ 2⁻¹) :
    shearedTorusShear A θ = 0 := by
  rw [shearedTorusShear, expNegInvGlue.zero_of_nonpos (sub_nonpos.2 hθ), zero_div, mul_zero]

/-- **The support of the shear profile.** For a positive twist, the shear profile is positive
exactly where `sin θ > 1/2`, that is on `(π/6, 5π/6)` modulo `2π`. -/
theorem shearedTorusShear_pos_iff {A : ℝ} (hA : 0 < A) {θ : ℝ} :
    0 < shearedTorusShear A θ ↔ 2⁻¹ < sin θ := by
  refine ⟨fun h ↦ not_le.1 fun hθ ↦ h.ne' (shearedTorusShear_eq_zero_of_sin_le hθ), fun hθ ↦ ?_⟩
  exact mul_pos hA (div_pos (expNegInvGlue.pos_of_pos (sub_pos.2 hθ)) integral_shearBump_pos)

/-- The shear profile vanishes on the lower semicircle `[-π, 0]`. -/
theorem eqOn_shearedTorusShear_Icc_neg_pi_zero (A : ℝ) :
    EqOn (shearedTorusShear A) 0 (Icc (-π) 0) := fun _ hθ ↦
  shearedTorusShear_eq_zero_of_sin_le
    ((sin_nonpos_of_nonpos_of_neg_pi_le hθ.2 hθ.1).trans (by norm_num))

/-- The shear profile vanishes where `|cos θ| ≥ 9/10`, a neighbourhood of the two critical
circles `θ = 0` and `θ = π`. -/
theorem shearedTorusShear_eq_zero_of_le_abs_cos {A θ : ℝ} (hθ : 9 / 10 ≤ |cos θ|) :
    shearedTorusShear A θ = 0 := by
  refine shearedTorusShear_eq_zero_of_sin_le (not_lt.1 fun hs ↦ ?_)
  have hc : (9 / 10) ^ 2 ≤ cos θ ^ 2 := by
    rw [← sq_abs (cos θ)]
    exact pow_le_pow_left₀ (by norm_num) hθ 2
  nlinarith [sin_sq_add_cos_sq θ]

/-- **The twist of the shear profile.** The integral of the shear profile over the upper
semicircle `[0, π]` is `A`. -/
@[simp]
theorem integral_shearedTorusShear (A : ℝ) : ∫ θ in (0 : ℝ)..π, shearedTorusShear A θ = A := by
  simp only [shearedTorusShear, intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    div_self integral_shearBump_pos.ne', mul_one]

/-! ### The coefficient of `dθ²` -/

/-- The cutoff `smoothTransition ((c + 9/10) · 5/9)` in `c = cos θ`: it is `0` where
`cos θ ≤ -9/10` and `1` where `cos θ ≥ 9/10`. -/
private def coeffCutoff (θ : ℝ) : ℝ := smoothTransition ((cos θ + 9 / 10) * (5 / 9))

private theorem coeffCutoff_of_le_cos {θ : ℝ} (hθ : 9 / 10 ≤ cos θ) : coeffCutoff θ = 1 :=
  smoothTransition.one_of_one_le (by linarith)

private theorem coeffCutoff_of_cos_le {θ : ℝ} (hθ : cos θ ≤ -(9 / 10)) : coeffCutoff θ = 0 :=
  smoothTransition.zero_of_nonpos (by nlinarith)

/-- The coefficient of `dθ²` of the standard sheared metric: the interpolation
`((1 + cos θ) χ + (1 - cos θ) (1 - χ)) / 4` for a smooth cutoff `χ` of `cos θ` which is `1`
where `cos θ ≥ 9/10` and `0` where `cos θ ≤ -9/10`. There it is `cos² (θ/2) / 2` and
`sin² (θ/2) / 2` respectively (`TauCeti.shearedTorusCoeff_of_le_cos`,
`TauCeti.shearedTorusCoeff_of_cos_le`), which make the sheared metric Euclidean in the signed Morse
coordinates of the two critical circles of `cos θ`. -/
def shearedTorusCoeff (θ : ℝ) : ℝ :=
  ((1 + cos θ) * coeffCutoff θ + (1 - cos θ) * (1 - coeffCutoff θ)) / 4

/-- The value of the coefficient: the interpolation through the cutoff
`smoothTransition ((cos θ + 9/10) · 5/9)`, which is `1` where `cos θ ≥ 9/10` and `0` where
`cos θ ≤ -9/10`. -/
theorem shearedTorusCoeff_apply (θ : ℝ) : shearedTorusCoeff θ =
    ((1 + cos θ) * smoothTransition ((cos θ + 9 / 10) * (5 / 9)) +
      (1 - cos θ) * (1 - smoothTransition ((cos θ + 9 / 10) * (5 / 9)))) / 4 := by
  rw [shearedTorusCoeff, coeffCutoff]

/-- The coefficient is a smooth function of `cos θ`. -/
private theorem shearedTorusCoeff_eq_comp_cos :
    shearedTorusCoeff = (fun c ↦ ((1 + c) * smoothTransition ((c + 9 / 10) * (5 / 9)) +
      (1 - c) * (1 - smoothTransition ((c + 9 / 10) * (5 / 9)))) / 4) ∘ cos :=
  rfl

/-- The coefficient is smooth. -/
theorem contDiff_shearedTorusCoeff : ContDiff ℝ ∞ shearedTorusCoeff := by
  rw [shearedTorusCoeff_eq_comp_cos]
  refine ContDiff.comp ?_ contDiff_cos
  have hχ : ContDiff ℝ ∞ fun c : ℝ ↦ smoothTransition ((c + 9 / 10) * (5 / 9)) :=
    smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).mul contDiff_const)
  exact (((contDiff_const.add contDiff_id).mul hχ).add
    ((contDiff_const.sub contDiff_id).mul (contDiff_const.sub hχ))).div_const _

/-- The coefficient is `2π`-periodic. -/
theorem periodic_shearedTorusCoeff : Periodic shearedTorusCoeff (2 * π) :=
  fun θ ↦ by simp [shearedTorusCoeff, coeffCutoff]

/-- The coefficient is even. -/
theorem even_shearedTorusCoeff : shearedTorusCoeff.Even :=
  fun θ ↦ by simp [shearedTorusCoeff, coeffCutoff]

/-- **Positivity of the coefficient.** The coefficient is positive, so the sheared metric for it is
a Riemannian metric (`TauCeti.shearedTorusMetric_self_pos`). -/
theorem shearedTorusCoeff_pos (θ : ℝ) : 0 < shearedTorusCoeff θ := by
  -- A convex combination of `1 + cos θ ≥ 0` and `1 - cos θ ≥ 0`; the cutoff is `1` where the
  -- second vanishes and `0` where the first does.
  have h0 := smoothTransition.nonneg ((cos θ + 9 / 10) * (5 / 9))
  have h1 := smoothTransition.le_one ((cos θ + 9 / 10) * (5 / 9))
  have hc₀ := neg_one_le_cos θ
  have hc₁ := cos_le_one θ
  unfold shearedTorusCoeff
  rcases eq_or_lt_of_le hc₁ with h | h
  · rw [coeffCutoff_of_le_cos (by linarith), h]
    norm_num
  rcases eq_or_lt_of_le hc₀ with h' | h'
  · rw [coeffCutoff_of_cos_le (by linarith), ← h']
    norm_num
  unfold coeffCutoff
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + cos θ) h0,
    mul_nonneg (by linarith : 0 ≤ 1 - cos θ) (sub_nonneg.2 h1)]

/-- Near the maximum circle, where `cos θ ≥ 9/10`, the coefficient is `cos² (θ/2) / 2`. -/
theorem shearedTorusCoeff_of_le_cos {θ : ℝ} (hθ : 9 / 10 ≤ cos θ) :
    shearedTorusCoeff θ = cos (θ / 2) ^ 2 / 2 := by
  rw [shearedTorusCoeff, coeffCutoff_of_le_cos hθ, cos_half_sq]
  ring

/-- Near the minimum circle, where `cos θ ≤ -9/10`, the coefficient is `sin² (θ/2) / 2`. -/
theorem shearedTorusCoeff_of_cos_le {θ : ℝ} (hθ : cos θ ≤ -(9 / 10)) :
    shearedTorusCoeff θ = sin (θ / 2) ^ 2 / 2 := by
  rw [shearedTorusCoeff, coeffCutoff_of_cos_le hθ, sin_half_sq]
  ring

/-! ### Signed Morse coordinates near the critical circles -/

/-- The signed Morse coordinate `x = √2 sin (θ/2)` near the maximum circle `θ = 0`, in which
`cos θ = 1 - x²` (`TauCeti.cos_eq_one_sub_shearedTorusMaxCoord_sq`). -/
def shearedTorusMaxCoord (θ : ℝ) : ℝ := √2 * sin (θ / 2)

/-- The signed Morse coordinate `y = √2 cos (θ/2)` near the minimum circle `θ = π`, in which
`cos θ = y² - 1` (`TauCeti.cos_eq_shearedTorusMinCoord_sq_sub_one`). -/
def shearedTorusMinCoord (θ : ℝ) : ℝ := √2 * cos (θ / 2)

/-- The value of the coordinate `x` near the maximum circle. -/
theorem shearedTorusMaxCoord_apply (θ : ℝ) : shearedTorusMaxCoord θ = √2 * sin (θ / 2) := by
  rw [shearedTorusMaxCoord]

/-- The value of the coordinate `y` near the minimum circle. -/
theorem shearedTorusMinCoord_apply (θ : ℝ) : shearedTorusMinCoord θ = √2 * cos (θ / 2) := by
  rw [shearedTorusMinCoord]

/-- `√2 ^ 2 = 2`. -/
private theorem sqrt_two_sq : √2 ^ 2 = 2 :=
  sq_sqrt zero_le_two

/-- `(x / √2) ^ 2 = x ^ 2 / 2`. -/
private theorem div_sqrt_two_sq (x : ℝ) : (x / √2) ^ 2 = x ^ 2 / 2 := by
  rw [div_pow, sqrt_two_sq]

/-- Near the maximum circle, `cos θ = 1 - x²`. -/
theorem cos_eq_one_sub_shearedTorusMaxCoord_sq (θ : ℝ) :
    cos θ = 1 - shearedTorusMaxCoord θ ^ 2 := by
  rw [shearedTorusMaxCoord, mul_pow, sqrt_two_sq, sin_half_sq]
  ring

/-- Near the minimum circle, `cos θ = y² - 1`. -/
theorem cos_eq_shearedTorusMinCoord_sq_sub_one (θ : ℝ) :
    cos θ = shearedTorusMinCoord θ ^ 2 - 1 := by
  rw [shearedTorusMinCoord, mul_pow, sqrt_two_sq, cos_half_sq]
  ring

/-- The derivative of the coordinate `x = √2 sin (θ/2)` is `cos (θ/2) / √2`. -/
theorem hasDerivAt_shearedTorusMaxCoord (θ : ℝ) :
    HasDerivAt shearedTorusMaxCoord (cos (θ / 2) / √2) θ := by
  have h := (((hasDerivAt_id' θ).div_const 2).sin).const_mul √2
  rwa [show √2 * (cos (θ / 2) * (1 / 2)) = cos (θ / 2) / √2 by
    rw [eq_div_iff (sqrt_ne_zero'.2 two_pos)]; linear_combination cos (θ / 2) / 2 * sqrt_two_sq]
    at h

/-- The derivative of the coordinate `y = √2 cos (θ/2)` is `-sin (θ/2) / √2`. -/
theorem hasDerivAt_shearedTorusMinCoord (θ : ℝ) :
    HasDerivAt shearedTorusMinCoord (-(sin (θ / 2) / √2)) θ := by
  have h := (((hasDerivAt_id' θ).div_const 2).cos).const_mul √2
  rwa [show √2 * (-sin (θ / 2) * (1 / 2)) = -(sin (θ / 2) / √2) by
    rw [neg_div', eq_div_iff (sqrt_ne_zero'.2 two_pos)]
    linear_combination -sin (θ / 2) / 2 * sqrt_two_sq] at h

/-- The coordinate `x` is strictly increasing on `[-π, π]`, so it is a coordinate on the
neighbourhood `(-π, π)` of the maximum circle. -/
theorem strictMonoOn_shearedTorusMaxCoord : StrictMonoOn shearedTorusMaxCoord (Icc (-π) π) :=
  fun _ hx _ hy hxy ↦ mul_lt_mul_of_pos_left
    (strictMonoOn_sin ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith))
    (sqrt_pos.2 two_pos)

/-- The coordinate `y` is strictly decreasing on `[0, 2π]`, so it is a coordinate on the
neighbourhood `(0, 2π)` of the minimum circle. -/
theorem strictAntiOn_shearedTorusMinCoord : StrictAntiOn shearedTorusMinCoord (Icc 0 (2 * π)) :=
  fun _ hx _ hy hxy ↦ mul_lt_mul_of_pos_left
    (strictAntiOn_cos ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith))
    (sqrt_pos.2 two_pos)

/-- Where `cos θ ≥ 9/10`, `cos (θ/2) ≠ 0`. -/
private theorem cos_half_ne_zero_of_le_cos {θ : ℝ} (hθ : 9 / 10 ≤ cos θ) : cos (θ / 2) ≠ 0 := by
  intro h
  have := cos_half_sq θ
  rw [h, zero_pow two_ne_zero] at this
  linarith

/-- Where `cos θ ≤ -9/10`, `sin (θ/2) ≠ 0`. -/
private theorem sin_half_ne_zero_of_cos_le {θ : ℝ} (hθ : cos θ ≤ -(9 / 10)) :
    sin (θ / 2) ≠ 0 := by
  intro h
  have := sin_half_sq θ
  rw [h, zero_pow two_ne_zero] at this
  linarith

variable {a : ℝ → ℝ}

/-- **The metric is Euclidean near the maximum circle.** Where `cos θ ≥ 9/10` and the shear
vanishes, the sheared metric for the coefficient `TauCeti.shearedTorusCoeff` is `dx² + dφ²` in the
signed Morse coordinate `x = √2 sin (θ/2)`, whose differential is `cos (θ/2) / √2 dθ`. -/
theorem shearedTorusMetric_shearedTorusCoeff_of_le_cos {θ : ℝ} (hθ : 9 / 10 ≤ cos θ)
    (ha : a θ = 0) (v w : ℝ × ℝ) :
    shearedTorusMetric shearedTorusCoeff a θ v w =
      cos (θ / 2) / √2 * v.1 * (cos (θ / 2) / √2 * w.1) + v.2 * w.2 := by
  rw [shearedTorusMetric_apply, shearedTorusCoeff_of_le_cos hθ, ha]
  linear_combination -(v.1 * w.1) * div_sqrt_two_sq (cos (θ / 2))

/-- **The metric is Euclidean near the minimum circle.** Where `cos θ ≤ -9/10` and the shear
vanishes, the sheared metric for the coefficient `TauCeti.shearedTorusCoeff` is `dy² + dφ²` in the
signed Morse coordinate `y = √2 cos (θ/2)`, whose differential is `-sin (θ/2) / √2 dθ`. -/
theorem shearedTorusMetric_shearedTorusCoeff_of_cos_le {θ : ℝ} (hθ : cos θ ≤ -(9 / 10))
    (ha : a θ = 0) (v w : ℝ × ℝ) :
    shearedTorusMetric shearedTorusCoeff a θ v w =
      -(sin (θ / 2) / √2) * v.1 * (-(sin (θ / 2) / √2) * w.1) + v.2 * w.2 := by
  rw [shearedTorusMetric_apply, shearedTorusCoeff_of_cos_le hθ, ha]
  linear_combination -(v.1 * w.1) * div_sqrt_two_sq (sin (θ / 2))

/-- Where `cos θ ≥ 9/10`, the `θ`-component of the negative gradient, read in the coordinate
`x`, is `2 x`. -/
private theorem mul_shearedTorusField_fst_of_le_cos {θ : ℝ} (hθ : 9 / 10 ≤ cos θ) (p : ℝ × ℝ)
    (hp : p.1 = θ) :
    cos (θ / 2) / √2 * (shearedTorusField shearedTorusCoeff a p).1 =
      2 * shearedTorusMaxCoord θ := by
  have hc := cos_half_ne_zero_of_le_cos hθ
  rw [shearedTorusField_apply, hp, shearedTorusCoeff_of_le_cos hθ, shearedTorusMaxCoord,
    show sin θ = sin (2 * (θ / 2)) by ring_nf, sin_two_mul]
  field_simp
  linear_combination -sin (θ / 2) * sqrt_two_sq

/-- Where `cos θ ≤ -9/10`, the `θ`-component of the negative gradient, read in the coordinate
`y`, is `-2 y`. -/
private theorem mul_shearedTorusField_fst_of_cos_le {θ : ℝ} (hθ : cos θ ≤ -(9 / 10))
    (p : ℝ × ℝ) (hp : p.1 = θ) :
    -(sin (θ / 2) / √2) * (shearedTorusField shearedTorusCoeff a p).1 =
      -(2 * shearedTorusMinCoord θ) := by
  have hs := sin_half_ne_zero_of_cos_le hθ
  rw [shearedTorusField_apply, hp, shearedTorusCoeff_of_cos_le hθ, shearedTorusMinCoord,
    show sin θ = sin (2 * (θ / 2)) by ring_nf, sin_two_mul]
  field_simp
  linear_combination cos (θ / 2) * sqrt_two_sq

/-- **The negative gradient is linear near the maximum circle.** Where `cos θ ≥ 9/10` and the
shear vanishes, the negative gradient of `cos θ` for the coefficient `TauCeti.shearedTorusCoeff`,
read in the coordinates `(x, φ)`, is the linear field `2 x ∂_x` of the normal form `f = 1 - x²`.
-/
theorem shearedTorusField_shearedTorusCoeff_of_le_cos {θ : ℝ} (hθ : 9 / 10 ≤ cos θ)
    (ha : a θ = 0) (φ : ℝ) :
    (cos (θ / 2) / √2 * (shearedTorusField shearedTorusCoeff a (θ, φ)).1,
      (shearedTorusField shearedTorusCoeff a (θ, φ)).2) = (2 * shearedTorusMaxCoord θ, 0) := by
  rw [mul_shearedTorusField_fst_of_le_cos hθ _ rfl, shearedTorusField_apply, ha, zero_mul]

/-- **The negative gradient is linear near the minimum circle.** Where `cos θ ≤ -9/10` and the
shear vanishes, the negative gradient of `cos θ` for the coefficient `TauCeti.shearedTorusCoeff`,
read in the coordinates `(y, φ)`, is the linear field `-2 y ∂_y` of the normal form
`f = -1 + y²`. -/
theorem shearedTorusField_shearedTorusCoeff_of_cos_le {θ : ℝ} (hθ : cos θ ≤ -(9 / 10))
    (ha : a θ = 0) (φ : ℝ) :
    (-(sin (θ / 2) / √2) * (shearedTorusField shearedTorusCoeff a (θ, φ)).1,
      (shearedTorusField shearedTorusCoeff a (θ, φ)).2) = (-(2 * shearedTorusMinCoord θ), 0) := by
  rw [mul_shearedTorusField_fst_of_cos_le hθ _ rfl, shearedTorusField_apply, ha, zero_mul]

variable {γ : ℝ → ℝ × ℝ}

/-- **The linear flow near the maximum circle.** If an integral curve of the negative gradient
for the coefficient `TauCeti.shearedTorusCoeff` stays where `cos θ ≥ 9/10` between the times `0`
and `t`, then its coordinate `x` is multiplied by `e^{2t}`. -/
theorem shearedTorusMaxCoord_eq_exp_mul_of_hasDerivAt
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField shearedTorusCoeff a (γ t)) t) {t : ℝ}
    (hθ : ∀ s ∈ uIcc 0 t, 9 / 10 ≤ cos (γ s).1) :
    shearedTorusMaxCoord (γ t).1 = exp (2 * t) * shearedTorusMaxCoord (γ 0).1 := by
  have h := eq_exp_smul_of_hasDerivAt_smul (v := fun s ↦ shearedTorusMaxCoord (γ s).1) (c := 2)
    (s := 0) (t := t) fun s hs ↦ by
    have hd := (hasDerivAt_shearedTorusMaxCoord (γ s).1).comp s
      (hasDerivAt_fst_of_hasDerivAt_shearedTorusField hγ s)
    exact hd.congr_deriv (by
      rw [smul_eq_mul]
      simpa only [shearedTorusField_apply] using
        mul_shearedTorusField_fst_of_le_cos (a := a) (hθ s hs) (γ s) rfl)
  rwa [sub_zero, smul_eq_mul] at h

/-- **The linear flow near the minimum circle.** If an integral curve of the negative gradient
for the coefficient `TauCeti.shearedTorusCoeff` stays where `cos θ ≤ -9/10` between the times `0`
and `t`, then its coordinate `y` is multiplied by `e^{-2t}`. -/
theorem shearedTorusMinCoord_eq_exp_neg_mul_of_hasDerivAt
    (hγ : ∀ t, HasDerivAt γ (shearedTorusField shearedTorusCoeff a (γ t)) t) {t : ℝ}
    (hθ : ∀ s ∈ uIcc 0 t, cos (γ s).1 ≤ -(9 / 10)) :
    shearedTorusMinCoord (γ t).1 = exp (-2 * t) * shearedTorusMinCoord (γ 0).1 := by
  have h := eq_exp_smul_of_hasDerivAt_smul (v := fun s ↦ shearedTorusMinCoord (γ s).1) (c := -2)
    (s := 0) (t := t) fun s hs ↦ by
    have hd := (hasDerivAt_shearedTorusMinCoord (γ s).1).comp s
      (hasDerivAt_fst_of_hasDerivAt_shearedTorusField hγ s)
    exact hd.congr_deriv (by
      rw [smul_eq_mul, neg_mul (2 : ℝ)]
      simpa only [shearedTorusField_apply] using
        mul_shearedTorusField_fst_of_cos_le (a := a) (hθ s hs) (γ s) rfl)
  rwa [sub_zero, smul_eq_mul] at h

/-! ### The endpoint maps of the two families of trajectories -/

section Endpoints

variable {A c : ℝ} (hγ : ∀ t, HasDerivAt γ (shearedTorusField shearedTorusCoeff
  (shearedTorusShear A) (γ t)) t)
include hγ

/-- **The upper family is rotated by `A`.** For the standard profiles, a trajectory through the
upper semicircle leaving the maximum circle at `(0, c)` arrives at `(π, c + A)` on the minimum
circle. -/
theorem tendsto_atTop_of_hasDerivAt_shearedTorusField_shearedTorusShear_of_mem_Ioo_zero_pi
    (h0 : (γ 0).1 ∈ Ioo 0 π) (hc : Tendsto γ atBot (𝓝 (0, c))) :
    Tendsto γ atTop (𝓝 (π, c + A)) := by
  have hh := contDiff_shearedTorusCoeff.of_le (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ∞)
  have ha := (contDiff_shearedTorusShear A).continuous
  have hsrc := tendsto_nhds_unique hc
    (tendsto_atBot_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi hh
      periodic_shearedTorusCoeff shearedTorusCoeff_pos ha hγ h0)
  rw [show c = _ from congrArg Prod.snd hsrc]
  simpa using tendsto_atTop_of_hasDerivAt_shearedTorusField_of_mem_Ioo_zero_pi hh
    periodic_shearedTorusCoeff shearedTorusCoeff_pos ha hγ h0

/-- **The lower family is not rotated.** For the standard profiles, a trajectory through the lower
semicircle leaving the maximum circle at `(0, c)` arrives at `(-π, c)`, the same point of the
minimum circle as `(π, c)`. -/
theorem tendsto_atTop_of_hasDerivAt_shearedTorusField_shearedTorusShear_of_mem_Ioo_neg_pi_zero
    (h0 : (γ 0).1 ∈ Ioo (-π) 0) (hc : Tendsto γ atBot (𝓝 (0, c))) :
    Tendsto γ atTop (𝓝 (-π, c)) := by
  have hh := contDiff_shearedTorusCoeff.of_le (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ∞)
  have ha := (contDiff_shearedTorusShear A).continuous
  have hsrc := tendsto_nhds_unique hc
    (tendsto_atBot_of_hasDerivAt_shearedTorusField_of_mem_Ioo_neg_pi_zero hh
      periodic_shearedTorusCoeff shearedTorusCoeff_pos ha hγ h0)
  rw [show c = _ from congrArg Prod.snd hsrc]
  exact tendsto_atTop_of_hasDerivAt_shearedTorusField_of_mem_Ioo_neg_pi_zero_of_eqOn hh
    periodic_shearedTorusCoeff shearedTorusCoeff_pos ha hγ
    (eqOn_shearedTorusShear_Icc_neg_pi_zero A) h0

end Endpoints

end TauCeti
