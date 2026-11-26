/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.MeasureTheory.Integral.CurveIntegral.Segment

/-!
# The complex slope and the incomplete beta kernel

For a slope `(s, t)` in the open triangle `𝒯 = {s > 0, t > 0, s + t < 1}`, the complex slope
`ξ(s, t) = e^{πis} sin(πt) / sin(π(1 - s - t))` (`complexSlope`) is the apex of the triangle on
`[0, 1]` with angles `πs` at `0` and `πt` at `1`. We prove the law of sines for this triangle,
`1 - ξ = e^{-πit} sin(πs) / sin(π(1 - s - t))` (`one_sub_complexSlope`), read off the arguments
and moduli of `ξ` and `1 - ξ`, and show that `(s, t) ↦ ξ(s, t)` is a bijection from `𝒯` onto the
upper half-plane with inverse `ξ ↦ (arg ξ / π, -arg (1 - ξ) / π)` (`bijOn_complexSlope`,
`complexSlope_arg_div_pi`).

For `v₁ = (x₁, y₁)` and `v₂ = (x₂, y₂)` in `ℤ²`, the incomplete beta kernel
`K_ξ(v₁; v₂) = (2πi)⁻¹ ∫ (1 - z)^(y₁ - y₂) z^(x₂ - x₁ - 1) dz` (`incompleteBetaKernel`) is
integrated from `conj ξ` to `ξ` along the polygonal path through `c = 1/2` when `y₁ ≥ y₂` and
through `c = -1` when `y₁ < y₂`, as a sum of Mathlib's curve integrals along two segments. It
depends only on `v₂ - v₁` (`incompleteBetaKernel_add_right`); on the diagonal it is `arg ξ / π`
for `ξ` in the slit plane `ℂ \ (-∞, 0]` (`incompleteBetaKernel_self`), and along a row it is
`K_ξ(v; v + (m, 0)) = |ξ|^m sin(m arg ξ) / (πm)` for `m ≠ 0` (`incompleteBetaKernel_add_row`).
For `ξ = ξ(s, t)` these are the density `s` and the discrete sine kernel `sin(πsm) / (πm)`
twisted by `|ξ|^m`.

The kernel gives the correlations of the incomplete beta process, the ergodic translation-invariant
Gibbs measure on lozenge tilings of slope `(s, t)`.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. (2023),
  Definitions 1.2 and 1.3.
* A. Okounkov and N. Reshetikhin, *Correlation function of Schur process with application to local
  geometry of a random 3-dimensional Young diagram*, J. Amer. Math. Soc. (2003), Definition 4.
-/

public section

open Complex Set
open scoped Real ComplexConjugate Pointwise

namespace TauCeti

/-! ### The complex slope -/

/-- The complex slope `ξ(s, t) = e^{πis} sin(πt) / sin(π(1 - s - t))` of a slope `(s, t)`. For
`(s, t)` in the open triangle `s > 0`, `t > 0`, `s + t < 1` it is the apex of the triangle on
`[0, 1]` with angles `πs` at `0` and `πt` at `1`. -/
noncomputable def complexSlope (s t : ℝ) : ℂ :=
  exp (↑(π * s) * I) * ↑(Real.sin (π * t) / Real.sin (π * (1 - s - t)))

/-- The defining formula of `complexSlope`. -/
theorem complexSlope_def (s t : ℝ) :
    complexSlope s t = exp (↑(π * s) * I) * ↑(Real.sin (π * t) / Real.sin (π * (1 - s - t))) :=
  (rfl)

private theorem complexSlope_eq_mul (s t : ℝ) :
    complexSlope s t = ↑(Real.sin (π * t) / Real.sin (π * (1 - s - t))) *
      (cos ↑(π * s) + sin ↑(π * s) * I) := by
  rw [complexSlope, exp_mul_I, mul_comm]

/-- **The law of sines** for the triangle `0, 1, ξ(s, t)`:
`1 - ξ = e^{-πit} sin(πs) / sin(π(1 - s - t))`. -/
theorem one_sub_complexSlope {s t : ℝ} (h : Real.sin (π * (1 - s - t)) ≠ 0) :
    1 - complexSlope s t =
      exp (↑(-(π * t)) * I) * ↑(Real.sin (π * s) / Real.sin (π * (1 - s - t))) := by
  have hS : Real.sin (π * (1 - s - t)) =
      Real.sin (π * s) * Real.cos (π * t) + Real.cos (π * s) * Real.sin (π * t) := by
    have hangle : π * (1 - s - t) = π - (π * s + π * t) := by ring
    rw [← Real.sin_add, hangle, Real.sin_pi_sub]
  rw [complexSlope, exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos,
    ← ofReal_sin, Real.cos_neg, Real.sin_neg]
  apply Complex.ext <;>
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, add_re, I_re, I_im, sub_im, one_im,
      mul_im, add_im] <;>
    field_simp
  · rw [hS]
    ring
  · ring

private theorem one_sub_complexSlope_eq_mul {s t : ℝ} (h : Real.sin (π * (1 - s - t)) ≠ 0) :
    1 - complexSlope s t = ↑(Real.sin (π * s) / Real.sin (π * (1 - s - t))) *
      (cos ↑(-(π * t)) + sin ↑(-(π * t)) * I) := by
  rw [one_sub_complexSlope h, exp_mul_I, mul_comm]

/-- On the open triangle, `sin(π(1 - s - t)) > 0`. -/
private theorem sin_pi_mul_one_sub_sub_pos {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s + t < 1) : 0 < Real.sin (π * (1 - s - t)) :=
  sin_pi_mul_pos_of_pos_of_lt_one (by linarith) (by linarith)

/-- On the open triangle, the argument of `ξ(s, t)` is `πs`: the angle of the triangle at `0`. -/
theorem arg_complexSlope {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    arg (complexSlope s t) = π * s := by
  rw [complexSlope_eq_mul]
  refine arg_mul_cos_add_sin_mul_I (div_pos (sin_pi_mul_pos_of_pos_of_lt_one ht (by linarith))
    (sin_pi_mul_one_sub_sub_pos hs ht hst)) ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

/-- On the open triangle, `|ξ(s, t)| = sin(πt) / sin(π(1 - s - t))`: the side opposite the angle
`πt`, by the law of sines. -/
theorem norm_complexSlope {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    ‖complexSlope s t‖ = Real.sin (π * t) / Real.sin (π * (1 - s - t)) := by
  rw [complexSlope, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (sin_pi_mul_pos_of_pos_of_lt_one ht (by linarith))
      (sin_pi_mul_one_sub_sub_pos hs ht hst))]

/-- On the open triangle, `ξ(s, t)` lies in the upper half-plane. -/
theorem im_complexSlope_pos {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    0 < (complexSlope s t).im := by
  rw [complexSlope_eq_mul, ← ofReal_cos, ← ofReal_sin]
  simp only [mul_im, ofReal_re, ofReal_im, add_im, I_re, I_im, zero_mul, mul_zero, add_zero,
    mul_one, zero_add]
  exact mul_pos (div_pos (sin_pi_mul_pos_of_pos_of_lt_one ht (by linarith))
    (sin_pi_mul_one_sub_sub_pos hs ht hst)) (sin_pi_mul_pos_of_pos_of_lt_one hs (by linarith))

/-- On the open triangle, the argument of `1 - ξ(s, t)` is `-πt`: the angle of the triangle at `1`
is `πt`. -/
theorem arg_one_sub_complexSlope {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    arg (1 - complexSlope s t) = -(π * t) := by
  rw [one_sub_complexSlope_eq_mul (sin_pi_mul_one_sub_sub_pos hs ht hst).ne']
  refine arg_mul_cos_add_sin_mul_I (div_pos (sin_pi_mul_pos_of_pos_of_lt_one hs (by linarith))
    (sin_pi_mul_one_sub_sub_pos hs ht hst)) ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

/-- On the open triangle, `|1 - ξ(s, t)| = sin(πs) / sin(π(1 - s - t))`: the side opposite the
angle `πs`, by the law of sines. -/
theorem norm_one_sub_complexSlope {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    ‖1 - complexSlope s t‖ = Real.sin (π * s) / Real.sin (π * (1 - s - t)) := by
  rw [one_sub_complexSlope (sin_pi_mul_one_sub_sub_pos hs ht hst).ne', norm_mul,
    norm_exp_ofReal_mul_I, one_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (sin_pi_mul_pos_of_pos_of_lt_one hs (by linarith))
      (sin_pi_mul_one_sub_sub_pos hs ht hst))]

/-- The complex slope of `(arg ξ / π, -arg (1 - ξ) / π)` is `ξ`, for `ξ` in the upper half-plane:
`ξ` is determined by the angles of the triangle `0, 1, ξ` at `0` and `1`. -/
theorem complexSlope_arg_div_pi {ξ : ℂ} (hξ : 0 < ξ.im) :
    complexSlope (arg ξ / π) (-arg (1 - ξ) / π) = ξ := by
  have h₁ : 1 - ξ ≠ 0 := fun h => by
    have := congrArg im h
    simp at this
    linarith
  have hS : Real.sin (π * (1 - arg ξ / π - -arg (1 - ξ) / π)) = ξ.im / (‖ξ‖ * ‖1 - ξ‖) := by
    rw [← sin_arg_sub_arg_one_sub ξ, ← Real.sin_pi_sub]
    congr 1
    field_simp
    ring
  have ht : Real.sin (π * (-arg (1 - ξ) / π)) = ξ.im / ‖1 - ξ‖ := by
    have hangle : π * (-arg (1 - ξ) / π) = -arg (1 - ξ) := by field_simp
    rw [hangle, Real.sin_neg, sin_arg]
    simp [neg_div]
  have hs : π * (arg ξ / π) = arg ξ := by field_simp
  rw [complexSlope, hS, ht, hs]
  conv_rhs => rw [← norm_mul_exp_arg_mul_I ξ]
  rw [mul_comm]
  congr 2
  field_simp

/-- The complex slope maps the open triangle `s > 0`, `t > 0`, `s + t < 1` bijectively onto the
upper half-plane. -/
theorem bijOn_complexSlope :
    BijOn (fun p : ℝ × ℝ => complexSlope p.1 p.2) {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
      {z | 0 < z.im} := by
  refine ⟨fun p hp => im_complexSlope_pos hp.1 hp.2.1 hp.2.2, fun p hp q hq hpq => ?_,
    fun ξ hξ => ?_⟩
  · have h₁ := congrArg arg hpq
    have h₂ := congrArg (fun z => arg (1 - z)) hpq
    simp only [arg_complexSlope hp.1 hp.2.1 hp.2.2, arg_complexSlope hq.1 hq.2.1 hq.2.2,
      arg_one_sub_complexSlope hp.1 hp.2.1 hp.2.2,
      arg_one_sub_complexSlope hq.1 hq.2.1 hq.2.2] at h₁ h₂
    exact Prod.ext (mul_left_cancel₀ Real.pi_ne_zero h₁)
      (mul_left_cancel₀ Real.pi_ne_zero (neg_injective h₂))
  · have hξ : 0 < ξ.im := hξ
    have h₀ : ξ ≠ 0 := fun h => by simp [h] at hξ
    have h₁ : 1 - ξ ≠ 0 := fun h => by
      have := congrArg im h
      simp at this
      linarith
    have ha : 0 < arg ξ := (arg_nonneg_iff.2 hξ.le).lt_of_ne fun h =>
      (arg_eq_zero_iff.1 h.symm).2.not_gt hξ
    have hb : arg (1 - ξ) < 0 := arg_neg_iff.2 (by simpa using hξ)
    have hsin : 0 < Real.sin (arg ξ - arg (1 - ξ)) := by
      rw [sin_arg_sub_arg_one_sub ξ]
      exact div_pos hξ (mul_pos (norm_pos_iff.2 h₀) (norm_pos_iff.2 h₁))
    have hlt : arg ξ - arg (1 - ξ) < π := by
      by_contra! hle
      have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := arg ξ - arg (1 - ξ) - 2 * π)
        (by linarith [arg_le_pi ξ, neg_pi_lt_arg (1 - ξ)]) (by linarith)
      rw [Real.sin_sub_two_pi] at this
      linarith
    refine ⟨(arg ξ / π, -arg (1 - ξ) / π), ⟨by positivity, div_pos (by linarith) Real.pi_pos, ?_⟩,
      complexSlope_arg_div_pi hξ⟩
    rw [← add_div, div_lt_one Real.pi_pos]
    linarith

/-! ### The incomplete beta kernel -/

/-- The incomplete beta kernel `K_ξ(v₁; v₂) = (2πi)⁻¹ ∫ (1 - z)^(y₁ - y₂) z^(x₂ - x₁ - 1) dz`
from `conj ξ` to `ξ` along the polygonal path through `c = 1/2` when `y₁ ≥ y₂` and through `c = -1`
when `y₁ < y₂`: the sum of Mathlib's curve integrals of the `1`-form `f(z) dz`, written
`v ↦ v • f z`, along `Path.segment (conj ξ) c` and `Path.segment c ξ`. For `ξ` in the upper
half-plane both segments avoid `0` and `1`. -/
noncomputable def incompleteBetaKernel (ξ : ℂ) (v₁ v₂ : ℤ × ℤ) : ℂ :=
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z =>
    ContinuousLinearMap.toSpanSingleton ℂ ((1 - z) ^ (v₁.2 - v₂.2) * z ^ (v₂.1 - v₁.1 - 1))
  let c : ℂ := if v₂.2 ≤ v₁.2 then 1 / 2 else -1
  (2 * π * I)⁻¹ * ((∫ᶜ z in Path.segment (conj ξ) c, ω z) + ∫ᶜ z in Path.segment c ξ, ω z)

/-- The defining formula of `incompleteBetaKernel`. -/
theorem incompleteBetaKernel_def (ξ : ℂ) (v₁ v₂ : ℤ × ℤ) :
    incompleteBetaKernel ξ v₁ v₂ = (2 * π * I)⁻¹ *
      ((∫ᶜ z in Path.segment (conj ξ) (if v₂.2 ≤ v₁.2 then 1 / 2 else -1 : ℂ),
          ContinuousLinearMap.toSpanSingleton ℂ
            ((1 - z) ^ (v₁.2 - v₂.2) * z ^ (v₂.1 - v₁.1 - 1))) +
        ∫ᶜ z in Path.segment (if v₂.2 ≤ v₁.2 then 1 / 2 else -1 : ℂ) ξ,
          ContinuousLinearMap.toSpanSingleton ℂ
            ((1 - z) ^ (v₁.2 - v₂.2) * z ^ (v₂.1 - v₁.1 - 1))) :=
  (rfl)

/-- The incomplete beta kernel depends only on `v₂ - v₁`. -/
theorem incompleteBetaKernel_add_right (ξ : ℂ) (v₁ v₂ w : ℤ × ℤ) :
    incompleteBetaKernel ξ (v₁ + w) (v₂ + w) = incompleteBetaKernel ξ v₁ v₂ := by
  simp only [incompleteBetaKernel, Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub]
  have hc : (if v₂.2 + w.2 ≤ v₁.2 + w.2 then (1 / 2 : ℂ) else -1) =
      if v₂.2 ≤ v₁.2 then 1 / 2 else -1 := by
    simp
  rw [hc]

/-- For `ξ` in the slit plane and `F` a primitive of `f` on the slit plane, the sum of the curve
integrals of `f z dz` along the segments `conj ξ → 1/2 → ξ` is `F ξ - F (conj ξ)`: the case of
`curveIntegral_segment_add_segment_toSpanSingleton_eq_sub` for the slit plane, star-convex at
`1/2`. -/
theorem curveIntegral_conj_half_add_eq_sub {F f : ℂ → ℂ} {ξ : ℂ} (hξ : ξ ∈ slitPlane)
    (hF : ∀ z ∈ slitPlane, HasDerivAt F (f z) z) (hf : ContinuousOn f slitPlane) :
    (∫ᶜ z in Path.segment (conj ξ) (1 / 2 : ℂ), ContinuousLinearMap.toSpanSingleton ℂ (f z)) +
        ∫ᶜ z in Path.segment (1 / 2 : ℂ) ξ, ContinuousLinearMap.toSpanSingleton ℂ (f z) =
      F ξ - F (conj ξ) := by
  have hstar : StarConvex ℝ (1 / 2 : ℂ) slitPlane := by
    simpa using starConvex_ofReal_slitPlane (x := 1 / 2) (by norm_num)
  have hξ' : conj ξ ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hξ ⊢
    simpa using hξ
  exact curveIntegral_segment_add_segment_toSpanSingleton_eq_sub hstar hξ' hξ hF hf

/-- For `ξ` off `[0, ∞)` and `F` a primitive of `f` off `[0, ∞)`, the sum of the curve integrals
of `f z dz` along the segments `conj ξ → -1 → ξ` is `F ξ - F (conj ξ)`: the case of
`curveIntegral_segment_add_segment_toSpanSingleton_eq_sub` for `-slitPlane = ℂ \ [0, ∞)`,
star-convex at `-1`. -/
theorem curveIntegral_conj_neg_one_add_eq_sub {F f : ℂ → ℂ} {ξ : ℂ} (hξ : -ξ ∈ slitPlane)
    (hF : ∀ z, -z ∈ slitPlane → HasDerivAt F (f z) z) (hf : ContinuousOn f (-slitPlane)) :
    (∫ᶜ z in Path.segment (conj ξ) (-1 : ℂ), ContinuousLinearMap.toSpanSingleton ℂ (f z)) +
        ∫ᶜ z in Path.segment (-1 : ℂ) ξ, ContinuousLinearMap.toSpanSingleton ℂ (f z) =
      F ξ - F (conj ξ) := by
  have hstar : StarConvex ℝ (-1 : ℂ) (-slitPlane) := by
    simpa using (starConvex_ofReal_slitPlane (x := 1) one_pos).neg
  have hξ' : -conj ξ ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hξ ⊢
    simpa using hξ
  exact curveIntegral_segment_add_segment_toSpanSingleton_eq_sub hstar hξ' hξ hF hf

/-- **The diagonal of the incomplete beta kernel**: for `ξ` in the slit plane `ℂ \ (-∞, 0]`,
`K_ξ(v; v) = arg ξ / π`, which is `s` for `ξ = ξ(s, t)`. Here the integrand is `z⁻¹`, with
primitive `log z` on the slit plane. It fails off the slit plane: for `ξ = -1` the two segments
are the same segment traversed in opposite directions, so `K_ξ(v; v) = 0 ≠ arg (-1) / π`. -/
theorem incompleteBetaKernel_self {ξ : ℂ} (hξ : ξ ∈ slitPlane) (v : ℤ × ℤ) :
    incompleteBetaKernel ξ v v = arg ξ / π := by
  have hlog := curveIntegral_conj_half_add_eq_sub (F := log) (f := fun z => z⁻¹) hξ
    (fun z hz => (hasStrictDerivAt_log hz).hasDerivAt)
    (continuousOn_inv₀.mono fun z hz => slitPlane_ne_zero hz)
  simp only [incompleteBetaKernel, sub_self, zpow_zero, one_mul, zero_sub, Int.reduceNeg,
    zpow_neg_one]
  have hc : (if v.2 ≤ v.2 then (1 / 2 : ℂ) else -1) = 1 / 2 := by simp
  rw [hc, hlog, log_conj ξ (mem_slitPlane_iff_arg.1 hξ).1, sub_conj, log_im]
  push_cast
  field_simp

/-- **The incomplete beta kernel along a row**: for `m ≠ 0`,
`K_ξ(v; v + (m, 0)) = |ξ|^m sin(m arg ξ) / (πm)`, which is `|ξ|^m sin(πsm) / (πm)` for
`ξ = ξ(s, t)`. Here the integrand is `z^(m - 1)`, with primitive `z^m / m` away from `0`. -/
theorem incompleteBetaKernel_add_row (ξ : ℂ) (v : ℤ × ℤ) {m : ℤ} (hm : m ≠ 0) :
    incompleteBetaKernel ξ v (v + (m, 0)) =
      ((‖ξ‖ ^ m * Real.sin (m * arg ξ) / (π * m) : ℝ) : ℂ) := by
  simp only [incompleteBetaKernel, Prod.fst_add, Prod.snd_add, add_zero, sub_self, zpow_zero,
    one_mul, add_sub_cancel_left]
  have hc : (if v.2 + 0 ≤ v.2 then (1 / 2 : ℂ) else -1) = 1 / 2 := by simp
  rw [hc, ← Complex.im_zpow]
  by_cases him : ξ.im = 0
  · have hc : conj ξ = ξ := conj_eq_iff_im.2 him
    have hreal : (ξ ^ m).im = 0 := by
      rw [← conj_eq_iff_im, map_zpow₀, hc]
    rw [hc, ← Path.segment_symm, curveIntegral_symm, neg_add_cancel, mul_zero, hreal, zero_div,
      ofReal_zero]
  · have hξ : ξ ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr him)
    have hm' : (m : ℂ) ≠ 0 := Int.cast_ne_zero.2 hm
    rw [curveIntegral_conj_half_add_eq_sub (F := fun z => z ^ m / m) (f := fun z => z ^ (m - 1)) hξ
      (fun z hz => by
        simpa [mul_div_cancel_left₀ _ hm'] using
          (hasDerivAt_zpow m z (Or.inl (slitPlane_ne_zero hz))).div_const (m : ℂ))
      ((continuousOn_id.zpow₀ _ fun z hz => Or.inl (slitPlane_ne_zero hz)))]
    rw [div_sub_div_same, ← map_zpow₀, sub_conj]
    push_cast
    field_simp

end TauCeti
