/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Kernel
import Mathlib.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Contour.Primitive

/-!
# Independence of the incomplete beta kernel from the contour

The incomplete beta kernel `K_ξ(v₁; v₂) = (2πi)⁻¹ ∫ (1 - z)^(y₁ - y₂) z^(x₂ - x₁ - 1) dz`
(`incompleteBetaKernel`) is defined by integrating from `conj ξ` to `ξ` along the polygonal path
through `1/2` when `y₁ ≥ y₂` and through `-1` when `y₁ < y₂`. We show that any piecewise-`C¹`
curve from `conj ξ` to `ξ` meeting the real axis only on the prescribed side, in `(0, 1)` when
`y₁ ≥ y₂` (`incompleteBetaKernel_eq_intervalIntegral_of_le`) and in `(-∞, 0)` when `y₁ < y₂`
(`incompleteBetaKernel_eq_intervalIntegral_of_lt`), gives the same value. Such a curve may cross
the real axis any number of times, as long as it does so on that side.

The curves of the first kind lie in `ℂ \ ((-∞, 0] ∪ [1, ∞))`, those of the second kind in
`ℂ \ [0, ∞)`: planes slit along the complement of a real interval, which are open and star-shaped
about every point of the interval (`TauCeti.starConvex_setOf_im_ne_zero_or_re_mem`), in particular
about `1/2` and about `-1`, the vertices of the defining polygons. They contain no pole of the
integrand. So the integrand has a primitive there (`TauCeti.Contour.isExactOn_of_starConvex`, from
the homology form of Cauchy's theorem), and the contour integral along any piecewise-`C¹` curve in
the set, like the curve integrals along the two segments of the polygon, is the difference of its
values at the endpoints
(`TauCeti.Contour.curveIntegral_segment_add_segment_eq_intervalIntegral_deriv_smul`).

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. (2023),
  Definition 1.3.
* A. Okounkov and N. Reshetikhin, *Correlation function of Schur process with application to local
  geometry of a random 3-dimensional Young diagram*, J. Amer. Math. Soc. (2003), Definition 4.
-/

public section

open Complex Set MeasureTheory
open scoped Real ComplexConjugate

namespace TauCeti

/-- A point of the plane slit along the complement of a real set `S` avoiding `0` and `1` is
neither `0` nor `1`. -/
private theorem ne_zero_and_one_sub_ne_zero {S : Set ℝ} (h₀ : (0 : ℝ) ∉ S) (h₁ : (1 : ℝ) ∉ S)
    {z : ℂ} (hz : z.im ≠ 0 ∨ z.re ∈ S) : z ≠ 0 ∧ 1 - z ≠ 0 := by
  rcases hz with hz | hz
  · refine ⟨fun h => hz (by simp [h]), fun h => hz ?_⟩
    simpa using congrArg im h
  · refine ⟨fun h => h₀ (by simpa [h] using hz), fun h => h₁ ?_⟩
    simpa [(sub_eq_zero.mp h).symm] using hz

/-- The integrand `(1 - z)^m z^n` is holomorphic on any set avoiding `0` and `1`. -/
private theorem differentiableOn_one_sub_zpow_mul_zpow {S : Set ℂ} (m n : ℤ)
    (hS : ∀ z ∈ S, z ≠ 0 ∧ 1 - z ≠ 0) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z) ^ m * z ^ n) S := fun z hz =>
  (((differentiableAt_const _).sub differentiableAt_id).zpow (Or.inl (hS z hz).2) |>.mul
    (differentiableAt_id.zpow (Or.inl (hS z hz).1))).differentiableWithinAt

/-- **Independence of the contour, crossing in `(0, 1)`.** For `y₂ ≤ y₁`, the incomplete beta
kernel `K_ξ(v₁; v₂)` is `(2πi)⁻¹` times the contour integral of
`(1 - z)^(y₁ - y₂) z^(x₂ - x₁ - 1)` along any piecewise-`C¹` curve from `conj ξ` to `ξ` that meets
the real axis only in `(0, 1)`. -/
theorem incompleteBetaKernel_eq_intervalIntegral_of_le {ξ : ℂ} {v₁ v₂ : ℤ × ℤ}
    (hv : v₂.2 ≤ v₁.2) {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (ha : γ a = conj ξ)
    (hb : γ b = ξ) (hreal : ∀ t ∈ uIcc a b, (γ t).im = 0 → (γ t).re ∈ Ioo 0 1) :
    incompleteBetaKernel ξ v₁ v₂ = (2 * π * I)⁻¹ *
      ∫ t in a..b, deriv γ t • ((1 - γ t) ^ (v₁.2 - v₂.2) * γ t ^ (v₂.1 - v₁.1 - 1)) := by
  have hγU : MapsTo γ (uIcc a b) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Ioo 0 1} := fun t ht =>
    or_iff_not_imp_left.2 fun h => hreal t ht (not_not.1 h)
  have hstar : StarConvex ℝ (1 / 2 : ℂ) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Ioo 0 1} := by
    have h := starConvex_setOf_im_ne_zero_or_re_mem (c := 1 / 2) (convex_Ioo (0 : ℝ) 1)
      (by norm_num)
    simpa using h
  rw [incompleteBetaKernel_def, ite_eq_left hv, ← ha, ← hb,
    Contour.curveIntegral_segment_add_segment_eq_intervalIntegral_deriv_smul
      (isOpen_setOf_im_ne_zero_or_re_mem isOpen_Ioo) hstar
      (differentiableOn_one_sub_zpow_mul_zpow _ _ fun _ hz =>
        ne_zero_and_one_sub_ne_zero (by simp) (by simp) hz) hγ hγU]

/-- **Independence of the contour, crossing in `(-∞, 0)`.** For `y₁ < y₂`, the incomplete beta
kernel `K_ξ(v₁; v₂)` is `(2πi)⁻¹` times the contour integral of
`(1 - z)^(y₁ - y₂) z^(x₂ - x₁ - 1)` along any piecewise-`C¹` curve from `conj ξ` to `ξ` that meets
the real axis only in `(-∞, 0)`. -/
theorem incompleteBetaKernel_eq_intervalIntegral_of_lt {ξ : ℂ} {v₁ v₂ : ℤ × ℤ}
    (hv : v₁.2 < v₂.2) {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (ha : γ a = conj ξ)
    (hb : γ b = ξ) (hreal : ∀ t ∈ uIcc a b, (γ t).im = 0 → (γ t).re < 0) :
    incompleteBetaKernel ξ v₁ v₂ = (2 * π * I)⁻¹ *
      ∫ t in a..b, deriv γ t • ((1 - γ t) ^ (v₁.2 - v₂.2) * γ t ^ (v₂.1 - v₁.1 - 1)) := by
  have hγU : MapsTo γ (uIcc a b) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Iio 0} := fun t ht =>
    or_iff_not_imp_left.2 fun h => hreal t ht (not_not.1 h)
  have hstar : StarConvex ℝ (-1 : ℂ) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Iio 0} := by
    have h := starConvex_setOf_im_ne_zero_or_re_mem (c := -1) (convex_Iio (0 : ℝ))
      (by norm_num)
    simpa using h
  rw [incompleteBetaKernel_def, ite_eq_right (not_le.2 hv), ← ha, ← hb,
    Contour.curveIntegral_segment_add_segment_eq_intervalIntegral_deriv_smul
      (isOpen_setOf_im_ne_zero_or_re_mem isOpen_Iio) hstar
      (differentiableOn_one_sub_zpow_mul_zpow _ _ fun _ hz =>
        ne_zero_and_one_sub_ne_zero (by simp) (by simp) hz) hγ hγU]

end TauCeti
