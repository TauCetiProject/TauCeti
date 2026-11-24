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
`y₁ ≥ y₂` (`incompleteBetaKernel_eq_inv_mul_intervalIntegral_of_le`) and in `(-∞, 0)` when
`y₁ < y₂` (`incompleteBetaKernel_eq_inv_mul_intervalIntegral_of_lt`), gives the same value. Such a
curve may cross the real axis any number of times, as long as it does so on that side.

The curves of the first kind lie in `ℂ \ ((-∞, 0] ∪ [1, ∞))`, those of the second kind in
`ℂ \ [0, ∞)`: planes slit along the complement of a real interval, which are open
(`TauCeti.isOpen_setOf_im_ne_zero_or_re_mem`) and star-shaped about every point of the interval
(`Convex.starConvex_setOf_im_ne_zero_or_re_mem`), in particular about `1/2` and about `-1`, the
vertices of the defining polygons. They contain no pole of the integrand. So the integrand has a
primitive there (`TauCeti.Contour.isExactOn_of_starConvex`, from the homology form of Cauchy's
theorem). The contour integral along any piecewise-`C¹` curve in the set and the sum of the curve
integrals along the two segments of the polygon both equal the difference of the values of the
primitive at the common endpoints `conj ξ` and `ξ`, so they agree
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

/-- The integrand `(1 - z)^m z^n` is holomorphic on any set avoiding `0` and `1`. -/
private theorem differentiableOn_one_sub_zpow_mul_zpow {S : Set ℂ} (m n : ℤ)
    (hS : ∀ z ∈ S, z ≠ 0 ∧ 1 - z ≠ 0) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z) ^ m * z ^ n) S := fun z hz =>
  (((differentiableAt_const _).sub differentiableAt_id).zpow (Or.inl (hS z hz).2) |>.mul
    (differentiableAt_id.zpow (Or.inl (hS z hz).1))).differentiableWithinAt

/-- **Path independence for the beta integrand.** Let `S` be an open real set avoiding `0` and
`1`, and let the plane slit along its complement be star-shaped about `c`. Along a
piecewise-`C¹` curve meeting the real axis only in `S`, the contour integral of
`(1 - z)^m z^n` is the sum of its curve integrals along the two segments through `c`. -/
private theorem curveIntegral_segment_add_segment_eq_of_re_mem {S : Set ℝ} (hS : IsOpen S)
    (h₀ : (0 : ℝ) ∉ S) (h₁ : (1 : ℝ) ∉ S) {c : ℂ}
    (hstar : StarConvex ℝ c {z : ℂ | z.im ≠ 0 ∨ z.re ∈ S}) (m n : ℤ) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hreal : ∀ t ∈ uIcc a b, (γ t).im = 0 → (γ t).re ∈ S) :
    (∫ᶜ z in Path.segment (γ a) c, ContinuousLinearMap.toSpanSingleton ℂ ((1 - z) ^ m * z ^ n)) +
        ∫ᶜ z in Path.segment c (γ b),
          ContinuousLinearMap.toSpanSingleton ℂ ((1 - z) ^ m * z ^ n) =
      ∫ t in a..b, deriv γ t • ((1 - γ t) ^ m * γ t ^ n) := by
  have hγU : MapsTo γ (uIcc a b) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ S} := fun t ht =>
    or_iff_not_imp_left.2 fun h => hreal t ht (not_not.1 h)
  have hpoles (z : ℂ) (hz : z ∈ {z : ℂ | z.im ≠ 0 ∨ z.re ∈ S}) : z ≠ 0 ∧ 1 - z ≠ 0 := by
    refine ⟨?_, fun h => ?_⟩
    · rintro rfl
      exact h₀ (ofReal_mem_setOf_im_ne_zero_or_re_mem_iff.1 (by rwa [ofReal_zero]))
    · rw [← sub_eq_zero.1 h] at hz
      exact h₁ (ofReal_mem_setOf_im_ne_zero_or_re_mem_iff.1 (by rwa [ofReal_one]))
  exact Contour.curveIntegral_segment_add_segment_eq_intervalIntegral_deriv_smul
    (isOpen_setOf_im_ne_zero_or_re_mem hS) hstar (differentiableOn_one_sub_zpow_mul_zpow m n hpoles)
    hγ hγU

/-- **Independence of the contour, crossing in `(0, 1)`.** For `y₂ ≤ y₁`, the incomplete beta
kernel `K_ξ(v₁; v₂)` is `(2πi)⁻¹` times the contour integral of
`(1 - z)^(y₁ - y₂) z^(x₂ - x₁ - 1)` along any piecewise-`C¹` curve from `conj ξ` to `ξ` that meets
the real axis only in `(0, 1)`. -/
theorem incompleteBetaKernel_eq_inv_mul_intervalIntegral_of_le {ξ : ℂ} {v₁ v₂ : ℤ × ℤ}
    (hv : v₂.2 ≤ v₁.2) {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (ha : γ a = conj ξ)
    (hb : γ b = ξ) (hreal : ∀ t ∈ uIcc a b, (γ t).im = 0 → (γ t).re ∈ Ioo 0 1) :
    incompleteBetaKernel ξ v₁ v₂ = (2 * π * I)⁻¹ *
      ∫ t in a..b, deriv γ t • ((1 - γ t) ^ (v₁.2 - v₂.2) * γ t ^ (v₂.1 - v₁.1 - 1)) := by
  have hstar : StarConvex ℝ (1 / 2 : ℂ) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Ioo 0 1} := by
    simpa using (convex_Ioo (0 : ℝ) 1).starConvex_setOf_im_ne_zero_or_re_mem (c := 1 / 2)
      (by norm_num)
  rw [incompleteBetaKernel_def, ite_eq_left hv, ← ha, ← hb,
    curveIntegral_segment_add_segment_eq_of_re_mem isOpen_Ioo (by simp) (by simp) hstar _ _ hγ
      hreal]

/-- **Independence of the contour, crossing in `(-∞, 0)`.** For `y₁ < y₂`, the incomplete beta
kernel `K_ξ(v₁; v₂)` is `(2πi)⁻¹` times the contour integral of
`(1 - z)^(y₁ - y₂) z^(x₂ - x₁ - 1)` along any piecewise-`C¹` curve from `conj ξ` to `ξ` that meets
the real axis only in `(-∞, 0)`. -/
theorem incompleteBetaKernel_eq_inv_mul_intervalIntegral_of_lt {ξ : ℂ} {v₁ v₂ : ℤ × ℤ}
    (hv : v₁.2 < v₂.2) {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (ha : γ a = conj ξ)
    (hb : γ b = ξ) (hreal : ∀ t ∈ uIcc a b, (γ t).im = 0 → (γ t).re < 0) :
    incompleteBetaKernel ξ v₁ v₂ = (2 * π * I)⁻¹ *
      ∫ t in a..b, deriv γ t • ((1 - γ t) ^ (v₁.2 - v₂.2) * γ t ^ (v₂.1 - v₁.1 - 1)) := by
  have hstar : StarConvex ℝ (-1 : ℂ) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Iio 0} := by
    simpa using (convex_Iio (0 : ℝ)).starConvex_setOf_im_ne_zero_or_re_mem (c := -1)
      (by norm_num)
  rw [incompleteBetaKernel_def, ite_eq_right (not_le.2 hv), ← ha, ← hb,
    curveIntegral_segment_add_segment_eq_of_re_mem isOpen_Iio (by simp) (by simp) hstar _ _ hγ
      hreal]

end TauCeti
