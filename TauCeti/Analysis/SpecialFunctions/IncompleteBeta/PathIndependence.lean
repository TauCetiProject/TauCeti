/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Kernel
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Contour.Curve.Integrability
import TauCeti.Analysis.Contour.Primitive
import TauCeti.MeasureTheory.Integral.CurveIntegral.Segment

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
`ℂ \ [0, ∞)`. Both sets are open, contain no pole of the integrand, and are star-shaped, about
`1/2` and about `-1` respectively, which are the vertices of the defining polygons. So the
integrand has a primitive there (`TauCeti.Contour.isExactOn_of_starConvex`, from the homology form
of Cauchy's theorem), and the contour integral along any curve in the set, like the curve
integrals along the two segments of the polygon, is the difference of its values at the endpoints
(`curveIntegral_segment_add_segment_eq_intervalIntegral_deriv_smul`).

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

/-- **Path independence through a star centre.** If `f` is holomorphic on an open set `U` that is
star-shaped about `c`, then for every piecewise-`C¹` curve `γ` in `U` the contour integral
`∫ t in a..b, γ' t • f (γ t)` equals the sum of the curve integrals of `f(z) dz` along
`Path.segment (γ a) c` and `Path.segment c (γ b)`. -/
theorem curveIntegral_segment_add_segment_eq_intervalIntegral_deriv_smul {U : Set ℂ} {c : ℂ}
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} (hU : IsOpen U) (hstar : StarConvex ℝ c U)
    (hf : DifferentiableOn ℂ f U) (hγ : IsPiecewiseC1On γ a b) (hγU : MapsTo γ (uIcc a b) U) :
    (∫ᶜ z in Path.segment (γ a) c, ContinuousLinearMap.toSpanSingleton ℂ (f z)) +
        ∫ᶜ z in Path.segment c (γ b), ContinuousLinearMap.toSpanSingleton ℂ (f z) =
      ∫ t in a..b, deriv γ t • f (γ t) := by
  obtain ⟨F, hF⟩ := Contour.isExactOn_of_starConvex hU hstar hf
  rw [curveIntegral_segment_add_segment_toSpanSingleton_eq_sub hstar (hγU left_mem_uIcc)
    (hγU right_mem_uIcc) hF hf.continuousOn]
  obtain ⟨P, hP, hPd⟩ := hγ.exists_countable_differentiableAt
  refine (integral_eq_of_hasDerivAt_off_countable (fun t => F (γ t)) _ hP ?_ (fun t ht => ?_)
    (hγ.intervalIntegrable_deriv_smul_comp_of_mapsTo hf.continuousOn hγU)).symm
  · exact fun t ht => (hF _ (hγU ht)).continuousAt.comp_continuousWithinAt (hγ.continuousOn t ht)
  · have htu : t ∈ uIcc a b := by
      rw [← Icc_min_max]
      exact Ioo_subset_Icc_self ht.1
    exact (hF _ (hγU htu)).scomp t (hPd t ht).hasDerivAt

/-- A point off the real axis or in `(0, 1)` is neither `0` nor `1`. -/
private theorem ne_zero_and_one_sub_ne_zero_of_Ioo {z : ℂ} (hz : z.im ≠ 0 ∨ z.re ∈ Ioo 0 1) :
    z ≠ 0 ∧ 1 - z ≠ 0 := by
  rcases hz with hz | ⟨h₀, h₁⟩
  · refine ⟨fun h => hz (by simp [h]), fun h => hz ?_⟩
    simpa using congrArg im h
  · refine ⟨fun h => by simp [h] at h₀, fun h => ?_⟩
    have := congrArg re h
    simp only [sub_re, one_re, zero_re] at this
    linarith

/-- A point off the real axis or in `(-∞, 0)` is neither `0` nor `1`. -/
private theorem ne_zero_and_one_sub_ne_zero_of_neg {z : ℂ} (hz : z.im ≠ 0 ∨ z.re < 0) :
    z ≠ 0 ∧ 1 - z ≠ 0 := by
  rcases hz with hz | hz
  · exact ne_zero_and_one_sub_ne_zero_of_Ioo (Or.inl hz)
  · refine ⟨fun h => by simp [h] at hz, fun h => ?_⟩
    have := congrArg re h
    simp only [sub_re, one_re, zero_re] at this
    linarith

/-- The integrand `(1 - z)^m z^n` is holomorphic on any set avoiding `0` and `1`. -/
private theorem differentiableOn_one_sub_zpow_mul_zpow {S : Set ℂ} (m n : ℤ)
    (hS : ∀ z ∈ S, z ≠ 0 ∧ 1 - z ≠ 0) :
    DifferentiableOn ℂ (fun z : ℂ => (1 - z) ^ m * z ^ n) S := fun z hz =>
  (((differentiableAt_const _).sub differentiableAt_id).zpow (Or.inl (hS z hz).2) |>.mul
    (differentiableAt_id.zpow (Or.inl (hS z hz).1))).differentiableWithinAt

/-- The plane slit along `(-∞, 0]` and `[1, ∞)` is open. -/
private theorem isOpen_setOf_im_ne_zero_or_re_mem_Ioo :
    IsOpen {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Ioo 0 1} :=
  (isOpen_ne_fun continuous_im continuous_const).union (isOpen_Ioo.preimage continuous_re)

/-- The plane slit along `[0, ∞)` is open. -/
private theorem isOpen_setOf_im_ne_zero_or_re_neg : IsOpen {z : ℂ | z.im ≠ 0 ∨ z.re < 0} :=
  (isOpen_ne_fun continuous_im continuous_const).union (isOpen_Iio.preimage continuous_re)

/-- The plane slit along `(-∞, 0]` and `[1, ∞)` is star-shaped about `1/2`. -/
private theorem starConvex_setOf_im_ne_zero_or_re_mem_Ioo :
    StarConvex ℝ (1 / 2 : ℂ) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Ioo 0 1} := by
  intro z hz s t hs ht hst
  simp only [mem_ofPred_eq, add_im, add_re, smul_re, smul_im, smul_eq_mul, mem_Ioo] at hz ⊢
  norm_num
  rcases ht.eq_or_lt with rfl | ht
  · right
    constructor <;> linarith
  · rcases hz with hz | ⟨h₀, h₁⟩
    · exact Or.inl ⟨ht.ne', hz⟩
    · right
      constructor <;> nlinarith

/-- The plane slit along `[0, ∞)` is star-shaped about `-1`. -/
private theorem starConvex_setOf_im_ne_zero_or_re_neg :
    StarConvex ℝ (-1 : ℂ) {z : ℂ | z.im ≠ 0 ∨ z.re < 0} := by
  intro z hz s t hs ht hst
  simp only [mem_ofPred_eq, add_im, add_re, smul_re, smul_im, smul_eq_mul] at hz ⊢
  norm_num
  rcases ht.eq_or_lt with rfl | ht
  · right
    linarith
  · rcases hz with hz | hz
    · exact Or.inl ⟨ht.ne', hz⟩
    · right
      nlinarith

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
  rw [incompleteBetaKernel_def, ite_eq_left hv, ← ha, ← hb,
    curveIntegral_segment_add_segment_eq_intervalIntegral_deriv_smul
      isOpen_setOf_im_ne_zero_or_re_mem_Ioo starConvex_setOf_im_ne_zero_or_re_mem_Ioo
      (differentiableOn_one_sub_zpow_mul_zpow _ _ fun _ hz =>
        ne_zero_and_one_sub_ne_zero_of_Ioo hz) hγ hγU]

/-- **Independence of the contour, crossing in `(-∞, 0)`.** For `y₁ < y₂`, the incomplete beta
kernel `K_ξ(v₁; v₂)` is `(2πi)⁻¹` times the contour integral of
`(1 - z)^(y₁ - y₂) z^(x₂ - x₁ - 1)` along any piecewise-`C¹` curve from `conj ξ` to `ξ` that meets
the real axis only in `(-∞, 0)`. -/
theorem incompleteBetaKernel_eq_intervalIntegral_of_lt {ξ : ℂ} {v₁ v₂ : ℤ × ℤ}
    (hv : v₁.2 < v₂.2) {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (ha : γ a = conj ξ)
    (hb : γ b = ξ) (hreal : ∀ t ∈ uIcc a b, (γ t).im = 0 → (γ t).re < 0) :
    incompleteBetaKernel ξ v₁ v₂ = (2 * π * I)⁻¹ *
      ∫ t in a..b, deriv γ t • ((1 - γ t) ^ (v₁.2 - v₂.2) * γ t ^ (v₂.1 - v₁.1 - 1)) := by
  have hγU : MapsTo γ (uIcc a b) {z : ℂ | z.im ≠ 0 ∨ z.re < 0} := fun t ht =>
    or_iff_not_imp_left.2 fun h => hreal t ht (not_not.1 h)
  rw [incompleteBetaKernel_def, ite_eq_right (not_le.2 hv), ← ha, ← hb,
    curveIntegral_segment_add_segment_eq_intervalIntegral_deriv_smul
      isOpen_setOf_im_ne_zero_or_re_neg starConvex_setOf_im_ne_zero_or_re_neg
      (differentiableOn_one_sub_zpow_mul_zpow _ _ fun _ hz =>
        ne_zero_and_one_sub_ne_zero_of_neg hz) hγ hγU]

end TauCeti
