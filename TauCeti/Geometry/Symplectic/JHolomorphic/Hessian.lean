/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.InteriorEstimate
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Interior Hessian estimates for the Cauchy–Riemann equation

Differentiating `∂s u + A ∂t u = 0` gives an inhomogeneous equation for each directional
derivative of `u`. The first derivative of `A` supplies its entire right hand side; no second
derivative of `u` occurs there. Applying the cutoff estimate to this equation controls the
directional Hessian in `L²` by first derivatives. The estimate applies when `A` is uniformly
close to a constant compatible complex structure on the cutoff support.

For `A = J ∘ u`, the error is quadratic in `du`. The final theorem makes this substitution
explicit, so bounded first derivatives and bounded `dJ` give local `L²` control of second
derivatives. Choosing the direction to be either coordinate vector controls every Hessian
component. These are estimates for classical solutions, not a weak regularity theorem.

The argument is the differentiation and coefficient freezing step of D. McDuff and D. Salamon,
*J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B. The cutoff estimate is
`TauCeti.integral_cutoff_sq_mul_norm_partialDeriv_sq_le`.
-/

public section

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

section Differentiation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {u : ℝ × ℝ → V} {A : ℝ × ℝ → V →L[ℝ] V} {z : ℝ × ℝ}

/-- A directional derivative of a solution satisfies the differentiated Cauchy–Riemann
equation. The coefficient derivative is the only inhomogeneous term. -/
theorem cauchyRiemann_fderiv_apply_eq_neg
    (hu : ContDiffAt ℝ 2 u z) (hA : DifferentiableAt ℝ A z)
    (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y stdComplexLineReal +
      A y (fderiv ℝ u y stdComplexLineImag) = 0) (e : ℝ × ℝ) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y e) z stdComplexLineReal +
      A z (fderiv ℝ (fun y ↦ fderiv ℝ u y e) z stdComplexLineImag) =
        -(fderiv ℝ A z e (fderiv ℝ u z stdComplexLineImag)) := by
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := congrArg (fun L : (ℝ × ℝ) →L[ℝ] V ↦ L e)
    (EventuallyEq.fderiv_eq (𝕜 := ℝ)
      (f₁ := fun y ↦ fderiv ℝ u y stdComplexLineReal +
        A y (fderiv ℝ u y stdComplexLineImag)) (f := fun _ ↦ (0 : V)) hCR)
  rw [fderiv_fun_add (hDu.clm_apply (differentiableAt_const _))
    (hA.clm_apply (hDu.clm_apply (differentiableAt_const _))),
    fderiv_clm_apply hA (hDu.clm_apply (differentiableAt_const _))] at h
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    fderiv_clm_apply_const_apply hDu] at h ⊢
  have hs := hu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField])
  rw [hs stdComplexLineReal e, hs stdComplexLineImag e]
  exact eq_neg_of_add_eq_zero_left (by simpa [add_assoc, add_comm, add_left_comm] using h)

end Differentiation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : ℝ × ℝ → V} {A : ℝ × ℝ → V →L[ℝ] V}
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {χ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}

/-- An interior `L²` estimate for the directional Hessian of a classical solution with varying
coefficients. It requires only first derivatives of the coefficients, and only on the open
set containing the cutoff support. No almost complex identity for `A` is required. -/
theorem integral_cutoff_sq_mul_norm_hessian_apply_sq_le
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U)
    (hu : ContDiff ℝ 3 u) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ U)
    (hCR : ∀ z ∈ U, fderiv ℝ u z stdComplexLineReal +
      A z (fderiv ℝ u z stdComplexLineImag) = 0)
    (hclose : ∀ z ∈ tsupport χ, ∀ v, ‖A z v - J₀ v‖ ≤ (1 / 2 : ℝ) * ‖v‖)
    (e : ℝ × ℝ) :
    (∫ z, χ z ^ 2 *
      (‖fderiv ℝ (fun y ↦ fderiv ℝ u y e) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (fun y ↦ fderiv ℝ u y e) z stdComplexLineImag‖ ^ 2)) ≤
      16 * (∫ z, χ z ^ 2 * ‖fderiv ℝ A z e (fderiv ℝ u z stdComplexLineImag)‖ ^ 2) +
      130 * ∫ z, (fderiv ℝ χ z stdComplexLineReal ^ 2 +
        fderiv ℝ χ z stdComplexLineImag ^ 2) * ‖fderiv ℝ u z e‖ ^ 2 := by
  have hξ : ContDiff ℝ 2 (fun z ↦ fderiv ℝ u z e) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hestimate := integral_cutoff_sq_mul_norm_partialDeriv_sq_le hg
    (hA.continuousOn.mono hsupp) hξ hχ hc hclose
  have heq : (fun z ↦ χ z ^ 2 *
      ‖fderiv ℝ (fun y ↦ fderiv ℝ u y e) z stdComplexLineReal +
        A z (fderiv ℝ (fun y ↦ fderiv ℝ u y e) z stdComplexLineImag)‖ ^ 2) =
      fun z ↦ χ z ^ 2 * ‖fderiv ℝ A z e (fderiv ℝ u z stdComplexLineImag)‖ ^ 2 := by
    funext z
    by_cases hz : z ∈ tsupport χ
    · rw [cauchyRiemann_fderiv_apply_eq_neg (hu.of_le (by norm_num)).contDiffAt
        ((hA.differentiableOn (by norm_num) z (hsupp hz)).differentiableAt
          (hU.mem_nhds (hsupp hz)))
        (Filter.mem_of_superset (hU.mem_nhds (hsupp hz)) (fun y hy ↦ hCR y hy)) e,
        norm_neg]
    · simp only [image_eq_zero_of_notMem_tsupport hz, zero_pow (by norm_num : 2 ≠ 0),
        zero_mul]
  simpa only [heq] using hestimate

/-- For a target-dependent structure, the Hessian error contains only `dJ` and first
derivatives of the curve. The hypotheses are local to an open set containing the cutoff
support, except for the classical smoothness needed by the cutoff estimate. -/
theorem integral_cutoff_sq_mul_norm_hessian_apply_sq_le_of_target
    {J : V → V →L[ℝ] V} {W : Set V}
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (hU : IsOpen U) (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hu : ContDiff ℝ 3 u) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ U) (hmaps : MapsTo u U W)
    (hCR : ∀ z ∈ U, fderiv ℝ u z stdComplexLineReal +
      J (u z) (fderiv ℝ u z stdComplexLineImag) = 0)
    (hclose : ∀ z ∈ tsupport χ, ∀ v, ‖J (u z) v - J₀ v‖ ≤ (1 / 2 : ℝ) * ‖v‖)
    (e : ℝ × ℝ) :
    (∫ z, χ z ^ 2 *
      (‖fderiv ℝ (fun y ↦ fderiv ℝ u y e) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (fun y ↦ fderiv ℝ u y e) z stdComplexLineImag‖ ^ 2)) ≤
      16 * (∫ z, χ z ^ 2 *
        ‖fderiv ℝ J (u z) (fderiv ℝ u z e) (fderiv ℝ u z stdComplexLineImag)‖ ^ 2) +
      130 * ∫ z, (fderiv ℝ χ z stdComplexLineReal ^ 2 +
        fderiv ℝ χ z stdComplexLineImag ^ 2) * ‖fderiv ℝ u z e‖ ^ 2 := by
  have hA : ContDiffOn ℝ 1 (fun z ↦ J (u z)) U :=
    hJ.comp (hu.of_le (by norm_num)).contDiffOn hmaps
  have hestimate := integral_cutoff_sq_mul_norm_hessian_apply_sq_le hg hU hA
    hu hχ hc hsupp hCR hclose e
  have heq : (fun z ↦ χ z ^ 2 *
      ‖fderiv ℝ (fun y ↦ J (u y)) z e (fderiv ℝ u z stdComplexLineImag)‖ ^ 2) =
      fun z ↦ χ z ^ 2 *
        ‖fderiv ℝ J (u z) (fderiv ℝ u z e) (fderiv ℝ u z stdComplexLineImag)‖ ^ 2 := by
    funext z
    by_cases hz : z ∈ tsupport χ
    · rw [fderiv_fun_comp z
        ((hJ.differentiableOn (by norm_num) (u z) (hmaps (hsupp hz))).differentiableAt
          (hW.mem_nhds (hmaps (hsupp hz)))) (hu.differentiable (by norm_num) z),
        ContinuousLinearMap.comp_apply]
    · simp only [image_eq_zero_of_notMem_tsupport hz, zero_pow (by norm_num : 2 ≠ 0),
        zero_mul]
  simpa only [heq] using hestimate

end TauCeti
