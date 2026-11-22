/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Distribution.TestFunction.Divergence
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.InnerProductSpace.LinearIsometry

/-!
# Divergence on a smooth symmetric slab

Let `E` be a real inner product space, `e` a unit vector, `ψ₀ ∈ 𝓓(⊤, E)` a test vector field,
and `ℓ : (ℝ ∙ e)ᗮ → ℝ` a smooth thickness profile (`ContDiff ℝ ∞ ℓ`). On the smooth symmetric
slab `{ (y : E) + t • e | |t| < ℓ y / 2 }`, integrating `div ψ₀` decomposes into a longitudinal
boundary difference and a transverse divergence pairing against the horizontal boundary average
`TauCeti.slabHorizAvg e he ψ₀ hℓ ∈ 𝓓(⊤, (ℝ ∙ e)ᗮ)`.

## Main definitions

* `TauCeti.slabHorizAvg`: the horizontal boundary-average test vector field
  `y ↦ (1 / 2) • (P_eᗮ (ψ₀ (y + (ℓ y / 2) • e)) + P_eᗮ (ψ₀ (y - (ℓ y / 2) • e)))` in
  `𝓓(⊤, (ℝ ∙ e)ᗮ)`.

## Main results

* `TauCeti.slabHorizAvg_apply`: pointwise evaluation of `TauCeti.slabHorizAvg`.
* `TauCeti.integrable_and_integral_horizontal_divergence_symmSlab_eq`: integrating the horizontal
  divergence of `ψ₀` over the smooth symmetric slab equals
  `-∫ y, fderiv ℝ ℓ y (slabHorizAvg e he ψ₀ hℓ y)`.
* `TauCeti.continuous_and_integrable_slabVerticalDiff`: continuity and integrability of the
  longitudinal boundary half-difference.
* `TauCeti.integrable_and_integral_divergenceCLM_symmSlab_eq`: the divergence integral over the
  smooth symmetric slab splits into twice the integral of the longitudinal boundary half-difference
  minus `∫ y, fderiv ℝ ℓ y (slabHorizAvg e he ψ₀ hℓ y)`.
* `TauCeti.norm_sq_slabBoundaryAvg_le_one`: when `‖ψ₀‖ ≤ 1`, the horizontal average and vertical
  half-difference satisfy `‖slabHorizAvg e he ψ₀ hℓ y‖ ^ 2 + d y ^ 2 ≤ 1`.
* `TauCeti.abs_slabVerticalDiff_le`: pointwise Lipschitz-cutoff bound for the vertical boundary
  half-difference against any real comparison value.
-/

public section

noncomputable section

open ContinuousLinearMap MeasureTheory Set TestFunction TopologicalSpace
open scoped ContDiff Distributions RealInnerProductSpace

namespace TauCeti

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The horizontal boundary-average test vector field in `𝓓(⊤, (ℝ ∙ e)ᗮ)` associated to `ψ₀` and
a smooth slab thickness `ℓ`. -/
def slabHorizAvg (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓((⊤ : Opens E), E))
    {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ) where
  toFun y := (2 : ℝ)⁻¹ •
    ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((y : E) + (ℓ y / 2) • e)) +
      (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((y : E) + (-(ℓ y / 2)) • e)))
  contDiff' := by
    have h1 : ContDiff ℝ ∞ (fun y : (ℝ ∙ e)ᗮ =>
        (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((y : E) + (ℓ y / 2) • e))) :=
      (ℝ ∙ e)ᗮ.orthogonalProjectionOnto.contDiff.comp (ψ₀.contDiff.comp
        ((ℝ ∙ e)ᗮ.subtypeL.contDiff.add ((hℓ.div_const 2).smul (contDiff_const (c := e)))))
    have h2 : ContDiff ℝ ∞ (fun y : (ℝ ∙ e)ᗮ =>
        (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((y : E) + (-(ℓ y / 2)) • e))) :=
      (ℝ ∙ e)ᗮ.orthogonalProjectionOnto.contDiff.comp (ψ₀.contDiff.comp
        ((ℝ ∙ e)ᗮ.subtypeL.contDiff.add ((hℓ.div_const 2).neg.smul (contDiff_const (c := e)))))
    exact (h1.add h2).const_smul (2 : ℝ)⁻¹
  hasCompactSupport' := by
    obtain ⟨hK, h0⟩ := ψ₀.hasCompactSupport.isCompact_fst_image_tsupport_orthogonalLineEquiv e he
    refine .of_support_subset_isCompact hK fun y hy => ?_
    by_contra hyK
    exact hy (by simp only [h0 hyK (ℓ y / 2), h0 hyK (-(ℓ y / 2)), map_zero, add_zero, smul_zero])
  tsupport_subset' := subset_univ _

/-- Pointwise evaluation of `TauCeti.slabHorizAvg`. -/
@[simp]
theorem slabHorizAvg_apply (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓((⊤ : Opens E), E))
    {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (y : (ℝ ∙ e)ᗮ) :
    slabHorizAvg e he ψ₀ hℓ y = (2 : ℝ)⁻¹ •
      ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((y : E) + (ℓ y / 2) • e)) +
        (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((y : E) + (-(ℓ y / 2)) • e))) := (rfl)

/-- Pointwise Pythagorean bound for the horizontal average `TauCeti.slabHorizAvg` and vertical
half-difference of `ψ₀` with `‖ψ₀‖ ≤ 1` on the boundary of a smooth symmetric slab. -/
theorem norm_sq_slabBoundaryAvg_le_one (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E))
    (hψ1 : ∀ x, ‖ψ₀ x‖ ≤ 1) {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (y : (ℝ ∙ e)ᗮ) :
    ‖slabHorizAvg e he ψ₀ hℓ y‖ ^ 2 +
      ((2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
        ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)) ^ 2 ≤ 1 := by
  rw [slabHorizAvg_apply]
  set x1 := (y : E) + (ℓ y / 2) • e
  set x2 := (y : E) + (-(ℓ y / 2)) • e
  set u1 := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ x1)
  set u2 := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ x2)
  set v1 := ⟪e, ψ₀ x1⟫
  set v2 := ⟪e, ψ₀ x2⟫
  have hdecomp (x : E) :
      ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ x) : E) + ⟪e, ψ₀ x⟫ • e = ψ₀ x := by
    rw [← orthogonalLineEquiv_symm_fst_eq_orthogonalProjectionOnto e he,
      orthogonalLineEquiv_symm_fst, sub_add_cancel]
  have hn1 : ‖(u1 : E) + v1 • e‖ ≤ 1 := by rw [hdecomp]; exact hψ1 x1
  have hn2 : ‖(u2 : E) + (-v2) • e‖ ≤ 1 := by
    have hsq : ‖(u2 : E) + (-v2) • e‖ ^ 2 ≤ 1 := by
      rw [norm_add_smul_sq e he, neg_sq, ← norm_add_smul_sq e he, hdecomp x2]
      exact pow_le_one₀ (norm_nonneg _) (hψ1 x2)
    nlinarith [norm_nonneg ((u2 : E) + (-v2) • e)]
  set z : E := (((2 : ℝ)⁻¹ • (u1 + u2) : (ℝ ∙ e)ᗮ) : E) + ((2 : ℝ)⁻¹ * (v1 - v2)) • e
  have hz_eq : z = (2 : ℝ)⁻¹ • (((u1 : E) + v1 • e) + ((u2 : E) + (-v2) • e)) := by
    simp only [z, Submodule.coe_smul_of_tower, Submodule.coe_add]; module
  have hz1 : ‖z‖ ≤ 1 := by
    rw [hz_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
    linarith [norm_add_le ((u1 : E) + v1 • e) ((u2 : E) + (-v2) • e)]
  rw [← norm_add_smul_sq e he]
  exact pow_le_one₀ (norm_nonneg z) hz1

/-- Pointwise bound `|(2 : ℝ)⁻¹ * (⟪e, ψ₀ (y + (t / 2) • e)⟫ - ⟪e, ψ₀ (y - (t / 2) • e)⟫)| ≤
min 1 (Mψ * L) + Mψ * |t - L|` for the vertical boundary half-difference of a test vector field `ψ₀`
with `‖ψ₀‖ ≤ 1` and `‖D⟪e, ψ₀ ·⟫‖ ≤ Mψ`, for any `t ≥ 0` and real comparison value `L`. -/
theorem abs_slabVerticalDiff_le (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E))
    (hψ1 : ∀ x, ‖ψ₀ x‖ ≤ 1) {Mψ : ℝ}
    (hMψ : ∀ x, ‖fderiv ℝ (fun z : E => ⟪e, ψ₀ z⟫) x‖ ≤ Mψ)
    (y : (ℝ ∙ e)ᗮ) {t : ℝ} (ht : 0 ≤ t) (L : ℝ) :
    |(2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (t / 2) • e)⟫ -
        ⟪e, ψ₀ ((y : E) + (-(t / 2)) • e)⟫)| ≤
      min 1 (Mψ * L) + Mψ * |t - L| := by
  have hM0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ 0)
  set f : E → ℝ := fun z => ⟪e, ψ₀ z⟫
  have hf : Differentiable ℝ f := ((innerSL ℝ e).contDiff.comp ψ₀.contDiff).differentiable (by simp)
  have hlip := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hf x)
    (fun x _ => hMψ x) convex_univ (mem_univ ((y : E) + (-(t / 2)) • e))
    (mem_univ ((y : E) + (t / 2) • e))
  have hdiff : ((y : E) + (t / 2) • e) - ((y : E) + (-(t / 2)) • e) = t • e := by
    simp only [neg_smul]; module
  rw [hdiff, norm_smul, Real.norm_of_nonneg ht, he, mul_one, Real.norm_eq_abs] at hlip
  have h1 : |(2 : ℝ)⁻¹ * (f ((y : E) + (t / 2) • e) - f ((y : E) + (-(t / 2)) • e))| ≤ 1 := by
    have ha (x : E) : |f x| ≤ 1 :=
      (abs_real_inner_le_norm e (ψ₀ x)).trans (by rw [he, one_mul]; exact hψ1 x)
    rw [abs_mul, abs_of_pos (by positivity)]
    linarith [abs_sub (f ((y : E) + (t / 2) • e)) (f ((y : E) + (-(t / 2)) • e)),
      ha ((y : E) + (t / 2) • e), ha ((y : E) + (-(t / 2)) • e)]
  have h2 : |(2 : ℝ)⁻¹ * (f ((y : E) + (t / 2) • e) - f ((y : E) + (-(t / 2)) • e))| ≤
      Mψ * t := by
    rw [abs_mul, abs_of_pos (by positivity)]
    linarith [mul_nonneg hM0 ht]
  refine (le_min h1 h2).trans ?_
  rcases le_total 1 (Mψ * L) with hb | hb
  · rw [min_eq_left hb]
    exact (min_le_left 1 _).trans (le_add_of_nonneg_right (mul_nonneg hM0 (abs_nonneg _)))
  · rw [min_eq_right hb]
    calc min 1 (Mψ * t) ≤ Mψ * t := min_le_right _ _
      _ = Mψ * L + Mψ * (t - L) := by ring
      _ ≤ Mψ * L + Mψ * |t - L| :=
          add_le_add_right (mul_le_mul_of_nonneg_left (le_abs_self _) hM0) _

end

section Integral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Integrating the horizontal divergence of `ψ₀` over the smooth symmetric slab `{|t| < ℓ y / 2}`
gives `-∫ y, Dℓ(y) (slabHorizAvg e he ψ₀ hℓ y)` and proves `y`-integrability. -/
theorem integrable_and_integral_horizontal_divergence_symmSlab_eq (e : E) (he : ‖e‖ = 1)
    (ψ₀ : 𝓓(⊤, E)) {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    Integrable (fun y : (ℝ ∙ e)ᗮ => ∫ t in (-(ℓ y / 2))..(ℓ y / 2),
        LinearMap.trace ℝ (ℝ ∙ e)ᗮ
          (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
            (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((z : E) + t • e))) y :
            (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ)) volume ∧
      (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-(ℓ y / 2))..(ℓ y / 2),
          LinearMap.trace ℝ (ℝ ∙ e)ᗮ
            (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
              (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((z : E) + t • e))) y :
              (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ)) =
        -∫ y : (ℝ ∙ e)ᗮ, fderiv ℝ ℓ y (slabHorizAvg e he ψ₀ hℓ y) := by
  set A : (ℝ ∙ e)ᗮ → ℝ → (ℝ ∙ e)ᗮ :=
    fun y t => (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((y : E) + t • e)) with hA_def
  have hA : ContDiff ℝ ∞ (Function.uncurry A) :=
    (ℝ ∙ e)ᗮ.orthogonalProjectionOnto.contDiff.comp (ψ₀.contDiff.comp
      (((ℝ ∙ e)ᗮ.subtypeL.contDiff.comp contDiff_fst).add (contDiff_snd.smul contDiff_const)))
  let a : (ℝ ∙ e)ᗮ → ℝ := fun y => ℓ y / 2
  have ha : ContDiff ℝ 1 a := (hℓ.div_const 2).of_le (by simp)
  obtain ⟨hK, hψ0⟩ := ψ₀.hasCompactSupport.isCompact_fst_image_tsupport_orthogonalLineEquiv e he
  have hA0 {y : (ℝ ∙ e)ᗮ} (hy : y ∉ Prod.fst '' ((orthogonalLineEquiv e he).symm '' tsupport ψ₀))
      (t : ℝ) : A y t = 0 := by simp [hA_def, hψ0 hy t]
  obtain ⟨hP1c, hP2c⟩ := continuous_trace_fderiv_comp_mul (hA.of_le (by simp)) ha
  have hswap {P : ℝ × (ℝ ∙ e)ᗮ → ℝ} (hP : Continuous P)
      (hvan : ∀ u, ∀ y ∉ Prod.fst '' ((orthogonalLineEquiv e he).symm '' tsupport ψ₀),
        P (u, y) = 0) :
      Integrable (fun y : (ℝ ∙ e)ᗮ => ∫ u in (-1 : ℝ)..1, P (u, y)) volume ∧
        (∫ u in (-1 : ℝ)..1, ∫ y : (ℝ ∙ e)ᗮ, P (u, y)) =
          ∫ y : (ℝ ∙ e)ᗮ, ∫ u in (-1 : ℝ)..1, P (u, y) := by
    have hint : Integrable P ((volume.restrict (uIoc (-1 : ℝ) 1)).prod volume) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact (hP.continuousOn.integrableOn_compact (isCompact_uIcc.prod hK)).of_forall_sdiff_eq_zero
        (measurableSet_uIoc.prod MeasurableSet.univ) fun ⟨u, y⟩ ⟨⟨hu, _⟩, hnot⟩ =>
          hvan u y fun hy => hnot ⟨uIoc_subset_uIcc hu, hy⟩
    refine ⟨?_, intervalIntegral_integral_swap (f := Function.curry P) hint⟩
    simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hint.integral_prod_right
  have h1 := hswap hP1c fun u y hy =>
    (trace_fderiv_comp_mul_eq_zero_of_notMem hK.isClosed hA0 a u hy).1
  have h2 := hswap hP2c fun u y hy =>
    (trace_fderiv_comp_mul_eq_zero_of_notMem hK.isClosed hA0 a u hy).2
  have hp1_eq (y : (ℝ ∙ e)ᗮ) : (∫ u in (-1 : ℝ)..1,
      a y * LinearMap.trace ℝ (ℝ ∙ e)ᗮ
        (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => A z (a y * u)) y : (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ)) =
      ∫ t in (-(ℓ y / 2))..(ℓ y / 2),
        LinearMap.trace ℝ (ℝ ∙ e)ᗮ (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
          (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((z : E) + t • e))) y :
          (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ) := by
    change (∫ u in (-1 : ℝ)..1,
        (ℓ y / 2) * LinearMap.trace ℝ (ℝ ∙ e)ᗮ
          (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => A z ((ℓ y / 2) * u)) y : (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ)) = _
    rw [intervalIntegral.integral_const_mul, ← smul_eq_mul,
      intervalIntegral.smul_integral_comp_mul_left
        (f := fun t => LinearMap.trace ℝ (ℝ ∙ e)ᗮ
          (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => A z t) y : (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ)),
      mul_neg_one, mul_one]
  have hp2_eq (y : (ℝ ∙ e)ᗮ) : (∫ u in (-1 : ℝ)..1,
      deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u) =
      fderiv ℝ ℓ y (slabHorizAvg e he ψ₀ hℓ y) := by
    have hΦ : ContDiff ℝ ∞ (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) :=
      (fderiv ℝ a y).contDiff.comp
        (contDiff_id.smul (hA.comp (contDiff_const.prodMk (contDiff_const.mul contDiff_id))))
    have ha_fderiv : fderiv ℝ a y = (2 : ℝ)⁻¹ • fderiv ℝ ℓ y :=
      (((hℓ.differentiable (by simp) y).hasFDerivAt.const_mul (2 : ℝ)⁻¹).congr_of_eventuallyEq
        (.of_forall fun z => div_eq_inv_mul (ℓ z) 2)).fderiv
    rw [intervalIntegral.integral_deriv_eq_sub (fun s _ => hΦ.differentiable (by simp) s)
      ((hΦ.continuous_deriv (by simp)).intervalIntegrable _ _)]
    simp only [ha_fderiv, slabHorizAvg_apply, hA_def, a, _root_.smul_apply,
      smul_eq_mul, one_smul, mul_one, mul_neg_one, neg_one_smul, map_neg, map_add, map_smul]
    ring
  refine ⟨h1.1.congr (.of_forall hp1_eq), ?_⟩
  simp_rw [← hp1_eq, ← hp2_eq, ← h1.2, ← h2.2,
    integral_mul_trace_fderiv_comp_mul_eq_neg hK (hA.of_le (by simp)) hA0 ha,
    intervalIntegral.integral_neg]

/-- Continuity and integrability of the longitudinal boundary half-difference on a smooth
symmetric slab. -/
theorem continuous_and_integrable_slabVerticalDiff (e : E) (he : ‖e‖ = 1)
    (ψ₀ : 𝓓(⊤, E)) {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    Continuous (fun y : (ℝ ∙ e)ᗮ => (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
        ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)) ∧
      Integrable (fun y : (ℝ ∙ e)ᗮ => (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
        ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)) volume := by
  have hpos : Continuous fun y : (ℝ ∙ e)ᗮ => ⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ :=
    (innerSL ℝ e).continuous.comp (ψ₀.continuous.comp
      ((ℝ ∙ e)ᗮ.subtypeL.continuous.add ((hℓ.continuous.div_const 2).smul continuous_const)))
  have hneg : Continuous fun y : (ℝ ∙ e)ᗮ => ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫ :=
    (innerSL ℝ e).continuous.comp (ψ₀.continuous.comp
      ((ℝ ∙ e)ᗮ.subtypeL.continuous.add
        ((hℓ.continuous.div_const 2).neg.smul continuous_const)))
  have hdc : Continuous fun y : (ℝ ∙ e)ᗮ => (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
      ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫) :=
    continuous_const.mul (hpos.sub hneg)
  obtain ⟨hK, h0⟩ := ψ₀.hasCompactSupport.isCompact_fst_image_tsupport_orthogonalLineEquiv e he
  refine ⟨hdc, hdc.integrable_of_hasCompactSupport (.of_support_subset_isCompact hK fun y hy => ?_)⟩
  by_contra hyK
  exact hy (by simp only [h0 hyK (ℓ y / 2), h0 hyK (-(ℓ y / 2)), inner_zero_right, sub_self,
    mul_zero])

/-- Integrating `divergenceCLM ψ₀` over the smooth symmetric slab `{|t| < ℓ y / 2}` splits into
twice the integral of the longitudinal boundary half-difference minus the pairing of `Dℓ` with the
transverse boundary average `TauCeti.slabHorizAvg`. -/
theorem integrable_and_integral_divergenceCLM_symmSlab_eq (e : E) (he : ‖e‖ = 1)
    (ψ₀ : 𝓓(⊤, E)) {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) :
    Integrable (fun y : (ℝ ∙ e)ᗮ =>
        ∫ t in (-(ℓ y / 2))..(ℓ y / 2), divergenceCLM ψ₀ ((y : E) + t • e)) volume ∧
      (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-(ℓ y / 2))..(ℓ y / 2), divergenceCLM ψ₀ ((y : E) + t • e)) =
        2 * (∫ y : (ℝ ∙ e)ᗮ, (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
          ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)) -
        ∫ y : (ℝ ∙ e)ᗮ, fderiv ℝ ℓ y (slabHorizAvg e he ψ₀ hℓ y) := by
  obtain ⟨hi1, heq1⟩ := integrable_and_integral_horizontal_divergence_symmSlab_eq e he ψ₀ hℓ
  obtain ⟨-, hdi⟩ := continuous_and_integrable_slabVerticalDiff e he ψ₀ hℓ
  let d : (ℝ ∙ e)ᗮ → ℝ := fun y =>
    (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ - ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)
  have hline (y : (ℝ ∙ e)ᗮ) :
      (∫ t in (-(ℓ y / 2))..(ℓ y / 2), divergenceCLM ψ₀ ((y : E) + t • e)) =
        (∫ t in (-(ℓ y / 2))..(ℓ y / 2), LinearMap.trace ℝ (ℝ ∙ e)ᗮ
          (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
            (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((z : E) + t • e))) y :
            (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ)) +
        2 * d y := by
    have hg : ContDiff ℝ ∞ (fun s : ℝ => ⟪e, ψ₀ ((y : E) + s • e)⟫) :=
      (innerSL ℝ e).contDiff.comp (ψ₀.contDiff.comp
        (contDiff_const.add (contDiff_id.smul contDiff_const)))
    have hi_div : IntervalIntegrable (fun t => divergenceCLM ψ₀ ((y : E) + t • e)) volume
        (-(ℓ y / 2)) (ℓ y / 2) :=
      ((divergenceCLM ψ₀).continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _
    have hi_v : IntervalIntegrable (deriv fun s : ℝ => ⟪e, ψ₀ ((y : E) + s • e)⟫) volume
        (-(ℓ y / 2)) (ℓ y / 2) :=
      (hg.continuous_deriv (by simp)).intervalIntegrable _ _
    have hi_h : IntervalIntegrable (fun t => LinearMap.trace ℝ (ℝ ∙ e)ᗮ
        (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
          (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((z : E) + t • e))) y :
          (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ))
        volume (-(ℓ y / 2)) (ℓ y / 2) := by
      convert hi_div.sub hi_v using 1
      ext t; linarith [divergenceCLM_orthogonalLine_eq e he ψ₀ y t]
    simp_rw [divergenceCLM_orthogonalLine_eq e he ψ₀ y]
    rw [intervalIntegral.integral_add hi_h hi_v,
      intervalIntegral.integral_deriv_eq_sub (fun s _ => hg.differentiable (by simp) s) hi_v]
    simp only [d]; ring
  refine ⟨(hi1.add (hdi.const_mul 2)).congr (.of_forall fun y => (hline y).symm), ?_⟩
  simp_rw [hline]
  rw [integral_add hi1 (hdi.const_mul 2), heq1, integral_const_mul]
  ring

end Integral

end TauCeti
