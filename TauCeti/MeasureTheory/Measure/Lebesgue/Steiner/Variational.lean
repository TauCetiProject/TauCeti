/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Transverse variational formula for Steiner perimeter

Let `E` be a finite-dimensional real inner product space, `e` a unit vector, and `s` a
null-measurable set of finite volume with Steiner symmetral `S_e s = steinerSymmetrization e he s`.
Write `L(y) = |{t | y + t • e ∈ s}|` for the section lengths on the orthogonal hyperplane
`(ℝ ∙ e)ᗮ` and `D = {y | 0 < |{t | y + t • e ∈ s}|}` for the positive-section set.

**Exact transverse variational formula for Steiner perimeter.** The perimeter `P(S_e s)` in `ℝ≥0∞`
equals the `ℝ≥0∞`-supremum of `2 ∫_D √(1 - ‖φ‖²) + ENNReal.ofReal (∫ div φ (y) L(y) dy)` over
transverse test vector fields `φ ∈ 𝓓(⊤, (ℝ ∙ e)ᗮ)` satisfying `‖φ‖ ≤ 1`
(`TauCeti.perimeter_steinerSymmetrization_eq_iSup`), with no finiteness assumption on `P(s)` or
`P(S_e s)`.

## Proof strategy

The lower bound `≥` in `TauCeti.perimeter_steinerSymmetrization_eq_iSup` is immediate from joint
slicing applied to `S_e s`. For the upper bound `≤`, if `|D| = ∞` then `φ = 0` already makes the
supremum `∞`. When `|D| < ∞`, we test `S_e s` against an arbitrary `ψ₀ ∈ 𝓓(⊤, E)` with
`‖ψ₀‖ ≤ 1`, write `ψ_⊥(y, t) = ((orthogonalLineEquiv e he).symm (ψ₀ (y + t • e))).1` for its
transverse projection, and regularize `L` by shrinking normalized bumps `L_k = ρ_k ⋆ L`. On the
smooth symmetric slab `{|t| < L_k(y) / 2}`, decomposing `div ψ₀` into horizontal divergence and
vertical derivative and integrating `(L_k / 2) ψ_⊥(y, L_k u / 2)` over `u ∈ (-1, 1)` rewrites
`∫_{|t| < L_k/2} div ψ₀` as `2 ∫ d_k - ∫ DL_k (b_k)`, where the boundary horizontal average `b_k`
and vertical half-difference `d_k` satisfy `‖b_k‖² + d_k² ≤ 1` everywhere. Moving `ρ_k` onto `b_k`
produces `φ_k = ρ_k ⋆ b_k ∈ 𝓓(⊤, (ℝ ∙ e)ᗮ)` with `‖φ_k‖² + (ρ_k ⋆ d_k)² ≤ 1`, while the off-`D`
contribution of `ρ_k ⋆ d_k` and the slab-replacement error vanish in `L¹` as `k → ∞`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), 1535–1593, §1.2 and Theorem 1.1.
* M. Chlebík, A. Cianchi, N. Fusco, *The perimeter inequality under Steiner symmetrization: cases
  of equality*, Ann. of Math. (2) **162** (2005), 525–555.
-/

public noncomputable section

open ContinuousLinearMap Filter MeasureTheory Metric Set TopologicalSpace TestFunction
open scoped Convolution ContDiff Distributions ENNReal RealInnerProductSpace Topology

namespace TauCeti

/-! ### Smooth symmetric slabs and mollified transverse test fields -/

section SmoothSymmetricSlab

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem isCompact_fst_image_tsupport (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E)) :
    IsCompact (Prod.fst '' ((orthogonalLineEquiv e he).symm '' tsupport ψ₀)) ∧
      ∀ {y : (ℝ ∙ e)ᗮ}, y ∉ Prod.fst '' ((orthogonalLineEquiv e he).symm '' tsupport ψ₀) →
        ∀ t : ℝ, ψ₀ ((y : E) + t • e) = 0 :=
  ⟨(ψ₀.hasCompactSupport.isCompact.image (orthogonalLineEquiv e he).symm.continuous).image
      continuous_fst,
    fun hy t => image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, ⟨_, h, rfl⟩, by
      rw [← orthogonalLineEquiv_apply e he _ t, ContinuousLinearEquiv.symm_apply_apply]⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The horizontal boundary-average test vector field in `𝓓(⊤, (ℝ ∙ e)ᗮ)` associated to `ψ₀` and a
smooth slab thickness `ℓ`. -/
private def slabHorizAvg (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓((⊤ : Opens E), E))
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
    obtain ⟨hK, h0⟩ := isCompact_fst_image_tsupport e he ψ₀
    refine .of_support_subset_isCompact hK fun y hy => ?_
    by_contra hyK
    exact hy (by simp only [h0 hyK (ℓ y / 2), h0 hyK (-(ℓ y / 2)), map_zero, add_zero, smul_zero])
  tsupport_subset' := subset_univ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
private theorem slabHorizAvg_apply (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓((⊤ : Opens E), E))
    {ℓ : (ℝ ∙ e)ᗮ → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (y : (ℝ ∙ e)ᗮ) :
    slabHorizAvg e he ψ₀ hℓ y = (2 : ℝ)⁻¹ •
      ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((y : E) + (ℓ y / 2) • e)) +
        (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ₀ ((y : E) + (-(ℓ y / 2)) • e))) := (rfl)

/-- Integrating the horizontal divergence of `ψ₀` over the smooth symmetric slab `{|t| < ℓ y / 2}`
gives `-∫ y, Dℓ(y) (slabHorizAvg e he ψ₀ hℓ y)` and proves `y`-integrability. -/
private theorem integrable_and_integral_horizontal_divergence_symmSlab_eq (e : E) (he : ‖e‖ = 1)
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
  obtain ⟨hK, hψ0⟩ := isCompact_fst_image_tsupport e he ψ₀
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

/-- Continuity and integrability of the longitudinal boundary half-difference `d` on a smooth
symmetric slab. -/
private theorem continuous_and_integrable_slabVerticalDiff (e : E) (he : ‖e‖ = 1)
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
  obtain ⟨hK, h0⟩ := isCompact_fst_image_tsupport e he ψ₀
  refine ⟨hdc, hdc.integrable_of_hasCompactSupport (.of_support_subset_isCompact hK fun y hy => ?_)⟩
  by_contra hyK
  exact hy (by simp only [h0 hyK (ℓ y / 2), h0 hyK (-(ℓ y / 2)), inner_zero_right, sub_self,
    mul_zero])

/-- Integrating `divergenceCLM ψ₀` over the smooth symmetric slab `{|t| < ℓ y / 2}` splits into
twice the integral of the longitudinal boundary half-difference minus the pairing of `Dℓ` with the
transverse boundary average. -/
private theorem integrable_and_integral_divergenceCLM_symmSlab_eq (e : E) (he : ‖e‖ = 1)
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
      ext t; linarith [TauCeti.divergenceCLM_orthogonalLine_eq e he ψ₀ y t]
    simp_rw [TauCeti.divergenceCLM_orthogonalLine_eq e he ψ₀ y]
    rw [intervalIntegral.integral_add hi_h hi_v,
      intervalIntegral.integral_deriv_eq_sub (fun s _ => hg.differentiable (by simp) s) hi_v]
    simp only [d]; ring
  refine ⟨(hi1.add (hdi.const_mul 2)).congr (.of_forall fun y => (hline y).symm), ?_⟩
  simp_rw [hline]
  rw [integral_add hi1 (hdi.const_mul 2), heq1, integral_const_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise Pythagorean bound for the horizontal average and vertical half-difference of `ψ₀` on
the boundary of the symmetric slab. -/
private theorem norm_sq_slabBoundaryAvg_le_one (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E))
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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise bound `|d_k y| ≤ min 1 (Mψ * L y) + Mψ * |ℓ y - L y|` for the vertical boundary
half-difference of `ψ₀`, killing the contribution off `{0 < L}` in `L¹`. -/
private theorem abs_slabVerticalDiff_le (e : E) (he : ‖e‖ = 1) (ψ₀ : 𝓓(⊤, E))
    (hψ1 : ∀ x, ‖ψ₀ x‖ ≤ 1) {Mψ : ℝ} (hM0 : 0 ≤ Mψ)
    (hMψ : ∀ x, ‖fderiv ℝ (fun z : E => ⟪e, ψ₀ z⟫) x‖ ≤ Mψ)
    {ℓ L : (ℝ ∙ e)ᗮ → ℝ} (hℓ0 : ∀ y, 0 ≤ ℓ y) (y : (ℝ ∙ e)ᗮ) :
    |(2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (ℓ y / 2) • e)⟫ -
        ⟪e, ψ₀ ((y : E) + (-(ℓ y / 2)) • e)⟫)| ≤
      min 1 (Mψ * L y) + Mψ * |ℓ y - L y| := by
  set f : E → ℝ := fun z => ⟪e, ψ₀ z⟫
  have hf : Differentiable ℝ f := ((innerSL ℝ e).contDiff.comp ψ₀.contDiff).differentiable (by simp)
  have hlip := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hf x)
    (fun x _ => hMψ x) convex_univ (mem_univ ((y : E) + (-(ℓ y / 2)) • e))
    (mem_univ ((y : E) + (ℓ y / 2) • e))
  have hdiff : ((y : E) + (ℓ y / 2) • e) - ((y : E) + (-(ℓ y / 2)) • e) = ℓ y • e := by
    simp only [neg_smul]; module
  rw [hdiff, norm_smul, Real.norm_of_nonneg (hℓ0 y), he, mul_one, Real.norm_eq_abs] at hlip
  have h1 : |(2 : ℝ)⁻¹ * (f ((y : E) + (ℓ y / 2) • e) - f ((y : E) + (-(ℓ y / 2)) • e))| ≤ 1 := by
    have ha (x : E) : |f x| ≤ 1 :=
      (abs_real_inner_le_norm e (ψ₀ x)).trans (by rw [he, one_mul]; exact hψ1 x)
    rw [abs_mul, abs_of_pos (by positivity)]
    linarith [abs_sub (f ((y : E) + (ℓ y / 2) • e)) (f ((y : E) + (-(ℓ y / 2)) • e)),
      ha ((y : E) + (ℓ y / 2) • e), ha ((y : E) + (-(ℓ y / 2)) • e)]
  have h2 : |(2 : ℝ)⁻¹ * (f ((y : E) + (ℓ y / 2) • e) - f ((y : E) + (-(ℓ y / 2)) • e))| ≤
      Mψ * ℓ y := by
    rw [abs_mul, abs_of_pos (by positivity)]
    linarith [mul_nonneg hM0 (hℓ0 y)]
  refine (le_min h1 h2).trans ?_
  rcases le_total 1 (Mψ * L y) with hb | hb
  · rw [min_eq_left hb]
    exact (min_le_left 1 _).trans (le_add_of_nonneg_right (mul_nonneg hM0 (abs_nonneg _)))
  · rw [min_eq_right hb]
    calc min 1 (Mψ * ℓ y) ≤ Mψ * ℓ y := min_le_right _ _
      _ = Mψ * L y + Mψ * (ℓ y - L y) := by ring
      _ ≤ Mψ * L y + Mψ * |ℓ y - L y| :=
          add_le_add_right (mul_le_mul_of_nonneg_left (le_abs_self _) hM0) _

/-- Single-bump slab bound when `volume D ≠ ⊤`: integrating `div ψ₀` over `{|t| < L_ρ / 2}` is
bounded by the variational functional at `φ = mollify B` plus `L¹` mollification errors. -/
private theorem symmSlab_integral_le_variational_add_err (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    (hDfin : volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} ≠ ⊤)
    (ψ₀ : 𝓓(⊤, E)) (hψ1 : ∀ x, ‖ψ₀ x‖ ≤ 1)
    {Mψ : ℝ} (hM0 : 0 ≤ Mψ) (hMψ : ∀ x, ‖fderiv ℝ (fun z : E => ⟪e, ψ₀ z⟫) x‖ ≤ Mψ)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) :
    ∃ (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)), (∀ y, ‖φ y‖ ≤ 1) ∧
      IntegrableOn (fun z : (ℝ ∙ e)ᗮ => √(1 - ‖φ z‖ ^ 2))
        {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} volume ∧
      (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-(
          (ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) y / 2))..(
          (ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) y / 2),
          divergenceCLM ψ₀ ((y : E) + t • e)) ≤
        2 * (∫ z in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
            √(1 - ‖φ z‖ ^ 2)) +
          (∫ z : (ℝ ∙ e)ᗮ, divergenceCLM φ z * volume.real {t : ℝ | (z : E) + t • e ∈ s}) +
          2 * ((∫ z : (ℝ ∙ e)ᗮ, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y : (ℝ ∙ e)ᗮ =>
              min 1 (Mψ * volume.real {t : ℝ | (y : E) + t • e ∈ s})) z -
              min 1 (Mψ * volume.real {t : ℝ | (z : E) + t • e ∈ s})‖) +
            Mψ * ∫ y : (ℝ ∙ e)ᗮ, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
              fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) y -
              volume.real {t : ℝ | (y : E) + t • e ∈ s}‖) := by
  set L : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s} with hL_def
  set D : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  have hDm : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hLi : Integrable L volume := integrable_measureReal_lineSection e he hs hfin
  set L_ρ := ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L
  have hLρ_s : ContDiff ℝ ∞ L_ρ :=
    (ρ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left _ ρ.contDiff_normed
      hLi.locallyIntegrable
  have hLρ0 (y : (ℝ ∙ e)ᗮ) : 0 ≤ L_ρ y :=
    le_convolution_lsmul_of_forall_le ρ.support_normed_eq.subset ρ.nonneg_normed ρ.integral_normed
      ((ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left _
        (ρ.continuous_normed (μ := volume)) hLi.locallyIntegrable y) fun _ _ => measureReal_nonneg
  set B := slabHorizAvg e he ψ₀ hLρ_s with hB_def
  set φ := B.mollify volume ρ (subset_univ _) with hφ_def
  set d : (ℝ ∙ e)ᗮ → ℝ := fun y =>
    (2 : ℝ)⁻¹ * (⟪e, ψ₀ ((y : E) + (L_ρ y / 2) • e)⟫ -
      ⟪e, ψ₀ ((y : E) + (-(L_ρ y / 2)) • e)⟫) with hd_def
  obtain ⟨-, hdi⟩ : Continuous d ∧ Integrable d volume :=
    continuous_and_integrable_slabVerticalDiff e he ψ₀ hLρ_s
  have hφ_sq (z : (ℝ ∙ e)ᗮ) : ‖φ z‖ ^ 2 + (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z ^ 2 ≤ 1 := by
    rw [hφ_def, mollify_apply]
    simpa only [Real.norm_eq_abs, sq_abs] using
      ρ.norm_normed_convolution_sq_add_norm_normed_convolution_sq_le
        (μ := volume) (f₁ := B) (f₂ := d) (M := 1)
        (fun y => by
          rw [hB_def, Real.norm_eq_abs, sq_abs]
          exact norm_sq_slabBoundaryAvg_le_one e he ψ₀ hψ1 hLρ_s y) z
  have hφ1 (z : (ℝ ∙ e)ᗮ) : ‖φ z‖ ≤ 1 := by
    nlinarith [norm_nonneg (φ z), hφ_sq z, sq_nonneg ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z)]
  have hwi : IntegrableOn (fun z : (ℝ ∙ e)ᗮ => √(1 - ‖φ z‖ ^ 2)) D volume :=
    (integrableOn_const (C := (1 : ℝ)) hDfin).mono'
      (Real.continuous_sqrt.comp (continuous_const.sub
        (φ.continuous.norm.pow 2))).aestronglyMeasurable.restrict
      (.of_forall fun z => (Real.norm_of_nonneg (Real.sqrt_nonneg _)).trans_le
        (Real.sqrt_le_one.2 (sub_le_self _ (sq_nonneg _))))
  refine ⟨φ, hφ1, hwi, ?_⟩
  have hgi : Integrable (fun y => min 1 (Mψ * L y)) volume :=
    (hLi.const_mul Mψ).const_inf zero_le_one
  have hL_err : Integrable (L_ρ - L) volume :=
    ((ρ.integrable_normed (μ := volume)).integrable_convolution (lsmul ℝ ℝ) hLi).sub hLi
  have hd_le (y : (ℝ ∙ e)ᗮ) : |d y| ≤ min 1 (Mψ * L y) + Mψ * |L_ρ y - L y| :=
    abs_slabVerticalDiff_le e he ψ₀ hψ1 hM0 hMψ (L := L) hLρ0 y
  have hg0 (z : (ℝ ∙ e)ᗮ) (hz : z ∈ Dᶜ) : min 1 (Mψ * L z) = 0 := by
    have hz0 : volume {t : ℝ | (z : E) + t • e ∈ s} = 0 := by simpa [D] using hz
    simp [hL_def, measureReal_def, hz0]
  have hρi : Integrable (ρ.normed volume) volume := ρ.integrable_normed (μ := volume)
  have hγi : Integrable (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) volume :=
    hρi.integrable_convolution (lsmul ℝ ℝ) hdi
  have htot : ∫ y : (ℝ ∙ e)ᗮ, d y = (∫ z in D, (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z) +
      ∫ z in Dᶜ, (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z := by
    have hconv := MeasureTheory.integral_convolution (lsmul ℝ ℝ) hρi hdi
    rw [ρ.integral_normed, lsmul_apply, one_smul] at hconv
    rw [← hconv, ← integral_add_compl₀ hDm hγi]
  have hD_le : ∫ z in D, (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z ≤
      ∫ z in D, √(1 - ‖φ z‖ ^ 2) :=
    setIntegral_mono_on₀ hγi.integrableOn hwi hDm fun z _ =>
      Real.le_sqrt_of_sq_le (by linarith [hφ_sq z])
  have hDc : ∫ z in Dᶜ, (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] d) z ≤
      (∫ z : (ℝ ∙ e)ᗮ, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => min 1 (Mψ * L y)) z -
        min 1 (Mψ * L z)‖) + Mψ * ∫ y : (ℝ ∙ e)ᗮ, ‖L_ρ y - L y‖ := by
    have h := setIntegral_convolution_lsmul_le_integral_norm_sub_add_mul hρi
      (.of_forall ρ.nonneg_normed) hdi hgi (hL_err.norm.const_mul Mψ)
      (.of_forall fun _ => mul_nonneg hM0 (norm_nonneg _))
      ((ae_restrict_mem₀ hDm.compl).mono fun z hz => (hg0 z hz).le)
      (.of_forall fun y => (le_abs_self _).trans (hd_le y))
    simpa only [ρ.integral_normed, one_mul, Pi.sub_apply, integral_const_mul] using h
  have hslab := (integrable_and_integral_divergenceCLM_symmSlab_eq e he ψ₀ hLρ_s).2
  simp_rw [← hd_def, ← hB_def] at hslab
  have hibp := (ρ.integral_divergenceCLM_mollify_smul_eq_neg_integral_fderiv_normed_convolution
    (hLi.locallyIntegrable.locallyIntegrableOn _) B (subset_univ _)).symm
  simp_rw [← hφ_def, smul_eq_mul] at hibp
  linarith

private theorem symmSlab_approx_sub_le (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    (ψ₀ : 𝓓(⊤, E)) {C₀ : ℝ} (hC₀ : ∀ x, ‖divergenceCLM ψ₀ x‖ ≤ C₀)
    (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ)) :
    (∫ x in steinerSymmetrization e he s, divergenceCLM ψ₀ x) -
      (∫ y : (ℝ ∙ e)ᗮ, ∫ t in (-((ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
          fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) y / 2))..
          ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
            fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) y / 2),
        divergenceCLM ψ₀ ((y : E) + t • e)) ≤
      C₀ * ∫ y : (ℝ ∙ e)ᗮ, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume]
        fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) y -
        volume.real {t : ℝ | (y : E) + t • e ∈ s}‖ := by
  set L : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
  have hLi : Integrable L volume := integrable_measureReal_lineSection e he hs hfin
  set L_ρ := ρ.normed volume ⋆[lsmul ℝ ℝ, volume] L
  have hLρ_s : ContDiff ℝ ∞ L_ρ :=
    (ρ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left _
      ρ.contDiff_normed hLi.locallyIntegrable
  have hsec := ae_volume_lineSection_lt_top e he hs hfin
  have hdiv_i : IntegrableOn (divergenceCLM ψ₀) (steinerSymmetrization e he s) volume :=
    ((divergenceCLM ψ₀).continuous.integrable_of_hasCompactSupport
      (divergenceCLM ψ₀).hasCompactSupport).integrableOn
  have hi_L := integrable_intervalIntegral_of_integrableOn_steinerSymmetrization e he hs hsec hdiv_i
  have hI_eq := setIntegral_steinerSymmetrization_eq_integral_intervalIntegral e he hs hsec hdiv_i
  have herr_i : Integrable (fun y : (ℝ ∙ e)ᗮ => C₀ * ‖L_ρ y - L y‖) volume :=
    (((ρ.integrable_normed (μ := volume)).integrable_convolution
      (lsmul ℝ ℝ) hLi).sub hLi).norm.const_mul C₀
  have hfc (y : (ℝ ∙ e)ᗮ) : Continuous (fun t : ℝ => divergenceCLM ψ₀ ((y : E) + t • e)) :=
    (divergenceCLM ψ₀).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hpt (y : (ℝ ∙ e)ᗮ) :
      ‖(∫ t in (-(L y / 2))..(L y / 2), divergenceCLM ψ₀ ((y : E) + t • e)) -
        (∫ t in (-(L_ρ y / 2))..(L_ρ y / 2), divergenceCLM ψ₀ ((y : E) + t • e))‖ ≤
        C₀ * ‖L_ρ y - L y‖ := by
    refine (intervalIntegral.norm_integral_sub_integral_le_of_norm_le_const_ae
      ((hfc y).intervalIntegrable _ _) ((hfc y).intervalIntegrable _ _)
      ((hfc y).intervalIntegrable _ _)
      (.of_forall fun t _ => hC₀ ((y : E) + t • e))
      (.of_forall fun t _ => hC₀ ((y : E) + t • e))).trans_eq ?_
    have h1 : -(L_ρ y / 2) - -(L y / 2) = -(L_ρ y - L y) / 2 := by ring
    have h2 : L_ρ y / 2 - L y / 2 = (L_ρ y - L y) / 2 := by ring
    rw [h1, h2, abs_div, abs_div, abs_neg, abs_two, Real.norm_eq_abs]
    ring
  rw [hI_eq, ← integral_sub hi_L
    (integrable_and_integral_divergenceCLM_symmSlab_eq e he ψ₀ hLρ_s).1, ← integral_const_mul]
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le
    (norm_integral_le_of_norm_le herr_i (.of_forall hpt)))

/-- When `volume D ≠ ⊤`, testing `S_e s` against any `ψ₀ ∈ 𝓓(⊤, E)` with `‖ψ₀‖ ≤ 1` is bounded by
the transverse variational supremum. -/
private theorem ofReal_setIntegral_steinerSymmetrization_le_iSup
    (e : E) (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤)
    (hDfin : volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} ≠ ⊤)
    (ψ₀ : 𝓓(⊤, E)) (hψ1 : ∀ x, ‖ψ₀ x‖ ≤ 1) :
    ENNReal.ofReal (∫ x in steinerSymmetrization e he s, divergenceCLM ψ₀ x) ≤
      ⨆ (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (_ : ∀ y, ‖φ y‖ ≤ 1),
        2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
          ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
        ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s}) := by
  let ρ : ℕ → ContDiffBump (0 : (ℝ ∙ e)ᗮ) := ContDiffBump.shrinking one_pos
  have hρ_lim : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking one_pos
  have hg_cd : ContDiff ℝ ∞ (fun z : E => ⟪e, ψ₀ z⟫) := (innerSL ℝ e).contDiff.comp ψ₀.contDiff
  have hg_cs : HasCompactSupport (fun z : E => ⟪e, ψ₀ z⟫) :=
    ψ₀.hasCompactSupport.comp_left (inner_zero_right e)
  obtain ⟨M₀, hM₀⟩ := (hg_cd.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hg_cs.fderiv ℝ)
  obtain ⟨Cψ, hCψ⟩ := (divergenceCLM ψ₀).continuous.bounded_above_of_compact_support
    (divergenceCLM ψ₀).hasCompactSupport
  set Mψ := max M₀ 0; set C₀ := max Cψ 0
  have hLi := integrable_measureReal_lineSection e he hs hfin
  have hgi : Integrable (fun y : (ℝ ∙ e)ᗮ =>
      min 1 (Mψ * volume.real {t : ℝ | (y : E) + t • e ∈ s})) volume :=
    (hLi.const_mul Mψ).const_inf zero_le_one
  have hL_lim := tendsto_integral_norm_normed_convolution_sub hρ_lim hLi
  have hg_lim := tendsto_integral_norm_normed_convolution_sub hρ_lim hgi
  set I₀ : ℝ := ∫ x in steinerSymmetrization e he s, divergenceCLM ψ₀ x
  have hlim := (tendsto_const_nhds (x := I₀)).sub ((hL_lim.const_mul C₀).add
    ((hg_lim.add (hL_lim.const_mul Mψ)).const_mul 2))
  simp only [mul_zero, add_zero, sub_zero] at hlim
  refine le_of_tendsto (ENNReal.tendsto_ofReal hlim) (.of_forall fun k => ?_)
  obtain ⟨φ, hφ1, hwi, hslab⟩ := symmSlab_integral_le_variational_add_err e he hs hfin hDfin ψ₀
    hψ1 (Mψ := Mψ) (le_max_right M₀ 0) (fun x => (hM₀ x).trans (le_max_left M₀ 0)) (ρ k)
  have herr₀ : I₀ - _ ≤ _ := symmSlab_approx_sub_le e he hs hfin ψ₀
    (C₀ := C₀) (fun x => (hCψ x).trans (le_max_left Cψ 0)) (ρ k)
  have hD_eq : ENNReal.ofReal (2 * ∫ z in
        {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}, √(1 - ‖φ z‖ ^ 2)) =
      2 * ∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
        ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) := by
    rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
      ofReal_integral_eq_lintegral_ofReal hwi (.of_forall fun _ => Real.sqrt_nonneg _)]
  refine le_trans ?_ (le_iSup₂_of_le φ hφ1 le_rfl)
  rw [← hD_eq]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  linarith

/-- **Variational formula for the perimeter of a Steiner symmetral.** For any null-measurable set
`s` of finite volume and any unit vector `e`, writing `L(y) = |{t | y + t • e ∈ s}|` for the
section lengths on `(ℝ ∙ e)ᗮ` and `D = {y | 0 < L(y)}` for the positive-section set, the perimeter
`P(S_e s)` in `ℝ≥0∞` equals the `ℝ≥0∞`-supremum of
`2 ∫_D √(1 - ‖φ‖²) + ENNReal.ofReal (∫ div φ · L)` over transverse test vector fields
`φ ∈ 𝓓(⊤, (ℝ ∙ e)ᗮ)` satisfying `‖φ‖ ≤ 1`, with no finiteness assumption on `P(s)` or `P(S_e s)`. -/
theorem perimeter_steinerSymmetrization_eq_iSup (e : E) (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ⊤) :
    perimeter volume ⊤ (steinerSymmetrization e he s) =
      ⨆ (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (_ : ∀ y, ‖φ y‖ ≤ 1),
        2 * (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
          ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)) +
        ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y *
          volume.real {t : ℝ | (y : E) + t • e ∈ s}) := by
  refine le_antisymm ?_ (iSup₂_le fun φ hφ => ?_)
  · set D : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
    rcases eq_or_ne (volume D) ⊤ with hDtop | hDfin
    · refine le_top.trans
        (le_iSup₂_of_le (0 : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ)) (by simp) ?_)
      have h0 : 2 * (∫⁻ y in D,
          ENNReal.ofReal √(1 - ‖(0 : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ)) y‖ ^ 2)) = ⊤ := by
        have h1 : (fun y : (ℝ ∙ e)ᗮ =>
            ENNReal.ofReal √(1 - ‖(0 : 𝓓((⊤ : Opens (ℝ ∙ e)ᗮ), (ℝ ∙ e)ᗮ)) y‖ ^ 2)) =
            fun _ => 1 := by
          ext y; simp only [FunLike.coe_zero, Pi.zero_apply, norm_zero]; norm_num
        rw [h1, setLIntegral_one, hDtop, ENNReal.mul_top (by norm_num)]
      rw [h0, top_add]
    · rw [perimeter_eq_iSup (nullMeasurableSet_steinerSymmetrization e he hs)]
      exact iSup₂_le fun ψ₀ hψ1 =>
        ofReal_setIntegral_steinerSymmetrization_le_iSup e he hs hfin hDfin ψ₀ hψ1
  · have hfinS : volume (steinerSymmetrization e he s) ≠ ⊤ := by
      rwa [volume_steinerSymmetrization e he hs]
    have hle := two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
      (nullMeasurableSet_steinerSymmetrization e he hs) hfinS e he .empty
      (.of_forall fun _ h => False.elim h) φ hφ
    simp only [measureReal_def, volume_lineSection_steinerSymmetrization] at hle ⊢
    exact (add_le_add le_self_add le_rfl).trans hle

end SmoothSymmetricSlab

end TauCeti
