/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Rademacher
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.LineDeriv.Measurable

/-!
# Locally Lipschitz functions are weakly differentiable

Let `u : E → F` be locally Lipschitz on an open subset `Ω` of a finite-dimensional real normed
space `E`, and let `μ` be an additive Haar measure. If `u` has line derivative `u' x` in the
direction `v` at almost every `x ∈ Ω`, then `u'` is the weak derivative of `u` in the direction
`v` on `Ω` (`LocallyLipschitzOn.hasWeakLineDerivOn`). In the same way an almost-everywhere
Fréchet derivative is the weak one (`LocallyLipschitzOn.hasWeakFDerivOn`), and when `F` is
finite-dimensional, Rademacher's theorem supplies it: `fderiv ℝ u` is the weak derivative of `u`
on `Ω` (`LocallyLipschitzOn.hasWeakFDerivOn_fderiv`). Near each point this weak derivative is
bounded by a local Lipschitz constant (`norm_fderiv_le_of_lipschitzOn`).

No regularity of `u` beyond the local Lipschitz bound is used, and the codomain `F` is an
arbitrary Banach space: the derivative is only assumed to exist almost everywhere. This is what a
change of variables by a Lipschitz map, such as the flattening of the region above a Lipschitz
graph, needs: composed with such a map, a smooth function is only locally Lipschitz.

## The argument

For real `u` and a test function `φ`, `u` is Lipschitz on a compact neighbourhood of the support
of `φ` inside `Ω`, so it agrees there with a globally Lipschitz function
(`LipschitzOnWith.extend_real`). Mathlib's integration by parts for Lipschitz functions
(`LipschitzWith.integral_lineDeriv_mul_eq`) applies to that extension, and near the support of `φ`
its line derivative is `u'` almost everywhere. Measurability and local integrability of `u'`
come from `LocallyLipschitzOn.locallyIntegrableOn_of_ae_hasLineDerivAt`. A vector-valued `u` is
reduced to the real case by testing the identity against continuous linear functionals.

## Main declarations

* `LocallyLipschitzOn.hasWeakLineDerivOn`: an almost-everywhere line derivative of a locally
  Lipschitz function is its weak derivative.
* `LocallyLipschitzOn.hasWeakFDerivOn`: the same for an almost-everywhere Fréchet derivative.
* `LocallyLipschitzOn.hasWeakFDerivOn_fderiv`: for a finite-dimensional codomain, `fderiv ℝ u` is
  the weak derivative.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.2.3, Theorem 4.5 and §3.1.2 (Rademacher's theorem).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2, Theorem 4.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {v : E} {u u' : E → F}

/-- The real case of `LocallyLipschitzOn.hasWeakLineDerivOn`, as an integration-by-parts identity:
`g` agrees near the support of `φ` with a globally Lipschitz function, to which Mathlib's
`LipschitzWith.integral_lineDeriv_mul_eq` applies. -/
private theorem integral_mul_eq_neg_integral_lineDeriv_mul {g g' : E → ℝ}
    (hg : LocallyLipschitzOn Ω g) (h : ∀ᵐ x ∂μ, x ∈ Ω → HasLineDerivAt ℝ g (g' x) x v)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x, g' x * φ x ∂μ = -∫ x, lineDeriv ℝ (φ : E → ℝ) x v * g x ∂μ := by
  have hK : IsCompact (tsupport (φ : E → ℝ)) := φ.hasCompactSupport.isCompact
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen φ.tsupport_subset
  obtain ⟨C, hC⟩ := (hg.mono hδΩ).exists_lipschitzOnWith_of_compact hK.cthickening
  -- Extend `g` from the compact thickening of the support of `φ` to a Lipschitz function `G`.
  obtain ⟨G, hG, hgG⟩ := hC.extend_real
  obtain ⟨D, hD⟩ := φ.contDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport (by simp)
  have hGg : ∀ x ∈ tsupport (φ : E → ℝ), G =ᶠ[𝓝 x] g := fun x hx =>
    eventuallyEq_of_mem (mem_of_superset (isOpen_thickening.mem_nhds
      (self_subset_thickening hδ _ hx)) (thickening_subset_cthickening _ _)) hgG.symm
  have h1 : ∫ x, g' x * φ x ∂μ = ∫ x, lineDeriv ℝ G x v * φ x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    by_cases hxK : x ∈ tsupport (φ : E → ℝ)
    · rw [((hx (φ.tsupport_subset hxK)).congr_of_eventuallyEq (hGg x hxK)).lineDeriv]
    · simp [image_eq_zero_of_notMem_tsupport hxK]
  have h2 : ∫ x, lineDeriv ℝ (φ : E → ℝ) x (-v) * G x ∂μ =
      -∫ x, lineDeriv ℝ (φ : E → ℝ) x v * g x ∂μ := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [lineDeriv_neg, neg_mul]
    by_cases hxK : x ∈ tsupport (φ : E → ℝ)
    · rw [hgG (self_subset_cthickening _ hxK)]
    · simp [lineDeriv_eq_zero_of_notMem_tsupport φ hxK]
  rw [h1, hG.integral_lineDeriv_mul_eq hD φ.hasCompactSupport v, h2]

/-- **A locally Lipschitz function is weakly differentiable.** If `u` is locally Lipschitz on the
open set `Ω` and has line derivative `u' x` in the direction `v` at almost every `x ∈ Ω`, then
`u'` is the weak derivative of `u` in the direction `v` on `Ω`. -/
theorem _root_.LocallyLipschitzOn.hasWeakLineDerivOn [CompleteSpace F]
    (hu : LocallyLipschitzOn Ω u) (h : ∀ᵐ x ∂μ, x ∈ Ω → HasLineDerivAt ℝ u (u' x) x v) :
    HasWeakLineDerivOn μ Ω u u' v := by
  have hui := hu.continuousOn.locallyIntegrableOn (μ := μ) Ω.isOpen.measurableSet
  have hu'i := hu.locallyIntegrableOn_of_ae_hasLineDerivAt (μ := μ) Ω.isOpen h
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hui, hu'i, fun φ => ?_⟩
  -- Test the identity against every continuous linear functional `ℓ`, reducing to `ℓ ∘ u`.
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => ?_
  have hℓ : LocallyLipschitzOn Ω fun x => ℓ (u x) := fun x hx => by
    obtain ⟨C, s, hs, hC⟩ := hu hx
    exact ⟨‖ℓ‖₊ * C, s, hs, ℓ.lipschitzWith.comp_lipschitzOnWith hC⟩
  have key := integral_mul_eq_neg_integral_lineDeriv_mul hℓ
    (h.mono fun x hx hxΩ => (ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hx hxΩ) :)) φ
  rw [map_neg, ← ℓ.integral_comp_comm (integrable_lineDeriv_smul_of_locallyIntegrableOn hui φ v),
    ← ℓ.integral_comp_comm (integrable_smul_of_locallyIntegrableOn hu'i φ)]
  simp only [map_smul, smul_eq_mul]
  have hc : ∫ x, (φ : E → ℝ) x * ℓ (u' x) ∂μ = ∫ x, ℓ (u' x) * (φ : E → ℝ) x ∂μ := by
    simp_rw [mul_comm]
  rw [hc, key, neg_neg]

/-- **A locally Lipschitz function is weakly differentiable.** If `u` is locally Lipschitz on the
open set `Ω` and has Fréchet derivative `U x` at almost every `x ∈ Ω`, then `U` is the weak
derivative of `u` on `Ω`. -/
theorem _root_.LocallyLipschitzOn.hasWeakFDerivOn [CompleteSpace F] {U : E → E →L[ℝ] F}
    (hu : LocallyLipschitzOn Ω u) (h : ∀ᵐ x ∂μ, x ∈ Ω → HasFDerivAt u (U x) x) :
    HasWeakFDerivOn μ Ω u U := hasWeakFDerivOn_iff.2 fun v =>
  hu.hasWeakLineDerivOn (h.mono fun _ hx hxΩ => (hx hxΩ).hasLineDerivAt v)

/-- **A locally Lipschitz function has its derivative as weak derivative.** A function between
finite-dimensional real normed spaces that is locally Lipschitz on the open set `Ω` has
`fderiv ℝ u` as its weak derivative on `Ω`; by Rademacher's theorem it is differentiable almost
everywhere there. -/
theorem _root_.LocallyLipschitzOn.hasWeakFDerivOn_fderiv [FiniteDimensional ℝ F]
    (hu : LocallyLipschitzOn Ω u) : HasWeakFDerivOn μ Ω u (fderiv ℝ u) :=
  hu.hasWeakFDerivOn ((hu.ae_differentiableAt_of_mem Ω.isOpen).mono fun _ hx hxΩ =>
    (hx hxΩ).hasFDerivAt)

end TauCeti
