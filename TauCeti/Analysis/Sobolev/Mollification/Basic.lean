/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import TauCeti.Analysis.Convolution.Jensen
public import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Trace
import TauCeti.Analysis.Distribution.TestFunction.Translation

/-!
# Mollification of weakly differentiable functions

This file proves the identity at the heart of mollification in Sobolev spaces. If `u'` is the
weak derivative of `u` in the direction `v` on an open domain and `rho` is smooth with compact
support, then

`D_v (u ⋆ rho) = u' ⋆ rho`

at every point `x` for which `x - tsupport rho` lies in the domain. The convolved function
(and, for the Fréchet form, its weak derivative field) is assumed locally integrable on the
whole space; zero extensions of domain `Lᵖ` functions satisfy this assumption. No weak
derivative identity outside the domain is required.

The derivative identities hold for functions with values in an arbitrary real Banach space and
for any s-finite, left-invariant measure on a real normed space, such as an additive Haar measure.
The Jensen corollary below also assumes that the measure is negation-invariant and that the space
is second countable, as holds for an additive Haar measure on a finite-dimensional space.

This identity applies successively to the derivative fields of a Sobolev function, and is the
analytic input to local smooth approximation and Meyers--Serrin density. Combined with Jensen's
inequality for convolution (`ConvexOn.lintegral_ofReal_map_norm_convolution_le`), it shows that
mollifying by a probability kernel does not increase a convex integral `∫ Φ(‖Du‖)` of the
gradient, which is the form in which superlinear bounds from de la Vallée Poussin's criterion
pass to mollifications.

Dually, against an additive Haar measure on a finite-dimensional normed space, a normalized-bump
mollifier can be moved from any locally integrable function `u` on `Omega` onto a test vector field
`φ ∈ 𝓓(Omega, E)` whose enlarged support stays in `Omega`, giving the adjoint integration-by-parts
identity `∫ div (φ.mollify mu ρ h) • u = -∫ D(ρ ⋆ u) (φ)`
(`ContDiffBump.integral_divergenceCLM_mollify_smul_eq_neg_integral_fderiv_normed_convolution`).

## Main statements

* `TauCeti.HasWeakLineDerivOn.hasLineDerivAt_convolution_right`: convolution by a smooth,
  compactly supported scalar kernel turns a local weak directional derivative into the
  corresponding classical directional derivative.
* `TauCeti.HasWeakFDerivOn.hasFDerivAt_convolution_right`: the Fréchet form, identifying the
  derivative with the convolution of the weak derivative field.
* `TauCeti.HasWeakLineDerivOn.convolution_eq_apply_fderiv_convolution`: mollification commutes
  with a weak derivative taken through a continuous linear map.
* `TauCeti.HasWeakLineDerivOn.lineDeriv_convolution_right` and
  `TauCeti.HasWeakFDerivOn.fderiv_convolution_right`: the corresponding derivative equations.
* `TauCeti.HasWeakFDerivOn.lintegral_ofReal_map_norm_fderiv_convolution_le`: for a whole-space
  weak derivative and a smooth compactly supported probability kernel `rho`, Jensen's bound
  `∫ Φ(‖D(u ⋆ rho)‖) ≤ ∫ Φ(‖U‖)` for every `Φ` convex and monotone on `[0, ∞)`, for a
  negation-invariant measure on a second-countable space.
* `ContDiffBump.integral_divergenceCLM_mollify_smul_eq_neg_integral_fderiv_normed_convolution`:
  moving a normalized-bump mollifier from a locally integrable function `u` onto a test vector
  field `φ` satisfies `∫ div (mollify φ) • u = -∫ D(ρ ⋆ u) (φ)`.

## References

L. C. Evans, *Partial Differential Equations*, Section 5.3.1, Theorem 1; L. C. Evans and
R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, Section 4.1.1.
-/

public section

open MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped ContDiff Convolution Distributions Pointwise

namespace TauCeti

section

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddLeftInvariant] [SFinite mu] {Omega : Opens E}

/-- **A weak derivative commutes with convolution by a smooth compactly supported kernel.**
If `u'` is the weak derivative of `u` in the direction `v` on `Omega`, then the convolution of
`u` with `rho` has directional derivative `(u' ⋆ rho) x` in the direction `v` at every point `x`
whose translated kernel support `x - tsupport rho` is contained in `Omega`. -/
theorem HasWeakLineDerivOn.hasLineDerivAt_convolution_right {u u' : E → F} {v : E}
    (h : HasWeakLineDerivOn mu Omega u u' v) (hu : LocallyIntegrable u mu)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasLineDerivAt ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) ((u' ⋆[(lsmul ℝ ℝ).flip, mu] rho) x) x v := by
  have hweak := h.integral_lineDeriv_smul_eq_neg_integral_smul
    (reflectTranslateTestFunction rho x hrho hrho_cpt hx)
  simp only [lineDeriv_reflectTranslateTestFunction, reflectTranslateTestFunction_apply, neg_smul,
    integral_neg, neg_inj] at hweak
  convert (hrho_cpt.hasFDerivAt_convolution_right (lsmul ℝ ℝ).flip hu
    (hrho.of_le (by simp)) x).hasLineDerivAt v using 1
  rw [convolution_precompR_apply (lsmul ℝ ℝ).flip hu (hrho_cpt.fderiv ℝ)
    (hrho.continuous_fderiv (by simp)) x v]
  simpa only [convolution_def, flip_apply, lsmul_apply] using hweak.symm

/-- The directional derivative of a convolution with a smooth compactly supported kernel is the
convolution of the weak directional derivative with that kernel. -/
theorem HasWeakLineDerivOn.lineDeriv_convolution_right {u u' : E → F} {v : E}
    (h : HasWeakLineDerivOn mu Omega u u' v) (hu : LocallyIntegrable u mu)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    lineDeriv ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) x v = (u' ⋆[(lsmul ℝ ℝ).flip, mu] rho) x :=
  (h.hasLineDerivAt_convolution_right hu rho hrho hrho_cpt x hx).lineDeriv

/-- **Mollification commutes with a weak derivative taken through a continuous linear map.** Let
`U` be locally integrable, let `y ↦ L (U y)` have weak derivative `U'` on `Omega`, and let `rho` be
a smooth compactly supported kernel with `x - tsupport rho ⊆ Omega`. Then the mollification
`g = rho ⋆ U` satisfies `(rho ⋆ U') x = L (∂_v g x)`. -/
theorem HasWeakLineDerivOn.convolution_eq_apply_fderiv_convolution [mu.IsNegInvariant]
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {L : F →L[ℝ] G} {U : E → F} {U' : E → G} {v : E}
    (hind : HasWeakLineDerivOn mu Omega (fun y ↦ L (U y)) U' v) (hU : LocallyIntegrable U mu)
    {rho : E → ℝ} (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) {x : E}
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    (rho ⋆[lsmul ℝ ℝ, mu] U') x = L (fderiv ℝ (rho ⋆[lsmul ℝ ℝ, mu] U) x v) := by
  set g := rho ⋆[lsmul ℝ ℝ, mu] U with hg_def
  have hgd : HasFDerivAt g (fderiv ℝ g x) x :=
    ((hrho_cpt.contDiff_convolution_left _ (hrho.of_le (by simp)) hU :
      ContDiff ℝ 1 g).differentiable one_ne_zero x).hasFDerivAt
  -- `L ∘ g` is the mollification of `L ∘ U`, so its derivative is the mollification of `U'`.
  have hLg : (fun y ↦ L (g y)) = (fun y ↦ L (U y)) ⋆[(lsmul ℝ ℝ).flip, mu] rho := by
    ext1 y
    rw [convolution_flip, hg_def,
      L.convolution_lsmul_comp_comm (hrho_cpt.convolutionExists_left _ hrho.continuous hU y)]
  have h₁ : HasLineDerivAt ℝ (fun y ↦ L (g y)) ((U' ⋆[(lsmul ℝ ℝ).flip, mu] rho) x) x v := by
    rw [hLg]
    exact hind.hasLineDerivAt_convolution_right
      (fun y ↦ L.integrableAtFilter_comp (hU y)) rho hrho hrho_cpt x hx
  rw [← convolution_flip]
  exact h₁.unique ((L.hasFDerivAt.comp x hgd).hasLineDerivAt v)

/-- **The Fréchet derivative of a mollification is the mollification of the weak derivative.**
If `U` is a weak derivative field of `u` on `Omega` and both are locally integrable on the whole
space, the convolution of `u` with a smooth compactly supported scalar kernel `rho` has derivative
`(U ⋆ rho) x` at every point `x` whose translated kernel support `x - tsupport rho` lies in
`Omega`. -/
theorem HasWeakFDerivOn.hasFDerivAt_convolution_right {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu Omega u U) (hu : LocallyIntegrable u mu)
    (hU : LocallyIntegrable U mu) (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasFDerivAt (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) ((U ⋆[(lsmul ℝ ℝ).flip, mu] rho) x) x := by
  have hd := hrho_cpt.hasFDerivAt_convolution_right (lsmul ℝ ℝ).flip hu (hrho.of_le (by simp)) x
  refine hd.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  refine ((hd.hasLineDerivAt v).unique ((h.hasWeakLineDerivOn v).hasLineDerivAt_convolution_right
    hu rho hrho hrho_cpt x hx)).trans ?_
  have hInt := (hrho_cpt.convolutionExists_right (lsmul ℝ ℝ).flip hU hrho.continuous x).integrable
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hInt]
  simp only [flip_apply, lsmul_apply, smul_apply]

/-- The Fréchet derivative of a convolution with a smooth compactly supported kernel is the
convolution of the weak Fréchet derivative field with that kernel. -/
theorem HasWeakFDerivOn.fderiv_convolution_right {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu Omega u U) (hu : LocallyIntegrable u mu)
    (hU : LocallyIntegrable U mu) (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    fderiv ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) x = (U ⋆[(lsmul ℝ ℝ).flip, mu] rho) x :=
  (h.hasFDerivAt_convolution_right hu hU rho hrho hrho_cpt x hx).fderiv

/-- **Jensen's bound for the gradient of a mollification.** If `U` is a weak derivative field of
`u` on the whole space and `rho` is a smooth compactly supported probability kernel, then
`∫ Φ(‖D(u ⋆ rho)‖) ≤ ∫ Φ(‖U‖)` for every `Φ` convex and monotone on `[0, ∞)`, in extended
nonnegative form. -/
theorem HasWeakFDerivOn.lintegral_ofReal_map_norm_fderiv_convolution_le
    [SecondCountableTopology E] [mu.IsNegInvariant] {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu ⊤ u U)
    (hu : LocallyIntegrable u mu) (hU : LocallyIntegrable U mu) {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Set.Ici 0) Φ) (hΦm : MonotoneOn Φ (Set.Ici 0)) {rho : E → ℝ}
    (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) (hrho0 : 0 ≤ᵐ[mu] rho)
    (hrho1 : ∫ x, rho x ∂mu = 1) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) x‖) ∂mu ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖U x‖) ∂mu := by
  have hfderiv : fderiv ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) = rho ⋆[lsmul ℝ ℝ, mu] U := by
    ext1 x
    rw [h.fderiv_convolution_right hu hU rho hrho hrho_cpt x fun _ _ => trivial, convolution_flip]
  rw [hfderiv]
  exact hΦ.lintegral_ofReal_map_norm_convolution_le hΦm hrho0 hrho1 hU.aestronglyMeasurable

end

end TauCeti

namespace ContDiffBump

section DivergenceMollify

open TauCeti
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E}

/-- **Adjoint mollification against divergence.** Moving a normalized-bump mollifier from a
locally integrable function `u` on `Omega` onto a test vector field `φ ∈ 𝓓(Omega, E)` whose
enlarged support stays in `Omega` satisfies
`∫ div (φ.mollify mu ρ h) • u = -∫ D(ρ ⋆ u) (φ)`. -/
theorem integral_divergenceCLM_mollify_smul_eq_neg_integral_fderiv_normed_convolution
    (ρ : ContDiffBump (0 : E)) {u : E → F} (hu : LocallyIntegrableOn u Omega mu)
    (φ : 𝓓(Omega, E)) (h : Metric.closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Omega : Set E)) :
    ∫ z, TestFunction.divergenceCLM (φ.mollify mu ρ h) z • u z ∂mu =
      -∫ y, fderiv ℝ (ρ.normed mu ⋆[lsmul ℝ ℝ, mu] u) y (φ y) ∂mu := by
  by_cases hF : CompleteSpace F
  swap
  · rw [integral_of_not_completeSpace hF, integral_of_not_completeSpace hF, neg_zero]
  have : CompleteSpace F := hF
  -- Truncate `u` to a compact neighbourhood `K ⊆ Omega` of `closedBall 0 ρ.rOut + tsupport φ`.
  set K₀ : Set E := Metric.closedBall (0 : E) ρ.rOut + tsupport φ
  have hK₀ : IsCompact K₀ := (isCompact_closedBall _ _).add φ.hasCompactSupport.isCompact
  obtain ⟨δ, hδ, hδΩ⟩ := hK₀.exists_cthickening_subset_open Omega.isOpen h
  set K : Set E := Metric.cthickening δ K₀
  have hK : IsCompact K := by
    have heq : K = Metric.closedBall (0 : E) δ + K₀ := by
      simpa only [K, zero_vadd] using (hK₀.closedBall_add hδ.le 0).symm
    rw [heq]
    exact (isCompact_closedBall _ _).add hK₀
  set w : E → F := K.indicator u
  have hw : Integrable w mu :=
    (hu.integrableOn_compact_subset hδΩ hK).integrable_indicator hK.measurableSet
  -- On `thickening δ (tsupport φ)`, `ρ ⋆ w = ρ ⋆ u`, so their derivatives agree on `tsupport φ`.
  have hconv_eq : ∀ y ∈ Metric.thickening δ (tsupport φ),
      (ρ.normed mu ⋆[lsmul ℝ ℝ, mu] w) y = (ρ.normed mu ⋆[lsmul ℝ ℝ, mu] u) y := by
    intro y hy
    obtain ⟨y₀, hy₀, hdist⟩ := Metric.mem_thickening_iff.1 hy
    refine convolution_indicator_eq_of_forall_sub_mem (lsmul ℝ ℝ) fun t ht => ?_
    have ht_neg : -t ∈ Metric.closedBall (0 : E) ρ.rOut := by
      have ht_ball : t ∈ Metric.ball (0 : E) ρ.rOut := ρ.support_normed_eq.subset ht
      rw [mem_closedBall_zero_iff, norm_neg]
      exact (mem_ball_zero_iff.1 ht_ball).le
    have hy₀t : y₀ - t ∈ K₀ := by
      rw [sub_eq_neg_add]
      exact Set.add_mem_add ht_neg hy₀
    refine Metric.mem_cthickening_of_dist_le _ (y₀ - t) δ _ hy₀t ?_
    simpa only [dist_sub_right] using hdist.le
  have hrhs_eq : (∫ y, fderiv ℝ (ρ.normed mu ⋆[lsmul ℝ ℝ, mu] u) y (φ y) ∂mu) =
      ∫ y, fderiv ℝ (ρ.normed mu ⋆[lsmul ℝ ℝ, mu] w) y (φ y) ∂mu := by
    refine integral_congr_ae (.of_forall fun y => ?_)
    dsimp only
    by_cases hy : y ∈ tsupport φ
    · have hev : (ρ.normed mu ⋆[lsmul ℝ ℝ, mu] w) =ᶠ[𝓝 y] (ρ.normed mu ⋆[lsmul ℝ ℝ, mu] u) :=
        Filter.eventually_of_mem
          (Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδ _ hy)) hconv_eq
      rw [hev.fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hy, map_zero, map_zero]
  have hlhs_eq : (∫ z, TestFunction.divergenceCLM (φ.mollify mu ρ h) z • u z ∂mu) =
      ∫ z, TestFunction.divergenceCLM (φ.mollify mu ρ h) z • w z ∂mu := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ K
    · simp only [w, Set.indicator_of_mem hz]
    · have hnot : z ∉ tsupport (TestFunction.divergenceCLM (φ.mollify mu ρ h)) := fun hmem => by
        have hsub : tsupport (TestFunction.divergenceCLM (φ.mollify mu ρ h)) ⊆ K₀ :=
          (TestFunction.tsupport_divergenceCLM_subset _).trans <| by
            rw [TestFunction.coe_mollify]
            exact ρ.tsupport_normed_convolution_subset
        exact hz (Metric.self_subset_cthickening _ (hsub hmem))
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_smul, zero_smul]
  rw [hlhs_eq, hrhs_eq]
  -- Integrate by parts on the smooth mollification `wρ = ρ ⋆ w`, then swap integrals via Fubini.
  set wρ := ρ.normed mu ⋆[lsmul ℝ ℝ, mu] w
  have hwρ_cd : ContDiff ℝ 1 wρ :=
    ((ρ.hasCompactSupport_normed (μ := mu)).contDiff_convolution_left _
      (ρ.contDiff_normed (n := ⊤)) hw.locallyIntegrable).of_le (by simp)
  have hweak : HasWeakFDerivOn mu Omega wρ (fderiv ℝ wρ) :=
    hwρ_cd.contDiffOn.hasWeakFDerivOn_fderiv
  have hibp : -∫ y, fderiv ℝ wρ y (φ y) ∂mu = ∫ y, TestFunction.divergenceCLM φ y • wρ y ∂mu :=
    (hweak.integral_divergenceCLM_smul_eq_neg_integral φ).symm
  rw [hibp, integral_smul_convolution_eq_integral_convolution_comp_neg_smul
    (TestFunction.divergenceCLM φ).continuous (TestFunction.divergenceCLM φ).hasCompactSupport
    (ρ.integrable_normed (μ := mu)) (ρ.hasCompactSupport_normed (μ := mu)) hw]
  simp only [ρ.normed_neg, TestFunction.divergenceCLM_mollify φ mu ρ h, TestFunction.mollify_apply]

end DivergenceMollify

end ContDiffBump
