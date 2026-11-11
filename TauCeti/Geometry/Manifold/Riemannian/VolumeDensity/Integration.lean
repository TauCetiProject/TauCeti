/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Signed change of variables for native Riemannian volume

The exact native pushforward measure identity for a partial diffeomorphism gives change of
variables for every signed a.e.-strongly measurable real weight; no integrability hypothesis
is needed. The coordinate integral uses the actual Gram Jacobian and the Haar measure
associated to the same coordinate basis.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2.
-/

public section
open Bundle MeasureTheory Set TauCeti
open scoped Manifold ContDiff ENNReal
noncomputable section
namespace PartialDiffeomorph
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Signed a.e.-strongly measurable weights on the actual target of a partial diffeomorphism
satisfy the native Riemannian change-of-variables formula; no integrability is assumed. -/
theorem setIntegral_riemannianVolume_eq
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M 1) (b : Module.Basis ι ℝ F)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : M → ℝ} (hf : AEStronglyMeasurable f ((riemannianVolume I M).restrict Φ.target)) :
    ∫ y in Φ.target, f y ∂riemannianVolume I M =
      ∫ x in Φ.source, riemannianJacobian (I := I) b Φ x * f (Φ x) ∂b.addHaar := by
  let μ := b.addHaar.restrict Φ.source
  let ρ := fun x => ENNReal.ofReal (riemannianJacobian (I := I) b Φ x)
  have hρ : AEMeasurable ρ μ :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_riemannianJacobian b Φ.contMDiffOn_toFun Φ.open_source)).aemeasurable
      Φ.open_source.measurableSet
  have hΦ : AEMeasurable Φ (μ.withDensity ρ) :=
    (Φ.contMDiffOn_toFun.continuousOn.aemeasurable Φ.open_source.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hfm : AEStronglyMeasurable f (Measure.map Φ (μ.withDensity ρ)) := by
    rw [Φ.map_withDensity_riemannianJacobian b hdim]
    exact hf
  rw [← Φ.map_withDensity_riemannianJacobian b hdim, integral_map hΦ hfm,
    integral_withDensity_eq_integral_toReal_smul₀ hρ
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ρ, μ, ENNReal.toReal_ofReal (riemannianJacobian_nonneg b Φ _), smul_eq_mul]
/-- Signed native volume integration over the actual image of an injective local
parametrization, with its actual open domain and genuine Gram Jacobian. -/
theorem _root_.IsLocalDiffeomorphOn.setIntegral_riemannianVolume_image
    {g : F → M} {U : Set F} (hg : IsLocalDiffeomorphOn 𝓘(ℝ, F) I 1 g U)
    (hU : IsOpen U) (hinj : Set.InjOn g U) (b : Module.Basis ι ℝ F)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : M → ℝ} (hf : AEStronglyMeasurable f ((riemannianVolume I M).restrict (g '' U))) :
    ∫ y in g '' U, f y ∂riemannianVolume I M =
      ∫ x in U, riemannianJacobian (I := I) b g x * f (g x) ∂b.addHaar := by
  let Φ := hg.partialDiffeomorphOfInjOn hU hinj
  have hfun : (Φ : F → M) = g :=
    IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn hg hU hinj
  have htarget : Φ.target = g '' U :=
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target hg hU hinj
  have hsource : Φ.source = U :=
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source hg hU hinj
  have h := Φ.setIntegral_riemannianVolume_eq b hdim (htarget.symm ▸ hf)
  rw [hsource, htarget, hfun] at h
  exact h
end PartialDiffeomorph
