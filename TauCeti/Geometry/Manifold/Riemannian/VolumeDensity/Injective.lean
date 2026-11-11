/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
/-!
# Riemannian change of variables on measurable injective carriers

An actual injective parametrization differentiable at every point of a measurable carrier
pushes its native Gram-Jacobian-weighted coordinate measure to Riemannian volume of the
image. Lusin–Suslin proves image measurability, and a native countable chart cover assembles
the preferred-chart change-of-variables identities.

A C¹ parametrization on an open neighborhood of the carrier gives the full nonnegative
measurable weighted integral. The carrier itself may be merely measurable, and the map
need not be injective on a surrounding open set. No partial diffeomorphism or regularity
certificate is required.
-/

public section
open Bundle FiberBundle MeasureTheory Set Riemannian.Tensor
open scoped ENNReal InnerProductSpace Manifold Topology
noncomputable section
namespace TauCeti
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- An actual injective parametrization differentiable on a measurable carrier pushes
its native Gram-Jacobian-weighted measure exactly to the native Riemannian image volume. -/
theorem _root_.Module.Basis.map_withDensity_riemannianJacobian_of_injOn
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s : Set F} (hs : MeasurableSet s) (hinj : InjOn f s)
    (hf : ∀ x ∈ s, MDifferentiableAt 𝓘(ℝ, F) I f x) :
    Measure.map f ((b.addHaar.restrict s).withDensity
      (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b f x))) =
      (riemannianVolume I M).restrict (f '' s) := by
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have hc : ContinuousOn f s := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have him : MeasurableSet (f '' s) := hs.image_of_continuousOn_injOn hc hinj
  let μ := (b.addHaar.restrict s).withDensity
    (fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b f x))
  have hF : AEMeasurable f μ := (hc.aemeasurable hs).mono_ac
    (withDensity_absolutelyContinuous _ _)
  have hpre (T : Set M) (hT : MeasurableSet T) : MeasurableSet (f ⁻¹' T ∩ s) := by
    have hcs : Continuous (fun x : s ↦ f x.val) :=
      hc.comp_continuous continuous_subtype_val (fun x ↦ x.property)
    have hi := (MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr
      (hT.preimage hcs.measurable)
    convert hi using 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, exists_prop]
    exact and_comm
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover
    (fun x : M ↦ (chartAt H x).source) fun x ↦ chart_source_mem_nhds H x
  apply Measure.ext_of_biUnion_eq_univ ht hcover
  intro α _
  ext A hA
  have hT : MeasurableSet (A ∩ (chartAt H α).source) :=
    hA.inter (chartAt H α).open_source.measurableSet
  let S := f ⁻¹' (A ∩ (chartAt H α).source) ∩ s
  have hS : MeasurableSet S := hpre _ hT
  have himage : f '' S = (A ∩ (chartAt H α).source) ∩ f '' s := by
    dsimp only [S]
    rw [inter_comm, image_inter_preimage, inter_comm]
  have hsub : MapsTo f S (chartAt H α).source := fun x hx ↦ hx.1.2
  have hcov := setLIntegral_riemannianVolume_image_of_subset_chart b hdim hS
    (himage ▸ hT.inter him) (hinj.mono inter_subset_right) hsub
    (fun x hx ↦ hf x hx.2) (fun _ ↦ 1)
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one, himage] at hcov
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA,
    Measure.restrict_apply hT, Measure.map_apply_of_aemeasurable hF hT,
    withDensity_apply', Measure.restrict_restrict' hs]
  exact hcov.symm
/-- Riemannian integration over an actual injective image of a measurable carrier is
Gram-Jacobian-weighted coordinate integration for every nonnegative measurable weight. -/
theorem _root_.Module.Basis.setLIntegral_riemannianVolume_image_of_injOn
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {s U : Set F} (hs : MeasurableSet s) (hU : IsOpen U) (hsub : s ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, F) I 1 f U) (hinj : InjOn f s)
    {φ : M → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y in f '' s, φ y ∂riemannianVolume I M =
      ∫⁻ x in s, ENNReal.ofReal (riemannianJacobian (I := I) b f x) * φ (f x) ∂b.addHaar := by
  let μ := b.addHaar.restrict s
  let ρ := fun x ↦ ENNReal.ofReal (riemannianJacobian (I := I) b f x)
  have hρ : AEMeasurable ρ μ :=
    ((ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_riemannianJacobian b hf hU)).mono hsub).aemeasurable hs
  have hF : AEMeasurable f (μ.withDensity ρ) :=
    ((hf.continuousOn.mono hsub).aemeasurable hs).mono_ac (withDensity_absolutelyContinuous _ _)
  have hdiff (x : F) (hx : x ∈ s) : MDifferentiableAt 𝓘(ℝ, F) I f x :=
    (hf.contMDiffAt (hU.mem_nhds (hsub hx))).mdifferentiableAt one_ne_zero
  rw [← b.map_withDensity_riemannianJacobian_of_injOn hdim hs hinj hdiff,
    lintegral_map' hφ.aemeasurable hF]
  simpa only [Function.comp_apply, Pi.mul_apply] using
    lintegral_withDensity_eq_lintegral_mul₀' hρ (hφ.comp_aemeasurable hF)
end TauCeti
