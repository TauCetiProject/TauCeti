/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic

/-!
# Continuity of the Levi-Civita Ricci tensor

The Ricci tensor of a smooth Riemannian metric is continuous as a section of the bundle of
continuous bilinear forms on tangent spaces.
-/

public noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The Levi-Civita Ricci tensor varies continuously in the bilinear-form bundle. -/
theorem continuous_leviCivita_ricciTensor :
    Continuous (fun x : M ↦
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
        ((leviCivitaConnection I M).ricciTensor x).toContinuousBilinearMap) := by
  let cov := leviCivitaConnection I M
  let ϕ (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    (cov.ricciTensor x).toContinuousBilinearMap
  change Continuous (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (ϕ x))
  refine continuous_iff_continuousAt.mpr fun a ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  dsimp only [TotalSpace.mk', TotalSpace.proj, TotalSpace.snd]
  simp only [← tangentBilinFormInCoordinates_def]
  rw [continuousAt_clm_apply]
  intro v
  rw [continuousAt_clm_apply]
  intro w
  let e := trivializationAt E (fun x : M ↦ TangentSpace I x) a
  have ha : a ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' a
  have hσ : CMDiffAt ∞ (T% (fun x ↦ e.symmL ℝ x v)) a :=
    (e.contMDiffAt_symmL ha).clm_bundle_apply (by
      rw [contMDiffAt_section_iff]
      exact contMDiffAt_const)
  have hτ : CMDiffAt ∞ (T% (fun x ↦ e.symmL ℝ x w)) a :=
    (e.contMDiffAt_symmL ha).clm_bundle_apply (by
      rw [contMDiffAt_section_iff]
      exact contMDiffAt_const)
  have h := (cov.contMDiffAt_ricciTensor_apply hσ hτ).continuousAt
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds ha] with x hx
  simp only [tangentBilinFormInCoordinates_apply a hx, ϕ,
    e.symmL_apply hx, LinearMap.toContinuousBilinearMap_apply]
  rfl

end TauCeti.Manifold
