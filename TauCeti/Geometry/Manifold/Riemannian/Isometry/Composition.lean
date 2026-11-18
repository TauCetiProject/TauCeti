/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local

/-!
# Cancellation of local Riemannian isometries

A smooth map is a local Riemannian isometry when its composition with a local Riemannian
isometry is one. Both invertibility and preservation of the metric follow by cancelling
the actual differential of the second map.
-/

public section
open Bundle Manifold
open scoped ContDiff Manifold
namespace TauCeti.IsLocalRiemannianIsometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : N ↦ TangentSpace J x)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {K : ModelWithCorners ℝ E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [RiemannianBundle (fun x : P ↦ TangentSpace K x)]
  {f : M → N} {g : N → P}
/-- Cancel a local Riemannian isometry on the left of a smooth composition. -/
theorem of_comp_left (hgf : IsLocalRiemannianIsometry I K (g ∘ f))
    (hg : IsLocalRiemannianIsometry J K g) (hf : ContMDiff I J ∞ f) :
    IsLocalRiemannianIsometry I J f := by
  refine ⟨hf, fun x ↦ ?_, fun x v w ↦ ?_⟩
  · have h := hgf.isInvertible_mfderiv x
    rw [mfderiv_comp x (hg.mdifferentiableAt (f x))
      (hf.mdifferentiableAt (by simp))] at h
    obtain ⟨A, hA⟩ := hg.isInvertible_mfderiv (f x)
    rw [← hA] at h
    exact ContinuousLinearMap.isInvertible_equiv_comp.mp h
  · have h := hgf.inner_mfderiv x v w
    rw [mfderiv_comp_apply x (hg.mdifferentiableAt (f x))
      (hf.mdifferentiableAt (by simp)),
      mfderiv_comp_apply x (hg.mdifferentiableAt (f x))
        (hf.mdifferentiableAt (by simp)), hg.inner_mfderiv] at h
    exact h
end TauCeti.IsLocalRiemannianIsometry
