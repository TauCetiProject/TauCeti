/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Topology.FiberBundle.ULift
public import TauCeti.Topology.VectorBundle.Transfer

/-!
# Universe change for topological vector bundles (`ULift` and `Shrink`)

Provides `VectorBundle` instances for universe-lifted (`ULift`) and shrunk (`Shrink`) fibre
families (`instVectorBundleULift`, `instVectorBundleShrink`) over the `FiberBundle` instances in
`TauCeti.Topology.FiberBundle.ULift`.
-/

public section
open Bundle
namespace TauCeti
universe u v w w'
variable {B : Type u} (F : Type v) (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E]

omit [NormedSpace 𝕜 F] [FiberBundle F E] [VectorBundle 𝕜 F E] in
private theorem compContinuousLinearEquiv_eq_compFiberHomeomorph
    {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (t : Trivialization F (π F E)) (φ : ∀ b, E' b ≃L[𝕜] E b) (e : ∀ b, E' b ≃ₜ E b)
    (hφ : ∀ b x, e b x = φ b x) (hφ_symm : ∀ b y, (e b).symm y = (φ b).symm y)
    (h_ind₁ : Topology.IsInducing
      (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace F E)))
    (h_ind₂ : Topology.IsInducing
      (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    t.compContinuousLinearEquiv φ h_ind₁ = t.compFiberHomeomorph e h_ind₂ := by
  refine Trivialization.ext' _ _ (OpenPartialHomeomorph.ext _ _ ?_ ?_ ?_) ?_
  · intro p
    exact (t.compContinuousLinearEquiv_apply φ h_ind₁ p).trans
      ((congrArg (fun v ↦ t ⟨p.proj, v⟩) (hφ p.proj p.snd).symm).trans
        (t.compFiberHomeomorph_apply e h_ind₂ p).symm)
  · intro p
    refine (t.compContinuousLinearEquiv_symm_apply φ h_ind₁ p).trans ?_
    rw [totalSpaceHomeomorphOfContinuousLinearEquiv_symm_apply]
    refine Eq.symm ((t.compFiberHomeomorph_symm_apply e h_ind₂ p).trans ?_)
    rw [totalSpaceHomeomorphOfHomeomorph_symm_apply]
    exact congrArg (TotalSpace.mk _) (hφ_symm _ _)
  · rw [Trivialization.source_eq, Trivialization.source_eq,
      Trivialization.compContinuousLinearEquiv_baseSet,
      Trivialization.compFiberHomeomorph_baseSet]
  · rw [Trivialization.compContinuousLinearEquiv_baseSet,
      Trivialization.compFiberHomeomorph_baseSet]

private theorem vectorBundle_of_continuousLinearEquiv_fiberHomeomorph
    {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (φ : ∀ b, E' b ≃L[𝕜] E b) (e : ∀ b, E' b ≃ₜ E b)
    (hφ : ∀ b x, e b x = φ b x) (hφ_symm : ∀ b y, (e b).symm y = (φ b).symm y)
    (h_ind₁ : Topology.IsInducing
      (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace F E)))
    (h_ind₂ : Topology.IsInducing
      (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    letI := FiberBundle.ofHomeomorph F e h_ind₂
    VectorBundle 𝕜 F E' := by
  let fb₁ := FiberBundle.ofHomeomorph F e h_ind₂
  let fb₂ := FiberBundle.ofContinuousLinearEquiv F φ h_ind₁
  have hatlas :
      (letI := fb₁; trivializationAtlas F E') = (letI := fb₂; trivializationAtlas F E') := by
    have h₁ : (letI := fb₁; trivializationAtlas F E') =
        (fun t : Trivialization F (π F E) ↦ t.compFiberHomeomorph e h_ind₂) ''
          trivializationAtlas F E :=
      FiberBundle.trivializationAtlas_ofHomeomorph F e h_ind₂
    have h₂ : (letI := fb₂; trivializationAtlas F E') =
        (fun t : Trivialization F (π F E) ↦ t.compContinuousLinearEquiv φ h_ind₁) ''
          trivializationAtlas F E :=
      FiberBundle.trivializationAtlas_ofContinuousLinearEquiv F φ h_ind₁
    rw [h₁, h₂]
    ext t'
    simp [compContinuousLinearEquiv_eq_compFiberHomeomorph F E _ φ e hφ hφ_symm h_ind₁ h_ind₂]
  have hvb : @VectorBundle 𝕜 B F E' _ _ _ _ _ _ _ _ fb₂ :=
    VectorBundle.ofContinuousLinearEquiv F φ h_ind₁
  let _ := fb₁
  exact
    { trivialization_linear' := fun t ht ↦
        @VectorBundle.trivialization_linear' 𝕜 B F E' _ _ _ _ _ _ _ _ fb₂ hvb t
          (by let _ := fb₂; exact ⟨hatlas ▸ ht.out⟩)
      continuousOn_coordChange' := fun t₁ t₂ ht₁ ht₂ ↦
        @VectorBundle.continuousOn_coordChange' 𝕜 B F E' _ _ _ _ _ _ _ _ fb₂ hvb t₁ t₂
          (by let _ := fb₂; exact ⟨hatlas ▸ ht₁.out⟩)
          (by let _ := fb₂; exact ⟨hatlas ▸ ht₂.out⟩) }

/-- Transport a `VectorBundle` structure to the universe-lifted fibre family `ULift (E ·)`. -/
instance instVectorBundleULift : VectorBundle 𝕜 F (fun b ↦ ULift.{w'} (E b)) :=
  vectorBundle_of_continuousLinearEquiv_fiberHomeomorph F E
    (fun _ ↦ ContinuousLinearEquiv.ulift) (fun _ ↦ Homeomorph.ulift)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (isInducing_totalSpaceInduced F (fun _ ↦ Equiv.ulift))
    (isInducing_totalSpaceInduced F (fun _ ↦ Equiv.ulift))

/-- Transport a `VectorBundle` structure to the shrunk fibre family `Shrink (E ·)`. -/
instance instVectorBundleShrink [∀ b, Small.{w'} (E b)] :
    VectorBundle 𝕜 F (fun b ↦ Shrink.{w'} (E b)) :=
  vectorBundle_of_continuousLinearEquiv_fiberHomeomorph F E
    (fun b ↦ Shrink.continuousLinearEquiv 𝕜 (E b)) (fun b ↦ (Shrink.homeomorph (E b)).symm)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (isInducing_totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm))
    (isInducing_totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm))

end TauCeti
