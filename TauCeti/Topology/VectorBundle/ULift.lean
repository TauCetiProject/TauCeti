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

private theorem vectorBundle_ofFiberHomeomorph
    {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (φ : ∀ b, E' b ≃L[𝕜] E b)
    (e : ∀ b, E' b ≃ₜ E b) (hφ : ∀ b x, e b x = φ b x)
    (h_ind : Topology.IsInducing
      (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    [FiberBundle F E']
    (hatlas : trivializationAtlas F E' =
      (fun t : Trivialization F (π F E) ↦ t.compFiberHomeomorph e h_ind) ''
        trivializationAtlas F E) :
    VectorBundle 𝕜 F E' := by
  have hlin : ∀ (t : Trivialization F (π F E)) [t.IsLinear 𝕜],
      (t.compFiberHomeomorph e h_ind).IsLinear 𝕜 := fun t _ ↦
    { linear := fun b hb ↦ by
        rw [Trivialization.compFiberHomeomorph_baseSet] at hb
        refine ⟨fun x y ↦ ?_, fun c x ↦ ?_⟩
        · simp only [Trivialization.compFiberHomeomorph_apply, hφ, map_add,
            (t.linear 𝕜 hb).map_add]
        · simp only [Trivialization.compFiberHomeomorph_apply, hφ, map_smul,
            (t.linear 𝕜 hb).map_smul] }
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro t' ht'
    have hmem := ht'.out
    rw [hatlas] at hmem
    rcases hmem with ⟨t, ht, rfl⟩
    have : MemTrivializationAtlas t := ⟨ht⟩
    exact hlin t
  · intro t₁' t₂' ht₁' ht₂'
    have hmem₁ := ht₁'.out; have hmem₂ := ht₂'.out
    rw [hatlas] at hmem₁ hmem₂
    rcases hmem₁ with ⟨t₁, ht₁, rfl⟩; rcases hmem₂ with ⟨t₂, ht₂, rfl⟩
    have : MemTrivializationAtlas t₁ := ⟨ht₁⟩; have : MemTrivializationAtlas t₂ := ⟨ht₂⟩
    have := hlin t₁; have := hlin t₂
    rw [Trivialization.compFiberHomeomorph_baseSet, Trivialization.compFiberHomeomorph_baseSet]
    refine (continuousOn_coordChange 𝕜 t₁ t₂).congr fun b hb ↦ ?_
    refine congrArg ContinuousLinearEquiv.toContinuousLinearMap ?_
    ext v
    have hb' : b ∈ (t₁.compFiberHomeomorph e h_ind).baseSet ∩
        (t₂.compFiberHomeomorph e h_ind).baseSet := by
      simpa only [Trivialization.compFiberHomeomorph_baseSet] using hb
    rw [Trivialization.coordChangeL_apply' _ _ hb', Trivialization.coordChangeL_apply' _ _ hb,
      Trivialization.compFiberHomeomorph_symm_apply, ← t₁.mk_symm hb.1 v,
      totalSpaceHomeomorphOfHomeomorph_symm_apply, Trivialization.compFiberHomeomorph_apply,
      Homeomorph.apply_symm_apply]

/-- Transport a `VectorBundle` structure to the universe-lifted fibre family `ULift (E ·)`. -/
instance instVectorBundleULift : VectorBundle 𝕜 F (fun b ↦ ULift.{w'} (E b)) :=
  vectorBundle_ofFiberHomeomorph F E
    (fun _ ↦ ContinuousLinearEquiv.ulift) (fun _ ↦ Homeomorph.ulift) (fun _ _ ↦ rfl)
    (isInducing_totalSpaceInduced F (fun _ ↦ Equiv.ulift))
    (FiberBundle.trivializationAtlas_ofHomeomorph F (fun _ ↦ Homeomorph.ulift)
      (isInducing_totalSpaceInduced F (fun _ ↦ Equiv.ulift)))

/-- Transport a `VectorBundle` structure to the shrunk fibre family `Shrink (E ·)`. -/
instance instVectorBundleShrink [∀ b, Small.{w'} (E b)] :
    VectorBundle 𝕜 F (fun b ↦ Shrink.{w'} (E b)) :=
  vectorBundle_ofFiberHomeomorph F E
    (fun b ↦ Shrink.continuousLinearEquiv 𝕜 (E b)) (fun b ↦ (Shrink.homeomorph (E b)).symm)
    (fun _ _ ↦ rfl)
    (isInducing_totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm))
    (FiberBundle.trivializationAtlas_ofHomeomorph F (fun b ↦ (Shrink.homeomorph (E b)).symm)
      (isInducing_totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm)))

end TauCeti
