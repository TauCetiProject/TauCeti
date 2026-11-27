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
`TauCeti.Topology.FiberBundle.ULift`, together with the preferred-chart identifications
`continuousLinearEquivAt_ulift` and `continuousLinearEquivAt_shrink`.
-/

public section
open Bundle
namespace TauCeti
universe u v w w'
variable {B : Type u} (F : Type v) (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- Transport `VectorBundle` along `e_homeo` by substituting an equal family `(e ·).toHomeomorph`
and applying `VectorBundle.ofContinuousLinearEquiv` (whose `FiberBundle` agrees definitionally). -/
private theorem vectorBundle_ofHomeomorph_eq
    {E' : B → Type w'} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b) (e_homeo : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : Topology.IsInducing
      (fun p : TotalSpace F E' ↦ (⟨p.proj, e_homeo p.proj p.snd⟩ : TotalSpace F E)))
    (he : e_homeo = fun b ↦ (e b).toHomeomorph) :
    letI := FiberBundle.ofHomeomorph F e_homeo h_ind
    VectorBundle 𝕜 F E' := by
  subst he
  exact VectorBundle.ofContinuousLinearEquiv F e h_ind

/-- Transport a `VectorBundle` structure to the universe-lifted fibre family `ULift (E ·)`. -/
instance instVectorBundleULift : VectorBundle 𝕜 F (fun b ↦ ULift.{w'} (E b)) :=
  vectorBundle_ofHomeomorph_eq F E
    (fun b ↦ (ContinuousLinearEquiv.ulift : ULift.{w'} (E b) ≃L[𝕜] E b))
    (fun _ ↦ Homeomorph.ulift)
    (isInducing_totalSpaceInduced F (fun _ ↦ Equiv.ulift))
    (funext fun _ ↦ Homeomorph.ext fun _ ↦ rfl)

/-- On the universe-lifted vector bundle, the preferred chart equivalence at `b` factors through
`ContinuousLinearEquiv.ulift`. -/
@[simp] theorem continuousLinearEquivAt_ulift (b : B) :
    VectorBundle.continuousLinearEquivAt 𝕜 F (fun x ↦ ULift.{w'} (E x)) b =
      (ContinuousLinearEquiv.ulift : ULift.{w'} (E b) ≃L[𝕜] E b).trans
        (VectorBundle.continuousLinearEquivAt 𝕜 F E b) := by
  refine DFunLike.ext _ _ fun v ↦ ?_
  rw [VectorBundle.continuousLinearEquivAt_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.ulift_apply, VectorBundle.continuousLinearEquivAt_apply]
  exact congrArg Prod.snd (trivializationAt_ulift_apply F E b ⟨b, v⟩)

/-- Transport a `VectorBundle` structure to the shrunk fibre family `Shrink (E ·)`. -/
instance instVectorBundleShrink [∀ b, Small.{w'} (E b)] :
    VectorBundle 𝕜 F (fun b ↦ Shrink.{w'} (E b)) :=
  vectorBundle_ofHomeomorph_eq F E
    (fun b ↦ Shrink.continuousLinearEquiv 𝕜 (E b))
    (fun b ↦ (Shrink.homeomorph (E b)).symm)
    (isInducing_totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm))
    (funext fun _ ↦ Homeomorph.ext fun _ ↦ rfl)

/-- On the shrunk vector bundle, the preferred chart equivalence at `b` factors through
`Shrink.continuousLinearEquiv`. -/
@[simp] theorem continuousLinearEquivAt_shrink [∀ b, Small.{w'} (E b)] (b : B) :
    VectorBundle.continuousLinearEquivAt 𝕜 F (fun x ↦ Shrink.{w'} (E x)) b =
      (Shrink.continuousLinearEquiv 𝕜 (E b)).trans
        (VectorBundle.continuousLinearEquivAt 𝕜 F E b) := by
  refine DFunLike.ext _ _ fun v ↦ ?_
  rw [VectorBundle.continuousLinearEquivAt_apply, ContinuousLinearEquiv.trans_apply,
    Shrink.continuousLinearEquiv_apply, VectorBundle.continuousLinearEquivAt_apply]
  exact congrArg Prod.snd (trivializationAt_shrink_apply F E b ⟨b, v⟩)

end TauCeti
