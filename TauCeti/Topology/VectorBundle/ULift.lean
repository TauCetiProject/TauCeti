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

/-- Transport a `VectorBundle` structure to the universe-lifted fibre family `ULift (E ·)`. -/
instance instVectorBundleULift : VectorBundle 𝕜 F (fun b ↦ ULift.{w'} (E b)) := by
  -- `instFiberBundleULift` is built via `FiberBundle.ofHomeomorph` using `Homeomorph.ulift`,
  -- while `VectorBundle.ofContinuousLinearEquiv` uses `FiberBundle.ofContinuousLinearEquiv`.
  -- Generalize the homeomorphism family and its inducing proof so `rfl` substitution aligns them.
  have h :
      ∀ (e : ∀ b, ULift.{w'} (E b) ≃ₜ E b)
        (h_ind : Topology.IsInducing
          (fun p : TotalSpace F (fun b ↦ ULift.{w'} (E b)) ↦
            (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))),
        e = (fun b ↦
          (ContinuousLinearEquiv.ulift : ULift.{w'} (E b) ≃L[𝕜] E b).toHomeomorph) →
        letI := FiberBundle.ofHomeomorph F e h_ind
        VectorBundle 𝕜 F (fun b ↦ ULift.{w'} (E b)) := by
    rintro e h_ind rfl
    exact (FiberBundle.ofContinuousLinearEquiv_eq_ofHomeomorph F
      (fun b ↦ (ContinuousLinearEquiv.ulift : ULift.{w'} (E b) ≃L[𝕜] E b)) h_ind).symm ▸
      VectorBundle.ofContinuousLinearEquiv F
        (fun b ↦ (ContinuousLinearEquiv.ulift : ULift.{w'} (E b) ≃L[𝕜] E b)) h_ind
  exact h (fun _ ↦ Homeomorph.ulift) (isInducing_totalSpaceInduced F (fun _ ↦ Equiv.ulift))
    (funext fun _ ↦ Homeomorph.ext fun _ ↦ rfl)

/-- Transport a `VectorBundle` structure to the shrunk fibre family `Shrink (E ·)`. -/
instance instVectorBundleShrink [∀ b, Small.{w'} (E b)] :
    VectorBundle 𝕜 F (fun b ↦ Shrink.{w'} (E b)) := by
  -- As above, align `(Shrink.homeomorph _).symm` with
  -- `(Shrink.continuousLinearEquiv 𝕜 _).toHomeomorph`.
  have h :
      ∀ (e : ∀ b, Shrink.{w'} (E b) ≃ₜ E b)
        (h_ind : Topology.IsInducing
          (fun p : TotalSpace F (fun b ↦ Shrink.{w'} (E b)) ↦
            (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))),
        e = (fun b ↦ (Shrink.continuousLinearEquiv 𝕜 (E b)).toHomeomorph) →
        letI := FiberBundle.ofHomeomorph F e h_ind
        VectorBundle 𝕜 F (fun b ↦ Shrink.{w'} (E b)) := by
    rintro e h_ind rfl
    exact (FiberBundle.ofContinuousLinearEquiv_eq_ofHomeomorph F
      (fun b ↦ Shrink.continuousLinearEquiv 𝕜 (E b)) h_ind).symm ▸
      VectorBundle.ofContinuousLinearEquiv F (fun b ↦ Shrink.continuousLinearEquiv 𝕜 (E b)) h_ind
  exact h (fun b ↦ (Shrink.homeomorph (E b)).symm)
    (isInducing_totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm))
    (funext fun _ ↦ Homeomorph.ext fun _ ↦ rfl)

end TauCeti
