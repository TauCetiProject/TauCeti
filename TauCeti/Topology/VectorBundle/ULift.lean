/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.TransferInstance
public import TauCeti.Topology.FiberBundle.ULift
public import TauCeti.Topology.VectorBundle.Transport

/-!
# Universe change for topological vector bundles (`ULift` and `Shrink`)

Specializes `TauCeti.vectorBundleOfContinuousLinearEquiv` to `ContinuousLinearEquiv.ulift` and
`Shrink.continuousLinearEquiv`, providing `VectorBundle` instances for universe-lifted (`ULift`)
and shrunk (`Shrink`) fibre families over the fibre-bundle instances in
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
instance instVectorBundleULift : VectorBundle 𝕜 F (fun b ↦ ULift.{w'} (E b)) :=
  vectorBundleOfContinuousLinearEquiv 𝕜 (fun _ ↦ ContinuousLinearEquiv.ulift) ⟨rfl⟩

/-- Transport a `VectorBundle` structure to the shrunk fibre family `Shrink (E ·)`. -/
instance instVectorBundleShrink [∀ b, Small.{w'} (E b)] :
    VectorBundle 𝕜 F (fun b ↦ Shrink.{w'} (E b)) :=
  vectorBundleOfContinuousLinearEquiv 𝕜 (fun b ↦ Shrink.continuousLinearEquiv 𝕜 (E b)) ⟨rfl⟩

end TauCeti
