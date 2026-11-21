/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Shrink
public import TauCeti.Topology.FiberBundle.Transport

/-!
# Universe change for fibre bundles (`ULift` and `Shrink`)

Specializes `TauCeti.totalSpaceHomeomorphOfIsInducing` and `TauCeti.fiberBundleOfHomeomorph` to
`ULift` and `Shrink` on the fibres of a fibre bundle: `instTopologicalSpaceTotalSpaceULift`,
`uliftTotalSpaceHomeomorph`, `instFiberBundleULift`, `trivializationAt_ulift_apply`, and the
corresponding `Shrink` instances and lemmas.
-/

public section
open Bundle
namespace TauCeti
universe u v w w'
variable {B : Type u} (F : Type v) (E : B → Type w) [TopologicalSpace (TotalSpace F E)]

/-- Equip the total space of `fun b ↦ ULift.{w'} (E b)` with the topology induced by `ULift.down`
on fibres. -/
instance instTopologicalSpaceTotalSpaceULift :
    TopologicalSpace (TotalSpace F (fun b ↦ ULift.{w'} (E b))) :=
  TopologicalSpace.induced (fun p : TotalSpace F (fun b ↦ ULift.{w'} (E b)) ↦
    (⟨p.proj, p.snd.down⟩ : TotalSpace F E)) inferInstance
/-- The total space of `fun b ↦ ULift.{w'} (E b)` is homeomorphic to `TotalSpace F E` over `B`. -/
def uliftTotalSpaceHomeomorph : TotalSpace F (fun b ↦ ULift.{w'} (E b)) ≃ₜ TotalSpace F E :=
  totalSpaceHomeomorphOfIsInducing F (fun _ ↦ Equiv.ulift) ⟨rfl⟩
@[simp] theorem uliftTotalSpaceHomeomorph_apply (p : TotalSpace F (fun b ↦ ULift.{w'} (E b))) :
    uliftTotalSpaceHomeomorph F E p = ⟨p.proj, p.snd.down⟩ := (rfl)
@[simp] theorem uliftTotalSpaceHomeomorph_symm_apply (p : TotalSpace F E) :
    (uliftTotalSpaceHomeomorph.{u, v, w, w'} F E).symm p = ⟨p.proj, ULift.up p.snd⟩ := (rfl)

section ULiftFiberBundle
variable [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
/-- Transport a `FiberBundle` structure to the universe-lifted fibre family `ULift (E ·)`. -/
noncomputable instance instFiberBundleULift : FiberBundle F (fun b ↦ ULift.{w'} (E b)) :=
  fiberBundleOfHomeomorph F (fun _ ↦ Homeomorph.ulift) ⟨rfl⟩
-- Not `@[simp]`: `instFiberBundleULift` is exposed as `fiberBundleOfHomeomorph`, so
-- `trivializationAt_fiberBundleOfHomeomorph` triggers `simpNF` on the LHS.
/-- Applying the chosen trivialization of the universe-lifted fibre bundle evaluates the underlying
trivialization at `ULift.down` on the fibre. -/
theorem trivializationAt_ulift_apply (b : B) (p : TotalSpace F (fun x ↦ ULift.{w'} (E x))) :
    trivializationAt F (fun x ↦ ULift.{w'} (E x)) b p =
      trivializationAt F E b ⟨p.proj, p.snd.down⟩ :=
  congrArg (fun e ↦ e p)
    (trivializationAt_fiberBundleOfHomeomorph F (fun _ ↦ Homeomorph.ulift) ⟨rfl⟩ b)
end ULiftFiberBundle

section Shrink
variable [∀ b, Small.{w'} (E b)]
/-- Equip the total space of `fun b ↦ Shrink.{w'} (E b)` with the topology induced by
`(equivShrink (E b)).symm` on fibres. -/
noncomputable instance instTopologicalSpaceTotalSpaceShrink :
    TopologicalSpace (TotalSpace F (fun b ↦ Shrink.{w'} (E b))) :=
  TopologicalSpace.induced (fun p : TotalSpace F (fun b ↦ Shrink.{w'} (E b)) ↦
    (⟨p.proj, (equivShrink (E p.proj)).symm p.snd⟩ : TotalSpace F E)) inferInstance
/-- The total space of `fun b ↦ Shrink.{w'} (E b)` is homeomorphic to `TotalSpace F E` over `B`. -/
noncomputable def shrinkTotalSpaceHomeomorph :
    TotalSpace F (fun b ↦ Shrink.{w'} (E b)) ≃ₜ TotalSpace F E :=
  totalSpaceHomeomorphOfIsInducing F (fun b ↦ (equivShrink (E b)).symm) ⟨rfl⟩
@[simp] theorem shrinkTotalSpaceHomeomorph_apply (p : TotalSpace F (fun b ↦ Shrink.{w'} (E b))) :
    shrinkTotalSpaceHomeomorph F E p = ⟨p.proj, (equivShrink (E p.proj)).symm p.snd⟩ := (rfl)
@[simp] theorem shrinkTotalSpaceHomeomorph_symm_apply (p : TotalSpace F E) :
    (shrinkTotalSpaceHomeomorph.{u, v, w, w'} F E).symm p =
      ⟨p.proj, equivShrink (E p.proj) p.snd⟩ := (rfl)

variable [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
/-- Transport a `FiberBundle` structure to the shrunk fibre family `Shrink (E ·)`. -/
noncomputable instance instFiberBundleShrink : FiberBundle F (fun b ↦ Shrink.{w'} (E b)) :=
  fiberBundleOfHomeomorph F (fun b ↦ (Shrink.homeomorph (E b)).symm) ⟨rfl⟩
-- Not `@[simp]`: `instFiberBundleShrink` is exposed as `fiberBundleOfHomeomorph`, so
-- `trivializationAt_fiberBundleOfHomeomorph` triggers `simpNF` on the LHS.
/-- Applying the chosen trivialization of the shrunk fibre bundle evaluates the underlying
trivialization at `(equivShrink _).symm` on the fibre. -/
theorem trivializationAt_shrink_apply (b : B) (p : TotalSpace F (fun x ↦ Shrink.{w'} (E x))) :
    trivializationAt F (fun x ↦ Shrink.{w'} (E x)) b p =
      trivializationAt F E b ⟨p.proj, (equivShrink (E p.proj)).symm p.snd⟩ :=
  congrArg (fun e ↦ e p)
    (trivializationAt_fiberBundleOfHomeomorph F (fun b ↦ (Shrink.homeomorph (E b)).symm) ⟨rfl⟩ b)
end Shrink
end TauCeti
