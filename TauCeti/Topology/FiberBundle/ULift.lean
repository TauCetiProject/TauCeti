/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Shrink
public import TauCeti.Topology.FiberBundle.Transfer

/-!
# Universe change for fibre bundles (`ULift` and `Shrink`)

Specializes `TauCeti.totalSpaceInduced`, `TauCeti.totalSpaceHomeomorphOfHomeomorph`, and
`FiberBundle.ofHomeomorph` to `ULift` and `Shrink` on the fibres of a fibre bundle:
`instTopologicalSpaceTotalSpaceULift`, `uliftTotalSpaceHomeomorph`, `instFiberBundleULift`,
`trivializationAt_ulift_apply`, and the corresponding `Shrink` instances and lemmas.
-/

public section
open Bundle
namespace TauCeti
universe u v w w'
variable {B : Type u} (F : Type v) (E : B → Type w) [TopologicalSpace (TotalSpace F E)]

/-- Equip the total space of `fun b ↦ ULift.{w'} (E b)` with the topology induced by `ULift.down`
on fibres. -/
@[instance_reducible]
instance instTopologicalSpaceTotalSpaceULift :
    TopologicalSpace (TotalSpace F (fun b ↦ ULift.{w'} (E b))) :=
  totalSpaceInduced F (fun _ ↦ Equiv.ulift)

section ULiftHomeomorph
variable [∀ b, TopologicalSpace (E b)]

/-- The total space of `fun b ↦ ULift.{w'} (E b)` is homeomorphic to `TotalSpace F E` over `B`. -/
def uliftTotalSpaceHomeomorph : TotalSpace F (fun b ↦ ULift.{w'} (E b)) ≃ₜ TotalSpace F E :=
  totalSpaceHomeomorphOfHomeomorph F (fun _ ↦ Homeomorph.ulift)
    (isInducing_totalSpaceInduced F (fun _ ↦ Equiv.ulift))

@[simp] theorem uliftTotalSpaceHomeomorph_apply (p : TotalSpace F (fun b ↦ ULift.{w'} (E b))) :
    uliftTotalSpaceHomeomorph F E p = ⟨p.proj, p.snd.down⟩ :=
  totalSpaceHomeomorphOfHomeomorph_apply F (fun _ ↦ Homeomorph.ulift) _ p

@[simp] theorem uliftTotalSpaceHomeomorph_symm_apply (p : TotalSpace F E) :
    (uliftTotalSpaceHomeomorph.{u, v, w, w'} F E).symm p = ⟨p.proj, ULift.up p.snd⟩ :=
  totalSpaceHomeomorphOfHomeomorph_symm_apply F (fun _ ↦ Homeomorph.ulift) _ p

end ULiftHomeomorph

section ULiftFiberBundle
variable [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- Transport a `FiberBundle` structure to the universe-lifted fibre family `ULift (E ·)`. -/
@[instance_reducible]
noncomputable instance instFiberBundleULift : FiberBundle F (fun b ↦ ULift.{w'} (E b)) :=
  FiberBundle.ofHomeomorph F (fun _ ↦ Homeomorph.ulift)
    (isInducing_totalSpaceInduced F (fun _ ↦ Equiv.ulift))

-- Not `@[simp]`: `instFiberBundleULift` is exposed as `FiberBundle.ofHomeomorph`, so
-- `FiberBundle.trivializationAt_ofHomeomorph` triggers `simpNF` on the LHS.
/-- Applying the chosen trivialization of the universe-lifted fibre bundle evaluates the underlying
trivialization at `ULift.down` on the fibre. -/
theorem trivializationAt_ulift_apply (b : B) (p : TotalSpace F (fun x ↦ ULift.{w'} (E x))) :
    trivializationAt F (fun x ↦ ULift.{w'} (E x)) b p =
      trivializationAt F E b ⟨p.proj, p.snd.down⟩ :=
  (congrArg (fun e ↦ e p)
    (FiberBundle.trivializationAt_ofHomeomorph F (fun _ ↦ Homeomorph.ulift)
      (isInducing_totalSpaceInduced F (fun _ ↦ Equiv.ulift)) b)).trans
    (Trivialization.compFiberHomeomorph_apply _ _ _ _)
end ULiftFiberBundle

section Shrink
variable [∀ b, Small.{w'} (E b)]

/-- Equip the total space of `fun b ↦ Shrink.{w'} (E b)` with the topology induced by
`(equivShrink (E b)).symm` on fibres. -/
@[instance_reducible]
noncomputable instance instTopologicalSpaceTotalSpaceShrink :
    TopologicalSpace (TotalSpace F (fun b ↦ Shrink.{w'} (E b))) :=
  totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm)

section ShrinkHomeomorph
variable [∀ b, TopologicalSpace (E b)]

/-- The total space of `fun b ↦ Shrink.{w'} (E b)` is homeomorphic to `TotalSpace F E` over `B`. -/
noncomputable def shrinkTotalSpaceHomeomorph :
    TotalSpace F (fun b ↦ Shrink.{w'} (E b)) ≃ₜ TotalSpace F E :=
  totalSpaceHomeomorphOfHomeomorph F (fun b ↦ (Shrink.homeomorph (E b)).symm)
    (isInducing_totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm))

@[simp] theorem shrinkTotalSpaceHomeomorph_apply (p : TotalSpace F (fun b ↦ Shrink.{w'} (E b))) :
    shrinkTotalSpaceHomeomorph F E p = ⟨p.proj, (equivShrink (E p.proj)).symm p.snd⟩ :=
  totalSpaceHomeomorphOfHomeomorph_apply F (fun b ↦ (Shrink.homeomorph (E b)).symm) _ p

@[simp] theorem shrinkTotalSpaceHomeomorph_symm_apply (p : TotalSpace F E) :
    (shrinkTotalSpaceHomeomorph.{u, v, w, w'} F E).symm p =
      ⟨p.proj, equivShrink (E p.proj) p.snd⟩ :=
  totalSpaceHomeomorphOfHomeomorph_symm_apply F (fun b ↦ (Shrink.homeomorph (E b)).symm) _ p

end ShrinkHomeomorph

variable [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- Transport a `FiberBundle` structure to the shrunk fibre family `Shrink (E ·)`. -/
@[instance_reducible]
noncomputable instance instFiberBundleShrink : FiberBundle F (fun b ↦ Shrink.{w'} (E b)) :=
  FiberBundle.ofHomeomorph F (fun b ↦ (Shrink.homeomorph (E b)).symm)
    (isInducing_totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm))

-- Not `@[simp]`: `instFiberBundleShrink` is exposed as `FiberBundle.ofHomeomorph`, so
-- `FiberBundle.trivializationAt_ofHomeomorph` triggers `simpNF` on the LHS.
/-- Applying the chosen trivialization of the shrunk fibre bundle evaluates the underlying
trivialization at `(equivShrink _).symm` on the fibre. -/
theorem trivializationAt_shrink_apply (b : B) (p : TotalSpace F (fun x ↦ Shrink.{w'} (E x))) :
    trivializationAt F (fun x ↦ Shrink.{w'} (E x)) b p =
      trivializationAt F E b ⟨p.proj, (equivShrink (E p.proj)).symm p.snd⟩ :=
  (congrArg (fun e ↦ e p)
    (FiberBundle.trivializationAt_ofHomeomorph F (fun b ↦ (Shrink.homeomorph (E b)).symm)
      (isInducing_totalSpaceInduced F (fun b ↦ (equivShrink (E b)).symm)) b)).trans
    (Trivialization.compFiberHomeomorph_apply _ _ _ _)
end Shrink
end TauCeti
