/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions

/-!
# A subset as a subspace of a larger subspace

If `s ⊆ t` are subsets of a topological space `X`, then `s` is homeomorphic to its preimage
`t ↓∩ s` under the inclusion `t → X`. This file upgrades Mathlib's
`Equiv.subtypeSubtypeEquivSubtype` to this homeomorphism.

## Main definitions

* `Homeomorph.preimageVal`: the homeomorphism `s ≃ₜ t ↓∩ s` for `s ⊆ t`.
-/

public section

open Topology

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X]

/-- A subset `s ⊆ t` is homeomorphic to its preimage in the subspace `t`. This is the
homeomorphism underlying the inverse of Mathlib's `Equiv.subtypeSubtypeEquivSubtype`. -/
def preimageVal {s t : Set X} (h : s ⊆ t) : s ≃ₜ ((↑) : t → X) ⁻¹' s where
  toEquiv := (Equiv.subtypeSubtypeEquivSubtype fun hx ↦ h hx).symm
  continuous_toFun := (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).continuous_iff.2 <|
    continuous_subtype_val.congr fun a ↦
      (Equiv.subtypeSubtypeEquivSubtype_symm_apply_coe_coe (fun hx ↦ h hx) a).symm
  continuous_invFun := IsEmbedding.subtypeVal.continuous_iff.2 <|
    (continuous_subtype_val.comp continuous_subtype_val).congr fun a ↦
      (Equiv.subtypeSubtypeEquivSubtype_apply_coe (fun hx ↦ h hx) a).symm

/-- `Homeomorph.preimageVal` does not move points of `X`. -/
@[simp]
theorem coe_preimageVal_apply {s t : Set X} (h : s ⊆ t) (a : s) :
    ((preimageVal h a : t) : X) = a :=
  Equiv.subtypeSubtypeEquivSubtype_symm_apply_coe_coe (fun hx ↦ h hx) a

/-- The inverse of `Homeomorph.preimageVal` does not move points of `X`. -/
@[simp]
theorem coe_preimageVal_symm_apply {s t : Set X} (h : s ⊆ t) (a : ((↑) : t → X) ⁻¹' s) :
    ((preimageVal h).symm a : X) = a :=
  Equiv.subtypeSubtypeEquivSubtype_apply_coe (fun hx ↦ h hx) a

end Homeomorph
