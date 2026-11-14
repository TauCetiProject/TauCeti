/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Commuting nested subspace restrictions

Restricting a topological space `X` first to a subset `s` and then to the preimage of `t`, or first
to `t` and then to the preimage of `s`, yields canonically homeomorphic nested subspaces.

## Main definitions

* `Homeomorph.Set.subtypePreimageComm`: the homeomorphism
  `((Subtype.val : s → X) ⁻¹' t) ≃ₜ ((Subtype.val : t → X) ⁻¹' s)`.

## Main results

* `Homeomorph.Set.subtypePreimageComm_apply`: pointwise evaluation of `subtypePreimageComm`.
* `Homeomorph.Set.subtypePreimageComm_symm`: the inverse of `subtypePreimageComm s t` is
  `subtypePreimageComm t s`.
-/

public section

namespace Homeomorph.Set

variable {X : Type*} [TopologicalSpace X]

/-- Commuting the order of restriction to two subsets `s` and `t` of `X` gives a canonical
homeomorphism between the two nested subspaces. -/
def subtypePreimageComm (s t : Set X) :
    ((Subtype.val : s → X) ⁻¹' t) ≃ₜ ((Subtype.val : t → X) ⁻¹' s) where
  toFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Homeomorph.Set.subtypePreimageComm` retypes a nested-subspace point without moving its
underlying ambient point. -/
@[simp]
theorem subtypePreimageComm_apply (s t : Set X) (y : (Subtype.val : s → X) ⁻¹' t) :
    subtypePreimageComm s t y = ⟨⟨y.1.1, y.2⟩, y.1.2⟩ := by
  rfl

/-- Reversing `Homeomorph.Set.subtypePreimageComm s t` exchanges the two subsets `s` and `t`. -/
@[simp]
theorem subtypePreimageComm_symm (s t : Set X) :
    (subtypePreimageComm s t).symm = subtypePreimageComm t s := by
  rfl

end Homeomorph.Set

end
