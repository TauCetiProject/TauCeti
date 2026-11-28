/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homeomorphisms that retype points of subspaces

This file records how Mathlib's `Homeomorph.setCongr`, the homeomorphism between the subtypes of
two equal sets, acts on points in both directions. It also identifies a subspace `t` of `X`
contained in `s` with the subspace `Subtype.val ⁻¹' t` of `s`.

## Main results

* `Homeomorph.setCongr_apply`: `setCongr` retypes a point without moving it.
* `Homeomorph.setCongr_symm_apply`: its inverse also retypes a point without moving it.
* `Homeomorph.Set.preimageVal`: for `t ⊆ s`, the subspace `Subtype.val ⁻¹' t` of `s` is
  homeomorphic to `t`.
-/

public section

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X]

/-- `Homeomorph.setCongr` retypes a point without moving it. This is the homeomorphism counterpart
of Mathlib's `Set.equivOfEq_apply`, which does not match through the homeomorphism constructor. -/
@[simp]
theorem setCongr_apply {s t : Set X} (h : s = t) (x : s) :
    setCongr h x = ⟨x, h ▸ x.property⟩ :=
  rfl

/-- The inverse of `Homeomorph.setCongr` retypes a point without moving it. This is the
homeomorphism counterpart of Mathlib's `Set.equivOfEq_symm_apply`. -/
@[simp]
theorem setCongr_symm_apply {s t : Set X} (h : s = t) (x : t) :
    (setCongr h).symm x = ⟨x, h.symm ▸ x.property⟩ :=
  rfl

/-- For `t ⊆ s`, the subspace `Subtype.val ⁻¹' t` of `s` is homeomorphic to `t`. This is the
homeomorphism counterpart of Mathlib's `Equiv.subtypeSubtypeEquivSubtype`. -/
def Set.preimageVal {s t : Set X} (h : t ⊆ s) : (Subtype.val ⁻¹' t : Set s) ≃ₜ t where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `Homeomorph.Set.preimageVal` forgets the larger set `s`. -/
@[simp]
theorem Set.preimageVal_apply {s t : Set X} (h : t ⊆ s) (x : (Subtype.val ⁻¹' t : Set s)) :
    Set.preimageVal h x = ⟨x.val.val, x.property⟩ :=
  (rfl)

/-- The inverse of `Homeomorph.Set.preimageVal` views a point of `t` as a point of `s`. -/
@[simp]
theorem Set.preimageVal_symm_apply {s t : Set X} (h : t ⊆ s) (x : t) :
    (Set.preimageVal h).symm x = ⟨⟨x.val, h x.property⟩, x.property⟩ :=
  (rfl)

end Homeomorph
