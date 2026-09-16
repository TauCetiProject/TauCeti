/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Transporting permutation groups along an equivalence

An equivalence `e : α ≃ β` induces the group isomorphism `Equiv.permCongrHom e` from
`Equiv.Perm α` to `Equiv.Perm β`, and so carries a subgroup `G ≤ Equiv.Perm α` to the subgroup
`G.map e.permCongrHom.toMonoidHom ≤ Equiv.Perm β`. The two subgroups are the same permutation
group written in two numberings of the points. This file records that the invariants of a
permutation group which do not depend on the numbering are unchanged: containment in the
alternating group, transitivity, and primitivity. (The order is `Subgroup.card_map_of_injective`.)

The same invariants may also be read off the image of a permutation representation instead of
the acting group: an action of `G` on `α` and the action of the subgroup
`(MulAction.toPermHom G α).range` of `Equiv.Perm α` have the same orbits and the same blocks.

## Main results

* `Equiv.map_permCongrHom_le_alternatingGroup_iff`: transport preserves evenness.
* `Equiv.isPretransitive_map_permCongrHom_iff`: transport preserves transitivity.
* `Equiv.isPreprimitive_map_permCongrHom_iff`: transport preserves primitivity.
* `MulAction.isPretransitive_range_toPermHom_iff`, `MulAction.isPreprimitive_range_toPermHom_iff`:
  a group action and its image in the permutations are transitive, respectively primitive,
  together.
-/

public section

open Equiv MulAction

namespace Equiv

variable {α β : Type*}

/-- The equivalence `e`, read as an equivariant map from the permutation representation of `G`
to that of its transport. -/
private def permCongrHomMulActionHom (e : α ≃ β) (G : Subgroup (Perm α)) :
    α →ₑ[e.permCongrHom.subgroupMap G] β where
  toFun := e
  map_smul' g x := by simp [Subgroup.smul_def, Equiv.permCongrHom_coe]

/-- Transport along an equivalence preserves transitivity. -/
theorem isPretransitive_map_permCongrHom_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    IsPretransitive (G.map e.permCongrHom.toMonoidHom) β ↔ IsPretransitive G α :=
  (isPretransitive_congr (e.permCongrHom.subgroupMap G).surjective
    (f := permCongrHomMulActionHom e G) e.bijective).symm

/-- Transport along an equivalence preserves primitivity. -/
theorem isPreprimitive_map_permCongrHom_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    IsPreprimitive (G.map e.permCongrHom.toMonoidHom) β ↔ IsPreprimitive G α :=
  (isPreprimitive_congr (e.permCongrHom.subgroupMap G).surjective
    (f := permCongrHomMulActionHom e G) e.bijective).symm

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Transport along an equivalence preserves containment in the alternating group, since it
preserves the sign of every permutation. -/
theorem map_permCongrHom_le_alternatingGroup_iff (e : α ≃ β) (G : Subgroup (Perm α)) :
    G.map e.permCongrHom.toMonoidHom ≤ alternatingGroup β ↔ G ≤ alternatingGroup α := by
  simp [SetLike.le_def, Equiv.Perm.mem_alternatingGroup,
    Equiv.permCongrHom_coe, Equiv.Perm.sign_permCongr]

end Equiv

namespace MulAction

variable (G α : Type*) [Group G] [MulAction G α]

/-- The identity of `α`, read as an equivariant map from the action of `G` to the action of its
image in the permutations of `α`. -/
private def rangeToPermHomMulActionHom :
    α →ₑ[(toPermHom G α).rangeRestrict] α where
  toFun := id
  map_smul' _ _ := rfl

/-- A group action is transitive exactly when its image in the permutations is. -/
theorem isPretransitive_range_toPermHom_iff :
    IsPretransitive (toPermHom G α).range α ↔ IsPretransitive G α :=
  (isPretransitive_congr (toPermHom G α).rangeRestrict_surjective
    (f := rangeToPermHomMulActionHom G α) Function.bijective_id).symm

/-- A group action is primitive exactly when its image in the permutations is. -/
theorem isPreprimitive_range_toPermHom_iff :
    IsPreprimitive (toPermHom G α).range α ↔ IsPreprimitive G α :=
  (isPreprimitive_congr (toPermHom G α).rangeRestrict_surjective
    (f := rangeToPermHomMulActionHom G α) Function.bijective_id).symm

end MulAction
