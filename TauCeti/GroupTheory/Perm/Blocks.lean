/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Order.LatticeIntervals

/-!
# Primitive actions from extremal blocks

For a transitive group action, the blocks containing a chosen point are order-isomorphic to the
subgroups containing its stabilizer. This file applies that correspondence at the two ends of the
block lattice.

A minimal non-singleton block gives a primitive action of its setwise stabilizer on the block.
A maximal proper block gives a maximal subgroup of the original group, and hence a primitive
action of the original group on the translates of the block. These are different actions: the
first resolves the action inside one block, while the second passes to the induced block system.

## Main results

* `MulAction.IsBlock.isAtom_iff_stabilizer_covBy`: atomicity of a block is equivalent to its
  stabilizer covering the point stabilizer.
* `MulAction.IsBlock.isPreprimitive_stabilizer_of_isAtom`: the stabilizer of an atomic block acts
  primitively on that block.
* `MulAction.IsBlock.isCoatom_iff_isCoatom_stabilizer`: a block is coatomic exactly when its
  stabilizer is a maximal subgroup.
* `MulAction.IsBlock.isPreprimitive_orbit_of_isCoatom`: the action on the translates of a
  coatomic block is primitive.

## References

* H. Wielandt, *Finite Permutation Groups*, Theorem 7.5.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, Theorem 1.5A.
-/

public section

namespace TauCeti

open scoped Pointwise

open MulAction

variable {G X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]
  {B : Set X} {a : X}

/-- A block `B` containing `a` is an atom in the block lattice exactly when its setwise stabilizer
covers the point stabilizer of `a`. -/
theorem _root_.MulAction.IsBlock.isAtom_iff_stabilizer_covBy
    (hB : IsBlock G B) (ha : a ∈ B) :
    IsAtom (⟨B, ha, hB⟩ : BlockMem G a) ↔
      stabilizer G a ⋖ stabilizer G B := by
  rw [covBy_iff_atom_Ici (hB.stabilizer_le ha)]
  exact (OrderIso.isAtom_iff (block_stabilizerOrderIso G a) ⟨B, ha, hB⟩).symm

/-- If `B` is a minimal non-singleton block containing `a`, then the setwise stabilizer of `B`
acts primitively on `B`.

Minimality is expressed by saying that `B` is an atom of `MulAction.BlockMem G a`. The bottom
element of this order is the singleton `{a}`, so atomicity also supplies the nontriviality of the
type `B` required by the point-stabilizer criterion for primitivity. -/
theorem _root_.MulAction.IsBlock.isPreprimitive_stabilizer_of_isAtom
    (hB : IsBlock G B) (ha : a ∈ B)
    (hmin : IsAtom (⟨B, ha, hB⟩ : BlockMem G a)) :
    IsPreprimitive (stabilizer G B) B := by
  have hstab_le : stabilizer G a ≤ stabilizer G B := hB.stabilizer_le ha
  have hcover : stabilizer G a ⋖ stabilizer G B :=
    (hB.isAtom_iff_stabilizer_covBy ha).mp hmin
  have hcoatom_Iic : IsCoatom
      (⟨stabilizer G a, hstab_le⟩ : Set.Iic (stabilizer G B)) :=
    (covBy_iff_coatom_Iic hcover.le).mp hcover
  let _ : OrderTop { H' : Subgroup G // H' ≤ stabilizer G B } := Set.Iic.orderTop
  have hcoatom : IsCoatom ((stabilizer G a).subgroupOf (stabilizer G B)) :=
    (OrderIso.isCoatom_iff (Subgroup.MapSubtype.orderIso (stabilizer G B)).symm _).mpr
      hcoatom_Iic
  have hB_ne : B ≠ {a} := by
    intro h
    apply hmin.ne_bot
    apply Subtype.ext
    rw [BlockMem.coe_bot]
    exact h
  let _ : Nontrivial B :=
    Set.Nontrivial.coe_sort ((Set.nontrivial_iff_ne_singleton ha).2 hB_ne)
  -- `B` is the orbit of `a` under `stabilizer G B`, so the action on `B` is transitive because
  -- the action on an orbit is; the two carriers differ only by the identification of the sets.
  let f : orbit (stabilizer G B) a →[stabilizer G B] (B : Set X) :=
    { toFun := fun x ↦ ⟨x, (hB.orbit_stabilizer_eq ha).subset x.2⟩
      map_smul' := fun _ _ ↦ rfl }
  let _ : IsPretransitive (stabilizer G B) B :=
    IsPretransitive.of_surjective_map (f := f)
      (fun y ↦ ⟨⟨y, (hB.orbit_stabilizer_eq ha).symm.subset y.2⟩, rfl⟩) inferInstance
  rw [← isCoatom_stabilizer_iff_preprimitive (stabilizer G B) ⟨a, ha⟩]
  convert hcoatom using 1
  ext g
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_stabilizer_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- A block `B` containing `a` is a coatom in the block lattice exactly when its setwise
stabilizer is a maximal subgroup of `G`. -/
theorem _root_.MulAction.IsBlock.isCoatom_iff_isCoatom_stabilizer
    (hB : IsBlock G B) (ha : a ∈ B) :
    IsCoatom (⟨B, ha, hB⟩ : BlockMem G a) ↔
      IsCoatom (stabilizer G B) := by
  constructor
  · intro hmax
    have himage : IsCoatom
        (block_stabilizerOrderIso G a ⟨B, ha, hB⟩) :=
      (OrderIso.isCoatom_iff (block_stabilizerOrderIso G a) _).mpr hmax
    exact IsCoatom.of_isCoatom_coe_Ici himage
  · intro hmax
    apply (OrderIso.isCoatom_iff (block_stabilizerOrderIso G a) _).mp
    exact hmax.Ici (hB.stabilizer_le ha)

/-- If `B` is a maximal proper block containing `a`, then `G` acts primitively on the block
system formed by the translates of `B`.

The carrier of this action is the orbit of `B` for the pointwise action of `G` on `Set X`; its
elements are exactly the sets `g • B`. -/
theorem _root_.MulAction.IsBlock.isPreprimitive_orbit_of_isCoatom
    (hB : IsBlock G B) (ha : a ∈ B)
    (hmax : IsCoatom (⟨B, ha, hB⟩ : BlockMem G a)) :
    IsPreprimitive G (orbit G B) := by
  let b : orbit G B := ⟨B, mem_orbit_self B⟩
  have hcoatom : IsCoatom (stabilizer G B) :=
    (hB.isCoatom_iff_isCoatom_stabilizer ha).mp hmax
  have horbit_nontrivial : (orbit G B).Nontrivial := by
    rw [← Set.not_subsingleton_iff]
    intro hsub
    apply hcoatom.ne_top
    rw [eq_top_iff]
    intro g _
    rw [mem_stabilizer_iff]
    exact (subsingleton_orbit_iff_mem_fixedPoints.mp hsub) g
  let _ : Nontrivial (orbit G B) :=
    Set.Nontrivial.coe_sort horbit_nontrivial
  rw [← isCoatom_stabilizer_iff_preprimitive G b]
  convert hcoatom using 1
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end TauCeti
