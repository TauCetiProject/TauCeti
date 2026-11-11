/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import TauCeti.GroupTheory.GroupAction.FixingSubgroup

/-!
# Point stabilizers, larger acting groups, and transitive normal subgroups in primitive actions

This file records three small facts about primitive and quasi-primitive actions.

The first is the fixed-point property that distinguishes a nonregular primitive action from a
regular one.  In a faithful primitive action, a nontrivial point stabilizer fixes only its base
point.  Equivalently, it moves every other point.  This is the local ingredient in the
primitivity of the product action of a permutation wreath product: a stabilizer element can
change one coordinate of a tuple while leaving a constant tuple fixed.

The second is monotonicity in the acting subgroup.  A block for a subgroup is a block for every
smaller subgroup, so primitivity passes from a subgroup to every larger one.  This is how
primitivity of a transitive permutation group is inherited by the groups containing it.  (The
corresponding statement for transitivity is Mathlib's `MulAction.IsPretransitive.of_compHom`.)

The third is the transitivity of nontrivial normal subgroups.  In a faithful quasi-primitive
action a nontrivial subgroup moves some point, so Mathlib's quasi-primitivity makes every
nontrivial normal subgroup transitive.  This is the first step of the simplicity criteria in
`TauCeti.GroupTheory.GroupAction.Simple.Basic` and
`TauCeti.GroupTheory.GroupAction.Simple.Stabilizer`.

## Main results

* `MulAction.IsBlock.of_le`, `MulAction.IsPreprimitive.of_le`: blocks pass to smaller subgroups
  and primitivity to larger ones.
* `MulAction.IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot`: in a faithful
  quasi-primitive action, every nontrivial normal subgroup acts transitively.
* `TauCeti.MulAction.fixedPoints_stabilizer_eq_singleton`: a nontrivial point stabilizer in a
  faithful primitive action fixes exactly its base point.
* `TauCeti.MulAction.exists_mem_stabilizer_smul_ne`: such a stabilizer moves every other point.
-/

public section

open scoped Pointwise

namespace TauCeti.MulAction

open _root_.MulAction

section Enlarge

variable {G X : Type*} [Group G] [MulAction G X] {H K : Subgroup G}

/-- The identity of `X`, equivariant along the inclusion of a subgroup `H` into a larger
subgroup `K`. -/
private def inclusionMulActionHom (h : H ≤ K) : X →ₑ[Subgroup.inclusion h] X where
  toFun := id
  map_smul' _ _ := rfl

/-- A block for a subgroup is a block for every smaller subgroup. -/
theorem _root_.MulAction.IsBlock.of_le (h : H ≤ K) {B : Set X} (hB : IsBlock K B) :
    IsBlock H B :=
  hB.preimage (inclusionMulActionHom h)

/-- A subgroup acting primitively makes every larger subgroup act primitively. -/
theorem _root_.MulAction.IsPreprimitive.of_le (h : H ≤ K) [IsPreprimitive H X] :
    IsPreprimitive K X :=
  IsPreprimitive.of_surjective (f := inclusionMulActionHom h) Function.surjective_id

end Enlarge

section Normal

variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [IsQuasiPreprimitive G X]

/-- In a faithful quasi-primitive action, every nontrivial normal subgroup acts transitively: it
moves some point, so quasi-primitivity makes it transitive. -/
theorem _root_.MulAction.IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : IsPretransitive N X :=
  IsQuasiPreprimitive.isPretransitive_of_normal (fixedPoints_ne_univ_of_ne_bot hN)

end Normal

variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
  [IsPreprimitive G X]

/-- In a faithful primitive action, the fixed-point set of a nontrivial point stabilizer is the
singleton consisting of that point. -/
@[simp]
theorem fixedPoints_stabilizer_eq_singleton (a : X) (ha : stabilizer G a ≠ ⊥) :
    fixedPoints (stabilizer G a) X = {a} := by
  refine Set.Subset.antisymm (fun b hb ↦ ?_) (Set.singleton_subset_iff.mpr fun g ↦ g.property)
  -- By faithfulness, the nontrivial stabilizer moves some point; in particular `X` is nontrivial.
  have hfix := fixedPoints_ne_univ_of_ne_bot (α := X) ha
  have : Nontrivial X := nontrivial_of_fixedPoints_ne_univ hfix
  have hco := IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G a
  obtain ⟨g, rfl⟩ := exists_smul_eq G a b
  -- The stabilizer of `g • a` contains the maximal stabilizer of `a`, so the two are equal.
  have heq : stabilizer G (g • a) = stabilizer G a :=
    (hco.le_iff_eq (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G (g • a)).ne_top).mp
      fun h hh ↦ hb ⟨h, hh⟩
  -- Hence `g` normalizes the stabilizer of `a`. If `g` moved `a`, maximality would make the
  -- stabilizer normal, hence transitive by quasi-primitivity, although it fixes `a`.
  by_contra hga
  have : (stabilizer G a).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine hco.2 _ (IsConcreteLE.lt_iff_le_and_exists.mpr ⟨Subgroup.le_normalizer, g, ?_, hga⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    conv_rhs => rw [← heq]
    simp [mul_smul]
  obtain ⟨h, hh⟩ :=
    (IsQuasiPreprimitive.isPretransitive_of_normal hfix).exists_smul_eq a (g • a)
  exact hga (hh.symm.trans (mem_stabilizer_iff.mp h.property))

/-- A nontrivial point stabilizer in a faithful primitive action moves every other point. -/
theorem exists_mem_stabilizer_smul_ne (a : X) (ha : stabilizer G a ≠ ⊥) {b : X}
    (hab : b ≠ a) : ∃ g : G, g ∈ stabilizer G a ∧ g • b ≠ b := by
  have hb : b ∉ fixedPoints (stabilizer G a) X := by
    rwa [fixedPoints_stabilizer_eq_singleton a ha]
  simpa [mem_fixedPoints] using hb

end TauCeti.MulAction
