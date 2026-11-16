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

This file records facts about blocks, primitive actions and quasi-primitive actions.

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

* `MulAction.IsBlock.orbit_stabilizer_subset`,
  `MulAction.IsBlock.orbit_inf_stabilizer_subset`: a block containing a point contains every
  orbit of its point stabilizer that it meets, also for an acting subgroup.
* `MulAction.IsBlock.of_le`, `MulAction.IsPreprimitive.of_le`: blocks pass to smaller subgroups
  and primitivity to larger ones.
* `MulAction.IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot`: in a faithful
  quasi-primitive action, every nontrivial normal subgroup acts transitively.
* `TauCeti.MulAction.fixedPoints_stabilizer_eq_singleton`: a nontrivial point stabilizer in a
  faithful primitive action fixes exactly its base point.
* `TauCeti.MulAction.exists_mem_stabilizer_smul_ne`: such a stabilizer moves every other point.
* `MulAction.IsBlock.setOf_stabilizer_eq_of_normal`: for a normal subgroup `N`, the points with a
  given stabilizer in `N` form a block.
* `TauCeti.MulAction.fixedPoints_stabilizer_eq_singleton_of_normal`: in a faithful primitive
  action on a finite set, a nontrivial point stabilizer of a normal subgroup fixes exactly its
  base point.
-/

public section

open scoped Pointwise

namespace TauCeti.MulAction

open _root_.MulAction

section Blocks

variable {G X : Type*} [Group G] [MulAction G X] {B : Set X} {a x : X}

/-- A block containing `a` contains the orbit under the stabilizer of `a` of each of its points. -/
theorem _root_.MulAction.IsBlock.orbit_stabilizer_subset (hB : IsBlock G B)
    (ha : a ∈ B) (hx : x ∈ B) : orbit (stabilizer G a) x ⊆ B := by
  intro y hy
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hy
  rw [Subgroup.smul_def, ← mem_stabilizer_iff.mp (hB.stabilizer_le ha g.property)]
  exact Set.smul_mem_smul_set hx

/-- For a subgroup action, a block containing `a` contains each orbit of the intersection
of the acting subgroup with the ambient stabilizer of `a` that it meets. -/
theorem _root_.MulAction.IsBlock.orbit_inf_stabilizer_subset {H : Subgroup G}
    (hB : IsBlock H B) (ha : a ∈ B) (hx : x ∈ B) :
    orbit ↥(H ⊓ stabilizer G a) x ⊆ B := by
  intro y hy
  apply hB.orbit_stabilizer_subset ha hx
  -- Use the orbit-relation bridge to compare the two subgroup action types.
  rw [← stabilizer_subgroupOf H a, ← orbitRel_apply, orbitRel_subgroupOf, inf_comm]
  exact orbitRel_apply.mpr hy

/-- For a normal subgroup `N`, the points whose stabilizer in `N` is that of `a` form a block:
conjugation by `g` carries the stabilizer of `z` in `N` to the stabilizer of `g • z`. -/
theorem _root_.MulAction.IsBlock.setOf_stabilizer_eq_of_normal {N : Subgroup G} [N.Normal]
    (a : X) : IsBlock G {z : X | stabilizer N z = stabilizer N a} := by
  have hconj (g : G) (z : X) :
      stabilizer N (g • z) = (stabilizer N z).map (MulAut.conjNormal g).toMonoidHom := by
    ext n
    rw [Subgroup.mem_map_equiv, mem_stabilizer_iff, mem_stabilizer_iff, Subgroup.smul_def,
      Subgroup.smul_def, MulAut.conjNormal_symm_apply, mul_smul, mul_smul, inv_smul_eq_iff]
  rw [isBlock_iff_smul_eq_of_mem]
  intro g b hb hgb
  have hfix : (stabilizer N a).map (MulAut.conjNormal g).toMonoidHom = stabilizer N a :=
    calc (stabilizer N a).map (MulAut.conjNormal g).toMonoidHom
      _ = (stabilizer N b).map (MulAut.conjNormal g).toMonoidHom := by rw [Set.mem_ofPred.mp hb]
      _ = stabilizer N (g • b) := (hconj g b).symm
      _ = stabilizer N a := Set.mem_ofPred.mp hgb
  ext w
  rw [Set.mem_smul_set, Set.mem_ofPred]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hconj, Set.mem_ofPred.mp hz, hfix]
  · intro hw
    refine ⟨g⁻¹ • w, Set.mem_ofPred.mpr ?_, smul_inv_smul g w⟩
    apply Subgroup.map_injective (f := (MulAut.conjNormal g).toMonoidHom)
      (MulAut.conjNormal g).injective
    rw [← hconj, smul_inv_smul, hw, hfix]

end Blocks

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

/-- In a faithful primitive action on a finite set, let `N` be a normal subgroup. If some
nonidentity element of `N` fixes the point `a`, then the elements of `N` fixing `a` have no other
common fixed point. For `N = ⊤` this is `fixedPoints_stabilizer_eq_singleton`. -/
@[simp]
theorem fixedPoints_stabilizer_eq_singleton_of_normal [Finite X] {N : Subgroup G} [N.Normal]
    (a : X) (ha : stabilizer N a ≠ ⊥) : fixedPoints (stabilizer N a) X = {a} := by
  refine Set.Subset.antisymm (fun b hb ↦ ?_) (Set.singleton_subset_iff.mpr fun g ↦ g.property)
  have hN : N ≠ ⊥ := by
    rintro rfl
    exact ha (Subsingleton.elim _ _)
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot N hN
  have : Nonempty X := ⟨a⟩
  -- The stabilizers of `a` and of `b` in `N` have the same finite index, so they are equal.
  have hle : stabilizer N a ≤ stabilizer N b := fun n hn ↦ hb ⟨n, hn⟩
  have hindex : (stabilizer N a).relIndex (stabilizer N b) = 1 := by
    have hmul := Subgroup.relIndex_mul_index hle
    rw [index_stabilizer_of_transitive, index_stabilizer_of_transitive] at hmul
    exact (mul_eq_right₀ Nat.card_pos.ne').mp hmul
  have heq : stabilizer N b = stabilizer N a :=
    le_antisymm (Subgroup.relIndex_eq_one.mp hindex) hle
  -- The points with this stabilizer in `N` form a block containing `a` and `b`.
  rcases (IsBlock.setOf_stabilizer_eq_of_normal (N := N) a).subsingleton_or_eq_univ with hs | hu
  · exact hs (Set.mem_ofPred.mpr heq) (Set.mem_ofPred.mpr rfl)
  · -- The block is everything, so the stabilizer of `a` in `N` fixes every point.
    refine (ha ((Subgroup.eq_bot_iff_forall _).mpr fun n hn ↦ ?_)).elim
    refine FaithfulSMul.eq_of_smul_eq_smul (α := X) fun z ↦ ?_
    have hz : z ∈ {z : X | stabilizer N z = stabilizer N a} := hu ▸ Set.mem_univ z
    rw [Set.mem_ofPred] at hz
    rw [one_smul]
    exact (hz ▸ hn : n ∈ stabilizer N z)

end TauCeti.MulAction
