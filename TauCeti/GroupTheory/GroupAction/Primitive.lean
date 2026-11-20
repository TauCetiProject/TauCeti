/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import TauCeti.GroupTheory.GroupAction.FixingSubgroup
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.GroupTheory.GroupAction.Transitive

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

The fourth concerns the point stabilizer `N_x` of a normal subgroup `N` in a faithful primitive
action on a finite set.  A nontrivial `N_x` has no fixed point other than `x`.  It is normal in
the stabilizer `G_x` of `x` in the whole group, so on an orbit `O` of `G_x` on which `G_x` acts
quasi-primitively it is either trivial or transitive; the first case is excluded by the
fixed-point property, so `N_x` is transitive on `O` and the length of `O` divides its order.

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
* `TauCeti.MulAction.eq_of_normal_of_le_of_stabilizer_eq_bot`,
  `TauCeti.MulAction.eq_top_of_characteristic_of_stabilizer_eq_bot`: in a quasi-primitive action,
  a subgroup acting regularly contains no nontrivial normal subgroup of the whole group other
  than itself, so a regular normal subgroup is characteristically simple.
* `MulAction.IsBlock.setOf_stabilizer_eq_of_normal`: for a normal subgroup `N`, the points with a
  given stabilizer in `N` form a block.
* `TauCeti.MulAction.fixedPoints_stabilizer_eq_singleton_of_normal`: in a faithful primitive
  action on a finite set, a nontrivial point stabilizer of a normal subgroup fixes exactly its
  base point.
* `TauCeti.MulAction.isPretransitive_subgroupOf_stabilizer_orbit`: in a faithful primitive action
  on a finite set, a normal subgroup with a nontrivial stabilizer of `x` meets the stabilizer of
  `x` in a subgroup acting transitively on each of its quasi-primitive orbits.
* `TauCeti.MulAction.natCard_orbit_stabilizer_dvd_natCard_stabilizer_of_normal`: the length of
  such an orbit divides the order of the stabilizer of `x` in the normal subgroup.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, §1.5 and §1.6 (blocks, and normal subgroups
  of primitive groups), and §3.2 (orbits of the point stabilizer).
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

/-- For a normal subgroup `N`, the points whose stabilizer in `N` is that of `a` form a block. -/
theorem _root_.MulAction.IsBlock.setOf_stabilizer_eq_of_normal {N : Subgroup G} [N.Normal]
    (a : X) : IsBlock G {z : X | stabilizer N z = stabilizer N a} :=
  -- The preimage of a point under `z ↦ stabilizer N z`, which is equivariant along conjugation.
  (IsBlock.singleton (a := stabilizer N a)).preimage
    (⟨stabilizer N, stabilizer_smul_eq_conjNormal_smul⟩ :
      X →ₑ[(MulAut.conjNormal : G → MulAut N)] Subgroup N)

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

section Regular

variable {G X : Type*} [Group G] [MulAction G X] [IsQuasiPreprimitive G X]

/-- In a quasi-primitive action, let `N` be a subgroup with a trivial point stabilizer. Then a
nontrivial normal subgroup of the whole group that is contained in `N` is equal to `N`. -/
theorem eq_of_normal_of_le_of_stabilizer_eq_bot {N H : Subgroup G} [H.Normal] {x : X}
    (hx : stabilizer N x = ⊥) (hHN : H ≤ N) (hH : H ≠ ⊥) : H = N := by
  -- A nonidentity element of `H` lies in `N`, so it moves `x`; hence `H` is transitive.
  have : IsPretransitive H X := by
    refine IsQuasiPreprimitive.isPretransitive_of_normal fun hfix ↦ hH ?_
    refine (Subgroup.eq_bot_iff_forall _).mpr fun h hh ↦ ?_
    have hmem : (⟨h, hHN hh⟩ : N) ∈ stabilizer N x := by
      rw [mem_stabilizer_iff, Subgroup.mk_smul, ← Subgroup.mk_smul h hh]
      exact mem_fixedPoints.mp (hfix ▸ Set.mem_univ x) ⟨h, hh⟩
    rw [hx, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  refine le_antisymm hHN fun n hn ↦ ?_
  obtain ⟨⟨h, hh⟩, hhn⟩ := exists_smul_eq H x (n • x)
  -- The elements `h` and `n` of `N` move `x` to the same point, so they are equal.
  have hmem : (⟨h⁻¹ * n, N.mul_mem (N.inv_mem (hHN hh)) hn⟩ : N) ∈ stabilizer N x := by
    rw [mem_stabilizer_iff, Subgroup.mk_smul, mul_smul, inv_smul_eq_iff, ← hhn, Subgroup.mk_smul]
  rw [hx, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp (congrArg Subtype.val hmem) ▸ hh

/-- In a quasi-primitive action, a normal subgroup `N` with a trivial point stabilizer is
characteristically simple: every nontrivial characteristic subgroup `K` of `N` equals `⊤`. -/
theorem eq_top_of_characteristic_of_stabilizer_eq_bot {N : Subgroup G} [N.Normal] {x : X}
    (hx : stabilizer N x = ⊥) {K : Subgroup N} [K.Characteristic] (hK : K ≠ ⊥) : K = ⊤ := by
  have hmap : K.map N.subtype = N :=
    eq_of_normal_of_le_of_stabilizer_eq_bot hx (Subgroup.map_subtype_le K)
      (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective])
  apply Subgroup.map_injective N.subtype_injective
  rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Regular

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
  refine Set.Subset.antisymm (fun b hb ↦ ?_) (Set.singleton_subset_iff.mpr fun g ↦
    (Subgroup.smul_def g a).trans (mem_stabilizer_iff.mp g.property))
  have hN : N ≠ ⊥ := by
    rintro rfl
    exact ha (Subsingleton.elim _ _)
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot N hN
  have : Nonempty X := ⟨a⟩
  -- The stabilizers of `a` and of `b` in `N` have the same finite index, so they are equal.
  have hle : stabilizer N a ≤ stabilizer N b := fun n hn ↦
    mem_stabilizer_iff.mpr ((Subgroup.mk_smul n hn b).symm.trans (mem_fixedPoints.mp hb ⟨n, hn⟩))
  have : (stabilizer N b).FiniteIndex :=
    ⟨by rw [index_stabilizer_of_transitive]; exact Nat.card_pos.ne'⟩
  have heq : stabilizer N a = stabilizer N b :=
    Subgroup.eq_of_index_dvd_index hle
      (by rw [index_stabilizer_of_transitive, index_stabilizer_of_transitive])
  -- The points with this stabilizer in `N` form a block containing `a` and `b`.
  rcases (IsBlock.setOf_stabilizer_eq_of_normal (N := N) a).subsingleton_or_eq_univ with hs | hu
  · exact hs (Set.mem_ofPred.mpr heq.symm) (Set.mem_ofPred.mpr rfl)
  · -- The block is everything, so the stabilizer of `a` in `N` fixes every point.
    refine (fixedPoints_ne_univ_of_ne_bot (α := X) ha (Set.eq_univ_iff_forall.mpr fun z ↦
      mem_fixedPoints.mpr fun n ↦ ?_)).elim
    have hz : z ∈ {z : X | stabilizer N z = stabilizer N a} := hu ▸ Set.mem_univ z
    rw [Subgroup.smul_def, ← mem_stabilizer_iff, Set.mem_ofPred.mp hz]
    exact n.property

/-- In a faithful primitive action on a finite set, let the stabilizer of `x` act
quasi-primitively on its orbit `O` of `y`, and let `N` be a normal subgroup in which the
stabilizer of `x` is nontrivial. Then the elements of `N` fixing `x` act transitively on `O`. -/
theorem isPretransitive_subgroupOf_stabilizer_orbit [Finite X] {x : X} (y : X)
    [IsQuasiPreprimitive (stabilizer G x) (orbit (stabilizer G x) y)]
    {N : Subgroup G} [N.Normal] (hN : stabilizer N x ≠ ⊥) :
    IsPretransitive (N.subgroupOf (stabilizer G x)) (orbit (stabilizer G x) y) := by
  have hM : (N.subgroupOf (stabilizer G x)).Normal := Subgroup.Normal.subgroupOf ‹_› _
  by_cases hyx : y = x
  · -- The orbit of `x` under its own stabilizer is a single point.
    subst hyx
    have : Subsingleton (orbit (stabilizer G y) y) :=
      (subsingleton_orbit_iff_mem_fixedPoints.mpr (mem_fixedPoints.mpr fun g ↦
        (Subgroup.smul_def g y).trans (mem_stabilizer_iff.mp g.property))).coe_sort
    infer_instance
  -- Otherwise the elements of `N` fixing `x` would all fix `y`, a second fixed point.
  refine IsQuasiPreprimitive.isPretransitive_of_normal fun hfix ↦ hyx ?_
  have hmem : y ∈ fixedPoints (stabilizer N x) X := by
    refine mem_fixedPoints.mpr fun n ↦ ?_
    have hn : (n : G) ∈ stabilizer G x :=
      mem_stabilizer_iff.mpr ((Subgroup.smul_def (n : N) x).symm.trans
        (mem_stabilizer_iff.mp n.property))
    have hy := mem_fixedPoints.mp
      (hfix ▸ Set.mem_univ (⟨y, mem_orbit_self y⟩ : orbit (stabilizer G x) y))
      ⟨⟨n, hn⟩, Subgroup.mem_subgroupOf.mpr (n : N).property⟩
    rw [Subtype.ext_iff, Subgroup.smul_def, orbit.coe_smul, Subgroup.mk_smul] at hy
    rw [Subgroup.smul_def, Subgroup.smul_def]
    exact hy
  rwa [fixedPoints_stabilizer_eq_singleton_of_normal x hN, Set.mem_singleton_iff] at hmem

/-- In a faithful primitive action on a finite set, let the stabilizer of `x` act
quasi-primitively on its orbit of `y`, and let `N` be a normal subgroup in which the stabilizer
of `x` is nontrivial. Then the length of this orbit divides the order of the stabilizer of `x`
in `N`. -/
theorem natCard_orbit_stabilizer_dvd_natCard_stabilizer_of_normal [Finite X] {x : X} (y : X)
    [IsQuasiPreprimitive (stabilizer G x) (orbit (stabilizer G x) y)]
    {N : Subgroup G} [N.Normal] (hN : stabilizer N x ≠ ⊥) :
    Nat.card (orbit (stabilizer G x) y) ∣ Nat.card (stabilizer N x) := by
  have := isPretransitive_subgroupOf_stabilizer_orbit y hN
  have : Nonempty (orbit (stabilizer G x) y) := (nonempty_orbit y).to_subtype
  -- Both subgroups are copies of the intersection of `N` with the stabilizer of `x`.
  have hcard : Nat.card (N.subgroupOf (stabilizer G x)) = Nat.card (stabilizer N x) := by
    rw [← stabilizer_subgroupOf, ← Subgroup.inf_subgroupOf_right N,
      ← Subgroup.inf_subgroupOf_left (stabilizer G x) N]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  exact hcard ▸ natCard_dvd_natCard_of_isPretransitive (N.subgroupOf (stabilizer G x))

end TauCeti.MulAction
