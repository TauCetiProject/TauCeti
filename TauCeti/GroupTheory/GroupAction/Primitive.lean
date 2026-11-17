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

This file records facts about primitive and quasi-primitive actions.

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

Finally, a block containing `a` is a union of stabilizer-`a` orbits. For a finite transitive
action covered by `a` and two such orbits, this gives primitivity when neither orbit size
plus one divides the degree; see Dixon–Mortimer, *Permutation Groups*, §1.5.

## Main results

* `MulAction.IsBlock.of_le`, `MulAction.IsPreprimitive.of_le`: blocks pass to smaller subgroups
  and primitivity to larger ones.
* `MulAction.IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot`: in a faithful
  quasi-primitive action, every nontrivial normal subgroup acts transitively.
* `MulAction.IsBlock.orbit_stabilizer_subset`: blocks are unions of point-stabilizer orbits.
* `MulAction.IsPreprimitive.of_two_orbit_stabilizer`: a divisibility criterion for primitivity
  of finite transitive actions covered by two non-base-point suborbits.
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

section Suborbits

variable {G X : Type*} [Group G] [MulAction G X]

/-- A block containing `a` contains the entire stabilizer-`a` orbit of each of its points. -/
theorem _root_.MulAction.IsBlock.orbit_stabilizer_subset {B : Set X} (hB : IsBlock G B)
    {a x : X} (ha : a ∈ B) (hx : x ∈ B) : orbit (stabilizer G a) x ⊆ B := by
  rintro y ⟨g, rfl⟩
  have hset := mem_stabilizer_iff.mp (hB.stabilizer_le ha g.property)
  simp only [Subgroup.smul_def]
  rw [← hset]
  exact Set.smul_mem_smul_set hx

/-- In a finite transitive action, a block contained in a base point together with one
stabilizer orbit is a singleton if the orbit size plus one does not divide the degree. -/
theorem _root_.MulAction.IsBlock.subsingleton_of_subset_insert_orbit_stabilizer
    [Finite X] [IsPretransitive G X]
    {B : Set X} (hB : IsBlock G B) {a b : X} (ha : a ∈ B)
    (hsub : B ⊆ insert a (orbit (stabilizer G a) b))
    (hb : ¬ (1 + (orbit (stabilizer G a) b).ncard) ∣ Nat.card X) : B.Subsingleton := by
  classical
  by_cases hbB : b ∈ B
  · have hset : B = insert a (orbit (stabilizer G a) b) :=
      hsub.antisymm (Set.insert_subset ha (hB.orbit_stabilizer_subset ha hbB))
    by_cases hab : a ∈ orbit (stabilizer G a) b
    · have hba : b = a := by
        obtain ⟨g, hg⟩ := mem_orbit_symm.mp hab
        simp only [Subgroup.smul_def] at hg
        exact hg.symm.trans (mem_stabilizer_iff.mp g.property)
      subst b
      apply Set.subsingleton_of_subset_singleton (a := a)
      intro x hx
      rcases hsub hx with rfl | ⟨g, rfl⟩
      · simp
      · simpa only [Subgroup.smul_def, Set.mem_singleton_iff] using
          mem_stabilizer_iff.mp g.property
    · have hdvd := hB.ncard_dvd_card ⟨a, ha⟩
      rw [hset, Set.ncard_insert_of_notMem hab, Nat.add_comm] at hdvd
      exact (hb hdvd).elim
  · apply Set.subsingleton_of_subset_singleton (a := a)
    intro x hx
    rcases hsub hx with rfl | hxb
    · simp
    · exact (hbB (hB.orbit_stabilizer_subset ha hx (mem_orbit_symm.mp hxb))).elim

/-- A finite transitive action covered by a base point and two stabilizer orbits is primitive
if adjoining the base point to either orbit gives a size that does not divide the degree.
The orbits need not be assumed distinct or nontrivial. -/
theorem _root_.MulAction.IsPreprimitive.of_two_orbit_stabilizer [Finite X]
    [IsPretransitive G X] (a b c : X)
    (hcover : ∀ x, x = a ∨ x ∈ orbit (stabilizer G a) b ∨ x ∈ orbit (stabilizer G a) c)
    (hb : ¬ (1 + (orbit (stabilizer G a) b).ncard) ∣ Nat.card X)
    (hc : ¬ (1 + (orbit (stabilizer G a) c).ncard) ∣ Nat.card X) :
    IsPreprimitive G X := by
  classical
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  by_cases hbB : b ∈ B
  · by_cases hcB : c ∈ B
    · right
      apply Set.eq_univ_of_forall
      intro x
      rcases hcover x with rfl | hx | hx
      · exact ha
      · exact hB.orbit_stabilizer_subset ha hbB hx
      · exact hB.orbit_stabilizer_subset ha hcB hx
    · left
      refine hB.subsingleton_of_subset_insert_orbit_stabilizer ha ?_ hb
      intro x hx
      rcases hcover x with rfl | hxb | hxc
      · simp
      · exact Set.mem_insert_of_mem a hxb
      · exact (hcB (hB.orbit_stabilizer_subset ha hx (mem_orbit_symm.mp hxc))).elim
  · left
    refine hB.subsingleton_of_subset_insert_orbit_stabilizer ha ?_ hc
    intro x hx
    rcases hcover x with rfl | hxb | hxc
    · simp
    · exact (hbB (hB.orbit_stabilizer_subset ha hx (mem_orbit_symm.mp hxb))).elim
    · exact Set.mem_insert_of_mem a hxc

end Suborbits

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
