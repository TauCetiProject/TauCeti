/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Inversion sets in a Weyl group

Relative to a base of a root pairing, the inversion set of a Weyl-group element consists of the
positive roots that it sends to negative roots. This file gives the set-theoretic API for inversion
sets and computes the inversion set of the identity and of a simple reflection.

These computations are the base cases for the root-level exchange step and the later identification
of Coxeter length with the number of inversions.

An inversion set and its complement in the positive roots are both closed under root addition. For
the left action of `w` on roots, `inversions P b w⁻¹` and its complement are the positive roots
`β` with `w⁻¹ β` negative, respectively positive. They index the root directions of the two
complementary intersections `U⁺ ∩ w U⁻ w⁻¹` and `U⁺ ∩ w U⁺ w⁻¹` used as coordinates on Bruhat
cells; closedness under root addition is the combinatorial condition for a set of positive roots
to be the set of roots of a subgroup of `U⁺` normalized by the torus.

## Main definitions and results

* `TauCeti.inversions` is the set of positive roots sent to negative roots.
* `TauCeti.inversions_one` computes the inversion set of the identity.
* `TauCeti.inversions_ofIdx` computes the inversion set of a simple reflection.
* `TauCeti.add_mem_inversions` and `TauCeti.add_mem_posRoots_sdiff_inversions`: an inversion set
  and its complement in the positive roots are closed under root addition.
* `TauCeti.mem_inversions_or_mem_inversions_of_add_mem`: an inversion that is a sum of two positive
  roots has an inversion among its summands.
* `TauCeti.weylGroupToPerm_mem_posRoots_sdiff_inversions_inv_iff` and
  `TauCeti.neg_weylGroupToPerm_mem_inversions_inv_iff`: `w` carries the positive roots it keeps
  positive onto those that `w⁻¹` keeps positive, and, followed by negation, its inversions onto
  the inversions of `w⁻¹`.
* `TauCeti.inversionsFinset`: the inversion set as a finset. Sums and products over it and over
  its complement in the positive roots are reindexed along `w` by
  `TauCeti.sum_inversionsFinset_comp_neg_weylGroupToPerm` and
  `TauCeti.sum_posRootsFinset_sdiff_inversionsFinset_comp_weylGroupToPerm`, and their product
  forms.
* `TauCeti.image_root_inversions` identifies index-level inversions with vector roots.
* `TauCeti.ncard_inversions_eq_ncard_vector_inversions` identifies their cardinalities.

## References

This file implements the inversion-set part of Layer 1 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The mathematical convention follows
Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6.
-/

public section

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [CharZero R]

/-- The inversion set of `w`: the positive root indices that `w` sends to negative roots. -/
def inversions (b : P.Base) (w : P.weylGroup) : Set ι :=
  {i | b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm w i)}

variable (b : P.Base) (w : P.weylGroup)

/-- Membership in an inversion set means being positive and having negative image. -/
@[simp]
lemma mem_inversions (i : ι) :
    i ∈ inversions P b w ↔ b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm w i) :=
  Iff.rfl

/-- An inversion set is the intersection of the positive roots with the preimage of the negative
roots. -/
lemma inversions_eq_inter_preimage :
    inversions P b w =
      posRoots P b ∩ (P.weylGroupToPerm w) ⁻¹' negRoots P b := by
  ext i
  simp only [mem_inversions, Set.mem_inter_iff, mem_posRoots, Set.mem_preimage,
    mem_negRoots]

/-- Every inversion is a positive root. -/
lemma inversions_subset_posRoots : inversions P b w ⊆ posRoots P b := by
  intro i hi
  exact (mem_posRoots P b i).mpr hi.1

/-- The image of every inversion is a negative root. -/
lemma mapsTo_inversions_negRoots :
    MapsTo (P.weylGroupToPerm w) (inversions P b w) (negRoots P b) := by
  intro i hi
  exact (mem_negRoots P b _).mpr hi.2

/-- An element has no inversions exactly when it sends every positive root to a positive root. -/
theorem inversions_eq_empty_iff :
    inversions P b w = ∅ ↔
      MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b) := by
  constructor
  · intro h i hi
    by_contra hwi
    have : i ∈ inversions P b w :=
      ⟨(mem_posRoots P b i).mp hi, (mem_posRoots P b _).not.mp hwi⟩
    rw [h] at this
    exact this
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro i hi
    exact hi.2 ((mem_posRoots P b _).mp (h ((mem_posRoots P b i).mpr hi.1)))

/-- Every positive root is an inversion exactly when all positive roots are sent to
negative roots. -/
theorem inversions_eq_posRoots_iff :
    inversions P b w = posRoots P b ↔
      MapsTo (P.weylGroupToPerm w) (posRoots P b) (negRoots P b) := by
  constructor
  · intro h i hi
    apply mapsTo_inversions_negRoots P b w
    rw [h]
    exact hi
  · intro h
    apply Set.Subset.antisymm (inversions_subset_posRoots P b w)
    intro i hi
    refine ⟨(mem_posRoots P b i).mp hi, ?_⟩
    exact (mem_negRoots P b _).mp (h hi)

/-- A positive root lies outside the inversion set exactly when its image is again positive. -/
lemma mem_posRoots_sdiff_inversions (i : ι) :
    i ∈ posRoots P b \ inversions P b w ↔ b.IsPos i ∧ b.IsPos (P.weylGroupToPerm w i) := by
  simp only [Set.mem_sdiff, mem_posRoots, mem_inversions, not_and, not_not]
  exact ⟨fun h ↦ ⟨h.1, h.2 h.1⟩, fun h ↦ ⟨h.1, fun _ ↦ h.2⟩⟩

/-- **Inversion sets are closed under root addition**: a root that is the sum of two inversions
of `w` is again an inversion of `w`. -/
theorem add_mem_inversions {i j k : ι} (hi : i ∈ inversions P b w) (hj : j ∈ inversions P b w)
    (hk : P.root k = P.root i + P.root j) : k ∈ inversions P b w :=
  ⟨hi.1.add hj.1 hk, fun hpos ↦ hi.2 (by
    -- The image of `k` is the sum of the images of `i` and `j`, both negative.
    have hneg := add_mem_negRoots P b ((mem_negRoots P b _).mpr hi.2)
      ((mem_negRoots P b _).mpr hj.2) (P.root_weylGroupToPerm_eq_add w hk)
    exact absurd hpos ((mem_negRoots P b _).mp hneg))⟩

/-- **The positive roots outside an inversion set are closed under root addition**: a root that is
the sum of two positive roots kept positive by `w` is itself positive and kept positive by `w`. -/
theorem add_mem_posRoots_sdiff_inversions {i j k : ι} (hi : i ∈ posRoots P b \ inversions P b w)
    (hj : j ∈ posRoots P b \ inversions P b w) (hk : P.root k = P.root i + P.root j) :
    k ∈ posRoots P b \ inversions P b w := by
  rw [mem_posRoots_sdiff_inversions] at hi hj ⊢
  exact ⟨hi.1.add hj.1 hk, hi.2.add hj.2 (P.root_weylGroupToPerm_eq_add w hk)⟩

/-- **Inversion sets are coclosed**: if a sum of two positive roots is an inversion of `w`, then
one of the two summands is an inversion of `w`. -/
theorem mem_inversions_or_mem_inversions_of_add_mem {i j k : ι} (hi : b.IsPos i)
    (hj : b.IsPos j) (hk : P.root k = P.root i + P.root j) (hkw : k ∈ inversions P b w) :
    i ∈ inversions P b w ∨ j ∈ inversions P b w := by
  by_contra! h
  have hdiff := add_mem_posRoots_sdiff_inversions P b w ⟨(mem_posRoots P b i).mpr hi, h.1⟩
    ⟨(mem_posRoots P b j).mpr hj, h.2⟩ hk
  exact hdiff.2 hkw

/-- The number of inversions is at most the number of positive roots. -/
lemma ncard_inversions_le [Finite ι] :
    (inversions P b w).ncard ≤ (posRoots P b).ncard :=
  Set.ncard_le_ncard (inversions_subset_posRoots P b w) (posRoots_finite P b)

/-- The identity Weyl-group element has no inversions. -/
@[simp]
theorem inversions_one : inversions P b 1 = ∅ := by
  ext i
  simp

/-- The number of inversions of the identity is zero. -/
lemma ncard_inversions_one : (inversions P b 1).ncard = 0 := by
  rw [inversions_one, Set.ncard_empty]

/-! ### `w` and `w⁻¹` -/

/-- `w` carries the positive roots that it keeps positive onto the positive roots that `w⁻¹`
keeps positive. -/
theorem weylGroupToPerm_mem_posRoots_sdiff_inversions_inv_iff (i : ι) :
    P.weylGroupToPerm w i ∈ posRoots P b \ inversions P b w⁻¹ ↔
      i ∈ posRoots P b \ inversions P b w := by
  rw [mem_posRoots_sdiff_inversions, mem_posRoots_sdiff_inversions, map_inv, Equiv.Perm.inv_def,
    Equiv.symm_apply_apply, and_comm]

/-- `w` followed by root negation carries the inversions of `w` onto the inversions of `w⁻¹`: a
positive root `α` with `w α` negative gives the positive root `-w α`, which `w⁻¹` sends to the
negative root `-α`. -/
theorem neg_weylGroupToPerm_mem_inversions_inv_iff (i : ι) :
    letI := P.indexNeg;
    -P.weylGroupToPerm w i ∈ inversions P b w⁻¹ ↔ i ∈ inversions P b w := by
  let := P.indexNeg
  rw [mem_inversions, mem_inversions, P.weylGroupToPerm_neg, map_inv, Equiv.Perm.inv_def,
    Equiv.symm_apply_apply, RootPairing.Base.IsPos.neg_iff_not,
    RootPairing.Base.IsPos.neg_iff_not, not_not, and_comm]

/-! ### The inversion set as a finset -/

section Finset

variable [Finite ι]

/-- The inversion set of `w` as a finset, so that it can be summed over. -/
noncomputable def inversionsFinset : Finset ι := (Set.toFinite (inversions P b w)).toFinset

@[simp]
lemma mem_inversionsFinset (i : ι) : i ∈ inversionsFinset P b w ↔ i ∈ inversions P b w :=
  Set.Finite.mem_toFinset _

@[simp, norm_cast]
lemma coe_inversionsFinset : (inversionsFinset P b w : Set ι) = inversions P b w :=
  Set.Finite.coe_toFinset _

/-- Counting the inversions as a finset agrees with counting them as a set. -/
lemma card_inversionsFinset : (inversionsFinset P b w).card = (inversions P b w).ncard :=
  (Set.ncard_eq_toFinset_card _ _).symm

/-- Every inversion is a positive root, at the level of finsets. -/
lemma inversionsFinset_subset_posRootsFinset : inversionsFinset P b w ⊆ posRootsFinset P b :=
  fun i hi ↦ (mem_posRootsFinset P b i).mpr
    (inversions_subset_posRoots P b w ((mem_inversionsFinset P b w i).mp hi))

/-- Reindexing a sum over the positive roots kept positive by `w` along `w`: they are carried onto
the positive roots kept positive by `w⁻¹`. -/
theorem sum_posRootsFinset_sdiff_inversionsFinset_comp_weylGroupToPerm [DecidableEq ι]
    {β : Type*} [AddCommMonoid β] (f : ι → β) :
    ∑ i ∈ posRootsFinset P b \ inversionsFinset P b w, f (P.weylGroupToPerm w i) =
      ∑ i ∈ posRootsFinset P b \ inversionsFinset P b w⁻¹, f i :=
  Finset.sum_equiv (P.weylGroupToPerm w) (fun i ↦ by
    simpa only [Finset.mem_sdiff, mem_posRootsFinset, mem_inversionsFinset, Set.mem_sdiff] using
      (weylGroupToPerm_mem_posRoots_sdiff_inversions_inv_iff P b w i).symm) fun _ _ ↦ rfl

/-- Reindexing a product over the positive roots kept positive by `w` along `w`: they are carried
onto the positive roots kept positive by `w⁻¹`. -/
theorem prod_posRootsFinset_sdiff_inversionsFinset_comp_weylGroupToPerm [DecidableEq ι]
    {β : Type*} [CommMonoid β] (f : ι → β) :
    ∏ i ∈ posRootsFinset P b \ inversionsFinset P b w, f (P.weylGroupToPerm w i) =
      ∏ i ∈ posRootsFinset P b \ inversionsFinset P b w⁻¹, f i :=
  Finset.prod_equiv (P.weylGroupToPerm w) (fun i ↦ by
    simpa only [Finset.mem_sdiff, mem_posRootsFinset, mem_inversionsFinset, Set.mem_sdiff] using
      (weylGroupToPerm_mem_posRoots_sdiff_inversions_inv_iff P b w i).symm) fun _ _ ↦ rfl

/-- Reindexing a sum over the inversions of `w` along `w` followed by root negation: they are
carried onto the inversions of `w⁻¹`. -/
theorem sum_inversionsFinset_comp_neg_weylGroupToPerm {β : Type*} [AddCommMonoid β]
    (f : ι → β) :
    letI := P.indexNeg;
    ∑ i ∈ inversionsFinset P b w, f (-P.weylGroupToPerm w i) =
      ∑ i ∈ inversionsFinset P b w⁻¹, f i := by
  let := P.indexNeg
  exact Finset.sum_equiv ((P.weylGroupToPerm w).trans (Equiv.neg ι)) (fun i ↦ by
    simpa only [mem_inversionsFinset, Equiv.trans_apply, Equiv.neg_apply] using
      (neg_weylGroupToPerm_mem_inversions_inv_iff P b w i).symm) fun _ _ ↦ rfl

/-- Reindexing a product over the inversions of `w` along `w` followed by root negation: they are
carried onto the inversions of `w⁻¹`. -/
theorem prod_inversionsFinset_comp_neg_weylGroupToPerm {β : Type*} [CommMonoid β]
    (f : ι → β) :
    letI := P.indexNeg;
    ∏ i ∈ inversionsFinset P b w, f (-P.weylGroupToPerm w i) =
      ∏ i ∈ inversionsFinset P b w⁻¹, f i := by
  let := P.indexNeg
  exact Finset.prod_equiv ((P.weylGroupToPerm w).trans (Equiv.neg ι)) (fun i ↦ by
    simpa only [mem_inversionsFinset, Equiv.trans_apply, Equiv.neg_apply] using
      (neg_weylGroupToPerm_mem_inversions_inv_iff P b w i).symm) fun _ _ ↦ rfl

end Finset

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- A simple reflection has exactly its defining simple root as an inversion. -/
@[simp]
theorem inversions_ofIdx {i : ι} (hi : i ∈ b.support) :
    inversions P b (RootPairing.weylGroup.ofIdx P i) = {i} := by
  ext j
  simp only [mem_inversions, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hj, hneg⟩
    by_contra hji
    exact hneg (hj.reflectionPerm hi hji)
  · rintro rfl
    refine ⟨b.isPos_of_mem_support hi, ?_⟩
    rw [RootPairing.weylGroupToPerm_ofIdx_apply, ← mem_negRoots,
      reflectionPerm_self_mem_negRoots_iff_mem_posRoots, mem_posRoots]
    exact b.isPos_of_mem_support hi

/-- A simple reflection has one inversion. -/
theorem ncard_inversions_ofIdx {i : ι} (hi : i ∈ b.support) :
    (inversions P b (RootPairing.weylGroup.ofIdx P i)).ncard = 1 := by
  rw [inversions_ofIdx P b hi, Set.ncard_singleton]

omit [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- Index-level inversions identify with the positive vector roots sent to negative vector roots. -/
theorem image_root_inversions :
    P.root '' inversions P b w =
      (P.root '' posRoots P b) ∩ {α | w • α ∈ P.root '' negRoots P b} := by
  ext α
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, (mem_posRoots P b i).mpr hi.1, rfl⟩, ?_⟩
    exact ⟨P.weylGroupToPerm w i, (mem_negRoots P b _).mpr hi.2,
      (P.weylGroup_apply_root w i).symm⟩
  · rintro ⟨⟨i, hi, rfl⟩, j, hj, hact⟩
    have hij : P.weylGroupToPerm w i = j :=
      P.root.injective ((P.weylGroup_apply_root w i).symm.trans hact.symm)
    refine ⟨i, ⟨(mem_posRoots P b i).mp hi, ?_⟩, rfl⟩
    rwa [hij, ← mem_negRoots P b j]

omit [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- The number of index-level inversions equals the number of vector-root inversions. -/
theorem ncard_inversions_eq_ncard_vector_inversions :
    (inversions P b w).ncard =
      ((P.root '' posRoots P b) ∩ {α | w • α ∈ P.root '' negRoots P b}).ncard := by
  rw [← image_root_inversions P b w, P.root.injective.injOn.ncard_image]

end TauCeti
