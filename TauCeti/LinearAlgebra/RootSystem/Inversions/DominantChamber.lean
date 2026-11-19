/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# Inversions of a Weyl-group element that preserves dominance

A Weyl-group element carrying a weight interior to the dominant chamber back into the closed
dominant chamber sends no positive root to a negative root, so its inversion set is empty. Since an
element with an empty inversion set is the identity, such an element is the identity: the Weyl
group acts freely on the interior of the dominant chamber.

The same argument works when the coefficient ring `K` is not ordered but the simple coroots take
positive values in an ordered subring `S`, as for weights of a complex root system on which the
simple coroots take positive real values: every coroot then takes a nonzero value of `S`, and the
Weyl group acts freely on such weights.

## Main results

* `TauCeti.mapsTo_posRoots_of_smul_mem_dominantChamber`: such an element maps positive roots to
  positive roots.
* `TauCeti.inversions_eq_empty_of_smul_mem_dominantChamber` and
  `TauCeti.inversions_eq_empty_of_smul_eq_self`: its inversion set is empty.
* `TauCeti.eq_one_of_smul_mem_dominantChamber`: such an element is the identity.
* `TauCeti.eq_one_of_smul_eq_self_of_mem_openDominantChamber`: the Weyl group acts freely on the
  interior of the dominant chamber.
* `TauCeti.exists_pos_coroot'_eq_of_mem_posRoots`, `TauCeti.exists_neg_coroot'_eq_of_mem_negRoots`
  and `TauCeti.exists_ne_zero_coroot'_eq`: if the simple coroots take positive values of an ordered
  subring `S` on a weight, every positive, negative, or arbitrary coroot takes a positive, negative,
  or nonzero value of `S` there.
* `TauCeti.eq_one_of_smul_eq_self_of_coroot'_eq`: the Weyl group acts freely on such weights.

## References

This file proves the interior case of the uniqueness half of the statement that the closed dominant
chamber is a fundamental domain for the Weyl group: for a weight interior to the
dominant chamber the moving element is forced to be the identity, and the Weyl group acts freely
there. The general case, where a weight on a wall of the chamber is fixed by the reflection in that
wall and the moving element need not be the identity, is
`TauCeti/LinearAlgebra/RootSystem/FundamentalDomain.lean`. The proof rests on the chamber
definitions in `TauCeti/LinearAlgebra/RootSystem/Chamber.lean` and the identity criterion for
inversion sets in `TauCeti/LinearAlgebra/RootSystem/Inversions/StrongExchange.lean`. The argument
is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9,
Ch. III, §10.
-/

public section

open Set

namespace TauCeti

open RootPairing

universe u v w x

/-! ### Weights positive on the simple coroots with respect to an ordered subring -/

section Ordered

variable {ι K M N S : Type*} [CommRing K] [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N] (P : _root_.RootPairing ι K M N) (b : P.Base) [CharZero K] [IsDomain K] [Finite ι]
  [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced] [CommRing S] [PartialOrder S]
  [IsStrictOrderedRing S] [Algebra S K] {x : M}

/-- If every simple coroot takes a positive value of the ordered subring `S` on `x`, so does
every positive coroot. -/
theorem exists_pos_coroot'_eq_of_mem_posRoots
    (hx : ∀ j ∈ b.support, ∃ t : S, 0 < t ∧ P.coroot' j x = algebraMap S K t) {i : ι}
    (hi : i ∈ posRoots P b) : ∃ t : S, 0 < t ∧ P.coroot' i x = algebraMap S K t := by
  obtain ⟨f, ⟨j, hj, hfj⟩, hsum⟩ := exists_coroot'_eq_sum_nat_of_mem_posRoots P b hi
  choose! t ht hxt using hx
  refine ⟨∑ k ∈ b.support, (f k : S) * t k, Finset.sum_pos'
    (fun k hk ↦ by positivity [(ht k hk).le])
    ⟨j, hj, mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hfj) (ht j hj)⟩, ?_⟩
  rw [hsum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [LinearMap.smul_apply, hxt k hk, map_mul, map_natCast, smul_eq_mul]

/-- If every simple coroot takes a positive value of `S` on `x`, every negative coroot takes a
negative value of `S` on `x`. -/
theorem exists_neg_coroot'_eq_of_mem_negRoots
    (hx : ∀ j ∈ b.support, ∃ t : S, 0 < t ∧ P.coroot' j x = algebraMap S K t) {i : ι}
    (hi : i ∈ negRoots P b) : ∃ t : S, t < 0 ∧ P.coroot' i x = algebraMap S K t := by
  obtain ⟨t, ht, hxt⟩ := exists_pos_coroot'_eq_of_mem_posRoots P b hx
    ((reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b i).2 hi)
  refine ⟨-t, neg_neg_of_pos ht, ?_⟩
  rw [coroot'_reflectionPerm_self, LinearMap.neg_apply, neg_eq_iff_eq_neg] at hxt
  rw [hxt, map_neg]

/-- If every simple coroot takes a positive value of `S` on `x`, every coroot takes a nonzero
value of `S` on `x`. -/
theorem exists_ne_zero_coroot'_eq
    (hx : ∀ j ∈ b.support, ∃ t : S, 0 < t ∧ P.coroot' j x = algebraMap S K t) (i : ι) :
    ∃ t : S, t ≠ 0 ∧ P.coroot' i x = algebraMap S K t := by
  rcases mem_posRoots_or_mem_negRoots P b i with hi | hi
  · obtain ⟨t, ht, hxt⟩ := exists_pos_coroot'_eq_of_mem_posRoots P b hx hi
    exact ⟨t, ht.ne', hxt⟩
  · obtain ⟨t, ht, hxt⟩ := exists_neg_coroot'_eq_of_mem_negRoots P b hx hi
    exact ⟨t, ht.ne, hxt⟩

/-- **The Weyl group acts freely on the weights on which every simple coroot takes a positive value
of the ordered subring `S`**: a positive root moved to a negative root would change the sign of
the value of its coroot. -/
theorem eq_one_of_smul_eq_self_of_coroot'_eq [FaithfulSMul S K]
    (hx : ∀ j ∈ b.support, ∃ t : S, 0 < t ∧ P.coroot' j x = algebraMap S K t)
    {w : P.weylGroup} (hw : w • x = x) : w = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.2 fun h ↦ hne (eq_one_of_inversions_eq_empty h)
  rw [mem_inversions] at hi
  obtain ⟨t, ht, hxt⟩ := exists_pos_coroot'_eq_of_mem_posRoots P b hx ((mem_posRoots P b i).2 hi.1)
  obtain ⟨t', ht', hxt'⟩ := exists_neg_coroot'_eq_of_mem_negRoots P b hx
    ((mem_negRoots P b _).2 hi.2)
  have h := coroot'_weylGroupToPerm_smul P w i x
  rw [hw, hxt, hxt'] at h
  exact (ht'.trans ht).ne (FaithfulSMul.algebraMap_injective S K h)

end Ordered

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [LinearOrder R] [IsStrictOrderedRing R] (b : P.Base)

variable [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced] {x : M}

/-- A Weyl-group element carrying a weight interior to the dominant chamber back into the closed
dominant chamber keeps every positive root positive. -/
theorem mapsTo_posRoots_of_smul_mem_dominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x ∈ dominantChamber P b) :
    MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b) := by
  intro i hi
  by_contra hneg
  rw [not_mem_posRoots_iff_mem_negRoots] at hneg
  -- The coroot functional of the image at the moved weight is the coroot functional of the root
  -- at the original weight, hence positive.
  have h := coroot'_nonpos_of_mem_negRoots P b hw hneg
  rw [RootPairing.coroot'_weylGroupToPerm_smul] at h
  exact absurd h (not_le.mpr (coroot'_pos_of_mem_posRoots P b hx hi))

/-- **A Weyl-group element carrying a weight interior to the dominant chamber back into the closed
dominant chamber has no inversions.** -/
theorem inversions_eq_empty_of_smul_mem_dominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x ∈ dominantChamber P b) :
    inversions P b w = ∅ :=
  (inversions_eq_empty_iff P b w).mpr (mapsTo_posRoots_of_smul_mem_dominantChamber P b w hx hw)

/-- A Weyl-group element fixing a weight interior to the dominant chamber has no inversions. -/
theorem inversions_eq_empty_of_smul_eq_self (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x = x) :
    inversions P b w = ∅ :=
  inversions_eq_empty_of_smul_mem_dominantChamber P b w hx
    (by rw [hw]; exact openDominantChamber_subset_dominantChamber P b hx)

/-- **A Weyl-group element carrying a weight interior to the dominant chamber back into the closed
dominant chamber is the identity.** -/
theorem eq_one_of_smul_mem_dominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x ∈ dominantChamber P b) : w = 1 :=
  eq_one_of_inversions_eq_empty (inversions_eq_empty_of_smul_mem_dominantChamber P b w hx hw)

/-- **The Weyl group acts freely on the interior of the dominant chamber.** -/
theorem eq_one_of_smul_eq_self_of_mem_openDominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x = x) : w = 1 :=
  eq_one_of_smul_eq_self_of_coroot'_eq P b (S := R)
    (fun j hj ↦ ⟨_, (mem_openDominantChamber P b x).1 hx j hj, rfl⟩) hw

end TauCeti
