/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Prime avoidance for a coset of an ideal

Mathlib's `Ideal.subset_union_prime` is prime avoidance for an ideal: an ideal contained in a
finite union of primes is contained in one of them. This file proves the version for a coset
`a + I` of an ideal, due to Davis: if no prime `p` of a finite family contains both `a` and `I`,
then some element of `a + I` lies outside every `p`.

It is the step used to move an element of a unimodular row outside every minimal prime of a
noetherian ring by elementary operations, which drives Bass's bound on the stable range of a
commutative noetherian ring by its Krull dimension.

## Main results

* `Ideal.exists_mem_forall_add_notMem`: coset prime avoidance.

## References

* I. Kaplansky, *Commutative Rings*, revised edition, University of Chicago Press (1974),
  Theorem 124.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- **Prime avoidance for a coset** (Davis). Let `S` be a finite set of prime ideals of a
commutative ring, `I` an ideal and `a` an element such that no `p ∈ S` contains both `a` and `I`.
Then some element `a + y` of the coset `a + I` lies outside every `p ∈ S`. -/
theorem exists_mem_forall_add_notMem {S : Set (Ideal R)} (hS : S.Finite)
    (hSp : ∀ p ∈ S, p.IsPrime) {I : Ideal R} {a : R} (h : ∀ p ∈ S, a ∈ p → ¬I ≤ p) :
    ∃ y ∈ I, ∀ p ∈ S, a + y ∉ p := by
  classical
  -- It suffices to avoid the maximal members of `S`, which are pairwise incomparable. Split them
  -- into those that contain `a` (`A`) and those that do not (`B`).
  have hM : {p | Maximal (· ∈ S) p}.Finite := hS.subset fun _ hp ↦ hp.prop
  set A := hM.toFinset.filter (a ∈ ·)
  set B := hM.toFinset.filter (a ∉ ·)
  -- Some `y ∈ I` lies in every member of `B` and outside every member of `A`: otherwise prime
  -- avoidance puts `I ⊓ ⨅ B` inside some `p ∈ A`, so `p` contains `I` or a member of `B`.
  have hJ : ¬∃ p ∈ A, I ⊓ B.inf id ≤ id p := by
    rintro ⟨p, hpA, hp⟩
    obtain ⟨hpM, hap⟩ := Finset.mem_filter.mp hpA
    have hpM := hM.mem_toFinset.mp hpM
    rcases (hSp p hpM.prop).inf_le.mp hp with hIp | hBp
    · exact h p hpM.prop hap hIp
    obtain ⟨q, hqB, hqp⟩ := (hSp p hpM.prop).inf_le'.mp hBp
    obtain ⟨hqM, haq⟩ := Finset.mem_filter.mp hqB
    exact haq ((hM.mem_toFinset.mp hqM).2 hpM.prop hqp hap)
  rw [← subset_union_prime (f := id) ⊤ ⊤
    fun p hp _ _ ↦ hSp p (hM.mem_toFinset.mp (Finset.mem_filter.mp hp).1).prop] at hJ
  obtain ⟨y, ⟨hyI, hyB⟩, hyA⟩ := Set.not_subset.mp hJ
  simp only [Set.mem_iUnion, id, SetLike.mem_coe, not_exists] at hyA
  refine ⟨y, hyI, fun p hp hayp ↦ ?_⟩
  obtain ⟨m, hpm, hm⟩ := hS.exists_le_maximal hp
  have hmM : m ∈ hM.toFinset := hM.mem_toFinset.mpr hm
  by_cases ham : a ∈ m
  · exact hyA m (Finset.mem_filter.mpr ⟨hmM, ham⟩) ((m.add_mem_iff_right ham).mp (hpm hayp))
  · exact ham ((m.add_mem_iff_left (Submodule.mem_finsetInf.mp hyB m
      (Finset.mem_filter.mpr ⟨hmM, ham⟩))).mp (hpm hayp))

end Ideal
