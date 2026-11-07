/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Complete splitting is trivial ramification and inertia

This file records the non-Galois counting criterion for primes in finite flat extensions of
domains: a prime has as many primes above it as the degree allows exactly when every one of them
is unramified with trivial residue extension.

The Galois form, where the count is compared with the order of the Galois group, is in
`TauCeti/NumberTheory/RamificationInertia/Galois.lean`. No Galois hypothesis is needed here:
the fundamental identity alone forces each summand `e * f` down to `1`.

## Main results

* `Ideal.ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank` — a maximal
  count of primes above `P` makes `e = f = 1` at each of them.
* `Ideal.ncard_primesOver_eq_finrank_iff_forall_ramificationIdx_eq_one_and_inertiaDeg_eq_one` —
  the count is maximal exactly when `e = f = 1` at every prime above `P`.
* `Ideal.bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank` —
  for `P` maximal, the same count makes the residue map `R ⧸ P → S ⧸ Q` bijective.

## Provenance

Built directly on Mathlib's fundamental identity for finite flat extensions of domains
(`Ideal.sum_ramification_inertia_eq_finrank`). The residue-field consequence additionally uses
Mathlib's identification of the inertia degree with the rank of the residue extension
(`Ideal.inertiaDeg_eq_of_isMaximal`) and its characterisation of rank-one algebras over a field
(`Algebra.finrank_eq_one_iff_bijective_algebraMap`).
-/

public section

open Ideal Module

namespace Ideal

/-- **A maximal count of primes above `P` forces `e = f = 1`.** If the number of primes of `S`
lying over a prime `P` of `R` equals the rank of `S` over `R`, then each such prime is unramified
over `P` and has trivial inertia degree. No Galois hypothesis is needed. -/
theorem ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Module.Flat R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S)
    [Q.IsPrime] [Q.LiesOver P] (hsplit : (P.primesOver S).ncard = finrank R S) :
    Q.ramificationIdx R = 1 ∧ Q.inertiaDeg R = 1 := by
  have := (Algebra.QuasiFinite.finite_primesOver (S := S) P).fintype
  have h := Ideal.sum_ramification_inertia_eq_finrank (S := S) P
  rw [← hsplit, Set.ncard_eq_toFinset_card', Set.toFinset_card, Fintype.card_eq_sum_ones] at h
  -- the fundamental identity writes the rank as `∑ e * f` over the primes above `P`; each
  -- summand is at least `1`, and their number already accounts for the whole rank
  exact mul_eq_one.mp ((Finset.sum_eq_sum_iff_of_le fun q _ ↦
    Nat.one_le_of_lt (Nat.mul_pos (ramificationIdx_pos R q.1) (inertiaDeg_pos q.1 R))).mp h.symm
    ⟨Q, ‹_›, ‹_›⟩ (Finset.mem_univ _)).symm

/-- **The count criterion for complete splitting.** The number of primes of `S` lying over a
prime `P` of `R` equals the rank of `S` over `R` exactly when every one of them has
ramification index and inertia degree `1`. No Galois hypothesis is needed: both directions are the
fundamental identity `∑ e * f = [S : R]`, a sum of positive terms indexed by those primes. -/
theorem ncard_primesOver_eq_finrank_iff_forall_ramificationIdx_eq_one_and_inertiaDeg_eq_one
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Module.Flat R S] (P : Ideal R) [P.IsPrime] :
    (P.primesOver S).ncard = finrank R S ↔
      ∀ Q ∈ P.primesOver S, Q.ramificationIdx R = 1 ∧ Q.inertiaDeg R = 1 := by
  refine ⟨fun h Q ⟨_, _⟩ ↦
    ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank P Q h,
    fun h ↦ ?_⟩
  have := (Algebra.QuasiFinite.finite_primesOver (S := S) P).fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank (p := P),
    Finset.sum_congr rfl fun q _ ↦ by rw [(h q.1 q.2).1, (h q.1 q.2).2, mul_one]]
  simp

/-- **A maximal count of primes above `P` makes the residue extension trivial.** If `P` is maximal
and the number of primes of `S` lying over `P` equals the rank of `S` over `R`, then the residue
map `R ⧸ P → S ⧸ Q` is bijective. No Galois hypothesis is needed. -/
theorem bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Module.Flat R S] (P : Ideal R) [P.IsMaximal] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P]
    (hsplit : (P.primesOver S).ncard = finrank R S) :
    Function.Bijective (algebraMap (R ⧸ P) (S ⧸ Q)) := by
  have : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q P
  let := Ideal.Quotient.field P
  rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap, ← inertiaDeg_eq_of_isMaximal P Q]
  exact (ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank P Q hsplit).2

end Ideal
