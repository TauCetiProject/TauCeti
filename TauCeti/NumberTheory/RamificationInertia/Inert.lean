/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# A single unramified prime above a prime

When exactly one prime `Q` of `S` lies over a prime `P` of `R` and `Q` is unramified over `P`,
the fundamental identity `∑ e f = [S : R]` collapses to `f = [S : R]`, and the factorisation of
`P S` into the primes over `P` collapses to `P S = Q`. This is the situation of an inert prime,
the opposite extreme to the complete splitting of
`TauCeti.NumberTheory.RamificationInertia.Splitting`.

## Main results

* `TauCeti.RamificationInertia.inertiaDeg_eq_finrank_of_ncard_primesOver_eq_one`: the single
  unramified prime above `P` has inertia degree `[S : R]`.
* `TauCeti.RamificationInertia.map_eq_of_ncard_primesOver_eq_one`: `P S` is that prime.
-/

public section

open Ideal Module

namespace TauCeti.RamificationInertia

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **The single unramified prime above `P` has full inertia degree.** If `Q` is the only prime
of `S` lying over the prime `P` of `R` and `Q` is unramified over `P`, then its inertia degree is
the rank of `S` over `R`. -/
theorem inertiaDeg_eq_finrank_of_ncard_primesOver_eq_one [IsDomain R] [Module.Finite R S]
    [Module.Flat R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P]
    (huniq : (P.primesOver S).ncard = 1) (he : Q.ramificationIdx R = 1) :
    Q.inertiaDeg R = finrank R S := by
  have hfin : Fintype (P.primesOver S) := (Algebra.QuasiFinite.finite_primesOver P).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (R := R) (S := S) (p := P)
  have hcard : Fintype.card (P.primesOver S) = 1 := by
    rw [← huniq, Set.ncard_eq_toFinset_card']
    simp
  have : Subsingleton (P.primesOver S) := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  rwa [Fintype.sum_subsingleton _ ⟨Q, ⟨inferInstance, inferInstance⟩⟩, he, one_mul] at hsum

/-- **The single unramified prime above `P` is `P S`.** If `Q` is the only prime of `S` lying
over the nonzero maximal ideal `P` of `R` and `Q` is unramified over `P`, then `P S = Q`. -/
theorem map_eq_of_ncard_primesOver_eq_one [IsDomain R] [IsDedekindDomain S]
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] (P : Ideal R) [P.IsMaximal] (hP : P ≠ 0)
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P] (huniq : (P.primesOver S).ncard = 1)
    (he : Q.ramificationIdx R = 1) : P.map (algebraMap R S) = Q := by
  classical
  have hQ : Q ∈ P.primesOver S := ⟨inferInstance, inferInstance⟩
  obtain ⟨Q', hQ'⟩ := Set.ncard_eq_one.mp huniq
  have hQQ : Q = Q' := by rw [hQ'] at hQ; exact hQ
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hP, Finset.prod_eq_single Q]
  · rw [he, pow_one]
  · intro P' hP' hPQ
    rw [Set.mem_toFinset, hQ'] at hP'
    exact absurd ((Set.mem_singleton_iff.mp hP').trans hQQ.symm) hPQ
  · intro hQn
    exact absurd (Set.mem_toFinset.mpr hQ) hQn

end TauCeti.RamificationInertia
