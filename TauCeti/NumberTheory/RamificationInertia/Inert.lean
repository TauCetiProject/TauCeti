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

When exactly one prime `Q` of `S` lies over an ideal `P` of `R` and `Q` is unramified over `P`,
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
of `S` lying over the ideal `P` of `R` and `Q` is unramified over `P`, then its inertia degree is
the rank of `S` over `R`. -/
theorem inertiaDeg_eq_finrank_of_ncard_primesOver_eq_one [IsDomain R] [Module.Finite R S]
    [Module.Flat R S] (P : Ideal R) (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P]
    (huniq : (P.primesOver S).ncard = 1) (he : Q.ramificationIdx R = 1) :
    Q.inertiaDeg R = finrank R S := by
  have : P.IsPrime := isPrime_of_liesOver Q P
  have := (Algebra.QuasiFinite.finite_primesOver (S := S) P).fintype
  have : Subsingleton (P.primesOver S) :=
    (Set.ncard_le_one_iff_subsingleton.mp huniq.le).coe_sort
  have hsum := sum_ramification_inertia_eq_finrank P S
  rwa [Fintype.sum_subsingleton _ ⟨Q, inferInstance, inferInstance⟩, he, one_mul] at hsum

/-- **The single unramified prime above `P` is `P S`.** If `Q` is the only prime of `S` lying
over the ideal `P` of `R` and `Q` is unramified over `P`, then `P S = Q`. -/
theorem map_eq_of_ncard_primesOver_eq_one [IsDomain R] [IsDedekindDomain S]
    [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] (P : Ideal R) (Q : Ideal S) [Q.IsPrime]
    [Q.LiesOver P] (huniq : (P.primesOver S).ncard = 1) (he : Q.ramificationIdx R = 1) :
    P.map (algebraMap R S) = Q := by
  rcases eq_or_ne P ⊥ with rfl | hP
  · rw [Ideal.map_bot, eq_bot_of_liesOver_bot R Q]
  have : Q.IsMaximal := IsPrime.isMaximal ‹_› (ne_bot_of_liesOver_of_ne_bot hP Q)
  have : P.IsMaximal := IsMaximal.of_isMaximal_liesOver Q P
  obtain ⟨Q', hQ'⟩ := Set.ncard_eq_one.mp huniq
  have hQ : Q ∈ P.primesOver S := ⟨inferInstance, inferInstance⟩
  obtain rfl : Q = Q' := Set.mem_singleton_iff.mp (hQ' ▸ hQ)
  simp [map_algebraMap_eq_finsetProd_pow hP, hQ', he]

end TauCeti.RamificationInertia
