/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Length

/-!
# Maximal ideals over an ideal with semilocal quotient

The maximal ideals of a commutative ring `R` containing an ideal `𝔞` are the pullbacks of the
maximal ideals of `R ⧸ 𝔞`. So if the quotient `R ⧸ 𝔞` is semilocal (has only finitely many maximal
ideals), then `𝔞` lies in only finitely many maximal ideals of `R`. This applies for instance
when `R ⧸ 𝔞` is Artinian (`IsArtinianRing.setOfPred_isMaximal_finite`), in particular when it is
finite. It also applies to every nonzero ideal of a Noetherian ring of dimension at most one, such
as a Dedekind domain: the maximal ideals containing such an ideal are minimal primes over it, and a
Noetherian ring has only finitely many of those.

## Main results

* `Ideal.finite_setOfPred_isMaximal_and_le`: an ideal with semilocal quotient ring lies in only
  finitely many maximal ideals.
* `Ideal.finite_setOfPred_isMaximal_and_le_of_ne_bot`: a nonzero ideal of a Noetherian ring of
  dimension at most one lies in only finitely many maximal ideals.
-/

public section

namespace Ideal

/-- An ideal with semilocal quotient ring, for instance with Artinian or finite quotient ring, lies
in only finitely many maximal ideals. -/
theorem finite_setOfPred_isMaximal_and_le {R : Type*} [CommRing R] (𝔞 : Ideal R)
    [Finite (MaximalSpectrum (R ⧸ 𝔞))] : {P : Ideal R | P.IsMaximal ∧ 𝔞 ≤ P}.Finite :=
  (Set.finite_range fun Q : MaximalSpectrum (R ⧸ 𝔞) => Q.asIdeal.comap (Quotient.mk 𝔞)).subset
    fun P ⟨_, h𝔞P⟩ => ⟨⟨P.map (Quotient.mk 𝔞), IsMaximal.map_of_surjective_of_ker_le
      Quotient.mk_surjective (mk_ker.trans_le h𝔞P)⟩, comap_map_mk h𝔞P⟩

/-- A nonzero ideal of a Noetherian ring of dimension at most one, for instance of a Dedekind
domain, lies in only finitely many maximal ideals. -/
theorem finite_setOfPred_isMaximal_and_le_of_ne_bot {R : Type*} [CommRing R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] {𝔞 : Ideal R} (h𝔞 : 𝔞 ≠ ⊥) :
    {P : Ideal R | P.IsMaximal ∧ 𝔞 ≤ P}.Finite :=
  𝔞.finite_minimalPrimes_of_isNoetherianRing.subset fun _ ⟨hP, h𝔞P⟩ =>
    have := hP.isPrime
    mem_minimalPrimes_of_ne_bot h𝔞 h𝔞P

end Ideal

namespace TauCeti

/-- A maximal ideal of `B` containing `b` is the preimage of a maximal ideal of `B ⧸ bB`. -/
theorem exists_maximalSpectrum_comap_mk_eq {B : Type*} [CommRing B] {b : B}
    {m : MaximalSpectrum B} (hbm : b ∈ m.asIdeal) :
    ∃ q : MaximalSpectrum (B ⧸ Ideal.span {b}),
      q.asIdeal.comap (Ideal.Quotient.mk _) = m.asIdeal := by
  have hle : Ideal.span {b} ≤ m.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hbm
  exact ⟨⟨_, Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])⟩, Ideal.comap_map_mk hle⟩

/-- For a domain `B` finite over a Noetherian domain `A` of dimension at most one, a nonzero
`b : B` lies in only finitely many maximal ideals of `B`. -/
theorem finite_setOf_mem_maximalSpectrum (A : Type*) {B : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] {b : B} (hb : b ≠ 0) :
    {m : MaximalSpectrum B | b ∈ m.asIdeal}.Finite := by
  have := isArtinianRing_quotient_span_singleton A hb
  have h := ((Ideal.span {b}).finite_setOfPred_isMaximal_and_le).preimage
      (f := MaximalSpectrum.asIdeal) (fun _ _ _ _ h ↦ MaximalSpectrum.ext h)
  exact h.subset fun m hm ↦ ⟨m.isMaximal, (Ideal.span_singleton_le_iff_mem _).2 hm⟩

end TauCeti
