/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
import TauCeti.RingTheory.Ideal.Quotient.IsPrincipal

/-!
# Factoriality from a principal ideal domain quotient

Let `R` be a Noetherian domain and `x` an element of its Jacobson radical such that `R ⧸ (x)` is a
principal ideal domain. Then `R` is a unique factorization domain: every nonzero prime `𝔮`
contains a prime element, namely `x` if `x ∈ 𝔮`, and otherwise a generator of `𝔮`, which is
principal by `Ideal.IsPrime.isPrincipal_of_isPrincipal_map_quotient_span_singleton`. Kaplansky's
criterion concludes.

## Main results

* `UniqueFactorizationMonoid.of_isPrincipalIdealRing_quotient_span_singleton`: a Noetherian domain
  with an element `x` of its Jacobson radical such that `R ⧸ (x)` is a principal ideal domain is a
  unique factorization domain.

## References

* I. Kaplansky, *Commutative Rings*, for the criterion by prime elements in prime ideals, which is
  Mathlib's `UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime`.
-/

public section

open Ideal

variable {R : Type*} [CommRing R]

/-- **A domain is factorial if it is a principal ideal domain modulo a radical element.** Let `R`
be a Noetherian domain and `x` an element of its Jacobson radical such that `R ⧸ (x)` is a principal
ideal domain. Then `R` is a unique factorization domain. -/
theorem UniqueFactorizationMonoid.of_isPrincipalIdealRing_quotient_span_singleton [IsDomain R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ (⊥ : Ideal R).jacobson) [IsDomain (R ⧸ span {x})]
    [IsPrincipalIdealRing (R ⧸ span {x})] : UniqueFactorizationMonoid R := by
  by_cases hx0 : x = 0
  · -- Modulo `x = 0` the ring is `R` itself, a principal ideal domain.
    subst hx0
    let e := (quotEquivOfEq (span_singleton_eq_bot.mpr rfl)).trans (RingEquiv.quotientBot R)
    have : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
    infer_instance
  have hxprime : Prime x :=
    (span_singleton_prime hx0).mp ((Quotient.isDomain_iff_prime _).mp inferInstance)
  refine iff_exists_prime_mem_of_isPrime.mpr fun q hq0 hq ↦ ?_
  by_cases hxq : x ∈ q
  · exact ⟨x, hxq, hxprime⟩
  obtain ⟨f, (hf : q = span {f})⟩ := hq.isPrincipal_of_isPrincipal_map_quotient_span_singleton
    (IsNoetherian.noetherian q) hx hxq (IsPrincipalIdealRing.principal _)
  refine ⟨f, hf ▸ mem_span_singleton_self f, (span_singleton_prime ?_).mp (hf ▸ hq)⟩
  rintro rfl
  exact hq0 (by simpa using hf)
