/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Finite approximation in Dedekind domains

This file gives the finite approximation theorem in the form used to patch local data over a
Dedekind domain. Given residue classes modulo powers of the maximal ideals in finitely many
localizations, one global element realizes all of them.

The proof combines the Chinese remainder theorem
`Ideal.pi_quotient_surjective` with the canonical comparison
`IsLocalization.AtPrime.equivQuotMaximalIdealPow` between a prime-power quotient and the
corresponding quotient after localization.

## Main results

* `TauCeti.DedekindDomain.exists_eq_mod_localized_prime_pow`: simultaneous approximation of
  finitely many classes in localized prime-power quotients.
* `TauCeti.DedekindDomain.exists_valuation_sub_le`: the same in valuation form — finitely many
  elements of the fraction field, each integral at its prime, are simultaneously approximated
  `v`-adically by one element of the ring.

This is the finite approximation input for the local-to-global patching arguments in
Silverman, *The Arithmetic of Elliptic Curves*, Chapter VIII, Section 8.
-/

public section

namespace TauCeti.DedekindDomain

open Function
open IsDedekindDomain

variable {R ι : Type*} [CommRing R] [IsDedekindDomain R] [Finite ι]

/-- **Finite approximation at height-one primes.**

For pairwise distinct height-one primes `v i`, arbitrary residue classes modulo the indicated
powers of the maximal ideals of `R_{v i}` are simultaneously represented by a single element
of `R`.

Allowing exponent zero is harmless: the corresponding quotient is the zero ring, so that
component imposes no condition. -/
theorem exists_eq_mod_localized_prime_pow
    (v : ι → HeightOneSpectrum R) (hv : Function.Injective v) (n : ι → ℕ)
    (x : (i : ι) →
      Localization.AtPrime (v i).asIdeal ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime (v i).asIdeal) ^ n i) :
    ∃ a : R, ∀ i,
      Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime (v i).asIdeal) a) = x i := by
  let y : (i : ι) → R ⧸ (v i).asIdeal ^ n i := fun i ↦
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow (v i).asIdeal
      (Localization.AtPrime (v i).asIdeal) (n i)).symm (x i)
  have hcoprime : Pairwise (IsCoprime on fun i ↦ (v i).asIdeal ^ n i) := by
    intro i j hij
    exact (v i).isCoprime_pow_of_ne (v j) (fun h ↦ hij (hv h)) (n i) (n j)
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hcoprime y
  refine ⟨a, fun i ↦ ?_⟩
  rw [← IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk (v i).asIdeal
    (Localization.AtPrime (v i).asIdeal) (n i) a, ha i]
  exact Equiv.apply_symm_apply _ (x i)

/-- **Finite approximation in valuation form.**

For a finite set `S` of height-one primes and elements `x v` of the fraction field with
`v (x v) ≤ 1` for `v ∈ S`, a single `a : R` satisfies `v (a - x v) ≤ exp (-n v)` for every
`v ∈ S`. Unlike `exists_eq_mod_localized_prime_pow`, the targets are elements of `K` and the
approximation is read through the `v`-adic valuations, the form in which local data over the
fraction field is patched. -/
theorem exists_valuation_sub_le {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Finset (HeightOneSpectrum R)) (n : HeightOneSpectrum R → ℕ)
    (x : HeightOneSpectrum R → K) (hx : ∀ v ∈ S, v.valuation K (x v) ≤ 1) :
    ∃ a : R, ∀ v ∈ S,
      v.valuation K (algebraMap R K a - x v) ≤ WithZero.exp (-(n v : ℤ)) := by
  -- First approximate each `x v` by an element of `R`, one prime at a time.
  have hloc (v : S) : ∃ b : R,
      v.1.valuation K (algebraMap R K b - x v) ≤ WithZero.exp (-(n v : ℤ)) := by
    obtain ⟨b, hb⟩ := v.1.exists_valuation_sub_lt_of_integer (hx v v.2)
      (Units.mk0 (WithZero.exp (-(n v : ℤ))) WithZero.exp_ne_zero)
    exact ⟨b, hb.le⟩
  choose b hb using hloc
  -- Then patch the finitely many approximations together by the Chinese remainder theorem.
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum R ↦ v.asIdeal) n (fun v _ ↦ v.prime)
    (fun v _ w _ hvw h ↦ hvw (HeightOneSpectrum.ext h)) b
  refine ⟨a, fun v hv ↦ ?_⟩
  have hab : v.valuation K (algebraMap R K (a - b ⟨v, hv⟩)) ≤ WithZero.exp (-(n v : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact ha v hv
  rw [map_sub] at hab
  have hsplit : algebraMap R K a - x v = (algebraMap R K a - algebraMap R K (b ⟨v, hv⟩)) +
      (algebraMap R K (b ⟨v, hv⟩) - x v) := by ring
  rw [hsplit]
  exact Valuation.map_add_le _ hab (hb ⟨v, hv⟩)

end TauCeti.DedekindDomain

end
