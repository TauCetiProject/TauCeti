/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

## Main result

* `TauCeti.DedekindDomain.exists_eq_mod_localized_prime_pow`: simultaneous approximation of
  finitely many classes in localized prime-power quotients.

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

end TauCeti.DedekindDomain

end
