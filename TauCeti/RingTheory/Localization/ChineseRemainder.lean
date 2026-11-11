/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The Chinese remainder theorem for localizations at maximal ideals

For finitely many distinct maximal ideals `p i` of a commutative ring `R`, residue classes modulo
powers of the maximal ideals of the localizations `R_{p i}` are simultaneously represented by a
single element of `R`.

The proof combines the Chinese remainder theorem `Ideal.pi_quotient_surjective` with the
canonical comparison `IsLocalization.AtPrime.equivQuotMaximalIdealPow` between a prime-power
quotient and the corresponding quotient after localization.

## Main results

* `TauCeti.Localization.AtPrime.exists_mk_algebraMap_eq_of_isMaximal`: simultaneous
  approximation of finitely many classes in localized maximal-ideal-power quotients.
-/

public section

namespace TauCeti.Localization.AtPrime

open Function

variable {R ι : Type*} [CommRing R] [Finite ι]

/-- **Chinese remainder theorem at maximal ideals, after localization.**

For pairwise distinct maximal ideals `p i`, arbitrary residue classes modulo the indicated
powers of the maximal ideals of `R_{p i}` are simultaneously represented by a single element
of `R`. In a Dedekind domain this applies to the ideals of finitely many distinct height-one
primes.

Allowing exponent zero is harmless: the corresponding quotient is the zero ring, so that
component imposes no condition. -/
theorem exists_mk_algebraMap_eq_of_isMaximal
    (p : ι → Ideal R) [∀ i, (p i).IsMaximal] (hp : Injective p) (n : ι → ℕ)
    (x : (i : ι) →
      Localization.AtPrime (p i) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime (p i)) ^ n i) :
    ∃ a : R, ∀ i, Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime (p i)) a) = x i := by
  let y : (i : ι) → R ⧸ p i ^ n i := fun i ↦
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow (p i) (Localization.AtPrime (p i))
      (n i)).symm (x i)
  have hcoprime : Pairwise (IsCoprime on fun i ↦ p i ^ n i) := fun i j hij ↦
    (Ideal.isCoprime_of_isMaximal (hp.ne hij)).pow
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hcoprime y
  refine ⟨a, fun i ↦ ?_⟩
  rw [← IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk (p i)
    (Localization.AtPrime (p i)) (n i) a, ha i]
  exact Equiv.apply_symm_apply _ (x i)

end TauCeti.Localization.AtPrime

end
