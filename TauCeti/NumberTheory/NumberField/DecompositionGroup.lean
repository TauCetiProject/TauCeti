/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import TauCeti.NumberTheory.NumberField.SplitsCompletely

/-!
# Splitting completely and the decomposition group

For a Galois number field `F / ℚ` and a prime `Q` of `𝓞 F` lying above a rational prime `p`, the
prime `p` splits completely — there are exactly `[F : ℚ]` primes of `𝓞 F` above `p` — if and only
if the decomposition group of `Q`, i.e. its stabilizer under the natural action of `Gal(F/ℚ)`, is
trivial.

This is the decomposition-group form of complete splitting, complementing the ramification/inertia
counting criterion. It is a bridge between Tau Ceti's complete-splitting criterion and Mathlib's
cardinality formula for decomposition groups.

## Main results

* `TauCeti.NumberField.ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot`: complete splitting is
  equivalent to a trivial decomposition group.

## Provenance

Specializes Tau Ceti's Dedekind-domain trivial-decomposition-group criterion
(`TauCeti.DedekindDomain.ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot_of_isGaloisGroup`);
prepared for the multiquadratic prime-splitting law (Layer 1 of the multiquadratic roadmap).
-/

open NumberField Ideal Module MulAction
open scoped Pointwise

namespace TauCeti.NumberField

attribute [local instance] Ideal.Quotient.field

/-- **Splitting completely ⟺ trivial decomposition group.** For a Galois number field `F` and a
prime `Q` of `𝓞 F` above the rational prime `p`, `p` splits completely (there are `[F : ℚ]` primes
above `p`) iff the decomposition group of `Q` — its stabilizer in `Gal(F/ℚ)` — is trivial. -/
theorem ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot (F : Type*) [Field F]
    [NumberField F] [IsGalois ℚ F] {p : ℕ} [Fact p.Prime] (Q : Ideal (𝓞 F)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 F)).ncard = finrank ℚ F ↔
      stabilizer (F ≃ₐ[ℚ] F) Q = ⊥ := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hpne
  haveI : (span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))
  haveI : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := Ideal.IsPrime.isMaximal ‹_› hp0
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal ‹Q.IsPrime› (ne_bot_of_liesOver_of_ne_bot hp0 Q)
  haveI : Finite (ℤ ⧸ (span {(p : ℤ)} : Ideal ℤ)) :=
    Ring.HasFiniteQuotients.finiteQuotient hp0
  haveI : Module.Finite (ℤ ⧸ (span {(p : ℤ)} : Ideal ℤ)) (𝓞 F ⧸ Q) := inferInstance
  haveI : Algebra.IsAlgebraic (ℤ ⧸ (span {(p : ℤ)} : Ideal ℤ)) (𝓞 F ⧸ Q) := inferInstance
  haveI : PerfectField (ℤ ⧸ (span {(p : ℤ)} : Ideal ℤ)) := inferInstance
  haveI : Algebra.IsSeparable (ℤ ⧸ (span {(p : ℤ)} : Ideal ℤ)) (𝓞 F ⧸ Q) :=
    inferInstance
  have h :=
    TauCeti.DedekindDomain.ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot_of_isGaloisGroup
      (F ≃ₐ[ℚ] F) (span {(p : ℤ)}) hp0 Q
  rwa [IsGaloisGroup.card_eq_finrank (F ≃ₐ[ℚ] F) ℚ F] at h

end TauCeti.NumberField
