/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.NumberTheory.DedekindDomain.RamificationInertia

/-!
# A counting criterion for a prime to split completely in a Galois number field

For a finite Galois number field `K / ℚ`, a rational prime `p` splits completely — meaning
there are exactly `[K : ℚ]` primes of `𝓞 K` above `p` — if and only if `p` is unramified with
residue degree one, i.e. both the ramification index `e` and the inertia degree `f` (which are
common to all primes above `p`, the extension being Galois) equal `1`.

This is the count form of the fundamental identity `(#primes) · e · f = [L : K]`: with the
product fixed at `[L : K]`, the number of primes is maximal exactly when `e = f = 1`. The
rational-prime corollary is the Galois-number-field criterion underlying the multiquadratic
prime-splitting law (Layer 1 of the multiquadratic roadmap), where complete splitting is read
off from residues.

## Main results

* `TauCeti.NumberField.ncard_primesOver_eq_finrank_iff`: the rational-prime specialization.

## Provenance

Built directly on Mathlib's Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`); the criterion is assembled
here for the Tau Ceti library.
-/

open NumberField Ideal Module

namespace TauCeti.NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L]

private theorem ncard_primesOver_eq_finrank_iff_of_isGalois {A : Type*} [CommRing A]
    [IsDedekindDomain A] [Algebra A (𝓞 L)] [Module.Finite A (𝓞 L)]
    [IsTorsionFree A (𝓞 L)] [IsGaloisGroup Gal(L/K) A (𝓞 L)] (P : Ideal A)
    [P.IsMaximal] (hP : P ≠ ⊥) :
    (primesOver P (𝓞 L)).ncard = finrank K L ↔
      P.ramificationIdxIn (𝓞 L) = 1 ∧ P.inertiaDegIn (𝓞 L) = 1 := by
  have h := TauCeti.DedekindDomain.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup
    (B := 𝓞 L) Gal(L/K) P hP
  rw [IsGaloisGroup.card_eq_finrank Gal(L/K) K L] at h
  exact h

/-- In a Galois number field, a rational prime `p` splits completely (there are `[K : ℚ]` primes
of `𝓞 K` above `p`) iff its ramification index and inertia degree are both `1`. -/
theorem ncard_primesOver_eq_finrank_iff (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p : ℕ) [Fact p.Prime] :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔
      (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧
        (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hpne
  haveI : (span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))
  haveI : (span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal ‹_› hp0
  have h := ncard_primesOver_eq_finrank_iff_of_isGalois ℚ K (A := ℤ) (span {(p : ℤ)}) hp0
  exact h

end TauCeti.NumberField
