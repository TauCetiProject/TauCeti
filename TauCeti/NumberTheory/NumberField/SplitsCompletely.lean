/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# A counting criterion for a prime to split completely in a Galois number field

For a finite Galois extension of Dedekind domains, a nonzero maximal ideal `P` of the base
splits completely — meaning there are exactly `Nat.card G` primes above `P` — if and only if
`P` is unramified with residue degree one. For a finite Galois extension of number fields
`L / K`, this says that a prime `P` of `𝓞 K` splits completely — meaning there are exactly
`[L : K]` primes of `𝓞 L` above `P` — if and only if `P` is
unramified with residue degree one, i.e. both the ramification index `e` and the inertia degree
`f` (which are common to all primes above `P`, the extension being Galois) equal `1`.

This is the count form of the fundamental identity `(#primes) · e · f = [L : K]`: with the
product fixed at `[L : K]`, the number of primes is maximal exactly when `e = f = 1`. The
rational-prime corollary is the Galois-number-field criterion underlying the multiquadratic
prime-splitting law (Layer 1 of the multiquadratic roadmap), where complete splitting is read
off from residues.

## Main results

* `TauCeti.NumberField.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup`: the
  Dedekind-domain criterion for an explicit Galois group.
* `TauCeti.NumberField.ncard_primesOver_eq_finrank_iff_of_isGalois`: a prime of the base
  number field splits completely iff `e = 1 ∧ f = 1`.
* `TauCeti.NumberField.ncard_primesOver_eq_finrank_iff`: the rational-prime specialization.

## Provenance

Built directly on Mathlib's Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`); the criterion is assembled
here for the Tau Ceti library.
-/

open NumberField Ideal Module

namespace TauCeti.NumberField

/-- In a finite Galois extension of Dedekind domains, a nonzero maximal ideal of the base
splits completely (there are `Nat.card G` primes above it) iff its ramification index and
inertia degree are both `1`. -/
theorem ncard_primesOver_eq_natCard_iff_of_isGaloisGroup {A B : Type*} [CommRing A]
    [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [IsTorsionFree A B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (P : Ideal A) [P.IsMaximal] (hP : P ≠ ⊥) :
    (primesOver P B).ncard = Nat.card G ↔
      P.ramificationIdxIn B = 1 ∧ P.inertiaDegIn B = 1 := by
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hP B G
  have hG : 0 < Nat.card G := Nat.card_pos
  constructor
  · intro hn
    rw [hn] at h_main
    have hef : P.ramificationIdxIn B * P.inertiaDegIn B = 1 :=
      Nat.eq_of_mul_eq_mul_left hG (by rw [mul_one]; exact h_main)
    exact mul_eq_one.mp hef
  · rintro ⟨he, hf⟩
    simpa [he, hf] using h_main

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- In a finite Galois extension of number fields, a prime of the base splits completely
(there are `[L : K]` primes above it) iff its ramification index and inertia degree are both
`1`. -/
theorem ncard_primesOver_eq_finrank_iff_of_isGalois (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : P ≠ ⊥) :
    (primesOver P (𝓞 L)).ncard = finrank K L ↔
      P.ramificationIdxIn (𝓞 L) = 1 ∧ P.inertiaDegIn (𝓞 L) = 1 := by
  have h := ncard_primesOver_eq_natCard_iff_of_isGaloisGroup (B := 𝓞 L) Gal(L/K) P hP
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
  have h := ncard_primesOver_eq_natCard_iff_of_isGaloisGroup (B := 𝓞 K) Gal(K/ℚ)
    (span {(p : ℤ)}) hp0
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K] at h
  exact h

end TauCeti.NumberField
