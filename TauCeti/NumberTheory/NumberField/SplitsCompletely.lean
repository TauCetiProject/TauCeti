/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A counting criterion for a prime to split completely in a Galois number field

For a Galois number field `K / ℚ`, a rational prime `p` splits completely — meaning there are
exactly `[K : ℚ]` primes of `𝓞 K` above `p` — if and only if `p` is unramified with residue
degree one, i.e. both the ramification index `e` and the inertia degree `f` (which are common to
all primes above `p`, the extension being Galois) equal `1`.

This is the count form of the fundamental identity `(#primes) · e · f = [K : ℚ]`: with the
product fixed at `[K : ℚ]`, the number of primes is maximal exactly when `e = f = 1`. It is the
general Galois-number-field criterion underlying the multiquadratic prime-splitting law (Layer 1
of the multiquadratic roadmap), where complete splitting is read off from residues.

## Main results

* `TauCeti.NumberField.ncard_primesOver_eq_finrank_iff`: `p` splits completely iff `e = 1 ∧ f = 1`.

## Provenance

Built directly on Mathlib's Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`); the criterion is assembled
here for the Tau Ceti library.
-/

open NumberField Ideal Module

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

/-- In a Galois number field, a rational prime `p` splits completely (there are `[K : ℚ]` primes
of `𝓞 K` above `p`) iff its ramification index and inertia degree are both `1`. -/
theorem ncard_primesOver_eq_finrank_iff (p : ℕ) [Fact p.Prime] :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔
      (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧
        (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hpne
  haveI : (span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))
  haveI : (span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal ‹_› hp0
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp0 (𝓞 K) Gal(K/ℚ)
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K] at h_main
  have hF : 0 < finrank ℚ K := finrank_pos
  constructor
  · intro hn
    rw [hn] at h_main
    have hef : (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) *
        (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 :=
      Nat.eq_of_mul_eq_mul_left hF (by rw [mul_one]; exact h_main)
    exact ⟨Nat.dvd_one.mp ⟨_, hef.symm⟩, Nat.dvd_one.mp ⟨_, by rw [mul_comm]; exact hef.symm⟩⟩
  · rintro ⟨he, hf⟩
    simpa [he, hf] using h_main

end TauCeti.NumberField
