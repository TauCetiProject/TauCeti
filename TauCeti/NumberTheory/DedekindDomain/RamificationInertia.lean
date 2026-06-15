/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Ramification and inertia counting criteria in Dedekind domains

This file records a Galois form of the fundamental identity for primes in finite extensions
of Dedekind domains: in a Galois extension, the number of primes above a nonzero maximal
ideal is maximal exactly when the common ramification index and inertia degree are both `1`.

## Main results

* `TauCeti.DedekindDomain.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup`: the
  Dedekind-domain Galois counting criterion.

## Provenance

Built directly on Mathlib's Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`).
-/

open Ideal Module

namespace TauCeti.DedekindDomain

/-- In a finite Galois extension of Dedekind domains, the number of primes over a nonzero
maximal ideal equals the order of the Galois group iff the common ramification index and
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

end TauCeti.DedekindDomain
