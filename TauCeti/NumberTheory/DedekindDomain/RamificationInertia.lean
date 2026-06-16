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
* `TauCeti.DedekindDomain.ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot_of_isGaloisGroup`:
  the corresponding trivial-decomposition-group criterion.

## Provenance

Built directly on Mathlib's Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`).
-/

open Ideal Module
open scoped Pointwise

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

attribute [local instance] Ideal.Quotient.field

/-- In a finite Galois extension of Dedekind domains, the number of primes over a nonzero
maximal ideal equals the order of the Galois group iff the decomposition group of any chosen
prime above it is trivial. -/
theorem ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot_of_isGaloisGroup {A B : Type*}
    [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [IsTorsionFree A B] (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G B] [IsGaloisGroup G A B] (P : Ideal A) [P.IsMaximal]
    (hP : P ≠ ⊥) (Q : Ideal B) [Q.LiesOver P] [Q.IsMaximal]
    [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)] :
    (primesOver P B).ncard = Nat.card G ↔ MulAction.stabilizer G Q = ⊥ := by
  have hsplit := ncard_primesOver_eq_natCard_iff_of_isGaloisGroup (B := B) G P hP
  have hcard :
      Nat.card (MulAction.stabilizer G Q) = P.ramificationIdxIn B * P.inertiaDegIn B :=
    Ideal.card_stabilizer_eq (G := G) P hP Q
  constructor
  · intro hn
    have hef := hsplit.mp hn
    have hc : Nat.card (MulAction.stabilizer G Q) = 1 := by
      rw [hcard, hef.1, hef.2]
    exact Subgroup.card_eq_one.mp hc
  · intro hst
    refine hsplit.mpr ?_
    have hc : Nat.card (MulAction.stabilizer G Q) = 1 := Subgroup.card_eq_one.mpr hst
    exact mul_eq_one.mp (hcard.symm.trans hc)

end TauCeti.DedekindDomain
