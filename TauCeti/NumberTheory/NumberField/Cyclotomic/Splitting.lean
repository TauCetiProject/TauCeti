/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Prime counts in cyclotomic fields

For an unramified rational prime in a cyclotomic field, the number of primes above it times
their residue degree is the degree of the field. This follows from Mathlib's cyclotomic
splitting law and the Galois fundamental identity.
-/

public section
noncomputable section

open Ideal NumberField
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- For an unramified rational prime in a cyclotomic field, the number of primes above it
times their residue degree is the degree of the field. -/
theorem ncard_primesOver_mul_orderOf_eq_totient {m : ℕ} [NeZero m]
    [IsCyclotomicExtension {m} ℚ K] (p : ℕ) [Fact p.Prime] (hm : ¬ p ∣ m) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard * orderOf (p : ZMod m) = Nat.totient m := by
  let _ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hm,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hm,
    IsGalois.card_aut_eq_finrank ℚ K, IsCyclotomicExtension.Rat.finrank m K] at h
  simpa using h

end TauCeti.NumberField

end
