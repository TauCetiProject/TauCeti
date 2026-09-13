/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import TauCeti.NumberTheory.NumberField.Discriminant.Relative
public import TauCeti.RingTheory.DedekindDomain.Discriminant.Ramification

/-!
# Ramification and relative discriminants of number fields

For an extension of number fields, the primes dividing the relative discriminant are exactly the
primes below an upper prime whose ramification index is greater than one. This is the classical
ramification criterion in the number-field setting, where finite residue fields make ramification
equivalent to a nontrivial ramification index.

## Main results

* `TauCeti.NumberField.dvd_relDiscr_iff_exists_one_lt_ramificationIdx`: a prime divides the
  relative discriminant exactly when a prime above it has ramification index greater than one.
-/

public section

open scoped NumberField nonZeroDivisors

namespace TauCeti.NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **A nonzero prime divides a number-field relative discriminant exactly when an upper prime has
ramification index greater than one.** -/
theorem dvd_relDiscr_iff_exists_one_lt_ramificationIdx {p : Ideal (𝓞 K)} [p.IsPrime]
    (hp : p ≠ ⊥) :
    p ∣ relDiscr (𝓞 K) (𝓞 L) ↔
      ∃ P : p.primesOver (𝓞 L), 1 < (P : Ideal (𝓞 L)).ramificationIdx (𝓞 K) := by
  rw [dvd_relDiscr_iff_exists_not_isUnramifiedAt hp]
  apply exists_congr
  intro P
  constructor
  · intro hPram
    refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨(Ideal.ramificationIdx_pos (P : Ideal (𝓞 L)) (𝓞 K)).ne', ?_⟩
    exact fun h => hPram (Ideal.ramificationIdx_eq_one_iff.mp h)
  · intro he hur
    exact he.ne' (Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K))

end TauCeti.NumberField

end
