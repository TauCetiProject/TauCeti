/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Surjectivity

/-!
# The index of the cyclotomic image over a finite extension of `ℚ_p`

The cyclotomic image of a finite extension `K/ℚ_p` has index dividing `[K : ℚ_p]` in `ℤ_pˣ`.
This combines the relative-index comparison for finite extensions with the full image over `ℚ_p`.
No valuation or topology on `K` is needed.

## Main results

* `TauCeti.index_range_localCyclotomicCharacter_dvd_finrank`: the index of the cyclotomic image
  divides the extension degree.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §4, for the cyclotomic extensions of `ℚ_p` and
  their Galois groups, which supply the full base-field image used in the index bound.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- The index of the cyclotomic image of a finite extension of `ℚ_p` divides its degree. -/
theorem index_range_localCyclotomicCharacter_dvd_finrank (K : Type*) [Field K]
    [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] :
    (localCyclotomicCharacter p K).range.index ∣ Module.finrank ℚ_[p] K := by
  have h := relIndex_range_localCyclotomicCharacter_dvd_finrank p ℚ_[p] K IsSepClosed.lift
  simpa only [range_localCyclotomicCharacter_ratPadic_eq_top, Subgroup.relIndex_top_right] using h

end TauCeti
