/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Units at the height-one primes of `ℚ`

Let `R` be the ring of integers of `ℚ` in the sense of `IsIntegralClosure R ℤ ℚ`, and let `v` be a
height-one prime of `R`, corresponding to the rational prime
`p = Rat.HeightOneSpectrum.primesEquiv v`.
This file compares the `v`-adic valuation with the `p`-adic valuation `padicValRat p`.

## Main results

* `Rat.HeightOneSpectrum.valuation_eq_one_iff_padicValRat_eq_zero`: a nonzero rational number is
  a unit at `v` exactly when its `p`-adic valuation vanishes.
-/

public section

open IsDedekindDomain

namespace Rat.HeightOneSpectrum

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ] [IsDedekindDomain R]
  [IsFractionRing R ℚ]

/-- A nonzero rational number is a unit at the height-one prime `v` exactly when its `p`-adic
valuation vanishes, for `p` the rational prime corresponding to `v`. -/
theorem valuation_eq_one_iff_padicValRat_eq_zero (v : HeightOneSpectrum R) {x : ℚ}
    (hx : x ≠ 0) : v.valuation ℚ x = 1 ↔ padicValRat (primesEquiv v) x = 0 := by
  have : Fact (primesEquiv v : ℕ).Prime := ⟨(primesEquiv v).2⟩
  rw [(valuation_equiv_padicValuation v).eq_one_iff_eq_one]
  simp [Rat.padicValuation, hx]

end Rat.HeightOneSpectrum
