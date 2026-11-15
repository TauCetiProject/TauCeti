/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Norm

/-!
# Positivity of fractional ideal norms

Mathlib defines the rational-valued absolute norm `FractionalIdeal.absNorm` on fractional ideals of
a Dedekind domain that is finite free over `ℤ`, and proves `FractionalIdeal.absNorm_nonneg` and
`FractionalIdeal.absNorm_eq_zero_iff`. This file records the corresponding strict positivity
characterization for nonzero fractional ideals.

## Main results

* `FractionalIdeal.absNorm_pos_iff`: `0 < FractionalIdeal.absNorm I ↔ I ≠ 0`.
* `FractionalIdeal.absNorm_pos`: `0 < FractionalIdeal.absNorm I` for `I ≠ 0`.
-/

public section

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]
  {K : Type*} [CommRing K] [IsDomain K] [Algebra R K] [IsFractionRing R K]

/-- The absolute norm of a fractional ideal is positive if and only if the ideal is nonzero. -/
@[simp]
theorem absNorm_pos_iff {I : FractionalIdeal R⁰ K} : 0 < absNorm I ↔ I ≠ 0 :=
  (absNorm_nonneg I).lt_iff_ne'.trans absNorm_eq_zero_iff.not

/-- The absolute norm of a nonzero fractional ideal is positive. -/
theorem absNorm_pos {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) : 0 < absNorm I :=
  absNorm_pos_iff.mpr hI

end FractionalIdeal
