/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.IsConjRoot
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Conjugate roots over the fraction field of an integrally closed domain

Over an integrally closed domain `R` with fraction field `K`, the minimal polynomial over `K` of
an element integral over `R` has coefficients in `R`. Hence a conjugate over `K` of an element
integral over `R` is again integral over `R`. Mathlib's `IsConjRoot.isIntegral` only transfers
integrality over the base ring of the conjugacy relation itself.

## Main results

* `IsConjRoot.isIntegral_of_isIntegrallyClosed`: a conjugate over `K` of an element integral over
  `R` is integral over `R`.
-/

public section

open Polynomial

namespace IsConjRoot

variable {R K S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDomain S] [Algebra R S] [Algebra K S] [IsScalarTower R K S]

/-- Over an integrally closed domain `R` with fraction field `K`, a conjugate over `K` of an
element integral over `R` is again integral over `R`. -/
theorem isIntegral_of_isIntegrallyClosed {x y : S} (h : IsConjRoot K x y) (hx : IsIntegral R x) :
    IsIntegral R y := by
  refine ⟨minpoly R x, minpoly.monic hx, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap K, ← minpoly.isIntegrallyClosed_eq_field_fractions' K hx]
  exact h.aeval_eq_zero

end IsConjRoot
