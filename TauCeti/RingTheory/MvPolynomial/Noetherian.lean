/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Basic

import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Noetherianity of multivariate polynomial rings

By Hilbert's basis theorem (`MvPolynomial.isNoetherianRing`), `MvPolynomial σ R` is Noetherian
whenever `R` is Noetherian and `σ` is finite. Conversely, over a nontrivial commutative ring `R`,
a polynomial ring in infinitely many variables is never Noetherian
(`MvPolynomial.not_isNoetherianRing`), while surjectivity of `MvPolynomial.constantCoeff` forces
`R` itself to be Noetherian whenever `MvPolynomial σ R` is.

## Main results

* `MvPolynomial.isNoetherianRing_iff`: over a nontrivial commutative ring `R`, `MvPolynomial σ R`
  is Noetherian if and only if `R` is Noetherian and `σ` is finite.
-/

public section

namespace MvPolynomial

/-- Over a nontrivial commutative ring `R`, `MvPolynomial σ R` is Noetherian if and only if `R` is
Noetherian and `σ` is finite. -/
theorem isNoetherianRing_iff {R σ : Type*} [CommRing R] [Nontrivial R] :
    IsNoetherianRing (MvPolynomial σ R) ↔ IsNoetherianRing R ∧ Finite σ := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨_, _⟩ ↦ inferInstance⟩
  · exact isNoetherianRing_of_surjective (MvPolynomial σ R) R MvPolynomial.constantCoeff
      fun r ↦ ⟨MvPolynomial.C r, by simp⟩
  · by_contra hinf
    have : Infinite σ := not_finite_iff_infinite.mp hinf
    exact not_isNoetherianRing σ R h

end MvPolynomial
