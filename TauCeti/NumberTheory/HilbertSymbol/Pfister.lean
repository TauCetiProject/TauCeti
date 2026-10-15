/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Pfister.Hyperbolic
public import TauCeti.NumberTheory.HilbertSymbol.Basic

/-!
# Hilbert symbols and two-fold Pfister forms

Over any field in which `2` is invertible, the two-fold Pfister form `<<a, b>> = <1, -a, -b, ab>`
is the norm form of the quaternion algebra `ℍ[K,a,b]`. It is isotropic exactly when `ℍ[K,a,b]`
splits, that is when `b = x² - a y²` has a solution in `K`. So its anisotropy is read off the
norm-equation Hilbert symbol.

## Main results

* `TauCeti.anisotropic_pfisterFormClass_two_iff_hilbertSymbol_eq_neg_one`: `<<a, b>>` is
  anisotropic exactly when the Hilbert symbol `(a, b)` is `-1`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, §2 (the splitting
  criterion, Theorem 2.7), with the convention `<<a>> = <1, -a>`.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- **Anisotropy of `<<a, b>>` is read off the Hilbert symbol**: the two-fold Pfister form
`<<a, b>>` is anisotropic exactly when `b = x² - a y²` has no solution in `K`, that is when
`(a, b) = -1`. -/
theorem anisotropic_pfisterFormClass_two_iff_hilbertSymbol_eq_neg_one (a b : Kˣ) :
    (pfisterFormClass ![a, b]).Anisotropic ↔ hilbertSymbol a b = -1 := by
  have h : hilbertSymbol a b = 1 ↔ ¬ (pfisterFormClass ![a, b]).Anisotropic :=
    (hilbertSymbol_eq_one_iff_nonempty_algEquiv_matrix a b).trans
      ((pfisterFormClass_two_tfae a b).out 1 2)
  rw [← not_iff_not, ← h, ← ne_eq, Int.units_ne_iff_eq_neg, neg_neg]

end TauCeti
