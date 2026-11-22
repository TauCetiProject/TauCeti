/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Algebra.DirectSum.Component

/-!
# Projections onto the forms of a fixed degree

Mathlib's `MvPolynomial.decomposition` decomposes a polynomial ring into its submodules of forms
of each degree. For this decomposition the projection `TauCeti.homogeneousProj` onto the forms of
degree `n`, followed by the inclusion, is Mathlib's homogeneous component
`MvPolynomial.homogeneousComponent n`.

These statements live in their own module rather than in
`TauCeti.RingTheory.MvPolynomial.Homogeneous`: they need `TauCeti.Algebra.DirectSum.Component`
imported publicly, whose `TauCeti.homogeneousComponent` would make the name `homogeneousComponent`
ambiguous in the modules downstream of that file that open both `TauCeti` and `MvPolynomial`.

## Main results

* `MvPolynomial.coe_homogeneousProj_homogeneousSubmodule`: the projection of `φ` onto the forms of
  degree `n` is `homogeneousComponent n φ`.
* `MvPolynomial.subtype_comp_homogeneousProj`: the same statement as an equality of linear maps.
-/

public section

namespace MvPolynomial

attribute [local instance] decomposition

variable {σ R : Type*} [CommSemiring R]

/-- The projection of `φ` onto the forms of degree `n` is the homogeneous component of degree `n`
of `φ`. -/
theorem coe_homogeneousProj_homogeneousSubmodule (n : ℕ) (φ : MvPolynomial σ R) :
    (TauCeti.homogeneousProj (homogeneousSubmodule σ R) n φ : MvPolynomial σ R) =
      homogeneousComponent n φ := by
  rw [TauCeti.homogeneousProj_apply, ← DirectSum.Decomposition.decompose'_eq,
    decomposition.decompose'_apply]

/-- The projection `TauCeti.homogeneousProj` onto the forms of degree `n`, followed by the
inclusion, is the homogeneous component of degree `n`. -/
theorem subtype_comp_homogeneousProj (n : ℕ) :
    (homogeneousSubmodule σ R n).subtype ∘ₗ TauCeti.homogeneousProj (homogeneousSubmodule σ R) n =
      homogeneousComponent n :=
  LinearMap.ext fun φ ↦ by
    rw [LinearMap.comp_apply, Submodule.subtype_apply, coe_homogeneousProj_homogeneousSubmodule]

end MvPolynomial
