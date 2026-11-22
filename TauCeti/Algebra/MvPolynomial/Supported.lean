/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Algebra generation for multivariate polynomials over an intermediate ring

For an `R`-algebra `B`, `MvPolynomial σ B` is generated as an `R`-algebra by the base constants
`C b` and the polynomial variables `X i` (`TauCeti.MvPolynomial.adjoin_range_C_union_range_X`).

## Main results

* `TauCeti.MvPolynomial.adjoin_range_C_union_range_X`: `MvPolynomial σ B` is generated as an
  `R`-algebra by base constants and variables.
-/

public section

namespace TauCeti.MvPolynomial

/-- `MvPolynomial σ B` is generated as an `R`-algebra by base constants `C b` and polynomial
variables `X i`. -/
theorem adjoin_range_C_union_range_X (R B σ : Type*) [CommSemiring R] [CommSemiring B]
    [Algebra R B] :
    Algebra.adjoin R
        (Set.range (_root_.MvPolynomial.C : B → _root_.MvPolynomial σ B) ∪
          Set.range _root_.MvPolynomial.X) =
      ⊤ := by
  rw [eq_top_iff, ← Subalgebra.restrictScalars_top R (S := B) (A := _root_.MvPolynomial σ B),
    ← _root_.MvPolynomial.adjoin_range_X (R := B) (σ := σ),
    Algebra.Subalgebra.restrictScalars_adjoin, sup_le_iff]
  refine ⟨?_, Algebra.adjoin_mono Set.subset_union_right⟩
  rintro _ ⟨b, rfl⟩
  exact Algebra.subset_adjoin (Or.inl ⟨b, rfl⟩)

end TauCeti.MvPolynomial
