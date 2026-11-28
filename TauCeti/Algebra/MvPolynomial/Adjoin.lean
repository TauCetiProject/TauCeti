/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Algebra generation for multivariate polynomials over a base algebra

Over a commutative `R`-algebra `B`, the polynomial algebra `MvPolynomial σ B` is generated as an
`R`-algebra by the base constants `MvPolynomial.C b` and the polynomial variables
`MvPolynomial.X i` (`MvPolynomial.adjoin_range_C_union_range_X`), extending
`MvPolynomial.adjoin_range_X` from base ring `R` to an `R`-algebra `B`.

## Main results

* `MvPolynomial.adjoin_range_C_union_range_X`: `MvPolynomial σ B` is generated as an `R`-algebra
  by base constants and variables.
-/

public section

namespace MvPolynomial

/-- `MvPolynomial σ B` is generated as an `R`-algebra by base constants `C b` and polynomial
variables `X i`. -/
theorem adjoin_range_C_union_range_X (R B σ : Type*) [CommSemiring R] [CommSemiring B]
    [Algebra R B] :
    Algebra.adjoin R
        (Set.range (C : B → MvPolynomial σ B) ∪ Set.range X) =
      ⊤ := by
  ext p
  simp only [Algebra.mem_top, iff_true]
  induction p using MvPolynomial.induction_on with
  | C b => exact Algebra.subset_adjoin (Or.inl ⟨b, rfl⟩)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))

end MvPolynomial
