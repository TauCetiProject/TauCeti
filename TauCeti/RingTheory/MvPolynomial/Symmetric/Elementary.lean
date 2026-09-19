/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Elementary symmetric polynomials in small finite alphabets

This file gives explicit formulas for elementary symmetric polynomials in small finite alphabets.
Such expansions support explicit computations of symmetric orbit products. In particular, the
four-variable formula is used to express the quartic `D₄` resolvent's orbit product in elementary
symmetric polynomials.

## Main results

* `TauCeti.esymm_fin_four`: the four elementary symmetric polynomials in four variables.
-/

public section

namespace TauCeti

/-- The elementary symmetric polynomials in four variables, written out explicitly. -/
theorem esymm_fin_four {R : Type*} [CommSemiring R] :
    MvPolynomial.esymm (Fin 4) R 1 =
        MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 2 =
        MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 2 +
          MvPolynomial.X 0 * MvPolynomial.X 3 + MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.X 1 * MvPolynomial.X 3 + MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 3 =
        MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 +
          MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
          MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 4 =
        MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 := by
  have h1 : Finset.powersetCard 1 (Finset.univ : Finset (Fin 4)) = {{0}, {1}, {2}, {3}} := by
    decide
  have h2 : Finset.powersetCard 2 (Finset.univ : Finset (Fin 4)) =
      {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by
    decide
  have h3 : Finset.powersetCard 3 (Finset.univ : Finset (Fin 4)) =
      {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} := by
    decide
  have h4 : Finset.powersetCard 4 (Finset.univ : Finset (Fin 4)) = {{0, 1, 2, 3}} := by
    decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp (config := { decide := true }) only [MvPolynomial.esymm, h1, h2, h3, h4,
        Finset.sum_insert, Finset.prod_insert, Finset.sum_singleton, Finset.prod_singleton,
        Finset.mem_insert, Finset.mem_singleton, add_assoc, mul_assoc]

end TauCeti
