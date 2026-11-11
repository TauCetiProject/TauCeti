/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases

/-!
# The weighted strip of two-variable exponents

For natural numbers `B` and `N`, the weighted strip is the set of exponents
`{μ : Fin 2 →₀ ℕ | μ 0 < B ∧ μ 0 + B * μ 1 < N}`. Polynomials in `Z = X 0` and `W = X 1` supported
on it have `Z`-degree below `B` (`MvPolynomial.degreeOf_lt_of_mem_restrictSupport`), which is the
condition under which the power substitution `Z ↦ X, W ↦ X ^ B` is injective, and their image
under that substitution has degree below `N`. This file records that the strip is finite, so that
`MvPolynomial.restrictSupport R` of it is a finite polynomial space.

## Main results

* `MvPolynomial.finite_weightedStrip`: the weighted strip is finite.
-/

public section

namespace MvPolynomial

/-- The weighted strip `{μ | μ 0 < B ∧ μ 0 + B * μ 1 < N}` of two-variable exponents is
finite. -/
theorem finite_weightedStrip (B N : ℕ) :
    {μ : Fin 2 →₀ ℕ | μ 0 < B ∧ μ 0 + B * μ 1 < N}.Finite := by
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun _ : Fin 2 ↦ N)).subset
    fun μ ⟨h0, h1⟩ ↦ ?_
  -- Both entries are at most `N`: `μ 1 ≤ B * μ 1` because `B > μ 0 ≥ 0`.
  have hB : 0 < B := by omega
  have := Nat.le_mul_of_pos_left (μ 1) hB
  intro i
  fin_cases i <;> simp <;> omega

end MvPolynomial
