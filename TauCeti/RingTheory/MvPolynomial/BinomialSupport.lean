/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Binary forms with binomial support

In two variables `x = X 0` and `y = X 1`, the span of the monomials `xⁱ yʲ` of degree
`d = i + j` whose binomial coefficient `d choose i` is nonzero in `R` is the restricted-support
submodule `MvPolynomial.restrictSupport R {m | m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0}`.
This file describes its monomials and the submodules containing it.
-/

public section

namespace TauCeti

open MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- The monomial `xⁱ yʲ` lies in the span of the monomials of degree `d` with nonzero binomial
coefficient exactly when `i + j = d` and `d choose i` is nonzero. -/
theorem X_pow_mul_X_pow_mem_restrictSupport_binomial_iff [Nontrivial R] {d i j : ℕ} :
    (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) ∈
        restrictSupport R {m | m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0} ↔
      i + j = d ∧ (d.choose i : R) ≠ 0 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, monomial_mem_restrictSupport]
  simp

/-- A submodule contains the span of the monomials of degree `d` with nonzero binomial coefficient
exactly when it contains each such monomial `xⁱ yʲ`. -/
theorem restrictSupport_binomial_le_iff {d : ℕ} {p : Submodule R (MvPolynomial (Fin 2) R)} :
    restrictSupport R {m | m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0} ≤ p ↔
      ∀ i j, i + j = d → (d.choose i : R) ≠ 0 →
        (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) ∈ p := by
  rw [restrictSupport_eq_span, Submodule.span_le]
  refine ⟨fun h i j hij hi ↦ ?_, ?_⟩
  · have hm := h ⟨Finsupp.single 0 i + Finsupp.single 1 j, by simpa using ⟨hij, hi⟩, rfl⟩
    simp only [SetLike.mem_coe, monomial_fin_two, map_one, one_mul, Finsupp.add_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne zero_ne_one,
      Finsupp.single_eq_of_ne one_ne_zero, add_zero, zero_add] at hm
    exact hm
  · rintro h _ ⟨m, ⟨hmd, hm⟩, rfl⟩
    simpa [monomial_fin_two] using h _ _ hmd hm

end TauCeti
