/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.KnotTheory.Jimbo.Enhancement.Basic

/-!
# Generic Laurent unit evaluations of Jimbo enhancement weights

Specializing Turaev's enhancement weights `TauCeti.KnotTheory.jimboWeight` at the universal unit
`LaurentPolynomial.genericUnit R` of `R[T;T⁻¹]` gives the Laurent monomials `T ^ (N - 1 - 2 * a)`
and the generic quantum dimension `[N]_T = ∑ a : Fin N, jimboWeight T a`.

For every positive `N` over a nontrivial semiring `R`, the generic quantum dimension `[N]_T` is
nonzero because the coefficient of `T ^ (N - 1)` is `1`
(`TauCeti.KnotTheory.jimboWeight_sum_genericUnit_ne_zero`). Evaluating the generic weights and
their sum along `LaurentPolynomial.eval₂ f q` recovers `jimboWeight q a` and `[N]_q` at any unit
`q : Sˣ` (`TauCeti.KnotTheory.eval₂_jimboWeight_genericUnit`,
`TauCeti.KnotTheory.eval₂_sum_jimboWeight_genericUnit`).

## Main results

* `TauCeti.KnotTheory.jimboWeight_sum_genericUnit_ne_zero`: for positive `N` over a nontrivial
  semiring, the generic quantum dimension `[N]_T` is nonzero in `R[T;T⁻¹]`.
* `TauCeti.KnotTheory.eval₂_jimboWeight_genericUnit` and
  `TauCeti.KnotTheory.eval₂_sum_jimboWeight_genericUnit`: evaluating the generic enhancement
  weights and their sum along `LaurentPolynomial.eval₂ f q` recovers the weights at `q`.

## References

* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388.
-/

public section

open scoped BigOperators

namespace TauCeti.KnotTheory

variable {N : ℕ}

/-- For positive `N` over a nontrivial semiring, the generic quantum dimension `[N]_T` in
`R[T;T⁻¹]` is nonzero. -/
theorem jimboWeight_sum_genericUnit_ne_zero (R : Type*) [Semiring R] [Nontrivial R]
    (N : ℕ) [NeZero N] :
    (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit R) a) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : LaurentPolynomial R ↦ p.coeff ((N : ℤ) - 1)) h
  simp only [jimboWeight_def, LaurentPolynomial.genericUnit_zpow_val,
    AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_zero,
    Finset.sum_apply', Finsupp.zero_apply] at hc
  have hterm : ∀ a : Fin N,
      (LaurentPolynomial.T ((N : ℤ) - 1 - 2 * (a : ℕ)) : LaurentPolynomial R).coeff
        ((N : ℤ) - 1) = if a = 0 then 1 else 0 := by
    intro a
    rw [LaurentPolynomial.T_apply]
    have hiff : (N : ℤ) - 1 - 2 * (a : ℕ) = (N : ℤ) - 1 ↔ a = 0 := by
      constructor
      · intro heq
        exact Fin.ext (by simp only [Fin.val_zero]; omega)
      · rintro rfl
        simp
    simp [hiff]
  simp_rw [hterm] at hc
  simp at hc

/-- Evaluating a generic-unit Jimbo weight at a unit `q` along any ring homomorphism gives the
Jimbo weight at `q`. -/
theorem eval₂_jimboWeight_genericUnit {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (q : Sˣ) (a : Fin N) :
    LaurentPolynomial.eval₂ f q (jimboWeight (LaurentPolynomial.genericUnit R) a) =
      jimboWeight q a := by
  simp [jimboWeight_def]

/-- Evaluating the generic quantum dimension `[N]_T` at a unit `q` along any ring homomorphism
recovers `[N]_q`. -/
theorem eval₂_sum_jimboWeight_genericUnit {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (q : Sˣ) (N : ℕ) :
    LaurentPolynomial.eval₂ f q (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit R) a) =
      ∑ a : Fin N, jimboWeight q a := by
  simp only [map_sum, eval₂_jimboWeight_genericUnit]

end TauCeti.KnotTheory
