/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Coefficient vectors under variable embeddings

The embedding `Polynomial.toMvPolynomial i` reindexes the native coefficient vector
by sending an exponent `n` to the multivariate exponent `Finsupp.single i n`.
This description lets coefficient constructions commute with placement in one coordinate.
-/

public section

namespace Polynomial

variable {R σ : Type*} [CommSemiring R]

/-- Placement in one coordinate reindexes the native coefficient vector by the
corresponding single-coordinate exponent embedding. -/
theorem coeff_toMvPolynomial_eq_embDomain (p : Polynomial R) (i : σ) :
    AddMonoidAlgebra.coeff (p.toMvPolynomial i) =
      p.toFinsupp.coeff.embDomain ⟨Finsupp.single i, Finsupp.single_injective i⟩ := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [_root_.map_add, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
      Finsupp.embDomain_add, hp, hq]
  | monomial n c =>
    simp [← Polynomial.C_mul_X_pow_eq_monomial, MvPolynomial.C_mul_X_pow_eq_monomial,
      ← MvPolynomial.single_eq_monomial,
      AddMonoidAlgebra.coeff_single, Finsupp.embDomain_single]

end Polynomial
