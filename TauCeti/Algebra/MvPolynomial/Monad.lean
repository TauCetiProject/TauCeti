/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Total degree under substitution

Substituting polynomials of total degree at most `D` for the variables of a polynomial `p`
multiplies the total degree by at most `D`. This bounds the degrees of polynomial expressions
after a change of generators of a finitely generated algebra.

## Main results

* `MvPolynomial.totalDegree_bind₁_le`: if every `f i` has total degree at most `D`, then
  `bind₁ f p` has total degree at most `p.totalDegree * D`.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- Substituting polynomials of total degree at most `D` for the variables multiplies the total
degree by at most `D`. -/
theorem totalDegree_bind₁_le {f : σ → MvPolynomial τ R} {D : ℕ}
    (hf : ∀ i, (f i).totalDegree ≤ D) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree * D := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs ↦ ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ s.support, (f i ^ s i).totalDegree ≤ ∑ i ∈ s.support, s i * D :=
        Finset.sum_le_sum fun i _ ↦ (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i))
    _ = (s.sum fun _ e ↦ e) * D := by rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ p.totalDegree * D := Nat.mul_le_mul_right _ (le_totalDegree hs)

end MvPolynomial
