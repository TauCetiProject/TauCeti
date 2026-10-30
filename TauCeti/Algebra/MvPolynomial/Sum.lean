/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Evaluation after separating two families of variables

`MvPolynomial.eval₂_sumAlgEquiv` evaluates a polynomial after one family of variables
has been moved into the coefficient ring by Mathlib's `MvPolynomial.sumAlgEquiv`.
This permits coefficient extraction with respect to one family while retaining polynomial
dependence on the other.
-/

public section

namespace MvPolynomial

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluating the two variable families separately agrees with joint evaluation. -/
theorem eval₂_sumAlgEquiv (f : R →+* S) (x : σ → S) (y : τ → S)
    (p : MvPolynomial (σ ⊕ τ) R) :
    eval₂ (eval₂Hom f y) x (sumAlgEquiv R σ τ p) = eval₂ f (Sum.elim x y) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [hp]

end MvPolynomial
