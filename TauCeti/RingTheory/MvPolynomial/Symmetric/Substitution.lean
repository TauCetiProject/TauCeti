/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Substitution in symmetric multivariate polynomials

Substituting into a symmetric multivariate polynomial a family of polynomials that is permuted
along with the variables, for instance the same univariate polynomial in every variable,
preserves symmetry. For finitely many variables over a commutative ring, Mathlib's fundamental
theorem of symmetric polynomials (`MvPolynomial.esymmAlgHom_surjective`) then expresses the
substituted polynomial in the elementary symmetric polynomials.

## Main declarations

* `MvPolynomial.IsSymmetric.bind₁`: substituting an equivariant family of polynomials preserves
  symmetry.
* `MvPolynomial.IsSymmetric.bind₁_aeval_X`: uniform univariate substitution preserves
  symmetry.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {p : MvPolynomial σ R}

/-- Substituting into a symmetric polynomial a family of polynomials `f` that is equivariant
under permutations of the variables, `rename e (f i) = f (e i)`, yields a symmetric
polynomial. -/
protected theorem IsSymmetric.bind₁ (hp : p.IsSymmetric) {f : σ → MvPolynomial σ R}
    (hf : ∀ (e : Equiv.Perm σ) (i : σ), rename e (f i) = f (e i)) :
    (bind₁ f p).IsSymmetric := fun e => by
  conv_rhs => rw [← hp e, bind₁_rename, Function.comp_def]
  simp_rw [rename_bind₁, hf]

/-- Substituting the same univariate polynomial into every variable of a symmetric multivariate
polynomial preserves symmetry. -/
theorem IsSymmetric.bind₁_aeval_X (hp : p.IsSymmetric) (q : Polynomial R) :
    (bind₁ (fun i => Polynomial.aeval (X i) q) p).IsSymmetric :=
  hp.bind₁ fun e i => by rw [← Polynomial.aeval_algHom_apply, rename_X]

end MvPolynomial
