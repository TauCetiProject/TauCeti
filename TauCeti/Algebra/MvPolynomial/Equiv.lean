/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Singling out an arbitrary variable of a polynomial ring in `n + 1` variables

Mathlib's `MvPolynomial.finSuccEquiv` identifies `R[X₀, …, Xₙ]` with the polynomial ring in the
variable `X₀` over `R[X₁, …, Xₙ]`. This file does the same with an arbitrary variable `Xₚ`
singled out: the remaining variables are indexed by `Fin n` through `p.succAbove`, as in the
equivalence `finSuccEquiv' p : Fin (n + 1) ≃ Option (Fin n)`.

This is the form in which a polynomial ring acquires one new variable in the middle of its
list, as happens to the coefficient ring of a grid complex when a grid diagram is stabilized.

## Main definitions

* `MvPolynomial.finSuccEquiv'`: the `R`-algebra isomorphism
  `R[X₀, …, Xₙ] ≃ R[X_{p.succAbove 0}, …, X_{p.succAbove (n-1)}][Xₚ]`.

## Main results

* `MvPolynomial.finSuccEquiv'_X_self`, `MvPolynomial.finSuccEquiv'_rename_succAbove`: the
  singled-out variable goes to the polynomial variable, and the others are constants.
* `MvPolynomial.finSuccEquiv'_zero`: for `p = 0` this is Mathlib's `MvPolynomial.finSuccEquiv`.
-/

public section

namespace MvPolynomial

variable (R : Type*) [CommSemiring R] {n : ℕ}

/-- The `R`-algebra isomorphism between polynomials in the variables `Fin (n + 1)` and
polynomials in the variable `X p` over the polynomials in the other variables, which are indexed
by `Fin n` through `p.succAbove`. -/
noncomputable def finSuccEquiv' (p : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv' p)).trans (optionEquivLeft R (Fin n))

variable {R}

/-- The singled-out variable becomes the polynomial variable. -/
@[simp]
theorem finSuccEquiv'_X_self (p : Fin (n + 1)) : finSuccEquiv' R p (X p) = Polynomial.X := by
  simp [finSuccEquiv', optionEquivLeft_X_none]

/-- A variable other than the singled-out one becomes a constant. -/
@[simp]
theorem finSuccEquiv'_X_succAbove (p : Fin (n + 1)) (i : Fin n) :
    finSuccEquiv' R p (X (p.succAbove i)) = Polynomial.C (X i) := by
  simp [finSuccEquiv', optionEquivLeft_X_some]

/-- Polynomials not involving the singled-out variable become constants. -/
@[simp]
theorem finSuccEquiv'_rename_succAbove (p : Fin (n + 1)) (f : MvPolynomial (Fin n) R) :
    finSuccEquiv' R p (rename p.succAbove f) = Polynomial.C f := by
  have : ((finSuccEquiv' R p).toAlgHom.comp (rename p.succAbove) :
      MvPolynomial (Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin n) R)) = Polynomial.CAlgHom :=
    algHom_ext fun i => by simp
  exact DFunLike.congr_fun this f

/-- The polynomial variable comes from the singled-out variable. -/
@[simp]
theorem finSuccEquiv'_symm_X (p : Fin (n + 1)) :
    (finSuccEquiv' R p).symm Polynomial.X = X p :=
  (finSuccEquiv' R p).symm_apply_eq.mpr (finSuccEquiv'_X_self p).symm

/-- The constants come from the polynomials in the other variables. -/
@[simp]
theorem finSuccEquiv'_symm_C (p : Fin (n + 1)) (f : MvPolynomial (Fin n) R) :
    (finSuccEquiv' R p).symm (Polynomial.C f) = rename p.succAbove f :=
  (finSuccEquiv' R p).symm_apply_eq.mpr (finSuccEquiv'_rename_succAbove p f).symm

/-- Singling out the variable `X 0` is `MvPolynomial.finSuccEquiv`. -/
theorem finSuccEquiv'_zero : finSuccEquiv' R (0 : Fin (n + 1)) = finSuccEquiv R n := by
  rw [finSuccEquiv', finSuccEquiv, _root_.finSuccEquiv'_zero]

end MvPolynomial
