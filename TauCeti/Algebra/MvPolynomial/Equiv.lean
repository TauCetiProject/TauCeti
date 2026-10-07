/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import TauCeti.Data.Finsupp.Fin

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
* `MvPolynomial.polynomial_eval_finSuccEquiv'`: evaluating the polynomial variable at `a`
  substitutes `a` for `X p`.
* `MvPolynomial.finSuccEquiv'_zero`: for `p = 0` this is Mathlib's `MvPolynomial.finSuccEquiv`.
* `MvPolynomial.finSuccEquiv'_map`, `MvPolynomial.finSuccEquiv_map`: singling out a variable
  commutes with mapping the coefficients along a ring homomorphism.
* `MvPolynomial.polynomial_eval_map_finSuccEquiv'`, `MvPolynomial.polynomial_eval_map_finSuccEquiv`:
  specializing the other variables to a point `s` and then evaluating the polynomial variable at
  `y` is evaluating at the point obtained by inserting `y` into `s` at position `p`.

The last two results are the compatibility of this equivalence with coefficient maps and with
evaluation. They let a polynomial in `n + 1` variables be treated as a family of univariate
polynomials in `X p` parametrized by the other coordinates, with integer input mapped to the
reals either before or after the variable is singled out.

Dually, the last variable `Xₙ` can be moved into the coefficients instead, through Mathlib's
`MvPolynomial.optionEquivRight` after renaming along `finSuccEquivLast`. This identifies
`R[X₀, …, Xₙ]` with the polynomials in `X₀, …, Xₙ₋₁` whose coefficients are polynomials in `Xₙ`.
The coefficient of `Xᵘ` then has as its coefficient of `Xₙ ^ k` the coefficient of `f` at the
exponent `Finsupp.snoc u k` (`MvPolynomial.optionEquivRight_rename_finSuccEquivLast_coeff_coeff`).
This is the form used for Lazard evaluation, where the base variables are eliminated first and
the last variable is kept.
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

/-- Constants stay constant. -/
@[simp]
theorem finSuccEquiv'_C (p : Fin (n + 1)) (r : R) :
    finSuccEquiv' R p (C r) = Polynomial.C (C r) :=
  (finSuccEquiv' R p).commutes r

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

/-- Evaluating the singled-out variable at `a` is substituting `a` for `X p` and keeping the
other variables. -/
theorem polynomial_eval_finSuccEquiv' (p : Fin (n + 1)) (a : MvPolynomial (Fin n) R)
    (f : MvPolynomial (Fin (n + 1)) R) :
    Polynomial.eval a (finSuccEquiv' R p f) = aeval (Fin.insertNth p a X) f := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    rw [← algebraMap_eq, AlgEquiv.commutes, AlgHom.commutes, Polynomial.algebraMap_apply,
      Polynomial.eval_C]
  | add f g hf hg => rw [map_add, Polynomial.eval_add, hf, hg, map_add]
  | mul_X f i hf =>
    rw [map_mul, Polynomial.eval_mul, hf, map_mul, aeval_X]
    congr 1
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p i <;> simp

/-- Singling out the variable `X 0` is `MvPolynomial.finSuccEquiv`. -/
theorem finSuccEquiv'_zero : finSuccEquiv' R (0 : Fin (n + 1)) = finSuccEquiv R n := by
  rw [finSuccEquiv', finSuccEquiv, _root_.finSuccEquiv'_zero]

section Map

variable {S : Type*} [CommSemiring S]

/-- Singling out a variable commutes with mapping the coefficients along `φ`. -/
theorem finSuccEquiv'_map (φ : R →+* S) (p : Fin (n + 1)) (f : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv' S p (map φ f) = (finSuccEquiv' R p f).map (map φ) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg => simp only [map_add, Polynomial.map_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, Polynomial.map_mul, hf, map_X]
    congr 1
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p i <;> simp

/-- Mapping the coefficients along `φ` commutes with the inverse of `finSuccEquiv' R p`. -/
theorem finSuccEquiv'_symm_map (φ : R →+* S) (p : Fin (n + 1))
    (f : Polynomial (MvPolynomial (Fin n) R)) :
    (finSuccEquiv' S p).symm (f.map (map φ)) = map φ ((finSuccEquiv' R p).symm f) := by
  rw [AlgEquiv.symm_apply_eq, finSuccEquiv'_map, AlgEquiv.apply_symm_apply]

/-- Singling out the variable `X 0` commutes with mapping the coefficients along `φ`. -/
theorem finSuccEquiv_map (φ : R →+* S) (f : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv S n (map φ f) = (finSuccEquiv R n f).map (map φ) := by
  simpa only [finSuccEquiv'_zero] using finSuccEquiv'_map φ 0 f

/-- Specializing the variables other than `X p` along `φ` at the point `s`, and then evaluating
the polynomial variable at `y`, is evaluating along `φ` at the point obtained by inserting `y`
into `s` at position `p`. -/
theorem polynomial_eval_map_finSuccEquiv' (φ : R →+* S) (p : Fin (n + 1)) (s : Fin n → S)
    (y : S) (f : MvPolynomial (Fin (n + 1)) R) :
    ((finSuccEquiv' R p f).map (eval₂Hom φ s)).eval y = eval₂ φ (Fin.insertNth p y s) f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg => simp only [map_add, Polynomial.map_add, Polynomial.eval_add, hf, hg, eval₂_add]
  | mul_X f i hf =>
    simp only [map_mul, Polynomial.map_mul, Polynomial.eval_mul, hf, eval₂_mul, eval₂_X]
    congr 1
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove p i <;> simp

/-- Specializing the variables `X 1, …, X n` along `φ` at the point `s`, and then evaluating the
polynomial variable at `y`, is evaluating along `φ` at the point `Fin.cons y s`. -/
theorem polynomial_eval_map_finSuccEquiv (φ : R →+* S) (s : Fin n → S) (y : S)
    (f : MvPolynomial (Fin (n + 1)) R) :
    ((finSuccEquiv R n f).map (eval₂Hom φ s)).eval y = eval₂ φ (Fin.cons y s) f := by
  simpa only [finSuccEquiv'_zero, Fin.insertNth_zero'] using
    polynomial_eval_map_finSuccEquiv' φ 0 s y f

end Map

section Last

open Finsupp

/-- Moving the last variable into the coefficients sends the monomial `r • X ^ d` to the monomial
in the first `n` variables with exponent `init d` whose coefficient is `r • Xₙ ^ d (Fin.last n)`. -/
theorem optionEquivRight_rename_finSuccEquivLast_monomial (d : Fin (n + 1) →₀ ℕ) (r : R) :
    optionEquivRight R (Fin n) (rename finSuccEquivLast (monomial d r)) =
      monomial (init d) (Polynomial.monomial (d (Fin.last n)) r) := by
  rw [monomial_eq, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_castSucc, Fin.init, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

/-- After moving the last variable into the coefficients, the coefficient of `Xₙ ^ k` in the
coefficient of `Xᵘ` is the coefficient of `f` at the exponent `Finsupp.snoc u k`. -/
theorem optionEquivRight_rename_finSuccEquivLast_coeff_coeff (f : MvPolynomial (Fin (n + 1)) R)
    (u : Fin n →₀ ℕ) (k : ℕ) :
    ((optionEquivRight R (Fin n) (rename finSuccEquivLast f)).coeff u).coeff k =
      f.coeff (snoc u k) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    simp only [optionEquivRight_rename_finSuccEquivLast_monomial, coeff_monomial, eq_snoc_iff,
      ite_and]
    split_ifs <;> simp [Polynomial.coeff_monomial, *]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hp,
      hq]

end Last

end MvPolynomial
