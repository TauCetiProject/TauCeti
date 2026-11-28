/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.MvPolynomial.DeterminantalIdeal
public import TauCeti.RingTheory.MvPolynomial.Rescale

/-!
# Substituting `z * X` for a rectangular generic matrix

Let `R` be a commutative semiring and `z : Matrix m' m R` a rectangular matrix. Write `X` for the
generic `m × n` matrix, whose entries are the variables of `MvPolynomial (m × n) R`. The algebra
map `Matrix.mvPolynomialMulLeft z` from `MvPolynomial (m' × n) R` to `MvPolynomial (m × n) R`
replaces the variables of the generic `m' × n` matrix by the entries of the `m' × n` matrix
`z * X`. It acts on the rows only, so it commutes with renaming the columns, and it turns a product
`g * z` into the composite of the two substitutions in the opposite order. Evaluating the image of
`f` at a matrix `Y` evaluates `f` at `z * Y`.

This is the action of matrices on the rows of the polynomial model of the dual Weyl modules
(`TauCeti.DualWeylModule.mvPolynomialMulLeft_mem_dualWeylModule`).

## Main definitions

* `Matrix.mvPolynomialMulLeft z`: the algebra map from `MvPolynomial (m' × n) R` to
  `MvPolynomial (m × n) R` replacing the generic `m' × n` matrix by `z * X`.

## Main results

* `Matrix.aeval_mvPolynomialMulLeft`, `Matrix.mvPolynomialMulLeft_mul` and
  `Matrix.map_mvPolynomialMulLeft`: evaluation, composition and change of coefficients.
* `Matrix.mvPolynomialMulLeft_diagonal`: a diagonal matrix rescales the rows.
* `Matrix.mvPolynomialMulLeft_mvPolynomialMinor`: a square `g` multiplies a maximal minor by
  `det g`.
-/

public section

open MvPolynomial

namespace Matrix

variable {R : Type*} [CommSemiring R] {m m' m'' n n' : Type*} [Fintype m]

/-- The substitution of `z * X` for a rectangular matrix `z : Matrix m' m R`, `X` the generic
`m × n` matrix: the algebra map from `MvPolynomial (m' × n) R` to `MvPolynomial (m × n) R` replacing
the variable `X (b, s)` of the generic `m' × n` matrix by the entry `∑ a, z b a * X (a, s)` of
`z * X`. -/
noncomputable def mvPolynomialMulLeft (z : Matrix m' m R) :
    MvPolynomial (m' × n) R →ₐ[R] MvPolynomial (m × n) R :=
  aeval fun p ↦ (z.map C * mvPolynomialX m n R : Matrix m' n (MvPolynomial (m × n) R)) p.1 p.2

/-- The defining formula of `Matrix.mvPolynomialMulLeft`. -/
theorem mvPolynomialMulLeft_def (z : Matrix m' m R) :
    mvPolynomialMulLeft (n := n) z = aeval fun p ↦
      (z.map C * mvPolynomialX m n R : Matrix m' n (MvPolynomial (m × n) R)) p.1 p.2 :=
  (rfl)

/-- The substitution of `z * X` replaces the variable `X (b, s)` by `∑ a, z b a * X (a, s)`. -/
@[simp]
theorem mvPolynomialMulLeft_X (z : Matrix m' m R) (p : m' × n) :
    mvPolynomialMulLeft z (X p) = ∑ a, C (z p.1 a) * X (a, p.2) := by
  simp [mvPolynomialMulLeft_def, Matrix.mul_apply]

/-- Evaluating `f (z * X)` at a matrix `Y` over an `R`-algebra evaluates `f` at `z * Y`. -/
theorem aeval_mvPolynomialMulLeft {S : Type*} [CommSemiring S] [Algebra R S] (z : Matrix m' m R)
    (Y : Matrix m n S) (f : MvPolynomial (m' × n) R) :
    aeval (fun p ↦ Y p.1 p.2) (mvPolynomialMulLeft z f) =
      aeval (fun p ↦ (z.map (algebraMap R S) * Y) p.1 p.2) f := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun p ↦ ?_
  simp [Matrix.mul_apply]

/-- Evaluating `f (z * X)` at a matrix `Y` over `R` evaluates `f` at `z * Y`. -/
theorem eval_mvPolynomialMulLeft (z : Matrix m' m R) (Y : Matrix m n R)
    (f : MvPolynomial (m' × n) R) :
    eval (fun p ↦ Y p.1 p.2) (mvPolynomialMulLeft z f) = eval (fun p ↦ (z * Y) p.1 p.2) f := by
  simpa using aeval_mvPolynomialMulLeft z Y f

/-- Substituting `1 * X` is the identity. -/
@[simp]
theorem mvPolynomialMulLeft_one [DecidableEq m] :
    mvPolynomialMulLeft (n := n) (1 : Matrix m m R) = AlgHom.id R (MvPolynomial (m × n) R) :=
  algHom_ext fun p ↦ by simp [Matrix.one_apply]

/-- Substituting `g * X` and then `z * X` substitutes `(g * z) * X`. -/
theorem mvPolynomialMulLeft_mul [Fintype m'] (g : Matrix m'' m' R) (z : Matrix m' m R) :
    mvPolynomialMulLeft (n := n) (g * z) = (mvPolynomialMulLeft z).comp (mvPolynomialMulLeft g) :=
  algHom_ext fun p ↦ by
    simp only [mvPolynomialMulLeft_X, AlgHom.comp_apply, map_sum, map_mul, algHom_C,
      algebraMap_eq, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

/-- Changing coefficients commutes with the substitution of `z * X`. -/
theorem map_mvPolynomialMulLeft {S : Type*} [CommSemiring S] (φ : R →+* S) (z : Matrix m' m R)
    (f : MvPolynomial (m' × n) R) :
    MvPolynomial.map φ (mvPolynomialMulLeft z f) =
      mvPolynomialMulLeft (z.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [mvPolynomialMulLeft_def]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f p hf => simp [hf]

/-- Renaming the columns commutes with the substitution of `z * X`, which acts on the rows. -/
theorem mvPolynomialMulLeft_rename (z : Matrix m' m R) (e : n → n')
    (f : MvPolynomial (m' × n) R) :
    mvPolynomialMulLeft z (rename (Prod.map id e) f) =
      rename (Prod.map id e) (mvPolynomialMulLeft z f) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun p ↦ ?_
  simp

/-- Substituting `diagonal x * X` rescales the variables of the row `a` by `x a`. -/
theorem mvPolynomialMulLeft_diagonal [DecidableEq m] (x : m → R) :
    mvPolynomialMulLeft (n := n) (diagonal x) = rescale fun p ↦ x p.1 :=
  algHom_ext fun p ↦ by simp [diagonal_apply, apply_ite C, ite_mul, Finset.sum_ite_eq]

/-- Substituting `g * X` for a square matrix `g` multiplies the minor of `X` on all rows and the
columns `c` by `det g`. -/
theorem mvPolynomialMulLeft_mvPolynomialMinor {R : Type*} [CommRing R] [DecidableEq m]
    (g : Matrix m m R) (c : m → n) :
    mvPolynomialMulLeft g (mvPolynomialMinor R id c) = C g.det * mvPolynomialMinor R id c := by
  rw [mvPolynomialMulLeft_def, aeval_mvPolynomialMinor,
    submatrix_mul _ _ _ id _ Function.bijective_id, det_mul]
  simp [mvPolynomialMinor_eq_det_submatrix, RingHom.map_det]

end Matrix
