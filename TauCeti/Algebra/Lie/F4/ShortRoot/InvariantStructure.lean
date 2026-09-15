/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Basic
public import TauCeti.LinearAlgebra.Matrix.Step

/-!
# The invariant form and the invariant multiplication of type F4

The twenty-six-dimensional short-root module of type `F₄` carries an invariant symmetric bilinear
form and an invariant symmetric multiplication `V × V → V`, each unique up to a scalar. Up to those
scalars the pair is the trace form and the trace-free part of the product of the
twenty-seven-dimensional exceptional Jordan algebra, restricted to its twenty-six-dimensional space
of trace-zero elements, and the group of type `F₄` is the joint stabilizer of the two.

This file writes both down over the integers, in the short-root weight basis of
`TauCeti.Algebra.Lie.F4.ShortRoot.Basic`. The form is recorded by its Gram matrix
`TauCeti.F4ShortRoot.invariantForm`, primitive over the integers and of determinant three; it is a
signed antidiagonal permutation away from the two zero-weight coordinates, where it is the block
with diagonal two and off-diagonal one. The multiplication is recorded by the twenty-six matrices
`TauCeti.F4ShortRoot.multiplicationOperator a`, the operator `v ↦ m (eₐ, v)`, which determine it
because it is symmetric.

Weights add along a nonzero structure constant, and every weight space of the module has dimension
at most two, so each product of two basis vectors is supported on at most two basis vectors. The
multiplication operators are therefore *double step matrices* in the sense of
`Matrix.IsDoubleStep`, and they are recorded by two target tables and two coefficient tables rather
than entry by entry.

This module defines the two tables and records that each is symmetric. It proves nothing about
their invariance, and on its own it does not pin them down: any symmetric Gram matrix and any
symmetric family of operators would satisfy every statement below. What identifies these
particular tables as the invariant structure of the type-`F₄` module is that the pinned data of
that module preserves them, and that is proved in
`TauCeti.Algebra.Lie.F4.ShortRoot.PinnedForm` and
`TauCeti.Algebra.Lie.F4.ShortRoot.PinnedMultiplication`, immediately above this file:
`TauCeti.F4ShortRoot.preservesForm_rootElementMatrix` and
`TauCeti.F4ShortRoot.preservesForm_weightTorusMatrix` for the form,
`TauCeti.F4ShortRoot.isDerivation_rootMatrix`,
`TauCeti.F4ShortRoot.preservesMultiplication_rootElementMatrix` and
`TauCeti.F4ShortRoot.preservesMultiplication_weightTorusMatrix` for the multiplication. The
separation is one of file size, not of content.

Neither the uniqueness of the form nor the uniqueness of the multiplication is proved anywhere in
this development, and no identification with the exceptional Jordan algebra is made. Only the
explicit tables and the step structure they record are used.

## Main definitions

* `TauCeti.F4ShortRoot.invariantForm`: the Gram matrix of the invariant symmetric bilinear form,
  tabulated by `TauCeti.F4ShortRoot.invariantFormEntry`.
* `TauCeti.F4ShortRoot.multiplicationOperator`: the operators of the invariant symmetric
  multiplication.

## Main results

* `TauCeti.F4ShortRoot.isDoubleStep_multiplicationOperator`: each multiplication operator has at
  most two nonzero entries in each column, at the tabulated targets and with the tabulated
  coefficients.
* `TauCeti.F4ShortRoot.transpose_invariantForm`: the Gram matrix is symmetric.
* `TauCeti.F4ShortRoot.multiplicationOperator_comm`: the multiplication is symmetric.

## References

* H. Freudenthal, *Beziehungen der `E₇` und `E₈` zur Oktavenebene I*, Indag. Math. **16** (1954),
  for the exceptional Jordan algebra and its trace form.
* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics **1**,
  Marcel Dekker (1971), §§I.3--I.4.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §7.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

/-! ## The invariant symmetric bilinear form -/

/-- The table of entries of the Gram matrix, in the short-root weight basis, of the invariant
symmetric bilinear form of the twenty-six-dimensional module of type `F₄`, taken primitive over the
integers. It pairs the coordinate of a weight with the coordinate of its negative. -/
@[expose] def invariantFormEntry : Fin 26 → Fin 26 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The Gram matrix of the invariant symmetric bilinear form. -/
def invariantForm : Matrix (Fin 26) (Fin 26) ℤ := Matrix.of invariantFormEntry

/-- The entrywise formula for the Gram matrix of the invariant form. -/
@[simp]
theorem invariantForm_apply (a b : Fin 26) : invariantForm a b = invariantFormEntry a b := by
  rw [invariantForm, Matrix.of_apply]

/-- **The invariant form is symmetric.** -/
theorem transpose_invariantForm : invariantFormᵀ = invariantForm := by
  ext a b
  rw [Matrix.transpose_apply, invariantForm_apply, invariantForm_apply]
  revert a b
  decide +kernel

/-! ## The invariant symmetric multiplication -/

/-- The first target of each column of a multiplication operator: the index of the first basis
vector in the support of the product of two basis vectors. -/
@[expose] def multTargetOne : Fin 26 → Fin 26 → Fin 26 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 4, 5, 6, 8, 10, 12],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 3, 0, 4, 0, 0, 7, 9, 11, 12, 15],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 5, 0, 6, 7, 9, 0, 0, 12, 14, 17],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 5, 0, 0, 7, 8, 0, 11, 0, 12, 0, 16, 19],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 6, 0, 8, 9, 0, 11, 0, 12, 0, 0, 18, 20],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 5, 5, 0, 7, 0, 0, 10, 0, 12, 0, 14, 16, 0, 21],
    ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 6, 6, 0, 9, 10, 0, 0, 12, 0, 14, 0, 18, 0, 22],
    ![0, 0, 0, 0, 1, 0, 2, 0, 3, 0, 5, 0, 0, 7, 0, 0, 0, 0, 12, 0, 15, 0, 17, 19, 21, 0],
    ![0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 8, 8, 10, 11, 0, 12, 0, 0, 0, 16, 18, 0, 0, 23],
    ![0, 0, 0, 1, 0, 2, 0, 0, 4, 0, 6, 0, 0, 9, 0, 0, 12, 0, 0, 15, 0, 17, 0, 20, 22, 0],
    ![0, 0, 0, 0, 0, 0, 0, 5, 0, 6, 0, 8, 10, 0, 0, 12, 0, 14, 0, 16, 18, 0, 0, 0, 0, 24],
    ![0, 0, 1, 0, 0, 3, 4, 0, 0, 0, 8, 0, 0, 11, 12, 0, 0, 15, 0, 0, 0, 19, 20, 0, 23, 0],
    ![0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 0, 12, 12, 0, 15, 0, 17, 0, 19, 20, 21, 22, 23, 24, 0],
    ![0, 1, 0, 0, 0, 5, 6, 7, 8, 9, 0, 11, 12, 12, 14, 0, 16, 17, 18, 19, 20, 0, 0, 0, 24, 25],
    ![0, 2, 0, 5, 6, 0, 0, 0, 10, 0, 0, 12, 0, 14, 0, 17, 0, 0, 0, 21, 22, 0, 0, 24, 0, 0],
    ![1, 0, 0, 0, 0, 7, 9, 0, 11, 0, 12, 0, 15, 0, 17, 0, 19, 0, 20, 0, 0, 0, 0, 0, 25, 0],
    ![0, 3, 5, 0, 8, 0, 10, 0, 0, 12, 0, 0, 0, 16, 0, 19, 0, 21, 0, 0, 23, 0, 24, 0, 0, 0],
    ![2, 0, 0, 7, 9, 0, 0, 0, 12, 0, 14, 15, 17, 17, 0, 0, 21, 0, 22, 0, 0, 0, 0, 25, 0, 0],
    ![0, 4, 6, 8, 0, 10, 0, 12, 0, 0, 0, 0, 0, 18, 0, 20, 0, 22, 0, 23, 0, 24, 0, 0, 0, 0],
    ![3, 0, 7, 0, 11, 0, 12, 0, 0, 15, 16, 0, 19, 19, 21, 0, 0, 0, 23, 0, 0, 0, 25, 0, 0, 0],
    ![4, 0, 9, 11, 0, 12, 0, 15, 0, 0, 18, 0, 20, 20, 22, 0, 23, 0, 0, 0, 0, 25, 0, 0, 0, 0],
    ![5, 7, 0, 0, 12, 0, 14, 0, 16, 17, 0, 19, 21, 0, 0, 0, 0, 0, 24, 0, 25, 0, 0, 0, 0, 0],
    ![6, 9, 0, 12, 0, 14, 0, 17, 18, 0, 0, 20, 22, 0, 0, 0, 24, 0, 0, 25, 0, 0, 0, 0, 0, 0],
    ![8, 11, 12, 0, 0, 16, 18, 19, 0, 20, 0, 0, 23, 0, 24, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0],
    ![10, 12, 14, 16, 18, 0, 0, 21, 0, 22, 0, 23, 24, 24, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![12, 15, 17, 19, 20, 21, 22, 0, 23, 0, 24, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The coefficient of the first target of each column of a multiplication operator. -/
@[expose] def multCoeffOne : Fin 26 → Fin 26 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 3, 0, 3, 3, 3, 3, 3, 3, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, -3, -3, -3, 0, -3, 0, -3, 0, 0, 3, 3, 3, 1, 3],
    ![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 3, 0, 0, 0, -3, 0, -3, -3, -3, 0, 0, 2, 3, 3],
    ![0, 0, 0, 0, 0, 0, -3, 0, 0, -3, 0, 0, 3, 0, 3, 0, 0, 3, -3, 0, -3, 0, -2, 0, 3, 3],
    ![0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 3, 0, 3, 0, 3, 3, 0, 3, 0, 2, 0, 0, 3, 3],
    ![0, 0, 0, 0, 3, 0, 0, 0, 0, -3, 0, -3, -3, -3, 0, -3, 0, 0, -3, 0, -1, 0, -3, -3, 0, 3],
    ![0, 0, 0, -3, 0, 0, 0, 3, 0, 0, 0, -3, -3, -3, 0, -3, 3, 0, 0, 1, 0, 3, 0, -3, 0, 3],
    ![0, 0, 0, 0, 3, 0, 3, 0, 3, 0, 3, 0, 0, 3, 0, 0, 0, 0, 1, 0, -3, 0, -3, -3, -3, 0],
    ![0, 0, 3, 0, 0, 0, 0, 3, 0, 3, 0, 0, -3, -3, -3, -3, 0, -1, 0, 0, 0, 3, 3, 0, 0, 3],
    ![0, 0, 0, -3, 0, -3, 0, 0, 3, 0, 3, 0, 0, 3, 0, 0, -1, 0, 0, 3, 0, 3, 0, -3, -3, 0],
    ![0, -3, 0, 0, 0, 0, 0, 3, 0, 3, 0, 3, 3, 0, 0, -2, 0, -3, 0, -3, -3, 0, 0, 0, 0, 3],
    ![0, 0, 3, 0, 0, -3, -3, 0, 0, 0, 3, 0, 0, 3, 1, 0, 0, -3, 0, 0, 0, 3, 3, 0, -3, 0],
    ![0, -3, 3, 3, 3, -3, -3, 0, -3, 0, 3, 0, -2, 2, 0, 3, 0, -3, 0, -3, -3, 3, 3, 3, -3, 0],
    ![3, -3, 0, 0, 0, -3, -3, 3, -3, 3, 0, 3, 2, 4, 3, 0, 3, -3, 3, -3, -3, 0, 0, 0, -3, 3],
    ![0, -3, 0, 3, 3, 0, 0, 0, -3, 0, 0, 1, 0, 3, 0, 3, 0, 0, 0, -3, -3, 0, 0, 3, 0, 0],
    ![3, 0, 0, 0, 0, -3, -3, 0, -3, 0, -2, 0, 3, 0, 3, 0, 3, 0, 3, 0, 0, 0, 0, 0, -3, 0],
    ![0, -3, -3, 0, 3, 0, 3, 0, 0, -1, 0, 0, 0, 3, 0, 3, 0, 3, 0, 0, -3, 0, -3, 0, 0, 0],
    ![3, 0, 0, 3, 3, 0, 0, 0, -1, 0, -3, -3, -3, -3, 0, 0, 3, 0, 3, 0, 0, 0, 0, 3, 0, 0],
    ![0, -3, -3, -3, 0, -3, 0, 1, 0, 0, 0, 0, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 0, 0, 0],
    ![3, 0, -3, 0, 3, 0, 1, 0, 0, 3, -3, 0, -3, -3, -3, 0, 0, 0, 3, 0, 0, 0, -3, 0, 0, 0],
    ![3, 0, -3, -3, 0, -1, 0, -3, 0, 0, -3, 0, -3, -3, -3, 0, -3, 0, 0, 0, 0, 3, 0, 0, 0, 0],
    ![3, 3, 0, 0, 2, 0, 3, 0, 3, 3, 0, 3, 3, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0],
    ![3, 3, 0, -2, 0, -3, 0, -3, 3, 0, 0, 3, 3, 0, 0, 0, -3, 0, 0, -3, 0, 0, 0, 0, 0, 0],
    ![3, 3, 2, 0, 0, -3, -3, -3, 0, -3, 0, 0, 3, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![3, 1, 3, 3, 3, 0, 0, -3, 0, -3, 0, -3, -3, -3, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 3, 3, 3, 3, 3, 3, 0, 3, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The second target of each column of a multiplication operator: the index of the second basis
vector in the support of the product of two basis vectors, taken to be the zeroth index when the
support has at most one element. -/
@[expose] def multTargetTwo : Fin 26 → Fin 26 → Fin 26 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The coefficient of the second target of each column of a multiplication operator. -/
@[expose] def multCoeffTwo : Fin 26 → Fin 26 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- **The operator of the invariant symmetric multiplication** of the twenty-six-dimensional
module of type `F₄`: the `b`th column of `multiplicationOperator a` lists the coordinates of the
product of the `a`th and the `b`th basis vectors. -/
def multiplicationOperator (a : Fin 26) : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.of fun c b =>
    (if c = multTargetOne a b then multCoeffOne a b else 0) +
      (if c = multTargetTwo a b then multCoeffTwo a b else 0)

/-- The entrywise formula for a multiplication operator. -/
@[simp]
theorem multiplicationOperator_apply (a c b : Fin 26) :
    multiplicationOperator a c b =
      (if c = multTargetOne a b then multCoeffOne a b else 0) +
        (if c = multTargetTwo a b then multCoeffTwo a b else 0) := by
  rw [multiplicationOperator, Matrix.of_apply]

/-- **Every multiplication operator has at most two nonzero entries in each column**, at the
tabulated targets and with the tabulated coefficients. -/
theorem isDoubleStep_multiplicationOperator (a : Fin 26) :
    (multiplicationOperator a).IsDoubleStep (multTargetOne a) (multCoeffOne a)
      (multTargetTwo a) (multCoeffTwo a) :=
  multiplicationOperator_apply a

/-- **The multiplication is symmetric**: the `b`th column of the `a`th operator is the `a`th
column of the `b`th operator. -/
theorem multiplicationOperator_comm (a b c : Fin 26) :
    multiplicationOperator a c b = multiplicationOperator b c a := by
  rw [multiplicationOperator_apply, multiplicationOperator_apply]
  revert a b c
  decide +kernel

end TauCeti.F4ShortRoot
