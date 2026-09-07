/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Minors on a pair of rows and a pair of columns

A `2 × 2` minor of a matrix is the determinant of the submatrix on an ordered pair of rows and an
ordered pair of columns. `Matrix.pairMinor` names it, so that a family of such minors can be
indexed by pairs rather than by `Fin 2`-valued reindexing functions, and
`Matrix.pairMinor_mul` is the Cauchy--Binet expansion of a minor of a product whose middle
index type has four elements.

The rows and the columns are indexed independently: a `2 × 2` minor makes sense for a rectangular
matrix, and the square case specializes.

Cauchy--Binet is stated only for a four-element middle index type, where the six index pairs can be
written out. That is the shape its consumers need, and a statement summing over
`Finset.powersetCard 2` of an arbitrary middle type is a different theorem, not a generalization
this file postpones.

## Main definitions

* `Matrix.pairMinor`: the `2 × 2` minor on an ordered row pair and an ordered column pair.

## Main results

* `Matrix.pairMinor_eq`: the minor written out as a difference of two products.
* `Matrix.pairMinor_map`: a ring morphism carries a minor to the minor of the mapped
  matrix.
* `Matrix.pairMinor_mul`: Cauchy--Binet, expanding a minor of a product over the six index
  pairs of a four-element middle type.
-/

public section

namespace Matrix

universe u

variable {m n : Type*} {R : Type u} [CommRing R]

/-- The `2 × 2` minor of a matrix on the ordered row pair `p` and the ordered column pair `q`. -/
def pairMinor (g : Matrix m n R) (p : m × m) (q : n × n) : R :=
  (g.submatrix ![p.1, p.2] ![q.1, q.2]).det

/-- The `2 × 2` minor written out. -/
theorem pairMinor_eq (g : Matrix m n R) (p : m × m) (q : n × n) :
    pairMinor g p q = g p.1 q.1 * g p.2 q.2 - g p.1 q.2 * g p.2 q.1 := by
  rw [pairMinor, Matrix.det_fin_two]
  simp

/-- A ring morphism carries a minor to the minor of the mapped matrix. -/
@[simp]
theorem pairMinor_map {S : Type*} [CommRing S] (f : R →+* S) (g : Matrix m n R)
    (p : m × m) (q : n × n) : pairMinor (g.map f) p q = f (pairMinor g p q) := by
  simp [pairMinor_eq]

/-- **Cauchy--Binet for `2 × 2` minors across a four-element middle index type.** -/
theorem pairMinor_mul (g : Matrix m (Fin 4) R) (h : Matrix (Fin 4) n R)
    (p : m × m) (q : n × n) :
    pairMinor (g * h) p q =
      pairMinor g p (0, 1) * pairMinor h (0, 1) q +
        pairMinor g p (0, 2) * pairMinor h (0, 2) q +
        pairMinor g p (0, 3) * pairMinor h (0, 3) q +
        pairMinor g p (1, 2) * pairMinor h (1, 2) q +
        pairMinor g p (1, 3) * pairMinor h (1, 3) q +
        pairMinor g p (2, 3) * pairMinor h (2, 3) q := by
  simp only [pairMinor_eq, Matrix.mul_apply, Fin.sum_univ_four]
  ring

end Matrix
