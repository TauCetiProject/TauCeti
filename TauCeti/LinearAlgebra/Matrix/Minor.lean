/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Algebra.BigOperators.Finset.Pairs

/-!
# Minors on a pair of rows and a pair of columns

A `2 × 2` minor of a matrix is the determinant of the submatrix on an ordered pair of rows and an
ordered pair of columns. `Matrix.pairMinor` names it, so that a family of such minors can be
indexed by pairs rather than by `Fin 2`-valued reindexing functions, and
`Matrix.pairMinor_mul` is the Cauchy--Binet expansion of a minor of a product, summing over the
increasing pairs of the middle index type.

The rows and the columns are indexed independently: a `2 × 2` minor makes sense for a rectangular
matrix, and the square case specializes.

The middle index type of Cauchy--Binet is linearly ordered, which is how the unordered pairs it
sums over are named without choosing representatives: each is written as the increasing one. The
sign of a minor depends on the order of its two indices, so some such choice is needed for the
statement to be sign-correct.

## Main definitions

* `Matrix.pairMinor`: the `2 × 2` minor on an ordered row pair and an ordered column pair.

## Main results

* `Matrix.pairMinor_eq`: the minor written out as a difference of two products, with
  `Matrix.pairMinor_self_left`, `Matrix.pairMinor_self_right`, `Matrix.pairMinor_swap_left`,
  `Matrix.pairMinor_swap_right` and `Matrix.pairMinor_transpose` for its behaviour under repeated
  indices, transposed pairs, and transposition.
* `Matrix.pairMinor_map`: a ring morphism carries a minor to the minor of the mapped
  matrix.
* `Matrix.pairMinor_mul`: Cauchy--Binet, expanding a minor of a product over the increasing pairs
  of the middle index type.
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

/-- A minor with a repeated row index vanishes. -/
@[simp]
theorem pairMinor_self_left (g : Matrix m n R) (a : m) (q : n × n) :
    pairMinor g (a, a) q = 0 := by
  simp only [pairMinor_eq]
  ring

/-- A minor with a repeated column index vanishes. -/
@[simp]
theorem pairMinor_self_right (g : Matrix m n R) (p : m × m) (b : n) :
    pairMinor g p (b, b) = 0 := by
  simp only [pairMinor_eq]
  ring

-- The two swap lemmas are deliberately not `@[simp]`: each rewrites a minor to the negation of the
-- minor on the transposed pair, which matches the same pattern again, so simp would not terminate.
/-- Swapping the two row indices negates the minor. -/
theorem pairMinor_swap_left (g : Matrix m n R) (a b : m) (q : n × n) :
    pairMinor g (b, a) q = -pairMinor g (a, b) q := by
  simp only [pairMinor_eq]
  ring

/-- Swapping the two column indices negates the minor. -/
theorem pairMinor_swap_right (g : Matrix m n R) (p : m × m) (a b : n) :
    pairMinor g p (b, a) = -pairMinor g p (a, b) := by
  simp only [pairMinor_eq]
  ring

/-- A minor of the transpose is the minor of the matrix with the row and column pairs
exchanged. -/
@[simp]
theorem pairMinor_transpose (g : Matrix m n R) (p : m × m) (q : n × n) :
    pairMinor gᵀ q p = pairMinor g p q := by
  simp [pairMinor_eq, Matrix.transpose_apply]
  ring

/-- A ring morphism carries a minor to the minor of the mapped matrix. -/
@[simp]
theorem pairMinor_map {S : Type*} [CommRing S] (f : R →+* S) (g : Matrix m n R)
    (p : m × m) (q : n × n) : pairMinor (g.map f) p q = f (pairMinor g p q) := by
  simp [pairMinor_eq]

/-- **Cauchy--Binet for `2 × 2` minors.** A minor of a product is the sum, over the increasing
pairs of the middle index type, of the products of the corresponding minors of the two factors. -/
theorem pairMinor_mul {l : Type*} [Fintype l] [LinearOrder l] (g : Matrix m l R)
    (h : Matrix l n R) (p : m × m) (q : n × n) :
    pairMinor (g * h) p q =
      ∑ ij ∈ {ij : l × l | ij.1 < ij.2}, pairMinor g p ij * pairMinor h ij q := by
  classical
  have hsum : pairMinor (g * h) p q =
      ∑ ij : l × l, g p.1 ij.1 * g p.2 ij.2 * pairMinor h ij q := by
    simp only [pairMinor_eq, Matrix.mul_apply, Finset.sum_mul_sum, ← Finset.sum_product',
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ij _ => by ring
  rw [hsum, TauCeti.sum_univ_prod_eq_sum_lt_add_swap _ fun a => by simp [pairMinor_eq]; ring]
  exact Finset.sum_congr rfl fun ij _ => by simp [pairMinor_eq, Prod.swap]; ring


/-- **Cauchy--Binet across a four-element middle index type**, with the six increasing pairs
written out. This is the shape the rank-two symplectic calculation consumes. -/
theorem pairMinor_mul_fin_four (g : Matrix m (Fin 4) R) (h : Matrix (Fin 4) n R)
    (p : m × m) (q : n × n) :
    pairMinor (g * h) p q =
      pairMinor g p (0, 1) * pairMinor h (0, 1) q +
        pairMinor g p (0, 2) * pairMinor h (0, 2) q +
        pairMinor g p (0, 3) * pairMinor h (0, 3) q +
        pairMinor g p (1, 2) * pairMinor h (1, 2) q +
        pairMinor g p (1, 3) * pairMinor h (1, 3) q +
        pairMinor g p (2, 3) * pairMinor h (2, 3) q := by
  rw [pairMinor_mul, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, Fin.lt_def]
  norm_num
  ring

end Matrix
