/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Regular.Defs
public import TauCeti.Algebra.BigOperators.Finset.Pairs

import Mathlib.Algebra.Regular.Pow

/-!
# Pair minors and principal minors

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

A principal minor of a square matrix, indexed by an arbitrary (possibly infinite) type, is the
determinant of its restriction to the rows and columns indexed by a finite set of indices.
`Matrix.principalMinor` names it; it is the building block of the principal-minor series
`det (1 - T A)` in `TauCeti.Analysis.Matrix.CharPowerSeries.Basic`.

## Main definitions

* `Matrix.pairMinor`: the `2 × 2` minor on an ordered row pair and an ordered column pair.
* `Matrix.principalMinor`: the principal minor on a finite set of indices.

## Main results

* `Matrix.pairMinor_eq`: the minor written out as a difference of two products, with
  `Matrix.pairMinor_self_left`, `Matrix.pairMinor_self_right`, `Matrix.pairMinor_swap_left`,
  `Matrix.pairMinor_swap_right` and `Matrix.pairMinor_transpose` for its behaviour under repeated
  indices, transposed pairs, and transposition.
* `Matrix.pairMinor_map`: a ring morphism carries a minor to the minor of the mapped
  matrix.
* `Matrix.pairMinor_mul`: Cauchy--Binet, expanding a minor of a product over the increasing pairs
  of the middle index type.
* `Matrix.principalMinor_empty`: the empty principal minor is `1`.
* `Matrix.principalMinor_submatrix`: principal minors of a restriction along an embedding of
  index types, in particular their invariance under reindexing.
* `Matrix.principalMinor_transpose`, `Matrix.principalMinor_map`, `Matrix.principalMinor_smul`:
  principal minors under transposition, ring morphisms and scaling.
* `Matrix.principalMinor_eq_zero_of_row_eq_zero`: a principal minor through a vanishing row is
  zero.
* `Matrix.principalMinor_eq_of_diagonal_intertwining`: principal minors are unchanged by
  intertwining with a diagonal matrix whose entries are regular.
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

section Principal

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The principal minor of `A` on a finite set `s` of indices: the determinant of the
restriction of `A` to the rows and columns indexed by `s`. -/
def principalMinor (A : Matrix ι ι R) (s : Finset ι) : R :=
  (A.submatrix (Subtype.val : s → ι) Subtype.val).det

theorem principalMinor_def (A : Matrix ι ι R) (s : Finset ι) :
    A.principalMinor s = (A.submatrix (Subtype.val : s → ι) Subtype.val).det := (rfl)

@[simp]
theorem principalMinor_empty (A : Matrix ι ι R) : A.principalMinor ∅ = 1 := by
  rw [principalMinor_def, det_isEmpty]

/-- A principal minor of the restriction of `A` along an embedding `e` of index types is the
principal minor of `A` on the image of the indices under `e`. In particular, principal minors are
invariant under reindexing the rows and columns by the same equivalence. -/
theorem principalMinor_submatrix (A : Matrix κ κ R) (e : ι ↪ κ) (s : Finset ι) :
    (A.submatrix e e).principalMinor s = A.principalMinor (s.map e) := by
  rw [principalMinor_def, principalMinor_def,
    ← det_submatrix_equiv_self (s.equivMap e) (A.submatrix Subtype.val Subtype.val),
    submatrix_submatrix, submatrix_submatrix]
  rfl

/-- Principal minors are unchanged by transposition. -/
@[simp]
theorem principalMinor_transpose (A : Matrix ι ι R) (s : Finset ι) :
    Aᵀ.principalMinor s = A.principalMinor s := by
  rw [principalMinor_def, principalMinor_def, ← transpose_submatrix, det_transpose]

/-- A ring morphism carries a principal minor to the principal minor of the mapped matrix. -/
@[simp]
theorem principalMinor_map {S : Type*} [CommRing S] (f : R →+* S) (A : Matrix ι ι R)
    (s : Finset ι) : (A.map f).principalMinor s = f (A.principalMinor s) := by
  rw [principalMinor_def, principalMinor_def, RingHom.map_det, RingHom.mapMatrix_apply,
    submatrix_map]

/-- Scaling a matrix by `c` scales its principal minor on `s` by `c ^ #s`. -/
@[simp]
theorem principalMinor_smul (c : R) (A : Matrix ι ι R) (s : Finset ι) :
    (c • A).principalMinor s = c ^ s.card * A.principalMinor s := by
  rw [principalMinor_def, principalMinor_def, ← Fintype.card_coe s, ← det_smul]
  congr 1

/-- A principal minor vanishes on a set containing an index whose row vanishes on that set. -/
theorem principalMinor_eq_zero_of_row_eq_zero {A : Matrix ι ι R} {s : Finset ι} {i : ι}
    (hi : i ∈ s) (h : ∀ j ∈ s, A i j = 0) : A.principalMinor s = 0 :=
  det_eq_zero_of_row_eq_zero ⟨i, hi⟩ fun j ↦ h j j.2

/-- Diagonal intertwining with regular entries preserves principal minors. The pointwise
relation expresses `A D = D B` without requiring the index type to be finite. The diagonal
entries need not be units, and the coefficient ring may have zero divisors. -/
theorem principalMinor_eq_of_diagonal_intertwining {A B : Matrix ι ι R} {d : ι → R}
    (s : Finset ι) (hd : ∀ i : s, IsRegular (d i))
    (h : ∀ i j : s, A i j * d j = d i * B i j) :
    A.principalMinor s = B.principalMinor s := by
  rw [principalMinor_def, principalMinor_def]
  apply (IsRegular.prod (s := Finset.univ) (f := fun i : s ↦ d i) fun i _ ↦ hd i).left
  dsimp only
  have hmatrix :
      Matrix.of (fun i j : s ↦ d j * A i j) = Matrix.of (fun i j : s ↦ d i * B i j) := by
    ext i j
    exact (mul_comm _ _).trans (h i j)
  rw [← det_mul_row (fun i : s ↦ d i) (A.submatrix Subtype.val Subtype.val),
    ← det_mul_column (fun i : s ↦ d i) (B.submatrix Subtype.val Subtype.val)]
  exact congrArg Matrix.det hmatrix

end Principal

end Matrix
