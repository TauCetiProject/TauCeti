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

* `Matrix.pairMinor_eq`: the minor written out as a difference of two products.
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

/-- A ring morphism carries a minor to the minor of the mapped matrix. -/
@[simp]
theorem pairMinor_map {S : Type*} [CommRing S] (f : R →+* S) (g : Matrix m n R)
    (p : m × m) (q : n × n) : pairMinor (g.map f) p q = f (pairMinor g p q) := by
  simp [pairMinor_eq]

-- The summand is antisymmetric in its two middle indices and vanishes on the diagonal, so the
-- sum over all ordered pairs collapses to a sum over the increasing ones.
private theorem sum_univ_prod_eq_sum_lt {l : Type*} [Fintype l] [LinearOrder l] {M : Type*}
    [AddCommMonoid M] (F : l × l → M) (hdiag : ∀ a, F (a, a) = 0) :
    ∑ ij : l × l, F ij =
      ∑ ij ∈ {ij : l × l | ij.1 < ij.2}, (F ij + F ij.swap) := by
  classical
  have hswap : ∑ ij ∈ {ij : l × l | ij.2 < ij.1}, F ij =
      ∑ ij ∈ {ij : l × l | ij.1 < ij.2}, F ij.swap :=
    Finset.sum_nbij' (i := Prod.swap) (j := Prod.swap) (by simp) (by simp) (by simp) (by simp)
      (by simp)
  have hnot : ∑ ij ∈ {ij : l × l | ij.2 < ij.1}, F ij =
      ∑ ij ∈ {ij : l × l | ¬ ij.1 < ij.2}, F ij := by
    refine Finset.sum_subset ?_ ?_
    · intro ij hij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hij ⊢
      exact hij.le
    · rintro ⟨a, b⟩ hmem hnotmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hmem hnotmem
      exact hdiag a ▸ congrArg (fun c => F (a, c)) (le_antisymm hnotmem hmem).symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ij : l × l => ij.1 < ij.2) F,
    ← hnot, hswap, Finset.sum_add_distrib]

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
  rw [hsum, sum_univ_prod_eq_sum_lt _ fun a => by simp [pairMinor_eq]; ring]
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
