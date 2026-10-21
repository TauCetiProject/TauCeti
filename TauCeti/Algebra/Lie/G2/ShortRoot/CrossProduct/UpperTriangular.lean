/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Basic

/-!
# Diagonal parts of upper-triangular cross-product automorphisms

In the ordered seven-dimensional weight basis, a nonzero coefficient of the type-`G₂`
cross product has indices satisfying `i + 3 = k + j`, where `k` and `j` are the inputs
and `i` is the output. Upper-triangular matrices preserve the associated filtration.
Their diagonal parts therefore preserve the cross product whenever the matrices do.

This gives the diagonal equations needed to separate an upper-triangular carrier point
into its weight-torus and upper-unitriangular factors. The statement does not require
invertibility, a field, or a characteristic restriction.

The cross-product table and normalization are those of
`TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Basic`.
-/

public section

open Matrix

namespace TauCeti.G2ShortRoot

variable {R : Type*} [CommRing R]

private theorem crossOperator_eq_zero_of_degree_ne (k i j : Fin 7)
    (h : (i : ℕ) + 3 ≠ (k : ℕ) + j) : crossOperator k i j = 0 := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num at h <;> norm_num [crossOperator_def]

private theorem diagonal_cross_entry_of_isUpperTriangular
    {g : Matrix (Fin 7) (Fin 7) R} (htri : g.IsUpperTriangular)
    (hcross : PreservesG2Cross g) (k i j : Fin 7)
    (hdeg : (i : ℕ) + 3 = (k : ℕ) + j) :
    g i i * (crossOperator k i j : R) =
      g k k * (crossOperator k i j : R) * g j j := by
  have h := congrFun (congrFun ((preservesG2Cross_def g).mp hcross k) i) j
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul] at h
  have hleft : ∑ b : Fin 7, g i b * (crossOperator k b j : R) =
      g i i * (crossOperator k i j : R) := by
    apply Finset.sum_eq_single i
    · intro b _ hbi
      rw [crossOperator_eq_zero_of_degree_ne k b j (by
        intro hb
        apply hbi
        apply Fin.ext
        omega), Int.cast_zero, mul_zero]
    · simp
  have hright : ∑ b : Fin 7, (∑ a : Fin 7,
      g a k * (crossOperator a i b : R)) * g b j =
      g k k * (crossOperator k i j : R) * g j j := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single k]
    · apply Finset.sum_eq_single j
      · intro b _ hbj
        rw [crossOperator_eq_zero_of_degree_ne k i b (by
          intro hb
          apply hbj
          apply Fin.ext
          omega), Int.cast_zero, mul_zero, zero_mul]
      · simp
    · intro a _ hak
      apply Finset.sum_eq_zero
      intro b _
      by_cases hka : k < a
      · rw [htri hka, zero_mul, zero_mul]
      by_cases hjb : j < b
      · rw [htri hjb, mul_zero]
      · rw [crossOperator_eq_zero_of_degree_ne a i b (by
          intro hab
          apply hak
          apply Fin.ext
          simp only [Fin.lt_def] at hka hjb
          omega), Int.cast_zero, mul_zero, zero_mul]
    · simp
  rw [hleft, hright] at h
  exact h

/-- The diagonal part of an upper-triangular matrix preserving the type-`G₂` cross product
also preserves that cross product, over any commutative ring. -/
theorem preservesG2Cross_diagonal_of_isUpperTriangular
    {g : Matrix (Fin 7) (Fin 7) R} (htri : g.IsUpperTriangular)
    (hcross : PreservesG2Cross g) : PreservesG2Cross (diagonal fun i ↦ g i i) := by
  rw [preservesG2Cross_def]
  intro k
  ext i j
  simp only [diagonal_mul, mul_diagonal, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp only [diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  by_cases hdeg : (i : ℕ) + 3 = (k : ℕ) + j
  · exact diagonal_cross_entry_of_isUpperTriangular htri hcross k i j hdeg
  · rw [crossOperator_eq_zero_of_degree_ne k i j hdeg, Int.cast_zero]
    simp

end TauCeti.G2ShortRoot
