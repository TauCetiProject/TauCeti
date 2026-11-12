/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Factorization
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties

import Mathlib.Tactic.LinearCombination

/-!
# Mutation of compatible alternating forms

An alternating integral form compatible with an extended exchange matrix mutates by the
congruence `Eεᵀ * Λ * Eε`. The two signs give the same form, column compatibility retains
its original weights, and simultaneous matrix and form mutation is involutive. Compatibility
weights may be negative or zero; the positive skew-symmetrizer is separate data.

The statements use the raw compatibility equation, without requiring a particular bundled
representation of compatible pairs. Alternation uses Mathlib's bilinear-form predicate.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics 195
  (2005), §3, Propositions 3.4 and 3.6.
-/

public section

namespace TauCeti

open Matrix

variable {I K I' K' : Type*} [DecidableEq I] [Fintype I]

/-- Mutation of an integral form, using the positive-sign left mutation factor. Column
compatibility makes this independent of the choice of sign. -/
def matrixFormMutation (row : K ↪ I) (B : Matrix I K ℤ) (Λ : Matrix I I ℤ) (k : K) :
    Matrix I I ℤ :=
  (matrixMutationLeft row B k 1)ᵀ * Λ * matrixMutationLeft row B k 1

private theorem isAlt_conjugate {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt)
    (E : Matrix I I ℤ) : (Eᵀ * Λ * E).toBilin'.IsAlt := by
  rw [← Matrix.toBilin'_comp]
  exact fun x ↦ hΛ (E.toLin' x)

/-- Congruence mutation preserves alternation, independently of compatibility. -/
theorem isAlt_matrixFormMutation (row : K ↪ I) (B : Matrix I K ℤ) {Λ : Matrix I I ℤ}
    (hΛ : Λ.toBilin'.IsAlt) (k : K) : (matrixFormMutation row B Λ k).toBilin'.IsAlt :=
  isAlt_conjugate hΛ _

private theorem alt_entry {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) (i j : I) :
    -Λ i j = Λ j i := by
  simpa using hΛ.neg_eq (Pi.single i 1) (Pi.single j 1)

private theorem alt_diag {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) (i : I) :
    Λ i i = 0 := by
  simpa using hΛ.self_eq_zero (Pi.single i 1)

private theorem conjugate_apply_of_ne (row : K ↪ I) (B : Matrix I K ℤ)
    (Λ : Matrix I I ℤ) (k : K) (ε : ℤ) (i : I) {j : I} (hj : j ≠ row k) :
    ((matrixMutationLeft row B k ε)ᵀ * Λ * matrixMutationLeft row B k ε) i j =
      ∑ l, matrixMutationLeft row B k ε l i * Λ l j := by
  simp [Matrix.mul_apply, matrixMutationLeft_apply_of_ne row B k ε _ hj, Matrix.one_apply]

private theorem conjugate_sign (row : K ↪ I) (B : Matrix I K ℤ) {Λ : Matrix I I ℤ}
    (hΛ : Λ.toBilin'.IsAlt) (k : K) (hkk : B (row k) k = 0) {w : ℤ}
    (h : ∀ j, (Bᵀ * Λ) k j = if row k = j then w else 0) :
    (matrixMutationLeft row B k 1)ᵀ * Λ * matrixMutationLeft row B k 1 =
      (matrixMutationLeft row B k (-1))ᵀ * Λ * matrixMutationLeft row B k (-1) := by
  have hd (l : I) : matrixMutationLeft row B k 1 l (row k) -
      matrixMutationLeft row B k (-1) l (row k) = -B l k := by
    by_cases hl : l = row k
    · simp [hl, hkk]
    · simp only [matrixMutationLeft_apply_col, hl, ite_false, neg_mul, one_mul,
        neg_neg]
      rw [posPart_neg]
      linear_combination -(posPart_sub_negPart (B l k))
  have hrow (j : I) (hj : j ≠ row k) :
      ((matrixMutationLeft row B k 1)ᵀ * Λ * matrixMutationLeft row B k 1) (row k) j =
      ((matrixMutationLeft row B k (-1))ᵀ * Λ *
        matrixMutationLeft row B k (-1)) (row k) j := by
    rw [conjugate_apply_of_ne row B Λ k 1 _ hj,
      conjugate_apply_of_ne row B Λ k (-1) _ hj]
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, hd, neg_mul]
    rw [Finset.sum_neg_distrib]
    have hh := h j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Ne.symm hj, ite_false] at hh
    exact neg_eq_zero.mpr hh
  ext i j
  by_cases hj : j = row k
  · subst j
    by_cases hi : i = row k
    · subst i
      rw [alt_diag (isAlt_conjugate hΛ _) _, alt_diag (isAlt_conjugate hΛ _) _]
    · rw [← alt_entry (isAlt_conjugate hΛ _) (row k) i,
        ← alt_entry (isAlt_conjugate hΛ _) (row k) i, hrow i hi]
  · by_cases hi : i = row k
    · simpa [hi] using hrow j hj
    · simp [conjugate_apply_of_ne row B Λ k 1 i hj,
        conjugate_apply_of_ne row B Λ k (-1) i hj,
        matrixMutationLeft_apply_of_ne row B k 1 _ hi,
        matrixMutationLeft_apply_of_ne row B k (-1) _ hi, Matrix.one_apply]

/-- Either signed congruence computes form mutation. Only the selected compatibility column
and its zero diagonal entry are needed. -/
theorem matrixFormMutation_eq_conjugate (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) (k : K)
    (hkk : B (row k) k = 0) {w : ℤ}
    (h : ∀ j, (Bᵀ * Λ) k j = if row k = j then w else 0)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    matrixFormMutation row B Λ k =
      (matrixMutationLeft row B k ε)ᵀ * Λ * matrixMutationLeft row B k ε := by
  rcases hε with rfl | rfl
  · rfl
  · exact conjugate_sign row B hΛ k hkk h


section Compatibility

variable [DecidableEq K]

/-- Simultaneous matrix and form mutation preserves column compatibility with the same
weights, which need not be positive or nonzero. -/
theorem transpose_matrixMutation_mul_matrixFormMutation (row : K ↪ I)
    (B : Matrix I K ℤ) {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt)
    {d w : K → ℤ} (hd : (B.submatrix row id).IsSkewSymmetrizer d)
    (h : Bᵀ * Λ = Matrix.of fun i j ↦ if row i = j then w i else 0) (k : K) :
    (matrixMutation row B k)ᵀ * matrixFormMutation row B Λ k =
      Matrix.of fun i j ↦ if row i = j then w i else 0 := by
  let : Fintype K := Fintype.ofInjective row row.injective
  let W : Matrix K I ℤ := Matrix.of fun i j ↦ if row i = j then w i else 0
  let E := matrixMutationLeft row B k 1
  let F := matrixMutationRight row B k 1
  have hv (i j : K) : (Bᵀ * Λ * B) i j = w i * B (row i) j := by
    rw [h]
    simp [Matrix.mul_apply, ite_mul]
  have hform : (Bᵀ * Λ * B).toBilin'.IsAlt := by
    rw [← Matrix.toBilin'_comp]
    exact fun x ↦ hΛ (B.toLin' x)
  have hw (i j : K) : w i * B (row i) j = -(w j * B (row j) i) := by
    have hh := alt_entry hform i j
    rw [hv, hv] at hh
    linear_combination -hh
  have hp (i : K) : w i * (-B (row i) k)⁺ = w k * (B (row k) i)⁺ := by
    by_cases hi : 0 ≤ B (row i) k
    · have hk : B (row k) i ≤ 0 :=
        le_of_not_gt fun hk ↦ not_lt_of_ge hi (hd.apply_pos_iff.mp hk)
      simp [posPart_def, max_eq_right (neg_nonpos.mpr hi), max_eq_right hk]
    · have hk : 0 < B (row k) i := hd.apply_pos_iff.mpr (lt_of_not_ge hi)
      simp only [posPart_def, max_eq_left (neg_nonneg.mpr (lt_of_not_ge hi).le),
        max_eq_left hk.le]
      linear_combination -hw i k
  have hWE (i : K) (j : I) : (W * E) i j = w i * E (row i) j := by
    simp [W, Matrix.mul_apply, ite_mul]
  have hFW (i : K) (j : I) : (Fᵀ * W) i j =
      if i = k then -W i j else W i j + W k j * (B (row k) i)⁺ := by
    have hh := mul_matrixMutationRight_apply row B k 1 Wᵀ j i
    have heq : Fᵀ * W = (Wᵀ * F)ᵀ := by simp [Matrix.transpose_mul]
    rw [heq]
    simpa [F] using hh
  have hFE : Fᵀ * W = W * E := by
    ext i j
    rw [hFW, hWE]
    by_cases hi : i = k
    · subst i
      by_cases hj : j = row k
      · simp [E, W, hj]
      · simp [E, W, hj, Ne.symm hj]
    · by_cases hj : j = row k
      · subst j
        simpa [E, W, hi, row.injective.eq_iff] using (hp i).symm
      · simp [E, W, hi, hj, Ne.symm hj, Matrix.one_apply]
  have hEE : E * E = 1 := matrixMutationLeft_mul_self row B k 1
  have hEt : Eᵀ * Eᵀ = 1 := by rw [← Matrix.transpose_mul, hEE, Matrix.transpose_one]
  rw [matrixMutation_eq_mul row B k 1 (hd.apply_self k) (Or.inl rfl)]
  change (E * B * F)ᵀ * (Eᵀ * Λ * E) = W
  calc
    (E * B * F)ᵀ * (Eᵀ * Λ * E) = Fᵀ * Bᵀ * (Eᵀ * Eᵀ) * Λ * E := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Fᵀ * (Bᵀ * Λ) * E := by simp [hEt, Matrix.mul_assoc]
    _ = (W * E) * E := by rw [h]; change (Fᵀ * W) * E = _; rw [hFE]
    _ = W := by rw [Matrix.mul_assoc, hEE, Matrix.mul_one]

/-- Simultaneous mutation of a compatible matrix and form is involutive. -/
theorem matrixFormMutation_matrixFormMutation (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) {d w : K → ℤ}
    (hd : (B.submatrix row id).IsSkewSymmetrizer d)
    (h : Bᵀ * Λ = Matrix.of fun i j ↦ if row i = j then w i else 0) (k : K) :
    matrixFormMutation row (matrixMutation row B k) (matrixFormMutation row B Λ k) k = Λ := by
  have hm := transpose_matrixMutation_mul_matrixFormMutation row B hΛ hd h k
  rw [matrixFormMutation_eq_conjugate row (matrixMutation row B k)
    (isAlt_matrixFormMutation row B hΛ k) k
    (by rw [matrixMutation_apply_col]; exact neg_eq_zero.mpr (hd.apply_self k))
    (fun j ↦ congr_fun (congr_fun hm k) j) (Or.inr rfl)]
  rw [show (-1 : ℤ) = -(1 : ℤ) by rfl, matrixMutationLeft_matrixMutation_neg]
  let E := matrixMutationLeft row B k 1
  have hEE : E * E = 1 := matrixMutationLeft_mul_self row B k 1
  have hEt : Eᵀ * Eᵀ = 1 := by rw [← Matrix.transpose_mul, hEE, Matrix.transpose_one]
  change Eᵀ * (Eᵀ * Λ * E) * E = Λ
  calc
    Eᵀ * (Eᵀ * Λ * E) * E = (Eᵀ * Eᵀ) * Λ * (E * E) := by
      simp only [Matrix.mul_assoc]
    _ = Λ := by rw [hEt, hEE, Matrix.one_mul, Matrix.mul_one]

end Compatibility

/-- Form mutation commutes with simultaneous bijective relabelling of all and mutable
indices. Frozen rows may be relabelled as well. -/
theorem matrixFormMutation_submatrix [DecidableEq I'] [Fintype I']
    (row : K ↪ I) (B : Matrix I K ℤ) (Λ : Matrix I I ℤ) {row' : K' ↪ I'}
    (e : I' ≃ I) (f : K' ≃ K) (h : ∀ a, e (row' a) = row (f a)) (k : K') :
    matrixFormMutation row' (B.submatrix e f) (Λ.submatrix e e) k =
      (matrixFormMutation row B Λ (f k)).submatrix e e := by
  simp only [matrixFormMutation,
    matrixMutationLeft_submatrix row B 1 e.injective h k]
  change (matrixMutationLeft row B (f k) 1)ᵀ.submatrix e e * Λ.submatrix e e *
    (matrixMutationLeft row B (f k) 1).submatrix e e = _
  simp only [Matrix.submatrix_mul_equiv]

/-- Negating both the matrix and its compatible form negates the mutated form. -/
theorem matrixFormMutation_neg (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) (k : K)
    (hkk : B (row k) k = 0) {w : ℤ}
    (h : ∀ j, (Bᵀ * Λ) k j = if row k = j then w else 0) :
    matrixFormMutation row (-B) (-Λ) k = -matrixFormMutation row B Λ k := by
  have hE : matrixMutationLeft row (-B) k 1 = matrixMutationLeft row B k (-1) := by
    ext i j
    simp [matrixMutationLeft_apply]
  rw [matrixFormMutation, hE,
    matrixFormMutation_eq_conjugate row B hΛ k hkk h (Or.inr rfl)]
  simp

/-- The zero form stays zero, including for rank-deficient exchange matrices. -/
@[simp]
theorem matrixFormMutation_zero (row : K ↪ I) (B : Matrix I K ℤ) (k : K) :
    matrixFormMutation row B 0 k = 0 := by
  simp [matrixFormMutation]

end TauCeti
