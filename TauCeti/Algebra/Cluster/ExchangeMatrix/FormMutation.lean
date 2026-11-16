/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Factorization
public import TauCeti.LinearAlgebra.Matrix.BilinearForm

import Mathlib.Tactic.LinearCombination

/-!
# Mutation of compatible alternating forms

An alternating integral form compatible with an extended exchange matrix mutates by the
congruence `Eεᵀ * Λ * Eε`. Column compatibility means
`(Bᵀ * Λ) i j = if j = row i then w i else 0`. The form records quasi-commutation
exponents of quantum-torus monomials and is mutated with the exchange matrix in quantum and
polynomial cluster seeds. For an alternating form and a skew-symmetrizable principal block,
mutation preserves this equation with the same weights, which may be negative or zero.
The positive skew-symmetrizer is separate data.

Sign-independence and double mutation need only alternation, `B (row k) k = 0`, and
vanishing of row `k` of `Bᵀ * Λ` outside `row k`. The statements use raw compatibility
equations and Mathlib's bilinear-form predicate, without imposing a bundled representation.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics 195
  (2005), §3, Propositions 3.4 and 3.6.
-/

public section

namespace TauCeti

open Matrix

variable {I K I' K' : Type*} [DecidableEq I] [Fintype I]

/-- Mutation of an integral form using the positive-sign left factor. If the form is
alternating, `B (row k) k = 0`, and row `k` of `Bᵀ * Λ` vanishes outside `row k`, either
choice of sign gives this form. -/
def formMutation (row : K ↪ I) (B : Matrix I K ℤ) (Λ : Matrix I I ℤ) (k : K) :
    Matrix I I ℤ :=
  (matrixMutationLeft row B k 1)ᵀ * Λ * matrixMutationLeft row B k 1

/-- The unconditional congruence formula defining form mutation. -/
theorem formMutation_def (row : K ↪ I) (B : Matrix I K ℤ)
    (Λ : Matrix I I ℤ) (k : K) :
    formMutation row B Λ k =
      (matrixMutationLeft row B k 1)ᵀ * Λ * matrixMutationLeft row B k 1 := by rfl

/-- Congruence mutation preserves alternation, independently of compatibility. -/
theorem isAlt_toBilin'_formMutation (row : K ↪ I) (B : Matrix I K ℤ) {Λ : Matrix I I ℤ}
    (hΛ : Λ.toBilin'.IsAlt) (k : K) : (formMutation row B Λ k).toBilin'.IsAlt :=
  Matrix.isAlt_toBilin'_transpose_mul_mul hΛ _

/-- Alternation is reflected as well as preserved by congruence mutation. -/
@[simp]
theorem isAlt_toBilin'_formMutation_iff (row : K ↪ I) (B : Matrix I K ℤ)
    (Λ : Matrix I I ℤ) (k : K) :
    (formMutation row B Λ k).toBilin'.IsAlt ↔ Λ.toBilin'.IsAlt := by
  constructor
  · intro hΛ
    set E := matrixMutationLeft row B k 1 with hE
    have hEE : E * E = 1 := matrixMutationLeft_mul_self row B k 1
    have hEt : Eᵀ * Eᵀ = 1 := by rw [← Matrix.transpose_mul, hEE, Matrix.transpose_one]
    have h := Matrix.isAlt_toBilin'_transpose_mul_mul hΛ E
    have heq : Eᵀ * formMutation row B Λ k * E = Λ := by
      rw [formMutation_def, ← hE]
      calc
        Eᵀ * (Eᵀ * Λ * E) * E = (Eᵀ * Eᵀ) * Λ * (E * E) := by
          simp only [Matrix.mul_assoc]
        _ = Λ := by rw [hEt, hEE, Matrix.one_mul, Matrix.mul_one]
    rwa [heq] at h
  · intro hΛ
    exact isAlt_toBilin'_formMutation row B hΛ k

/-- Transposing a form commutes with its congruence mutation. -/
@[simp]
theorem transpose_formMutation (row : K ↪ I) (B : Matrix I K ℤ)
    (Λ : Matrix I I ℤ) (k : K) :
    (formMutation row B Λ k)ᵀ = formMutation row B Λᵀ k := by
  simp [formMutation_def, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem transpose_mul_mul_apply_of_ne (row : K ↪ I) (B : Matrix I K ℤ)
    (Λ : Matrix I I ℤ) (k : K) (ε : ℤ) (i : I) {j : I} (hj : j ≠ row k) :
    ((matrixMutationLeft row B k ε)ᵀ * Λ * matrixMutationLeft row B k ε) i j =
      ∑ l, matrixMutationLeft row B k ε l i * Λ l j := by
  simp [Matrix.mul_apply, matrixMutationLeft_apply_of_ne row B k ε _ hj, Matrix.one_apply]

/-- The entries of form mutation are the usual double sum for congruence. -/
theorem formMutation_apply (row : K ↪ I) (B : Matrix I K ℤ) (Λ : Matrix I I ℤ)
    (k : K) (i j : I) :
    formMutation row B Λ k i j =
      ∑ a, ∑ b, matrixMutationLeft row B k 1 a i * Λ a b *
        matrixMutationLeft row B k 1 b j := by
  rw [formMutation_def, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, mul_assoc]

/-- Entries outside the selected row and column are unchanged, without assumptions on the form. -/
@[simp]
theorem formMutation_apply_of_ne (row : K ↪ I) (B : Matrix I K ℤ)
    (Λ : Matrix I I ℤ) (k : K) {i j : I} (hi : i ≠ row k) (hj : j ≠ row k) :
    formMutation row B Λ k i j = Λ i j := by
  rw [formMutation_def, transpose_mul_mul_apply_of_ne row B Λ k 1 i hj]
  simp [matrixMutationLeft_apply_of_ne row B k 1 _ hi, Matrix.one_apply]

/-- An off-diagonal entry in the selected row is its negative plus the weighted other rows.
No alternation or compatibility hypothesis is needed. -/
theorem formMutation_apply_row (row : K ↪ I) (B : Matrix I K ℤ)
    (Λ : Matrix I I ℤ) (k : K) {j : I} (hj : j ≠ row k) :
    formMutation row B Λ k (row k) j =
      -Λ (row k) j + ∑ l ∈ Finset.univ.erase (row k), (-B l k)⁺ * Λ l j := by
  rw [formMutation_def, transpose_mul_mul_apply_of_ne row B Λ k 1 _ hj,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (row k))]
  simp only [matrixMutationLeft_apply_col, ite_true, neg_mul, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  simp [(Finset.mem_erase.mp hl).1]

/-- An off-diagonal entry in the selected column is its negative plus the weighted other
columns. No alternation or compatibility hypothesis is needed. -/
theorem formMutation_apply_col (row : K ↪ I) (B : Matrix I K ℤ)
    (Λ : Matrix I I ℤ) (k : K) {i : I} (hi : i ≠ row k) :
    formMutation row B Λ k i (row k) =
      -Λ i (row k) + ∑ l ∈ Finset.univ.erase (row k), (-B l k)⁺ * Λ i l := by
  have hh := formMutation_apply_row row B Λᵀ k hi
  rw [← transpose_formMutation] at hh
  simpa only [Matrix.transpose_apply] using hh

/-- Every diagonal entry of an alternating form remains zero under mutation. -/
@[simp]
theorem formMutation_apply_self (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) (k : K) (i : I) :
    formMutation row B Λ k i i = 0 :=
  Matrix.apply_self_eq_zero_of_isAlt_toBilin' (isAlt_toBilin'_formMutation row B hΛ k) _

private theorem transpose_mul_mul_sign (row : K ↪ I) (B : Matrix I K ℤ) {Λ : Matrix I I ℤ}
    (hΛ : Λ.toBilin'.IsAlt) (k : K) (hkk : B (row k) k = 0)
    (h : ∀ j ≠ row k, (Bᵀ * Λ) k j = 0) :
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
    rw [transpose_mul_mul_apply_of_ne row B Λ k 1 _ hj,
      transpose_mul_mul_apply_of_ne row B Λ k (-1) _ hj]
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, hd, neg_mul]
    rw [Finset.sum_neg_distrib]
    have hh := h j hj
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hh
    exact neg_eq_zero.mpr hh
  have hAlt (ε : ℤ) :=
    Matrix.isAlt_toBilin'_transpose_mul_mul hΛ (matrixMutationLeft row B k ε)
  ext i j
  by_cases hj : j = row k
  · subst j
    by_cases hi : i = row k
    · subst i
      rw [Matrix.apply_self_eq_zero_of_isAlt_toBilin' (hAlt 1) _,
        Matrix.apply_self_eq_zero_of_isAlt_toBilin' (hAlt (-1)) _]
    · rw [← Matrix.neg_apply_eq_of_isAlt_toBilin' (hAlt 1) (row k) i,
        ← Matrix.neg_apply_eq_of_isAlt_toBilin' (hAlt (-1)) (row k) i, hrow i hi]
  · by_cases hi : i = row k
    · simpa [hi] using hrow j hj
    · simp [transpose_mul_mul_apply_of_ne row B Λ k 1 i hj,
        transpose_mul_mul_apply_of_ne row B Λ k (-1) i hj,
        matrixMutationLeft_apply_of_ne row B k 1 _ hi,
        matrixMutationLeft_apply_of_ne row B k (-1) _ hi, Matrix.one_apply]

/-- For an alternating form, either signed congruence computes form mutation when
`B (row k) k = 0` and row `k` of `Bᵀ * Λ` vanishes outside `row k`. -/
theorem formMutation_eq_transpose_mul_mul (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) (k : K)
    (hkk : B (row k) k = 0)
    (h : ∀ j ≠ row k, (Bᵀ * Λ) k j = 0)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    formMutation row B Λ k =
      (matrixMutationLeft row B k ε)ᵀ * Λ * matrixMutationLeft row B k ε := by
  rcases hε with rfl | rfl
  · rfl
  · exact transpose_mul_mul_sign row B hΛ k hkk h


/-- Under column compatibility, evaluating the form on two exchange-matrix columns gives
its diagonal weight times the corresponding principal entry. -/
theorem transpose_mul_mul_apply_of_transpose_mul_eq (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} {w : K → ℤ}
    (h : Bᵀ * Λ = Matrix.of fun i j ↦ if j = row i then w i else 0) (i j : K) :
    (Bᵀ * Λ * B) i j = w i * B (row i) j := by
  rw [h]
  simp [Matrix.mul_apply, ite_mul]

/-- Compatibility of an alternating form forces the weighted principal entries to be
skew-symmetric, with no positivity assumption on the weights. -/
theorem mul_apply_eq_neg_mul_apply_of_transpose_mul_eq (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) {w : K → ℤ}
    (h : Bᵀ * Λ = Matrix.of fun i j ↦ if j = row i then w i else 0) (i j : K) :
    w i * B (row i) j = -(w j * B (row j) i) := by
  classical
  let : Fintype K := Fintype.ofInjective row row.injective
  have hh := Matrix.neg_apply_eq_of_isAlt_toBilin'
    (Matrix.isAlt_toBilin'_transpose_mul_mul hΛ B) i j
  rw [transpose_mul_mul_apply_of_transpose_mul_eq row B h,
    transpose_mul_mul_apply_of_transpose_mul_eq row B h] at hh
  linear_combination -hh

/-- Positive compatibility weights of an alternating form are themselves a skew-symmetrizer
of the principal block. No separate skew-symmetrizer is needed for this implication. -/
theorem isSkewSymmetrizer_submatrix_of_transpose_mul_eq (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) {w : K → ℤ}
    (h : Bᵀ * Λ = Matrix.of fun i j ↦ if j = row i then w i else 0)
    (hw : ∀ i, 0 < w i) : (B.submatrix row id).IsSkewSymmetrizer w :=
  ⟨hw, mul_apply_eq_neg_mul_apply_of_transpose_mul_eq row B hΛ h⟩

/-- For a skew-symmetrizable principal block and an alternating compatible form, the signed
weights exchange the negative part of a principal entry with the positive part of the
transposed principal entry. -/
theorem mul_posPart_neg_eq_mul_posPart_of_transpose_mul_eq (row : K ↪ I)
    (B : Matrix I K ℤ) {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) {d w : K → ℤ}
    (hd : (B.submatrix row id).IsSkewSymmetrizer d)
    (h : Bᵀ * Λ = Matrix.of fun i j ↦ if j = row i then w i else 0) (i k : K) :
    w i * (-B (row i) k)⁺ = w k * (B (row k) i)⁺ := by
  by_cases hi : 0 ≤ B (row i) k
  · have hk : B (row k) i ≤ 0 :=
      le_of_not_gt fun hk ↦ not_lt_of_ge hi (hd.apply_pos_iff.mp hk)
    simp [posPart_def, max_eq_right (neg_nonpos.mpr hi), max_eq_right hk]
  · have hk : 0 < B (row k) i := hd.apply_pos_iff.mpr (lt_of_not_ge hi)
    simp only [posPart_def, max_eq_left (neg_nonneg.mpr (lt_of_not_ge hi).le),
      max_eq_left hk.le]
    linear_combination -mul_apply_eq_neg_mul_apply_of_transpose_mul_eq row B hΛ h i k

section Compatibility

variable [DecidableEq K]

/-- Simultaneous matrix and form mutation preserves column compatibility of an alternating
form with the same, possibly zero or negative, weights, when the principal block has a
positive skew-symmetrizer. -/
theorem transpose_matrixMutation_mul_formMutation (row : K ↪ I)
    (B : Matrix I K ℤ) {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt)
    {d w : K → ℤ} (hd : (B.submatrix row id).IsSkewSymmetrizer d)
    (h : Bᵀ * Λ = Matrix.of fun i j ↦ if j = row i then w i else 0) (k : K) :
    (matrixMutation row B k)ᵀ * formMutation row B Λ k =
      Matrix.of fun i j ↦ if j = row i then w i else 0 := by
  let : Fintype K := Fintype.ofInjective row row.injective
  set W : Matrix K I ℤ := Matrix.of fun i j ↦ if j = row i then w i else 0 with hW
  set E := matrixMutationLeft row B k 1 with hE
  set F := matrixMutationRight row B k 1 with hF
  have hWE (i : K) (j : I) : (W * E) i j = w i * E (row i) j := by
    simp [hW, Matrix.mul_apply, ite_mul]
  have hFW (i : K) (j : I) : (Fᵀ * W) i j =
      if i = k then -W i j else W i j + W k j * (B (row k) i)⁺ := by
    have hh := mul_matrixMutationRight_apply row B k 1 Wᵀ j i
    have heq : Fᵀ * W = (Wᵀ * F)ᵀ := by simp [Matrix.transpose_mul]
    rw [heq]
    simpa [hF] using hh
  have hFE : Fᵀ * W = W * E := by
    ext i j
    rw [hFW, hWE]
    by_cases hi : i = k
    · subst i
      by_cases hj : j = row k
      · simp [hE, hW, hj]
      · simp [hE, hW, hj, Ne.symm hj]
    · by_cases hj : j = row k
      · subst j
        simpa [hE, hW, hi, Ne.symm hi, row.injective.eq_iff] using
          (mul_posPart_neg_eq_mul_posPart_of_transpose_mul_eq row B hΛ hd h i k).symm
      · simp [hE, hW, hi, hj, Matrix.one_apply, eq_comm]
  have hEE : E * E = 1 := matrixMutationLeft_mul_self row B k 1
  have hEt : Eᵀ * Eᵀ = 1 := by rw [← Matrix.transpose_mul, hEE, Matrix.transpose_one]
  rw [matrixMutation_eq_mul row B k 1 (hd.apply_self k) (Or.inl rfl),
    formMutation_def, ← hE, ← hF]
  calc
    (E * B * F)ᵀ * (Eᵀ * Λ * E) = Fᵀ * Bᵀ * (Eᵀ * Eᵀ) * Λ * E := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Fᵀ * (Bᵀ * Λ) * E := by simp [hEt, Matrix.mul_assoc]
    _ = (W * E) * E := by rw [h, hFE]
    _ = W := by rw [Matrix.mul_assoc, hEE, Matrix.mul_one]

end Compatibility

/-- For an alternating form, mutating along `B` and its mutation in the same direction
recovers the form if `B (row k) k = 0` and row `k` of `Bᵀ * Λ` vanishes outside `row k`. -/
@[simp]
theorem formMutation_formMutation [DecidableEq K]
    (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) (k : K)
    (hkk : B (row k) k = 0)
    (h : ∀ j ≠ row k, (Bᵀ * Λ) k j = 0) :
    formMutation row (matrixMutation row B k) (formMutation row B Λ k) k = Λ := by
  rw [formMutation_def, matrixMutationLeft_matrixMutation,
    formMutation_eq_transpose_mul_mul row B hΛ k hkk h (Or.inr rfl)]
  set E := matrixMutationLeft row B k (-1) with hE
  have hEE : E * E = 1 := by rw [hE, matrixMutationLeft_mul_self]
  have hEt : Eᵀ * Eᵀ = 1 := by rw [← Matrix.transpose_mul, hEE, Matrix.transpose_one]
  calc
    Eᵀ * (Eᵀ * Λ * E) * E = (Eᵀ * Eᵀ) * Λ * (E * E) := by
      simp only [Matrix.mul_assoc]
    _ = Λ := by rw [hEt, hEE, Matrix.one_mul, Matrix.mul_one]

/-- Form mutation commutes with bijective relabelling of all rows and any compatible
map of mutable columns. In particular mutable columns can be frozen. -/
theorem formMutation_submatrix [DecidableEq I'] [Fintype I']
    (row : K ↪ I) (B : Matrix I K ℤ) (Λ : Matrix I I ℤ) {row' : K' ↪ I'}
    {f : I' → I} {g : K' → K} (hf : Function.Bijective f)
    (h : ∀ a, f (row' a) = row (g a)) (k : K') :
    formMutation row' (B.submatrix f g) (Λ.submatrix f f) k =
      (formMutation row B Λ (g k)).submatrix f f := by
  simp only [formMutation_def,
    matrixMutationLeft_submatrix row B 1 hf.injective h k, Matrix.transpose_submatrix]
  rw [← Matrix.submatrix_mul _ _ f f f hf, ← Matrix.submatrix_mul _ _ f f f hf]

/-- Negating the form negates its mutation, without compatibility or alternation assumptions. -/
@[simp]
theorem formMutation_neg (row : K ↪ I) (B : Matrix I K ℤ)
    (Λ : Matrix I I ℤ) (k : K) :
    formMutation row B (-Λ) k = -formMutation row B Λ k := by
  simp [formMutation_def]

/-- For an alternating form, negating the exchange matrix fixes its mutation when
`B (row k) k = 0` and row `k` of `Bᵀ * Λ` vanishes outside `row k`. -/
@[simp]
theorem formMutation_neg_left (row : K ↪ I) (B : Matrix I K ℤ)
    {Λ : Matrix I I ℤ} (hΛ : Λ.toBilin'.IsAlt) (k : K)
    (hkk : B (row k) k = 0) (h : ∀ j ≠ row k, (Bᵀ * Λ) k j = 0) :
    formMutation row (-B) Λ k = formMutation row B Λ k := by
  rw [formMutation_def, matrixMutationLeft_neg]
  exact (formMutation_eq_transpose_mul_mul row B hΛ k hkk h (Or.inr rfl)).symm

/-- The zero form stays zero, including for rank-deficient exchange matrices. -/
@[simp]
theorem formMutation_zero (row : K ↪ I) (B : Matrix I K ℤ) (k : K) :
    formMutation row B 0 k = 0 := by
  simp [formMutation]

end TauCeti
