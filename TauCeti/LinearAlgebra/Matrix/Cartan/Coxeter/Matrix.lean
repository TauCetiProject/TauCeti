/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Generalized

/-!
# The Coxeter matrix of an integral or generalized Cartan matrix

Any square integral matrix `A : Matrix I I ℤ` determines `Matrix.cartanCoxeterMatrix A :
CoxeterMatrix I`, equal to `1` on the diagonal, `TauCeti.coxeterOrder (A i j * A j i)` off the
diagonal when `A i j * A j i ≤ 3` (`2, 3, 4, 6` on `{0, 1, 2, 3}`), and `0` (infinite order) when
`i ≠ j` and `3 < A i j * A j i` (Kac, *Infinite-dimensional Lie algebras*, Proposition 3.13).
We relate it to `TauCeti.coxeterMatrixOfCartanMatrix`, `TauCeti.CartanDatum.braidLength`, and
Mathlib's `CoxeterMatrix.A`, `CoxeterMatrix.F₄`, and `CoxeterMatrix.G₂`.
-/

public section

namespace Matrix

variable {I J : Type*}

open scoped Classical in
/-- The **Coxeter matrix** read off a square integral matrix `A`: `1` on the diagonal, the dihedral
order `TauCeti.coxeterOrder (A i j * A j i)` (`2, 3, 4, 6` on `{0, 1, 2, 3}`) off the diagonal when
`A i j * A j i ≤ 3`, and `0` (infinite order) when `i ≠ j` and `3 < A i j * A j i`. -/
noncomputable def cartanCoxeterMatrix (A : Matrix I I ℤ) : CoxeterMatrix I where
  M := .of fun i j ↦
    if i = j then 1
    else if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i) else 0
  isSymm := Matrix.IsSymm.ext fun i j ↦ by simp only [Matrix.of_apply, eq_comm (a := i), mul_comm]
  diagonal i := by simp
  off_diagonal i j hij := by
    simp only [Matrix.of_apply, hij, ↓reduceIte]
    set c := A i j * A j i
    split_ifs with hle
    · by_cases h0 : 0 ≤ c
      · have h2 := TauCeti.two_le_coxeterOrder (c := c) (by simp; omega)
        omega
      · rw [TauCeti.coxeterOrder_eq_zero_iff.mpr (by simp; omega)]; decide
    · decide

theorem cartanCoxeterMatrix_apply [DecidableEq I] (A : Matrix I I ℤ) (i j : I) :
    A.cartanCoxeterMatrix i j =
      if i = j then 1
      else if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i) else 0 := by
  rcases eq_or_ne i j with rfl | hij <;> simp [cartanCoxeterMatrix, *]

theorem cartanCoxeterMatrix_of_ne (A : Matrix I I ℤ) {i j : I} (hij : i ≠ j) :
    A.cartanCoxeterMatrix i j =
      if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i) else 0 := by
  classical rw [cartanCoxeterMatrix_apply, ite_eq_right hij]

theorem cartanCoxeterMatrix_of_ne_of_le (A : Matrix I I ℤ) {i j : I} (hij : i ≠ j)
    (hle : A i j * A j i ≤ 3) :
    A.cartanCoxeterMatrix i j = TauCeti.coxeterOrder (A i j * A j i) := by
  rw [cartanCoxeterMatrix_of_ne A hij, ite_eq_left hle]

theorem cartanCoxeterMatrix_of_ne_of_lt (A : Matrix I I ℤ) {i j : I} (hij : i ≠ j)
    (hlt : 3 < A i j * A j i) : A.cartanCoxeterMatrix i j = 0 := by
  rw [cartanCoxeterMatrix_of_ne A hij, ite_eq_right (not_le.mpr hlt)]

theorem cartanCoxeterMatrix_eq_zero_iff {A : Matrix I I ℤ}
    (hnonneg : ∀ i j, i ≠ j → 0 ≤ A i j * A j i) (i j : I) :
    A.cartanCoxeterMatrix i j = 0 ↔ i ≠ j ∧ 3 < A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [cartanCoxeterMatrix_of_ne A hij]
    refine ⟨fun h0 ↦ ⟨hij, not_le.mp fun hle ↦ ?_⟩, fun ⟨_, hlt⟩ ↦ ite_eq_right (not_le.mpr hlt)⟩
    have hnn := hnonneg i j hij
    set c := A i j * A j i
    rw [ite_eq_left hle] at h0
    have h2 := TauCeti.two_le_coxeterOrder (c := c) (by simp; omega)
    omega

theorem cartanCoxeterMatrix_eq_two_iff_of_ne {A : Matrix I I ℤ}
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) {i j : I} (hij : i ≠ j) :
    A.cartanCoxeterMatrix i j = 2 ↔ A i j = 0 := by
  rw [cartanCoxeterMatrix_of_ne A hij]
  refine ⟨fun h ↦ ?_, fun h0 ↦ by simp [h0]⟩
  split_ifs at h with hle
  exact (mul_eq_zero.mp (TauCeti.coxeterOrder_eq_two_iff.mp h)).elim id (hzero i j).mpr

@[simp]
theorem cartanCoxeterMatrix_transpose (A : Matrix I I ℤ) :
    Aᵀ.cartanCoxeterMatrix = A.cartanCoxeterMatrix := by
  ext i j; classical
  exact (cartanCoxeterMatrix_apply Aᵀ i j).trans <| by
    simpa only [transpose_apply, mul_comm] using (cartanCoxeterMatrix_apply A i j).symm

theorem cartanCoxeterMatrix_submatrix_equiv (A : Matrix I I ℤ) (e : J ≃ I) :
    (A.submatrix e e).cartanCoxeterMatrix = A.cartanCoxeterMatrix.reindex e.symm := by
  ext i j; rcases eq_or_ne i j with rfl | hij
  · simp
  · exact (cartanCoxeterMatrix_of_ne _ hij).trans <|
      (cartanCoxeterMatrix_of_ne A (e.injective.ne hij)).symm.trans
        (by simp [CoxeterMatrix.reindex_apply])

theorem cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix (A : Matrix I I ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) :
    A.cartanCoxeterMatrix = TauCeti.coxeterMatrixOfCartanMatrix A hdiag hmem := by
  ext i j; rcases eq_or_ne i j with rfl | hij
  · simp
  · have hm := hmem i j hij
    set c := A i j * A j i
    exact (cartanCoxeterMatrix_of_ne_of_le A hij (by simp at hm; omega)).trans
      (TauCeti.coxeterMatrixOfCartanMatrix_apply A hdiag hmem i j).symm

namespace IsGeneralizedCartan

variable {A : Matrix I I ℤ} (hA : A.IsGeneralizedCartan)
include hA

theorem cartanCoxeterMatrix_eq_zero_iff (i j : I) :
    A.cartanCoxeterMatrix i j = 0 ↔ i ≠ j ∧ 3 < A i j * A j i :=
  Matrix.cartanCoxeterMatrix_eq_zero_iff (fun i j _ ↦ hA.mul_nonneg i j) i j

theorem cartanCoxeterMatrix_eq_two_iff (i j : I) :
    A.cartanCoxeterMatrix i j = 2 ↔ A i j = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hA.diag i]
  · exact cartanCoxeterMatrix_eq_two_iff_of_ne hA.zero_comm hij

theorem cartanCoxeterMatrix_mem_of_ne_of_le {i j : I} (hij : i ≠ j)
    (hle : A i j * A j i ≤ 3) : A.cartanCoxeterMatrix i j ∈ ({2, 3, 4, 6} : Set ℕ) := by
  rw [cartanCoxeterMatrix_of_ne_of_le A hij hle]
  have h0 := hA.mul_nonneg i j
  set c := A i j * A j i
  exact TauCeti.coxeterOrder_mem (by simp; omega)

end IsGeneralizedCartan

end Matrix

namespace TauCeti.CartanDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

theorem isGeneralizedCartan : D.cartan.IsGeneralizedCartan :=
  ⟨D.cartan_apply_self, fun _ _ ↦ D.cartan_nonpos, D.cartan_eq_zero_iff⟩

@[simp]
theorem cartanCoxeterMatrix_apply [DecidableEq ι] (i j : ι) :
    D.cartan.cartanCoxeterMatrix i j = D.braidLength i j := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · by_cases hle : D.cartan i j * D.cartan j i ≤ 3
    · rw [Matrix.cartanCoxeterMatrix_of_ne_of_le _ hij hle, D.braidLength_of_le hle]
    · rw [Matrix.cartanCoxeterMatrix_of_ne_of_lt _ hij (not_le.mp hle),
        D.braidLength_of_ne_of_lt hij (not_le.mp hle)]

end TauCeti.CartanDatum

namespace CartanMatrix

@[simp]
theorem cartanCoxeterMatrix_A (n : ℕ) : (A n).cartanCoxeterMatrix = CoxeterMatrix.A n := by
  ext i j; refine (Matrix.cartanCoxeterMatrix_apply (A n) i j).trans ?_
  rcases eq_or_ne i j with rfl | hij
  · simp [CoxeterMatrix.A]
  · simp only [CoxeterMatrix.A, Matrix.of_apply, hij, hij.symm, ↓reduceIte, A]
    split_ifs <;> simp_all

@[simp]
theorem cartanCoxeterMatrix_F₄ : F₄.cartanCoxeterMatrix = CoxeterMatrix.F₄ := by
  ext i j; refine (Matrix.cartanCoxeterMatrix_apply F₄ i j).trans ?_
  fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.F₄, F₄]

@[simp]
theorem cartanCoxeterMatrix_G₂ : G₂.cartanCoxeterMatrix = CoxeterMatrix.G₂ := by
  ext i j; refine (Matrix.cartanCoxeterMatrix_apply G₂ i j).trans ?_
  fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.G₂, G₂]

end CartanMatrix
