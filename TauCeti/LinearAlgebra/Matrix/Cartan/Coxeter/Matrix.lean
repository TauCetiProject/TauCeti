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

Any square integral matrix `A` on an arbitrary index type `I` determines a `CoxeterMatrix I`,
`Matrix.cartanCoxeterMatrix A`:

* on the diagonal, `A.cartanCoxeterMatrix i i = 1`;
* for `i ≠ j` with `A i j * A j i ≤ 3`, `A.cartanCoxeterMatrix i j` is
  `TauCeti.coxeterOrder (A i j * A j i)`, sending `0, 1, 2, 3` to `2, 3, 4, 6` (and negative
  products to `0`);
* for `i ≠ j` with `3 < A i j * A j i` (such as affine `A₁⁽¹⁾` where `(-2) * (-2) = 4`, or
  hyperbolic pairs), `A.cartanCoxeterMatrix i j = 0`, Mathlib's encoding of an infinite order.

When all off-diagonal Cartan products lie in `{0, 1, 2, 3}`, this agrees with
`TauCeti.coxeterMatrixOfCartanMatrix`; for a `TauCeti.CartanDatum`, its entries are
`TauCeti.CartanDatum.braidLength`.

## Main definitions

* `Matrix.cartanCoxeterMatrix`: the `CoxeterMatrix I` attached to `A : Matrix I I ℤ`.

## Main results

* `Matrix.cartanCoxeterMatrix_of_ne_of_le`, `Matrix.cartanCoxeterMatrix_of_ne_of_lt`: off-diagonal
  values in the dihedral and infinite-order regimes.
* `Matrix.IsGeneralizedCartan.cartanCoxeterMatrix_eq_zero_iff`: for a generalized Cartan matrix,
  the Coxeter entry vanishes precisely when `i ≠ j` and `3 < A i j * A j i`.
* `Matrix.IsGeneralizedCartan.cartanCoxeterMatrix_eq_two_iff`: the Coxeter entry is `2` precisely
  when `A i j = 0`.
* `Matrix.cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix` and
  `TauCeti.CartanDatum.cartanCoxeterMatrix_apply`: compatibility with finite-type Cartan Coxeter
  matrices and with `TauCeti.CartanDatum.braidLength`.
* `CartanMatrix.cartanCoxeterMatrix_A`, `CartanMatrix.cartanCoxeterMatrix_F₄`,
  `CartanMatrix.cartanCoxeterMatrix_G₂`: identification with Mathlib's standard Coxeter matrices.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.7 and Proposition 3.13.
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
    else if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i)
    else 0
  isSymm := Matrix.IsSymm.ext fun i j ↦ by
    simp only [Matrix.of_apply, eq_comm (a := i), mul_comm (A i j)]
  diagonal i := by simp
  off_diagonal i j hij := by
    simp only [Matrix.of_apply, hij, ↓reduceIte]
    split_ifs with hle
    · by_cases h0 : 0 ≤ A i j * A j i
      · have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega
        have h2 := TauCeti.two_le_coxeterOrder hmem
        omega
      · rw [TauCeti.coxeterOrder_eq_zero_iff.mpr]
        · decide
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega
    · decide

theorem cartanCoxeterMatrix_apply [DecidableEq I] (A : Matrix I I ℤ) (i j : I) :
    A.cartanCoxeterMatrix i j =
      if i = j then 1
      else if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i)
      else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp only [cartanCoxeterMatrix, Matrix.of_apply, hij, ↓reduceIte]

theorem cartanCoxeterMatrix_of_ne (A : Matrix I I ℤ) {i j : I} (hij : i ≠ j) :
    A.cartanCoxeterMatrix i j =
      if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i) else 0 := by
  classical
  rw [cartanCoxeterMatrix_apply, ite_eq_right hij]

theorem cartanCoxeterMatrix_of_ne_of_le (A : Matrix I I ℤ) {i j : I} (hij : i ≠ j)
    (hle : A i j * A j i ≤ 3) :
    A.cartanCoxeterMatrix i j = TauCeti.coxeterOrder (A i j * A j i) := by
  rw [cartanCoxeterMatrix_of_ne A hij, ite_eq_left hle]

theorem cartanCoxeterMatrix_of_ne_of_lt (A : Matrix I I ℤ) {i j : I} (hij : i ≠ j)
    (hlt : 3 < A i j * A j i) :
    A.cartanCoxeterMatrix i j = 0 := by
  rw [cartanCoxeterMatrix_of_ne A hij, ite_eq_right (not_le.mpr hlt)]

/-- When off-diagonal Cartan products are nonnegative, an entry of `A.cartanCoxeterMatrix` is `0`
(encoding infinite order) if and only if it is off the diagonal with Cartan product strictly
greater than `3`. -/
theorem cartanCoxeterMatrix_eq_zero_iff {A : Matrix I I ℤ}
    (hnonneg : ∀ i j, i ≠ j → 0 ≤ A i j * A j i) (i j : I) :
    A.cartanCoxeterMatrix i j = 0 ↔ i ≠ j ∧ 3 < A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [cartanCoxeterMatrix_of_ne A hij]
    constructor
    · intro h0
      refine ⟨hij, not_le.mp fun hle ↦ ?_⟩
      rw [ite_eq_left hle] at h0
      have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
        have hnn := hnonneg i j hij
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      have h2 := TauCeti.two_le_coxeterOrder hmem
      omega
    · rintro ⟨-, hlt⟩
      exact ite_eq_right (not_le.mpr hlt)

/-- For distinct indices of a matrix with symmetric zero pattern, the Coxeter entry is `2`
if and only if `A i j = 0`. -/
theorem cartanCoxeterMatrix_eq_two_iff_of_ne {A : Matrix I I ℤ}
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) {i j : I} (hij : i ≠ j) :
    A.cartanCoxeterMatrix i j = 2 ↔ A i j = 0 := by
  rw [cartanCoxeterMatrix_of_ne A hij]
  constructor
  · intro h
    split_ifs at h with hle
    rw [TauCeti.coxeterOrder_eq_two_iff, mul_eq_zero] at h
    exact h.elim id (hzero i j).mpr
  · intro h0
    simp [h0]

@[simp]
theorem cartanCoxeterMatrix_transpose (A : Matrix I I ℤ) :
    Aᵀ.cartanCoxeterMatrix = A.cartanCoxeterMatrix := by
  ext i j
  classical
  exact (cartanCoxeterMatrix_apply Aᵀ i j).trans <| by
    simpa only [transpose_apply, mul_comm] using (cartanCoxeterMatrix_apply A i j).symm

theorem cartanCoxeterMatrix_submatrix_equiv (A : Matrix I I ℤ) (e : J ≃ I) :
    (A.submatrix e e).cartanCoxeterMatrix = A.cartanCoxeterMatrix.reindex e.symm := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · refine (cartanCoxeterMatrix_of_ne _ hij).trans ?_
    exact (cartanCoxeterMatrix_of_ne A (e.injective.ne hij)).symm.trans (by
      simp [CoxeterMatrix.reindex_apply])

/-- When all off-diagonal Cartan products lie in `{0, 1, 2, 3}`, `Matrix.cartanCoxeterMatrix`
agrees with `TauCeti.coxeterMatrixOfCartanMatrix`. -/
theorem cartanCoxeterMatrix_eq_coxeterMatrixOfCartanMatrix (A : Matrix I I ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) :
    A.cartanCoxeterMatrix = TauCeti.coxeterMatrixOfCartanMatrix A hdiag hmem := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have hle : A i j * A j i ≤ 3 := by
      have hm := hmem i j hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      omega
    exact (cartanCoxeterMatrix_of_ne_of_le A hij hle).trans
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
    (hle : A i j * A j i ≤ 3) :
    A.cartanCoxeterMatrix i j ∈ ({2, 3, 4, 6} : Set ℕ) := by
  rw [cartanCoxeterMatrix_of_ne_of_le A hij hle]
  refine TauCeti.coxeterOrder_mem ?_
  have h0 := hA.mul_nonneg i j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

end IsGeneralizedCartan

end Matrix

namespace TauCeti.CartanDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

/-- The Cartan matrix of a symmetrizable Cartan datum is a generalized Cartan matrix. -/
theorem isGeneralizedCartan : D.cartan.IsGeneralizedCartan where
  diag := D.cartan_apply_self
  offDiag_nonpos _ _ := D.cartan_nonpos
  zero_comm := D.cartan_eq_zero_iff

/-- The entries of `D.cartan.cartanCoxeterMatrix` agree with `D.braidLength`. -/
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
theorem cartanCoxeterMatrix_A (n : ℕ) :
    (A n).cartanCoxeterMatrix = CoxeterMatrix.A n := by
  ext i j
  refine (Matrix.cartanCoxeterMatrix_apply (A n) i j).trans ?_
  rcases eq_or_ne i j with rfl | hij
  · simp [CoxeterMatrix.A]
  · simp only [CoxeterMatrix.A, Matrix.of_apply, hij, hij.symm, ↓reduceIte, A]
    split_ifs <;> simp_all

@[simp]
theorem cartanCoxeterMatrix_F₄ : F₄.cartanCoxeterMatrix = CoxeterMatrix.F₄ := by
  ext i j
  refine (Matrix.cartanCoxeterMatrix_apply F₄ i j).trans ?_
  fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.F₄, F₄]

@[simp]
theorem cartanCoxeterMatrix_G₂ : G₂.cartanCoxeterMatrix = CoxeterMatrix.G₂ := by
  ext i j
  refine (Matrix.cartanCoxeterMatrix_apply G₂ i j).trans ?_
  fin_cases i <;> fin_cases j <;> simp [CoxeterMatrix.G₂, G₂]

end CartanMatrix
