/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.IsotropicFlag.Antidiagonal.Basic

/-!
# A signed permutation congruence from the antidiagonal form to `JFin`

The antidiagonal alternating form `Q = TauCeti.JAntidiag m R` on `Fin (m + m)` is `-JFin m R`
permuted by the self-dual flag order `σ = TauCeti.GLSymplecticFin.IsotropicFlag.flagOrder m`
(`TauCeti.JAntidiag_eq_neg_submatrix_flagOrder`). This file turns that identity into a
congruence by an explicit signed permutation matrix

`P = diag(s) · P_σ`, where `s = (-1, …, -1, 1, …, 1)` and `P_σ` is the permutation matrix of `σ`

(`TauCeti.antidiagCongr`). It is orthogonal, `P Pᵀ = 1`, and `P Q Pᵀ = JFin m R`
(`TauCeti.antidiagCongr_mul_JAntidiag_mul_transpose`): `P_σ` undoes the flag order, and the
signs `s`, opposite on the two halves, undo the global negation.

Conjugation by `P` moves the symplectic group of `JFin` to that of `Q` and is explicit on
matrices: `P⁻¹ M P` is `M` permuted by `σ` with the signs `s_i s_j` on its entries
(`TauCeti.antidiagCongr_inv_mul_mul`). Hence

* it sends a diagonal matrix `diag(d)` to `diag(d ∘ σ)`: the diagonal torus
  `diag(t₁, …, t_m, t₁⁻¹, …, t_m⁻¹)` of the `JFin` model becomes
  `diag(t₁, …, t_m, t_m⁻¹, …, t₁⁻¹)` (`TauCeti.antidiagCongr_inv_mul_diagonal_mul`);
* `P⁻¹ M P` is upper triangular exactly when `M` is upper triangular after reindexing by `σ`, the
  condition defining the isotropic-flag Borel subgroup of the `JFin` model
  (`TauCeti.blockTriangular_antidiagCongr_inv_mul_mul_iff`); conversely, `P M P⁻¹` vanishes below
  the diagonal in the flag order exactly when `M` is upper triangular
  (`TauCeti.forall_flagOrder_lt_antidiagCongr_mul_mul_inv_eq_zero_iff`).

Everything holds over an arbitrary commutative ring, including `m = 0`.
-/

public section

open Matrix

namespace TauCeti

open GLSymplecticFin.IsotropicFlag

variable (m : ℕ) (R : Type*) [CommRing R]

/-- The signs of the congruence: `-1` on the isotropic half `Fin.castAdd` and `1` on the dual half
`Fin.addNat` of `Fin (m + m)`. -/
def antidiagSign : Fin (m + m) → R :=
  Fin.addCases (motive := fun _ ↦ R) (fun _ ↦ -1) fun _ ↦ 1

variable {m R}

@[simp]
theorem antidiagSign_castAdd (i : Fin m) : antidiagSign m R (i.castAdd m) = -1 := by
  simp [antidiagSign]

@[simp]
theorem antidiagSign_addNat (i : Fin m) : antidiagSign m R (i.addNat m) = 1 := by
  simp [antidiagSign, ← Fin.natAdd_eq_addNat]

@[simp]
theorem antidiagSign_mul_self (i : Fin (m + m)) : antidiagSign m R i * antidiagSign m R i = 1 := by
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
  · simp
  · simp [Fin.natAdd_eq_addNat]

@[simp]
theorem isUnit_antidiagSign (i : Fin (m + m)) : IsUnit (antidiagSign m R i) :=
  .of_mul_eq_one _ (antidiagSign_mul_self i)

@[simp]
theorem antidiagSign_flagOrder (i : Fin (m + m)) :
    antidiagSign m R (flagOrder m i) = antidiagSign m R i := by
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
  · simp
  · simp [Fin.natAdd_eq_addNat]

/-- The permutation matrix `P_σ` of the self-dual flag order is symmetric, since `σ` is an
involution. -/
theorem transpose_toMatrix_flagOrder :
    ((flagOrder m).toPEquiv.toMatrix : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ =
      (flagOrder m).toPEquiv.toMatrix := by
  rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, flagOrder_symm]

/-- Conjugating by the permutation matrix `P_σ` of the self-dual flag order permutes rows and
columns by `σ`, since `σ` is an involution. -/
theorem toMatrix_flagOrder_mul_mul (M : Matrix (Fin (m + m)) (Fin (m + m)) R) :
    (flagOrder m).toPEquiv.toMatrix * M * (flagOrder m).toPEquiv.toMatrix =
      M.submatrix (flagOrder m) (flagOrder m) := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
    flagOrder_symm, Function.comp_id, Function.id_comp]

variable (m R)

/-- The signed permutation matrix `P = diag(s) · P_σ` with `P Q Pᵀ = JFin m R`, for the
antidiagonal form `Q` and the self-dual flag order `σ`. -/
def antidiagCongrMatrix : Matrix (Fin (m + m)) (Fin (m + m)) R :=
  diagonal (antidiagSign m R) * (flagOrder m).toPEquiv.toMatrix

variable {m R}

/-- The entries of `P`: row `i` has the single nonzero entry `s_i`, in column `σ i`. -/
theorem antidiagCongrMatrix_apply (i j : Fin (m + m)) :
    antidiagCongrMatrix m R i j = if j = flagOrder m i then antidiagSign m R i else 0 := by
  simp [antidiagCongrMatrix, PEquiv.toMatrix_apply, eq_comm]

/-- Congruence by the signed permutation matrix: `P M Pᵀ` is `M` permuted by the flag order with
the signs `s_i s_j` on its entries. -/
theorem antidiagCongrMatrix_mul_mul_transpose (M : Matrix (Fin (m + m)) (Fin (m + m)) R) :
    antidiagCongrMatrix m R * M * (antidiagCongrMatrix m R)ᵀ =
      diagonal (antidiagSign m R) * M.submatrix (flagOrder m) (flagOrder m) *
        diagonal (antidiagSign m R) := by
  rw [antidiagCongrMatrix, transpose_mul, diagonal_transpose, transpose_toMatrix_flagOrder,
    ← toMatrix_flagOrder_mul_mul]
  simp only [Matrix.mul_assoc]

/-- The transposed congruence: `Pᵀ M P` is `diag(s) M diag(s)` permuted by the flag order. -/
theorem transpose_antidiagCongrMatrix_mul_mul (M : Matrix (Fin (m + m)) (Fin (m + m)) R) :
    (antidiagCongrMatrix m R)ᵀ * M * antidiagCongrMatrix m R =
      (diagonal (antidiagSign m R) * M * diagonal (antidiagSign m R)).submatrix (flagOrder m)
        (flagOrder m) := by
  rw [antidiagCongrMatrix, transpose_mul, diagonal_transpose, transpose_toMatrix_flagOrder,
    ← toMatrix_flagOrder_mul_mul]
  simp only [Matrix.mul_assoc]

theorem diagonal_antidiagSign_mul_self :
    diagonal (antidiagSign m R) * diagonal (antidiagSign m R) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext antidiagSign_mul_self)

@[simp]
theorem antidiagCongrMatrix_mul_transpose :
    antidiagCongrMatrix m R * (antidiagCongrMatrix m R)ᵀ = 1 := by
  have h := antidiagCongrMatrix_mul_mul_transpose (m := m) (R := R) 1
  rwa [Matrix.mul_one, submatrix_one_equiv, Matrix.mul_one, diagonal_antidiagSign_mul_self] at h

@[simp]
theorem transpose_antidiagCongrMatrix_mul :
    (antidiagCongrMatrix m R)ᵀ * antidiagCongrMatrix m R = 1 := by
  have h := transpose_antidiagCongrMatrix_mul_mul (m := m) (R := R) 1
  rwa [Matrix.mul_one, Matrix.mul_one, diagonal_antidiagSign_mul_self, submatrix_one_equiv] at h

/-- The inverse of `P` is its transpose. -/
@[simp]
theorem inv_antidiagCongrMatrix : (antidiagCongrMatrix m R)⁻¹ = (antidiagCongrMatrix m R)ᵀ :=
  inv_eq_left_inv transpose_antidiagCongrMatrix_mul

variable (m R)

/-- The signed permutation `P = diag(s) · P_σ` as an invertible matrix, with inverse `Pᵀ`. -/
def antidiagCongr : GL (Fin (m + m)) R :=
  ⟨antidiagCongrMatrix m R, (antidiagCongrMatrix m R)ᵀ, antidiagCongrMatrix_mul_transpose,
    transpose_antidiagCongrMatrix_mul⟩

variable {m R}

@[simp]
theorem coe_antidiagCongr :
    (antidiagCongr m R : Matrix (Fin (m + m)) (Fin (m + m)) R) = antidiagCongrMatrix m R :=
  (rfl)

/-- The signs of the congruence are preserved by ring homomorphisms. -/
@[simp]
theorem map_antidiagSign {S : Type*} [CommRing S] (f : R →+* S) (i : Fin (m + m)) :
    f (antidiagSign m R i) = antidiagSign m S i := by
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
  · simp
  · simp

/-- The signed permutation `P` is preserved by ring homomorphisms. -/
@[simp]
theorem map_antidiagCongr {S : Type*} [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (antidiagCongr m R) = antidiagCongr m S := by
  apply Units.ext
  ext i j
  simp only [GeneralLinearGroup.map_apply, coe_antidiagCongr, antidiagCongrMatrix_apply,
    apply_ite f, map_antidiagSign, map_zero]

/-- The inverse of `P` is its transpose. -/
theorem coe_antidiagCongr_inv :
    ((antidiagCongr m R)⁻¹ : GL (Fin (m + m)) R) = (antidiagCongrMatrix m R)ᵀ :=
  (rfl)

/-- **The antidiagonal form is congruent to `JFin` by a signed permutation**:
`P Q Pᵀ = JFin m R`. -/
theorem antidiagCongr_mul_JAntidiag_mul_transpose :
    (antidiagCongr m R : Matrix (Fin (m + m)) (Fin (m + m)) R) * JAntidiag m R *
        (antidiagCongr m R : Matrix (Fin (m + m)) (Fin (m + m)) R)ᵀ = JFin m R := by
  rw [coe_antidiagCongr, antidiagCongrMatrix_mul_mul_transpose,
    JAntidiag_eq_neg_submatrix_flagOrder]
  ext i j
  simp only [diagonal_mul, mul_diagonal, submatrix_apply, Matrix.neg_apply, flagOrder_flagOrder]
  refine Fin.addCases (fun a ↦ ?_) (fun a ↦ ?_) i <;>
    refine Fin.addCases (fun b ↦ ?_) (fun b ↦ ?_) j <;>
    simp only [antidiagSign, Fin.addCases_left, Fin.addCases_right, JFin_eq_submatrix,
      submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd] <;>
    simp [J]

/-- **Conjugation by `P` on matrices**: `P⁻¹ M P` is `M` with the signs `s_i s_j` on its entries,
permuted by the flag order. -/
theorem antidiagCongr_inv_mul_mul (M : Matrix (Fin (m + m)) (Fin (m + m)) R) :
    (((antidiagCongr m R)⁻¹ : GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R) * M *
        (antidiagCongr m R : Matrix (Fin (m + m)) (Fin (m + m)) R) =
      (diagonal (antidiagSign m R) * M * diagonal (antidiagSign m R)).submatrix (flagOrder m)
        (flagOrder m) := by
  rw [coe_antidiagCongr_inv, coe_antidiagCongr, transpose_antidiagCongrMatrix_mul_mul]

/-- **The diagonal torus.** Conjugation by `P` sends `diag(d)` to `diag(d ∘ σ)`: the torus
`diag(t₁, …, t_m, t₁⁻¹, …, t_m⁻¹)` of the `JFin` model becomes
`diag(t₁, …, t_m, t_m⁻¹, …, t₁⁻¹)`. -/
theorem antidiagCongr_inv_mul_diagonal_mul (d : Fin (m + m) → R) :
    (((antidiagCongr m R)⁻¹ : GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R) *
        diagonal d * (antidiagCongr m R : Matrix (Fin (m + m)) (Fin (m + m)) R) =
      diagonal (d ∘ flagOrder m) := by
  rw [antidiagCongr_inv_mul_mul, diagonal_mul_diagonal, diagonal_mul_diagonal,
    submatrix_diagonal_equiv]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [mul_comm, ← mul_assoc, antidiagSign_mul_self, one_mul]

/-- **The Borel subgroup.** `P⁻¹ M P` is upper triangular exactly when `M` is upper triangular
after reindexing by the flag order, the condition cutting out the isotropic-flag Borel subgroup in
the `JFin` model. -/
theorem blockTriangular_antidiagCongr_inv_mul_mul_iff (M : Matrix (Fin (m + m)) (Fin (m + m)) R) :
    ((((antidiagCongr m R)⁻¹ : GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R) * M *
        (antidiagCongr m R : Matrix (Fin (m + m)) (Fin (m + m)) R)).BlockTriangular id ↔
      (M.submatrix (flagOrder m) (flagOrder m)).BlockTriangular id := by
  rw [antidiagCongr_inv_mul_mul]
  simp only [BlockTriangular, submatrix_apply, diagonal_mul, mul_diagonal, id,
    IsUnit.mul_left_eq_zero, IsUnit.mul_right_eq_zero, isUnit_antidiagSign]

/-- **The Borel subgroup, conjugated the other way.** `P M P⁻¹` vanishes below the diagonal in
the flag order, the condition cutting out the isotropic-flag Borel subgroup in the `JFin` model,
exactly when `M` is upper triangular. -/
theorem forall_flagOrder_lt_antidiagCongr_mul_mul_inv_eq_zero_iff
    (M : Matrix (Fin (m + m)) (Fin (m + m)) R) :
    (∀ i j, flagOrder m j < flagOrder m i →
        ((antidiagCongr m R : Matrix (Fin (m + m)) (Fin (m + m)) R) * M *
          (((antidiagCongr m R)⁻¹ : GL (Fin (m + m)) R) :
            Matrix (Fin (m + m)) (Fin (m + m)) R)) i j = 0) ↔
      M.BlockTriangular id := by
  rw [coe_antidiagCongr, coe_antidiagCongr_inv, antidiagCongrMatrix_mul_mul_transpose]
  simp only [diagonal_mul, mul_diagonal, submatrix_apply, IsUnit.mul_left_eq_zero,
    IsUnit.mul_right_eq_zero, isUnit_antidiagSign]
  refine ⟨fun h i j hij ↦ ?_, fun h i j hij ↦ h hij⟩
  simpa only [flagOrder_flagOrder] using
    h (flagOrder m i) (flagOrder m j) (by rwa [flagOrder_flagOrder, flagOrder_flagOrder])

end TauCeti
