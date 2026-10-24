/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup

-- Non-public: `noncomm_ring` normalises the conjugation identities below, but no statement
-- mentions it.
import Mathlib.Tactic.NoncommRing

/-!
# The canonical skew-symmetric matrix as a unit, and block matrices in the symplectic group

Mathlib's `Matrix.J` satisfies `J * J = -1`, so it is a unit with inverse `-J`. This file records
that unit and the conjugation cancellation it supports — `X = J * Y * J⁻¹` iff `X * J = J * Y` —
and solves the symplectic inverse formula `SymplecticGroup.inv_eq_symplectic_inv` for the
transpose, `Aᵀ = J * A⁻¹ * J⁻¹`. Conjugation by `J` is the shape the matrix exponential consumes:
the exponential does not interact with `Aᵀ * J = J * (-A)`, but it does turn `Aᵀ = J * (-A) * J⁻¹`
into `(exp A)ᵀ = J * (exp A)⁻¹ * J⁻¹`.

Read entrywise, `Jᵀ = -J` and `J * Jᵀ = 1` become the antisymmetry of the entries and the pairing
of a row of `J` with itself; summing the latter over all rows contracts `J` against itself to
`2 * card l`, the loop value of the symplectic Brauer diagrams up to sign. Read entrywise in the
same way, `Jᵀ * J = 1` is the orthonormality of the columns of `J`.

It also records membership in `Matrix.symplecticGroup` of three families of block matrices, each a
specialisation of `SymplecticGroup.fromBlocks_mem_iff`.

## Main results

* `Matrix.J_mul_neg_J`, `Matrix.neg_J_mul_J` and `Matrix.isUnit_J`: the canonical skew-symmetric
  matrix is a unit, with inverse `-J`.
* `Matrix.J_apply_swap` and `Matrix.sum_J_mul_J`: the two entrywise identities for `J`, its
  antisymmetry and the pairing of a row with itself; `Matrix.sum_sum_J_mul_J` is the double sum of
  the latter, `tr (J * Jᵀ) = 2 * card l`.
* `Matrix.sum_J_mul_J_eq_ite`: the columns of `J` are orthonormal, `Jᵀ * J = 1` read entrywise.
* `Matrix.eq_J_conj_iff_mul_J_eq`: cancelling a conjugation by `J`.
* `SymplecticGroup.transpose_eq_J_conj_inv`: the transpose of a symplectic matrix is the
  `J`-conjugate of its inverse.
* `SymplecticGroup.mem_iff_neg_J_mul_transpose_mul_J_mul_eq_one`: the symplectic matrices are the
  unitary elements for the symplectic adjoint `A ↦ -(J * Aᵀ * J)`.
* `SymplecticGroup.fromBlocks_upper_mem`: `fromBlocks 1 B 0 1` for symmetric `B`;
* `SymplecticGroup.fromBlocks_lower_mem`: `fromBlocks 1 0 C 1` for symmetric `C`;
* `SymplecticGroup.fromBlocks_diagonal_mem`: `fromBlocks A 0 0 D` when `Aᵀ * D = 1`.
-/

public section

open Matrix

namespace Matrix

variable (l : Type*) [DecidableEq l] [Fintype l] (R : Type*) [CommRing R]

/-- `J * (-J) = 1`: the companion of `Matrix.J_squared` in the form the conjugation arguments
below use. -/
theorem J_mul_neg_J : J l R * (-J l R) = 1 := by
  rw [mul_neg, J_squared, neg_neg]

/-- `(-J) * J = 1`, the other one-sided inverse identity for `Matrix.J`. -/
theorem neg_J_mul_J : (-J l R) * J l R = 1 := by
  rw [neg_mul, J_squared, neg_neg]

/-- The canonical skew-symmetric matrix is a unit, with inverse `-J`, because `J * J = -1`. -/
theorem isUnit_J : IsUnit (J l R) :=
  ⟨⟨J l R, -J l R, J_mul_neg_J l R, neg_J_mul_J l R⟩, rfl⟩

omit [Fintype l] in
/-- `J` is antisymmetric, entrywise: `Jᵀ = -J` read at a pair of indices. -/
theorem J_apply_swap (x y : l ⊕ l) : J l R y x = -J l R x y := by
  have h := congrFun (congrFun (J_transpose l R) x) y
  simpa only [transpose_apply, neg_apply] using h

/-- Each row of `J` pairs with itself to `1`, because `J * Jᵀ = 1`. -/
theorem sum_J_mul_J (x : l ⊕ l) : ∑ y : l ⊕ l, J l R x y * J l R x y = 1 := by
  have hJ : J l R * (J l R)ᵀ = 1 := by
    rw [J_transpose]
    exact J_mul_neg_J l R
  have h := congrFun (congrFun hJ x) x
  simpa only [mul_apply, one_apply_eq, transpose_apply] using h

/-- The columns of `J` are orthonormal for the pairing by `J` itself, because `Jᵀ * J = 1`. -/
theorem sum_J_mul_J_eq_ite (y p : l ⊕ l) :
    ∑ x : l ⊕ l, J l R x y * J l R x p = if y = p then 1 else 0 := by
  have hJ : (J l R)ᵀ * J l R = 1 := by
    rw [J_transpose]
    exact neg_J_mul_J l R
  have h := congrFun (congrFun hJ y) p
  simpa only [mul_apply, one_apply, transpose_apply] using h

/-- **`J` contracted against itself** is `tr (J * Jᵀ) = tr 1 = 2 * card l`: the double sum of
`Matrix.sum_J_mul_J` over the `2 * card l` rows. -/
theorem sum_sum_J_mul_J :
    ∑ x : l ⊕ l, ∑ y : l ⊕ l, J l R x y * J l R x y = (2 * Fintype.card l : R) := by
  rw [Finset.sum_congr rfl fun x _ => sum_J_mul_J l R x, Finset.sum_const, Finset.card_univ,
    Fintype.card_sum, nsmul_eq_mul, mul_one, Nat.cast_add, two_mul]

variable {l R}

/-- **Cancelling a conjugation by `J`**: since `J` is a unit, `X` is the `J`-conjugate of `Y`
exactly when `X * J = J * Y`. This is Mathlib's `Matrix.mul_inv_eq_iff_eq_mul_of_invertible` with
the invertibility of `J` supplied; every identity below that moves a matrix past `J` is an instance
of it. -/
theorem eq_J_conj_iff_mul_J_eq (X Y : Matrix (l ⊕ l) (l ⊕ l) R) :
    X = J l R * Y * (J l R)⁻¹ ↔ X * J l R = J l R * Y := by
  have : Invertible (J l R) := ⟨-J l R, neg_J_mul_J l R, J_mul_neg_J l R⟩
  rw [eq_comm, mul_inv_eq_iff_eq_mul_of_invertible, eq_comm]

end Matrix

namespace SymplecticGroup

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

/-- **The transpose of a symplectic matrix is the `J`-conjugate of its inverse.** Mathlib's
`SymplecticGroup.inv_eq_symplectic_inv` computes the inverse as `-J * Aᵀ * J`; cancelling the
conjugation by `J` solves that identity for `Aᵀ` instead. -/
theorem transpose_eq_J_conj_inv {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : A ∈ Matrix.symplecticGroup l R) : Aᵀ = J l R * A⁻¹ * (J l R)⁻¹ := by
  rw [eq_J_conj_iff_mul_J_eq, inv_eq_symplectic_inv A hA]
  calc Aᵀ * J l R = J l R * (-J l R) * (Aᵀ * J l R) := by rw [J_mul_neg_J, one_mul]
    _ = J l R * (-J l R * Aᵀ * J l R) := by noncomm_ring

/-- **Symplectic matrices are the unitary elements for the symplectic adjoint**
`A ↦ J⁻¹ * Aᵀ * J = -(J * Aᵀ * J)`: a matrix is symplectic exactly when its adjoint is a left
inverse. Mathlib's `SymplecticGroup.inv_left_mul_aux` is the forward direction. -/
theorem mem_iff_neg_J_mul_transpose_mul_J_mul_eq_one {A : Matrix (l ⊕ l) (l ⊕ l) R} :
    A ∈ symplecticGroup l R ↔ -(J l R * Aᵀ * J l R * A) = 1 := by
  refine ⟨inv_left_mul_aux, fun h => mem_iff'.mpr ?_⟩
  calc Aᵀ * J l R * A = -J l R * J l R * (Aᵀ * J l R * A) := by rw [neg_J_mul_J, one_mul]
    _ = J l R * -(J l R * Aᵀ * J l R * A) := by noncomm_ring
    _ = J l R := by rw [h, mul_one]

/-- An upper unitriangular block matrix is symplectic when its upper-right block is symmetric. -/
theorem fromBlocks_upper_mem {B : Matrix l l R} (hB : Bᵀ = B) :
    fromBlocks 1 B 0 1 ∈ symplecticGroup l R := by
  rw [fromBlocks_mem_iff]
  simp [hB]

/-- A lower unitriangular block matrix is symplectic when its lower-left block is symmetric. -/
theorem fromBlocks_lower_mem {C : Matrix l l R} (hC : Cᵀ = C) :
    fromBlocks 1 0 C 1 ∈ symplecticGroup l R := by
  rw [fromBlocks_mem_iff]
  simp [hC]

/-- A block-diagonal matrix is symplectic when its diagonal blocks satisfy the defining inverse
transpose relation. -/
theorem fromBlocks_diagonal_mem {A D : Matrix l l R} (hAD : Aᵀ * D = 1) :
    fromBlocks A 0 0 D ∈ symplecticGroup l R := by
  rw [fromBlocks_mem_iff]
  simp [hAD]

end SymplecticGroup
