/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.IdealEntries
public import TauCeti.LinearAlgebra.Matrix.Symmetric

-- Non-public: `noncomm_ring` normalises the conjugation identities below, and the Schur complement
-- evaluates `det J`, but no statement mentions either.
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NoncommRing

/-!
# The canonical skew-symmetric matrix as a unit, and block matrices in the symplectic group

Mathlib's `Matrix.J` satisfies `J * J = -1`, so it is a unit with inverse `-J`, and its
determinant is `1`. This file records that unit and the conjugation cancellation it supports —
`X = J * Y * J⁻¹` iff `X * J = J * Y` — and solves the symplectic inverse formula
`SymplecticGroup.inv_eq_symplectic_inv` for the transpose, `Aᵀ = J * A⁻¹ * J⁻¹`.
Conjugation by `J` is the shape the matrix exponential consumes:
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
* `Matrix.det_J`: its determinant is `1`.
* `Matrix.star_J` and `Matrix.J_mem_unitaryGroup`: over any star ring its adjoint is `-J`, so
  it is unitary (orthogonal over `ℝ`).
* `Matrix.J_apply_swap` and `Matrix.sum_J_mul_J`: the two entrywise identities for `J`, its
  antisymmetry and the pairing of a row with itself; `Matrix.sum_sum_J_mul_J` is the double sum of
  the latter, `tr (J * Jᵀ) = 2 * card l`.
* `Matrix.J_apply_eq_zero_of_ne_swap` and `Matrix.J_apply_swap_ne_zero`: the nonzero entries of
  `J` are exactly those at the pairs `(x, x.swap)`.
* `Matrix.sum_J_mul_J_eq_ite`: the columns of `J` are orthonormal, `Jᵀ * J = 1` read entrywise.
* `Matrix.eq_J_conj_iff_mul_J_eq`: cancelling a conjugation by `J`.
* `Matrix.J_mul_mul_J_mul_J`: sandwiching twice by `J` is the identity.
* `Matrix.transpose_mul_J_mul_transpose` and `Matrix.mul_J_mul_transpose_apply_self`: the
  congruence transform `C * J * Cᵀ` of `J` by a rectangular matrix is alternating, that is
  antisymmetric with zero diagonal, in every characteristic;
  `Matrix.transpose_mul_J_mul_transpose_sub_J` and `Matrix.mul_J_mul_transpose_apply_self_sub_J`
  say the same of the defect `M * J * Mᵀ - J` of a square matrix `M`.
* `Matrix.exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero`: the linearized symplectic
  equation `E + X * J + J * Xᵀ = 0` is solvable with entries of `X` in an ideal `I` for every
  alternating `E` with entries in `I`, without dividing by two.
* `SymplecticGroup.transpose_eq_J_conj_inv`: the transpose of a symplectic matrix is the
  `J`-conjugate of its inverse; `SymplecticGroup.mem_of_J_conj_eq_transpose` is its converse, a
  matrix whose `J`-conjugate is its inverse transpose is symplectic.
* `SymplecticGroup.mem_iff_neg_J_mul_transpose_mul_J_mul_eq_one`: the symplectic matrices are the
  unitary elements for the symplectic adjoint `A ↦ -(J * Aᵀ * J)`.
* `SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute` and
  `SymplecticGroup.commute_J_of_mem_orthogonalGroup`: among the matrices commuting with `J`, the
  symplectic ones are exactly the orthogonal ones, and an orthogonal symplectic matrix commutes
  with `J`. Any two of the three conditions symplectic, orthogonal and commuting with `J` imply the
  third.
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

/-- The canonical skew-symmetric matrix has determinant one. Mathlib records only
`det J * det J = 1` (`Matrix.J_det_mul_J_det`), which leaves the sign open. -/
@[simp]
theorem det_J : (J l R).det = 1 := by
  -- Multiplying by a unipotent block matrix moves the identity block into the corner, where
  -- `Matrix.det_fromBlocks_one₂₂` evaluates the determinant.
  have hJ : J l R * fromBlocks 1 1 0 1 = fromBlocks 0 (-1) 1 1 := by
    simp [J, fromBlocks_multiply]
  simpa [det_fromBlocks_zero₂₁, det_fromBlocks_one₂₂] using congrArg det hJ

omit [Fintype l] in
/-- The adjoint of the canonical skew-symmetric matrix is `-J`: its entries are `0` and `±1`, which
every star ring fixes, so its adjoint is its transpose. -/
@[simp]
theorem star_J [StarRing R] : star (J l R) = -J l R := by
  simp [star_eq_conjTranspose, J, fromBlocks_conjTranspose, fromBlocks_neg]

/-- The canonical skew-symmetric matrix is unitary, orthogonal over `ℝ`: its adjoint is
`-J = J⁻¹`. -/
theorem J_mem_unitaryGroup [StarRing R] : J l R ∈ unitaryGroup (l ⊕ l) R := by
  rw [mem_unitaryGroup_iff', star_J]
  exact neg_J_mul_J l R

omit [Fintype l] in
/-- `J` is antisymmetric, entrywise: `Jᵀ = -J` read at a pair of indices. -/
theorem J_apply_swap (x y : l ⊕ l) : J l R y x = -J l R x y := by
  have h := congrFun (congrFun (J_transpose l R) x) y
  simpa only [transpose_apply, Matrix.neg_apply] using h

omit [Fintype l] in
/-- An entry of `J` vanishes unless its two indices are the two members `x` and `x.swap` of one
pair. -/
theorem J_apply_eq_zero_of_ne_swap {x y : l ⊕ l} (h : y ≠ x.swap) : J l R x y = 0 := by
  rcases x with i | i <;> rcases y with j | j <;> simp_all [Matrix.J, eq_comm]

omit [Fintype l] in
/-- The entries of `J` at the two members `x` and `x.swap` of a pair are `-1` or `1`, in
particular nonzero. -/
theorem J_apply_swap_ne_zero [Nontrivial R] (x : l ⊕ l) : J l R x x.swap ≠ 0 := by
  rcases x with i | i <;> simp [Matrix.J]

/-- Each row of `J` pairs with itself to `1`, because `J * Jᵀ = 1`. -/
theorem sum_J_mul_J (x : l ⊕ l) : ∑ y : l ⊕ l, J l R x y * J l R x y = 1 := by
  have hJ : J l R * (J l R)ᵀ = 1 := by
    rw [J_transpose]
    exact J_mul_neg_J l R
  have h := congrFun (congrFun hJ x) x
  simpa only [Matrix.mul_apply, one_apply_eq, transpose_apply] using h

/-- The columns of `J` are orthonormal for the standard coordinate dot product, because
`Jᵀ * J = 1`. -/
theorem sum_J_mul_J_eq_ite (y p : l ⊕ l) :
    ∑ x : l ⊕ l, J l R x y * J l R x p = if y = p then 1 else 0 := by
  have hJ : (J l R)ᵀ * J l R = 1 := by
    rw [J_transpose]
    exact neg_J_mul_J l R
  have h := congrFun (congrFun hJ y) p
  simpa only [Matrix.mul_apply, Matrix.one_apply, transpose_apply] using h

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

/-- Sandwiching twice by the standard symplectic matrix is the identity:
`J * (J * M * J) * J = M`, since `J * J = -1`. -/
theorem J_mul_mul_J_mul_J (M : Matrix (l ⊕ l) (l ⊕ l) R) :
    J l R * (J l R * M * J l R) * J l R = M := by
  calc J l R * (J l R * M * J l R) * J l R = (J l R * J l R) * M * (J l R * J l R) := by
        noncomm_ring
    _ = M := by simp [J_squared]

/-- The congruence transform `C * J * Cᵀ` of `J` by a rectangular matrix `C` is antisymmetric. -/
theorem transpose_mul_J_mul_transpose {m : Type*} (C : Matrix m (l ⊕ l) R) :
    (C * J l R * Cᵀ)ᵀ = -(C * J l R * Cᵀ) := by
  simp [transpose_mul, Matrix.mul_assoc]

/-- The congruence transform `C * J * Cᵀ` of `J` has zero diagonal, in every characteristic: its
entries are the values of the standard alternating form on pairs of rows of `C`. -/
@[simp]
theorem mul_J_mul_transpose_apply_self {m : Type*} (C : Matrix m (l ⊕ l) R) (i : m) :
    (C * J l R * Cᵀ) i i = 0 := by
  simp [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, mul_comm]

/-- The defect `M * J * Mᵀ - J` of a matrix is antisymmetric. -/
theorem transpose_mul_J_mul_transpose_sub_J (M : Matrix (l ⊕ l) (l ⊕ l) R) :
    (M * J l R * Mᵀ - J l R)ᵀ = -(M * J l R * Mᵀ - J l R) := by
  rw [transpose_sub, transpose_mul_J_mul_transpose, J_transpose, neg_sub_neg, neg_sub]

/-- The defect `M * J * Mᵀ - J` of a matrix has zero diagonal. -/
theorem mul_J_mul_transpose_apply_self_sub_J (M : Matrix (l ⊕ l) (l ⊕ l) R) (i : l ⊕ l) :
    (M * J l R * Mᵀ - J l R) i i = 0 := by
  rw [Matrix.sub_apply, mul_J_mul_transpose_apply_self]
  simpa using mul_J_mul_transpose_apply_self (1 : Matrix (l ⊕ l) (l ⊕ l) R) i

/-- **The linearized symplectic equation is solvable over an ideal.** An alternating matrix `E`
with entries in an ideal `I` is minus the linearized symplectic defect `X * J + J * Xᵀ` of a
matrix `X` with entries in `I`. The matrix `X` is built from `Matrix.subTransposeEqEquiv`, which
avoids division by two, so this holds in every characteristic. -/
theorem exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero (I : Ideal R)
    (E : Matrix (l ⊕ l) (l ⊕ l) R) (hE_mem : ∀ i j, E i j ∈ I) (hE_transpose : Eᵀ = -E)
    (hE_diag : ∀ i, E i i = 0) :
    ∃ X : Matrix (l ⊕ l) (l ⊕ l) R, (∀ i j, X i j ∈ I) ∧ E + X * J l R + J l R * Xᵀ = 0 := by
  let _ : LinearOrder (l ⊕ l) := (Fintype.equivFin (l ⊕ l)).linearOrder
  have hQ : (-E)ᵀ = -(-E) := by rw [transpose_neg, hE_transpose]
  have hQd : ∀ i, (-E) i i = 0 := fun i => by simp [hE_diag]
  let Y : Matrix (l ⊕ l) (l ⊕ l) R := ((subTransposeEqEquiv hQ hQd).symm 0).1
  have hY_mem : ∀ i j, Y i j ∈ I := fun i j => by
    simp only [Y, coe_subTransposeEqEquiv_symm_apply, Pi.zero_apply, zero_add]
    split_ifs
    · exact I.neg_mem (hE_mem i j)
    · exact I.zero_mem
  have hY_sub : Y - Yᵀ = -E := ((subTransposeEqEquiv hQ hQd).symm 0).2
  have hX_mul_J : -(Y * J l R) * J l R = Y := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, J_squared]
    simp
  have hJ_mul_Xt : J l R * (-(Y * J l R))ᵀ = -Yᵀ := by
    simp [transpose_mul, J_transpose, ← Matrix.mul_assoc, J_squared]
  refine ⟨-(Y * J l R), fun i j => ?_, ?_⟩
  · simpa using I.neg_mem (by simpa using mul_mul_apply_mem hY_mem 1 (J l R) i j)
  · rw [hX_mul_J, hJ_mul_Xt]
    calc
      E + Y + -Yᵀ = E + (Y - Yᵀ) := by abel
      _ = 0 := by rw [hY_sub, add_neg_cancel]

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

/-- **A matrix whose `J`-conjugate is its inverse transpose is symplectic.** If `Y * X = 1` and
`J * X * J⁻¹ = Yᵀ`, that is `(X⁻¹)ᵀ = J * X * J⁻¹`, then `X` is symplectic. This is a converse of
`SymplecticGroup.transpose_eq_J_conj_inv`, with the left inverse `Y` supplied explicitly. -/
theorem mem_of_J_conj_eq_transpose {X Y : Matrix (l ⊕ l) (l ⊕ l) R} (hYX : Y * X = 1)
    (h : J l R * X * (J l R)⁻¹ = Yᵀ) : X ∈ symplecticGroup l R := by
  have hJ : Yᵀ * J l R = J l R * X := (eq_J_conj_iff_mul_J_eq _ _).1 h.symm
  rw [mem_iff', Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, ← transpose_mul, hYX, transpose_one,
    Matrix.one_mul]

/-- **Symplectic matrices are the unitary elements for the symplectic adjoint**
`A ↦ J⁻¹ * Aᵀ * J = -(J * Aᵀ * J)`: a matrix is symplectic exactly when its adjoint is a left
inverse. Mathlib's `SymplecticGroup.inv_left_mul_aux` is the forward direction. -/
theorem mem_iff_neg_J_mul_transpose_mul_J_mul_eq_one {A : Matrix (l ⊕ l) (l ⊕ l) R} :
    A ∈ symplecticGroup l R ↔ -(J l R * Aᵀ * J l R * A) = 1 := by
  refine ⟨inv_left_mul_aux, fun h => mem_iff'.mpr ?_⟩
  calc Aᵀ * J l R * A = -J l R * J l R * (Aᵀ * J l R * A) := by rw [neg_J_mul_J, one_mul]
    _ = J l R * -(J l R * Aᵀ * J l R * A) := by noncomm_ring
    _ = J l R := by rw [h, mul_one]

/-- **For a matrix commuting with `J`, symplectic means orthogonal**: if `A * J = J * A` then
`A * J * Aᵀ = J * (A * Aᵀ)`, which is `J` exactly when `A * Aᵀ = 1`, since `J` is a unit. -/
theorem mem_iff_mem_orthogonalGroup_of_commute {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (h : Commute (J l R) A) : A ∈ symplecticGroup l R ↔ A ∈ orthogonalGroup (l ⊕ l) R := by
  rw [mem_iff, mem_orthogonalGroup_iff, ← h.eq, Matrix.mul_assoc, (isUnit_J l R).mul_eq_left]

/-- **An orthogonal symplectic matrix commutes with `J`**: from `A * J * Aᵀ = J` and
`Aᵀ * A = 1`, multiplying on the right by `A` gives `A * J = J * A`. -/
theorem commute_J_of_mem_orthogonalGroup {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hS : A ∈ symplecticGroup l R) (hO : A ∈ orthogonalGroup (l ⊕ l) R) :
    Commute (J l R) A := by
  rw [mem_iff] at hS
  rw [mem_orthogonalGroup_iff'] at hO
  calc J l R * A = A * J l R * Aᵀ * A := by rw [hS]
    _ = A * J l R := by rw [Matrix.mul_assoc, hO, Matrix.mul_one]

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
