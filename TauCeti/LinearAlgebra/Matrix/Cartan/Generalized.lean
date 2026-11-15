/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# Generalized Cartan matrices and their Coxeter matrices

A *generalized Cartan matrix* on an index type `I` is an integral matrix `A = (aᵢⱼ)` with
`aᵢᵢ = 2`, `aᵢⱼ ≤ 0` for `i ≠ j`, and `aᵢⱼ = 0 ↔ aⱼᵢ = 0`. No finiteness of `I`, invertibility of
`A`, or symmetrizability is required.

To every generalized Cartan matrix `A` we attach its *Coxeter matrix*
`Matrix.IsGeneralizedCartan.coxeterMatrix`: on the diagonal its entries are `1`, and for `i ≠ j`
its `(i, j)`-entry is `2, 3, 4, 6` according as the Cartan product `aᵢⱼ aⱼᵢ` is `0, 1, 2, 3`, and
`0` (Mathlib's encoding of `∞`) when `aᵢⱼ aⱼᵢ ≥ 4`. Separating the off-diagonal product `4` from
the diagonal product `aᵢᵢ² = 4` is essential: in affine type `A₁⁽¹⁾`, `a₀₁ a₁₀ = (-2)(-2) = 4`
gives infinite dihedral order (`0`), whereas `TauCeti.coxeterOrder 4 = 1`.

## Main definitions

* `Matrix.IsGeneralizedCartan`: the predicate that an integral matrix is a generalized Cartan
  matrix.
* `Matrix.IsGeneralizedCartan.coxeterMatrix`: the `CoxeterMatrix` read off a generalized Cartan
  matrix.

## Main results

* `Matrix.IsGeneralizedCartan.transpose`, `Matrix.IsGeneralizedCartan.submatrix`,
  `Matrix.IsGeneralizedCartan.reindex`, `Matrix.IsGeneralizedCartan.fromBlocks`: closure under
  transposition, principal submatrices, reindexing, and block-diagonal direct sums.
* `Matrix.IsGeneralizedCartan.coxeterMatrix_eq_two_iff`, `coxeterMatrix_eq_three_iff`,
  `coxeterMatrix_eq_four_iff`, `coxeterMatrix_eq_six_iff`, `coxeterMatrix_eq_zero_iff`:
  characterizations of each Coxeter entry by the Cartan product `aᵢⱼ aⱼᵢ`.
* `Matrix.IsGeneralizedCartan.coxeterMatrix_eq_coxeterMatrixOfCartanMatrix`: agreement with
  `TauCeti.coxeterMatrixOfCartanMatrix` when every off-diagonal Cartan product is at most `3`.
* `Matrix.IsFiniteCartan.isGeneralizedCartan`, `TauCeti.SymmetrizableDatum.isGeneralizedCartan`,
  `TauCeti.CartanDatum.isGeneralizedCartan_cartan`: bridges from finite-type Cartan matrices,
  symmetrizable data, and full-lattice Cartan data.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §1.1 and §3.7.
-/

public section

namespace Matrix

/-- An integral matrix `A` indexed by `I` is a **generalized Cartan matrix** if its diagonal
entries are `2`, its off-diagonal entries are nonpositive, and its zero pattern is symmetric. -/
structure IsGeneralizedCartan {I : Type*} (A : Matrix I I ℤ) : Prop where
  /-- Every diagonal entry is `2`. -/
  diag : ∀ i, A i i = 2
  /-- Off-diagonal entries are nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  /-- An entry vanishes if and only if the transposed entry vanishes. -/
  zero_comm : ∀ i j, A i j = 0 ↔ A j i = 0

/-- On an empty index type every matrix is vacously a generalized Cartan matrix. -/
theorem isGeneralizedCartan_of_isEmpty {I : Type*} [IsEmpty I] (A : Matrix I I ℤ) :
    A.IsGeneralizedCartan :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩

namespace IsGeneralizedCartan

variable {I J : Type*} {A : Matrix I I ℤ} (hA : A.IsGeneralizedCartan)
include hA

/-- Over any ring, the entrywise cast of a generalized Cartan matrix has diagonal entries `2`. -/
theorem cast_diag {R : Type*} [NonAssocRing R] (i : I) :
    A.map (Int.cast : ℤ → R) i i = 2 := by
  simp [hA.diag i]

/-- Every Cartan product `aᵢⱼ aⱼᵢ` of a generalized Cartan matrix is nonnegative. -/
theorem mul_nonneg (i j : I) : 0 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hA.diag i]
  · exact mul_nonneg_of_nonpos_of_nonpos (hA.offDiag_nonpos i j hij)
      (hA.offDiag_nonpos j i hij.symm)

/-- The Cartan product `aᵢⱼ aⱼᵢ` vanishes if and only if `aᵢⱼ` vanishes. -/
theorem mul_eq_zero_iff (i j : I) : A i j * A j i = 0 ↔ A i j = 0 := by
  rw [_root_.mul_eq_zero]
  exact or_iff_left_iff_imp.mpr (hA.zero_comm j i).mp

/-- Off the diagonal, a positive Cartan product `aᵢⱼ aⱼᵢ` forces `aᵢⱼ` to be strictly negative. -/
theorem neg_of_mul_pos {i j : I} (h : 0 < A i j * A j i) (hij : i ≠ j) : A i j < 0 := by
  refine lt_of_le_of_ne (hA.offDiag_nonpos i j hij) fun h₀ ↦ ?_
  rw [h₀, zero_mul] at h
  exact lt_irrefl 0 h

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose : A.transpose.IsGeneralizedCartan where
  diag i := hA.diag i
  offDiag_nonpos i j hij := hA.offDiag_nonpos j i hij.symm
  zero_comm i j := hA.zero_comm j i

/-- A principal submatrix of a generalized Cartan matrix along an embedding is a generalized Cartan
matrix. -/
protected theorem submatrix (f : J ↪ I) : (A.submatrix f f).IsGeneralizedCartan where
  diag i := hA.diag (f i)
  offDiag_nonpos i j hij := hA.offDiag_nonpos (f i) (f j) (f.injective.ne hij)
  zero_comm i j := hA.zero_comm (f i) (f j)

/-- Reindexing a generalized Cartan matrix along a bijection gives a generalized Cartan matrix. -/
protected theorem reindex (e : I ≃ J) : (A.reindex e e).IsGeneralizedCartan :=
  hA.submatrix e.symm.toEmbedding

/-- The block-diagonal direct sum of two generalized Cartan matrices is a generalized Cartan
matrix. -/
protected theorem fromBlocks {B : Matrix J J ℤ} (hB : B.IsGeneralizedCartan) :
    (Matrix.fromBlocks A 0 0 B).IsGeneralizedCartan where
  diag := by rintro (i | j) <;> simp [hA.diag, hB.diag]
  offDiag_nonpos := by
    rintro (i | i) (j | j) hij
    · exact hA.offDiag_nonpos i j fun h ↦ hij (congrArg Sum.inl h)
    · simp
    · simp
    · exact hB.offDiag_nonpos i j fun h ↦ hij (congrArg Sum.inr h)
  zero_comm := by rintro (i | i) (j | j) <;> simp [hA.zero_comm, hB.zero_comm]

/-! ### The Coxeter matrix of a generalized Cartan matrix -/

open scoped Classical in
/-- The **Coxeter matrix** of a generalized Cartan matrix (Kac, §3.7): `1` on the diagonal, and for
`i ≠ j` equal to `2, 3, 4, 6` when `aᵢⱼ aⱼᵢ = 0, 1, 2, 3` (`TauCeti.coxeterOrder`), and `0`
(representing `∞`) when `aᵢⱼ aⱼᵢ ≥ 4`. -/
noncomputable def coxeterMatrix : CoxeterMatrix I where
  M := .of fun i j ↦
    if i = j then 1
    else if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i) else 0
  isSymm := by
    ext i j
    simp only [transpose_apply, of_apply, eq_comm (a := j), mul_comm (A j i)]
  diagonal i := by simp
  off_diagonal i j hij := by
    simp only [of_apply, hij, ↓reduceIte]
    split_ifs with hle
    · have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
        have := hA.mul_nonneg i j
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      have := TauCeti.two_le_coxeterOrder hmem
      omega
    · decide

/-- Explicit entry formula for `Matrix.IsGeneralizedCartan.coxeterMatrix`. -/
theorem coxeterMatrix_apply [DecidableEq I] (i j : I) :
    hA.coxeterMatrix i j =
      if i = j then 1
      else if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i) else 0 := by
  unfold coxeterMatrix
  dsimp only [of_apply]
  split_ifs <;> rfl

/-- When `aᵢⱼ aⱼᵢ ≤ 3`, the `(i, j)`-entry of the Coxeter matrix is `TauCeti.coxeterOrder` of the
Cartan product. -/
theorem coxeterMatrix_of_le {i j : I} (h : A i j * A j i ≤ 3) :
    hA.coxeterMatrix i j = TauCeti.coxeterOrder (A i j * A j i) := by
  classical
  have hij : i ≠ j := by
    rintro rfl
    rw [hA.diag i] at h
    omega
  simp [hA.coxeterMatrix_apply, hij, h]

/-- For distinct indices with `aᵢⱼ aⱼᵢ > 3`, the Coxeter entry is `0` (representing `∞`). -/
theorem coxeterMatrix_of_ne_of_lt {i j : I} (hij : i ≠ j) (h : 3 < A i j * A j i) :
    hA.coxeterMatrix i j = 0 := by
  classical
  simp [hA.coxeterMatrix_apply, hij, not_le.mpr h]

/-- Every entry of the Coxeter matrix of a generalized Cartan matrix lies in `{0, 1, 2, 3, 4, 6}`.
-/
theorem coxeterMatrix_le_six (i j : I) : hA.coxeterMatrix i j ≤ 6 := by
  classical
  rw [hA.coxeterMatrix_apply]
  split_ifs with h₁ h₂
  · omega
  · exact TauCeti.coxeterOrder_le_six _
  · omega

/-- A Coxeter entry is `0` (infinite dihedral order) if and only if `i ≠ j` and `aᵢⱼ aⱼᵢ ≥ 4`. -/
theorem coxeterMatrix_eq_zero_iff {i j : I} :
    hA.coxeterMatrix i j = 0 ↔ i ≠ j ∧ 4 ≤ A i j * A j i := by
  classical
  rw [hA.coxeterMatrix_apply]
  split_ifs with hij hle
  · simp [hij]
  · have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
      have := hA.mul_nonneg i j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    have := TauCeti.two_le_coxeterOrder hmem
    omega
  · refine ⟨fun _ ↦ ⟨hij, by omega⟩, fun _ ↦ rfl⟩

/-- A Coxeter entry is `2` if and only if `aᵢⱼ = 0`. -/
theorem coxeterMatrix_eq_two_iff {i j : I} :
    hA.coxeterMatrix i j = 2 ↔ A i j = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · classical
    rw [hA.coxeterMatrix_apply] at h
    split_ifs at h with hij hle
    · omega
    · exact (hA.mul_eq_zero_iff i j).mp (TauCeti.coxeterOrder_eq_two_iff.mp h)
  · have hmul : A i j * A j i = 0 := by rw [h, zero_mul]
    rw [hA.coxeterMatrix_of_le (by omega), hmul, TauCeti.coxeterOrder_zero]

private theorem mem_four_of_le {i j : I} (hle : A i j * A j i ≤ 3) :
    A i j * A j i = 0 ∨ A i j * A j i = 1 ∨ A i j * A j i = 2 ∨ A i j * A j i = 3 := by
  have := hA.mul_nonneg i j
  omega

/-- A Coxeter entry is `3` if and only if `aᵢⱼ aⱼᵢ = 1` (equivalently, `aᵢⱼ = aⱼᵢ = -1`). -/
theorem coxeterMatrix_eq_three_iff {i j : I} :
    hA.coxeterMatrix i j = 3 ↔ A i j * A j i = 1 := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ by rw [hA.coxeterMatrix_of_le (by omega), h, TauCeti.coxeterOrder_one]⟩
  classical
  rw [hA.coxeterMatrix_apply] at h
  split_ifs at h with hij hle
  · omega
  · rcases hA.mem_four_of_le hle with hc | hc | hc | hc <;> rw [hc] at h ⊢ <;> simp at h ⊢

/-- A Coxeter entry is `4` if and only if `aᵢⱼ aⱼᵢ = 2`. -/
theorem coxeterMatrix_eq_four_iff {i j : I} :
    hA.coxeterMatrix i j = 4 ↔ A i j * A j i = 2 := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ by rw [hA.coxeterMatrix_of_le (by omega), h, TauCeti.coxeterOrder_two]⟩
  classical
  rw [hA.coxeterMatrix_apply] at h
  split_ifs at h with hij hle
  · omega
  · rcases hA.mem_four_of_le hle with hc | hc | hc | hc <;> rw [hc] at h ⊢ <;> simp at h ⊢

/-- A Coxeter entry is `6` if and only if `aᵢⱼ aⱼᵢ = 3`. -/
theorem coxeterMatrix_eq_six_iff {i j : I} :
    hA.coxeterMatrix i j = 6 ↔ A i j * A j i = 3 := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ by rw [hA.coxeterMatrix_of_le (by omega), h, TauCeti.coxeterOrder_three]⟩
  classical
  rw [hA.coxeterMatrix_apply] at h
  split_ifs at h with hij hle
  · omega
  · rcases hA.mem_four_of_le hle with hc | hc | hc | hc <;> rw [hc] at h ⊢ <;> simp at h ⊢

/-- Transposing a generalized Cartan matrix leaves its Coxeter matrix unchanged. -/
@[simp]
theorem coxeterMatrix_transpose : hA.transpose.coxeterMatrix = hA.coxeterMatrix := by
  ext i j
  classical
  simp only [coxeterMatrix_apply, transpose_apply, mul_comm (A j i)]

/-- Taking a principal submatrix restricts the Coxeter matrix to the same indices. -/
theorem coxeterMatrix_submatrix (f : J ↪ I) (i j : J) :
    (hA.submatrix f).coxeterMatrix i j = hA.coxeterMatrix (f i) (f j) := by
  classical
  rw [(hA.submatrix f).coxeterMatrix_apply, hA.coxeterMatrix_apply]
  split_ifs with h₁ h₂ <;> simp_all

/-- Reindexing a generalized Cartan matrix reindexes its Coxeter matrix. -/
@[simp]
theorem coxeterMatrix_reindex (e : I ≃ J) :
    (hA.reindex e).coxeterMatrix = hA.coxeterMatrix.reindex e := by
  ext i j
  exact hA.coxeterMatrix_submatrix e.symm.toEmbedding i j

/-- When every off-diagonal Cartan product is at most `3`, `coxeterMatrix` agrees with
`TauCeti.coxeterMatrixOfCartanMatrix`. -/
theorem coxeterMatrix_eq_coxeterMatrixOfCartanMatrix
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) :
    hA.coxeterMatrix = TauCeti.coxeterMatrixOfCartanMatrix A hA.diag hmem := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have hle : A i j * A j i ≤ 3 := by
      have := hmem i j hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      omega
    rw [hA.coxeterMatrix_of_le hle, TauCeti.coxeterMatrixOfCartanMatrix_apply]

end IsGeneralizedCartan

@[simp]
theorem isGeneralizedCartan_transpose {I : Type*} (A : Matrix I I ℤ) :
    A.transpose.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h ↦ h.transpose, IsGeneralizedCartan.transpose⟩

@[simp]
theorem isGeneralizedCartan_submatrix_equiv {I J : Type*} (e : J ≃ I) (A : Matrix I I ℤ) :
    (A.submatrix e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h ↦ by simpa using h.submatrix e.symm.toEmbedding, fun h ↦ h.submatrix e.toEmbedding⟩

theorem isGeneralizedCartan_reindex {I J : Type*} (e : I ≃ J) (A : Matrix I I ℤ) :
    (A.reindex e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan := by
  simp

/-! ### Bridges from finite-type Cartan matrices, symmetrizable data, and Cartan data -/

/-- Every finite-type Cartan matrix is a generalized Cartan matrix. -/
theorem IsFiniteCartan.isGeneralizedCartan {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : A.IsFiniteCartan) : A.IsGeneralizedCartan where
  diag := hA.diag
  offDiag_nonpos := hA.offDiag_nonpos
  zero_comm := hA.zero_comm

end Matrix

namespace TauCeti

/-- The underlying matrix of a symmetrizable datum is a generalized Cartan matrix. -/
theorem SymmetrizableDatum.isGeneralizedCartan {I : Type*} (D : SymmetrizableDatum I) :
    D.cartan.IsGeneralizedCartan where
  diag := D.diag
  offDiag_nonpos := D.offDiag_nonpos
  zero_comm := D.zero_comm

namespace CartanDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

/-- The Cartan matrix of a full-lattice Cartan datum is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_cartan : D.cartan.IsGeneralizedCartan where
  diag := D.cartan_apply_self
  offDiag_nonpos _ _ hij := D.cartan_nonpos hij
  zero_comm := D.cartan_eq_zero_iff

/-- The Coxeter matrix of `D.cartan` agrees entrywise with `CartanDatum.braidLength`. -/
@[simp]
theorem isGeneralizedCartan_cartan_coxeterMatrix_apply [DecidableEq ι] (i j : ι) :
    D.isGeneralizedCartan_cartan.coxeterMatrix i j = D.braidLength i j := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rcases le_or_gt (D.cartan i j * D.cartan j i) 3 with hle | hgt
    · rw [D.isGeneralizedCartan_cartan.coxeterMatrix_of_le hle, D.braidLength_of_le hle]
    · rw [D.isGeneralizedCartan_cartan.coxeterMatrix_of_ne_of_lt hij hgt,
        D.braidLength_of_ne_of_lt hij hgt]

end CartanDatum

end TauCeti
