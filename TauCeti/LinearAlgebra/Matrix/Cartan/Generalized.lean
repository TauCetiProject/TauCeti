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
`aᵢᵢ = 2`, `aᵢⱼ ≤ 0` for `i ≠ j`, and `aᵢⱼ = 0 ↔ aⱼᵢ = 0`, without finiteness, invertibility, or
symmetrizability hypotheses. Its *Coxeter matrix* `Matrix.IsGeneralizedCartan.coxeterMatrix` has
`1` on the diagonal and, for `i ≠ j`, equals `2, 3, 4, 6` according as `aᵢⱼ aⱼᵢ = 0, 1, 2, 3`, and
`0` (`∞`) when `aᵢⱼ aⱼᵢ ≥ 4`. Separating off-diagonal `aᵢⱼ aⱼᵢ = 4` (order `0`, as in `A₁⁽¹⁾`) from
diagonal `aᵢᵢ² = 4` (`TauCeti.coxeterOrder 4 = 1`) is essential beyond finite type.

## Main definitions and results

* `Matrix.IsGeneralizedCartan`: the generalized Cartan matrix predicate, closed under `transpose`,
  `submatrix`, `reindex`, and `fromBlocks`, with bridges from `Matrix.IsFiniteCartan`,
  `TauCeti.SymmetrizableDatum`, and `TauCeti.CartanDatum`.
* `Matrix.IsGeneralizedCartan.coxeterMatrix`: the associated `CoxeterMatrix`, entrywise
  characterizations for `0, 2, 3, 4, 6`, and agreement with `TauCeti.coxeterMatrixOfCartanMatrix`
  and `TauCeti.CartanDatum.braidLength`.

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

/-- On an empty index type every matrix is vacuously a generalized Cartan matrix. -/
theorem isGeneralizedCartan_of_isEmpty {I : Type*} [IsEmpty I] (A : Matrix I I ℤ) :
    A.IsGeneralizedCartan :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩

namespace IsGeneralizedCartan

variable {I J : Type*} {A : Matrix I I ℤ} (hA : A.IsGeneralizedCartan)
include hA

/-- Over any ring, the entrywise cast of a generalized Cartan matrix has diagonal entries `2`. -/
theorem cast_diag {R : Type*} [NonAssocRing R] (i : I) : A.map (Int.cast : ℤ → R) i i = 2 := by
  simp [hA.diag i]

/-- Every Cartan product `aᵢⱼ aⱼᵢ` of a generalized Cartan matrix is nonnegative. -/
theorem mul_nonneg (i j : I) : 0 ≤ A i j * A j i := by
  obtain rfl | hij := eq_or_ne i j
  · simp [hA.diag i]
  · exact mul_nonneg_of_nonpos_of_nonpos (hA.offDiag_nonpos i j hij)
      (hA.offDiag_nonpos j i hij.symm)

/-- The Cartan product `aᵢⱼ aⱼᵢ` vanishes if and only if `aᵢⱼ` vanishes. -/
theorem mul_eq_zero_iff (i j : I) : A i j * A j i = 0 ↔ A i j = 0 :=
  _root_.mul_eq_zero.trans (or_iff_left_iff_imp.mpr (hA.zero_comm j i).mp)

/-- Off the diagonal, a positive Cartan product `aᵢⱼ aⱼᵢ` forces `aᵢⱼ` to be strictly negative. -/
theorem neg_of_mul_pos {i j : I} (h : 0 < A i j * A j i) (hij : i ≠ j) : A i j < 0 :=
  lt_of_le_of_ne (hA.offDiag_nonpos i j hij) fun h₀ ↦ by simp [h₀] at h

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose : A.transpose.IsGeneralizedCartan where
  diag i := hA.diag i
  offDiag_nonpos i j hij := hA.offDiag_nonpos j i hij.symm
  zero_comm i j := hA.zero_comm j i

/-- A principal submatrix of a generalized Cartan matrix along an embedding is again one. -/
protected theorem submatrix (f : J ↪ I) : (A.submatrix f f).IsGeneralizedCartan where
  diag i := hA.diag (f i)
  offDiag_nonpos i j hij := hA.offDiag_nonpos (f i) (f j) (f.injective.ne hij)
  zero_comm i j := hA.zero_comm (f i) (f j)

/-- Reindexing a generalized Cartan matrix along a bijection gives a generalized Cartan matrix. -/
protected theorem reindex (e : I ≃ J) : (A.reindex e e).IsGeneralizedCartan :=
  hA.submatrix e.symm.toEmbedding

/-- The block-diagonal direct sum of two generalized Cartan matrices is generalized Cartan. -/
protected theorem fromBlocks {B : Matrix J J ℤ} (hB : B.IsGeneralizedCartan) :
    (Matrix.fromBlocks A 0 0 B).IsGeneralizedCartan where
  diag := by rintro (i | j) <;> simp [hA.diag, hB.diag]
  offDiag_nonpos := by
    rintro (i | i) (j | j) hij
    · exact hA.offDiag_nonpos i j (hij ∘ congrArg Sum.inl)
    · simp
    · simp
    · exact hB.offDiag_nonpos i j (hij ∘ congrArg Sum.inr)
  zero_comm := by rintro (i | i) (j | j) <;> simp [hA.zero_comm, hB.zero_comm]

/-! ### The Coxeter matrix of a generalized Cartan matrix -/

private theorem mem_four_set_of_le {i j : I} (hle : A i j * A j i ≤ 3) :
    A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
  have := hA.mul_nonneg i j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

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
    · exact ne_of_gt (lt_of_lt_of_le one_lt_two
        (TauCeti.two_le_coxeterOrder (hA.mem_four_set_of_le hle)))
    · decide

/-- Explicit entry formula for `Matrix.IsGeneralizedCartan.coxeterMatrix`. -/
theorem coxeterMatrix_apply [DecidableEq I] (i j : I) :
    hA.coxeterMatrix i j =
      if i = j then 1
      else if A i j * A j i ≤ 3 then TauCeti.coxeterOrder (A i j * A j i) else 0 := by
  unfold coxeterMatrix
  dsimp only [of_apply]
  split_ifs <;> rfl

/-- When `aᵢⱼ aⱼᵢ ≤ 3`, `(hA.coxeterMatrix) i j = TauCeti.coxeterOrder (A i j * A j i)`. -/
theorem coxeterMatrix_of_le {i j : I} (h : A i j * A j i ≤ 3) :
    hA.coxeterMatrix i j = TauCeti.coxeterOrder (A i j * A j i) := by
  classical
  have hij : i ≠ j := fun heq ↦ by simp [heq, hA.diag j] at h
  simp [hA.coxeterMatrix_apply, hij, h]

/-- For distinct indices with `aᵢⱼ aⱼᵢ > 3`, the Coxeter entry is `0` (representing `∞`). -/
theorem coxeterMatrix_of_ne_of_lt {i j : I} (hij : i ≠ j) (h : 3 < A i j * A j i) :
    hA.coxeterMatrix i j = 0 := by
  classical
  simp [hA.coxeterMatrix_apply, hij, not_le.mpr h]

/-- Every entry of the Coxeter matrix of a generalized Cartan matrix is at most `6`. -/
theorem coxeterMatrix_le_six (i j : I) : hA.coxeterMatrix i j ≤ 6 := by
  classical
  rw [hA.coxeterMatrix_apply]
  split_ifs
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
  · have := TauCeti.two_le_coxeterOrder (hA.mem_four_set_of_le hle)
    omega
  · exact ⟨fun _ ↦ ⟨hij, by omega⟩, fun _ ↦ rfl⟩

/-- A Coxeter entry is `2` if and only if `aᵢⱼ = 0`. -/
theorem coxeterMatrix_eq_two_iff {i j : I} : hA.coxeterMatrix i j = 2 ↔ A i j = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · classical
    rw [hA.coxeterMatrix_apply] at h
    split_ifs at h with hij hle
    · omega
    · exact (hA.mul_eq_zero_iff i j).mp (TauCeti.coxeterOrder_eq_two_iff.mp h)
  · rw [hA.coxeterMatrix_of_le (by simp [h]), h, zero_mul, TauCeti.coxeterOrder_zero]

private theorem coxeterMatrix_eq_iff_aux {i j : I} {m : ℕ} {c : ℤ} (hm : 1 < m) (hc : c ≤ 3)
    (hord : TauCeti.coxeterOrder c = m)
    (hinj : ∀ x ∈ ({0, 1, 2, 3} : Set ℤ), TauCeti.coxeterOrder x = m → x = c) :
    hA.coxeterMatrix i j = m ↔ A i j * A j i = c := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [hA.coxeterMatrix_of_le (h ▸ hc), h, hord]⟩
  classical
  rw [hA.coxeterMatrix_apply] at h
  split_ifs at h with hij hle
  · omega
  · exact hinj _ (hA.mem_four_set_of_le hle) h
  · omega

/-- A Coxeter entry is `3` if and only if `aᵢⱼ aⱼᵢ = 1` (equivalently, `aᵢⱼ = aⱼᵢ = -1`). -/
theorem coxeterMatrix_eq_three_iff {i j : I} : hA.coxeterMatrix i j = 3 ↔ A i j * A j i = 1 :=
  hA.coxeterMatrix_eq_iff_aux (by decide) (by decide) TauCeti.coxeterOrder_one <| by
    rintro x (rfl | rfl | rfl | rfl) <;> simp

/-- A Coxeter entry is `4` if and only if `aᵢⱼ aⱼᵢ = 2`. -/
theorem coxeterMatrix_eq_four_iff {i j : I} : hA.coxeterMatrix i j = 4 ↔ A i j * A j i = 2 :=
  hA.coxeterMatrix_eq_iff_aux (by decide) (by decide) TauCeti.coxeterOrder_two <| by
    rintro x (rfl | rfl | rfl | rfl) <;> simp

/-- A Coxeter entry is `6` if and only if `aᵢⱼ aⱼᵢ = 3`. -/
theorem coxeterMatrix_eq_six_iff {i j : I} : hA.coxeterMatrix i j = 6 ↔ A i j * A j i = 3 :=
  hA.coxeterMatrix_eq_iff_aux (by decide) (by decide) TauCeti.coxeterOrder_three <| by
    rintro x (rfl | rfl | rfl | rfl) <;> simp

/-- Transposing a generalized Cartan matrix leaves its Coxeter matrix unchanged. -/
@[simp] theorem coxeterMatrix_transpose : hA.transpose.coxeterMatrix = hA.coxeterMatrix := by
  classical
  ext i j
  simp only [coxeterMatrix_apply, transpose_apply, mul_comm (A j i)]

/-- Taking a principal submatrix restricts the Coxeter matrix to the same indices. -/
theorem coxeterMatrix_submatrix (f : J ↪ I) (i j : J) :
    (hA.submatrix f).coxeterMatrix i j = hA.coxeterMatrix (f i) (f j) := by
  classical
  rw [(hA.submatrix f).coxeterMatrix_apply, hA.coxeterMatrix_apply]
  split_ifs <;> simp_all

/-- Reindexing a generalized Cartan matrix reindexes its Coxeter matrix. -/
@[simp] theorem coxeterMatrix_reindex (e : I ≃ J) :
    (hA.reindex e).coxeterMatrix = hA.coxeterMatrix.reindex e := by
  ext i j
  exact hA.coxeterMatrix_submatrix e.symm.toEmbedding i j

/-- When every off-diagonal Cartan product is at most `3`, `coxeterMatrix` agrees with
`TauCeti.coxeterMatrixOfCartanMatrix`. -/
theorem coxeterMatrix_eq_coxeterMatrixOfCartanMatrix
    (hmem : ∀ i j, i ≠ j → A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)) :
    hA.coxeterMatrix = TauCeti.coxeterMatrixOfCartanMatrix A hA.diag hmem := by
  ext i j
  obtain rfl | hij := eq_or_ne i j
  · simp
  · have hle : A i j * A j i ≤ 3 := by
      have hm := hmem i j hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      omega
    rw [hA.coxeterMatrix_of_le hle, TauCeti.coxeterMatrixOfCartanMatrix_apply]

end IsGeneralizedCartan

@[simp] theorem isGeneralizedCartan_transpose {I : Type*} (A : Matrix I I ℤ) :
    A.transpose.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨IsGeneralizedCartan.transpose, IsGeneralizedCartan.transpose⟩

@[simp] theorem isGeneralizedCartan_submatrix_equiv {I J : Type*} (e : J ≃ I) (A : Matrix I I ℤ) :
    (A.submatrix e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h ↦ by simpa using h.submatrix e.symm.toEmbedding, fun h ↦ h.submatrix e.toEmbedding⟩

theorem isGeneralizedCartan_reindex {I J : Type*} (e : I ≃ J) (A : Matrix I I ℤ) :
    (A.reindex e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan := by simp

/-! ### Bridges from finite-type Cartan matrices, symmetrizable data, and Cartan data -/

/-- Every finite-type Cartan matrix is a generalized Cartan matrix. -/
theorem IsFiniteCartan.isGeneralizedCartan {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : A.IsFiniteCartan) : A.IsGeneralizedCartan :=
  ⟨hA.diag, hA.offDiag_nonpos, hA.zero_comm⟩

end Matrix

namespace TauCeti

/-- The underlying matrix of a symmetrizable datum is a generalized Cartan matrix. -/
theorem SymmetrizableDatum.isGeneralizedCartan {I : Type*} (D : SymmetrizableDatum I) :
    D.cartan.IsGeneralizedCartan :=
  ⟨D.diag, D.offDiag_nonpos, D.zero_comm⟩

namespace CartanDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

/-- The Cartan matrix of a full-lattice Cartan datum is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_cartan : D.cartan.IsGeneralizedCartan :=
  ⟨D.cartan_apply_self, fun _ _ ↦ D.cartan_nonpos, D.cartan_eq_zero_iff⟩

/-- The Coxeter matrix of `D.cartan` agrees entrywise with `CartanDatum.braidLength`. -/
@[simp] theorem isGeneralizedCartan_cartan_coxeterMatrix_apply [DecidableEq ι] (i j : ι) :
    D.isGeneralizedCartan_cartan.coxeterMatrix i j = D.braidLength i j := by
  obtain rfl | hij := eq_or_ne i j
  · simp
  · rcases le_or_gt (D.cartan i j * D.cartan j i) 3 with hle | hgt
    · rw [D.isGeneralizedCartan_cartan.coxeterMatrix_of_le hle, D.braidLength_of_le hle]
    · rw [D.isGeneralizedCartan_cartan.coxeterMatrix_of_ne_of_lt hij hgt,
        D.braidLength_of_ne_of_lt hij hgt]

end CartanDatum

end TauCeti
