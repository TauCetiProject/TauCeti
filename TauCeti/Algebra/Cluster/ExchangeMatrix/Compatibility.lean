/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Rank
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Column compatibility and principal compatible pairs

Column compatibility of an extended matrix `B` with a matrix `Λ` means that `BᵀΛ`
is diagonal on the mutable coordinates and vanishes on the frozen coordinates.
The diagonal weights are separate from a positive skew-symmetrizer: they can vanish
or be negative. For skew-symmetric `Λ` they satisfy the skew-symmetrizing identity
on the principal block; over an integral domain, nonzero weights force the extended
columns to be independent.

Every square exchange matrix has a principal extension `(B; 1)` and a compatible
integer alternating form with blocks `(0, -D; D, BᵀD)`, where `D` is its chosen
positive symmetrizer. This construction does not require the original matrix to
be invertible. It supplies the initial compatible pair for principal quantum seeds.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §3, Definition 3.1 and the principal-coefficient construction.
-/

public section

open Matrix

namespace Matrix

variable {I K R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- Column compatibility with weights `w`: `BᵀΛ` has entry `w k` at `(k, row k)`
and zero elsewhere. The weights are not required to be positive or nonzero. -/
def IsColumnCompatible (B : Matrix I K R) (row : K ↪ I) (Λ : Matrix I I R)
    (w : K → R) : Prop :=
  Bᵀ * Λ = of fun k i ↦ if row k = i then w k else 0

/-- The entrywise criterion for column compatibility. -/
theorem isColumnCompatible_iff {B : Matrix I K R} {row : K ↪ I} {Λ : Matrix I I R}
    {w : K → R} : B.IsColumnCompatible row Λ w ↔
      ∀ k i, ∑ j, B j k * Λ j i = if row k = i then w k else 0 :=
  Matrix.ext_iff.symm

namespace IsColumnCompatible

variable {B : Matrix I K R} {row : K ↪ I} {Λ : Matrix I I R} {w : K → R}

/-- The compatible matrix product on a mutable coordinate. -/
theorem apply_row [DecidableEq K] (h : B.IsColumnCompatible row Λ w) (k l : K) :
    (Bᵀ * Λ) k (row l) = if k = l then w k else 0 := by
  rw [h]
  simp

/-- The compatible matrix product vanishes on frozen coordinates. -/
theorem apply_of_not_mem_range (h : B.IsColumnCompatible row Λ w) {i : I}
    (hi : i ∉ Set.range row) (k : K) : (Bᵀ * Λ) k i = 0 := by
  rw [h]
  have hki : row k ≠ i := fun hki ↦ hi ⟨k, hki⟩
  simp [hki]

/-- Column compatibility is preserved by coefficient maps, including noninjective maps. -/
protected theorem map {S : Type*} [CommRing S] (h : B.IsColumnCompatible row Λ w)
    (f : R →+* S) : (B.map f).IsColumnCompatible row (Λ.map f) (f ∘ w) := by
  unfold IsColumnCompatible at h ⊢
  have he := congrArg (fun M ↦ M.map f) h
  simp only [Matrix.map_mul, transpose_map] at he
  rw [he]
  ext k i
  by_cases hki : row k = i <;> simp [hki]

/-- Relabelling all indices preserves column compatibility when the mutable embedding
is relabelled with them. -/
protected theorem reindex {I' K' : Type*} [Fintype I'] [DecidableEq I']
    (h : B.IsColumnCompatible row Λ w) (eI : I ≃ I') (eK : K ≃ K')
    {row' : K' ↪ I'} (hr : ∀ k, eI (row k) = row' (eK k)) :
    (B.reindex eI eK).IsColumnCompatible row' (Λ.reindex eI eI) (w ∘ eK.symm) := by
  apply isColumnCompatible_iff.mpr
  intro k i
  simp only [reindex_apply, submatrix_apply]
  rw [eI.symm.sum_comp (fun j ↦ B j (eK.symm k) * Λ j (eI.symm i)),
    isColumnCompatible_iff.mp h]
  have hr' : row (eK.symm k) = eI.symm (row' k) := by
    simp [Equiv.eq_symm_apply, hr]
  simp [hr']

/-- Contracting a compatible pair with `B` gives the weighted principal block. -/
theorem mul [Fintype K] [DecidableEq K] (h : B.IsColumnCompatible row Λ w) :
    (Bᵀ * Λ) * B = diagonal w * B.submatrix row id := by
  rw [h]
  ext k l
  simp [Matrix.mul_apply, diagonal, eq_comm]

/-- For a skew-symmetric form, compatibility weights skew-symmetrize the mutable block,
without any positivity assumption. -/
theorem weight_mul (h : B.IsColumnCompatible row Λ w)
    (hΛ : Λᵀ = -Λ) (k l : K) :
    w k * B (row k) l = -(w l * B (row l) k) := by
  classical
  let := Fintype.ofInjective row row.injective
  have hs : ((Bᵀ * Λ) * B)ᵀ = -((Bᵀ * Λ) * B) := by
    simp [transpose_mul, hΛ, Matrix.mul_assoc]
  rw [h.mul] at hs
  have he := congrFun (congrFun hs l) k
  simpa using he

/-- Over an integral domain, nonzero compatibility weights force independence of the
extended columns. Skew-symmetry of the form is not needed for this implication. -/
theorem linearIndependent [IsDomain R]
    (h : B.IsColumnCompatible row Λ w) (hw : ∀ k, w k ≠ 0) :
    LinearIndependent R B.col := by
  classical
  exact TauCeti.linearIndependent_of_dotProduct_diagonal
    (w := fun k i ↦ Λ i (row k)) (c := w)
    (fun k ↦ (IsRegular.of_ne_zero (hw k)).right)
    (fun k ↦ by simpa [Matrix.mul_apply, dotProduct] using h.apply_row k k)
    (fun k l hkl ↦ by simpa [Matrix.mul_apply, dotProduct, hkl] using h.apply_row k l)

/-- Over a field, a compatible extended matrix with nonzero weights has full column rank. -/
theorem rank_eq_card {F : Type*} [Field F] [Fintype K]
    {B : Matrix I K F} {Λ : Matrix I I F} {w : K → F}
    (h : B.IsColumnCompatible row Λ w) (hw : ∀ k, w k ≠ 0) :
    B.rank = Fintype.card K := by
  simpa only [row_transpose, rank_transpose] using (h.linearIndependent hw).rank_matrix

end IsColumnCompatible

/-- The zero form is compatible with zero weights, even for rank-deficient matrices. -/
@[simp]
theorem isColumnCompatible_zero (B : Matrix I K R) (row : K ↪ I) :
    B.IsColumnCompatible row 0 0 := by
  apply isColumnCompatible_iff.mpr
  simp

end Matrix

namespace TauCeti.ExchangeMatrix

variable {K : Type*} [DecidableEq K] (B : ExchangeMatrix (Function.Embedding.refl K))

/-- The principal extension of a square exchange matrix, obtained by appending an identity
block of frozen rows. -/
def principalExtension : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ K) where
  matrix := fromRows B.matrix 1
  symmetrizer := B.symmetrizer
  isSkewSymmetrizer := B.isSkewSymmetrizer

@[simp]
theorem principalExtension_matrix : B.principalExtension.matrix = fromRows B.matrix 1 :=
  (rfl)

@[simp]
theorem principalExtension_symmetrizer : B.principalExtension.symmetrizer = B.symmetrizer :=
  (rfl)

/-- The mutable block of the principal extension is the original exchange matrix. -/
@[simp]
theorem principal_principalExtension : B.principalExtension.principal = B := by
  ext i j <;> simp

/-- The canonical integral form for principal coefficients, with blocks
`(0, -D; D, BᵀD)` for `D = diagonal B.symmetrizer`. -/
def principalForm : Matrix (K ⊕ K) (K ⊕ K) ℤ :=
  fromBlocks 0 (-diagonal B.symmetrizer) (diagonal B.symmetrizer)
    (of fun i j ↦ B.matrix j i * B.symmetrizer j)

/-- The mutable-mutable block of the principal form is zero. -/
@[simp]
theorem principalForm_inl_inl (i j : K) : B.principalForm (Sum.inl i) (Sum.inl j) = 0 :=
  (rfl)

/-- The mutable-frozen block is the negative symmetrizer. -/
@[simp]
theorem principalForm_inl_inr (i j : K) :
    B.principalForm (Sum.inl i) (Sum.inr j) = -(diagonal B.symmetrizer i j) :=
  (rfl)

/-- The frozen-mutable block is the symmetrizer. -/
@[simp]
theorem principalForm_inr_inl (i j : K) :
    B.principalForm (Sum.inr i) (Sum.inl j) = diagonal B.symmetrizer i j :=
  (rfl)

/-- The frozen-frozen block has entries `b_{ji} d_j`. -/
@[simp]
theorem principalForm_inr_inr (i j : K) :
    B.principalForm (Sum.inr i) (Sum.inr j) = B.matrix j i * B.symmetrizer j :=
  (rfl)

/-- The principal form is skew-symmetric, including when the exchange matrix is singular. -/
@[simp]
theorem transpose_principalForm : B.principalFormᵀ = -B.principalForm := by
  ext (i | i) (j | j)
  · simp
  · by_cases h : i = j <;> simp [diagonal, h, eq_comm]
  · by_cases h : i = j <;> simp [diagonal, h, eq_comm]
  · simpa [mul_comm] using B.symmetrizer_mul_matrix i j

/-- The principal form has zero diagonal. -/
@[simp]
theorem principalForm_apply_self (i : K ⊕ K) : B.principalForm i i = 0 := by
  rcases i with i | i
  · simp
  · have hd : B.matrix i i = 0 := B.matrix_row_self i
    simp [hd]

/-- Principal extension commutes with simultaneous relabelling of the mutable indices
and their frozen copies. -/
@[simp]
theorem principalExtension_reindex {K' : Type*} [DecidableEq K'] (e : K ≃ K') :
    (reindex e e (fun _ ↦ rfl) B).principalExtension =
      reindex (e.sumCongr e) e (fun _ ↦ rfl) B.principalExtension := by
  ext : 1
  · rw [reindex_matrix (row' := Function.Embedding.inl) B.principalExtension
      (e.sumCongr e) e (fun _ ↦ rfl)]
    ext (i | i) j <;>
      simp [reindex_matrix (row' := Function.Embedding.refl K') B e e (fun _ ↦ rfl),
        Matrix.one_apply]
  · rw [principalExtension_symmetrizer,
      reindex_symmetrizer (row' := Function.Embedding.refl K') B e e (fun _ ↦ rfl),
      reindex_symmetrizer (row' := Function.Embedding.inl) B.principalExtension
        (e.sumCongr e) e (fun _ ↦ rfl),
      principalExtension_symmetrizer]

/-- The principal form commutes with simultaneous relabelling of both copies of the
mutable index set. -/
@[simp]
theorem principalForm_reindex {K' : Type*} [DecidableEq K'] (e : K ≃ K') :
    (reindex e e (fun _ ↦ rfl) B).principalForm =
      B.principalForm.reindex (e.sumCongr e) (e.sumCongr e) := by
  ext (i | i) (j | j) <;>
    simp [diagonal, reindex_apply,
      reindex_matrix (row' := Function.Embedding.refl K') B e e (fun _ ↦ rfl),
      reindex_symmetrizer (row' := Function.Embedding.refl K') B e e (fun _ ↦ rfl)]

section Finite

variable [Fintype K]

/-- The lower-right block of the principal form is `BᵀD` in matrix notation. -/
theorem principalForm_eq_fromBlocks :
    B.principalForm = fromBlocks 0 (-diagonal B.symmetrizer) (diagonal B.symmetrizer)
      (B.matrixᵀ * diagonal B.symmetrizer) := by
  ext (i | i) (j | j) <;> simp only [principalForm, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, mul_diagonal, transpose_apply,
    of_apply]

/-- The bilinear form on the integral exponent lattice defined by the principal matrix
is alternating. -/
theorem isAlt_principalForm : (toBilin' B.principalForm).IsAlt := by
  intro x
  have he := congrArg (fun M ↦ x ⬝ᵥ M *ᵥ x) B.transpose_principalForm
  have ht : x ⬝ᵥ B.principalFormᵀ *ᵥ x = x ⬝ᵥ B.principalForm *ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [ht] at he
  simpa only [neg_mulVec, dotProduct_neg, ← add_eq_zero_iff_eq_neg,
    add_self_eq_zero, toBilin'_apply'] using he

/-- The principal extension and principal form are compatible with the original
positive symmetrizer as weights. -/
theorem isColumnCompatible_principalExtension :
    B.principalExtension.matrix.IsColumnCompatible Function.Embedding.inl
      B.principalForm B.symmetrizer := by
  apply isColumnCompatible_iff.mpr
  intro k i
  rcases i with i | i
  · by_cases h : k = i <;> simp [Fintype.sum_sum_type, diagonal, h, eq_comm]
  · simp only [principalExtension_matrix, fromRows_apply_inl, fromRows_apply_inr,
      Fintype.sum_sum_type, principalForm_inl_inr, principalForm_inr_inr]
    simp [diagonal, Matrix.one_apply, mul_ite, ite_mul, eq_comm]

end Finite

/-- Principal extensions have rationally independent columns, irrespective of the rank
of their mutable block. -/
theorem linearIndependent_principalExtension :
    LinearIndependent ℚ (B.principalExtension.matrix.map (Int.castRingHom ℚ)).col := by
  apply LinearIndependent.of_comp (LinearMap.funLeft ℚ ℚ Sum.inr)
  convert Pi.linearIndependent_single_one K ℚ using 1
  ext k i
  simp [LinearMap.funLeft_apply, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- A zero mutable matrix in rank one still has a nonzero principal compatible form. -/
example (B : ExchangeMatrix (Function.Embedding.refl Unit)) (h : B.symmetrizer () = 1) :
    B.principalForm (Sum.inl ()) (Sum.inr ()) = -1 := by
  simp [h]

/-- Rank zero is admitted by the principal construction. -/
example (B : ExchangeMatrix (Function.Embedding.refl Empty)) :
    B.principalForm = 0 := by
  ext (i | i) <;> exact i.elim

end TauCeti.ExchangeMatrix
