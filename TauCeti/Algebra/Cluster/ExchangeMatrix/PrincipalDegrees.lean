/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Compatibility
public import TauCeti.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Principal compatible pairs with exchange degrees

For a square exchange matrix `B` and column degrees `r`, append the frozen block
`diagonal r`. Unlike the identity frozen block, this extension retains divisibility
of each column by its degree. If the degrees also divide the chosen symmetrizer,
construct the integral alternating form with blocks
`(0, -V; V, W)`, where `V = diagonal (d / r)` and
`W i j = (B j i / r i) * (d j / r j)`.
Its compatibility weights are the original positive symmetrizer `d`.

The construction allows singular and zero mutable matrices and empty index sets.
The extended columns are independent whenever the degrees are nonzero. Degree one
recovers `ExchangeMatrix.principalExtension` and `ExchangeMatrix.principalForm`.
These pairs provide initial data for polynomial exchanges of degrees greater than one.
-/

public section

namespace TauCeti.ExchangeMatrix

open Matrix

variable {K : Type*} [DecidableEq K]
  (B : ExchangeMatrix (Function.Embedding.refl K)) (r : K → ℤ)

/-- The principal extension with frozen block `diagonal r`. Its symmetrizer is
that of the original mutable matrix. -/
def degreePrincipalExtension : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ K) where
  matrix := fromRows B.matrix (diagonal r)
  symmetrizer := B.symmetrizer
  isSkewSymmetrizer := B.isSkewSymmetrizer

@[simp]
theorem degreePrincipalExtension_matrix :
    (B.degreePrincipalExtension r).matrix = fromRows B.matrix (diagonal r) :=
  (rfl)

@[simp]
theorem degreePrincipalExtension_symmetrizer :
    (B.degreePrincipalExtension r).symmetrizer = B.symmetrizer :=
  (rfl)

/-- Taking the mutable block recovers the original matrix, including its symmetrizer. -/
@[simp]
theorem principal_degreePrincipalExtension :
    (B.degreePrincipalExtension r).principal = B := by
  ext i j <;> simp

/-- The principal columns have a common divisor precisely when the mutable columns do,
and the divisor divides the degree of the column. -/
@[simp↓]
theorem dvd_degreePrincipalExtension_column_iff (d : ℤ) (j : K) :
    (∀ i, d ∣ (B.degreePrincipalExtension r).matrix i j) ↔
      (∀ i, d ∣ B.matrix i j) ∧ d ∣ r j := by
  constructor
  · intro h
    exact ⟨fun i ↦ h (Sum.inl i), by simpa [diagonal] using h (Sum.inr j)⟩
  · rintro ⟨hB, hr⟩ (i | i)
    · exact hB i
    · by_cases hij : i = j
      · simpa [diagonal, hij] using hr
      · simp [diagonal, hij]

/-- Column divisibility of the principal extension is exactly column divisibility
of the mutable matrix. -/
@[simp↓]
theorem dvd_degreePrincipalExtension_iff :
    (∀ i j, r j ∣ (B.degreePrincipalExtension r).matrix i j) ↔
      ∀ i j, r j ∣ B.matrix i j := by
  calc
    _ ↔ ∀ j, (∀ i, r j ∣ B.matrix i j) ∧ r j ∣ r j := by
      rw [forall_comm]
      simp_rw [dvd_degreePrincipalExtension_column_iff]
    _ ↔ _ := by
      simp only [dvd_rfl, and_true]
      exact forall_comm

/-- Dividing the principal columns by their nonzero degrees leaves an identity
frozen block. This is the primitive-column presentation used in exchange monomials. -/
theorem of_degreePrincipalExtension_matrix_ediv (hr : ∀ i, r i ≠ 0) :
    (of fun i j ↦ (B.degreePrincipalExtension r).matrix i j / r j) =
      fromRows (of fun i j ↦ B.matrix i j / r j) 1 := by
  ext (i | i) j
  · simp
  · by_cases hij : i = j <;> simp [diagonal, hij, hr]

/-- The integral candidate for the degree-compatible principal form.
The divisions are exact when the degrees divide their columns and the symmetrizer. -/
def degreePrincipalForm : Matrix (K ⊕ K) (K ⊕ K) ℤ :=
  fromBlocks 0 (-diagonal (fun i ↦ B.symmetrizer i / r i))
    (diagonal (fun i ↦ B.symmetrizer i / r i))
    (of fun i j ↦ (B.matrix j i / r i) * (B.symmetrizer j / r j))

@[simp]
theorem degreePrincipalForm_inl_inl (i j : K) :
    B.degreePrincipalForm r (Sum.inl i) (Sum.inl j) = 0 :=
  (rfl)

@[simp]
theorem degreePrincipalForm_inl_inr (i j : K) :
    B.degreePrincipalForm r (Sum.inl i) (Sum.inr j) =
      -(diagonal (fun i ↦ B.symmetrizer i / r i) i j) :=
  (rfl)

@[simp]
theorem degreePrincipalForm_inr_inl (i j : K) :
    B.degreePrincipalForm r (Sum.inr i) (Sum.inl j) =
      diagonal (fun i ↦ B.symmetrizer i / r i) i j :=
  (rfl)

@[simp]
theorem degreePrincipalForm_inr_inr (i j : K) :
    B.degreePrincipalForm r (Sum.inr i) (Sum.inr j) =
      (B.matrix j i / r i) * (B.symmetrizer j / r j) :=
  (rfl)

/-- The whole block-matrix presentation of the degree-compatible principal form. -/
theorem degreePrincipalForm_def :
    B.degreePrincipalForm r =
      fromBlocks 0 (-diagonal (fun i ↦ B.symmetrizer i / r i))
        (diagonal (fun i ↦ B.symmetrizer i / r i))
        (of fun i j ↦ (B.matrix j i / r i) * (B.symmetrizer j / r j)) :=
  (rfl)

/-- Multiplying the frozen-frozen entry by its two degrees recovers the
corresponding entry of `Bᵀ * diagonal d`. This characterizes the integral divisions. -/
theorem degreePrincipalForm_inr_inr_mul {i j : K}
    (hcol : r i ∣ B.matrix j i) (hd : r j ∣ B.symmetrizer j) :
    B.degreePrincipalForm r (Sum.inr i) (Sum.inr j) * (r i * r j) =
      B.matrix j i * B.symmetrizer j := by
  rw [degreePrincipalForm_inr_inr]
  calc
    _ = (B.matrix j i / r i * r i) * (B.symmetrizer j / r j * r j) := by ring
    _ = _ := by rw [Int.ediv_mul_cancel hcol, Int.ediv_mul_cancel hd]

/-- The degree-compatible principal form is skew-symmetric. -/
@[simp]
theorem transpose_degreePrincipalForm
    (hcol : ∀ i j, r j ∣ B.matrix i j) (hd : ∀ i, r i ∣ B.symmetrizer i) :
    (B.degreePrincipalForm r)ᵀ = -B.degreePrincipalForm r := by
  have hr (i) : r i ≠ 0 := ne_zero_of_dvd_ne_zero (B.symmetrizer_pos i).ne' (hd i)
  ext (i | i) (j | j)
  · simp
  · by_cases hij : i = j <;> simp [diagonal, hij, eq_comm]
  · by_cases hij : i = j <;> simp [diagonal, hij, eq_comm]
  · apply mul_right_cancel₀ (mul_ne_zero (hr i) (hr j))
    simp only [transpose_apply, Matrix.neg_apply, neg_mul]
    rw [B.degreePrincipalForm_inr_inr_mul r (hcol j i) (hd j),
      mul_comm (r i) (r j), B.degreePrincipalForm_inr_inr_mul r (hcol i j) (hd i)]
    simpa [mul_comm] using B.symmetrizer_mul_matrix i j

/-- The diagonal vanishes even before imposing the divisibility hypotheses. -/
@[simp]
theorem degreePrincipalForm_apply_self (i : K ⊕ K) :
    B.degreePrincipalForm r i i = 0 := by
  rcases i with i | i
  · simp
  · have hi : B.matrix i i = 0 := B.matrix_row_self i
    simp [hi]

section Finite

variable [Fintype K]

/-- The lower-right block is the product of the divided transpose and the diagonal
quotient of the symmetrizer by the degrees. -/
theorem degreePrincipalForm_eq_fromBlocks :
    B.degreePrincipalForm r = fromBlocks 0 (-diagonal (fun i ↦ B.symmetrizer i / r i))
      (diagonal (fun i ↦ B.symmetrizer i / r i))
      ((of fun i j ↦ B.matrix i j / r j)ᵀ * diagonal (fun i ↦ B.symmetrizer i / r i)) := by
  rw [degreePrincipalForm_def]
  ext (i | i) (j | j) <;> simp

/-- The bilinear form defined by the degree-compatible principal matrix is alternating. -/
theorem isAlt_degreePrincipalForm
    (hcol : ∀ i j, r j ∣ B.matrix i j) (hd : ∀ i, r i ∣ B.symmetrizer i) :
    (toBilin' (B.degreePrincipalForm r)).IsAlt :=
  Matrix.isAlt_toBilin'_of_transpose_eq_neg (B.transpose_degreePrincipalForm r hcol hd)

/-- The degree-compatible principal pair has the original symmetrizer as its weights.
In particular, no invertibility assumption on the mutable matrix is required. -/
theorem isColumnCompatible_degreePrincipalExtension
    (hcol : ∀ i j, r j ∣ B.matrix i j) (hd : ∀ i, r i ∣ B.symmetrizer i) :
    (B.degreePrincipalExtension r).matrix.IsColumnCompatible Function.Embedding.inl
      (B.degreePrincipalForm r) B.symmetrizer := by
  apply isColumnCompatible_iff.mpr
  intro k i
  rcases i with i | i
  · by_cases hki : k = i
    · subst i
      simp [Fintype.sum_sum_type, diagonal, Int.mul_ediv_cancel' (hd k)]
    · simp [Fintype.sum_sum_type, diagonal, hki, eq_comm]
  · simp only [degreePrincipalExtension_matrix, fromRows_apply_inl, fromRows_apply_inr,
      Fintype.sum_sum_type, degreePrincipalForm_inl_inr, degreePrincipalForm_inr_inr]
    simp [diagonal, mul_ite, ite_mul, ← mul_assoc, Int.mul_ediv_cancel' (hcol i k),
      Finset.sum_neg_distrib]

/-- Scaling the frozen basis vectors by their degrees recovers the ordinary
principal form. The mutable basis vectors are fixed. -/
theorem diagonal_mul_degreePrincipalForm_mul_diagonal
    (hcol : ∀ i j, r j ∣ B.matrix i j) (hd : ∀ i, r i ∣ B.symmetrizer i) :
    diagonal (Sum.elim 1 r) * B.degreePrincipalForm r * diagonal (Sum.elim 1 r) =
      B.principalForm := by
  ext (i | i) (j | j)
    <;> simp only [mul_diagonal, diagonal_mul, Sum.elim_inl, Sum.elim_inr,
      Pi.one_apply, one_mul, mul_one]
  · simp
  · by_cases hij : i = j <;>
      simp [diagonal, hij, Int.ediv_mul_cancel (hd j)]
  · by_cases hij : i = j <;>
      simp [diagonal, hij, Int.mul_ediv_cancel' (hd j)]
  · simpa only [mul_assoc, mul_left_comm, principalForm_inr_inr] using
      B.degreePrincipalForm_inr_inr_mul r (hcol j i) (hd j)

end Finite

/-- The frozen diagonal makes the extended columns independent over a ring whenever
the degree images are right-regular, including for infinite index sets. -/
theorem linearIndependent_degreePrincipalExtension {R : Type*} [Ring R]
    (hr : ∀ i, IsRightRegular (r i : R)) :
    LinearIndependent R ((B.degreePrincipalExtension r).matrix.map (Int.castRingHom R)).col := by
  apply LinearIndependent.of_comp (LinearMap.funLeft R R Sum.inr)
  convert (Pi.linearIndependent_single_one K R).smul_of_isRightRegular hr using 1
  ext k i
  by_cases hki : k = i <;>
    simp [LinearMap.funLeft_apply, diagonal, hki, eq_comm]

/-- In finite rank the extended matrix has full column rank whenever the degree images
are right-regular over a commutative ring satisfying the strong rank condition. -/
theorem rank_degreePrincipalExtension [Fintype K] {R : Type*} [CommRing R] [StrongRankCondition R]
    (hr : ∀ i, IsRightRegular (r i : R)) :
    ((B.degreePrincipalExtension r).matrix.map (Int.castRingHom R)).rank = Fintype.card K := by
  rw [Matrix.rank_eq_finrank_span_cols,
    finrank_span_eq_card (B.linearIndependent_degreePrincipalExtension r hr)]

/-! ### Relabelling and degree one -/

/-- Relabelling the mutable coordinates and their frozen copies transports the degrees. -/
@[simp]
theorem degreePrincipalExtension_reindex {K' : Type*} [DecidableEq K'] (e : K ≃ K') :
    (reindex e e (fun _ ↦ rfl) B).degreePrincipalExtension (r ∘ e.symm) =
      reindex (e.sumCongr e) e (fun _ ↦ rfl) (B.degreePrincipalExtension r) := by
  ext : 1
  · rw [reindex_matrix (row' := Function.Embedding.inl) (B.degreePrincipalExtension r)
      (e.sumCongr e) e (fun _ ↦ rfl)]
    ext (i | i) j <;> simp [diagonal,
      reindex_matrix (row' := Function.Embedding.refl K') B e e (fun _ ↦ rfl)]
  · simp only [degreePrincipalExtension_symmetrizer,
      reindex_symmetrizer (row' := Function.Embedding.refl K') B e e (fun _ ↦ rfl),
      reindex_symmetrizer (row' := Function.Embedding.inl) (B.degreePrincipalExtension r)
        (e.sumCongr e) e (fun _ ↦ rfl), degreePrincipalExtension_symmetrizer]

/-- The degree-compatible principal form is equivariant under relabelling. -/
@[simp]
theorem degreePrincipalForm_reindex {K' : Type*} [DecidableEq K'] (e : K ≃ K') :
    (reindex e e (fun _ ↦ rfl) B).degreePrincipalForm (r ∘ e.symm) =
      (B.degreePrincipalForm r).reindex (e.sumCongr e) (e.sumCongr e) := by
  ext (i | i) (j | j) <;>
    simp [diagonal, reindex_apply,
      reindex_matrix (row' := Function.Embedding.refl K') B e e (fun _ ↦ rfl),
      reindex_symmetrizer (row' := Function.Embedding.refl K') B e e (fun _ ↦ rfl)]

/-- Degree one recovers the ordinary principal extension. -/
@[simp]
theorem degreePrincipalExtension_one : B.degreePrincipalExtension 1 = B.principalExtension := by
  ext : 1 <;> simp only [degreePrincipalExtension_matrix, diagonal_one',
    principalExtension_matrix, degreePrincipalExtension_symmetrizer, principalExtension_symmetrizer]

/-- Degree one recovers the ordinary principal compatible form. -/
@[simp]
theorem degreePrincipalForm_one : B.degreePrincipalForm 1 = B.principalForm := by
  ext (i | i) (j | j) <;> simp

end TauCeti.ExchangeMatrix
