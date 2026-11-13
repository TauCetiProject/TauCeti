/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Compatibility
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Divisibility

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

/-- Column divisibility of the principal extension is exactly column divisibility
of the mutable matrix. The new frozen entries impose no additional condition. -/
@[simp↓]
theorem dvd_degreePrincipalExtension_iff :
    (∀ i j, r j ∣ (B.degreePrincipalExtension r).matrix i j) ↔
      ∀ i j, r j ∣ B.matrix i j := by
  constructor
  · exact fun h i j ↦ h (Sum.inl i) j
  · intro h i j
    rcases i with i | i
    · exact h i j
    · by_cases hij : i = j <;> simp [diagonal, hij]

/-- Dividing the principal columns by their nonzero degrees leaves an identity
frozen block. This is the primitive-column presentation used in exchange monomials. -/
theorem degreePrincipalExtension_dividedMatrix (hr : ∀ i, r i ≠ 0) :
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

/-- Multiplying the frozen-frozen entry by its two degrees recovers the
corresponding entry of `Bᵀ * diagonal d`. This characterizes the integral divisions. -/
theorem degreePrincipalForm_inr_inr_mul
    (hcol : ∀ i j, r j ∣ B.matrix i j) (hd : ∀ i, r i ∣ B.symmetrizer i) (i j : K) :
    B.degreePrincipalForm r (Sum.inr i) (Sum.inr j) * (r i * r j) =
      B.matrix j i * B.symmetrizer j := by
  rw [degreePrincipalForm_inr_inr]
  calc
    _ = (B.matrix j i / r i * r i) * (B.symmetrizer j / r j * r j) := by ring
    _ = _ := by rw [Int.ediv_mul_cancel (hcol j i), Int.ediv_mul_cancel (hd j)]

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
    rw [B.degreePrincipalForm_inr_inr_mul r hcol hd i j,
      mul_comm (r i) (r j), B.degreePrincipalForm_inr_inr_mul r hcol hd j i]
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

/-- The bilinear form defined by the degree-compatible principal matrix is alternating. -/
theorem isAlt_degreePrincipalForm
    (hcol : ∀ i j, r j ∣ B.matrix i j) (hd : ∀ i, r i ∣ B.symmetrizer i) :
    (toBilin' (B.degreePrincipalForm r)).IsAlt := by
  intro x
  have he := congrArg (fun M ↦ x ⬝ᵥ M *ᵥ x)
    (B.transpose_degreePrincipalForm r hcol hd)
  have ht : x ⬝ᵥ (B.degreePrincipalForm r)ᵀ *ᵥ x =
      x ⬝ᵥ B.degreePrincipalForm r *ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [ht] at he
  simpa only [neg_mulVec, dotProduct_neg, ← add_eq_zero_iff_eq_neg,
    add_self_eq_zero, toBilin'_apply'] using he

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
      B.degreePrincipalForm_inr_inr_mul r hcol hd i j

end Finite

/-- The frozen diagonal makes the extended columns independent over a coefficient
domain whenever the degree images are nonzero, including for infinite index sets. -/
theorem linearIndependent_degreePrincipalExtension {R : Type*} [CommRing R] [IsDomain R]
    (hr : ∀ i, (r i : R) ≠ 0) :
    LinearIndependent R ((B.degreePrincipalExtension r).matrix.map (Int.castRingHom R)).col := by
  apply LinearIndependent.of_comp (LinearMap.funLeft R R Sum.inr)
  convert (Pi.linearIndependent_single_one K R).smul_of_isRightRegular
    (fun i ↦ (IsRegular.of_ne_zero (hr i)).right) using 1
  ext k i
  by_cases hki : k = i <;>
    simp [LinearMap.funLeft_apply, diagonal, hki, eq_comm]

/-- In finite rank the extended matrix has full rational column rank. -/
theorem rank_degreePrincipalExtension [Fintype K] (hr : ∀ i, r i ≠ 0) :
    ((B.degreePrincipalExtension r).matrix.map (Int.castRingHom ℚ)).rank = Fintype.card K := by
  simpa only [row_transpose, rank_transpose] using
    (B.linearIndependent_degreePrincipalExtension r
      (fun i ↦ Int.cast_ne_zero.mpr (hr i) : ∀ i, (r i : ℚ) ≠ 0)).rank_matrix

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
