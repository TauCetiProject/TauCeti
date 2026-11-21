/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Basic

/-!
# Ice quivers and rectangular exchange matrices

An ice quiver records the finite number of arrows between each ordered pair of vertices,
with mutable vertices specified by an embedding. It has no loops, oriented two-cycles, or
arrows between two frozen vertices. No finiteness of the vertex sets is required.

The matrix convention is `bᵢₖ = qᵢₖ - qₖᵢ`, where a positive entry records arrows from
the row vertex to the mutable column vertex.
The bijection `IceQuiver.matrixEquiv` identifies ice quivers with raw rectangular integer
matrices whose principal block is skew-symmetric, without an additional chosen symmetrizer.
`IceQuiver.toExchangeMatrix` supplies the canonical symmetrizer-one exchange matrix for
skew-symmetric seeds with frozen variables, and `IceQuiver.reindex` relabels vertices compatibly.

## References

* S. Fomin, L. Williams and A. Zelevinsky, *Introduction to Cluster Algebras. Chapters 1–3*,
  [arXiv:1608.05735](https://arxiv.org/abs/1608.05735), §§2.1, 2.6–2.7.
-/

public section

namespace TauCeti

/-- A quiver with designated mutable vertices, no loops, no two-cycles, and no arrows between
frozen vertices. `arrows i j` counts the arrows from `i` to `j`. -/
@[ext]
structure IceQuiver {I K : Type*} (row : K ↪ I) where
  /-- The number of arrows between each ordered pair of vertices. -/
  arrows : I → I → ℕ
  /-- There are no loops. -/
  arrows_self : ∀ i, arrows i i = 0
  /-- There is at most one direction of arrows between two vertices. -/
  arrows_mul_arrows_eq_zero : ∀ i j, arrows i j * arrows j i = 0
  /-- There are no arrows between two frozen vertices. -/
  arrows_eq_zero_of_notMem_range : ∀ i j, i ∉ Set.range row → j ∉ Set.range row → arrows i j = 0

namespace IceQuiver

attribute [simp] arrows_self

variable {I K : Type*} {row : K ↪ I}

/-- The rectangular integer matrix of an ice quiver, with columns indexed by mutable
vertices. -/
def matrix (q : IceQuiver row) : Matrix I K ℤ :=
  fun i k ↦ (q.arrows i (row k) : ℤ) - q.arrows (row k) i

theorem matrix_apply (q : IceQuiver row) (i : I) (k : K) :
    q.matrix i k = (q.arrows i (row k) : ℤ) - q.arrows (row k) i := (rfl)

/-- The principal block of a quiver matrix is skew-symmetric. -/
theorem matrix_skew (q : IceQuiver row) (i j : K) :
    q.matrix (row i) j = -q.matrix (row j) i := by
  simp only [matrix_apply]
  omega

/-- The mutable diagonal entries of a quiver matrix vanish. -/
@[simp]
theorem matrix_row_self (q : IceQuiver row) (k : K) : q.matrix (row k) k = 0 := by
  simp [matrix_apply]

/-- The diagonal entries of an unfrozen quiver matrix vanish. -/
@[simp]
theorem matrix_refl_self (q : IceQuiver (Function.Embedding.refl K)) (k : K) :
    q.matrix k k = 0 := q.matrix_row_self k

/-- Regard the quiver matrix as an exchange matrix with canonical symmetrizer one. This does
not identify quivers with exchange matrices carrying arbitrary chosen symmetrizers. -/
def toExchangeMatrix (q : IceQuiver row) : ExchangeMatrix row where
  matrix := q.matrix
  symmetrizer := fun _ ↦ 1
  isSkewSymmetrizer :=
    ⟨fun _ ↦ by decide, fun i j ↦ by simpa using q.matrix_skew i j⟩

@[simp]
theorem toExchangeMatrix_matrix (q : IceQuiver row) : q.toExchangeMatrix.matrix = q.matrix :=
  (rfl)

@[simp]
theorem toExchangeMatrix_symmetrizer (q : IceQuiver row) :
    q.toExchangeMatrix.symmetrizer = 1 := (rfl)

/-- The positive part of a quiver matrix entry is its forward arrow count. -/
@[simp]
theorem posPart_matrix (q : IceQuiver row) (i : I) (k : K) :
    (q.matrix i k)⁺ = (q.arrows i (row k) : ℤ) := by
  rcases Nat.mul_eq_zero.mp (q.arrows_mul_arrows_eq_zero i (row k)) with h | h
  · simp [matrix_apply, h]
  · simp [matrix_apply, h]

/-- The negative part of a quiver matrix entry is its reverse arrow count. -/
@[simp]
theorem negPart_matrix (q : IceQuiver row) (i : I) (k : K) :
    (q.matrix i k)⁻ = (q.arrows (row k) i : ℤ) := by
  rcases Nat.mul_eq_zero.mp (q.arrows_mul_arrows_eq_zero i (row k)) with h | h
  · simp [matrix_apply, h]
  · simp [matrix_apply, h]

/-- Taking the nonnegative part of a matrix entry recovers the arrow count toward the mutable
vertex. -/
@[simp]
theorem toNat_matrix (q : IceQuiver row) (i : I) (k : K) :
    (q.matrix i k).toNat = q.arrows i (row k) := by
  rcases Nat.mul_eq_zero.mp (q.arrows_mul_arrows_eq_zero i (row k)) with h | h <;>
    simp [matrix_apply, h]

/-- Taking the nonnegative part of the negated matrix entry recovers the reverse arrows. -/
@[simp]
theorem toNat_neg_matrix (q : IceQuiver row) (i : I) (k : K) :
    (-q.matrix i k).toNat = q.arrows (row k) i := by
  rcases Nat.mul_eq_zero.mp (q.arrows_mul_arrows_eq_zero i (row k)) with h | h <;>
    simp [matrix_apply, h]

/-- A quiver is determined by its rectangular matrix: all omitted frozen--frozen entries are
zero, and the other arrows are recovered from the positive and negative parts. -/
theorem matrix_injective : Function.Injective (matrix (row := row)) := by
  intro q q' h
  ext i j
  by_cases hj : j ∈ Set.range row
  · obtain ⟨k, rfl⟩ := hj
    rw [← q.toNat_matrix i k, ← q'.toNat_matrix i k, h]
  · by_cases hi : i ∈ Set.range row
    · obtain ⟨k, rfl⟩ := hi
      rw [← q.toNat_neg_matrix j k, ← q'.toNat_neg_matrix j k, h]
    · rw [q.arrows_eq_zero_of_notMem_range i j hi hj, q'.arrows_eq_zero_of_notMem_range i j hi hj]

@[simp]
theorem matrix_inj {q q' : IceQuiver row} : q.matrix = q'.matrix ↔ q = q' :=
  matrix_injective.eq_iff

/-- The canonical exchange-matrix construction is injective. -/
theorem toExchangeMatrix_injective : Function.Injective (toExchangeMatrix (row := row)) := by
  intro q q' h
  exact matrix_injective (congrArg ExchangeMatrix.matrix h)

@[simp]
theorem toExchangeMatrix_inj {q q' : IceQuiver row} :
    q.toExchangeMatrix = q'.toExchangeMatrix ↔ q = q' := toExchangeMatrix_injective.eq_iff

/-! ### Recovering a quiver from a rectangular matrix -/

private noncomputable def completion (row : K ↪ I) (B : Matrix I K ℤ) (i j : I) : ℤ :=
  Function.extend row (B i) (fun j ↦ Function.extend row (-B j ·) 0 i) j

private theorem completion_col (B : Matrix I K ℤ) (i : I) (k : K) :
    completion row B i (row k) = B i k :=
  row.injective.extend_apply _ _ k

private theorem completion_row (B : Matrix I K ℤ) (k : K) (j : I)
    (hj : j ∉ Set.range row) : completion row B (row k) j = -B j k := by
  rw [completion, Function.extend_apply' _ _ j hj, row.injective.extend_apply]

private theorem completion_frozen (B : Matrix I K ℤ) (i j : I)
    (hi : i ∉ Set.range row) (hj : j ∉ Set.range row) : completion row B i j = 0 := by
  rw [completion, Function.extend_apply' _ _ j hj, Function.extend_apply' _ _ i hi,
    Pi.zero_apply]

private theorem completion_skew (B : Matrix I K ℤ)
    (hB : ∀ i j, B (row i) j = -B (row j) i) (i j : I) :
    completion row B i j = -completion row B j i := by
  by_cases hi : i ∈ Set.range row
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : j ∈ Set.range row
    · obtain ⟨l, rfl⟩ := hj
      simpa only [completion_col] using hB k l
    · rw [completion_row B k j hj, completion_col]
  · by_cases hj : j ∈ Set.range row
    · obtain ⟨k, rfl⟩ := hj
      rw [completion_col, completion_row B k i hi, neg_neg]
    · rw [completion_frozen B i j hi hj, completion_frozen B j i hj hi, neg_zero]

/-- Recover the unique ice quiver whose matrix is `B`. The principal skew-symmetry condition
is precisely what makes the prescriptions in two mutable directions agree. -/
noncomputable def ofMatrix (B : Matrix I K ℤ)
    (hB : ∀ i j, B (row i) j = -B (row j) i) : IceQuiver row where
  arrows i j := (completion row B i j).toNat
  arrows_self i := by
    have h := completion_skew B hB i i
    have hz : completion row B i i = 0 := by omega
    simp [hz]
  arrows_mul_arrows_eq_zero i j := by
    have hs := completion_skew B hB i j
    rcases le_total (completion row B i j) 0 with h | h
    · have hz : (completion row B i j).toNat = 0 := by omega
      simp [hz]
    · have hz : (completion row B j i).toNat = 0 := by omega
      simp [hz]
  arrows_eq_zero_of_notMem_range i j hi hj := by simp [completion_frozen B i j hi hj]

/-- The forward arrow counts of the recovered quiver are the nonnegative parts
`(B i k).toNat` of the corresponding matrix entries. -/
@[simp]
theorem ofMatrix_arrows_col (B : Matrix I K ℤ)
    (hB : ∀ i j, B (row i) j = -B (row j) i) (i : I) (k : K) :
    (ofMatrix B hB).arrows i (row k) = (B i k).toNat := by
  exact congrArg Int.toNat (completion_col B i k)

/-- Without frozen vertices, every arrow count is the nonnegative part of the corresponding
matrix entry. -/
@[simp]
theorem ofMatrix_refl_arrows (B : Matrix K K ℤ)
    (hB : ∀ i j, B ((Function.Embedding.refl K) i) j =
      -B ((Function.Embedding.refl K) j) i) (i j : K) :
    (ofMatrix (row := Function.Embedding.refl K) B hB).arrows i j = (B i j).toNat :=
  ofMatrix_arrows_col B hB i j

/-- The backward arrow counts of the recovered quiver are the nonnegative parts
`(-B i k).toNat` of the negated matrix entries. -/
@[simp]
theorem ofMatrix_arrows_row (B : Matrix I K ℤ)
    (hB : ∀ i j, B (row i) j = -B (row j) i) (k : K) (i : I) :
    (ofMatrix B hB).arrows (row k) i = (-B i k).toNat := by
  simp only [ofMatrix]
  rw [completion_skew B hB, completion_col]

/-- The reconstructed quiver has exactly the original rectangular matrix. -/
@[simp]
theorem matrix_ofMatrix (B : Matrix I K ℤ)
    (hB : ∀ i j, B (row i) j = -B (row j) i) : (ofMatrix B hB).matrix = B := by
  ext i k
  simp only [matrix_apply, ofMatrix_arrows_col, ofMatrix_arrows_row]
  omega

/-- Recovering a quiver from its rectangular matrix gives back the quiver. -/
@[simp]
theorem ofMatrix_matrix (q : IceQuiver row) : ofMatrix q.matrix q.matrix_skew = q :=
  matrix_injective (matrix_ofMatrix q.matrix q.matrix_skew)

/-- Ice quivers correspond bijectively to raw extended integer matrices with skew-symmetric
principal block. There is no extra choice of a symmetrizer on the matrix side. -/
noncomputable def matrixEquiv : IceQuiver row ≃
    {B : Matrix I K ℤ // ∀ i j, B (row i) j = -B (row j) i} where
  toFun q := ⟨q.matrix, q.matrix_skew⟩
  invFun B := ofMatrix B B.property
  left_inv q := q.ofMatrix_matrix
  right_inv B := by
    apply Subtype.ext
    exact matrix_ofMatrix B.val B.property

@[simp]
theorem val_matrixEquiv_apply (q : IceQuiver row) : (matrixEquiv q).val = q.matrix := (rfl)

/-- The matrix equivalence sends a reconstructed quiver to the original matrix subtype. -/
@[simp]
theorem matrixEquiv_ofMatrix (B : Matrix I K ℤ)
    (hB : ∀ i j, B (row i) j = -B (row j) i) :
    matrixEquiv (ofMatrix B hB) = ⟨B, hB⟩ :=
  Subtype.ext (matrix_ofMatrix B hB)

@[simp]
theorem matrixEquiv_symm_apply
    (B : {B : Matrix I K ℤ // ∀ i j, B (row i) j = -B (row j) i}) :
    matrixEquiv.symm B = ofMatrix B B.property := (rfl)

/-! ### Relabelling -/

private def reindexFun {I' K' : Type*} {row' : K' ↪ I'} (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (q : IceQuiver row) : IceQuiver row' where
  arrows i j := q.arrows (eI.symm i) (eI.symm j)
  arrows_self i := q.arrows_self _
  arrows_mul_arrows_eq_zero i j := q.arrows_mul_arrows_eq_zero _ _
  arrows_eq_zero_of_notMem_range i j hi hj := by
    apply q.arrows_eq_zero_of_notMem_range
    · rintro ⟨k, hk⟩
      apply hi
      exact ⟨eK k, by simpa [h] using congrArg eI hk⟩
    · rintro ⟨k, hk⟩
      apply hj
      exact ⟨eK k, by simpa [h] using congrArg eI hk⟩

/-- Simultaneously relabel mutable directions and all vertices, along compatible
equivalences. Frozen vertices are then relabelled automatically. -/
def reindex {I' K' : Type*} {row' : K' ↪ I'} (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) : IceQuiver row ≃ IceQuiver row' where
  toFun := reindexFun eI eK h
  invFun := reindexFun eI.symm eK.symm (fun k ↦ by simp [Equiv.symm_apply_eq, h])
  left_inv q := by ext i j; simp [reindexFun]
  right_inv q := by ext i j; simp [reindexFun]

@[simp]
theorem reindex_arrows {I' K' : Type*} {row' : K' ↪ I'} (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (q : IceQuiver row) (i j : I') :
    (reindex eI eK h q).arrows i j = q.arrows (eI.symm i) (eI.symm j) := (rfl)

/-- Quiver matrices commute with relabelling the mutable and ambient vertices. -/
@[simp]
theorem matrix_reindex {I' K' : Type*} {row' : K' ↪ I'} (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (q : IceQuiver row) :
    (reindex eI eK h q).matrix = q.matrix.submatrix eI.symm eK.symm := by
  ext i k
  have hm : eI.symm (row' k) = row (eK.symm k) := by simp [Equiv.symm_apply_eq, h]
  simp only [matrix_apply, reindex_arrows, Matrix.submatrix_apply, hm]

/-- Canonical exchange-matrix conversion commutes with compatible relabelling. -/
@[simp]
theorem toExchangeMatrix_reindex {I' K' : Type*} {row' : K' ↪ I'}
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (q : IceQuiver row) :
    (reindex eI eK h q).toExchangeMatrix = ExchangeMatrix.reindex eI eK h q.toExchangeMatrix := by
  ext : 1
  · simp
  · ext k
    simp

/-- Reconstruction from a raw matrix commutes with compatible relabelling. -/
theorem reindex_ofMatrix {I' K' : Type*} {row' : K' ↪ I'}
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (B : Matrix I K ℤ) (hB : ∀ i j, B (row i) j = -B (row j) i) :
    reindex eI eK h (ofMatrix B hB) = ofMatrix (B.submatrix eI.symm eK.symm)
      (fun i j ↦ by
        have hm (k : K') : eI.symm (row' k) = row (eK.symm k) := by
          simp [Equiv.symm_apply_eq, h]
        simpa only [Matrix.submatrix_apply, hm] using hB (eK.symm i) (eK.symm j)) := by
  apply matrix_injective
  simp

@[simp]
theorem reindex_refl : reindex (Equiv.refl I) (Equiv.refl K) (fun _ ↦ rfl) =
    Equiv.refl (IceQuiver row) := by
  ext q i j
  rfl

/-- Successive compatible relabellings compose. -/
@[simp]
theorem reindex_trans {I' K' I'' K'' : Type*} {row' : K' ↪ I'} {row'' : K'' ↪ I''}
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (eI' : I' ≃ I'') (eK' : K' ≃ K'') (h' : ∀ k, eI' (row' k) = row'' (eK' k)) :
    (reindex eI eK h).trans (reindex eI' eK' h') =
      reindex (eI.trans eI') (eK.trans eK') (fun k ↦ by simp [h, h']) := by
  ext q i j
  simp

/-- Successive compatible relabellings of a quiver compose. -/
@[simp]
theorem reindex_reindex {I' K' I'' K'' : Type*} {row' : K' ↪ I'} {row'' : K'' ↪ I''}
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (eI' : I' ≃ I'') (eK' : K' ≃ K'') (h' : ∀ k, eI' (row' k) = row'' (eK' k))
    (q : IceQuiver row) :
    reindex eI' eK' h' (reindex eI eK h q) =
      reindex (eI.trans eI') (eK.trans eK') (fun k ↦ by simp [h, h']) q := by
  ext i j
  rfl

@[simp]
theorem reindex_symm {I' K' : Type*} {row' : K' ↪ I'} (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) :
    (reindex eI eK h).symm =
      reindex eI.symm eK.symm (fun k ↦ by simp [Equiv.symm_apply_eq, h]) := by
  ext q i j
  rfl

end IceQuiver

end TauCeti
