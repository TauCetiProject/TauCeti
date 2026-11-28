/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# Entries of Cartan matrices

Entry characterizations of the standard Cartan matrices across arbitrary rank, together with
closure and Cartan-product lemmas for `Matrix.IsGeneralizedCartan` and rational constructors for
`Matrix.IsFiniteCartan`:

* `CartanMatrix.A_apply_eq_neg_one_iff`: entries equal to `-1` in the type-`A` Cartan matrix are
  exactly consecutive pairs of indices.
* `CartanMatrix.B_apply_eq_neg_two_iff` and `CartanMatrix.B_apply_neg_iff`: the oriented double
  edge and consecutive nodes of the type-`B` Cartan matrix.
* `CartanMatrix.D_apply_eq_neg_one_iff`: entries equal to `-1` in the type-`D` Cartan matrix
  connect consecutive stem indices and connect the branch node `n - 3` to the two fork leaves
  `n - 2` and `n - 1` (vacuously none when `n ≤ 2`).
* `CartanMatrix.E_ne_of_eq_neg_one`: an entry equal to `-1` in the generalized type-`E` Cartan
  matrix has distinct row and column indices, supplying the distinctness hypothesis for
  adjacent-root Serre relations.
* `CartanMatrix.toNat_neg_G₂`: the exponents of the higher Serre relations of type `G₂` are `0`,
  `3`, `1` and `0`.
* `Matrix.IsGeneralizedCartan.submatrix`, `Matrix.IsGeneralizedCartan.fromBlocks`,
  `Matrix.IsGeneralizedCartan.fromBlocks_iff`, `Matrix.IsGeneralizedCartan.transpose`,
  `Matrix.IsGeneralizedCartan.transpose_iff`, and
  `Matrix.IsGeneralizedCartan.one_le_apply_mul_apply`: closure of generalized Cartan matrices under
  injective principal submatrices, block-diagonal sums, and transposition, plus the lower bound
  `1 ≤ A i j * A j i` for nonzero entries.
* `Matrix.IsFiniteCartan.mk_of_posDef_rat`: construct `Matrix.IsFiniteCartan` from diagonal
  entries `2`, nonpositive off-diagonal entries, and a rational symmetrizer with positive definite
  symmetrization.
-/

public section

namespace CartanMatrix

/-- Entries equal to `-1` in the type-`A` Cartan matrix are exactly consecutive pairs of
indices. -/
lemma A_apply_eq_neg_one_iff {n : ℕ} (i j : Fin n) :
    A n i j = -1 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> simp_all

/-- The unique double entry in the type-B Cartan matrix is the oriented last edge. -/
lemma B_apply_eq_neg_two_iff {n : ℕ} (i j : Fin n) :
    B n i j = -2 ↔ i.val + 2 = n ∧ j.val + 1 = n := by
  simp only [B, Matrix.of_apply]
  split_ifs <;> simp_all <;> omega

/-- Negative entries in the type-B Cartan matrix are exactly consecutive pairs of indices. -/
lemma B_apply_neg_iff {n : ℕ} (i j : Fin n) :
    B n i j < 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- Entries equal to `-1` in the type-`D` Cartan matrix connect consecutive stem indices (where the
larger index satisfies `+ 2 < n`) and connect the branch index `n - 3` to the two fork leaves
`n - 2` and `n - 1`, in every rank `n` (with no `-1` entries when `n ≤ 2`). -/
lemma D_apply_eq_neg_one_iff {n : ℕ} (i j : Fin n) :
    D n i j = -1 ↔
      (i.val + 1 = j.val ∧ j.val + 2 < n) ∨
      (j.val + 1 = i.val ∧ i.val + 2 < n) ∨
      (i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n)) ∨
      (j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n)) := by
  simp only [D, Matrix.of_apply, Fin.ext_iff]
  (split_ifs <;> simp_all) <;> omega

/-- Nodes joined by an entry `-1` in the type-`E` Cartan matrix are distinct, in every rank. -/
theorem E_ne_of_eq_neg_one {n : ℕ} {i j : Fin n} (hij : E n i j = -1) : i ≠ j := by
  rintro rfl
  exact (by decide : (2 : ℤ) ≠ -1) ((E_diag n i).symm.trans hij)

/-- The exponents `-CMᵢⱼ` of the higher Serre relations of type `G₂` are `0`, `3`, `1` and `0`. -/
theorem toNat_neg_G₂ : (-G₂ 0 0).toNat = 0 ∧ (-G₂ 0 1).toNat = 3 ∧
    (-G₂ 1 0).toNat = 1 ∧ (-G₂ 1 1).toNat = 0 := by
  decide

end CartanMatrix

namespace Matrix.IsGeneralizedCartan

variable {ι κ : Type*} {A : Matrix ι ι ℤ}

/-- A principal submatrix of a generalized Cartan matrix along an injective index map is a
generalized Cartan matrix. -/
protected theorem submatrix (h : A.IsGeneralizedCartan) {e : κ → ι}
    (he : Function.Injective e) :
    (A.submatrix e e).IsGeneralizedCartan where
  diag i := h.diag (e i)
  offDiag_nonpos i j hij := h.offDiag_nonpos (e i) (e j) (he.ne hij)
  zero_comm i j := h.zero_comm (e i) (e j)

/-- The block-diagonal matrix of two generalized Cartan matrices is a generalized Cartan
matrix. -/
protected theorem fromBlocks {B : Matrix κ κ ℤ} (hA : A.IsGeneralizedCartan)
    (hB : B.IsGeneralizedCartan) :
    (Matrix.fromBlocks A 0 0 B).IsGeneralizedCartan where
  diag := by rintro (i | i) <;> simp [hA.diag, hB.diag]
  offDiag_nonpos := by
    rintro (i | i) (j | j) hij
    · simpa using hA.offDiag_nonpos i j fun h ↦ hij (congrArg Sum.inl h)
    · simp
    · simp
    · simpa using hB.offDiag_nonpos i j fun h ↦ hij (congrArg Sum.inr h)
  zero_comm := by rintro (i | i) (j | j) <;> simp [hA.zero_comm, hB.zero_comm]

/-- A block-diagonal matrix is a generalized Cartan matrix if and only if both diagonal blocks
are generalized Cartan matrices. -/
@[simp]
protected theorem fromBlocks_iff {B : Matrix κ κ ℤ} :
    (Matrix.fromBlocks A 0 0 B).IsGeneralizedCartan ↔
      A.IsGeneralizedCartan ∧ B.IsGeneralizedCartan :=
  ⟨fun h ↦
    ⟨by
      have h1 : (Matrix.fromBlocks A 0 0 B).submatrix Sum.inl Sum.inl = A := by ext; simp
      rw [← h1]
      exact h.submatrix Sum.inl_injective,
     by
      have h2 : (Matrix.fromBlocks A 0 0 B).submatrix Sum.inr Sum.inr = B := by ext; simp
      rw [← h2]
      exact h.submatrix Sum.inr_injective⟩,
   fun ⟨hA, hB⟩ ↦ hA.fromBlocks hB⟩

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose (h : A.IsGeneralizedCartan) : Aᵀ.IsGeneralizedCartan where
  diag i := h.diag i
  offDiag_nonpos i j hij := h.offDiag_nonpos j i hij.symm
  zero_comm i j := h.zero_comm j i

@[simp]
protected theorem transpose_iff : Aᵀ.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h ↦ by simpa using h.transpose, IsGeneralizedCartan.transpose⟩

/-- **A nonzero entry has Cartan product at least `1`.** Off the diagonal both entries of such a
transposed pair are at most `-1`: they are nonpositive, and neither vanishes, because the vanishing
pattern is symmetric. On the diagonal the product is `2 * 2`. -/
theorem one_le_apply_mul_apply (h : A.IsGeneralizedCartan) {i j : ι} (hne : A i j ≠ 0) :
    1 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · rw [h.diag]; norm_num
  have hi : A i j ≤ -1 := by have := h.offDiag_nonpos i j hij; omega
  have hj : A j i ≤ -1 := by
    have hle := h.offDiag_nonpos j i hij.symm
    have hne' : A j i ≠ 0 := fun hc ↦ hne ((h.zero_comm i j).mpr hc)
    omega
  rw [← neg_mul_neg]
  exact one_le_mul_of_one_le_of_one_le (by omega) (by omega)

end Matrix.IsGeneralizedCartan

namespace Matrix.IsFiniteCartan

/-- Building a finite-type Cartan matrix from a rational symmetrizer `d` whose symmetrization
`fun i j ↦ d i * (M i j : ℚ)` is positive definite. Positive definiteness already forces
`0 < d i` on the diagonal (since `M i i = 2`) and the symmetric vanishing pattern
`M i j = 0 ↔ M j i = 0`. -/
theorem mk_of_posDef_rat {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℤ}
    (h2 : ∀ i, M i i = 2) (hle : ∀ i j, i ≠ j → M i j ≤ 0)
    {d : ι → ℚ} (hpd : (Matrix.of fun i j ↦ d i * (M i j : ℚ)).PosDef) :
    M.IsFiniteCartan := by
  have hd (i : ι) : 0 < d i := by
    have hdiag : (0 : ℚ) < (Matrix.of fun p q ↦ d p * (M p q : ℚ)) i i := hpd.diag_pos
    simp only [Matrix.of_apply, h2 i, Int.cast_ofNat] at hdiag
    linarith
  obtain ⟨⟨c, hc_pos⟩, hc'⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) d
  choose d' hd' using hc'
  have hd'_eq (i : ι) : (d' i : ℚ) = (c : ℚ) * d i := by simpa [Algebra.smul_def] using hd' i
  have hc_qpos : (0 : ℚ) < (c : ℚ) := Int.cast_pos.mpr hc_pos
  have hd'_pos (i : ι) : 0 < d' i := by
    have : (0 : ℚ) < (d' i : ℚ) := by rw [hd'_eq i]; exact mul_pos hc_qpos (hd i)
    exact_mod_cast this
  have hpdZ : (Matrix.diagonal d' * M).PosDef := by
    rw [← TauCeti.Matrix.posDef_map_intCast_iff]
    have hsmul : (Matrix.diagonal d' * M).map (Int.cast : ℤ → ℚ) =
        (c : ℚ) • Matrix.of fun i j ↦ d i * (M i j : ℚ) := by
      ext i j
      simp [Matrix.diagonal_mul, hd'_eq i, mul_assoc]
    rw [hsmul]
    exact hpd.smul hc_qpos
  exact .mk_of_exists_posDef h2 hle ⟨d', hd'_pos, hpdZ⟩

end Matrix.IsFiniteCartan

