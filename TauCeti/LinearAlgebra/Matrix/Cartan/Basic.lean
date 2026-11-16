/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Entries of Cartan matrices and generalized Cartan matrices

An entry equal to `-1` in the generalized type-`E` Cartan matrix has distinct row and
column indices. This supplies the distinctness hypothesis for adjacent-root Serre relations.
The type-`B` entry characterizations identify the oriented double edge and consecutive nodes.
The exponents of the higher Serre relations of type `G₂` are `0`, `3`, `1` and `0`
(`CartanMatrix.toNat_neg_G₂`).

This file also defines `Matrix.IsGeneralizedCartan`: an integer matrix over an arbitrary index type
with `2` on the diagonal, nonpositive off-diagonal entries, and symmetric zero pattern (`A i j = 0`
iff `A j i = 0`), requiring neither finiteness, decidable equality, invertibility, nor
symmetrizability, together with closure under transpose, principal submatrices, and reindexing, and
certificates for finite-type Cartan matrices, classical families `A`, `B`, `C`, and untwisted affine
`A₁⁽¹⁾` (`CartanMatrix.affineA₁`).

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.1.
-/

public section

open scoped Matrix

/-! ### Generalized Cartan matrices -/

/-- The proposition that an integer matrix is a **generalized Cartan matrix**: its diagonal entries
are `2`, its off-diagonal entries are nonpositive, and its zero pattern is symmetric. Neither
finiteness of the index type nor symmetrizability is required. -/
structure Matrix.IsGeneralizedCartan {I : Type*} (A : Matrix I I ℤ) : Prop where
  /-- Every diagonal entry equals `2`. -/
  diag : ∀ i, A i i = 2
  /-- Off-diagonal entries are nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  /-- Off-diagonal zeros are symmetric. -/
  zero_comm : ∀ i j, A i j = 0 ↔ A j i = 0

namespace Matrix.IsGeneralizedCartan

variable {I : Type*} {A : Matrix I I ℤ} (hA : A.IsGeneralizedCartan)
include hA

/-- Every Cartan product `A i j * A j i` of a generalized Cartan matrix is nonnegative. -/
theorem mul_nonneg (i j : I) : 0 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hA.diag]
  · exact mul_nonneg_of_nonpos_of_nonpos (hA.offDiag_nonpos i j hij)
      (hA.offDiag_nonpos j i hij.symm)

/-- The Cartan product `A i j * A j i` vanishes iff both `A i j` and `A j i` vanish. -/
theorem mul_eq_zero_iff (i j : I) : A i j * A j i = 0 ↔ A i j = 0 ∧ A j i = 0 := by
  rw [mul_eq_zero]
  exact ⟨fun h ↦ h.elim (fun h₁ ↦ ⟨h₁, (hA.zero_comm i j).mp h₁⟩)
    (fun h₂ ↦ ⟨(hA.zero_comm i j).mpr h₂, h₂⟩), fun h ↦ Or.inl h.1⟩

/-- The diagonal entries of the cast of `A` to any ring with `1` equal `2`. -/
theorem diag_map (R : Type*) [AddGroupWithOne R] (i : I) :
    A.map (Int.cast : ℤ → R) i i = 2 := by
  simp [hA.diag]

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose : Aᵀ.IsGeneralizedCartan where
  diag i := hA.diag i
  offDiag_nonpos i j hij := hA.offDiag_nonpos j i hij.symm
  zero_comm i j := hA.zero_comm j i

omit hA in
/-- The transpose of an integer matrix is a generalized Cartan matrix iff the matrix itself is. -/
@[simp]
protected theorem transpose_iff : Aᵀ.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h ↦ h.transpose, IsGeneralizedCartan.transpose⟩

/-- Any principal submatrix of a generalized Cartan matrix along an embedding is a generalized
Cartan matrix. -/
protected theorem submatrix {J : Type*} (f : J ↪ I) : (A.submatrix f f).IsGeneralizedCartan where
  diag i := hA.diag (f i)
  offDiag_nonpos i j hij := hA.offDiag_nonpos (f i) (f j) (f.injective.ne hij)
  zero_comm i j := hA.zero_comm (f i) (f j)

/-- Reindexing a generalized Cartan matrix gives a generalized Cartan matrix. -/
protected theorem reindex {J : Type*} (e : I ≃ J) : (A.reindex e e).IsGeneralizedCartan :=
  hA.submatrix e.symm.toEmbedding

end Matrix.IsGeneralizedCartan

/-- Every finite-type Cartan matrix is a generalized Cartan matrix. -/
theorem Matrix.IsFiniteCartan.isGeneralizedCartan {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : A.IsFiniteCartan) : A.IsGeneralizedCartan :=
  ⟨hA.diag, hA.offDiag_nonpos, hA.zero_comm⟩

/-! ### Entries and generalized-Cartan certificates of specific Cartan matrices -/

namespace CartanMatrix

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

/-- Nodes joined by an entry `-1` in the type-`E` Cartan matrix are distinct, in every rank. -/
theorem E_ne_of_eq_neg_one {n : ℕ} {i j : Fin n} (hij : E n i j = -1) : i ≠ j := by
  rintro rfl
  exact (by decide : (2 : ℤ) ≠ -1) ((E_diag n i).symm.trans hij)

/-- The exponents `-CMᵢⱼ` of the higher Serre relations of type `G₂` are `0`, `3`, `1` and `0`. -/
theorem toNat_neg_G₂ : (-G₂ 0 0).toNat = 0 ∧ (-G₂ 0 1).toNat = 3 ∧
    (-G₂ 1 0).toNat = 1 ∧ (-G₂ 1 1).toNat = 0 := by
  decide

/-- Every classical type-`A` Cartan matrix `CartanMatrix.A n` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_A (n : ℕ) : (CartanMatrix.A n).IsGeneralizedCartan where
  diag i := by simpa using congrFun (A_diag n) i
  offDiag_nonpos := A_apply_le_zero_of_ne n
  zero_comm i j := by
    have h : CartanMatrix.A n j i = CartanMatrix.A n i j := by
      simpa [Matrix.transpose_apply] using congrArg (fun M ↦ M i j) (A_transpose n)
    rw [h]

/-- Every classical type-`B` Cartan matrix `CartanMatrix.B n` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_B (n : ℕ) : (CartanMatrix.B n).IsGeneralizedCartan where
  diag := B_diag n
  offDiag_nonpos := B_off_diag_nonpos n
  zero_comm i j := by
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> simp_all

/-- Every classical type-`C` Cartan matrix `CartanMatrix.C n` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_C (n : ℕ) : (CartanMatrix.C n).IsGeneralizedCartan := by
  rw [← B_transpose]
  exact (isGeneralizedCartan_B n).transpose

/-- The `2 × 2` generalized Cartan matrix `!![2, -2; -2, 2]` of untwisted affine type `A₁⁽¹⁾`. -/
abbrev affineA₁ : Matrix (Fin 2) (Fin 2) ℤ := !![2, -2; -2, 2]

/-- `CartanMatrix.affineA₁` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_affineA₁ : affineA₁.IsGeneralizedCartan where
  diag := by simp [Fin.forall_fin_two, affineA₁]
  offDiag_nonpos := by simp [Fin.forall_fin_two, affineA₁]
  zero_comm := by simp [Fin.forall_fin_two, affineA₁]

end CartanMatrix
