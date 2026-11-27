/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.MulChar.Basic
import TauCeti.LinearAlgebra.Matrix.ColumnRowPartitioned
import TauCeti.LinearAlgebra.Matrix.Determinant.ComplementaryMinor
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Completion
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
import TauCeti.NumberTheory.MulChar.Basic

/-!
# Matched functions on rectangular matrices

Let `R` be a commutative ring, `χ` a multiplicative character of `R` with values in a commutative
monoid with zero `Λ`, and `σ : b ⊕ a ≃ n` a splitting of a finite index type. An invertible
`n × n` matrix `k` has two shadows: the `n × b` matrix `y_k` of its columns indexed by `b`, and
the `a × n` matrix `x_k` of the rows of `k⁻¹` indexed by `a`. Functions `Φ` of `a × n` matrices
and `Ψ` of `n × b` matrices are *matched* for `χ` along `σ`, `MulChar.AreMatched`, if `Φ` vanishes
off the `x_k`, `Ψ` vanishes off the `y_k`, and `Φ x_k = χ (det k) * Ψ y_k` for every invertible
`k`.

Matched pairs are the finite data, at the ramified places of a tame character, on the two sides of
the exchange identity between theta integrals of complementary hermitian spaces and of the
commuting squares of theta lifts built from it. This file develops the linear algebra of matching.

* A matched partner is unique on either side, and matching is stable under translation by
  `GL_n(R)`.
* The second function of a matched pair transforms by `χ⁻¹ ∘ det` under `GL_b(R)` acting on the
  right, and conversely every function that vanishes off the `y_k` and has this transformation law
  has a matched partner. Without the transformation law a partner need not exist: over `𝔽₃` with
  `n = 2`, `a = b = 1` and `χ = 1`, the indicator of the column `(1, 0)` has none, because the
  matrices `1` and `diag(2, 1)` have the same `x_k` and the columns `(1, 0)` and `(2, 0)` as `y_k`.
* Given a function `f` of `a × b` matrices, the block functions
  `Φ (x₁ x₂) = χ⁻¹ (det x₂) * f (x₂⁻¹ x₁)` and `Ψ (y₁; y₂) = χ⁻¹ (det y₁) * f (-y₂ y₁⁻¹)` are
  matched. Here `x₂` is the square block of the columns `a` of `x` and `x₁` the block of its columns
  `b`, `y₁` is the square block of the rows `b` of `y` and `y₂` the block of its rows `a`; both
  functions vanish where the square block is singular. When `R` is finite and `Λ` a commutative
  semiring, paired with functions `L`, `L'` that transform by `χ ∘ det` under `GL_a(R)` on the
  left, respectively `GL_b(R)` on the right, they give
  `∑ x, Φ x * L x = #GL_a(R) * ∑ z, f z * L (z 1)` and
  `∑ y, Ψ y * L' y = #GL_b(R) * ∑ z, f z * L' (1; -z)`, where `(z 1)` has the block `z` on the
  columns `b` and the identity on the columns `a`, and `(1; -z)` has the identity on the rows `b`
  and the block `-z` on the rows `a`.

## Main definitions

* `MulChar.AreMatched χ σ Φ Ψ`: `Φ` and `Ψ` are matched for `χ` along `σ`.
* `MulChar.rowBlockFun χ σ f` and `MulChar.colBlockFun χ σ f`: the block functions of `f`.

## Main results

* `MulChar.AreMatched.left_unique`, `MulChar.AreMatched.right_unique`: matched partners are
  unique.
* `MulChar.AreMatched.translate`: if `(Φ, Ψ)` are matched and `g ∈ GL_n(R)`, so are
  `x ↦ χ (det g) * Φ (x g)` and `y ↦ Ψ (g⁻¹ y)`.
* `MulChar.exists_areMatched_iff`: `Ψ` has a matched partner if and only if it vanishes off the
  `y_k` and `χ (det h) * Ψ (y h) = Ψ y` for all `h ∈ GL_b(R)`.
* `MulChar.areMatched_rowBlockFun_colBlockFun`: the block functions of `f` are matched.
* `MulChar.sum_rowBlockFun_mul`, `MulChar.sum_colBlockFun_mul`: the pairings of the block
  functions with equivariant functions.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, files
  `src/New/Determinant/Exchange/MatchingPartners.lean` (declaration `New.Rows.areMatched_block`)
  and `src/New/Determinant/Chain/SquareLaw.lean` (declarations `New.areMatched_matchOf`,
  `New.AreMatched.unique`, `New.AreMatched.translate`); Apache 2.0, Copyright 2026 Anthropic, PBC.
  The statements follow the route of these declarations; the proofs here are written from it.
-/

public section

open Matrix

namespace MulChar

variable {R Λ a b n : Type*} [CommRing R]

section Matched

variable [CommMonoidWithZero Λ] [Fintype n] [DecidableEq n]

/-- Functions `Φ` of `a × n` matrices and `Ψ` of `n × b` matrices over `R` are *matched* for the
character `χ` along the splitting `σ : b ⊕ a ≃ n` if, writing `x_k` for the `a × n` matrix of the
rows of `k⁻¹` indexed by `a` and `y_k` for the `n × b` matrix of the columns of `k` indexed by `b`,
`Φ` vanishes off the `x_k`, `Ψ` vanishes off the `y_k`, and `Φ x_k = χ (det k) * Ψ y_k` for every
`k ∈ GL_n(R)`. -/
structure AreMatched (χ : MulChar R Λ) (σ : b ⊕ a ≃ n) (Φ : Matrix a n R → Λ)
    (Ψ : Matrix n b R → Λ) : Prop where
  /-- `Φ` vanishes off the rows indexed by `a` of the inverses of invertible matrices. -/
  support_left_subset : Function.support Φ ⊆
    Set.range fun k : GL n R ↦ ((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id
  /-- `Ψ` vanishes off the columns indexed by `b` of invertible matrices. -/
  support_right_subset : Function.support Ψ ⊆
    Set.range fun k : GL n R ↦ (k : Matrix n n R).submatrix id (σ ∘ Sum.inl)
  /-- The values of `Φ` and `Ψ` at the two shadows of an invertible matrix `k` differ by the
  factor `χ (det k)`. -/
  apply_eq (k : GL n R) : Φ (((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id) =
    χ (k : Matrix n n R).det * Ψ ((k : Matrix n n R).submatrix id (σ ∘ Sum.inl))

variable {χ : MulChar R Λ} {σ : b ⊕ a ≃ n} {Φ Φ' : Matrix a n R → Λ} {Ψ Ψ' : Matrix n b R → Λ}

/-- The value of a character at the determinant of an invertible matrix is a unit. -/
private theorem isUnit_apply_det (χ : MulChar R Λ) (k : GL n R) :
    IsUnit (χ (k : Matrix n n R).det) :=
  .of_mul_eq_one _ (apply_mul_inv_apply_of_isUnit χ (isUnits_det_units k))

namespace AreMatched

/-- The first function of a matched pair vanishes off the shadows `x_k`. -/
theorem eq_zero_left (h : χ.AreMatched σ Φ Ψ) {x : Matrix a n R}
    (hx : ∀ k : GL n R, ((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id ≠ x) :
    Φ x = 0 :=
  Function.notMem_support.mp fun hΦ ↦ by
    obtain ⟨k, hk⟩ := h.support_left_subset hΦ
    exact hx k hk

/-- The second function of a matched pair vanishes off the shadows `y_k`. -/
theorem eq_zero_right (h : χ.AreMatched σ Φ Ψ) {y : Matrix n b R}
    (hy : ∀ k : GL n R, (k : Matrix n n R).submatrix id (σ ∘ Sum.inl) ≠ y) : Ψ y = 0 :=
  Function.notMem_support.mp fun hΨ ↦ by
    obtain ⟨k, hk⟩ := h.support_right_subset hΨ
    exact hy k hk

/-- The second function of a matched pair determines the first. -/
theorem left_unique (h : χ.AreMatched σ Φ Ψ) (h' : χ.AreMatched σ Φ' Ψ) : Φ = Φ' := by
  funext x
  by_cases hx : ∃ k : GL n R, ((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id = x
  · obtain ⟨k, rfl⟩ := hx
    rw [h.apply_eq, h'.apply_eq]
  · push Not at hx
    rw [h.eq_zero_left hx, h'.eq_zero_left hx]

/-- The first function of a matched pair determines the second. -/
theorem right_unique (h : χ.AreMatched σ Φ Ψ) (h' : χ.AreMatched σ Φ Ψ') : Ψ = Ψ' := by
  funext y
  by_cases hy : ∃ k : GL n R, (k : Matrix n n R).submatrix id (σ ∘ Sum.inl) = y
  · obtain ⟨k, rfl⟩ := hy
    exact (isUnit_apply_det χ k).mul_left_cancel ((h.apply_eq k).symm.trans (h'.apply_eq k))
  · push Not at hy
    rw [h.eq_zero_right hy, h'.eq_zero_right hy]

/-- Matching is stable under translation by `GL_n(R)`: if `(Φ, Ψ)` are matched and `g` is
invertible, so are `x ↦ χ (det g) * Φ (x g)` and `y ↦ Ψ (g⁻¹ y)`. -/
theorem translate (h : χ.AreMatched σ Φ Ψ) (g : GL n R) :
    χ.AreMatched σ (fun x ↦ χ (g : Matrix n n R).det * Φ (x * (g : Matrix n n R)))
      (fun y ↦ Ψ (((g⁻¹ : GL n R) : Matrix n n R) * y)) where
  support_left_subset x hx := by
    obtain ⟨k, hk⟩ := h.support_left_subset (right_ne_zero_of_mul hx)
    refine ⟨g * k, ?_⟩
    simp only [_root_.mul_inv_rev, Units.val_mul] at hk ⊢
    rw [submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id, hk, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  support_right_subset y hy := by
    obtain ⟨k, hk⟩ := h.support_right_subset hy
    refine ⟨g * k, ?_⟩
    simp only [Units.val_mul] at hk ⊢
    rw [submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id, hk, ← Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  apply_eq k := by
    have hk := h.apply_eq (g⁻¹ * k)
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul] at hk
    rw [submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id,
      submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id] at hk
    rw [hk, ← mul_assoc, ← map_mul, ← det_mul, ← Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]

end AreMatched

/-! ### Matrices whose rows indexed by `a` are those of the identity -/

section Stabilizer

variable [Fintype b] [DecidableEq b]

omit [Fintype b] [DecidableEq b] in
/-- The indices `a` of a splitting `σ : b ⊕ a ≃ n` of a finite type form a finite type. -/
private noncomputable abbrev fintypeOfSplitting (σ : b ⊕ a ≃ n) : Fintype a :=
  Fintype.ofInjective (σ ∘ Sum.inr) (σ.injective.comp Sum.inr_injective)

/-- If the rows indexed by `a` of `m ∈ GL_n(R)` are those of the identity matrix, then `k` and
`k m` have the same shadow `x`, the shadow `y` of `k m` is that of `k` times the square block of `m`
on the indices `b`, and this block has the determinant of `m`. -/
private theorem shadows_mul_of_rows_eq_one (m : GL n R)
    (hm : ∀ i j, (m : Matrix n n R) (σ (.inr i)) j = (1 : Matrix n n R) (σ (.inr i)) j)
    (k : GL n R) :
    (((k * m)⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id =
        ((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id ∧
      ((k * m : GL n R) : Matrix n n R).submatrix id (σ ∘ Sum.inl) =
        (k : Matrix n n R).submatrix id (σ ∘ Sum.inl) *
          (m : Matrix n n R).submatrix (σ ∘ Sum.inl) (σ ∘ Sum.inl) ∧
      (m : Matrix n n R).det = ((m : Matrix n n R).submatrix (σ ∘ Sum.inl) (σ ∘ Sum.inl)).det := by
  classical
  let _ := fintypeOfSplitting σ
  -- The rows indexed by `a` of `m⁻¹` are those of the identity as well.
  have hinv (i : a) (j : n) :
      (m : Matrix n n R)⁻¹ (σ (.inr i)) j = (1 : Matrix n n R) (σ (.inr i)) j := by
    have h1 : ((m : Matrix n n R) * (m : Matrix n n R)⁻¹) (σ (.inr i)) j =
        (1 : Matrix n n R) (σ (.inr i)) j := by
      rw [mul_nonsing_inv _ (isUnits_det_units m)]
    rw [Matrix.mul_apply] at h1
    simpa [hm, Matrix.one_apply] using h1
  refine ⟨?_, ?_, ?_⟩
  · rw [_root_.mul_inv_rev, GeneralLinearGroup.coe_mul, coe_units_inv, coe_units_inv]
    ext i j
    simp [Matrix.mul_apply, hinv, Matrix.one_apply]
  · rw [GeneralLinearGroup.coe_mul]
    ext i j
    simp [Matrix.mul_apply, ← σ.sum_comp, Fintype.sum_sum_type, hm]
  · have hblocks : (m : Matrix n n R).submatrix σ σ =
        fromBlocks ((m : Matrix n n R).submatrix (σ ∘ Sum.inl) (σ ∘ Sum.inl))
          ((m : Matrix n n R).submatrix (σ ∘ Sum.inl) (σ ∘ Sum.inr)) 0 1 := by
      ext (i | i) (j | j) <;> simp [hm, Matrix.one_apply, σ.injective.eq_iff]
    rw [← det_submatrix_equiv_self σ, hblocks, det_fromBlocks_zero₂₁, det_one, mul_one]

/-- The reindex along `σ` of the block diagonal matrix `h ⊕ 1` is the identity on the rows indexed
by `a`. -/
private theorem reindexGL_fromBlocksGL_one_apply_inr [Fintype a] [DecidableEq a] (h : GL b R)
    (i : a) (j : n) :
    (σ.reindexGL R (TauCeti.fromBlocksGL (h, 1)) : Matrix n n R) (σ (.inr i)) j =
      (1 : Matrix n n R) (σ (.inr i)) j := by
  obtain ⟨j, rfl⟩ := σ.surjective j
  rcases j with j | j <;> simp [Matrix.one_apply]

/-- The reindex along `σ` of the block diagonal matrix `h ⊕ 1` is `h` on the indices `b`. -/
private theorem submatrix_reindexGL_fromBlocksGL_one [Fintype a] [DecidableEq a] (h : GL b R) :
    (σ.reindexGL R (TauCeti.fromBlocksGL (h, 1)) : Matrix n n R).submatrix (σ ∘ Sum.inl)
      (σ ∘ Sum.inl) = h := by
  ext i j
  simp

/-- The second function of a matched pair transforms by `χ⁻¹ ∘ det` under `GL_b(R)` acting on the
right: `χ (det h) * Ψ (y h) = Ψ y`. -/
theorem AreMatched.mul_apply_mul (hm : χ.AreMatched σ Φ Ψ) (h : GL b R) (y : Matrix n b R) :
    χ (h : Matrix b b R).det * Ψ (y * (h : Matrix b b R)) = Ψ y := by
  classical
  let _ := fintypeOfSplitting σ
  by_cases hy : ∃ k : GL n R, (k : Matrix n n R).submatrix id (σ ∘ Sum.inl) = y
  · obtain ⟨k, rfl⟩ := hy
    obtain ⟨hx, hyk, hdet⟩ := shadows_mul_of_rows_eq_one
      (σ.reindexGL R (TauCeti.fromBlocksGL (h, 1))) (reindexGL_fromBlocksGL_one_apply_inr h) k
    rw [submatrix_reindexGL_fromBlocksGL_one] at hyk hdet
    have e := hm.apply_eq (k * σ.reindexGL R (TauCeti.fromBlocksGL (h, 1)))
    rw [hx, hyk, GeneralLinearGroup.coe_mul, det_mul, hdet, hm.apply_eq k, map_mul,
      mul_assoc] at e
    exact ((isUnit_apply_det χ k).mul_left_cancel e).symm
  · push Not at hy
    have hy' (k : GL n R) :
        (k : Matrix n n R).submatrix id (σ ∘ Sum.inl) ≠ y * (h : Matrix b b R) := by
      intro hk
      obtain ⟨-, hyk, -⟩ := shadows_mul_of_rows_eq_one
        (σ.reindexGL R (TauCeti.fromBlocksGL (h⁻¹, 1)))
        (reindexGL_fromBlocksGL_one_apply_inr h⁻¹) k
      rw [submatrix_reindexGL_fromBlocksGL_one, hk, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one] at hyk
      exact hy _ hyk
    rw [hm.eq_zero_right hy, hm.eq_zero_right hy', mul_zero]

/-- If two invertible matrices have the same shadow `x`, their shadows `y` differ by an invertible
matrix `h` on the right, and their determinants by `det h`. -/
private theorem exists_submatrix_eq_mul_of_submatrix_inv_eq {k k' : GL n R}
    (hkk' : ((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id =
      ((k'⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id) :
    ∃ h : GL b R, (k' : Matrix n n R).submatrix id (σ ∘ Sum.inl) =
        (k : Matrix n n R).submatrix id (σ ∘ Sum.inl) * (h : Matrix b b R) ∧
      (k' : Matrix n n R).det = (k : Matrix n n R).det * (h : Matrix b b R).det := by
  have hm (i : a) (j : n) : ((k⁻¹ * k' : GL n R) : Matrix n n R) (σ (.inr i)) j =
      (1 : Matrix n n R) (σ (.inr i)) j := by
    have hrow (l : n) : ((k⁻¹ : GL n R) : Matrix n n R) (σ (.inr i)) l =
        ((k'⁻¹ : GL n R) : Matrix n n R) (σ (.inr i)) l := by
      simpa using congrArg (fun M : Matrix a n R ↦ M i l) hkk'
    rw [GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    simp_rw [hrow]
    rw [← Matrix.mul_apply, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
      GeneralLinearGroup.coe_one]
  obtain ⟨-, hyk, hdet⟩ := shadows_mul_of_rows_eq_one _ hm k
  rw [mul_inv_cancel_left] at hyk
  refine ⟨GeneralLinearGroup.mk''
    (((k⁻¹ * k' : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inl) (σ ∘ Sum.inl))
    (hdet ▸ isUnits_det_units _), hyk, ?_⟩
  rw [GeneralLinearGroup.val_mk'', ← hdet, ← det_mul, ← GeneralLinearGroup.coe_mul,
    mul_inv_cancel_left]

/-- **Existence of matched partners.** A function `Ψ` of `n × b` matrices has a matched partner if
and only if it vanishes off the `n × b` matrices of columns indexed by `b` of invertible matrices
and transforms by `χ⁻¹ ∘ det` under `GL_b(R)` acting on the right. -/
theorem exists_areMatched_iff (χ : MulChar R Λ) :
    (∃ Φ, χ.AreMatched σ Φ Ψ) ↔
      Function.support Ψ ⊆
          Set.range (fun k : GL n R ↦ (k : Matrix n n R).submatrix id (σ ∘ Sum.inl)) ∧
        ∀ (h : GL b R) (y : Matrix n b R),
          χ (h : Matrix b b R).det * Ψ (y * (h : Matrix b b R)) = Ψ y := by
  refine ⟨fun ⟨Φ, hm⟩ ↦ ⟨hm.support_right_subset, hm.mul_apply_mul⟩, fun ⟨hsupp, hΨ⟩ ↦ ?_⟩
  classical
  -- The value `χ (det k) * Ψ y_k` depends on `k` only through `x_k`.
  have hwd {k k' : GL n R}
      (hkk' : ((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id =
        ((k'⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id) :
      χ (k' : Matrix n n R).det * Ψ ((k' : Matrix n n R).submatrix id (σ ∘ Sum.inl)) =
        χ (k : Matrix n n R).det * Ψ ((k : Matrix n n R).submatrix id (σ ∘ Sum.inl)) := by
    obtain ⟨h, hy, hdet⟩ := exists_submatrix_eq_mul_of_submatrix_inv_eq hkk'
    rw [hy, hdet, map_mul, mul_assoc, hΨ]
  refine ⟨fun x ↦ if hx : ∃ k : GL n R,
      ((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id = x then
    χ (hx.choose : Matrix n n R).det * Ψ ((hx.choose : Matrix n n R).submatrix id (σ ∘ Sum.inl))
    else 0, fun x hx ↦ ?_, hsupp, fun k ↦ ?_⟩
  · by_contra hne
    have hne' : ¬∃ k : GL n R, ((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id = x :=
      hne
    exact hx (by simp only [hne', ↓reduceDIte])
  · have hx : ∃ k' : GL n R, ((k'⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id =
        ((k⁻¹ : GL n R) : Matrix n n R).submatrix (σ ∘ Sum.inr) id := ⟨k, rfl⟩
    simp only [hx, ↓reduceDIte]
    exact hwd hx.choose_spec.symm

end Stabilizer

end Matched

/-! ### Block functions -/

section BlockFun

variable [CommMonoidWithZero Λ]

/-- The row block function of a function `f` of `a × b` matrices: at an `a × n` matrix `x`, with
square block `x₂` of the columns indexed by `a` and block `x₁` of the columns indexed by `b`, it is
`χ⁻¹ (det x₂) * f (x₂⁻¹ * x₁)`. It vanishes where `x₂` is singular. -/
noncomputable def rowBlockFun [Fintype a] [DecidableEq a] (χ : MulChar R Λ) (σ : b ⊕ a ≃ n)
    (f : Matrix a b R → Λ) (x : Matrix a n R) : Λ :=
  χ⁻¹ (x.submatrix id (σ ∘ Sum.inr)).det *
    f ((x.submatrix id (σ ∘ Sum.inr))⁻¹ * x.submatrix id (σ ∘ Sum.inl))

/-- The column block function of a function `f` of `a × b` matrices: at an `n × b` matrix `y`,
with square block `y₁` of the rows indexed by `b` and block `y₂` of the rows indexed by `a`, it is
`χ⁻¹ (det y₁) * f (-(y₂ * y₁⁻¹))`. It vanishes where `y₁` is singular. -/
noncomputable def colBlockFun [Fintype b] [DecidableEq b] (χ : MulChar R Λ) (σ : b ⊕ a ≃ n)
    (f : Matrix a b R → Λ) (y : Matrix n b R) : Λ :=
  χ⁻¹ (y.submatrix (σ ∘ Sum.inl) id).det *
    f (-(y.submatrix (σ ∘ Sum.inr) id * (y.submatrix (σ ∘ Sum.inl) id)⁻¹))

variable (χ : MulChar R Λ) {σ : b ⊕ a ≃ n} (f : Matrix a b R → Λ)

/-- The row block function vanishes where the square block of the columns `a` is singular. -/
theorem rowBlockFun_eq_zero [Fintype a] [DecidableEq a] {x : Matrix a n R}
    (hx : ¬IsUnit (x.submatrix id (σ ∘ Sum.inr)).det) :
    χ.rowBlockFun σ f x = 0 := by
  rw [rowBlockFun, χ⁻¹.map_nonunit hx, zero_mul]

/-- The column block function vanishes where the square block of the rows `b` is singular. -/
theorem colBlockFun_eq_zero [Fintype b] [DecidableEq b] {y : Matrix n b R}
    (hy : ¬IsUnit (y.submatrix (σ ∘ Sum.inl) id).det) :
    χ.colBlockFun σ f y = 0 := by
  rw [colBlockFun, χ⁻¹.map_nonunit hy, zero_mul]

/-- The row block function at `h * (z 1)`, the matrix with blocks `h z` on the columns `b` and `h`
on the columns `a`, is `χ⁻¹ (det h) * f z`. -/
@[simp]
theorem rowBlockFun_mul_fromCols [Fintype a] [DecidableEq a] (h : GL a R) (z : Matrix a b R) :
    χ.rowBlockFun σ f ((h : Matrix a a R) * (fromCols z 1).submatrix id σ.symm) =
      χ⁻¹ (h : Matrix a a R).det * f z := by
  rw [rowBlockFun, submatrix_mul_fromCols_submatrix_comp_inl,
    submatrix_mul_fromCols_submatrix_comp_inr, Matrix.mul_one,
    nonsing_inv_mul_cancel_left _ _ (isUnits_det_units h)]

/-- The column block function at `(1; -z) * h`, the matrix with blocks `h` on the rows `b` and
`-z h` on the rows `a`, is `χ⁻¹ (det h) * f z`. -/
@[simp]
theorem colBlockFun_fromRows_mul [Fintype b] [DecidableEq b] (h : GL b R) (z : Matrix a b R) :
    χ.colBlockFun σ f ((fromRows 1 (-z)).submatrix σ.symm id * (h : Matrix b b R)) =
      χ⁻¹ (h : Matrix b b R).det * f z := by
  rw [colBlockFun, submatrix_fromRows_submatrix_mul_comp_inl,
    submatrix_fromRows_submatrix_mul_comp_inr, Matrix.one_mul,
    mul_nonsing_inv_cancel_right _ _ (isUnits_det_units h), neg_neg]

/-- **Block functions are matched.** For every function `f` of `a × b` matrices, the row block
function `x ↦ χ⁻¹ (det x₂) * f (x₂⁻¹ x₁)` and the column block function
`y ↦ χ⁻¹ (det y₁) * f (-y₂ y₁⁻¹)` are matched for `χ` along `σ`. -/
theorem areMatched_rowBlockFun_colBlockFun [Fintype a] [Fintype b] [Fintype n] [DecidableEq a]
    [DecidableEq b] [DecidableEq n] (σ : b ⊕ a ≃ n) :
    χ.AreMatched σ (χ.rowBlockFun σ f) (χ.colBlockFun σ f) where
  support_left_subset x hx := by
    obtain ⟨k, hk⟩ := GeneralLinearGroup.exists_submatrix_comp_inr_id_eq_of_isUnit_det σ
      (by_contra fun hu ↦ hx (rowBlockFun_eq_zero χ f hu))
    exact ⟨k⁻¹, by simpa only [inv_inv] using hk⟩
  support_right_subset y hy :=
    GeneralLinearGroup.exists_submatrix_id_comp_inl_eq_of_isUnit_det σ
      (by_contra fun hu ↦ hy (colBlockFun_eq_zero χ f hu))
  apply_eq k := by
    set K : Matrix n n R := (k : Matrix n n R)
    have hK : IsUnit K.det := isUnits_det_units k
    have hjac := det_submatrix_comp_inl_eq_det_mul_det_submatrix_comp_inr_nonsing_inv K hK σ
    simp only [rowBlockFun, colBlockFun, coe_units_inv, submatrix_submatrix, Function.comp_id,
      Function.id_comp]
    by_cases hu : IsUnit (K⁻¹.submatrix (σ ∘ Sum.inr) (σ ∘ Sum.inr)).det
    · rw [inv_submatrix_nonsing_inv_mul_eq_neg_submatrix_mul_inv K hK σ, hjac, map_mul,
        ← mul_assoc, ← mul_assoc, apply_mul_inv_apply_of_isUnit χ hK, one_mul]
    · have hu' : ¬IsUnit (K.submatrix (σ ∘ Sum.inl) (σ ∘ Sum.inl)).det := by
        rw [hjac, IsUnit.mul_iff]
        exact fun h ↦ hu h.2
      rw [χ⁻¹.map_nonunit hu, χ⁻¹.map_nonunit hu', zero_mul, zero_mul, mul_zero]

end BlockFun

section Sum

variable [CommSemiring Λ] (χ : MulChar R Λ) {σ : b ⊕ a ≃ n} (f : Matrix a b R → Λ)

/-- Pairing the row block function of `f` with a function `L` of `a × n` matrices that transforms
by `χ ∘ det` under `GL_a(R)` acting on the left reduces to a sum over `f`: the sum of
`rowBlockFun f x * L x` over all `x` is `#GL_a(R)` times the sum of `f z * L (z 1)` over all `z`,
where `(z 1)` has the block `z` on the columns `b` and the identity on the columns `a`. -/
theorem sum_rowBlockFun_mul [Fintype R] [Fintype a] [Fintype b] [Fintype n] [DecidableEq a]
    [DecidableEq b] [DecidableEq n] {L : Matrix a n R → Λ}
    (hL : ∀ (h : GL a R) (x : Matrix a n R), L ((h : Matrix a a R) * x) =
      χ (h : Matrix a a R).det * L x) :
    ∑ x, χ.rowBlockFun σ f x * L x =
      Nat.card (GL a R) * ∑ z, f z * L ((fromCols z 1).submatrix id σ.symm) := by
  classical
  calc ∑ x, χ.rowBlockFun σ f x * L x
      = ∑ x with IsUnit (x.submatrix id (σ ∘ Sum.inr)).det, χ.rowBlockFun σ f x * L x := by
        refine (Finset.sum_filter_of_ne fun x _ hx ↦ ?_).symm
        by_contra hu
        exact hx (by rw [rowBlockFun_eq_zero χ f hu, zero_mul])
    _ = ∑ p : GL a R × Matrix a b R, f p.2 * L ((fromCols p.2 1).submatrix id σ.symm) := by
        refine (Finset.sum_bij (fun p _ ↦ (p.1 : Matrix a a R) *
          (fromCols p.2 1).submatrix id σ.symm) (fun p _ ↦ ?_) (fun p _ p' _ hpp' ↦ ?_)
          (fun x hx ↦ ?_) (fun p _ ↦ ?_)).symm
        · simp
        · have h₁ := congrArg (fun x : Matrix a n R ↦ x.submatrix id (σ ∘ Sum.inr)) hpp'
          have h₂ := congrArg (fun x : Matrix a n R ↦ x.submatrix id (σ ∘ Sum.inl)) hpp'
          simp only [submatrix_mul_fromCols_submatrix_comp_inr,
            submatrix_mul_fromCols_submatrix_comp_inl, Matrix.mul_one] at h₁ h₂
          rw [h₁] at h₂
          refine Prod.ext (Units.ext h₁) ?_
          simpa [nonsing_inv_mul_cancel_left _ _ (isUnits_det_units p'.1)] using
            congrArg ((p'.1 : Matrix a a R)⁻¹ * ·) h₂
        · have hu : IsUnit (x.submatrix id (σ ∘ Sum.inr)).det := (Finset.mem_filter.mp hx).2
          refine ⟨(GeneralLinearGroup.mk'' _ hu,
            (x.submatrix id (σ ∘ Sum.inr))⁻¹ * x.submatrix id (σ ∘ Sum.inl)), Finset.mem_univ _, ?_⟩
          refine ext_of_submatrix_id_comp_inl_inr σ ?_ ?_
          · rw [submatrix_mul_fromCols_submatrix_comp_inl, GeneralLinearGroup.val_mk'',
              mul_nonsing_inv_cancel_left _ _ hu]
          · rw [submatrix_mul_fromCols_submatrix_comp_inr, GeneralLinearGroup.val_mk'',
              Matrix.mul_one]
        · rw [rowBlockFun_mul_fromCols, hL, mul_mul_mul_comm, mul_comm (χ⁻¹ _),
            apply_mul_inv_apply_of_isUnit χ (isUnits_det_units p.1), one_mul]
    _ = _ := by
        simp [Fintype.sum_prod_type, Nat.card_eq_fintype_card]

/-- Pairing the column block function of `f` with a function `L'` of `n × b` matrices that
transforms by `χ ∘ det` under `GL_b(R)` acting on the right reduces to a sum over `f`: the sum of
`colBlockFun f y * L' y` over all `y` is `#GL_b(R)` times the sum of `f z * L' (1; -z)` over all
`z`, where `(1; -z)` has the identity on the rows `b` and the block `-z` on the rows `a`. -/
theorem sum_colBlockFun_mul [Fintype R] [Fintype a] [Fintype b] [Fintype n] [DecidableEq a]
    [DecidableEq b] [DecidableEq n] {L' : Matrix n b R → Λ}
    (hL' : ∀ (h : GL b R) (y : Matrix n b R), L' (y * (h : Matrix b b R)) =
      χ (h : Matrix b b R).det * L' y) :
    ∑ y, χ.colBlockFun σ f y * L' y =
      Nat.card (GL b R) * ∑ z, f z * L' ((fromRows 1 (-z)).submatrix σ.symm id) := by
  classical
  calc ∑ y, χ.colBlockFun σ f y * L' y
      = ∑ y with IsUnit (y.submatrix (σ ∘ Sum.inl) id).det, χ.colBlockFun σ f y * L' y := by
        refine (Finset.sum_filter_of_ne fun y _ hy ↦ ?_).symm
        by_contra hu
        exact hy (by rw [colBlockFun_eq_zero χ f hu, zero_mul])
    _ = ∑ p : GL b R × Matrix a b R, f p.2 * L' ((fromRows 1 (-p.2)).submatrix σ.symm id) := by
        refine (Finset.sum_bij (fun p _ ↦ (fromRows 1 (-p.2)).submatrix σ.symm id *
          (p.1 : Matrix b b R)) (fun p _ ↦ ?_) (fun p _ p' _ hpp' ↦ ?_)
          (fun y hy ↦ ?_) (fun p _ ↦ ?_)).symm
        · simp
        · have h₁ := congrArg (fun y : Matrix n b R ↦ y.submatrix (σ ∘ Sum.inl) id) hpp'
          have h₂ := congrArg (fun y : Matrix n b R ↦ y.submatrix (σ ∘ Sum.inr) id) hpp'
          simp only [submatrix_fromRows_submatrix_mul_comp_inl,
            submatrix_fromRows_submatrix_mul_comp_inr, Matrix.one_mul] at h₁ h₂
          rw [h₁, Matrix.neg_mul, Matrix.neg_mul, neg_inj] at h₂
          refine Prod.ext (Units.ext h₁) ?_
          simpa [mul_nonsing_inv_cancel_right _ _ (isUnits_det_units p'.1)] using
            congrArg (· * (p'.1 : Matrix b b R)⁻¹) h₂
        · have hu : IsUnit (y.submatrix (σ ∘ Sum.inl) id).det := (Finset.mem_filter.mp hy).2
          refine ⟨(GeneralLinearGroup.mk'' _ hu,
            -(y.submatrix (σ ∘ Sum.inr) id * (y.submatrix (σ ∘ Sum.inl) id)⁻¹)), Finset.mem_univ _,
            ?_⟩
          refine ext_of_submatrix_comp_inl_inr_id σ ?_ ?_
          · rw [submatrix_fromRows_submatrix_mul_comp_inl, GeneralLinearGroup.val_mk'',
              Matrix.one_mul]
          · rw [submatrix_fromRows_submatrix_mul_comp_inr, GeneralLinearGroup.val_mk'', neg_neg,
              nonsing_inv_mul_cancel_right _ _ hu]
        · rw [colBlockFun_fromRows_mul, hL', mul_mul_mul_comm, mul_comm (χ⁻¹ _),
            apply_mul_inv_apply_of_isUnit χ (isUnits_det_units p.1), one_mul]
    _ = _ := by
        simp [Fintype.sum_prod_type, Nat.card_eq_fintype_card]

end Sum

end MulChar
