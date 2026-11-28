/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Complementary block columns and inverse rows in `GL n R`

For an index splitting `e : b ⊕ a ≃ n` and an invertible matrix `γ : GL n R` over a commutative
ring `R`, this file defines the `n × b` block of first columns `firstCols e γ` of `γ` together with
the complementary `b × n` and `a × n` blocks `invFirstRows e γ` and `invLastRows e γ` of `γ⁻¹`,
and proves that agreeing on `invLastRows e` implies that `firstCols e γ'` differs from
`firstCols e γ` by right multiplication by an invertible `h : GL b R` with
`γ'.val.det = γ.val.det * h.val.det`.

## Main definitions and results

* `TauCeti.firstCols`, `TauCeti.invFirstRows`, `TauCeti.invLastRows`: the complementary column
  and inverse-row submatrices of `γ : GL n R` along `e : b ⊕ a ≃ n`.
* `TauCeti.invFirstRows_mul_firstCols`: `invFirstRows e γ * firstCols e γ = 1`.
* `TauCeti.invLastRows_mul_firstCols`: `invLastRows e γ * firstCols e γ = 0`.
* `TauCeti.firstCols_mul_invFirstRows_mul`: if `invLastRows e γ * M = 0`, then
  `firstCols e γ * (invFirstRows e γ * M) = M`.
* `TauCeti.exists_firstCols_eq_mul_of_invLastRows_eq`: if `invLastRows e γ = invLastRows e γ'`,
  then `firstCols e γ' = firstCols e γ * h.val` and `γ'.val.det = γ.val.det * h.val.det` for some
  `h : GL b R`.

## Provenance

Adapted from `src/New/Determinant/Chain/SquareLaw.lean`
(`New.Exchange.exists_firstCols_eq_mul_of_invLastRows_eq`) and
`src/New/Determinant/Exchange/MatchingPartners.lean` (`New.firstCols`, `New.invFirstRows`,
`New.invLastRows`) in <https://github.com/lsernau/grh-lean> at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Matrix

variable {R a b n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The `n × b` submatrix of `γ : GL n R` formed by the columns indexed by `b` along
`e : b ⊕ a ≃ n`. -/
def firstCols (e : b ⊕ a ≃ n) (γ : GL n R) : Matrix n b R :=
  γ.val.submatrix id (e ∘ Sum.inl)

/-- The `b × n` submatrix of `γ⁻¹` formed by the rows indexed by `b` along `e : b ⊕ a ≃ n`. -/
def invFirstRows (e : b ⊕ a ≃ n) (γ : GL n R) : Matrix b n R :=
  γ⁻¹.val.submatrix (e ∘ Sum.inl) id

/-- The `a × n` submatrix of `γ⁻¹` formed by the rows indexed by `a` along `e : b ⊕ a ≃ n`. -/
def invLastRows (e : b ⊕ a ≃ n) (γ : GL n R) : Matrix a n R :=
  γ⁻¹.val.submatrix (e ∘ Sum.inr) id

/-- The first `b` rows of `γ⁻¹` times the first `b` columns of `γ` is the identity matrix. -/
theorem invFirstRows_mul_firstCols [DecidableEq b] (e : b ⊕ a ≃ n) (γ : GL n R) :
    invFirstRows e γ * firstCols e γ = 1 := by
  ext i j
  have h : (γ⁻¹.val * γ.val) (e (.inl i)) (e (.inl j)) = (1 : Matrix n n R) (e (.inl i))
      (e (.inl j)) := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simpa [invFirstRows, firstCols, Matrix.mul_apply, Matrix.one_apply] using h

/-- The last `a` rows of `γ⁻¹` times the first `b` columns of `γ` is zero. -/
theorem invLastRows_mul_firstCols (e : b ⊕ a ≃ n) (γ : GL n R) :
    invLastRows e γ * firstCols e γ = 0 := by
  ext i j
  have h : (γ⁻¹.val * γ.val) (e (.inr i)) (e (.inl j)) = (1 : Matrix n n R) (e (.inr i))
      (e (.inl j)) := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simpa [invLastRows, firstCols, Matrix.mul_apply, Matrix.one_apply] using h

/-- If `invLastRows e γ * M = 0`, then `M` is recovered by projecting via `invFirstRows e γ` and
multiplying on the left by `firstCols e γ`. -/
theorem firstCols_mul_invFirstRows_mul [Fintype b] {c : Type*} (e : b ⊕ a ≃ n)
    (γ : GL n R) {M : Matrix n c R} (hM : invLastRows e γ * M = 0) :
    firstCols e γ * (invFirstRows e γ * M) = M := by
  have : Finite a := Finite.of_injective (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective)
  cases nonempty_fintype a
  ext i k
  have h_id : (γ.val * (γ⁻¹.val * M)) i k = M i k := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rw [← h_id, Matrix.mul_apply, Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  have h_inr (j : a) : (γ⁻¹.val * M) (e (.inr j)) k = 0 := by
    simpa [invLastRows, Matrix.mul_apply] using congrFun (congrFun hM j) k
  simp only [h_inr, mul_zero, Finset.sum_const_zero, add_zero, firstCols, invFirstRows,
    submatrix_apply, id_eq, Function.comp_apply, Matrix.mul_apply]

/-- If `γ, γ' : GL n R` have the same last `a` rows in their inverses (`invLastRows e`), then
`firstCols e γ' = firstCols e γ * h.val` and `γ'.val.det = γ.val.det * h.val.det` for some
`h : GL b R`. -/
theorem exists_firstCols_eq_mul_of_invLastRows_eq [Fintype b] [DecidableEq b]
    {e : b ⊕ a ≃ n} {γ γ' : GL n R} (h_eq : invLastRows e γ = invLastRows e γ') :
    ∃ h : GL b R, firstCols e γ' = firstCols e γ * h.val ∧ γ'.val.det = γ.val.det * h.val.det := by
  classical
  have : Finite a := Finite.of_injective (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective)
  cases nonempty_fintype a
  have h_cols : firstCols e γ * (invFirstRows e γ * firstCols e γ') = firstCols e γ' :=
    firstCols_mul_invFirstRows_mul e γ (by rw [h_eq, invLastRows_mul_firstCols])
  have h_inv : (invFirstRows e γ' * firstCols e γ) * (invFirstRows e γ * firstCols e γ') = 1 := by
    rw [Matrix.mul_assoc, h_cols, invFirstRows_mul_firstCols]
  have h_unit : IsUnit (invFirstRows e γ * firstCols e γ').det :=
    isUnit_iff_exists_inv.mpr ⟨(invFirstRows e γ' * firstCols e γ).det,
      by rw [mul_comm, ← Matrix.det_mul, h_inv, Matrix.det_one]⟩
  let h : GL b R := GeneralLinearGroup.mk'' (invFirstRows e γ * firstCols e γ') h_unit
  refine ⟨h, h_cols.symm, ?_⟩
  have h_one : (γ.val * γ⁻¹.val).det = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h_row (i : a) (k : n) : γ⁻¹.val (e (.inr i)) k = γ'⁻¹.val (e (.inr i)) k :=
    congrFun (congrFun h_eq i) k
  have h_tri : (γ⁻¹.val * γ'.val).submatrix e e =
      fromBlocks h.val ((γ⁻¹.val * γ'.val).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)) 0 1 := by
    ext (i | i) (j | j)
    · rfl
    · rfl
    · have h2 := congrFun (congrFun (invLastRows_mul_firstCols e γ') i) j
      simp only [submatrix_apply, fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.mul_apply, h_row]
      simpa only [invLastRows, firstCols, submatrix_apply, id_eq, Function.comp_apply,
        Matrix.mul_apply, Matrix.zero_apply] using h2
    · have h2 : (γ'⁻¹.val * γ'.val) (e (.inr i)) (e (.inr j)) =
          (1 : Matrix n n R) (e (.inr i)) (e (.inr j)) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp only [submatrix_apply, fromBlocks_apply₂₂, Matrix.mul_apply, h_row]
      simpa only [Matrix.mul_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq,
        Sum.inr.injEq] using h2
  have h_det_prod : γ⁻¹.val.det * γ'.val.det = h.val.det := by
    rw [← Matrix.det_mul, ← Matrix.det_submatrix_equiv_self e, h_tri, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one]
  rw [← h_det_prod, ← mul_assoc, ← Matrix.det_mul, h_one, one_mul]

end TauCeti
