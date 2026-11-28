/-
Copyright (c) 2026 Tau Ceti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Padded leading-row matrices and leading principal minors

For an `n × n` matrix `M` and `j : Fin (n + 1)`, `TauCeti.paddedLeading j M` keeps the first `j`
rows of `M` and replaces the remaining `n - j` rows by those of the identity matrix. Its
determinant is the leading `j × j` principal minor of `M`, and any vector supported on indices
`< j` has the same image under `paddedLeading j M` as under `M` on the first `j` entries (and `0`
on the rest), giving a quick criterion for vanishing of the leading `j × j` minor.

## Main definitions and results

* `TauCeti.paddedLeading`: the matrix obtained by keeping the first `j` rows of `M` and filling
  the remaining rows from `1`.
* `TauCeti.det_paddedLeading`: `(paddedLeading j M).det` equals the leading `j × j` minor of `M`.
* `TauCeti.paddedLeading_mulVec_eq_zero`: if `M *ᵥ x = 0` and `x` vanishes at indices `≥ j`, then
  `paddedLeading j M *ᵥ x = 0`.
* `TauCeti.det_leadingMinor_eq_zero_of_mulVec_eq_zero`: over a domain, if `M` annihilates a
  nonzero vector supported on indices `< j`, then the leading `j × j` minor of `M` vanishes.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/Spanning/RemainingTerms/BorderedDeterminant.lean`, declarations
`New.Filling.paddedLeading`, `New.Filling.det_paddedLeading`, and
`New.Filling.leadingMinor_eq_zero_of_mulVec_eq_zero`, generalized from `Fin (ϱ + 1)` over a CM
field to arbitrary `Fin n` over a commutative ring (or domain).
-/

@[expose] public section

namespace TauCeti

open Matrix

/-- The `n × n` matrix whose first `j` rows agree with `M` and whose remaining rows agree with the
identity matrix. -/
def paddedLeading {R : Type*} [Zero R] [One R] {n : ℕ} (j : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b ↦ if a.val < j.val then M a b else if a = b then 1 else 0

@[simp]
theorem paddedLeading_apply {R : Type*} [Zero R] [One R] {n : ℕ} (j : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    paddedLeading j M a b = if a.val < j.val then M a b else if a = b then 1 else 0 := rfl

/-- The determinant of `paddedLeading j M` is the leading `j × j` principal minor of `M`. -/
@[simp]
theorem det_paddedLeading {R : Type*} [CommRing R] {n : ℕ} (j : Fin (n + 1))
    (M : Matrix (Fin n) (Fin n) R) :
    (paddedLeading j M).det =
      (M.submatrix (Fin.castLE j.is_le) (Fin.castLE j.is_le)).det := by
  let e : Fin j.val ⊕ Fin (n - j.val) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le j.is_le))
  rw [← det_submatrix_equiv_self e]
  have h_blk : (paddedLeading j M).submatrix e e =
      fromBlocks (M.submatrix (Fin.castLE j.is_le) (Fin.castLE j.is_le))
        (M.submatrix (Fin.castLE j.is_le) (fun b : Fin (n - j.val) ↦ e (.inr b))) 0 1 := by
    ext (a | a) (b | b)
    · simp [e, paddedLeading, a.isLt]; rfl
    · simp [e, paddedLeading, a.isLt]; rfl
    · have ha : ¬ (e (.inr a)).val < j.val := by simp [e]
      have hne : e (.inr a) ≠ e (.inl b) := fun h ↦ Sum.inr_ne_inl (e.injective h)
      simp [paddedLeading, ha, hne]
    · have ha : ¬ (e (.inr a)).val < j.val := by simp [e]
      simp [paddedLeading, ha, e.injective.eq_iff, Matrix.one_apply]
  rw [h_blk, det_fromBlocks_zero₂₁, det_one, mul_one]

/-- If `M *ᵥ x = 0` and `x` vanishes at all indices `≥ j`, then `paddedLeading j M *ᵥ x = 0`. -/
theorem paddedLeading_mulVec_eq_zero {R : Type*} [CommRing R] {n : ℕ} {j : Fin (n + 1)}
    {M : Matrix (Fin n) (Fin n) R} {x : Fin n → R} (hMx : M *ᵥ x = 0)
    (h_above : ∀ b : Fin n, j.val ≤ b.val → x b = 0) :
    paddedLeading j M *ᵥ x = 0 := by
  funext a
  have ha_row : (M *ᵥ x) a = 0 := congrFun hMx a
  by_cases ha : a.val < j.val
  · simpa [paddedLeading, mulVec, dotProduct, ha] using ha_row
  · have hxa : x a = 0 := h_above a (Nat.le_of_not_lt ha)
    simp [paddedLeading, mulVec, dotProduct, ha, hxa]

/-- Over an integral domain, if `M` annihilates a nonzero vector `x` whose entries vanish at all
indices `≥ j`, then the leading `j × j` principal minor of `M` is zero. -/
theorem det_leadingMinor_eq_zero_of_mulVec_eq_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {j : Fin (n + 1)} {M : Matrix (Fin n) (Fin n) R} {x : Fin n → R} (hx_ne : x ≠ 0)
    (hMx : M *ᵥ x = 0) (h_above : ∀ b : Fin n, j.val ≤ b.val → x b = 0) :
    (M.submatrix (Fin.castLE j.is_le) (Fin.castLE j.is_le)).det = 0 := by
  rw [← det_paddedLeading]
  exact exists_mulVec_eq_zero_iff.mp ⟨x, hx_ne, paddedLeading_mulVec_eq_zero hMx h_above⟩

end TauCeti
