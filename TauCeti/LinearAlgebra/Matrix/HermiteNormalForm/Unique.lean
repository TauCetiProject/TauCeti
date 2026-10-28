/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.HermiteNormalForm.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFounded
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# Uniqueness of the Hermite normal form

Two integer matrices in (column-style, upper) Hermite normal form with the same column lattice
have the same number of columns and are equal. So a sublattice of `ℤ^m` has at most one basis in
Hermite normal form, which can then serve as a canonical label for it: this is what makes the
Hermite matrix of an integer matrix, or of an ideal of a number field in a fixed integral basis,
well defined once it exists.

Along the way the pivot data of a matrix `H` in Hermite normal form is read off its column lattice
`L`: the pivot rows are the rows in which some vector of `L` has its lowest nonzero entry, and the
pivot in a given row divides the entry in that row of every vector of `L` vanishing below it. In
particular the pivot rows and the (positive) pivots depend only on `L`.

## Main results

* `Matrix.IsHermitePivotedBy.exists_mulVec_apply_pivot`: the lowest nonzero entry of a nonzero
  vector `H *ᵥ c` lies in the pivot row of the last column with a nonzero coefficient, and is that
  pivot times the coefficient.
* `Matrix.IsHermitePivotedBy.mem_range_iff`: the pivot rows are the rows in which a vector of the
  column lattice has its lowest nonzero entry.
* `Matrix.IsHermitePivotedBy.pivot_dvd_of_mem_range_mulVecLin`: the pivot in row `p j` divides the
  entry in that row of every lattice vector vanishing below it.
* `Matrix.IsHermiteNormalForm.width_eq_of_range_mulVecLin_eq`: two matrices in Hermite normal form
  with the same column lattice have the same number of columns.
* `Matrix.IsHermiteNormalForm.eq_of_range_mulVecLin_eq`: two matrices in Hermite normal form with
  the same column lattice are equal.
* `Matrix.IsHermiteNormalForm.sigma_mk_eq_of_range_mulVecLin_eq`: both statements at once, as an
  equality of pairs `⟨k, H⟩`.

## References

* Daniele Micciancio, *CSE 206A: Lattice Algorithms and Applications*, lecture 4 (Basic
  algorithms), Section 1: every lattice has a unique basis in Hermite normal form.
-/

public section

namespace Matrix

variable {m k k' : ℕ} {H : Matrix (Fin m) (Fin k) ℤ} {H' : Matrix (Fin m) (Fin k') ℤ}
  {p : Fin k → Fin m} {p' : Fin k' → Fin m}

namespace IsHermitePivotedBy

/-- If the coefficients `c` vanish beyond column `l`, then the entry of `H *ᵥ c` in the pivot row
of column `l` is the pivot times `c l`. -/
theorem mulVec_apply_pivot (h : H.IsHermitePivotedBy p) {c : Fin k → ℤ} {l : Fin k}
    (hc : ∀ l', l < l' → c l' = 0) : (H *ᵥ c) (p l) = H (p l) l * c l := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_single l (fun l' _ hne ↦ ?_) fun hl ↦ absurd (Finset.mem_univ l) hl
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [h.eq_zero_of_lt l' (h.strictMono hlt), zero_mul]
  · rw [hc l' hlt, mul_zero]

/-- If the coefficients `c` vanish beyond column `l`, then `H *ᵥ c` vanishes below the pivot row
of column `l`. -/
theorem mulVec_apply_eq_zero_of_lt (h : H.IsHermitePivotedBy p) {c : Fin k → ℤ} {l : Fin k}
    (hc : ∀ l', l < l' → c l' = 0) {i : Fin m} (hi : p l < i) : (H *ᵥ c) i = 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l' _ ↦ ?_
  rcases le_or_gt l' l with hle | hlt
  · rw [h.eq_zero_of_lt l' ((h.strictMono.monotone hle).trans_lt hi), zero_mul]
  · rw [hc l' hlt, mul_zero]

/-- For a nonzero coefficient vector `c`, let `l` be the last column with `c l ≠ 0`. Then `H *ᵥ c`
vanishes below the pivot row of column `l`, and its entry in that row is the pivot times `c l`;
in particular this is the lowest nonzero entry of `H *ᵥ c`. -/
theorem exists_mulVec_apply_pivot (h : H.IsHermitePivotedBy p) {c : Fin k → ℤ} (hc : c ≠ 0) :
    ∃ l, c l ≠ 0 ∧ (∀ l', l < l' → c l' = 0) ∧ (H *ᵥ c) (p l) = H (p l) l * c l ∧
      ∀ i, p l < i → (H *ᵥ c) i = 0 := by
  obtain ⟨l₀, hl₀⟩ := Function.ne_iff.mp hc
  obtain ⟨l, hl, hmax⟩ := (Finset.univ.filter (c · ≠ 0)).exists_max_image id
    ⟨l₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl₀⟩⟩
  have hc' : ∀ l', l < l' → c l' = 0 := fun l' hlt ↦
    not_not.mp fun hne ↦ (hmax l' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)).not_gt hlt
  exact ⟨l, (Finset.mem_filter.mp hl).2, hc', h.mulVec_apply_pivot hc',
    fun _ ↦ h.mulVec_apply_eq_zero_of_lt hc'⟩

/-- If `H *ᵥ c` vanishes below row `i`, then `c` vanishes on every column whose pivot row lies
below row `i`. -/
theorem eq_zero_of_mulVec_apply_eq_zero (h : H.IsHermitePivotedBy p) {c : Fin k → ℤ} {i : Fin m}
    (hv : ∀ i', i < i' → (H *ᵥ c) i' = 0) {l : Fin k} (hl : i < p l) : c l = 0 := by
  by_contra hcl
  obtain ⟨l', hl', hc', hpiv, -⟩ := h.exists_mulVec_apply_pivot (Function.ne_iff.mpr ⟨l, hcl⟩)
  have hle : l ≤ l' := not_lt.mp fun hlt ↦ hcl (hc' l hlt)
  rw [hv _ (hl.trans_le (h.strictMono.monotone hle))] at hpiv
  exact mul_ne_zero (h.pivot_ne_zero l') hl' hpiv.symm

/-- The pivot rows of a matrix in Hermite normal form are the rows in which some vector of its
column lattice has its lowest nonzero entry. -/
theorem mem_range_iff (h : H.IsHermitePivotedBy p) {i : Fin m} :
    i ∈ Set.range p ↔
      ∃ v ∈ LinearMap.range H.mulVecLin, v i ≠ 0 ∧ ∀ i', i < i' → v i' = 0 := by
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨H.col j, H.col_mem_range_mulVecLin j, h.pivot_ne_zero j, fun _ ↦ h.eq_zero_of_lt j⟩
  · rintro ⟨_, ⟨c, rfl⟩, hi, hbelow⟩
    rw [mulVecLin_apply] at hi hbelow
    obtain ⟨l, hl, -, hpiv, hzero⟩ :=
      h.exists_mulVec_apply_pivot (c := c) (by rintro rfl; exact hi (by simp))
    refine ⟨l, le_antisymm ?_ ?_⟩
    · exact not_lt.mp fun hlt ↦ mul_ne_zero (h.pivot_ne_zero l) hl (hpiv ▸ hbelow _ hlt)
    · exact not_lt.mp fun hlt ↦ hi (hzero i hlt)

/-- Two matrices in Hermite normal form with the same column lattice have the same pivot rows. -/
theorem range_eq_of_range_mulVecLin_eq (h : H.IsHermitePivotedBy p)
    (h' : H'.IsHermitePivotedBy p')
    (hHH' : LinearMap.range H.mulVecLin = LinearMap.range H'.mulVecLin) :
    Set.range p = Set.range p' := by
  ext i
  rw [h.mem_range_iff, h'.mem_range_iff, hHH']

/-- The pivot of column `j` divides the entry in row `p j` of every vector of the column lattice
vanishing below that row. -/
theorem pivot_dvd_of_mem_range_mulVecLin (h : H.IsHermitePivotedBy p) {v : Fin m → ℤ}
    (hv : v ∈ LinearMap.range H.mulVecLin) {j : Fin k} (hbelow : ∀ i, p j < i → v i = 0) :
    H (p j) j ∣ v (p j) := by
  obtain ⟨c, rfl⟩ := hv
  rw [mulVecLin_apply] at hbelow ⊢
  -- The vector only involves the first `j + 1` columns of `H`, and its entry in row `p j` is the
  -- pivot times the last coefficient.
  have hcj : ∀ l, j < l → c l = 0 := fun _ hlt ↦
    h.eq_zero_of_mulVec_apply_eq_zero hbelow (h.strictMono hlt)
  exact ⟨c j, h.mulVec_apply_pivot hcj⟩

/-- Two matrices in Hermite normal form with the same pivot rows and the same column lattice are
equal. -/
theorem eq_of_range_mulVecLin_eq {H' : Matrix (Fin m) (Fin k) ℤ} (h : H.IsHermitePivotedBy p)
    (h' : H'.IsHermitePivotedBy p)
    (hHH' : LinearMap.range H.mulVecLin = LinearMap.range H'.mulVecLin) : H = H' := by
  -- The pivots agree, since each divides the other.
  have hpiv : ∀ j, H (p j) j = H' (p j) j := fun j ↦
    Int.dvd_antisymm (h.pivot_pos j).le (h'.pivot_pos j).le
      (h.pivot_dvd_of_mem_range_mulVecLin (hHH' ▸ H'.col_mem_range_mulVecLin j) fun _ ↦
        h'.eq_zero_of_lt j)
      (h'.pivot_dvd_of_mem_range_mulVecLin (hHH'.symm ▸ H.col_mem_range_mulVecLin j) fun _ ↦
        h.eq_zero_of_lt j)
  ext i j
  refine congrFun (?_ : H.col j = H'.col j) i
  -- The difference of the two columns `j` is a lattice vector `H *ᵥ c` vanishing below `p j`.
  obtain ⟨c, hc⟩ : H'.col j - H.col j ∈ LinearMap.range H.mulVecLin :=
    sub_mem (hHH' ▸ H'.col_mem_range_mulVecLin j) (H.col_mem_range_mulVecLin j)
  rw [mulVecLin_apply] at hc
  suffices c = 0 by
    rw [this, mulVec_zero, eq_comm, sub_eq_zero] at hc
    exact hc.symm
  by_contra hc0
  obtain ⟨l, hl, -, hl_piv, -⟩ := h.exists_mulVec_apply_pivot hc0
  have hlj : l ≤ j := not_lt.mp fun hlt ↦ hl <| h.eq_zero_of_mulVec_apply_eq_zero
    (fun i hi ↦ by rw [hc, Pi.sub_apply, col_apply, col_apply, h.eq_zero_of_lt j hi,
      h'.eq_zero_of_lt j hi, sub_zero]) (h.strictMono hlt)
  rw [hc, Pi.sub_apply, col_apply, col_apply] at hl_piv
  rcases hlj.lt_or_eq with hlt | rfl
  · -- The lowest nonzero entry of the difference is a nonzero multiple of the pivot `H (p l) l`,
    -- but it is a difference of two entries reduced modulo that pivot.
    have h₁ := h.nonneg_of_lt hlt
    have h₂ := h.lt_pivot_of_lt hlt
    have h₃ := h'.nonneg_of_lt hlt
    have h₄ := h'.lt_pivot_of_lt hlt
    rw [← hpiv] at h₄
    rcases hl.lt_or_gt with hneg | hpos <;> nlinarith
  · -- In row `p l` the difference is the difference of the equal pivots.
    rw [← hpiv, sub_self, eq_comm] at hl_piv
    exact mul_ne_zero (h.pivot_ne_zero l) hl hl_piv

end IsHermitePivotedBy

namespace IsHermiteNormalForm

/-- Two matrices in Hermite normal form with the same column lattice have the same number of
columns, namely the number of rows in which a lattice vector has its lowest nonzero entry. -/
theorem width_eq_of_range_mulVecLin_eq (hH : H.IsHermiteNormalForm)
    (hH' : H'.IsHermiteNormalForm)
    (hHH' : LinearMap.range H.mulVecLin = LinearMap.range H'.mulVecLin) : k = k' := by
  obtain ⟨p, h⟩ := isHermiteNormalForm_iff.mp hH
  obtain ⟨p', h'⟩ := isHermiteNormalForm_iff.mp hH'
  have hcard := congrArg Set.ncard (h.range_eq_of_range_mulVecLin_eq h' hHH')
  simpa [Set.ncard_range_of_injective h.strictMono.injective,
    Set.ncard_range_of_injective h'.strictMono.injective] using hcard

/-- **Uniqueness of the Hermite normal form.** Two matrices in Hermite normal form with the same
column lattice are equal. -/
theorem eq_of_range_mulVecLin_eq {H' : Matrix (Fin m) (Fin k) ℤ} (hH : H.IsHermiteNormalForm)
    (hH' : H'.IsHermiteNormalForm)
    (hHH' : LinearMap.range H.mulVecLin = LinearMap.range H'.mulVecLin) : H = H' := by
  obtain ⟨p, h⟩ := isHermiteNormalForm_iff.mp hH
  obtain ⟨p', h'⟩ := isHermiteNormalForm_iff.mp hH'
  obtain rfl : p = p' := (h.strictMono.range_inj_of_wellFoundedLT h'.strictMono).mp
    (h.range_eq_of_range_mulVecLin_eq h' hHH')
  exact h.eq_of_range_mulVecLin_eq h' hHH'

/-- **Uniqueness of the Hermite normal form.** Two matrices in Hermite normal form with the same
column lattice have the same number of columns and are equal. -/
theorem sigma_mk_eq_of_range_mulVecLin_eq (hH : H.IsHermiteNormalForm)
    (hH' : H'.IsHermiteNormalForm)
    (hHH' : LinearMap.range H.mulVecLin = LinearMap.range H'.mulVecLin) :
    (⟨k, H⟩ : Σ k, Matrix (Fin m) (Fin k) ℤ) = ⟨k', H'⟩ := by
  obtain rfl := hH.width_eq_of_range_mulVecLin_eq hH' hHH'
  rw [hH.eq_of_range_mulVecLin_eq hH' hHH']

end IsHermiteNormalForm

/-! ### Examples -/

/-- A matrix in Hermite normal form whose columns span `ℤ^m` has `m` columns. -/
example {H : Matrix (Fin m) (Fin k) ℤ} (hH : H.IsHermiteNormalForm)
    (htop : LinearMap.range H.mulVecLin = ⊤) : k = m :=
  hH.width_eq_of_range_mulVecLin_eq IsHermiteNormalForm.one (by simpa using htop)

/-- The only square matrix in Hermite normal form whose columns span `ℤ^m` is the identity. -/
example {H : Matrix (Fin m) (Fin m) ℤ} (hH : H.IsHermiteNormalForm)
    (htop : LinearMap.range H.mulVecLin = ⊤) : H = 1 :=
  hH.eq_of_range_mulVecLin_eq IsHermiteNormalForm.one (by simpa using htop)

/-- The matrices with columns `(3, 0), (2, 1)` and `(3, 0), (5, 1)` have the same column lattice,
and the first is in Hermite normal form; so it is the only matrix in Hermite normal form with this
column lattice. -/
example {H : Matrix (Fin 2) (Fin 2) ℤ} (hH : H.IsHermiteNormalForm)
    (hHH : LinearMap.range H.mulVecLin = LinearMap.range (!![(3 : ℤ), 5; 0, 1]).mulVecLin) :
    H = !![3, 2; 0, 1] := by
  refine hH.eq_of_range_mulVecLin_eq (IsHermitePivotedBy.isHermiteNormalForm (p := id)
    ⟨strictMono_id, by decide, by decide, by decide, by decide⟩) (hHH.trans (le_antisymm ?_ ?_))
  · rintro _ ⟨c, rfl⟩
    exact ⟨![c 0 + c 1, c 1], by ext i; fin_cases i <;> simp [vecHead, vecTail]; ring⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨![c 0 - c 1, c 1], by ext i; fin_cases i <;> simp [vecHead, vecTail]; ring⟩

end Matrix
