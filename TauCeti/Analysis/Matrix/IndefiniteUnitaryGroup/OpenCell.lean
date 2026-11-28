/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Analysis.Matrix.DeterminantBound.Lipschitz
import TauCeti.Analysis.Matrix.EntrywiseOpNorm
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Data.Nat.Factorial.NatCast
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse

/-!
# Matrices bounded in the open cell

Let `Z` be a square matrix of size `ϱ + 1` over a seminormed commutative ring, such as `ℝ` or
`ℂ`, with leading principal minors
`D_{ϱ+1} = det Z` and `D_ϱ` (the determinant of the top left block of size `ϱ`). For a real
number `N` the **discriminant** of `Z` is

`g_N(Z) = |D_{ϱ+1}|² - N² |D_ϱ|²`  (`Matrix.gramDisc N Z`).

The **open cell** (`Matrix.openCell`) is the set of invertible `Z` whose inverse has last
diagonal entry `ξ(Z)` of norm less than `1`; put `ν(Z) = (1 - |ξ(Z)|²) ^ (1/2)`
(`Matrix.openCellNu`). The matrix `Z` is **bounded in the cell by `P`**
(`Matrix.IsBoundedInCell P Z`) if it lies in the open cell and `‖Z‖`, `‖Z⁻¹‖` and `ν(Z)⁻¹` are at
most `P`; here `𝕜` is `RCLike` and matrices carry the `ℓ²` operator norm: these definitions and
results are stated in the scope `Matrix.Norms.L2Operator`, which users must open.

By the cofactor formula `ξ(Z) = D_ϱ / D_{ϱ+1}` (`Matrix.inv_apply_last_last`), so over a normed
field `1 - |ξ(Z)|² = g_1(Z) / |D_{ϱ+1}|²` for invertible `Z`
(`Matrix.openCellNu_eq_sqrt_gramDisc_div`): a matrix lies in the open cell exactly when
`g_1(Z) > 0` (`Matrix.mem_openCell_iff_gramDisc_pos`), so the open cell is open
(`Matrix.isOpen_openCell`), and `ν` is positive there (`Matrix.openCellNu_pos`). Bounds on the
entries and a lower bound for `g_1(Z)` then bound `Z`, its inverse (through the adjugate) and
`ν(Z)⁻¹`, and since the square of the norm of the determinant is Lipschitz on entrywise bounded
matrices (`Matrix.abs_norm_det_sq_sub_le`), the same holds on a small ball around `Z`.

## Main definitions

* `Matrix.gramDisc N Z`: the discriminant `|det Z|² - N² |D_ϱ|²`.
* `Matrix.openCell 𝕜 ϱ`: the open cell.
* `Matrix.openCellNu Z`: the number `ν(Z) = (1 - |ξ(Z)|²) ^ (1/2)`.
* `Matrix.IsBoundedInCell P Z`: `Z` is bounded in the cell by `P`.

## Main results

* `Matrix.mem_openCell_iff_gramDisc_pos`, `Matrix.isOpen_openCell`, `Matrix.openCellNu_pos` and
  `Matrix.openCellNu_eq_sqrt_gramDisc_div`: the open cell and `ν` through the discriminant.
* `Matrix.isBoundedInCell_of_inv_le_gramDisc`: if `ϱ + 1 ≤ M`, the entries of `Z` have norm at
  most `M²` and `g_1(Z) ≥ M⁻¹`, then `Z` is bounded in the cell by every `T ≥ M ^ (8 (ϱ + 1))`.
* `Matrix.gramDisc_div_two_le_and_isBoundedInCell`: if moreover `M ≥ 8 (ϱ + 1)` and
  `P ≥ M ^ (9 (ϱ + 1))`, every `Z'` with `‖Z' - Z‖ ≤ P⁻⁶` has `g_1(Z') ≥ g_1(Z) / 2` and is bounded
  in the cell by `P`.

## References

The open cell and these bounds are used in the analysis of Bessel functions on `U(p, q)` near
the big cell. The statements follow the formal proof in the folder `grh` of
https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
`New/Spanning/Bessel/OpenCellBound.lean`, declarations
`New.RealPlace.isBoundedInCell_of_inv_le_gramDiscReal` and
`New.RealPlace.gramDiscReal_div_two_le_and_isBoundedInCell`, with the definition
`New.RealPlace.gramDiscReal` of `New/Spanning/Bessel/Basic.lean`.
-/

public section

noncomputable section

open Fin Finset
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} {ϱ : ℕ}

/-! ### Definitions -/

section SeminormedCommRing

variable [SeminormedCommRing 𝕜]

/-- The **discriminant** `g_N(Z) = |D_{ϱ+1}|² - N² |D_ϱ|²` of a square matrix `Z` of size
`ϱ + 1`, where `D_{ϱ+1} = det Z` and `D_ϱ` is the leading principal minor of order `ϱ`. -/
def gramDisc (N : ℝ) (Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜) : ℝ :=
  ‖Z.det‖ ^ 2 - N ^ 2 * ‖(Z.submatrix castSucc castSucc).det‖ ^ 2

/-- Unfolding lemma for `Matrix.gramDisc`. -/
theorem gramDisc_def (N : ℝ) (Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜) :
    gramDisc N Z = ‖Z.det‖ ^ 2 - N ^ 2 * ‖(Z.submatrix castSucc castSucc).det‖ ^ 2 :=
  (rfl)

variable (𝕜 ϱ) in
/-- The **open cell**: the invertible square matrices of size `ϱ + 1` whose inverse has last
diagonal entry of norm less than `1`. -/
def openCell : Set (Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜) :=
  {Z | IsUnit Z ∧ ‖Z⁻¹ (last ϱ) (last ϱ)‖ < 1}

/-- Membership in the open cell, unfolded. -/
theorem mem_openCell_iff {Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜} :
    Z ∈ openCell 𝕜 ϱ ↔ IsUnit Z ∧ ‖Z⁻¹ (last ϱ) (last ϱ)‖ < 1 :=
  (Iff.rfl)

/-- The number `ν(Z) = (1 - |ξ(Z)|²) ^ (1/2)`, where `ξ(Z)` is the last diagonal entry of `Z⁻¹`.
It is positive on the open cell. -/
def openCellNu (Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜) : ℝ :=
  √(1 - ‖Z⁻¹ (last ϱ) (last ϱ)‖ ^ 2)

/-- Unfolding lemma for `Matrix.openCellNu`. -/
theorem openCellNu_def (Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜) :
    openCellNu Z = √(1 - ‖Z⁻¹ (last ϱ) (last ϱ)‖ ^ 2) :=
  (rfl)

/-- `ν(Z)` is positive on the open cell. -/
theorem openCellNu_pos {Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜} (hZ : Z ∈ openCell 𝕜 ϱ) :
    0 < openCellNu Z := by
  rw [openCellNu_def, Real.sqrt_pos, sub_pos]
  exact pow_lt_one₀ (norm_nonneg _) (mem_openCell_iff.1 hZ).2 two_ne_zero

end SeminormedCommRing

/-! ### The open cell through the discriminant -/

section NormedField

variable [NormedField 𝕜]

/-- A matrix lies in the open cell exactly when its discriminant `g_1(Z)` is positive. -/
theorem mem_openCell_iff_gramDisc_pos {Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜} :
    Z ∈ openCell 𝕜 ϱ ↔ 0 < gramDisc 1 Z := by
  rw [mem_openCell_iff, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, inv_apply_last_last,
    Ring.inverse_eq_inv', ← div_eq_inv_mul, norm_div, gramDisc_def, one_pow, one_mul, sub_pos]
  constructor
  · rintro ⟨hD, h⟩
    exact pow_lt_pow_left₀ ((div_lt_one (norm_pos_iff.2 hD)).1 h) (norm_nonneg _) two_ne_zero
  · intro h
    have hlt := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h
    have hD : 0 < ‖Z.det‖ := (norm_nonneg _).trans_lt hlt
    exact ⟨norm_pos_iff.1 hD, (div_lt_one hD).2 hlt⟩

/-- The open cell is open. -/
theorem isOpen_openCell : IsOpen (openCell 𝕜 ϱ) := by
  have hg : Continuous fun Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜 ↦ gramDisc 1 Z := by
    simp only [gramDisc_def]
    exact (continuous_id.matrix_det.norm.pow 2).sub (continuous_const.mul
      ((continuous_id.matrix_submatrix _ _).matrix_det.norm.pow 2))
  have hcell : openCell 𝕜 ϱ = (fun Z ↦ gramDisc 1 Z) ⁻¹' Set.Ioi 0 :=
    Set.ext fun _ ↦ mem_openCell_iff_gramDisc_pos
  rw [hcell]
  exact isOpen_Ioi.preimage hg

/-- For an invertible `Z`, `ν(Z) = g_1(Z) ^ (1/2) / |det Z|`. -/
theorem openCellNu_eq_sqrt_gramDisc_div {Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜}
    (hZ : IsUnit Z) : openCellNu Z = √(gramDisc 1 Z) / ‖Z.det‖ := by
  have hD : 0 < ‖Z.det‖ := norm_pos_iff.2 ((isUnit_iff_isUnit_det Z).1 hZ).ne_zero
  rw [openCellNu_def, inv_apply_last_last, Ring.inverse_eq_inv', ← div_eq_inv_mul, norm_div,
    ← Real.sqrt_sq hD.le, ← Real.sqrt_div' _ (by positivity)]
  congr 1
  field_simp
  simp [gramDisc_def]

end NormedField

variable [RCLike 𝕜]

/-- `Z` is **bounded in the cell by `P`**: it lies in the open cell, and its `ℓ²` operator norm,
that of its inverse, and `ν(Z)⁻¹` are at most `P`. -/
def IsBoundedInCell (P : ℝ) (Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜) : Prop :=
  Z ∈ openCell 𝕜 ϱ ∧ ‖Z‖ ≤ P ∧ ‖Z⁻¹‖ ≤ P ∧ (openCellNu Z)⁻¹ ≤ P

/-- Unfolding lemma for `Matrix.IsBoundedInCell`. -/
theorem isBoundedInCell_iff {P : ℝ} {Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜} :
    IsBoundedInCell P Z ↔ Z ∈ openCell 𝕜 ϱ ∧ ‖Z‖ ≤ P ∧ ‖Z⁻¹‖ ≤ P ∧ (openCellNu Z)⁻¹ ≤ P :=
  (Iff.rfl)

/-! ### Bounds from the entries and the discriminant -/

/-- If the entries of `Z` have norm at most `c ≥ 1` and `s ^ 2 ≤ g_1(Z)`, then `Z` is bounded in
the cell by every `P` with `(ϱ + 1) c ≤ P` and `(ϱ + 1)! c ^ (ϱ + 1) ≤ P s` (these force
`s > 0`). -/
private theorem isBoundedInCell_of_norm_apply_le {Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜}
    {c s P : ℝ} (hc : 1 ≤ c) (hZ : ∀ i j, ‖Z i j‖ ≤ c) (hg : s ^ 2 ≤ gramDisc 1 Z)
    (hP₁ : (ϱ + 1) * c ≤ P) (hP₂ : (ϱ + 1).factorial * c ^ (ϱ + 1) ≤ P * s) :
    IsBoundedInCell P Z := by
  have hP : 0 < P := (mul_pos (by positivity) (zero_lt_one.trans_le hc)).trans_le hP₁
  have hs : 0 < s := pos_of_mul_pos_right ((by positivity : (0 : ℝ) < _).trans_le hP₂) hP.le
  have hcell := mem_openCell_iff_gramDisc_pos.2 ((pow_pos hs 2).trans_le hg)
  have hg' : s ^ 2 ≤ ‖Z.det‖ ^ 2 - ‖(Z.submatrix castSucc castSucc).det‖ ^ 2 := by
    simpa [gramDisc_def] using hg
  have hsD : s ≤ ‖Z.det‖ := le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
    (by linarith [sq_nonneg ‖(Z.submatrix castSucc castSucc).det‖])
  have hDpos : 0 < ‖Z.det‖ := hs.trans_le hsD
  have hsg : s ≤ √(gramDisc 1 Z) := (Real.le_sqrt' hs).2 hg
  have hdet : ‖Z.det‖ ≤ (ϱ + 1).factorial * c ^ (ϱ + 1) := by
    simpa using norm_det_le_factorial_mul_pow hZ
  refine isBoundedInCell_iff.2 ⟨hcell, ?_, ?_, ?_⟩
  · simpa using (l2_opNorm_le_card_mul_of_norm_apply_le hZ).trans (by simpa using hP₁)
  · rw [inv_def, Ring.inverse_eq_inv', norm_smul, norm_inv, inv_mul_le_iff₀ hDpos]
    calc ‖Z.adjugate‖ ≤ (ϱ + 1) * (ϱ.factorial * c ^ ϱ) := by
          simpa using l2_opNorm_le_card_mul_of_norm_apply_le (norm_adjugate_apply_le hZ)
      _ ≤ (ϱ + 1).factorial * c ^ (ϱ + 1) := by
          rw [Nat.factorial_succ, Nat.cast_mul, mul_assoc]
          push_cast
          gcongr
          omega
      _ ≤ P * s := hP₂
      _ ≤ ‖Z.det‖ * P := by rw [mul_comm ‖Z.det‖]; exact mul_le_mul_of_nonneg_left hsD hP.le
  · rw [openCellNu_eq_sqrt_gramDisc_div (mem_openCell_iff.1 hcell).1, inv_div,
      div_le_iff₀ (hs.trans_le hsg)]
    exact hdet.trans (hP₂.trans (mul_le_mul_of_nonneg_left hsg hP.le))

/-- The discriminant moves by at most `4 ((ϱ + 1)!)² (ϱ + 1) c ^ (2 (ϱ + 1)) ε` between two
matrices whose entries have norm at most `c ≥ 1` and differ by at most `ε`. -/
private theorem abs_gramDisc_sub_le {Z Z' : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜} {c ε : ℝ}
    (hc : 1 ≤ c) (hZ : ∀ i j, ‖Z i j‖ ≤ c) (hZ' : ∀ i j, ‖Z' i j‖ ≤ c)
    (hZZ' : ∀ i j, ‖Z' i j - Z i j‖ ≤ ε) :
    |gramDisc 1 Z' - gramDisc 1 Z| ≤
      4 * (ϱ + 1).factorial ^ 2 * (ϱ + 1) * c ^ (2 * (ϱ + 1)) * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hZZ' 0 0)
  have h₁ := abs_norm_det_sq_sub_le hZ' hZ hZZ'
  have h₂ := abs_norm_det_sq_sub_le (A := Z'.submatrix castSucc castSucc)
    (B := Z.submatrix castSucc castSucc) (fun _ _ ↦ hZ' _ _) (fun _ _ ↦ hZ _ _)
    (fun _ _ ↦ hZZ' _ _)
  simp only [Fintype.card_fin] at h₁ h₂
  -- Both bounds are at most half of the claimed one, since `c ≥ 1`.
  have h₃ : 2 * ((ϱ + 1).factorial : ℝ) ^ 2 * (ϱ + 1 : ℕ) * c ^ (2 * (ϱ + 1) - 1) * ε ≤
      2 * (ϱ + 1).factorial ^ 2 * (ϱ + 1 : ℕ) * c ^ (2 * (ϱ + 1)) * ε := by
    gcongr
    omega
  have h₄ : 2 * (ϱ.factorial : ℝ) ^ 2 * ϱ * c ^ (2 * ϱ - 1) * ε ≤
      2 * (ϱ + 1).factorial ^ 2 * (ϱ + 1 : ℕ) * c ^ (2 * (ϱ + 1)) * ε := by
    gcongr <;> omega
  rw [gramDisc_def, gramDisc_def, one_pow, one_mul, one_mul]
  calc _ = |(‖Z'.det‖ ^ 2 - ‖Z.det‖ ^ 2) - (‖(Z'.submatrix castSucc castSucc).det‖ ^ 2 -
        ‖(Z.submatrix castSucc castSucc).det‖ ^ 2)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by push_cast at h₁ h₃ h₄ ⊢; linarith

/-! ### Bounds in the cell -/

/-- **Bounded in the cell.** If `ϱ + 1 ≤ M`, the entries of `Z` have norm at most `M²` and
`g_1(Z) ≥ M⁻¹`, then `Z` is bounded in the cell by every `T ≥ M ^ (8 (ϱ + 1))`. -/
theorem isBoundedInCell_of_inv_le_gramDisc {Z : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜}
    {M T : ℝ} (hn : ϱ + 1 ≤ M) (hZ : ∀ i j, ‖Z i j‖ ≤ M ^ 2) (hg : M⁻¹ ≤ gramDisc 1 Z)
    (hT : M ^ (8 * (ϱ + 1)) ≤ T) : IsBoundedInCell T Z := by
  have hM : 1 ≤ M := by linarith [(Nat.cast_nonneg ϱ : (0 : ℝ) ≤ ϱ)]
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hfac := Nat.cast_factorial_le_pow_of_le (n := ϱ + 1) (by push_cast; exact hn)
  refine isBoundedInCell_of_norm_apply_le (s := M⁻¹) (one_le_pow₀ hM) hZ ?_ ?_ ?_
  · refine le_trans ?_ hg
    rw [inv_pow, inv_le_inv₀ (by positivity) hM0]
    exact le_self_pow₀ hM two_ne_zero
  · calc (ϱ + 1) * M ^ 2 ≤ M * M ^ 2 := by gcongr
      _ = M ^ 3 := by ring
      _ ≤ M ^ (8 * (ϱ + 1)) := pow_le_pow_right₀ hM (by omega)
      _ ≤ T := hT
  · rw [le_mul_inv_iff₀ hM0, ← pow_mul]
    calc ((ϱ + 1).factorial : ℝ) * M ^ (2 * (ϱ + 1)) * M
        ≤ M ^ (ϱ + 1) * M ^ (2 * (ϱ + 1)) * M ^ 1 := by gcongr; rw [pow_one]
      _ = M ^ (3 * (ϱ + 1) + 1) := by rw [← pow_add, ← pow_add]; congr 1; ring
      _ ≤ M ^ (8 * (ϱ + 1)) := pow_le_pow_right₀ hM (by omega)
      _ ≤ T := hT

/-- The numerical inequality behind the second assertion: for `M ≥ 8 (ϱ + 1)` and
`P ≥ M ^ (9 (ϱ + 1))`, the bound of `abs_gramDisc_sub_le` with `c = 2 M²` and `ε = P⁻⁶` is at most
`(2 M)⁻¹`. -/
private theorem four_mul_factorial_sq_mul_le {M P : ℝ} (hM : 8 * (ϱ + 1) ≤ M)
    (hP : M ^ (9 * (ϱ + 1)) ≤ P) :
    4 * ((ϱ + 1).factorial : ℝ) ^ 2 * (ϱ + 1) * (2 * M ^ 2) ^ (2 * (ϱ + 1)) * (P ^ 6)⁻¹ ≤
      (2 * M)⁻¹ := by
  have hϱ : (0 : ℝ) ≤ ϱ := Nat.cast_nonneg ϱ
  have hM1 : 1 ≤ M := by linarith [hϱ]
  have hn : ((ϱ + 1 : ℕ) : ℝ) ≤ M := by push_cast; linarith [hϱ]
  have hfac := Nat.cast_factorial_le_pow_of_le hn
  have hP0 : 0 < P := (pow_pos (zero_lt_one.trans_le hM1) _).trans_le hP
  have h2 : 2 * M ^ 2 ≤ M ^ 3 := by
    rw [pow_succ, mul_comm 2]; exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg M)
  have h54 : 54 * (ϱ + 1) = 9 * (ϱ + 1) * 6 := by ring
  have hP6 : M ^ (54 * (ϱ + 1)) ≤ P ^ 6 := by
    rw [h54, pow_mul]
    gcongr
  rw [mul_inv_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  calc 4 * ((ϱ + 1).factorial : ℝ) ^ 2 * (ϱ + 1) * (2 * M ^ 2) ^ (2 * (ϱ + 1)) * (2 * M)
      = 8 * ((ϱ + 1).factorial : ℝ) ^ 2 * (ϱ + 1) * (2 * M ^ 2) ^ (2 * (ϱ + 1)) * M := by ring
    _ ≤ M * (M ^ (ϱ + 1)) ^ 2 * M * (M ^ 3) ^ (2 * (ϱ + 1)) * M := by
        gcongr
        · linarith
        · linarith
    _ = M ^ (8 * (ϱ + 1) + 3) := by rw [← pow_mul, ← pow_mul]; ring
    _ ≤ M ^ (54 * (ϱ + 1)) := pow_le_pow_right₀ hM1 (by omega)
    _ ≤ P ^ 6 := hP6

/-- **Bounded in the cell near `Z`.** If the entries of `Z` have norm at most `M²`,
`g_1(Z) ≥ M⁻¹`, `M ≥ 8 (ϱ + 1)` and `P ≥ M ^ (9 (ϱ + 1))`, then every `Z'` with
`‖Z' - Z‖ ≤ P⁻⁶` has `g_1(Z') ≥ g_1(Z) / 2` and is bounded in the cell by `P`. -/
theorem gramDisc_div_two_le_and_isBoundedInCell {Z Z' : Matrix (Fin (ϱ + 1)) (Fin (ϱ + 1)) 𝕜}
    {M P : ℝ} (hZ : ∀ i j, ‖Z i j‖ ≤ M ^ 2) (hg : M⁻¹ ≤ gramDisc 1 Z) (hM : 8 * (ϱ + 1) ≤ M)
    (hP : M ^ (9 * (ϱ + 1)) ≤ P) (hZ' : ‖Z' - Z‖ ≤ (P ^ 6)⁻¹) :
    gramDisc 1 Z / 2 ≤ gramDisc 1 Z' ∧ IsBoundedInCell P Z' := by
  have hM1 : 1 ≤ M := by linarith [(Nat.cast_nonneg ϱ : (0 : ℝ) ≤ ϱ)]
  have hP1 : 1 ≤ P := (one_le_pow₀ hM1).trans hP
  have hε : (P ^ 6)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hP1)
  have hd (i j) : ‖Z' i j - Z i j‖ ≤ (P ^ 6)⁻¹ := by
    simpa only [Matrix.sub_apply] using ((Z' - Z).norm_apply_le_l2_opNorm i j).trans hZ'
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
  have hc : 1 ≤ 2 * M ^ 2 := by linarith
  have hZ₂ (i j) : ‖Z i j‖ ≤ 2 * M ^ 2 := (hZ i j).trans (by linarith)
  have hn : (ϱ : ℝ) + 1 ≤ M := by linarith [(Nat.cast_nonneg ϱ : (0 : ℝ) ≤ ϱ)]
  have h2M : 2 * M ≤ M ^ 2 := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : 2 * M ^ 2 ≤ M ^ 3 := by
    rw [pow_succ, mul_comm 2]; exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg M)
  have hZ'₂ (i j) : ‖Z' i j‖ ≤ 2 * M ^ 2 := by
    have h := norm_add_le (Z i j) (Z' i j - Z i j)
    rw [add_sub_cancel] at h
    linarith [hZ i j, hd i j]
  have hΔ := (abs_gramDisc_sub_le hc hZ₂ hZ'₂ hd).trans
    (four_mul_factorial_sq_mul_le hM hP)
  have hhalf : gramDisc 1 Z / 2 ≤ gramDisc 1 Z' := by
    rw [mul_inv] at hΔ
    linarith [(abs_le.1 hΔ).1]
  refine ⟨hhalf, isBoundedInCell_of_norm_apply_le (s := (2 * M)⁻¹) hc hZ'₂ ?_ ?_ ?_⟩
  · have h₁ : (2 * M)⁻¹ ^ 2 ≤ (2 * M)⁻¹ :=
      pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by linarith)) two_ne_zero
    have h₂ : (2 * M)⁻¹ = M⁻¹ / 2 := by rw [mul_inv]; ring
    linarith
  · calc (ϱ + 1) * (2 * M ^ 2) ≤ M * M ^ 3 := by gcongr
      _ = M ^ 4 := by ring
      _ ≤ M ^ (9 * (ϱ + 1)) := pow_le_pow_right₀ hM1 (by omega)
      _ ≤ P := hP
  · have hfac := Nat.cast_factorial_le_pow_of_le (M := M) (n := ϱ + 1) (by push_cast; exact hn)
    rw [le_mul_inv_iff₀ (by positivity)]
    calc ((ϱ + 1).factorial : ℝ) * (2 * M ^ 2) ^ (ϱ + 1) * (2 * M)
        ≤ M ^ (ϱ + 1) * (M ^ 3) ^ (ϱ + 1) * M ^ 2 := by gcongr
      _ = M ^ (4 * (ϱ + 1) + 2) := by rw [← pow_mul]; ring
      _ ≤ M ^ (9 * (ϱ + 1)) := pow_le_pow_right₀ hM1 (by omega)
      _ ≤ P := hP

end Matrix
