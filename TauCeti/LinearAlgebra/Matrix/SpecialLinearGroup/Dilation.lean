/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.SpecialFunctions.Exp.Half
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The dilations in `SL(2, ℝ)`

The diagonal matrices `dilation s = !![exp (s / 2), 0; 0, exp (-(s / 2))]` form a one-parameter
subgroup of `SL(2, ℝ)` (`dilation_zero`, `dilation_add`, `dilation_inv`): the positive component
of the diagonal subgroup of `SL(2, ℝ)`, parametrised by the logarithm of the eigenvalue ratio.
Acting on the upper half-plane by Möbius transformations they are the dilations
`z ↦ exp s * z`, which is why the parameter is `s` rather than the eigenvalue `exp (s / 2)`:
`dilation s` moves a point of the imaginary axis upward by the signed displacement `s`, that is,
by hyperbolic distance `|s|`, upward for `s > 0` and downward for `s < 0`.

## Main declarations

* `Matrix.SpecialLinearGroup.dilation`: the dilation matrix, with entries `coe_dilation`.
* `Matrix.SpecialLinearGroup.dilation_add`, `dilation_inv`, `dilation_zpow`: the family is a
  one-parameter subgroup.
* `Matrix.SpecialLinearGroup.eq_dilation_two_mul_log`: every diagonal matrix of `SL(2, ℝ)` with
  positive entries is a dilation.
* `Matrix.SpecialLinearGroup.conj_dilation_apply_zero_zero` and its siblings: the entries of a
  conjugate `X * dilation s * X⁻¹`; `dilation_conj_apply_zero_one` and its siblings: conjugation
  by a dilation rescales the off-diagonal entries inversely.
* `Matrix.SpecialLinearGroup.conj_dilation_eq_dilation`, `conj_dilation_eq_dilation_neg`: a
  diagonal matrix conjugates `dilation s` to itself and an antidiagonal one to `dilation (-s)`;
  conversely `diag_or_antidiag_of_conj_dilation`: only these conjugate a nontrivial dilation to
  a diagonal matrix; `off_diag_eq_zero_of_mk_eq_dilation`: a matrix whose class in `PSL(2, ℝ)` is
  a dilation is diagonal.
* `Matrix.SpecialLinearGroup.exists_dilation_conj_le`: conjugating by a suitable integer power of
  a dilation balances the two off-diagonal entries of a matrix of `SL(2, ℝ)`.
* `Matrix.SpecialLinearGroup.trace_dilation`, `trace_commutatorElement_dilation`: the trace of a
  dilation and of its commutator with any matrix of `SL(2, ℝ)`.
-/

public section

noncomputable section

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-- The dilation `!![exp (s / 2), 0; 0, exp (-(s / 2))]`, an element of `SL(2, ℝ)` acting on `ℍ`
as `z ↦ exp s * z`. -/
def dilation (s : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.exp (s / 2), 0; 0, Real.exp (-(s / 2))], by
    rw [Matrix.det_fin_two_of]
    simp [← Real.exp_add]⟩

/-- The entries of `dilation s`. -/
@[simp]
theorem coe_dilation (s : ℝ) :
    (dilation s : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.exp (s / 2), 0; 0, Real.exp (-(s / 2))] :=
  (rfl)

/-- The dilation by `0` is the identity. -/
@[simp]
theorem dilation_zero : dilation 0 = 1 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
    fin_cases i <;> fin_cases j <;> simp

/-- The dilations form a one-parameter subgroup: `dilation (s + t) = dilation s * dilation t`. -/
theorem dilation_add (s t : ℝ) : dilation (s + t) = dilation s * dilation t :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add, add_div, add_comm]

/-- The inverse of `dilation s` is `dilation (-s)`. -/
@[simp]
theorem dilation_inv (s : ℝ) : (dilation s)⁻¹ = dilation (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← dilation_add, add_neg_cancel, dilation_zero])

/-- The integer powers of `dilation s` are the dilations by the integer multiples of `s`. -/
@[simp]
theorem dilation_zpow (s : ℝ) (k : ℤ) : dilation s ^ k = dilation (k * s) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one, ih, ← dilation_add]
      congr 1
      push_cast
      ring
  | pred n ih =>
      rw [zpow_sub_one, ih, dilation_inv, ← dilation_add]
      congr 1
      push_cast
      ring

/-- A diagonal matrix of `SL(2, ℝ)` with positive entries is a dilation: the one by twice the
logarithm of its top-left entry. -/
theorem eq_dilation_two_mul_log {A : SL(2, ℝ)} (h₁₀ : A 1 0 = 0) (h₀₁ : A 0 1 = 0)
    (hpos : 0 < A 0 0) : A = dilation (2 * Real.log (A 0 0)) := by
  have hdet := A.det_coe
  rw [Matrix.det_fin_two, h₁₀, h₀₁, mul_zero, sub_zero] at hdet
  have h₁₁ : A 1 1 = (A 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h₁₀, h₀₁, h₁₁, Real.exp_neg, Real.exp_log hpos]

/-! ### Conjugates of a dilation -/

attribute [local simp] Matrix.adjugate_fin_two

/-- The top-left entry of a conjugate `X * dilation s * X⁻¹` of a dilation. -/
theorem conj_dilation_apply_zero_zero (s : ℝ) (X : SL(2, ℝ)) :
    (X * dilation s * X⁻¹) 0 0 =
      Real.exp (s / 2) + (Real.exp (s / 2) - Real.exp (-(s / 2))) * (X 0 1 * X 1 0) := by
  have h := X.fin_two_mul_sub_mul_eq_one
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination Real.exp (s / 2) * h

/-- The top-right entry of a conjugate `X * dilation s * X⁻¹` of a dilation. -/
theorem conj_dilation_apply_zero_one (s : ℝ) (X : SL(2, ℝ)) :
    (X * dilation s * X⁻¹) 0 1 = X 0 0 * X 0 1 * (Real.exp (-(s / 2)) - Real.exp (s / 2)) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The bottom-left entry of a conjugate `X * dilation s * X⁻¹` of a dilation. -/
theorem conj_dilation_apply_one_zero (s : ℝ) (X : SL(2, ℝ)) :
    (X * dilation s * X⁻¹) 1 0 = X 1 0 * X 1 1 * (Real.exp (s / 2) - Real.exp (-(s / 2))) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The bottom-right entry of a conjugate `X * dilation s * X⁻¹` of a dilation. -/
theorem conj_dilation_apply_one_one (s : ℝ) (X : SL(2, ℝ)) :
    (X * dilation s * X⁻¹) 1 1 =
      Real.exp (-(s / 2)) - (Real.exp (s / 2) - Real.exp (-(s / 2))) * (X 0 1 * X 1 0) := by
  have h := X.fin_two_mul_sub_mul_eq_one
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination Real.exp (-(s / 2)) * h

/-- Conjugation by a dilation fixes the top-left entry. -/
theorem dilation_conj_apply_zero_zero (r : ℝ) (X : SL(2, ℝ)) :
    (dilation r * X * dilation (-r)) 0 0 = X 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, neg_div]
  linear_combination X 0 0 * Real.exp_half_mul_exp_neg_half r

/-- Conjugation by `dilation r` multiplies the top-right entry by `exp r`. -/
theorem dilation_conj_apply_zero_one (r : ℝ) (X : SL(2, ℝ)) :
    (dilation r * X * dilation (-r)) 0 1 = Real.exp r * X 0 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, neg_div]
  linear_combination X 0 1 * Real.exp_half_mul_exp_half r

/-- Conjugation by `dilation r` multiplies the bottom-left entry by `exp (-r)`. -/
theorem dilation_conj_apply_one_zero (r : ℝ) (X : SL(2, ℝ)) :
    (dilation r * X * dilation (-r)) 1 0 = Real.exp (-r) * X 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, neg_div]
  linear_combination X 1 0 * Real.exp_neg_half_mul_exp_neg_half r

/-- Conjugation by a dilation fixes the bottom-right entry. -/
theorem dilation_conj_apply_one_one (r : ℝ) (X : SL(2, ℝ)) :
    (dilation r * X * dilation (-r)) 1 1 = X 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, neg_div]
  linear_combination X 1 1 * Real.exp_half_mul_exp_neg_half r

/-- A diagonal matrix of `SL(2, ℝ)` commutes with every dilation: it fixes the fixed points `0`
and `∞` of the dilation. -/
theorem conj_dilation_eq_dilation (s : ℝ) {X : SL(2, ℝ)} (h01 : X 0 1 = 0) (h10 : X 1 0 = 0) :
    X * dilation s * X⁻¹ = dilation s :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      simp [conj_dilation_apply_zero_zero, conj_dilation_apply_zero_one,
        conj_dilation_apply_one_zero, conj_dilation_apply_one_one, h01, h10]

/-- An antidiagonal matrix of `SL(2, ℝ)` conjugates `dilation s` to its inverse `dilation (-s)`:
it exchanges the fixed points `0` and `∞` of the dilation. -/
theorem conj_dilation_eq_dilation_neg (s : ℝ) {X : SL(2, ℝ)} (h00 : X 0 0 = 0)
    (h11 : X 1 1 = 0) : X * dilation s * X⁻¹ = dilation (-s) := by
  have hbc : X 0 1 * X 1 0 = -1 := by
    linear_combination -X.fin_two_mul_sub_mul_eq_one + X 1 1 * h00
  exact Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      simp [conj_dilation_apply_zero_zero, conj_dilation_apply_zero_one,
        conj_dilation_apply_one_zero, conj_dilation_apply_one_one, h00, h11, hbc, neg_div]

/-- If `X * dilation s * X⁻¹` is diagonal for a nontrivial dilation, then `X` is diagonal or
antidiagonal. -/
theorem diag_or_antidiag_of_conj_dilation {s : ℝ} (hs : s ≠ 0) {X : SL(2, ℝ)}
    (h01 : (X * dilation s * X⁻¹) 0 1 = 0) (h10 : (X * dilation s * X⁻¹) 1 0 = 0) :
    (X 0 1 = 0 ∧ X 1 0 = 0) ∨ (X 0 0 = 0 ∧ X 1 1 = 0) := by
  have huv : Real.exp (s / 2) - Real.exp (-(s / 2)) ≠ 0 := by
    rw [sub_ne_zero, Ne, Real.exp_eq_exp]
    intro h
    exact hs (by linarith)
  rw [conj_dilation_apply_zero_one] at h01
  rw [conj_dilation_apply_one_zero] at h10
  have hab : X 0 0 * X 0 1 = 0 :=
    (mul_eq_zero.1 h01).resolve_right fun h ↦ huv (by linear_combination -h)
  have hcd : X 1 0 * X 1 1 = 0 := (mul_eq_zero.1 h10).resolve_right huv
  have h := X.fin_two_mul_sub_mul_eq_one
  rcases mul_eq_zero.1 hab with ha | hb
  · have hc : X 1 0 ≠ 0 := by
      rintro hc
      rw [ha, hc] at h
      simp at h
    exact Or.inr ⟨ha, (mul_eq_zero.1 hcd).resolve_left hc⟩
  · have hd : X 1 1 ≠ 0 := by
      rintro hd
      rw [hb, hd] at h
      simp at h
    exact Or.inl ⟨hb, (mul_eq_zero.1 hcd).resolve_right hd⟩

/-- A matrix of `SL(2, ℝ)` whose class in `PSL(2, ℝ)` is a dilation is diagonal. -/
theorem off_diag_eq_zero_of_mk_eq_dilation {Y : SL(2, ℝ)} {t : ℝ}
    (h : (Y : PSL(2, ℝ)) = ((dilation t : SL(2, ℝ)) : PSL(2, ℝ))) : Y 0 1 = 0 ∧ Y 1 0 = 0 := by
  rcases Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff.1 h with h | h
  · simp [← h]
  · simp [neg_eq_iff_eq_neg.1 h.symm]

/-! ### Balancing the off-diagonal entries -/

/-- For `s > 0`, conjugating a matrix of `SL(2, ℝ)` by a suitable power of `dilation s` makes both
of its off-diagonal entries at most `exp s * ρ` in absolute value, as soon as their product is at
most `ρ ^ 2`. -/
theorem exists_dilation_conj_le {s : ℝ} (hs : 0 < s) {X : SL(2, ℝ)} {ρ : ℝ} (hρ : 0 < ρ)
    (hX : |X 0 1 * X 1 0| ≤ ρ ^ 2) :
    ∃ k : ℤ, |(dilation (k * s) * X * dilation (-(k * s))) 0 1| ≤ Real.exp s * ρ ∧
      |(dilation (k * s) * X * dilation (-(k * s))) 1 0| ≤ Real.exp s * ρ := by
  simp only [dilation_conj_apply_zero_one, dilation_conj_apply_one_zero]
  generalize X 0 1 = x, X 1 0 = y at hX ⊢
  have hes : 1 ≤ Real.exp s := Real.one_le_exp hs.le
  have hρle : ρ ≤ Real.exp s * ρ := le_mul_of_one_le_left hρ.le hes
  rw [abs_mul] at hX
  by_cases hy : y = 0
  · by_cases hx : x = 0
    · exact ⟨0, by rw [hx, mul_zero, abs_zero]; positivity,
        by rw [hy, mul_zero, abs_zero]; positivity⟩
    -- make the first entry small: `k s ≤ log ρ - log |x|`
    have hx0 : 0 < |x| := abs_pos.2 hx
    refine ⟨⌊(Real.log ρ - Real.log |x|) / s⌋, ?_, by rw [hy, mul_zero, abs_zero]; positivity⟩
    have hk : (⌊(Real.log ρ - Real.log |x|) / s⌋ : ℝ) * s ≤ Real.log ρ - Real.log |x| :=
      (le_div_iff₀ hs).1 (Int.floor_le _)
    rw [abs_mul, Real.abs_exp]
    calc Real.exp (⌊(Real.log ρ - Real.log |x|) / s⌋ * s) * |x|
        ≤ Real.exp (Real.log ρ - Real.log |x|) * |x| :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hk) (abs_nonneg _)
      _ = ρ := by rw [Real.exp_sub, Real.exp_log hρ, Real.exp_log hx0]; field_simp
      _ ≤ Real.exp s * ρ := hρle
  -- make the second entry small: `log |y| - log ρ ≤ k s < log |y| - log ρ + s`
  have hy0 : 0 < |y| := abs_pos.2 hy
  set m := (Real.log |y| - Real.log ρ) / s
  refine ⟨⌈m⌉, ?_, ?_⟩
  · have hk : (⌈m⌉ : ℝ) * s ≤ Real.log |y| - Real.log ρ + s := by
      have := (Int.ceil_lt_add_one m).le
      rw [← le_div_iff₀ hs]
      calc (⌈m⌉ : ℝ) ≤ m + 1 := this
        _ = (Real.log |y| - Real.log ρ + s) / s := by rw [add_div, div_self hs.ne']
    rw [abs_mul, Real.abs_exp]
    calc Real.exp (⌈m⌉ * s) * |x| ≤ Real.exp (Real.log |y| - Real.log ρ + s) * |x| :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hk) (abs_nonneg _)
      _ = Real.exp s * (|x| * |y|) / ρ := by
          rw [Real.exp_add, Real.exp_sub, Real.exp_log hy0, Real.exp_log hρ]
          field_simp
      _ ≤ Real.exp s * ρ ^ 2 / ρ := by gcongr
      _ = Real.exp s * ρ := by field_simp
  · have hk : Real.log |y| - Real.log ρ ≤ (⌈m⌉ : ℝ) * s :=
      (div_le_iff₀ hs).1 (Int.le_ceil m)
    rw [abs_mul, Real.abs_exp]
    calc Real.exp (-(⌈m⌉ * s)) * |y| ≤ Real.exp (-(Real.log |y| - Real.log ρ)) * |y| :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg hk)) (abs_nonneg _)
      _ = ρ := by
          rw [neg_sub, Real.exp_sub, Real.exp_log hy0, Real.exp_log hρ]
          field_simp
      _ ≤ Real.exp s * ρ := hρle

/-! ### Traces -/

/-- The trace of `dilation s` is `exp (s / 2) + exp (-(s / 2))`. -/
theorem trace_dilation (s : ℝ) :
    ((dilation s : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      Real.exp (s / 2) + Real.exp (-(s / 2)) := by
  simp [Matrix.trace_fin_two]

open scoped commutatorElement in
/-- The trace of the commutator of `dilation s` with `X = !![a, b; c, d]` is
`2 - (exp (s / 2) - exp (-(s / 2))) ^ 2 * (b * c)`. -/
theorem trace_commutatorElement_dilation (s : ℝ) (X : SL(2, ℝ)) :
    ((⁅dilation s, X⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      2 - (Real.exp (s / 2) - Real.exp (-(s / 2))) ^ 2 * (X 0 1 * X 1 0) := by
  have h := X.fin_two_mul_sub_mul_eq_one
  have hu := Real.exp_half_mul_exp_half s
  have hv := Real.exp_neg_half_mul_exp_neg_half s
  have huv := Real.exp_half_mul_exp_neg_half s
  rw [commutatorElement_def, coe_mul _ X⁻¹, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, dilation_inv, dilation_conj_apply_zero_zero,
    dilation_conj_apply_zero_one, dilation_conj_apply_one_zero, dilation_conj_apply_one_one]
  simp only [inv_apply_zero_zero, inv_apply_zero_one, inv_apply_one_zero, inv_apply_one_one,
    mul_neg]
  linear_combination 2 * h + X 0 1 * X 1 0 * hu + X 0 1 * X 1 0 * hv -
    2 * (X 0 1 * X 1 0) * huv

end Matrix.SpecialLinearGroup
