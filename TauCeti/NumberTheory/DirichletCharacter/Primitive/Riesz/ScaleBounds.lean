/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Lipschitz
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder

/-!
# Scale bounds for primitive Dirichlet Riesz remainders

The remainder at conductor one subtracts a logarithmic term, unlike the remainders of
nontrivial primitive characters. Nevertheless, the same cap variation estimate holds for
all conductors. On an interval of radius one around a scale `x`, changing the argument to
`x` costs at most a logarithmic bound, which also controls `‖Gχ(x)‖ / x`.

For a fixed finite set of characters and any further characters with logarithmic derivative
bounded by `C' * log x` at one, the constant in these last two estimates is independent of
the choice of the further characters. These are the pointwise inputs to the thick-place
comparison in Levent Alpöge's `Deduction.CharacterBalanceMoves.one_char` in
[`ChCore.lean`][ch-core]. The principal estimates use the Chebyshev Riesz bounds in
`TauCeti.NumberTheory.Chebyshev.RieszRemainder`, and the nonprincipal estimates use the bounds in
`TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder`.

[ch-core]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean
-/

public section

open Finset Real
open scoped ArithmeticFunction

namespace TauCeti.PrimitiveDirichletCharacter

/-- The conductor-one remainder is the complexification of the real von Mangoldt sum
with its logarithmic and Euler–Mascheroni corrections. -/
theorem rieszRemainder_one_eq_ofReal (y : ℝ) :
    (1 : PrimitiveDirichletCharacter).rieszRemainder y =
      ((∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) - y * log y +
        (1 + eulerMascheroniConstant) * y : ℝ) : ℂ) := by
  rw [rieszRemainder_one, Complex.ofReal_add, Complex.ofReal_sub,
    ofReal_sum_Ioc_floor_mul_div_sub_one]
  push_cast
  ring

/-- Changing a positive cap in a scaled primitive Dirichlet remainder costs at most
`3 * (a / min w v) * |w - v|`, including at conductor one. -/
theorem norm_mul_rieszRemainder_div_sub_le (χ : PrimitiveDirichletCharacter) {a w v : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hv : 0 < v) :
    ‖(w : ℂ) * χ.rieszRemainder (a / w) - (v : ℂ) * χ.rieszRemainder (a / v)‖ ≤
      3 * (a / min w v) * |w - v| := by
  rcases eq_or_ne χ 1 with rfl | hχ
  · rw [rieszRemainder_one_eq_ofReal, rieszRemainder_one_eq_ofReal, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact Chebyshev.abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le ha hw hv
  · simpa only [rieszRemainder_of_ne_one hχ] using
      χ.character.norm_mul_rieszSum_div_add_mul_logDeriv_sub_le ha hw hv

/-- Between zero and one, the trivial Riesz remainder differs from its value at one by
at most `(1 + γ) * (1 - y)`. Here the von Mangoldt sum vanishes. -/
theorem norm_rieszRemainder_one_sub_rieszRemainder_one_le {y : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) :
    ‖(1 : PrimitiveDirichletCharacter).rieszRemainder y -
      (1 : PrimitiveDirichletCharacter).rieszRemainder 1‖ ≤
      (1 + eulerMascheroniConstant) * (1 - y) := by
  have hsmall (z : ℝ) (hz : z ≤ 1) : (1 : PrimitiveDirichletCharacter).rieszRemainder z =
      ((z * (1 + eulerMascheroniConstant) - z * log z : ℝ) : ℂ) := by
    rw [rieszRemainder_one, rieszSum_eq_zero_of_le_one _ hz, zero_add]
    push_cast
    ring
  rw [hsmall y hy₁, hsmall 1 le_rfl, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_le]
  simp only [one_mul, log_one, sub_zero]
  have hγ : 0 ≤ eulerMascheroniConstant * (1 - y) :=
    mul_nonneg (by linarith [one_half_lt_eulerMascheroniConstant]) (sub_nonneg.mpr hy₁)
  constructor
  · linarith only [mul_log_nonpos hy₀ hy₁]
  · linarith only [self_sub_one_le_mul_log hy₀, hγ, sub_nonneg.mpr hy₁]

/-- At conductor one the Riesz remainder is `(log 4 + 4 + γ)`-Lipschitz against a scale
`x ≥ 1`, for every `y ≥ 0`. Below one this uses the closed form of the remainder. -/
theorem norm_rieszRemainder_one_sub_le {x y : ℝ} (hy : 0 ≤ y) (hx : 1 ≤ x) :
    ‖(1 : PrimitiveDirichletCharacter).rieszRemainder y -
      (1 : PrimitiveDirichletCharacter).rieszRemainder x‖ ≤
      (log 4 + 4 + eulerMascheroniConstant) * |y - x| := by
  set F := (1 : PrimitiveDirichletCharacter).rieszRemainder
  set A := log 4 + 4 + eulerMascheroniConstant
  have hsub (z : ℝ) (hz : 1 ≤ z) : ‖F z - F x‖ ≤ A * |z - x| := by
    simpa only [F, A, rieszRemainder_one_eq_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using
      Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le hz hx
  by_cases hy₁ : 1 ≤ y
  · exact hsub y hy₁
  have hy₁' : y ≤ 1 := le_of_not_ge hy₁
  have hA : 1 + eulerMascheroniConstant ≤ A := by
    have : 0 ≤ log 4 := log_nonneg (by norm_num)
    dsimp only [A]
    linarith
  calc
    _ ≤ ‖F y - F 1‖ + ‖F 1 - F x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1 + eulerMascheroniConstant) * (1 - y) + A * |1 - x| :=
      add_le_add (norm_rieszRemainder_one_sub_rieszRemainder_one_le hy hy₁') (hsub 1 le_rfl)
    _ ≤ A * |y - x| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx), abs_of_nonpos (sub_nonpos.mpr (hy₁'.trans hx))]
      calc
        _ ≤ A * (1 - y) + A * -(1 - x) := by gcongr
        _ = _ := by ring

/-- A bound for the nonprincipal logarithmic derivative gives the same error budget for
freezing the Riesz argument within one unit of `x` and for bounding the remainder at `x`
after dividing by `x`. At conductor one no logarithmic derivative is needed. -/
theorem norm_rieszRemainder_sub_le_and_norm_le (χ : PrimitiveDirichletCharacter) {x y K : ℝ}
    (hx : 1 ≤ x) (hy : |y - x| ≤ 1)
    (hK : χ ≠ 1 → ‖logDeriv χ.character.LFunction 1‖ ≤ K) :
    let D := log (x + 1) + (log 4 + 6 + eulerMascheroniConstant) + max K 0
    ‖χ.rieszRemainder y - χ.rieszRemainder x‖ ≤ D ∧ ‖χ.rieszRemainder x‖ ≤ x * D := by
  dsimp only
  obtain ⟨hlo, hhi⟩ := abs_le.mp hy
  have hlog : log (max y x) ≤ log (x + 1) :=
    log_le_log (by positivity) (max_le (by linarith) (by linarith))
  have hxlog : log x ≤ log (x + 1) := log_le_log (by positivity) (by linarith)
  have hlog₀ : 0 ≤ log (x + 1) := log_nonneg (by linarith)
  have hγ : 0 ≤ eulerMascheroniConstant :=
    le_trans (by norm_num) one_half_lt_eulerMascheroniConstant.le
  have hmax : 0 ≤ max K 0 := le_max_right ..
  rcases eq_or_ne χ 1 with rfl | hχ
  · have hvar := norm_rieszRemainder_one_sub_le (y := y) (by linarith) hx
    refine ⟨hvar.trans ((mul_le_of_le_one_right (by positivity) hy).trans ?_), ?_⟩
    · linarith
    · rw [rieszRemainder_one_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
      refine (Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_le hx).trans ?_
      rw [mul_comm _ x]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · simp only [rieszRemainder_of_ne_one hχ]
    have hderiv := (hK hχ).trans (le_max_left K 0)
    constructor
    · refine (χ.character.norm_rieszSum_add_mul_logDeriv_sub_le (le_max_of_le_right hx)).trans ?_
      refine (mul_le_of_le_one_left ?_ hy).trans (by linarith)
      have : 0 ≤ log (max y x) := log_nonneg (le_max_of_le_right hx)
      positivity
    · exact (χ.character.norm_rieszSum_add_mul_logDeriv_le hx).trans
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

/-- Fix the finite set of characters whose logarithmic derivatives need not satisfy a
uniform hypothesis. A single constant bounds the change from `y` to `x` by `C * log x`
and the remainder at `x` by `x * (C * log x)`, for every `x ≥ 2` and `|y - x| ≤ 1`. It also
works for every nontrivial character with `‖L′/L(1,χ)‖ ≤ C' * log x` at that scale, and for
the trivial character without any restriction. -/
theorem exists_norm_rieszRemainder_sub_le_mul_log_and_norm_le
    (S : Finset PrimitiveDirichletCharacter) (C' : ℝ) :
    ∃ C > 0, ∀ (χ : PrimitiveDirichletCharacter) ⦃x y : ℝ⦄, 2 ≤ x → |y - x| ≤ 1 →
      (χ ∉ S → χ ≠ 1 → ‖logDeriv χ.character.LFunction 1‖ ≤ C' * log x) →
      ‖χ.rieszRemainder y - χ.rieszRemainder x‖ ≤ C * log x ∧
        ‖χ.rieszRemainder x‖ ≤ x * (C * log x) := by
  let B := ∑ χ ∈ S, ‖logDeriv χ.character.LFunction 1‖
  let A := log 4 + 6 + eulerMascheroniConstant
  have hB : 0 ≤ B := sum_nonneg fun _ _ ↦ norm_nonneg _
  have hA : 0 ≤ A := by
    have : 0 ≤ log 4 := log_nonneg (by norm_num)
    have := one_half_lt_eulerMascheroniConstant
    dsimp only [A]
    linarith
  have hlog₂ : 0 < log 2 := log_pos (by norm_num)
  let C := 2 + (A + B) / log 2 + max C' 0
  refine ⟨C, by dsimp only [C]; positivity, fun χ x y hx hy hχ ↦ ?_⟩
  have hlogx := log_le_log (by norm_num : (0 : ℝ) < 2) hx
  have hlog₀ : 0 ≤ log x := hlog₂.le.trans hlogx
  let K := B + max C' 0 * log x
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hχK (h₁ : χ ≠ 1) : ‖logDeriv χ.character.LFunction 1‖ ≤ K := by
    by_cases hm : χ ∈ S
    · exact (single_le_sum (f := fun ψ ↦ ‖logDeriv ψ.character.LFunction 1‖)
        (fun _ _ ↦ norm_nonneg _) hm).trans
        (le_add_of_nonneg_right (b := max C' 0 * log x) (by positivity))
    · exact (hχ hm h₁).trans ((mul_le_mul_of_nonneg_right (le_max_left C' 0) hlog₀).trans
        (le_add_of_nonneg_left hB))
  have hlog : log (x + 1) ≤ 2 * log x := by
    calc
      log (x + 1) ≤ log (x ^ 2) := log_le_log (by positivity)
        (by nlinarith only [hx, sq_nonneg (x - 2)])
      _ = 2 * log x := by simp [log_pow]
  have hbudget : log (x + 1) + A + max K 0 ≤ C * log x := by
    rw [max_eq_left hK]
    have hconst : A + B ≤ (A + B) / log 2 * log x := calc
      A + B = (A + B) / log 2 * log 2 := (div_mul_cancel₀ _ hlog₂.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogx (by positivity)
    dsimp only [C, K]
    linarith only [hlog, hconst, mul_nonneg (le_max_right C' 0) hlog₀]
  obtain ⟨hvar, hsize⟩ := χ.norm_rieszRemainder_sub_le_and_norm_le (by linarith) hy hχK
  exact ⟨hvar.trans hbudget, hsize.trans (mul_le_mul_of_nonneg_left hbudget (by positivity))⟩

end TauCeti.PrimitiveDirichletCharacter
