/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.MulChar.Duality
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder

/-!
# Bounds at one from von Mangoldt truncations

A truncation estimate for the logarithmic derivative at one is converted to a bound for
its norm by Mertens' theorem. If the estimate holds up to a zero-free box height `Q`,
the choice `x = (log Q) ^ (2 + ε)` makes the truncation error bounded. The short sum
then costs `((2 + ε) / δ₀) * log (log Q)` plus a constant, uniformly in the character.
The fixed-width bound with coefficient `1000` is the one used in Levent Alpöge's
formalization of the Riemann hypothesis for Dirichlet L-functions.
-/

public section

open ArithmeticFunction Finset Filter

namespace DirichletCharacter

/-- A norm bound for the residual after a von Mangoldt truncation bounds the size of the
logarithmic derivative at one, with additive loss `log z + log 4 + 4` at cutoff `z ≥ 1`. -/
theorem norm_logDeriv_one_le_of_truncation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z E : ℝ} (hz : 1 ≤ z)
    (h : ‖logDeriv χ.LFunction 1 + ∑ n ∈ Ioc 0 ⌊z⌋₊, χ n * (Λ n : ℂ) / n‖ ≤ E) :
    ‖logDeriv χ.LFunction 1‖ ≤ E + (Real.log z + (Real.log 4 + 4)) := by
  have hsum : ‖∑ n ∈ Ioc 0 ⌊z⌋₊, χ n * (Λ n : ℂ) / n‖ ≤ Real.log z + (Real.log 4 + 4) := by
    refine (norm_sum_le_of_le _ (fun n _ ↦ ?_)).trans (Chebyshev.sum_vonMangoldt_div_le hz)
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (χ.norm_mul_vonMangoldt_le n) (Nat.cast_nonneg n)
  calc
    _ ≤ ‖logDeriv χ.LFunction 1 + (∑ n ∈ Ioc 0 ⌊z⌋₊, χ n * (Λ n : ℂ) / n)‖ +
        ‖∑ n ∈ Ioc 0 ⌊z⌋₊, χ n * (Λ n : ℂ) / n‖ := by
      let S : ℂ := ∑ n ∈ Ioc 0 ⌊z⌋₊, χ n * (Λ n : ℂ) / n
      simpa only [add_sub_cancel_right] using norm_sub_le (logDeriv χ.LFunction 1 + S) S
    _ ≤ _ := add_le_add h hsum

/-- For characters whose moduli are bounded by `M`, the logarithmic derivatives at one
have a common bound. Here `logDeriv` is total, so the principal characters need not be removed. -/
theorem exists_norm_logDeriv_one_le_of_level_le (M : ℕ) :
    ∃ B : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ M →
      ‖logDeriv χ.LFunction 1‖ ≤ B := by
  let J := Σ q : Fin (M + 1), DirichletCharacter ℂ (q : ℕ)
  let (q : Fin (M + 1)) : Finite (DirichletCharacter ℂ (q : ℕ)) := inferInstance
  let F : J → ℝ := fun j ↦ if h : (j.1 : ℕ) = 0 then 0 else
    letI : NeZero (j.1 : ℕ) := ⟨h⟩
    ‖logDeriv j.2.LFunction 1‖
  obtain ⟨B, hB⟩ := Finite.bddAbove_range F
  refine ⟨B, fun q _ χ hq ↦ ?_⟩
  simpa only [F, NeZero.ne q, dite_false] using hB (Set.mem_range_self (⟨⟨q, by omega⟩, χ⟩ : J))

/-- A uniform von Mangoldt truncation estimate in a zero-free box implies the bound
`((2 + ε) / δ₀) * log (log Q) + C` at one. The input is needed only at the offset
`δ₀ * ε / (2 + ε)` for nonprincipal characters; the conclusion is uniform in the modulus
and the box height. -/
theorem norm_logDeriv_one_le_log_log_of_truncation {δ₀ ε : ℝ}
    (hδ₀ : 0 < δ₀) (hε : -2 < ε)
    (htrunc : let δ := δ₀ * ε / (2 + ε)
      ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ Q : ℝ, (q : ℝ) ≤ Q → 2 ≤ Q →
      (∀ s : ℂ, 1 - δ₀ < s.re → |s.im| ≤ Q → χ.LFunction s ≠ 0) →
      ∀ x : ℝ, 2 ≤ x → x ^ (1 / δ₀ + 3) ≤ Q →
      ‖logDeriv χ.LFunction 1 + ∑ n ∈ Ioc 0 ⌊x ^ (1 / δ₀)⌋₊,
        χ n * (Λ n : ℂ) / n‖ ≤ K * (x ^ (-1 + δ / δ₀) * (Real.log Q) ^ 2)) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ Q : ℝ, (q : ℝ) ≤ Q → 2 ≤ Q →
      (∀ s : ℂ, 1 - δ₀ < s.re → |s.im| ≤ Q → χ.LFunction s ≠ 0) →
      ‖logDeriv χ.LFunction 1‖ ≤ ((2 + ε) / δ₀) * Real.log (Real.log Q) + C := by
  let p := 2 + ε
  let r := 1 / δ₀
  have hp : 0 < p := by dsimp [p]; linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hpr : p * r = (2 + ε) / δ₀ := by simp [p, r, div_eq_mul_inv]
  obtain ⟨K, hK⟩ := htrunc
  have hpow := (isLittleO_log_rpow_rpow_atTop (p * (r + 3)) (s := 1) one_pos).eventuallyLE
  have hscale : ∀ᶠ Q : ℝ in atTop, 0 < Real.log Q ∧ 2 ≤ (Real.log Q) ^ p ∧
      ((Real.log Q) ^ p) ^ (r + 3) ≤ Q := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,
      ((tendsto_rpow_atTop hp).comp Real.tendsto_log_atTop).eventually_ge_atTop 2,
      eventually_ge_atTop (0 : ℝ), hpow] with Q hlog hx hQ hpowQ
    refine ⟨hlog, hx, ?_⟩
    rw [Real.rpow_one, Real.norm_of_nonneg hQ, Real.norm_eq_abs] at hpowQ
    rw [← Real.rpow_mul hlog.le]
    exact (le_abs_self _).trans hpowQ
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp hscale
  obtain ⟨B, hB⟩ := exists_norm_logDeriv_one_le_of_level_le ⌊Q₀⌋₊
  let C := max (K + (Real.log 4 + 4)) (B - (p * r) * Real.log (Real.log 2))
  refine ⟨C, fun q _ χ hχ Q hq hQ hbox ↦ ?_⟩
  rw [← hpr]
  by_cases hlarge : Q₀ ≤ Q
  · obtain ⟨hlog, hx, hxQ⟩ := hQ₀ Q hlarge
    have hcancel : p * (-1 + δ₀ * ε / (2 + ε) / δ₀) = -2 := by
      have hp' : 2 + ε ≠ 0 := hp.ne'
      dsimp only [p]
      field_simp [hp', hδ₀.ne']
      ring
    have herr : ((Real.log Q) ^ p) ^ (-1 + δ₀ * ε / (2 + ε) / δ₀) *
        (Real.log Q) ^ 2 = 1 := by
      rw [← Real.rpow_mul hlog.le, hcancel, Real.rpow_neg hlog.le, Real.rpow_two,
        inv_mul_cancel₀ (pow_ne_zero _ hlog.ne')]
    have htail := hK q χ hχ Q hq hQ hbox ((Real.log Q) ^ p) hx hxQ
    rw [herr, mul_one] at htail
    have hz : 1 ≤ ((Real.log Q) ^ p) ^ r := Real.one_le_rpow (by linarith) hr.le
    refine (χ.norm_logDeriv_one_le_of_truncation hz htail).trans ?_
    rw [← Real.rpow_mul hlog.le, Real.log_rpow hlog]
    have hmax : K + (Real.log 4 + 4) ≤ C := le_max_left _ _
    linarith only [hmax]
  · have hbounded : q ≤ ⌊Q₀⌋₊ := Nat.le_floor (hq.trans (lt_of_not_ge hlarge).le)
    have hlog : Real.log (Real.log 2) ≤ Real.log (Real.log Q) :=
      Real.log_le_log (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hQ)
    have hmono := mul_le_mul_of_nonneg_left hlog (mul_nonneg hp.le hr.le)
    refine (hB q χ hbounded).trans ?_
    have hmax : B - (p * r) * Real.log (Real.log 2) ≤ C := le_max_right _ _
    linarith only [hmax, hmono]

end DirichletCharacter
