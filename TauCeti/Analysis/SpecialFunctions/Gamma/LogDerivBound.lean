/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
public import TauCeti.Analysis.SpecialFunctions.Gamma.Real
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# An explicit bound for the real-place gamma term on `[1, 3]`

The constant `gammaLogDerivBound`, written `C_Γ`, is
`(|-γ - 2 log 2| + |2 - γ - 2 log 2| + |log π|) / 2`, built from Euler's constant and elementary
logarithms only. The first two absolute values are `|ψ(1/2)|` and `|ψ(3/2)|`, which sum to `2`,
so `C_Γ = 1 + (log π) / 2 ≈ 1.57236`.

For real `1 ≤ s ≤ 3`, `logDeriv Gammaℝ s = ψ(s/2)/2 - (log π)/2` is real, negative, and lies
between its values `ψ(1/2)/2 - (log π)/2 ≈ -1.55412` at `s = 1` and
`ψ(3/2)/2 - (log π)/2 ≈ -0.55412` at `s = 3`, because real digamma is monotone on the positive
axis. Hence `‖logDeriv Gammaℝ s‖ ≤ C_Γ`. The interval `[1, 3]` covers both parity shifts `σ + κ`
with `1 < σ ≤ 2` and `κ ∈ {0, 1}` of the gamma factor of a Dirichlet L-function.

## Main declarations

* `TauCeti.gammaLogDerivBound`: the constant `C_Γ`.
* `TauCeti.gammaLogDerivBound_eq_digamma`, `TauCeti.gammaLogDerivBound_eq`,
  `TauCeti.gammaLogDerivBound_nonneg`: `C_Γ = (ψ(3/2) - ψ(1/2) + log π) / 2 = 1 + (log π) / 2`
  and `0 ≤ C_Γ`.
* `Complex.logDeriv_Gammaℝ_ofReal`: at a positive real point, the logarithmic derivative of
  `Gammaℝ` is the real number `ψ(s/2)/2 - (log π)/2`.
* `Complex.re_logDeriv_Gammaℝ_ofReal_mem_Icc`, `Complex.re_logDeriv_Gammaℝ_ofReal_neg`: on
  `[1, 3]` it lies between its endpoint values and is negative.
* `Complex.norm_logDeriv_Gammaℝ_ofReal_le`: on `[1, 3]` its norm is at most `C_Γ`.
* `Complex.norm_logDeriv_Gammaℝ_one`, `Complex.one_lt_norm_logDeriv_Gammaℝ_one`: the norm at the
  tight end `s = 1` is `(γ + 2 log 2 + log π) / 2`, which exceeds `1`, so the `|log π|` term
  of `C_Γ` cannot be dropped.

## References

* NIST Digital Library of Mathematical Functions, §§5.4 and 5.5.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 14.
-/

public section

open Real Set

/-- `log π` is positive. -/
theorem Real.log_pi_pos : 0 < log π := log_pos (by linarith [two_le_pi])

namespace TauCeti

/-- The constant `C_Γ = (|-γ - 2 log 2| + |2 - γ - 2 log 2| + |log π|) / 2` bounding the
logarithmic derivative of `Gammaℝ` on the real interval `[1, 3]`. The first two absolute values
are `|ψ(1/2)|` and `|ψ(3/2)|`. -/
noncomputable def gammaLogDerivBound : ℝ :=
  (|-eulerMascheroniConstant - 2 * log 2| + |2 - eulerMascheroniConstant - 2 * log 2| +
    |log π|) / 2

/-- `C_Γ = (ψ(3/2) - ψ(1/2) + log π) / 2`, since `ψ(1/2) < 0 < ψ(3/2)` and `log π > 0`. -/
theorem gammaLogDerivBound_eq_digamma :
    gammaLogDerivBound = (digamma (3 / 2) - digamma (1 / 2) + log π) / 2 := by
  rw [gammaLogDerivBound, ← digamma_one_half, ← digamma_three_halves,
    abs_of_neg digamma_one_half_neg, abs_of_pos digamma_three_halves_pos, abs_of_pos log_pi_pos]
  ring

/-- `C_Γ = 1 + (log π) / 2`: `-ψ(1/2)` and `ψ(3/2)` are positive and sum to `2`. -/
theorem gammaLogDerivBound_eq : gammaLogDerivBound = 1 + log π / 2 := by
  rw [gammaLogDerivBound_eq_digamma, digamma_one_half, digamma_three_halves]
  ring

/-- The constant `C_Γ` is nonnegative. -/
theorem gammaLogDerivBound_nonneg : 0 ≤ gammaLogDerivBound := by
  unfold gammaLogDerivBound
  positivity

end TauCeti

namespace Complex

open TauCeti

/-- At a positive real point, the logarithmic derivative of `Gammaℝ` is the real number
`ψ(s/2)/2 - (log π)/2`. -/
theorem logDeriv_Gammaℝ_ofReal {s : ℝ} (hs : 0 < s) :
    logDeriv Gammaℝ (s : ℂ) = ((Real.digamma (s / 2) / 2 - Real.log π / 2 : ℝ) : ℂ) := by
  have hpole : ∀ n : ℕ, (s : ℂ) ≠ -(2 * n) := by
    intro n hn
    have : s = -(2 * n) := by exact_mod_cast hn
    have := n.cast_nonneg (α := ℝ)
    linarith
  rw [logDeriv_Gammaℝ hpole, show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; rfl,
    digamma_ofReal]
  push_cast
  rfl

/-- For real `1 ≤ s ≤ 3`, the logarithmic derivative of `Gammaℝ` lies between its values
`ψ(1/2)/2 - (log π)/2` at `s = 1` and `ψ(3/2)/2 - (log π)/2` at `s = 3`. -/
theorem re_logDeriv_Gammaℝ_ofReal_mem_Icc {s : ℝ} (hs : s ∈ Icc 1 3) :
    (logDeriv Gammaℝ (s : ℂ)).re ∈
      Icc (Real.digamma (1 / 2) / 2 - Real.log π / 2)
        (Real.digamma (3 / 2) / 2 - Real.log π / 2) := by
  obtain ⟨h1, h3⟩ := hs
  rw [logDeriv_Gammaℝ_ofReal (by linarith), ofReal_re]
  have hm := Real.monotoneOn_digamma
  constructor
  · linarith [hm (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) (show s / 2 ∈ Ioi 0 by
      simp only [mem_Ioi]; linarith) (by linarith)]
  · linarith [hm (show s / 2 ∈ Ioi 0 by simp only [mem_Ioi]; linarith)
      (show (3 / 2 : ℝ) ∈ Ioi 0 by norm_num) (by linarith)]

/-- For real `1 ≤ s ≤ 3`, the logarithmic derivative of `Gammaℝ` is negative:
`ψ(3/2) ≤ log (3/2) < log π`. -/
theorem re_logDeriv_Gammaℝ_ofReal_neg {s : ℝ} (hs : s ∈ Icc 1 3) :
    (logDeriv Gammaℝ (s : ℂ)).re < 0 := by
  have hup := (re_logDeriv_Gammaℝ_ofReal_mem_Icc hs).2
  have hψ := (Real.digamma_le_log_le (show (0 : ℝ) < 3 / 2 by norm_num)).1
  have hlog : Real.log (3 / 2) < Real.log π :=
    Real.log_lt_log (by norm_num) (by linarith [two_le_pi])
  linarith

/-- For real `1 ≤ s ≤ 3`, the logarithmic derivative of `Gammaℝ` has norm at most `C_Γ`. -/
theorem norm_logDeriv_Gammaℝ_ofReal_le {s : ℝ} (hs : s ∈ Icc 1 3) :
    ‖logDeriv Gammaℝ (s : ℂ)‖ ≤ gammaLogDerivBound := by
  have hmem := re_logDeriv_Gammaℝ_ofReal_mem_Icc hs
  rw [logDeriv_Gammaℝ_ofReal (by linarith [hs.1]), ofReal_re] at hmem
  rw [logDeriv_Gammaℝ_ofReal (by linarith [hs.1]), norm_real, Real.norm_eq_abs,
    gammaLogDerivBound_eq_digamma, abs_le]
  have := Real.digamma_one_half_neg
  have := Real.digamma_three_halves_pos
  have := log_pi_pos
  constructor <;> linarith [hmem.1, hmem.2]

/-- The norm of the logarithmic derivative of `Gammaℝ` at `s = 1`, where the bound `C_Γ` is
nearly attained: `(γ + 2 log 2 + log π) / 2 ≈ 1.55412`. -/
theorem norm_logDeriv_Gammaℝ_one :
    ‖logDeriv Gammaℝ 1‖ = (eulerMascheroniConstant + 2 * Real.log 2 + Real.log π) / 2 := by
  have h := logDeriv_Gammaℝ_ofReal (s := 1) one_pos
  rw [ofReal_one, show (1 : ℝ) / 2 = 1 / 2 from rfl] at h
  rw [h, norm_real, Real.norm_eq_abs,
    abs_of_neg (by linarith [Real.digamma_one_half_neg, log_pi_pos]), Real.digamma_one_half]
  ring

/-- At `s = 1` the norm of the logarithmic derivative of `Gammaℝ` exceeds `1`, so the bound
`C_Γ` needs its `|log π|` term: without it the constant would be `1`. -/
theorem one_lt_norm_logDeriv_Gammaℝ_one : 1 < ‖logDeriv Gammaℝ 1‖ := by
  rw [norm_logDeriv_Gammaℝ_one]
  have hγ := one_half_lt_eulerMascheroniConstant
  have h2 := log_two_gt_d9
  have h3 : 1 < Real.log π := by
    rw [lt_log_iff_exp_lt pi_pos]
    linarith [exp_one_lt_d9, pi_gt_three]
  norm_num at h2
  linarith

/-- The norm of the logarithmic derivative of `Gammaℝ` at `s = 3`:
`(log π - ψ(3/2)) / 2 ≈ 0.55412`. -/
theorem norm_logDeriv_Gammaℝ_three :
    ‖logDeriv Gammaℝ 3‖ = (Real.log π - Real.digamma (3 / 2)) / 2 := by
  have h := re_logDeriv_Gammaℝ_ofReal_neg (s := 3) ⟨by norm_num, le_rfl⟩
  rw [logDeriv_Gammaℝ_ofReal (s := 3) (by norm_num), ofReal_re] at h
  have h' := logDeriv_Gammaℝ_ofReal (s := 3) (by norm_num)
  rw [show ((3 : ℝ) : ℂ) = 3 by norm_num] at h'
  rw [h', norm_real, Real.norm_eq_abs, abs_of_neg h]
  ring

end Complex
