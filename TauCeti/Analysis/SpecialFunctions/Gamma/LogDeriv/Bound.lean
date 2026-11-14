/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
public import TauCeti.Analysis.SpecialFunctions.Gamma.Real
public import TauCeti.Analysis.SpecialFunctions.Log.Pi
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# An explicit bound for the real-place gamma term on `[1, 3]`

The constant `gammaLogDerivBound`, written `C_Γ`, is
`(|-γ - 2 log 2| + |2 - γ - 2 log 2| + |log π|) / 2`, built from Euler's constant and elementary
logarithms only. The first two absolute values are `|ψ(1/2)|` and `|ψ(3/2)|`, which sum to `2`,
so `C_Γ = 1 + (log π) / 2 ≈ 1.57236`.

At a real point `s` off the poles, `logDeriv Gammaℝ s = ψ(s/2)/2 - (log π)/2` is real. For
`1 ≤ s ≤ 3` it is negative and lies between its values `ψ(1/2)/2 - (log π)/2 ≈ -1.55412` at
`s = 1` and `ψ(3/2)/2 - (log π)/2 ≈ -0.55412` at `s = 3`, because real digamma is monotone on
the positive axis. Hence `‖logDeriv Gammaℝ s‖ ≤ C_Γ`. The interval `[1, 3]` covers both parity
shifts `σ + κ` with `1 < σ ≤ 2` and `κ ∈ {0, 1}` of the gamma factor of a Dirichlet L-function.

## Main declarations

* `TauCeti.gammaLogDerivBound`, `TauCeti.gammaLogDerivBound_def`: the constant `C_Γ`.
* `TauCeti.gammaLogDerivBound_eq_digamma`, `TauCeti.gammaLogDerivBound_eq`,
  `TauCeti.gammaLogDerivBound_nonneg`: `C_Γ = (ψ(3/2) - ψ(1/2) + log π) / 2 = 1 + (log π) / 2`
  and `0 ≤ C_Γ`.
* `Complex.logDeriv_Gammaℝ_ofReal`: at a real point `s ≠ 0, -2, -4, …`, the logarithmic
  derivative of `Gammaℝ` is the real number `ψ(s/2)/2 - (log π)/2`.
* `Complex.monotoneOn_re_logDeriv_Gammaℝ_ofReal`: its real part is monotone on the positive real
  axis.
* `Complex.re_logDeriv_Gammaℝ_ofReal_mem_Icc`, `Complex.re_logDeriv_Gammaℝ_ofReal_neg`: on
  `[a, b]` with `0 < a` its real part lies between its values at `a` and `b`, and on `(0, 2π)` its
  real part is negative.
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

namespace TauCeti

/-- The constant `C_Γ = (|-γ - 2 log 2| + |2 - γ - 2 log 2| + |log π|) / 2` bounding the
logarithmic derivative of `Gammaℝ` on the real interval `[1, 3]`. The first two absolute values
are `|ψ(1/2)|` and `|ψ(3/2)|`. -/
noncomputable def gammaLogDerivBound : ℝ :=
  (|-eulerMascheroniConstant - 2 * log 2| + |2 - eulerMascheroniConstant - 2 * log 2| +
    |log π|) / 2

/-- The defining formula of `C_Γ`. -/
theorem gammaLogDerivBound_def :
    gammaLogDerivBound = (|-eulerMascheroniConstant - 2 * log 2| +
      |2 - eulerMascheroniConstant - 2 * log 2| + |log π|) / 2 := by
  rw [gammaLogDerivBound]

/-- `C_Γ = (ψ(3/2) - ψ(1/2) + log π) / 2`. -/
theorem gammaLogDerivBound_eq_digamma :
    gammaLogDerivBound = (digamma (3 / 2) - digamma (1 / 2) + log π) / 2 := by
  -- `ψ(1/2) < 0 < ψ(3/2)` and `log π > 0` remove the absolute values.
  rw [gammaLogDerivBound, ← digamma_one_half, ← digamma_three_halves,
    abs_of_neg digamma_one_half_neg, abs_of_pos digamma_three_halves_pos, abs_of_pos log_pi_pos]
  ring

/-- `C_Γ = 1 + (log π) / 2`. -/
theorem gammaLogDerivBound_eq : gammaLogDerivBound = 1 + log π / 2 := by
  -- `ψ(3/2) - ψ(1/2) = 2`.
  rw [gammaLogDerivBound_eq_digamma, digamma_one_half, digamma_three_halves]
  ring

/-- The constant `C_Γ` is nonnegative. -/
theorem gammaLogDerivBound_nonneg : 0 ≤ gammaLogDerivBound := by
  unfold gammaLogDerivBound
  positivity

end TauCeti

namespace Complex

open TauCeti

/-- A positive real number is not a pole `-2n` of `Gammaℝ`. -/
private theorem ne_neg_two_mul_nat_of_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : s ≠ -(2 * n) := by
  have := n.cast_nonneg (α := ℝ)
  linarith

/-- At a real point `s` off the poles `0, -2, -4, …`, the logarithmic derivative of `Gammaℝ` is
the real number `ψ(s/2)/2 - (log π)/2`. -/
theorem logDeriv_Gammaℝ_ofReal {s : ℝ} (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    logDeriv Gammaℝ (s : ℂ) = ((Real.digamma (s / 2) / 2 - Real.log π / 2 : ℝ) : ℂ) := by
  have hpole (n : ℕ) : (s : ℂ) ≠ -(2 * n) := by exact_mod_cast hs n
  simp [logDeriv_Gammaℝ hpole, ← digamma_ofReal]

/-- On the positive real axis, the real part of the logarithmic derivative of `Gammaℝ` is
monotone. -/
theorem monotoneOn_re_logDeriv_Gammaℝ_ofReal :
    MonotoneOn (fun s : ℝ ↦ (logDeriv Gammaℝ (s : ℂ)).re) (Ioi 0) := by
  intro x hx y hy hxy
  simp only [logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos (mem_Ioi.1 hx)),
    logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos (mem_Ioi.1 hy)), ofReal_re]
  -- Real digamma is monotone on the positive axis.
  have := Real.monotoneOn_digamma (half_pos (mem_Ioi.1 hx)) (half_pos (mem_Ioi.1 hy))
    (by linarith)
  linarith

/-- For real `0 < a ≤ s ≤ b`, the real part of the logarithmic derivative of `Gammaℝ` at `s` lies
between its values `ψ(a/2)/2 - (log π)/2` at `a` and `ψ(b/2)/2 - (log π)/2` at `b`. -/
theorem re_logDeriv_Gammaℝ_ofReal_mem_Icc {a b s : ℝ} (ha : 0 < a) (hs : s ∈ Icc a b) :
    (logDeriv Gammaℝ (s : ℂ)).re ∈
      Icc (Real.digamma (a / 2) / 2 - Real.log π / 2)
        (Real.digamma (b / 2) / 2 - Real.log π / 2) := by
  obtain ⟨ha', hb'⟩ := hs
  have hm := monotoneOn_re_logDeriv_Gammaℝ_ofReal
  have hs0 : s ∈ Ioi 0 := mem_Ioi.2 (ha.trans_le ha')
  have hb0 : b ∈ Ioi 0 := mem_Ioi.2 (ha.trans_le (ha'.trans hb'))
  have hlo := hm (mem_Ioi.2 ha) hs0 ha'
  have hhi := hm hs0 hb0 hb'
  simp only [logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos ha),
    logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos (mem_Ioi.1 hb0)), ofReal_re] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- For real `0 < s < 2π`, the real part of the logarithmic derivative of `Gammaℝ` is
negative. -/
theorem re_logDeriv_Gammaℝ_ofReal_neg {s : ℝ} (hs0 : 0 < s) (hs : s < 2 * π) :
    (logDeriv Gammaℝ (s : ℂ)).re < 0 := by
  rw [logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos hs0), ofReal_re]
  -- `ψ(s/2) ≤ log (s/2) < log π`.
  have hψ := (Real.digamma_le_log_le (half_pos hs0)).1
  have hlog : Real.log (s / 2) < Real.log π := Real.log_lt_log (half_pos hs0) (by linarith)
  linarith

/-- For real `1 ≤ s ≤ 3`, the logarithmic derivative of `Gammaℝ` has norm at most `C_Γ`. -/
theorem norm_logDeriv_Gammaℝ_ofReal_le {s : ℝ} (hs : s ∈ Icc 1 3) :
    ‖logDeriv Gammaℝ (s : ℂ)‖ ≤ gammaLogDerivBound := by
  have hs0 : 0 < s := one_pos.trans_le hs.1
  have hmem := re_logDeriv_Gammaℝ_ofReal_mem_Icc one_pos hs
  rw [logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos hs0), ofReal_re] at hmem
  rw [logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos hs0), norm_real, Real.norm_eq_abs,
    gammaLogDerivBound_eq_digamma, abs_le]
  have := Real.digamma_one_half_neg
  have := Real.digamma_three_halves_pos
  have := log_pi_pos
  constructor <;> linarith [hmem.1, hmem.2]

/-- The norm of the logarithmic derivative of `Gammaℝ` at `s = 1`, where the bound `C_Γ` is
nearly attained: `(γ + 2 log 2 + log π) / 2 ≈ 1.55412`. -/
theorem norm_logDeriv_Gammaℝ_one :
    ‖logDeriv Gammaℝ 1‖ = (eulerMascheroniConstant + 2 * Real.log 2 + Real.log π) / 2 := by
  have h := logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos one_pos)
  rw [ofReal_one] at h
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
  have h3 : (0 : ℝ) < 3 := three_pos
  have h := re_logDeriv_Gammaℝ_ofReal_neg h3 (by linarith [two_le_pi])
  rw [logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos h3), ofReal_re] at h
  have h' := logDeriv_Gammaℝ_ofReal (ne_neg_two_mul_nat_of_pos h3)
  rw [ofReal_ofNat] at h'
  rw [h', norm_real, Real.norm_eq_abs, abs_of_neg h]
  ring

end Complex
