/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import TauCeti.Analysis.Complex.Taylor.CauchyEstimate
import TauCeti.Analysis.Complex.Taylor.Laurent
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.SpecificLimits.Window

/-!
# Comparing window bounds with isolated poles of finite order

In the windowed Landau argument the same Taylor degree controls both a coefficient at a shifted
centre and the real part of a reflected coefficient at the real centre. An isolated pole in the
shifted disc cannot be hidden by the holomorphic contribution from the real disc. When the pole
is real, a leading Laurent coefficient of positive real part instead forces the reflected real
part itself to grow too fast.

The window estimate at radius `R` is `C * exp (η * U) / R ^ k`, at an index `k ≥ U` for arbitrarily
large `U` and every positive loss rate `η`.

These extend the two comparisons of Levent Alpöge's windowed Landau argument for simple poles
(`Deduction.landau_window`, <https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Filter Metric TauCeti
open scoped Nat

namespace DifferentiableOn

/-- If a disc about `z` isolates a pole at `ρ` and a disc about `w` of radius greater than
`‖z - ρ‖` is holomorphic, a window bound on the sum of the coefficient norm at `z` and the
reflected coefficient's real part at `w` can only hold with `R ≤ ‖z - ρ‖`. -/
theorem le_norm_sub_of_window_taylor_bound_of_pole {F : ℂ → ℂ} {z w ρ : ℂ}
    {rz rw R : ℝ} (hz : DifferentiableOn ℂ F (ball z rz \ {ρ}))
    (hw : DifferentiableOn ℂ F (ball w rw)) (hd : ‖z - ρ‖ < min rz rw) (hzρ : z ≠ ρ)
    (hp : meromorphicOrderAt F ρ < 0)
    (hupper : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ U₀ : ℝ, ∃ U ≥ U₀, ∃ k : ℕ,
      U ≤ (k : ℝ) ∧
        ‖iteratedDeriv k F z / (k ! : ℂ)‖ + ((-1) ^ k * (iteratedDeriv k F w / (k ! : ℂ))).re ≤
          C * Real.exp (η * U) / R ^ k) :
    R ≤ ‖z - ρ‖ := by
  obtain ⟨m, hp⟩ := exists_meromorphicOrderAt_eq_neg_succ_of_lt_zero hp
  obtain ⟨hdz, hdw⟩ := lt_min_iff.1 hd
  let d := ‖z - ρ‖
  have hd₀ : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hzρ)
  obtain ⟨r, hdr, hrw⟩ := exists_between hdw
  obtain ⟨M, hM⟩ := hw.exists_norm_iteratedDeriv_div_factorial_le (hd₀.trans hdr) hrw
  have hp' : meromorphicOrderAt F ρ ≠ 0 := by
    have hm : (-(↑(m + 1) : ℤ)) ≠ 0 := by omega
    rw [hp]
    exact_mod_cast hm
  have hm := meromorphicAt_of_meromorphicOrderAt_ne_zero hp'
  have hc : 0 < ‖meromorphicTrailingCoeffAt F ρ‖ :=
    norm_pos_iff.2 (hm.meromorphicTrailingCoeffAt_ne_zero (hp ▸ WithTop.coe_ne_top))
  -- Absorb the fixed order factor `d ^ m` into the lower-bound constant, and reserve half
  -- the resulting bound for the real-centred coefficient.
  let a := ‖meromorphicTrailingCoeffAt F ρ‖ / 4 / d ^ m
  have ha : 0 < a := div_pos (by positivity) (pow_pos hd₀ _)
  refine le_of_window_exp_div_pow_bound ha hd₀ ?_ hupper
  filter_upwards [Complex.eventually_le_norm_iteratedDeriv_div_factorial_of_pole hz hp hdz,
    eventually_div_pow_le_div_pow M ha hd₀ hdr] with k hk hsmall
  have hbase : -(M / r ^ k) ≤ ((-1) ^ k * (iteratedDeriv k F w / (k ! : ℂ))).re := by
    refine (neg_le_neg ?_).trans (abs_le.mp (Complex.abs_re_le_norm _)).1
    simpa [norm_mul, norm_div] using hM k
  have hscale : 2 * (a / d ^ (k + 1)) = ‖meromorphicTrailingCoeffAt F ρ‖ / 2 / d ^ (k + m + 1) := by
    simp only [a, pow_add, pow_one, div_div, mul_assoc, mul_left_comm, mul_comm]
    ring
  linarith only [hscale, hk, hsmall, hbase]

/-- An isolated real pole to the left of its Taylor centre, at distance less than the radius in
the window bound, cannot have a leading Laurent coefficient of positive real part. The real
parts of the reflected coefficients suffice; no reality assumption is needed. -/
theorem meromorphicTrailingCoeffAt_re_nonpos_of_window_taylor_bound {F : ℂ → ℂ}
    {x β r R : ℝ} (hF : DifferentiableOn ℂ F (ball (x : ℂ) r \ {(β : ℂ)}))
    (hβ : β < x) (hd : x - β < min r R)
    (hp : meromorphicOrderAt F (β : ℂ) < 0)
    (hupper : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ U₀ : ℝ, ∃ U ≥ U₀, ∃ k : ℕ,
      U ≤ (k : ℝ) ∧
        ((-1) ^ k * (iteratedDeriv k F x / (k ! : ℂ))).re ≤ C * Real.exp (η * U) / R ^ k) :
    (meromorphicTrailingCoeffAt F β).re ≤ 0 := by
  obtain ⟨m, hp⟩ := exists_meromorphicOrderAt_eq_neg_succ_of_lt_zero hp
  by_contra! hc
  obtain ⟨hdr, hdR⟩ := lt_min_iff.1 hd
  have hd₀ := sub_pos.mpr hβ
  have ha : 0 < (meromorphicTrailingCoeffAt F β).re / 2 / (x - β) ^ m := by positivity
  refine hdR.not_ge (le_of_window_exp_div_pow_bound ha hd₀ ?_ hupper)
  filter_upwards [Complex.eventually_le_re_neg_one_pow_mul_iteratedDeriv_div_factorial_of_pole
    hF hp hc hβ hdr] with k hk
  have hscale : (meromorphicTrailingCoeffAt F β).re / 2 / (x - β) ^ m / (x - β) ^ (k + 1) =
      (meromorphicTrailingCoeffAt F β).re / 2 / (x - β) ^ (k + m + 1) := by
    simp only [pow_add, pow_one, div_div, mul_assoc, mul_left_comm, mul_comm]
  exact hscale.trans_le hk

end DifferentiableOn
