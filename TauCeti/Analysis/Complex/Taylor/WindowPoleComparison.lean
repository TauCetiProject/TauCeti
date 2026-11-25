/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Complex.Taylor.CauchyEstimate
import TauCeti.Analysis.Complex.Taylor.CoeffSimplePole
import TauCeti.Analysis.Contour.Residue.RegularPart
import TauCeti.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.SpecificLimits.Window

/-!
# Comparing window bounds with isolated simple poles

In the windowed Landau argument the same Taylor degree controls both a coefficient at a shifted
centre and the real part of a reflected coefficient at the real centre. An isolated pole in the
shifted disc cannot be hidden by the holomorphic contribution from the real disc. When the pole
is real, a positive residue instead forces the reflected real part itself to grow too fast.

The window estimate at radius `R` is `C * exp (η * U) / R ^ k`, at an index `k ≥ U` for arbitrarily
large `U` and every positive loss rate `η`.

These are the two pole comparisons in Levent Alpöge's windowed Landau argument for simple poles
(`Deduction.landau_window`, <https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Filter Metric TauCeti
open scoped Nat

namespace DifferentiableOn

/-- If a disc about `z` isolates a simple pole at `ρ` and a disc about `w` of radius greater than
`‖z - ρ‖` is holomorphic, a window bound on the sum of the coefficient norm at `z` and the
reflected coefficient's real part at `w` can only hold with `R ≤ ‖z - ρ‖`. -/
theorem le_norm_sub_of_window_taylor_bound_of_simple_pole {F : ℂ → ℂ} {z w ρ : ℂ}
    {rz rw R : ℝ} (hz : DifferentiableOn ℂ F (ball z rz \ {ρ}))
    (hw : DifferentiableOn ℂ F (ball w rw)) (hd : ‖z - ρ‖ < min rz rw) (hzρ : z ≠ ρ)
    (hp : meromorphicOrderAt F ρ = -1)
    (hupper : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ U₀ : ℝ, ∃ U ≥ U₀, ∃ k : ℕ,
      U ≤ (k : ℝ) ∧
        ‖iteratedDeriv k F z / (k ! : ℂ)‖ + ((-1) ^ k * (iteratedDeriv k F w / (k ! : ℂ))).re ≤
          C * Real.exp (η * U) / R ^ k) :
    R ≤ ‖z - ρ‖ := by
  obtain ⟨hdz, hdw⟩ := lt_min_iff.1 hd
  have hd₀ : 0 < ‖z - ρ‖ := norm_pos_iff.2 (sub_ne_zero.2 hzρ)
  obtain ⟨r, hdr, hrw⟩ := exists_between hdw
  obtain ⟨M, hM⟩ := hw.exists_norm_iteratedDeriv_div_factorial_le (hd₀.trans hdr) hrw
  have hm : MeromorphicAt F ρ := meromorphicAt_of_meromorphicOrderAt_ne_zero (by simp [hp])
  obtain ⟨h, hh, heq⟩ := hm.exists_analyticAt_eventuallyEq_inv_smul_residue_add hp.ge
  simp only [smul_eq_mul, inv_mul_eq_div] at heq
  have hc : 0 < ‖Contour.residue F ρ‖ := by
    rw [Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one hp, norm_pos_iff]
    exact hm.meromorphicTrailingCoeffAt_ne_zero (by simp [hp])
  refine le_of_window_exp_div_pow_bound (half_pos (half_pos hc)) hd₀ ?_ hupper
  have hlower := Complex.eventually_le_norm_iteratedDeriv_div_factorial_of_simple_pole hz hh heq hdz
  filter_upwards [hlower, eventually_div_pow_le_div_pow M (half_pos (half_pos hc)) hd₀ hdr]
    with k hk hsmall
  have hbase : - (M / r ^ k) ≤ ((-1) ^ k * (iteratedDeriv k F w / (k ! : ℂ))).re := by
    refine (neg_le_neg ?_).trans (abs_le.mp (Complex.abs_re_le_norm _)).1
    simpa [norm_mul, norm_div] using hM k
  have hdouble : 2 * (‖Contour.residue F ρ‖ / 2 / 2 / ‖z - ρ‖ ^ (k + 1)) =
      ‖Contour.residue F ρ‖ / 2 / ‖z - ρ‖ ^ (k + 1) := by ring
  rw [← hdouble] at hk
  linarith only [hk, hsmall, hbase]

/-- An at-most-simple pole to the left of its Taylor centre, at distance less than the radius in
the window bound, cannot have positive real residue. The real-centred coefficient need not be
real: only the real part of the reflected coefficient is bounded. -/
theorem residue_re_nonpos_of_window_taylor_bound {F : ℂ → ℂ}
    {x β r R : ℝ} (hF : DifferentiableOn ℂ F (ball (x : ℂ) r \ {(β : ℂ)}))
    (hβ : β < x) (hd : x - β < min r R) (hp : -1 ≤ meromorphicOrderAt F (β : ℂ))
    (hupper : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ U₀ : ℝ, ∃ U ≥ U₀, ∃ k : ℕ,
      U ≤ (k : ℝ) ∧
        ((-1) ^ k * (iteratedDeriv k F x / (k ! : ℂ))).re ≤ C * Real.exp (η * U) / R ^ k) :
    (Contour.residue F β).re ≤ 0 := by
  by_contra! hc
  obtain ⟨hdr, hdR⟩ := lt_min_iff.1 hd
  have hnegative : meromorphicOrderAt F (β : ℂ) < 0 := by
    by_contra! hnonneg
    simp [Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg hnonneg] at hc
  have hm := meromorphicAt_of_meromorphicOrderAt_ne_zero hnegative.ne
  obtain ⟨h, hh, heq⟩ := hm.exists_analyticAt_eventuallyEq_inv_smul_residue_add hp
  simp only [smul_eq_mul, inv_mul_eq_div] at heq
  exact hdR.not_ge (le_of_window_exp_div_pow_bound (half_pos hc) (sub_pos.2 hβ)
    (Complex.eventually_le_re_neg_one_pow_mul_iteratedDeriv_div_factorial_of_simple_pole
      hF hh heq hc hβ hdr) hupper)

end DifferentiableOn
