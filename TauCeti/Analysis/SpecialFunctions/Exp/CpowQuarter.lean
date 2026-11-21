/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Exponential
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# Decay of `exp(-c z^{1/4})` at infinity

For `c > 0` and the principal fourth root `z^{1/4}`, the real part of `c z^{1/4}` is at least
`c |z|^{1/4} / 2` on the whole plane, so `exp(-c z^{1/4})` decays faster than every power of
`z⁻¹` along `cobounded ℂ`. The function is holomorphic off the negative real axis, where the
principal power is.

## Main results

* `TauCeti.norm_cexp_neg_mul_cpow_quarter_le`: `‖exp(-c z^{1/4})‖ ≤ (4N)! (2/c)^{4N} |z|⁻ᴺ`.
* `TauCeti.isBigO_cexp_neg_mul_cpow_quarter`: `exp(-c z^{1/4}) = O(z⁻ᴺ)` at infinity.
* `TauCeti.differentiableOn_cexp_neg_mul_cpow_quarter`: holomorphy on the slit plane.

The estimates are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean`.
-/

public section

open Complex Filter Bornology

namespace TauCeti

/-- For `c > 0`, `‖exp(-c z^{1/4})‖ ≤ (4N)! (2/c)^{4N} |z|⁻ᴺ`. -/
theorem norm_cexp_neg_mul_cpow_quarter_le {c : ℝ} (hc : 0 < c) (N : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖cexp (-(c * z ^ (1 / 4 : ℂ)))‖ ≤ (4 * N).factorial * (2 / c) ^ (4 * N) * (‖z‖ ^ N)⁻¹ := by
  have ht : 0 < ‖z‖ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.2 hz) _
  set t := ‖z‖ ^ (1 / 4 : ℝ) with ht_def
  have h4 : t ^ (4 * N) = ‖z‖ ^ N := by
    rw [pow_mul, ht_def, ← Real.rpow_mul_natCast (norm_nonneg z)]
    norm_num
  have hre := norm_rpow_le_two_mul_re_cpow_quarter (z := z)
  have hexp := Real.pow_div_factorial_le_exp (c / 2 * t) (by positivity) (4 * N)
  rw [Complex.norm_exp, neg_re, re_ofReal_mul]
  calc Real.exp (-(c * (z ^ (1 / 4 : ℂ)).re)) ≤ Real.exp (-(c / 2 * t)) :=
        Real.exp_le_exp.2 (by nlinarith)
    _ = (Real.exp (c / 2 * t))⁻¹ := Real.exp_neg _
    _ ≤ ((c / 2 * t) ^ (4 * N) / (4 * N).factorial)⁻¹ := inv_anti₀ (by positivity) hexp
    _ = _ := by rw [← h4]; field_simp; rw [← mul_pow]; congr 1; field_simp

/-- For `c > 0`, `exp(-c z^{1/4}) = O(z⁻ᴺ)` at infinity for every `N`. -/
theorem isBigO_cexp_neg_mul_cpow_quarter {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (fun z : ℂ => cexp (-(c * z ^ (1 / 4 : ℂ)))) =O[cobounded ℂ] fun z => (z ^ N)⁻¹ := by
  refine Asymptotics.IsBigO.of_bound ((4 * N).factorial * (2 / c) ^ (4 * N)) ?_
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z hz
  rw [norm_inv, norm_pow]
  exact norm_cexp_neg_mul_cpow_quarter_le hc N (norm_pos_iff.1 hz)

/-- `exp(-c z^{1/4})` is holomorphic off the negative real axis. -/
theorem differentiableOn_cexp_neg_mul_cpow_quarter {c : ℂ} :
    DifferentiableOn ℂ (fun z => cexp (-(c * z ^ (1 / 4 : ℂ)))) slitPlane := fun _ hz =>
  ((differentiableAt_id.cpow_const hz).const_mul c).neg.cexp.differentiableWithinAt

end TauCeti
