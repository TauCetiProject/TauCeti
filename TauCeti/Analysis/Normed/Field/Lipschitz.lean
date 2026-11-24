/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import TauCeti.Algebra.Field.LinearFractional

/-!
# The reciprocal of a Lipschitz function and local Möbius bounds

If `f` takes values in a normed division ring, is `K`-Lipschitz on a set `s` and stays at norm at
least `m > 0` there, then `x ↦ (f x)⁻¹` is `K / m²`-Lipschitz on `s`, because
`dist a⁻¹ b⁻¹ = dist a b / (‖a‖ ‖b‖)` (`dist_inv_inv₀`). This is how a coefficient bounded below,
such as the normal component of a uniformly elliptic coefficient field, is divided out while
keeping Lipschitz control.

The map `y ↦ c ^ 2 / y` is `1`-Lipschitz on `{y | ‖c‖ ≤ ‖y‖}` in any normed division ring
(`TauCeti.norm_sq_div_sub_sq_div_le`). Similarly, a linear fractional transformation
`t ↦ (a * t + b) / (c * t + d)` over a normed field keeps denominator norm at least
`‖c * w + d‖ / 2` and distorts distances from `w` by at most `2 * ‖a * d - b * c‖ / ‖c * w + d‖ ^ 2`
on `{t | ‖c‖ * ‖t - w‖ ≤ ‖c * w + d‖ / 2}` (`TauCeti.div_two_le_norm_mul_add`,
`TauCeti.norm_moebius_sub_moebius_le`).

## Main results

* `LipschitzOnWith.inv_of_le_norm`: the reciprocal of a function Lipschitz on `s` and bounded away
  from zero there is Lipschitz on `s`.
* `TauCeti.norm_sq_div_sub_sq_div_le`: `y ↦ c ^ 2 / y` is `1`-Lipschitz on `{y | ‖c‖ ≤ ‖y‖}`.
* `TauCeti.div_two_le_norm_mul_add`: if `‖c * (t - w)‖ ≤ ‖c * w + d‖ / 2`, then
  `‖c * w + d‖ / 2 ≤ ‖c * t + d‖`.
* `TauCeti.norm_moebius_sub_moebius_le`: local distance bound for `(a * t + b) / (c * t + d)` near
  a base point `w` when `‖c‖ * ‖t - w‖ ≤ ‖c * w + d‖ / 2`.
-/

public section

open scoped NNReal

namespace LipschitzOnWith

variable {α 𝕜 : Type*} [PseudoMetricSpace α] [NormedDivisionRing 𝕜]

/-- The reciprocal of a `K`-Lipschitz function on `s` whose norm is at least `m > 0` on `s` is
`K / m²`-Lipschitz on `s`. -/
theorem inv_of_le_norm {f : α → 𝕜} {s : Set α} {K m : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hm : 0 < m) (hfm : ∀ x ∈ s, (m : ℝ) ≤ ‖f x‖) :
    LipschitzOnWith (K / m ^ 2) (fun x => (f x)⁻¹) s :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    have hx' : (0 : ℝ) < ‖f x‖ := (NNReal.coe_pos.2 hm).trans_le (hfm x hx)
    have hy' : (0 : ℝ) < ‖f y‖ := (NNReal.coe_pos.2 hm).trans_le (hfm y hy)
    rw [dist_inv_inv₀ (norm_pos_iff.1 hx') (norm_pos_iff.1 hy'),
      div_le_iff₀ (mul_pos hx' hy')]
    calc dist (f x) (f y) ≤ K * dist x y := hf.dist_le_mul x hx y hy
      _ = K / m ^ 2 * dist x y * (m * m) := by
          field_simp [(NNReal.coe_pos.2 hm).ne']
      _ ≤ (K / m ^ 2 : ℝ≥0) * dist x y * (‖f x‖ * ‖f y‖) := by
          push_cast
          gcongr
          exacts [hfm x hx, hfm y hy]

end LipschitzOnWith

namespace TauCeti

/-- In a normed division ring, `y ↦ c ^ 2 / y` is `1`-Lipschitz on the points whose norm is at
least `‖c‖`. -/
theorem norm_sq_div_sub_sq_div_le {𝕜 : Type*} [NormedDivisionRing 𝕜] {c x y : 𝕜}
    (hx : ‖c‖ ≤ ‖x‖) (hy : ‖c‖ ≤ ‖y‖) :
    ‖c ^ 2 / x - c ^ 2 / y‖ ≤ ‖x - y‖ := by
  rcases eq_or_ne x 0 with rfl | hxn
  · simp [norm_le_zero_iff.mp (by simpa using hx : ‖c‖ ≤ 0)]
  rcases eq_or_ne y 0 with rfl | hyn
  · simp [norm_le_zero_iff.mp (by simpa using hy : ‖c‖ ≤ 0)]
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hxn
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hyn
  simp_rw [div_eq_mul_inv]
  rw [← mul_sub, norm_mul, ← dist_eq_norm, dist_inv_inv₀ hxn hyn, dist_eq_norm, norm_pow]
  have hb : ‖c‖ ^ 2 ≤ ‖x‖ * ‖y‖ := by nlinarith [norm_nonneg c]
  calc ‖c‖ ^ 2 * (‖x - y‖ / (‖x‖ * ‖y‖)) ≤ (‖x‖ * ‖y‖) * (‖x - y‖ / (‖x‖ * ‖y‖)) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = ‖x - y‖ := mul_div_cancel₀ _ (mul_pos hx0 hy0).ne'

/-- In a seminormed ring, if `c * (t - w)` has norm at most half that of `c * w + d`, then
`c * t + d` has norm at least `‖c * w + d‖ / 2`. -/
theorem div_two_le_norm_mul_add {R : Type*} [SeminormedRing R] {c d w t : R}
    (h : ‖c * (t - w)‖ ≤ ‖c * w + d‖ / 2) :
    ‖c * w + d‖ / 2 ≤ ‖c * t + d‖ := by
  have hsub : (c * w + d) - c * (w - t) = c * t + d := by
    rw [mul_sub, sub_sub_eq_add_sub, add_right_comm (c * w) d (c * t), add_assoc,
      add_sub_cancel_left]
  have htri := norm_sub_norm_le (c * w + d) (c * (w - t))
  rw [hsub, ← neg_sub t w, mul_neg, norm_neg] at htri
  linarith

/-- **Local distance bound for a linear fractional transformation.** Over a normed field, whenever
`‖c‖ * ‖t - w‖ ≤ ‖c * w + d‖ / 2`,
`‖(a * t + b) / (c * t + d) - (a * w + b) / (c * w + d)‖ ≤
2 * ‖a * d - b * c‖ / ‖c * w + d‖ ^ 2 * ‖t - w‖`. -/
theorem norm_moebius_sub_moebius_le {𝕜 : Type*} [NormedField 𝕜] {a b c d w t : 𝕜}
    (h : ‖c‖ * ‖t - w‖ ≤ ‖c * w + d‖ / 2) :
    ‖(a * t + b) / (c * t + d) - (a * w + b) / (c * w + d)‖ ≤
      2 * ‖a * d - b * c‖ / ‖c * w + d‖ ^ 2 * ‖t - w‖ := by
  by_cases hw : c * w + d = 0
  · rw [hw, norm_zero, zero_div] at h
    rcases mul_eq_zero.mp (le_antisymm h (by positivity)) with hc | htw
    · have hc0 : c = 0 := norm_eq_zero.mp hc
      have hd0 : d = 0 := by simpa [hc0] using hw
      simp [hc0, hd0]
    · simp [sub_eq_zero.mp (norm_eq_zero.mp htw)]
  · have hden : ‖c * w + d‖ / 2 ≤ ‖c * t + d‖ := div_two_le_norm_mul_add (by rwa [norm_mul])
    have hw_pos : 0 < ‖c * w + d‖ := norm_pos_iff.mpr hw
    have ht : c * t + d ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (half_pos hw_pos) hden)
    rw [moebius_sub_moebius hw ht, norm_div, norm_mul, norm_mul]
    calc ‖a * d - b * c‖ * ‖t - w‖ / (‖c * t + d‖ * ‖c * w + d‖)
        ≤ ‖a * d - b * c‖ * ‖t - w‖ / (‖c * w + d‖ / 2 * ‖c * w + d‖) := by gcongr
      _ = 2 * ‖a * d - b * c‖ / ‖c * w + d‖ ^ 2 * ‖t - w‖ := by ring

end TauCeti
