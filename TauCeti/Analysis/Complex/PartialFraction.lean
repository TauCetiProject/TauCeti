/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Locally uniform convergence of paired partial-fraction series

A partial-fraction series whose poles come in pairs `± a i` can be summed pairwise. The paired
term `1 / (z - a) + 1 / (z + a) = 2 z / (z² - a²)` is `O(|a|⁻²)` uniformly for `z` in a bounded
set (`TauCeti.norm_one_div_sub_add_one_div_add_le`). So for any family of poles `a i` that are
nonzero for all but finitely many `i` and satisfy `∑ |a i|⁻² < ∞`, the paired series converges
locally uniformly on all of `ℂ`, the terms at the poles taking their totalized values
(`TauCeti.hasSumLocallyUniformly_one_div_sub_add_one_div_add`). The pairing is essential: for the
poles `a n = n + 1` the one-sided series `∑ 1 / (z - a n)` diverges.

## Main results

* `TauCeti.norm_one_div_sub_add_one_div_add_le`: the bound `4 R / |a|²` on the paired term.
* `TauCeti.hasSumLocallyUniformly_one_div_sub_add_one_div_add`: locally uniform convergence of
  paired series with cofinitely nonzero, inverse-square summable poles.
-/

public section

open Filter

namespace TauCeti

/-- The paired term `1 / (z - a) + 1 / (z + a)` is bounded by `4 R / ‖a‖²` when `‖z‖ ≤ R` and
`2 R ≤ ‖a‖`. -/
theorem norm_one_div_sub_add_one_div_add_le {z a : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R)
    (ha : 2 * R ≤ ‖a‖) : ‖1 / (z - a) + 1 / (z + a)‖ ≤ 4 * R / ‖a‖ ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  rcases eq_or_ne a 0 with rfl | ha₀
  · obtain rfl : z = 0 := norm_le_zero_iff.mp (hz.trans (by rw [norm_zero] at ha; linarith))
    simp
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha₀
  have hza : ‖z‖ < ‖a‖ := by linarith
  have h₁ : z - a ≠ 0 := fun h ↦ hza.ne (by rw [sub_eq_zero.mp h])
  have h₂ : z + a ≠ 0 := fun h ↦ hza.ne (by rw [eq_neg_of_add_eq_zero_left h, norm_neg])
  have heq : 1 / (z - a) + 1 / (z + a) = 2 * z / ((z - a) * (z + a)) := by
    field_simp
    ring
  have hlow : 3 / 4 * ‖a‖ ^ 2 ≤ ‖(z - a) * (z + a)‖ := by
    have h := norm_sub_norm_le (a ^ 2) (z ^ 2)
    rw [norm_pow, norm_pow, norm_sub_rev, show z ^ 2 - a ^ 2 = (z - a) * (z + a) by ring] at h
    nlinarith [mul_self_le_mul_self (norm_nonneg z) (hz.trans (by linarith : R ≤ ‖a‖ / 2))]
  rw [heq, norm_div, norm_mul, RCLike.norm_ofNat,
    div_le_div_iff₀ (norm_pos_iff.mpr (mul_ne_zero h₁ h₂)) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hlow (by linarith : (0 : ℝ) ≤ 4 * R),
    mul_le_mul_of_nonneg_right hz (sq_nonneg ‖a‖)]

/-- **Locally uniform convergence of paired partial-fraction series.** If the poles `a i` are
nonzero for all but finitely many `i` and `∑ ‖a i‖⁻² < ∞`, then
`∑ (1 / (z - a i) + 1 / (z + a i))` converges locally uniformly on `ℂ`, the terms at the poles
taking their totalized values. -/
theorem hasSumLocallyUniformly_one_div_sub_add_one_div_add {ι : Type*} {a : ι → ℂ}
    (ha : ∀ᶠ i in cofinite, a i ≠ 0) (hs : Summable fun i ↦ (‖a i‖ ^ 2)⁻¹) :
    HasSumLocallyUniformly (fun i z ↦ 1 / (z - a i) + 1 / (z + a i))
      (fun z ↦ ∑' i, (1 / (z - a i) + 1 / (z + a i))) := by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR₀, hR⟩ := hK.isBounded.exists_pos_norm_le
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually (hs.mul_left (4 * R)) ?_
  filter_upwards [ha, hs.tendsto_cofinite_zero.eventually
    (ge_mem_nhds (by positivity : (0 : ℝ) < ((2 * R) ^ 2)⁻¹))] with i hi₀ hi z hz
  have hi' : 2 * R ≤ ‖a i‖ := by
    rwa [inv_le_inv₀ (pow_pos (norm_pos_iff.mpr hi₀) 2) (by positivity),
      sq_le_sq₀ (by positivity) (norm_nonneg _)] at hi
  simpa only [div_eq_mul_inv] using norm_one_div_sub_add_one_div_add_le (hR z hz) hi'

end TauCeti
