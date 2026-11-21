/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-!
# A uniform strict power mean inequality

For `1 ≤ q` and nonnegative `s`, `t`, the power mean inequality
`(s + t) ^ q ≤ 2 ^ (q - 1) * (s ^ q + t ^ q)` is `NNReal.rpow_add_le_mul_rpow_add_rpow`. For
`1 < q` it is strict for every `0 ≤ u ≤ s + t` with `u < 2 * s`: if `s ≠ t`, by strict convexity
of `t ↦ t ^ q`, and if `s = t`, because `u < 2 * s = s + t`.

The improvement is uniform once `u` is bounded away from `2 * s`: for each `0 < δ` there is
`κ > 0` with `u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q)` whenever `0 ≤ t ≤ s`,
`0 ≤ u ≤ s + t` and `u ≤ (2 - δ) * s`. For `s > 0`, the strict inequality at
`u = min (s + t) ((2 - δ) * s)` comes from strict convexity when `t / s < 1`, and from the cutoff
`u ≤ (2 - δ) * s` when `t / s = 1`; compactness of `[0, 1]` makes it uniform in the ratio
`t / s`. This is the scalar step in showing that `q`-th powers of norms on a uniformly convex
space are uniformly convex.

## Main results

* `Real.rpow_lt_of_le_add_of_lt_two_mul`: `u ^ q < 2 ^ (q - 1) * (s ^ q + t ^ q)` for `1 < q`,
  `0 ≤ t`, `0 ≤ u ≤ s + t` and `u < 2 * s`.
* `Real.exists_rpow_le_of_le_add_of_le_two_sub_mul`: for `1 < q` and `0 < δ` there is `κ > 0`
  with `u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q)` whenever `0 ≤ t ≤ s`, `0 ≤ u ≤ s + t`
  and `u ≤ (2 - δ) * s`.
-/

public section

namespace Real

/-- **A strict power mean inequality.** For `1 < q`, `0 ≤ t` and `0 ≤ u ≤ s + t` with
`u < 2 * s`, `u ^ q < 2 ^ (q - 1) * (s ^ q + t ^ q)`. -/
theorem rpow_lt_of_le_add_of_lt_two_mul {q s t u : ℝ} (hq : 1 < q) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hus : u ≤ s + t) (hu2 : u < 2 * s) : u ^ q < 2 ^ (q - 1) * (s ^ q + t ^ q) := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < s := by linarith
  have h2sub : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := rpow_sub_one two_ne_zero q
  rcases eq_or_ne s t with rfl | hst
  · calc u ^ q < (2 * s) ^ q := rpow_lt_rpow hu hu2 hq0
      _ = 2 ^ (q - 1) * (s ^ q + s ^ q) := by rw [mul_rpow zero_le_two hs.le, h2sub]; ring
  have hstrict := (strictConvexOn_rpow hq).2 (Set.mem_Ici.2 hs.le) (Set.mem_Ici.2 ht) hst
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hstrict
  have hhalf : (s + t) ^ q = 2 ^ q * (1 / 2 * s + 1 / 2 * t) ^ q := by
    rw [← mul_rpow zero_le_two (by positivity)]
    ring_nf
  have := mul_lt_mul_of_pos_left hstrict (by positivity : (0 : ℝ) < 2 ^ q)
  calc u ^ q ≤ (s + t) ^ q := rpow_le_rpow hu hus hq0.le
    _ < 2 ^ (q - 1) * (s ^ q + t ^ q) := by
      rw [hhalf, h2sub]
      linarith

/-- **A uniform strict power mean inequality.** For `1 < q` and `0 < δ` there is `κ > 0`
such that `u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q)` whenever
`0 ≤ t ≤ s` and `0 ≤ u ≤ min (s + t) ((2 - δ) * s)`. This is the scalar part of
`TauCeti.exists_forall_norm_add_rpow_le`. -/
theorem exists_rpow_le_of_le_add_of_le_two_sub_mul {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) :
    ∃ κ, 0 < κ ∧ ∀ s t u : ℝ, 0 ≤ t → t ≤ s → 0 ≤ u → u ≤ s + t → u ≤ (2 - δ) * s →
      u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
  -- For `δ > 1` the bound `u ≤ (2 - δ) * s` implies the case `δ = 1`.
  wlog hδ1 : δ ≤ 1 generalizing δ
  · obtain ⟨κ, hκ, h⟩ := this one_pos le_rfl
    refine ⟨κ, hκ, fun s t u ht hts hu hus hu2 ↦ h s t u ht hts hu hus ?_⟩
    nlinarith [ht.trans hts, not_le.1 hδ1]
  have hq0 : 0 < q := by linarith
  have h2sub : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := rpow_sub_one two_ne_zero q
  -- The gap between the two sides after rescaling to `s = 1`.
  set φ : ℝ → ℝ := fun r ↦ 2 ^ (q - 1) * (1 + r ^ q) - min (1 + r) (2 - δ) ^ q with hφ
  have hφc : Continuous φ := by
    have := continuous_rpow_const hq0.le
    fun_prop
  obtain ⟨r₀, hr₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) hφc.continuousOn
  have hm : 0 < φ r₀ := by
    have h := rpow_lt_of_le_add_of_lt_two_mul (s := 1) (u := min (1 + r₀) (2 - δ)) hq hr₀.1
      (le_min (by linarith [hr₀.1]) (by linarith)) (min_le_left _ _)
      ((min_le_right _ _).trans_lt (by linarith))
    rw [one_rpow] at h
    simpa only [hφ] using sub_pos.2 h
  refine ⟨φ r₀ / 2 ^ q, by positivity, fun s t u ht hts hu hus hu2 ↦ ?_⟩
  rcases (ht.trans hts).eq_or_lt with rfl | hs
  · obtain rfl : t = 0 := le_antisymm hts ht
    obtain rfl : u = 0 := le_antisymm (by simpa using hus) hu
    simp [zero_rpow hq0.ne']
  set r := t / s with hr_def
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg ht hs.le, div_le_one_of_le₀ hts hs.le⟩
  have hv : u / s ≤ min (1 + r) (2 - δ) := by
    refine le_min ?_ ?_ <;> rw [div_le_iff₀ hs]
    · rw [hr_def, add_mul, div_mul_cancel₀ _ hs.ne', one_mul]
      exact hus
    · linarith
  have hrq : r ^ q ≤ 1 := rpow_le_one hr.1 hr.2 hq0.le
  have hgap : φ r₀ ≤ φ r := hmin hr
  have hvq : (u / s) ^ q ≤ min (1 + r) (2 - δ) ^ q :=
    rpow_le_rpow (div_nonneg hu hs.le) hv hq0.le
  have key : (u / s) ^ q ≤ (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q) := by
    simp only [hφ] at hgap
    have hrq0 : 0 ≤ r ^ q := rpow_nonneg hr.1 q
    have : (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q) =
        2 ^ (q - 1) * (1 + r ^ q) - φ r₀ * ((1 + r ^ q) / 2) := by
      rw [h2sub]
      field_simp
    rw [this]
    nlinarith
  have hsq : 0 < s ^ q := rpow_pos_of_pos hs q
  calc u ^ q = s ^ q * (u / s) ^ q := by
        rw [div_rpow hu hs.le, mul_div_cancel₀ _ hsq.ne']
    _ ≤ s ^ q * ((1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q)) := by gcongr
    _ = (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
        rw [hr_def, div_rpow ht hs.le]
        field_simp

end Real
