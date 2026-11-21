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
import TauCeti.Topology.ContinuousOn.CompactDomination

/-!
# A uniform strict power mean inequality

For `1 ≤ q` and nonnegative `s`, `t`, the power mean inequality
`(s + t) ^ q ≤ 2 ^ (q - 1) * (s ^ q + t ^ q)` is `NNReal.rpow_add_le_mul_rpow_add_rpow`. For
`1 < q` it is strict at every `0 ≤ u ≤ s + t` unless `s = t` and `u = s + t`: if `s ≠ t`, by strict
convexity of `t ↦ t ^ q`, and if `u < s + t`, because `t ↦ t ^ q` is strictly increasing.

The improvement is uniform once `u` is bounded away from `2 * s`: for each `0 < δ` there is
`κ > 0` with `u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q)` whenever `0 ≤ s`, `0 ≤ t`,
`0 ≤ u ≤ s + t` and `u ≤ (2 - δ) * s`. Since `(2 - δ) * s ≤ s` for `δ ≥ 1`, it is enough to treat
`0 < δ ≤ 1`, and by symmetry `t ≤ s`. Rescaling to `s = 1`, the strict inequality holds at
`u = min (1 + r) (2 - δ)` for every ratio `r = t / s ∈ [0, 1]`: by strict convexity when `r < 1`,
and because `2 - δ < 2` when `r = 1`. Compactness of `[0, 1]` makes the gap a uniform fraction of
the right-hand side. This is the scalar step in showing that `q`-th powers of norms on a uniformly
convex space are uniformly convex.

## Main results

* `Real.rpow_lt_mul_rpow_add_rpow_of_le_add`: `u ^ q < 2 ^ (q - 1) * (s ^ q + t ^ q)` for
  `1 < q`, `0 ≤ s`, `0 ≤ t` and `0 ≤ u ≤ s + t`, when `s ≠ t` or `u < s + t`.
* `Real.exists_rpow_le_of_le_add_of_le_two_sub_mul`: for `1 < q` and `0 < δ` there is `κ > 0`
  with `u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q)` whenever `0 ≤ s`, `0 ≤ t`,
  `0 ≤ u ≤ s + t` and `u ≤ (2 - δ) * s`.
-/

public section

namespace Real

/-- **A strict power mean inequality.** For `1 < q`, `0 ≤ s`, `0 ≤ t` and `0 ≤ u ≤ s + t`,
`u ^ q < 2 ^ (q - 1) * (s ^ q + t ^ q)` unless `s = t` and `u = s + t`. -/
theorem rpow_lt_mul_rpow_add_rpow_of_le_add (u : ℝ) {q s t : ℝ} (hq : 1 < q) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hus : u ≤ s + t) (hne : s ≠ t ∨ u < s + t) :
    u ^ q < 2 ^ (q - 1) * (s ^ q + t ^ q) := by
  have hq0 : 0 < q := by linarith
  -- The midpoint form `(s + t) ^ q = 2 ^ (q - 1) * (2 * ((s + t) / 2) ^ q)`.
  have hmid : (s + t) ^ q = 2 ^ (q - 1) * (2 * (1 / 2 * s + 1 / 2 * t) ^ q) := by
    rw [← mul_assoc, ← rpow_add_one two_ne_zero, sub_add_cancel,
      ← mul_rpow zero_le_two (by positivity)]
    congr 1
    ring
  rcases hne with hst | hlt
  · have hstrict := (strictConvexOn_rpow hq).2 (Set.mem_Ici.2 hs) (Set.mem_Ici.2 ht) hst
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hstrict
    calc u ^ q ≤ (s + t) ^ q := rpow_le_rpow hu hus hq0.le
      _ < 2 ^ (q - 1) * (s ^ q + t ^ q) := by
        rw [hmid]
        gcongr
        linarith
  · have hconv := (convexOn_rpow hq.le).2 (Set.mem_Ici.2 hs) (Set.mem_Ici.2 ht)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hconv
    calc u ^ q < (s + t) ^ q := rpow_lt_rpow hu hlt hq0
      _ ≤ 2 ^ (q - 1) * (s ^ q + t ^ q) := by
        rw [hmid]
        gcongr
        linarith

/-- The normalized gap behind `Real.exists_rpow_le_of_le_add_of_le_two_sub_mul`: at `s = 1`
and `t = r ∈ [0, 1]`, the `q`-th power of the largest admissible `u = min (1 + r) (2 - δ)` is a
uniform fraction below the power mean bound. -/
private theorem exists_min_rpow_le_one_sub_mul {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ2 : δ ≤ 2) :
    ∃ κ, 0 < κ ∧ ∀ r ∈ Set.Icc (0 : ℝ) 1,
      min (1 + r) (2 - δ) ^ q ≤ (1 - κ) * (2 ^ (q - 1) * (1 + r ^ q)) := by
  have hq0 : 0 < q := by linarith
  set f : ℝ → ℝ := fun r ↦ 2 ^ (q - 1) * (1 + r ^ q)
  set m : ℝ → ℝ := fun r ↦ min (1 + r) (2 - δ)
  -- Pointwise the bound `f r` strictly exceeds `m r ^ q`, so the gap is positive.
  have hgap (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) : m r ^ q < f r := by
    have hne : (1 : ℝ) ≠ r ∨ m r < 1 + r :=
      (ne_or_eq 1 r).imp_right fun h ↦ (min_le_right _ _).trans_lt (by linarith)
    have h := (m r).rpow_lt_mul_rpow_add_rpow_of_le_add hq zero_le_one hr.1
      (le_min (by linarith [hr.1]) (by linarith)) (min_le_left _ _) hne
    rwa [one_rpow] at h
  have := continuous_rpow_const hq0.le
  have hfc : Continuous f := by fun_prop
  have hmc : Continuous fun r ↦ m r ^ q := by fun_prop
  -- On the compact `[0, 1]`, `f` is dominated by a multiple `A` of the gap.
  obtain ⟨A, hA, hAf⟩ := isCompact_Icc.exists_pos_forall_lt_mul hfc.continuousOn
    (hfc.sub hmc).continuousOn (fun r hr ↦ (sub_pos.2 (hgap r hr)).le)
    (fun r hr h0 ↦ absurd h0 (sub_pos.2 (hgap r hr)).ne')
  refine ⟨A⁻¹, inv_pos.2 hA, fun r hr ↦ ?_⟩
  have h : A⁻¹ * f r < f r - m r ^ q := by
    rw [inv_mul_lt_iff₀ hA]
    exact hAf r hr
  change m r ^ q ≤ (1 - A⁻¹) * f r
  linarith

/-- **A uniform strict power mean inequality.** For `1 < q` and `0 < δ` there is `κ > 0`
such that `u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q)` whenever `0 ≤ s`, `0 ≤ t` and
`0 ≤ u ≤ min (s + t) ((2 - δ) * s)`. This is the scalar part of
`TauCeti.exists_forall_norm_add_rpow_le`. -/
theorem exists_rpow_le_of_le_add_of_le_two_sub_mul {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) :
    ∃ κ, 0 < κ ∧ ∀ s t u : ℝ, 0 ≤ s → 0 ≤ t → 0 ≤ u → u ≤ s + t → u ≤ (2 - δ) * s →
      u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
  -- For `δ > 1` the bound `u ≤ (2 - δ) * s` implies the case `δ = 1`.
  wlog hδ1 : δ ≤ 1 generalizing δ
  · obtain ⟨κ, hκ, h⟩ := this one_pos le_rfl
    refine ⟨κ, hκ, fun s t u hs ht hu hus hu2 ↦ h s t u hs ht hu hus ?_⟩
    nlinarith [not_le.1 hδ1]
  have hq0 : 0 < q := by linarith
  obtain ⟨κ, hκ, hgap⟩ := exists_min_rpow_le_one_sub_mul hq hδ (by linarith)
  refine ⟨κ, hκ, fun s t u hs ht hu hus hu2 ↦ ?_⟩
  -- The bound is symmetric in `s` and `t`, and `u ≤ (2 - δ) * s` persists when `s` grows.
  wlog hts : t ≤ s generalizing s t
  · have hst := (not_le.1 hts).le
    have h := this t s ht hs (by linarith)
      (hu2.trans (mul_le_mul_of_nonneg_left hst (by linarith))) hst
    rwa [add_comm (t ^ q)] at h
  rcases hs.eq_or_lt with rfl | hs
  · obtain rfl : t = 0 := le_antisymm hts ht
    obtain rfl : u = 0 := le_antisymm (by simpa using hus) hu
    simp [zero_rpow hq0.ne']
  -- Rescale to `s = 1` with ratio `r = t / s ∈ [0, 1]`.
  set r := t / s with hr_def
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg ht hs.le, div_le_one_of_le₀ hts hs.le⟩
  have hv : u / s ≤ min (1 + r) (2 - δ) := by
    refine le_min ?_ ?_ <;> rw [div_le_iff₀ hs]
    · rw [hr_def, add_mul, div_mul_cancel₀ _ hs.ne', one_mul]
      exact hus
    · linarith
  have hsq : 0 < s ^ q := rpow_pos_of_pos hs q
  calc u ^ q = s ^ q * (u / s) ^ q := by
        rw [div_rpow hu hs.le, mul_div_cancel₀ _ hsq.ne']
    _ ≤ s ^ q * min (1 + r) (2 - δ) ^ q :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow (div_nonneg hu hs.le) hv hq0.le) hsq.le
    _ ≤ s ^ q * ((1 - κ) * (2 ^ (q - 1) * (1 + r ^ q))) :=
        mul_le_mul_of_nonneg_left (hgap r hr) hsq.le
    _ = (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
        rw [hr_def, div_rpow ht hs.le]
        field_simp

end Real
