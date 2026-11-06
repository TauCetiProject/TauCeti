/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Negative powers of the distance to a point, integrated along a segment

A function with an algebraic singularity at a point `p` is still integrable along a segment
passing arbitrarily close to `p`, provided the exponent is larger than `-1`. This file proves
the quantitative form of that statement in `ℂ`, for use in the Schwarz--Christoffel boundary
theory.

The geometric input is that on the segment from `w` to `z`, parametrized by `[0, 1]`, the
distance to `p` is at least the length of the segment times the distance of the parameter to a
fixed parameter `c`, namely the foot of the perpendicular from `p` clamped to `[0, 1]`; the
Cauchy--Schwarz inequality is what makes the comparison work.  Both pieces of the parameter
interval then compare with a power of the distance to `c`, whose integral Mathlib computes, and
the singularity contributes only the finite constant `2 / (u + 1)`.

## Main results

* `Complex.exists_mem_Icc_mul_abs_sub_le_dist` -- the lower bound for the distance to `p` along
  a segment.
* `Complex.integral_dist_rpow_segment_le` -- the arclength integral of `dist ⬝ p ^ u` along a
  segment of length `L` is at most `2 / (u + 1) * L ^ (u + 1)` when `-1 < u ≤ 0`.
-/

public section

open MeasureTheory RealInnerProductSpace Set

namespace Complex

/-- On the segment from `w` to `z`, the distance to a point `p` is bounded below by the length of
the segment times the distance of the parameter to a fixed parameter `c ∈ [0, 1]`.  Geometrically
`c` is the foot of the perpendicular from `p`, clamped to the parameter interval. -/
theorem exists_mem_Icc_mul_abs_sub_le_dist (p z w : ℂ) :
    ∃ c ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖z - w‖ * |s - c| ≤ dist (w + s • (z - w)) p := by
  rcases eq_or_ne z w with rfl | hzw
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun s _ => by simp⟩
  have hL : (0 : ℝ) < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzw)
  set A : ℂ := w - p with hA
  set B : ℂ := z - w with _hB
  set q : ℝ := ⟪A, B⟫ with hq
  set s₀ : ℝ := -q / ‖B‖ ^ 2 with hs₀
  have key : ∀ t : ℝ, ‖B‖ * |t - s₀| ≤ ‖A + t • B‖ := by
    intro t
    have hnorm : ‖A + t • B‖ ^ 2 = ‖A‖ ^ 2 + 2 * t * q + t ^ 2 * ‖B‖ ^ 2 := by
      rw [hq, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    -- Cauchy--Schwarz, in the form that bounds the defect of the projection
    have hcs : q * q ≤ ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
      rw [hq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      exact real_inner_mul_inner_self_le A B
    have hdiv : q ^ 2 / ‖B‖ ^ 2 ≤ ‖A‖ ^ 2 := by
      rw [div_le_iff₀ (pow_pos hL 2)]
      nlinarith [hcs]
    have hsq : (‖B‖ * |t - s₀|) ^ 2 ≤ ‖A + t • B‖ ^ 2 := by
      have hexp : (‖B‖ * |t - s₀|) ^ 2 =
          ‖B‖ ^ 2 * t ^ 2 + 2 * t * q + q ^ 2 / ‖B‖ ^ 2 := by
        rw [mul_pow, sq_abs, hs₀]
        field_simp
        ring
      rw [hexp, hnorm]
      linarith [hdiv]
    exact (abs_le_of_sq_le_sq' hsq (norm_nonneg _)).2
  set c : ℝ := ↑(projIcc (0 : ℝ) 1 zero_le_one s₀)
  refine ⟨c, (projIcc (0 : ℝ) 1 zero_le_one s₀).2, ?_⟩
  intro s hs
  -- `projIcc` is a contraction, and it fixes the parameters already in `[0, 1]`
  have hclamp : |s - c| ≤ |s - s₀| := by
    have h := Set.abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)
      (c := s) (d := s₀)
    rwa [projIcc_of_mem _ hs] at h
  have hseg : w + s • B - p = A + s • B := by rw [hA]; abel
  calc ‖B‖ * |s - c| ≤ ‖B‖ * |s - s₀| :=
        mul_le_mul_of_nonneg_left hclamp (norm_nonneg _)
    _ ≤ ‖A + s • B‖ := key s
    _ = dist (w + s • B) p := by rw [dist_eq_norm, hseg]

end Complex

namespace intervalIntegral

/-- A nonnegative function bounded on `[a, b]` (away from `a`) by `K * (s - a) ^ u` with
`-1 < u` is interval integrable on `[a, b]`, and its integral is at most
`K * ((b - a) ^ (u + 1) / (u + 1))`. -/
theorem intervalIntegrable_and_integral_le_of_le_mul_rpow_sub_right {f : ℝ → ℝ} {a b K u : ℝ}
    (hu : -1 < u) (hab : a ≤ b) (hf0 : ∀ s, 0 ≤ f s) (hmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ s ∈ Icc a b, s ≠ a → f s ≤ K * (s - a) ^ u) :
    IntervalIntegrable f volume a b ∧
      ∫ s in a..b, f s ≤ K * ((b - a) ^ (u + 1) / (u + 1)) := by
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  have hint : IntervalIntegrable (fun s : ℝ => K * (s - a) ^ u) volume a b := by
    have h := (intervalIntegrable_rpow' (a := 0) (b := b - a) hu).comp_sub_right a
    simpa using h.const_mul K
  have hi : IntervalIntegrable f volume a b := by
    refine hint.mono_fun' hmeas.restrict ?_
    filter_upwards [Measure.ae_ne (volume.restrict (uIoc a b)) a,
      self_mem_ae_restrict measurableSet_uIoc] with s hsne hsmem
    rw [uIoc_of_le hab] at hsmem
    rw [Real.norm_of_nonneg (hf0 s)]
    exact hbound s (Ioc_subset_Icc_self hsmem) hsne
  refine ⟨hi, (integral_mono_ae_restrict hab hi hint ?_).trans_eq ?_⟩
  · filter_upwards [Measure.ae_ne (volume.restrict (Icc a b)) a,
      self_mem_ae_restrict (measurableSet_Icc (a := a) (b := b))] with s hsne hsmem
    exact hbound s hsmem hsne
  · rw [integral_const_mul, integral_comp_sub_right (fun x : ℝ => x ^ u) a, sub_self,
      integral_rpow (Or.inl hu), Real.zero_rpow hu1.ne']
    ring

/-- The mirror image of
`intervalIntegral.intervalIntegrable_and_integral_le_of_le_mul_rpow_sub_right`: the singularity
is at the right endpoint `b`. -/
theorem intervalIntegrable_and_integral_le_of_le_mul_rpow_sub_left {f : ℝ → ℝ} {a b K u : ℝ}
    (hu : -1 < u) (hab : a ≤ b) (hf0 : ∀ s, 0 ≤ f s) (hmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ s ∈ Icc a b, s ≠ b → f s ≤ K * (b - s) ^ u) :
    IntervalIntegrable f volume a b ∧
      ∫ s in a..b, f s ≤ K * ((b - a) ^ (u + 1) / (u + 1)) := by
  obtain ⟨hi, hle⟩ :=
    intervalIntegrable_and_integral_le_of_le_mul_rpow_sub_right (f := fun s => f (a + b - s))
      (K := K) hu hab (fun s => hf0 _)
      (hmeas.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume (a + b)))
      (fun s hs hsa => by
        have := hbound (a + b - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
          (fun h => hsa (by linarith))
        rwa [show b - (a + b - s) = s - a by ring] at this)
  refine ⟨?_, ?_⟩
  · simpa using (hi.comp_sub_left (a + b)).symm
  · rwa [integral_comp_sub_left f (a + b), show a + b - b = a by ring,
      show a + b - a = b by ring] at hle

end intervalIntegral

namespace Complex

/-- The arclength integral of a nonpositive power of the distance to `p` along the segment from
`w` to `z`: the parameter integral over `[0, 1]` is multiplied by the length `‖z - w‖` of the
segment.  For `-1 < u ≤ 0`, the bound `2 / (u + 1) * ‖z - w‖ ^ (u + 1)` is uniform in the
position of `p`; in particular `p` is allowed to lie on the segment. -/
theorem integral_dist_rpow_segment_le {p : ℂ} {u : ℝ} (hu : -1 < u) (hu0 : u ≤ 0) {z w : ℂ} :
    (∫ s in (0 : ℝ)..1, dist (w + s • (z - w)) p ^ u) * ‖z - w‖
      ≤ 2 / (u + 1) * ‖z - w‖ ^ (u + 1) := by
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  rcases eq_or_ne z w with rfl | hzw
  · rw [sub_self, norm_zero, mul_zero, Real.zero_rpow hu1.ne', mul_zero]
  have hL : (0 : ℝ) < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzw)
  obtain ⟨c, hc, hclamp⟩ := exists_mem_Icc_mul_abs_sub_le_dist p z w
  have hmeas : AEStronglyMeasurable (fun s : ℝ => dist (w + s • (z - w)) p ^ u) volume := by
    have hcontd : Continuous fun s : ℝ => dist (w + s • (z - w)) p := by fun_prop
    exact (hcontd.measurable.pow measurable_const).aestronglyMeasurable
  have hnn : ∀ s : ℝ, 0 ≤ dist (w + s • (z - w)) p ^ u := fun s => Real.rpow_nonneg dist_nonneg _
  -- the segment meets `p` at the single parameter `c` at worst, so that parameter is discarded
  have hbnd : ∀ s ∈ Icc (0 : ℝ) 1, s ≠ c →
      dist (w + s • (z - w)) p ^ u ≤ ‖z - w‖ ^ u * |s - c| ^ u := by
    intro s hs hsne
    have _ : 0 < |s - c| := abs_pos.mpr (sub_ne_zero_of_ne hsne)
    have hpos : 0 < ‖z - w‖ * |s - c| := by positivity
    calc dist (w + s • (z - w)) p ^ u ≤ (‖z - w‖ * |s - c|) ^ u :=
          Real.rpow_le_rpow_of_nonpos hpos (hclamp s hs) hu0
      _ = ‖z - w‖ ^ u * |s - c| ^ u := Real.mul_rpow (norm_nonneg _) (abs_nonneg _)
  -- the piece to the right of the foot of the perpendicular
  obtain ⟨hi2, hb2⟩ := intervalIntegral.intervalIntegrable_and_integral_le_of_le_mul_rpow_sub_right
    (a := c) (b := 1) (K := ‖z - w‖ ^ u) hu hc.2 hnn hmeas fun s hs hsne => by
      have hb := hbnd s ⟨hc.1.trans hs.1, hs.2⟩ hsne
      rwa [abs_of_pos (sub_pos.mpr (lt_of_le_of_ne hs.1 hsne.symm))] at hb
  -- the piece to the left of the foot of the perpendicular
  obtain ⟨hi1, hb1⟩ := intervalIntegral.intervalIntegrable_and_integral_le_of_le_mul_rpow_sub_left
    (a := 0) (b := c) (K := ‖z - w‖ ^ u) hu hc.1 hnn hmeas fun s hs hsne => by
      have hb := hbnd s ⟨hs.1, hs.2.trans hc.2⟩ hsne
      rwa [abs_of_neg (sub_neg.mpr (lt_of_le_of_ne hs.2 hsne)), neg_sub] at hb
  rw [sub_zero] at hb1
  have hsplit : (∫ s in (0 : ℝ)..1, dist (w + s • (z - w)) p ^ u)
      = (∫ s in (0 : ℝ)..c, dist (w + s • (z - w)) p ^ u)
        + ∫ s in c..(1 : ℝ), dist (w + s • (z - w)) p ^ u :=
    (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  have hc1 : c ^ (u + 1) ≤ 1 := Real.rpow_le_one hc.1 hc.2 hu1.le
  have hc2 : (1 - c) ^ (u + 1) ≤ 1 :=
    Real.rpow_le_one (by linarith [hc.2]) (by linarith [hc.1]) hu1.le
  have hbound : (∫ s in (0 : ℝ)..1, dist (w + s • (z - w)) p ^ u)
      ≤ ‖z - w‖ ^ u * (2 / (u + 1)) := by
    rw [hsplit]
    have _ : (0 : ℝ) ≤ ‖z - w‖ ^ u := Real.rpow_nonneg (norm_nonneg _) u
    calc _ ≤ ‖z - w‖ ^ u * (c ^ (u + 1) / (u + 1))
            + ‖z - w‖ ^ u * ((1 - c) ^ (u + 1) / (u + 1)) := add_le_add hb1 hb2
      _ ≤ ‖z - w‖ ^ u * (1 / (u + 1)) + ‖z - w‖ ^ u * (1 / (u + 1)) := by
          gcongr
      _ = ‖z - w‖ ^ u * (2 / (u + 1)) := by ring
  calc (∫ s in (0 : ℝ)..1, dist (w + s • (z - w)) p ^ u) * ‖z - w‖
      ≤ ‖z - w‖ ^ u * (2 / (u + 1)) * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ = 2 / (u + 1) * ‖z - w‖ ^ (u + 1) := by
        rw [Real.rpow_add hL, Real.rpow_one]
        ring

end Complex
