/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

import TauCeti.MeasureTheory.Integral.IntervalIntegral.PowerBounds

/-!
# Negative powers of the distance to a point, integrated along a segment

A function with an algebraic singularity at a point `p` is still integrable along a segment
passing arbitrarily close to `p`, provided the exponent is larger than `-1`. This file proves
the quantitative form of that statement in a real inner product space; in `ℂ` it feeds the
Schwarz--Christoffel boundary theory.

The geometric input is that on the segment from `w` to `z`, parametrized by `[0, 1]`, the
distance to `p` is at least the length of the segment times the distance of the parameter to a
fixed parameter `c`, namely the foot of the perpendicular from `p` clamped to `[0, 1]`; the
Cauchy--Schwarz inequality is what makes the comparison work.  Both pieces of the parameter
interval then compare with a power of the distance to `c`, through the one-sided estimates
`TauCeti.intervalIntegral.norm_integral_le_of_norm_le_mul_sub_rpow_right` and `..._left` of
`TauCeti.MeasureTheory.Integral.IntervalIntegral.PowerBounds`, and the singularity contributes
only the finite constant `2 / (u + 1)`.

## Main results

* `TauCeti.exists_mem_Icc_mul_abs_sub_le_dist` -- the lower bound for the distance to `p` along
  a segment.
* `TauCeti.integral_dist_rpow_segment_le` -- the arclength integral of `dist ⬝ p ^ u` along a
  segment of length `L` is at most `2 / (u + 1) * L ^ (u + 1)` when `-1 < u ≤ 0`.
-/

public section

open MeasureTheory RealInnerProductSpace Set

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On the segment from `w` to `z`, the distance to a point `p` is bounded below by the length of
the segment times the distance of the parameter to a fixed parameter `c ∈ [0, 1]`.  Geometrically
`c` is the foot of the perpendicular from `p`, clamped to the parameter interval. -/
theorem exists_mem_Icc_mul_abs_sub_le_dist (p z w : E) :
    ∃ c ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖z - w‖ * |s - c| ≤ dist (w + s • (z - w)) p := by
  rcases (norm_nonneg (z - w)).eq_or_lt with hL | hL
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun s _ => by simp [← hL]⟩
  set s₀ : ℝ := -⟪w - p, z - w⟫ / ‖z - w‖ ^ 2 with hs₀
  refine ⟨projIcc (0 : ℝ) 1 zero_le_one s₀, (projIcc (0 : ℝ) 1 zero_le_one s₀).2, fun s hs => ?_⟩
  -- `projIcc` is a contraction, and it fixes the parameters already in `[0, 1]`
  have hclamp : |s - projIcc (0 : ℝ) 1 zero_le_one s₀| ≤ |s - s₀| := by
    simpa only [projIcc_of_mem _ hs] using abs_projIcc_sub_projIcc (zero_le_one' ℝ) (c := s)
  -- the component of `w + s • (z - w) - p` along `z - w` is `‖z - w‖ * (s - s₀)`
  have hinner : ⟪w + s • (z - w) - p, z - w⟫ = ‖z - w‖ ^ 2 * (s - s₀) := by
    rw [add_sub_right_comm, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hs₀]
    field_simp
    ring
  refine le_of_mul_le_mul_left ?_ hL
  calc ‖z - w‖ * (‖z - w‖ * |s - projIcc (0 : ℝ) 1 zero_le_one s₀|)
      ≤ ‖z - w‖ * (‖z - w‖ * |s - s₀|) := by gcongr
    _ = |⟪w + s • (z - w) - p, z - w⟫| := by rw [hinner, abs_mul, abs_sq, sq, mul_assoc]
    _ ≤ ‖z - w‖ * dist (w + s • (z - w)) p := by
      rw [dist_eq_norm, mul_comm]
      exact abs_real_inner_le_norm _ _

/-- The arclength integral of a nonpositive power of the distance to `p` along the segment from
`w` to `z`: the parameter integral over `[0, 1]` is multiplied by the length `‖z - w‖` of the
segment.  For `-1 < u ≤ 0`, the bound `2 / (u + 1) * ‖z - w‖ ^ (u + 1)` is uniform in the
position of `p`; in particular `p` is allowed to lie on the segment. -/
theorem integral_dist_rpow_segment_le {p : E} {u : ℝ} (hu : -1 < u) (hu0 : u ≤ 0) {z w : E} :
    (∫ s in (0 : ℝ)..1, dist (w + s • (z - w)) p ^ u) * ‖z - w‖
      ≤ 2 / (u + 1) * ‖z - w‖ ^ (u + 1) := by
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  rcases (norm_nonneg (z - w)).eq_or_lt with hL | hL
  · rw [← hL, mul_zero, Real.zero_rpow hu1.ne', mul_zero]
  obtain ⟨c, hc, hclamp⟩ := exists_mem_Icc_mul_abs_sub_le_dist p z w
  have hmeas : AEStronglyMeasurable (fun s : ℝ => dist (w + s • (z - w)) p ^ u) volume :=
    ((by fun_prop : Continuous fun s : ℝ => dist (w + s • (z - w)) p).measurable.pow_const
      u).aestronglyMeasurable
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
  have hbr : ∀ᵐ s ∂volume.restrict (Ioc c 1), ‖dist (w + s • (z - w)) p ^ u‖ ≤
      ‖z - w‖ ^ u * (s - c) ^ u := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
    have hb := hbnd s ⟨hc.1.trans hs.1.le, hs.2⟩ hs.1.ne'
    rw [Real.norm_of_nonneg (hnn s)]
    rwa [abs_of_pos (sub_pos.mpr hs.1)] at hb
  have hi2 := TauCeti.intervalIntegral.intervalIntegrable_of_norm_le_mul_sub_rpow_right
    (f := fun s : ℝ => dist (w + s • (z - w)) p ^ u) (a := c) (b := 1) (K := ‖z - w‖ ^ u) hu
    hc.2 hmeas.restrict hbr
  have hb2 := (Real.le_norm_self _).trans
    (TauCeti.intervalIntegral.norm_integral_le_of_norm_le_mul_sub_rpow_right
      (f := fun s : ℝ => dist (w + s • (z - w)) p ^ u) (a := c) (b := 1) (K := ‖z - w‖ ^ u) hu
      hc.2 hbr)
  -- the piece to the left of the foot of the perpendicular
  have hbl : ∀ᵐ s ∂volume.restrict (Ioc 0 c), ‖dist (w + s • (z - w)) p ^ u‖ ≤
      ‖z - w‖ ^ u * (c - s) ^ u := by
    filter_upwards [Measure.ae_ne (volume.restrict (Ioc 0 c)) c,
      self_mem_ae_restrict measurableSet_Ioc] with s hsne hs
    have hb := hbnd s ⟨hs.1.le, hs.2.trans hc.2⟩ hsne
    rw [Real.norm_of_nonneg (hnn s)]
    rwa [abs_of_neg (sub_neg.mpr (lt_of_le_of_ne hs.2 hsne)), neg_sub] at hb
  have hi1 := TauCeti.intervalIntegral.intervalIntegrable_of_norm_le_mul_sub_rpow_left
    (f := fun s : ℝ => dist (w + s • (z - w)) p ^ u) (a := 0) (b := c) (K := ‖z - w‖ ^ u) hu
    hc.1 hmeas.restrict hbl
  have hb1 := (Real.le_norm_self _).trans
    (TauCeti.intervalIntegral.norm_integral_le_of_norm_le_mul_sub_rpow_left
      (f := fun s : ℝ => dist (w + s • (z - w)) p ^ u) (a := 0) (b := c) (K := ‖z - w‖ ^ u) hu
      hc.1 hbl)
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

end TauCeti
