/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CurveAction.Basic
public import TauCeti.Topology.MetricSpace.Length
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The action of a geodesic segment

A constant-speed geodesic has constant metric derivative on the interior of its parameter
interval. Consequently its `p`-action is exactly the `p`th power of the distance between its
endpoints. This is the pathwise identity used when dynamic plans are concentrated on minimizing
geodesics.

Conversely, the Hölder estimate bounds the `p`-action of every absolutely continuous curve on
`[0, 1]` below by `d(γ 0, γ 1) ^ p`, and for `1 < p` the curves attaining this bound are exactly
the constant-speed geodesic segments
(`AbsolutelyContinuousOnInterval.isGeodesicSegment_of_curveAction_le`). This rigidity is what
forces the paths of a dynamic plan of minimal action to be geodesics. It fails for `p = 1`, where
every monotone reparametrisation of a geodesic has the same action.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Interval

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {x y : X}

/-- On the interior of its parameter interval, a constant-speed geodesic segment has metric
derivative equal to the distance between its endpoints. -/
theorem IsGeodesicSegment.metricDerivative_eq (h : IsGeodesicSegment γ x y)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    metricDerivative γ t = ENNReal.ofReal (dist x y) := by
  apply metricDerivative_eq_of_tendsto
  have hIoo : ∀ᶠ s in 𝓝[≠] t, s ∈ Ioo (0 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds ht.1 ht.2)
  have hquot : (fun s ↦ edist (γ s) (γ t) / edist s t) =ᶠ[𝓝[≠] t]
      fun _ ↦ ENNReal.ofReal (dist x y) := by
    filter_upwards [hIoo, self_mem_nhdsWithin] with s hs hst
    have hst' : s ≠ t := by simpa using hst
    rw [edist_dist, edist_dist, h.dist_eq s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩,
      Real.dist_eq]
    rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
    exact ENNReal.mul_div_cancel_right
      (ENNReal.ofReal_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hst'))).ne'
      ENNReal.ofReal_ne_top
  exact tendsto_const_nhds.congr' hquot.symm

/-- The `p`-action of a constant-speed geodesic segment is the `p`th power of the distance
between its endpoints. The values of the metric derivative at the two endpoints do not affect the
integral. -/
theorem IsGeodesicSegment.curveAction_eq (h : IsGeodesicSegment γ x y) (p : ℝ) :
    curveAction p γ 0 1 = ENNReal.ofReal (dist x y) ^ p := by
  rw [curveAction_def]
  have hderiv : (fun t ↦ metricDerivative γ t ^ p) =ᵐ[volume.restrict (Ι (0 : ℝ) 1)]
      fun _ ↦ ENNReal.ofReal (dist x y) ^ p := by
    refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
    filter_upwards [volume.ae_ne 1] with t h1 ht
    rw [uIoc_of_le zero_le_one] at ht
    exact congrArg (fun z : ℝ≥0∞ ↦ z ^ p)
      (h.metricDerivative_eq ⟨ht.1, lt_of_le_of_ne ht.2 h1⟩)
  rw [lintegral_congr_ae hderiv, setLIntegral_const, Real.volume_uIoc]
  simp

/-- A geodesic segment is absolutely continuous on `[0, 1]`, being Lipschitz there. -/
theorem IsGeodesicSegment.absolutelyContinuousOnInterval (h : IsGeodesicSegment γ x y) :
    AbsolutelyContinuousOnInterval γ 0 1 := by
  have hL := h.lipschitzOnWith
  rw [← uIcc_of_le zero_le_one] at hL
  exact hL.absolutelyContinuousOnInterval

section Rigidity

variable {p : ℝ}

/-- The strict convexity estimate behind `curveAction_zero_eq_mul_of_curveAction_le`. Let
`1 < p` and `0 < s < 1`. If a total length `a + c ≥ D` is split into pieces with
`a ^ p ≤ s ^ (p - 1) * α` and `c ^ p ≤ (1 - s) ^ (p - 1) * β`, while `α + β ≤ D ^ p`, then
`α = s * D ^ p`: the budget `D ^ p` leaves room only for the affine split, by strict convexity of
`x ↦ x ^ p`. -/
private theorem eq_mul_rpow_of_rpow_le_rpow_sub_one_mul {s a c D α β : ℝ} (hp : 1 < p)
    (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 ≤ a) (hc : 0 ≤ c) (hD : 0 ≤ D) (hDac : D ≤ a + c)
    (hα : a ^ p ≤ s ^ (p - 1) * α) (hβ : c ^ p ≤ (1 - s) ^ (p - 1) * β)
    (hαβ : α + β ≤ D ^ p) : α = s * D ^ p := by
  have hs1' : 0 < 1 - s := sub_pos.2 hs1
  -- Write the pieces as `a = s * u` and `c = (1 - s) * v`.
  set u := a / s
  set v := c / (1 - s)
  have hu : 0 ≤ u := div_nonneg ha hs0.le
  have hv : 0 ≤ v := div_nonneg hc hs1'.le
  have ha' : a = s * u := (mul_div_cancel₀ a hs0.ne').symm
  have hc' : c = (1 - s) * v := (mul_div_cancel₀ c hs1'.ne').symm
  -- Dividing the two bounds by the weights gives `s * u ^ p ≤ α` and `(1 - s) * v ^ p ≤ β`.
  have hweight {w x γ' : ℝ} (hw : 0 < w) (hx : 0 ≤ x) (h : (w * x) ^ p ≤ w ^ (p - 1) * γ') :
      w * x ^ p ≤ γ' := by
    refine le_of_mul_le_mul_left ?_ (Real.rpow_pos_of_pos hw (p - 1))
    rwa [← mul_assoc, ← Real.rpow_add_one hw.ne', sub_add_cancel, ← Real.mul_rpow hw.le hx]
  have hαu : s * u ^ p ≤ α := hweight hs0 hu (ha' ▸ hα)
  have hβv : (1 - s) * v ^ p ≤ β := hweight hs1' hv (hc' ▸ hβ)
  have hDp : D ^ p ≤ (s * u + (1 - s) * v) ^ p :=
    Real.rpow_le_rpow hD (ha' ▸ hc' ▸ hDac) (by linarith)
  rcases eq_or_ne u v with huv | huv
  · -- Equal speeds: then `D ≤ u`, and the two bounds pin `α` to `s * D ^ p`.
    rw [← huv] at hβv hDp
    have hDu : D ^ p ≤ u ^ p := by rwa [← add_mul, add_sub_cancel, one_mul] at hDp
    nlinarith [mul_le_mul_of_nonneg_left hDu hs0.le, mul_le_mul_of_nonneg_left hDu hs1'.le]
  · -- Different speeds: strict convexity makes the budget `D ^ p` too small.
    have hlt := (strictConvexOn_rpow hp).2 (mem_Ici.2 hu) (mem_Ici.2 hv) huv hs0 hs1'
      (add_sub_cancel s 1)
    simp only [smul_eq_mul] at hlt
    linarith

/-- **Minimal action is spent at a constant rate.** For `1 < p`, if a curve absolutely
continuous on `[0, 1]` has `p`-action at most `d(γ 0, γ 1) ^ p`, then its `p`-action on `[0, s]`
is `s * d(γ 0, γ 1) ^ p` for every `s ∈ [0, 1]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.curveAction_zero_eq_mul_of_curveAction_le
    (hγ : AbsolutelyContinuousOnInterval γ 0 1) (hp : 1 < p)
    (h : curveAction p γ 0 1 ≤ edist (γ 0) (γ 1) ^ p) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    curveAction p γ 0 s = ENNReal.ofReal (s * dist (γ 0) (γ 1) ^ p) := by
  set D := dist (γ 0) (γ 1)
  have hD : edist (γ 0) (γ 1) ^ p = ENNReal.ofReal (D ^ p) := by
    rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (zero_lt_one.trans hp).le]
  rw [hD] at h
  have hfin : curveAction p γ 0 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hsplit := curveAction_add p γ (Icc_subset_uIcc hs)
  have h0s : curveAction p γ 0 s ≠ ∞ := ne_top_of_le_ne_top hfin (hsplit ▸ le_self_add)
  have hs1 : curveAction p γ s 1 ≠ ∞ := ne_top_of_le_ne_top hfin (hsplit ▸ le_add_self)
  rcases hs.1.eq_or_lt with rfl | hs0
  · simp [curveAction_self]
  rcases hs.2.eq_or_lt with rfl | hs1'
  · refine le_antisymm (by simpa using h) ?_
    simpa [hD] using hγ.edist_rpow_le_curveAction hp.le
  -- Split `[0, 1]` at `s`: the Hölder estimate on both pieces and the budget `D ^ p` force the
  -- affine split.
  rw [← ENNReal.ofReal_toReal h0s]
  congr 1
  have h0s' := hγ.dist_rpow_le_mul_toReal_curveAction hp.le left_mem_uIcc (Icc_subset_uIcc hs)
    hs.1 h0s
  rw [sub_zero] at h0s'
  refine eq_mul_rpow_of_rpow_le_rpow_sub_one_mul hp hs0 hs1' dist_nonneg dist_nonneg
    dist_nonneg (dist_triangle _ _ _) h0s'
    (hγ.dist_rpow_le_mul_toReal_curveAction hp.le (Icc_subset_uIcc hs) right_mem_uIcc hs.2 hs1) ?_
  rw [← ENNReal.toReal_add h0s hs1, hsplit]
  exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg dist_nonneg _) h

/-- **Curves of minimal action are geodesics.** For `1 < p`, an absolutely continuous curve on
`[0, 1]` whose `p`-action is at most `d(γ 0, γ 1) ^ p` is a constant-speed geodesic segment from
`γ 0` to `γ 1`. Together with the Hölder estimate and `IsGeodesicSegment.curveAction_eq`, the
geodesic segments are exactly the absolutely continuous curves on `[0, 1]` attaining the lower
bound `d(γ 0, γ 1) ^ p ≤ A_p(γ)`. -/
theorem _root_.AbsolutelyContinuousOnInterval.isGeodesicSegment_of_curveAction_le
    (hγ : AbsolutelyContinuousOnInterval γ 0 1) (hp : 1 < p)
    (h : curveAction p γ 0 1 ≤ edist (γ 0) (γ 1) ^ p) : IsGeodesicSegment γ (γ 0) (γ 1) := by
  set D := dist (γ 0) (γ 1)
  have hA {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) := hγ.curveAction_zero_eq_mul_of_curveAction_le hp h hs
  -- The piece `[s, t]` costs `(t - s) * D ^ p`, and the Hölder estimate bounds its length.
  refine isGeodesicSegment_of_dist_le rfl rfl fun s hs t ht hst ↦ ?_
  have hst' : curveAction p γ s t = ENNReal.ofReal ((t - s) * D ^ p) := by
    have hadd := curveAction_add p γ (a := 0) (b := s) (c := t)
      (by rw [uIcc_of_le (hs.1.trans hst)]; exact ⟨hs.1, hst⟩)
    rw [hA hs, hA ht] at hadd
    rw [sub_mul, ENNReal.ofReal_sub _ (mul_nonneg hs.1 (Real.rpow_nonneg dist_nonneg _)), ← hadd,
      ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]
  have hle := hγ.dist_rpow_le_mul_toReal_curveAction hp.le (Icc_subset_uIcc hs)
    (Icc_subset_uIcc ht) hst (hst' ▸ ENNReal.ofReal_ne_top)
  rw [hst', ENNReal.toReal_ofReal
    (mul_nonneg (sub_nonneg.2 hst) (Real.rpow_nonneg dist_nonneg _))] at hle
  have hrhs : (t - s) ^ (p - 1) * ((t - s) * D ^ p) = ((t - s) * D) ^ p := by
    rw [Real.mul_rpow (sub_nonneg.2 hst) dist_nonneg, ← mul_assoc,
      ← Real.rpow_add_one' (sub_nonneg.2 hst) (by linarith), sub_add_cancel]
  rwa [hrhs, Real.rpow_le_rpow_iff dist_nonneg
    (mul_nonneg (sub_nonneg.2 hst) dist_nonneg) (zero_lt_one.trans hp)] at hle

end Rigidity

end TauCeti
