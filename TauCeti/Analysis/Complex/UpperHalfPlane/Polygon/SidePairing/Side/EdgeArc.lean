/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Elliptic

/-!
# Open-interval parametrization of polygon edges and half-edges

Let `σ` pair the sides of a convex hyperbolic `n`-gon `P`, whose vertices may lie either in `ℍ` or
on the boundary `∂ℍ = OnePoint ℝ`. In the CW cell decomposition of the quotient surface, each side
`i` with `σ.pair i ≠ i` contributes its entire open side (excluding any finite endpoints), whereas
each self-paired side (`σ.pair i = i`) folds about `σ.selfPairedSideFixedPoint ⟨i, hi⟩` and
contributes only the open half-side between `P.vertex i` and `σ.selfPairedSideFixedPoint ⟨i, hi⟩`.

This file constructs an explicit continuous injective parametrization
`σ.edgeArc i : ℝ → ℍ` of that open carrier on `Ioo (-1 : ℝ) 1` along `P.sideGeodesic i`, handling
bounded geodesic segments, geodesic rays, and bi-infinite geodesics uniformly, and records its
boundary limits as `u → -1` and `u → 1` within `Ioo (-1) 1`: convergence in `ℍ` at finite vertices
and self-paired midpoints, and convergence to infinity in horodisc height `(g • ·).im` at ideal
vertices sent to `∞` by `g : PSL(2, ℝ)`.

## Main definitions and results

* `ConvexPolygon.SidePairing.edgeArc`: the open `1`-cell arc `ℝ → ℍ` on `Ioo (-1 : ℝ) 1` carried
  by side `i`.
* `ConvexPolygon.SidePairing.continuousOn_edgeArc` and `ConvexPolygon.SidePairing.injOn_edgeArc`:
  continuity and injectivity on `Ioo (-1) 1`.
* `ConvexPolygon.SidePairing.mem_image_edgeArc_or_selfPaired_of_mem_side`: every non-vertex point
  of `P.side j` lies either on `σ.edgeArc j '' Ioo (-1) 1`, at `σ.selfPairedSideFixedPoint`, or on
  the image under `(σ.map j)⁻¹` of `σ.edgeArc j '' Ioo (-1) 1`.
* `ConvexPolygon.SidePairing.tendsto_edgeArc_neg_one_of_eq_inl`,
  `ConvexPolygon.SidePairing.tendsto_edgeArc_neg_one_atImInfty_of_eq_inr`,
  `ConvexPolygon.SidePairing.tendsto_edgeArc_one_of_pair_eq`,
  `ConvexPolygon.SidePairing.tendsto_edgeArc_one_of_eq_inl`, and
  `ConvexPolygon.SidePairing.tendsto_edgeArc_one_atImInfty_of_eq_inr`: endpoint behaviour at `-1`
  and `1`.
-/

public section

noncomputable section

open Metric MulAction Set Topology UpperHalfPlane
open scoped MatrixGroups OnePoint

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

/-! ### Open real intervals parametrized by `(-1, 1)` -/

/-- The four open parameter-interval shapes along an oriented geodesic line on `ℍ`: bounded
`(a, b)`, forward ray `(a, ∞)`, backward ray `(-∞, b)`, or the whole line `ℝ`. -/
private inductive EdgeInterval : Type
  | bounded (a b : ℝ)
  | fromPoint (a : ℝ)
  | toPoint (b : ℝ)
  | full

namespace EdgeInterval

private def Valid : EdgeInterval → Prop
  | bounded a b => a < b
  | _ => True

private def openSet : EdgeInterval → Set ℝ
  | bounded a b => Ioo a b
  | fromPoint a => Ioi a
  | toPoint b => Iio b
  | full => univ

/-- Order-preserving rational bijection from `Ioo (-1 : ℝ) 1` onto `I.openSet`. -/
private def param : EdgeInterval → ℝ → ℝ
  | bounded a b, u => (a + b) / 2 + (b - a) / 2 * u
  | fromPoint a, u => a + (1 + u) / (1 - u)
  | toPoint b, u => b - (1 - u) / (1 + u)
  | full, u => u / (1 - u ^ 2)

private theorem continuousOn_param (I : EdgeInterval) : ContinuousOn I.param (Ioo (-1) 1) := by
  cases I with
  | bounded a b => exact Continuous.continuousOn (by unfold param; fun_prop)
  | fromPoint a =>
    refine ContinuousOn.add continuousOn_const (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    exact fun u hu ↦ by linarith [hu.2]
  | toPoint b =>
    refine ContinuousOn.sub continuousOn_const (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    exact fun u hu ↦ by linarith [hu.1]
  | full =>
    refine ContinuousOn.div continuousOn_id (by fun_prop) fun u hu ↦ ?_
    nlinarith [hu.1, hu.2]

private theorem injOn_param {I : EdgeInterval} (hI : I.Valid) : InjOn I.param (Ioo (-1) 1) := by
  intro u hu v hv h
  cases I with
  | bounded a b =>
    have hab : a < b := hI
    simp only [param] at h
    exact mul_left_cancel₀ (by linarith : (b - a) / 2 ≠ 0) (by linarith)
  | fromPoint a =>
    simp only [param, add_right_inj] at h
    rw [div_eq_div_iff (by linarith [hu.2]) (by linarith [hv.2])] at h
    linarith
  | toPoint b =>
    simp only [param, sub_right_inj] at h
    rw [div_eq_div_iff (by linarith [hu.1]) (by linarith [hv.1])] at h
    linarith
  | full =>
    simp only [param] at h
    rw [div_eq_div_iff (by nlinarith [hu.1, hu.2]) (by nlinarith [hv.1, hv.2])] at h
    rcases mul_eq_zero.1 (by linear_combination h : (u - v) * (1 + u * v) = 0) with huv | hp
    · linarith
    · exfalso
      nlinarith [hu.1, hu.2, hv.1, hv.2]

private theorem image_full_param_Ioo : full.param '' Ioo (-1) 1 = univ := by
  ext t
  simp only [param, mem_image, mem_Ioo, mem_univ, iff_true]
  by_cases ht : t = 0
  · exact ⟨0, ⟨by norm_num, by norm_num⟩, by simp [ht]⟩
  · set s := Real.sqrt (1 + 4 * t ^ 2)
    have hs_sq : s ^ 2 = 1 + 4 * t ^ 2 := Real.sq_sqrt (by positivity)
    have hs_pos : 1 < s := by
      nlinarith [sq_pos_of_ne_zero ht, Real.sqrt_nonneg (1 + 4 * t ^ 2)]
    have hs_ub : s < 1 + 2 * |t| := by
      have hsq : (1 + 2 * |t|) ^ 2 = 1 + 4 * |t| + 4 * t ^ 2 := by
        rw [add_sq, mul_pow, sq_abs]
        ring
      nlinarith [abs_pos.2 ht, Real.sqrt_nonneg (1 + 4 * t ^ 2)]
    refine ⟨(s - 1) / (2 * t), ?_, ?_⟩
    · rw [← abs_lt, abs_div, abs_of_pos (sub_pos.2 hs_pos), abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2),
        div_lt_one (mul_pos (by norm_num) (abs_pos.2 ht))]
      linarith
    · have hnum : 1 - ((s - 1) / (2 * t)) ^ 2 = (s - 1) / (2 * t ^ 2) := by
        field_simp
        linear_combination -hs_sq
      rw [hnum]
      have hs1 : s - 1 ≠ 0 := by linarith
      field_simp

private theorem image_param_Ioo {I : EdgeInterval} (hI : I.Valid) :
    I.param '' Ioo (-1) 1 = I.openSet := by
  cases I with
  | bounded a b =>
    ext t
    have hab : a < b := hI
    simp only [param, openSet, mem_image, mem_Ioo]
    refine ⟨fun ⟨u, ⟨hu₁, hu₂⟩, h⟩ ↦ ⟨by nlinarith, by nlinarith⟩,
      fun ht ↦ ⟨(2 * t - (a + b)) / (b - a), ?_, ?_⟩⟩
    · have hba : 0 < b - a := sub_pos.2 hab
      exact ⟨(lt_div_iff₀ hba).2 (by linarith), (div_lt_iff₀ hba).2 (by linarith)⟩
    · have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
      field_simp
      ring
  | fromPoint a =>
    ext t
    simp only [param, openSet, mem_image, mem_Ioo, mem_Ioi]
    refine ⟨fun ⟨u, ⟨hu₁, hu₂⟩, h⟩ ↦
        by linarith [div_pos (by linarith : 0 < 1 + u) (by linarith : 0 < 1 - u)],
      fun ht ↦ ⟨(t - a - 1) / (t - a + 1), ?_, ?_⟩⟩
    · have hd : 0 < t - a + 1 := by linarith
      exact ⟨(lt_div_iff₀ hd).2 (by linarith), (div_lt_iff₀ hd).2 (by linarith)⟩
    · have hd : t - a + 1 ≠ 0 := by linarith
      have h1 : 1 - (t - a - 1) / (t - a + 1) = 2 / (t - a + 1) := by field_simp; ring
      rw [h1]
      field_simp
      ring
  | toPoint b =>
    ext t
    simp only [param, openSet, mem_image, mem_Ioo, mem_Iio]
    refine ⟨fun ⟨u, ⟨hu₁, hu₂⟩, h⟩ ↦
        by linarith [div_pos (by linarith : 0 < 1 - u) (by linarith : 0 < 1 + u)],
      fun ht ↦ ⟨(1 - (b - t)) / (1 + (b - t)), ?_, ?_⟩⟩
    · have hd : 0 < 1 + (b - t) := by linarith
      exact ⟨(lt_div_iff₀ hd).2 (by linarith), (div_lt_iff₀ hd).2 (by linarith)⟩
    · have hd : 1 + (b - t) ≠ 0 := by linarith
      have h1 : 1 + (1 - (b - t)) / (1 + (b - t)) = 2 / (1 + (b - t)) := by field_simp; ring
      rw [h1]
      field_simp
      ring
  | full => exact image_full_param_Ioo

private theorem tendsto_bounded_neg_one (a b : ℝ) :
    Filter.Tendsto (bounded a b).param (𝓝[Ioo (-1) 1] (-1)) (𝓝 a) := by
  have hc : Continuous (bounded a b).param := by unfold param; fun_prop
  have hev : (bounded a b).param (-1) = a := by unfold param; ring
  exact (hev ▸ hc.tendsto (-1)).mono_left nhdsWithin_le_nhds

private theorem tendsto_bounded_one (a b : ℝ) :
    Filter.Tendsto (bounded a b).param (𝓝[Ioo (-1) 1] 1) (𝓝 b) := by
  have hc : Continuous (bounded a b).param := by unfold param; fun_prop
  have hev : (bounded a b).param 1 = b := by unfold param; ring
  exact (hev ▸ hc.tendsto 1).mono_left nhdsWithin_le_nhds

private theorem tendsto_fromPoint_neg_one (a : ℝ) :
    Filter.Tendsto (fromPoint a).param (𝓝[Ioo (-1) 1] (-1)) (𝓝 a) := by
  have hc : ContinuousAt (fromPoint a).param (-1) := by
    unfold param
    exact continuousAt_const.add (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
  have hev : (fromPoint a).param (-1) = a := by unfold param; norm_num
  exact (hev ▸ hc.tendsto).mono_left nhdsWithin_le_nhds

private theorem tendsto_toPoint_one (b : ℝ) :
    Filter.Tendsto (toPoint b).param (𝓝[Ioo (-1) 1] 1) (𝓝 b) := by
  have hc : ContinuousAt (toPoint b).param 1 := by
    unfold param
    exact continuousAt_const.sub (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
  have hev : (toPoint b).param 1 = b := by unfold param; norm_num
  exact (hev ▸ hc.tendsto).mono_left nhdsWithin_le_nhds

private theorem tendsto_fromPoint_atTop (a : ℝ) :
    Filter.Tendsto (fromPoint a).param (𝓝[Ioo (-1) 1] 1) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  set δ := min (1 : ℝ) (1 / (max (M - a) 0 + 1))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds 1 hδ), self_mem_nhdsWithin]
    with u hu hIoo
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
  have hu0 : 0 < u := by linarith [min_le_left (1 : ℝ) (1 / (max (M - a) 0 + 1)), hu.1]
  have h1u : 0 < 1 - u := by linarith [hIoo.2]
  have hle : 1 - u < 1 / (max (M - a) 0 + 1) :=
    (by linarith [hu.1] : 1 - u < δ).trans_le (min_le_right _ _)
  have hmul : (max (M - a) 0 + 1) * (1 - u) < 1 :=
    (mul_lt_mul_of_pos_left hle (by positivity)).trans_eq (mul_one_div_cancel (by positivity))
  have hdiv : max (M - a) 0 + 1 < (1 + u) / (1 - u) := by
    rw [lt_div_iff₀ h1u]
    linarith
  simp only [param]
  linarith [le_max_left (M - a) 0]

private theorem tendsto_toPoint_atBot (b : ℝ) :
    Filter.Tendsto (toPoint b).param (𝓝[Ioo (-1) 1] (-1)) Filter.atBot := by
  have hneg : Filter.Tendsto (fun u : ℝ ↦ -u) (𝓝 (-1)) (𝓝 1) := by
    simpa using continuous_neg.tendsto (-1 : ℝ)
  have ht : Filter.Tendsto (fun u : ℝ ↦ -u) (𝓝[Ioo (-1) 1] (-1)) (𝓝[Ioo (-1) 1] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hneg.mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset self_mem_nhdsWithin
        fun u hu ↦ ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  refine ((Filter.tendsto_neg_atTop_atBot.comp (tendsto_fromPoint_atTop (-b))).comp ht).congr'
    (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [Function.comp_apply, param]
  ring

private theorem tendsto_full_atTop :
    Filter.Tendsto full.param (𝓝[Ioo (-1) 1] 1) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  set δ := min (1 / 2 : ℝ) (1 / (4 * (max M 0 + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds 1 hδ), self_mem_nhdsWithin]
    with u hu hIoo
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
  have hu_half : 1 / 2 < u := by
    linarith [min_le_left (1 / 2 : ℝ) (1 / (4 * (max M 0 + 1))), hu.1]
  have h1u2 : 0 < 1 - u ^ 2 := by nlinarith [hIoo.1, hIoo.2]
  have hle : 1 - u < 1 / (4 * (max M 0 + 1)) :=
    (by linarith [hu.1] : 1 - u < δ).trans_le (min_le_right _ _)
  have h1 : 4 * (max M 0 + 1) * (1 - u) < 1 :=
    (mul_lt_mul_of_pos_left hle (by positivity)).trans_eq (mul_one_div_cancel (by positivity))
  have hdiv : max M 0 + 1 < u / (1 - u ^ 2) :=
    (lt_div_iff₀ h1u2).2 (by nlinarith [hIoo.2, le_max_right M 0])
  simp only [param]
  linarith [le_max_left M 0]

private theorem tendsto_full_atBot :
    Filter.Tendsto full.param (𝓝[Ioo (-1) 1] (-1)) Filter.atBot := by
  have hneg : Filter.Tendsto (fun u : ℝ ↦ -u) (𝓝 (-1)) (𝓝 1) := by
    simpa using continuous_neg.tendsto (-1 : ℝ)
  have ht : Filter.Tendsto (fun u : ℝ ↦ -u) (𝓝[Ioo (-1) 1] (-1)) (𝓝[Ioo (-1) 1] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hneg.mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset self_mem_nhdsWithin
        fun u hu ↦ ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  refine ((Filter.tendsto_neg_atTop_atBot.comp tendsto_full_atTop).comp ht).congr'
    (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [Function.comp_apply, param, neg_sq, neg_div, neg_neg]

end EdgeInterval

/-! ### Side and half-side parameter intervals -/

section Intervals

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

open scoped Classical in
private def startParam (P : ConvexPolygon n) (i : Fin n) : ℝ :=
  if h : ∃ v, P.vertex i = .inl v then
    Classical.choose ((h.choose_spec ▸ P.isGeodesicFromTo_sideGeodesic i).left_mem_range)
  else 0

private theorem geodesicLine_startParam {i : Fin n} {v : ℍ} (hv : P.vertex i = .inl v) :
    geodesicLine (P.sideGeodesic i) (startParam P i) = v := by
  have hex : ∃ v', P.vertex i = .inl v' := ⟨v, hv⟩
  rw [startParam, dite_eq_left hex]
  have hspec := Classical.choose_spec
    ((hex.choose_spec ▸ P.isGeodesicFromTo_sideGeodesic i).left_mem_range)
  exact hspec.trans (Sum.inl.inj (hex.choose_spec.symm.trans hv))

open scoped Classical in
private def endParam (P : ConvexPolygon n) (i : Fin n) : ℝ :=
  if h : ∃ w, P.vertex (i + 1) = .inl w then
    Classical.choose ((h.choose_spec ▸ P.isGeodesicFromTo_sideGeodesic i).right_mem_range)
  else 0

private theorem geodesicLine_endParam {i : Fin n} {w : ℍ} (hw : P.vertex (i + 1) = .inl w) :
    geodesicLine (P.sideGeodesic i) (endParam P i) = w := by
  have hex : ∃ w', P.vertex (i + 1) = .inl w' := ⟨w, hw⟩
  rw [endParam, dite_eq_left hex]
  have hspec := Classical.choose_spec
    ((hex.choose_spec ▸ P.isGeodesicFromTo_sideGeodesic i).right_mem_range)
  exact hspec.trans (Sum.inl.inj (hex.choose_spec.symm.trans hw))

private theorem startParam_lt_endParam {i : Fin n} {v w : ℍ}
    (hv : P.vertex i = .inl v) (hw : P.vertex (i + 1) = .inl w) :
    startParam P i < endParam P i := by
  have hg := P.isGeodesicFromTo_sideGeodesic i
  rw [hv, hw] at hg
  obtain ⟨s, t, hst, hs, ht⟩ := isGeodesicFromTo_inl_inl.1 hg
  rwa [geodesicLine_injective _ ((geodesicLine_startParam hv).trans hs.symm),
    geodesicLine_injective _ ((geodesicLine_endParam hw).trans ht.symm)]

private def sideInterval (P : ConvexPolygon n) (i : Fin n) : EdgeInterval :=
  match P.vertex i, P.vertex (i + 1) with
  | .inl _, .inl _ => .bounded (startParam P i) (endParam P i)
  | .inl _, .inr _ => .fromPoint (startParam P i)
  | .inr _, .inl _ => .toPoint (endParam P i)
  | .inr _, .inr _ => .full

private theorem mem_side_and_ne_endpoints_iff_mem_sideInterval {i : Fin n} {z : ℍ} :
    (z ∈ P.side i ∧ P.vertex i ≠ .inl z ∧ P.vertex (i + 1) ≠ .inl z) ↔
      ∃ t ∈ (sideInterval P i).openSet, geodesicLine (P.sideGeodesic i) t = z := by
  have hg := P.isGeodesicFromTo_sideGeodesic i
  unfold sideInterval
  rcases hp : P.vertex i with v | ξ <;> rcases hq : P.vertex (i + 1) with w | η
  · rw [P.side_def, hp, hq, extGeodesicSegment_inl_inl, ← geodesicLine_startParam hp,
      ← geodesicLine_endParam hq, geodesicSegment_geodesicLine,
      uIcc_of_le (startParam_lt_endParam hp hq).le]
    simp only [EdgeInterval.openSet, mem_Ioo, mem_image, mem_Icc, ne_eq, Sum.inl.injEq]
    constructor
    · rintro ⟨⟨t, ⟨ht₁, ht₂⟩, rfl⟩, hne₁, hne₂⟩
      exact ⟨t, ⟨ht₁.lt_of_ne fun h ↦ hne₁ (congrArg _ h),
        ht₂.lt_of_ne fun h ↦ hne₂ (congrArg _ h.symm)⟩, rfl⟩
    · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
      exact ⟨⟨t, ⟨ht₁.le, ht₂.le⟩, rfl⟩, fun h ↦ ht₁.ne (geodesicLine_injective _ h),
        fun h ↦ ht₂.ne' (geodesicLine_injective _ h)⟩
  · have hg' := hg
    rw [hp, hq] at hg'
    obtain ⟨_, hinf⟩ := isGeodesicFromTo_inl_inr.1 hg'
    rw [P.side_def, hp, hq, ← geodesicLine_startParam hp, ← hinf, ← geodesicLine_image_Ici]
    simp only [EdgeInterval.openSet, mem_Ioi, mem_image, mem_Ici, ne_eq, Sum.inl.injEq,
      reduceCtorEq, not_false_eq_true, and_true]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hne⟩
      exact ⟨t, ht.lt_of_ne fun h ↦ hne (congrArg _ h), rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.le, rfl⟩, fun h ↦ ht.ne (geodesicLine_injective _ h)⟩
  · have hg' := hg
    rw [hp, hq] at hg'
    obtain ⟨h0, _⟩ := isGeodesicFromTo_inr_inl.1 hg'
    rw [P.side_def, hp, hq, ← h0, ← geodesicLine_endParam hq, ← geodesicLine_image_Iic]
    simp only [EdgeInterval.openSet, mem_Iio, mem_image, mem_Iic, ne_eq, Sum.inl.injEq,
      reduceCtorEq, not_false_eq_true, true_and]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hne⟩
      exact ⟨t, ht.lt_of_ne fun h ↦ hne (congrArg _ h.symm), rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.le, rfl⟩, fun h ↦ ht.ne' (geodesicLine_injective _ h)⟩
  · have hg' := hg
    rw [hp, hq] at hg'
    obtain ⟨h0, hinf⟩ := isGeodesicFromTo_inr_inr.1 hg'
    rw [P.side_def, hp, hq, ← h0, ← hinf, ← range_geodesicLine_eq_extGeodesicSegment]
    simp [EdgeInterval.openSet, mem_range]

private def midParam {i : Fin n} (hi : σ.pair i = i) : ℝ :=
  Classical.choose (P.side_subset_range_sideGeodesic i
    (σ.selfPairedSideFixedPoint_spec ⟨i, hi⟩).1)

private theorem geodesicLine_midParam {i : Fin n} (hi : σ.pair i = i) :
    geodesicLine (P.sideGeodesic i) (σ.midParam hi) = σ.selfPairedSideFixedPoint ⟨i, hi⟩ :=
  Classical.choose_spec (P.side_subset_range_sideGeodesic i
    (σ.selfPairedSideFixedPoint_spec ⟨i, hi⟩).1)

private theorem map_smul_geodesicLine_of_pair_eq {i : Fin n} (hi : σ.pair i = i) (t : ℝ) :
    σ.map i • geodesicLine (P.sideGeodesic i) t =
      geodesicLine (P.sideGeodesic i) (2 * σ.midParam hi - t) := by
  have hg := (P.isGeodesicFromTo_sideGeodesic i).smul (σ.map i)
  rw [σ.map_smul_vertex, σ.map_smul_vertex_add_one, hi] at hg
  obtain ⟨r, hr⟩ := (isGeodesicFromTo_mul_pslS_iff.mpr
    (P.isGeodesicFromTo_sideGeodesic i)).exists_eq_mul_dilation hg
  have hact (u : ℝ) : σ.map i • geodesicLine (P.sideGeodesic i) u =
      geodesicLine (P.sideGeodesic i) (-(r + u)) := by
    rw [smul_geodesicLine, hr, geodesicLine_mul_dilation, geodesicLine_mul_pslS]
  have hfix : σ.map i • geodesicLine (P.sideGeodesic i) (-r / 2) =
      geodesicLine (P.sideGeodesic i) (-r / 2) := by
    rw [hact]
    congr 1
    ring
  have hm : σ.midParam hi = -r / 2 :=
    geodesicLine_injective _
      ((σ.geodesicLine_midParam hi).trans (σ.selfPairedSideFixedPoint_eq ⟨i, hi⟩ hfix))
  rw [hact, hm]
  congr 1
  ring

private theorem midParam_eq_avg {i : Fin n} (hi : σ.pair i = i) {v : ℍ}
    (hv : P.vertex i = .inl v) :
    ∃ w : ℍ, P.vertex (i + 1) = .inl w ∧
      σ.midParam hi = (startParam P i + endParam P i) / 2 := by
  have hw : P.vertex (i + 1) = .inl (σ.map i • v) := by
    simpa [hi, hv] using (σ.map_smul_vertex i).symm
  refine ⟨σ.map i • v, hw, ?_⟩
  have h1 : geodesicLine (P.sideGeodesic i) (2 * σ.midParam hi - startParam P i) =
      geodesicLine (P.sideGeodesic i) (endParam P i) := by
    rw [← σ.map_smul_geodesicLine_of_pair_eq hi, geodesicLine_startParam hv,
      geodesicLine_endParam hw]
  linarith [geodesicLine_injective _ h1]

private theorem startParam_lt_midParam {i : Fin n} (hi : σ.pair i = i) {v : ℍ}
    (hv : P.vertex i = .inl v) : startParam P i < σ.midParam hi := by
  obtain ⟨w, hw, hm⟩ := σ.midParam_eq_avg hi hv
  linarith [startParam_lt_endParam hv hw]

private def edgeInterval (i : Fin n) : EdgeInterval :=
  if hi : σ.pair i = i then
    match P.vertex i with
    | .inl _ => .bounded (startParam P i) (σ.midParam hi)
    | .inr _ => .toPoint (σ.midParam hi)
  else
    sideInterval P i

private theorem valid_edgeInterval (i : Fin n) : (σ.edgeInterval i).Valid := by
  unfold edgeInterval
  split_ifs with hi
  · rcases hp : P.vertex i with v | ξ
    · exact σ.startParam_lt_midParam hi hp
    · trivial
  · unfold sideInterval
    rcases hp : P.vertex i with v | ξ <;> rcases hq : P.vertex (i + 1) with w | η
    · exact startParam_lt_endParam hp hq
    · trivial
    · trivial
    · trivial

private theorem edgeInterval_subset_sideInterval (i : Fin n) :
    (σ.edgeInterval i).openSet ⊆ (sideInterval P i).openSet := by
  intro t ht
  unfold edgeInterval at ht
  split_ifs at ht with hi
  · unfold sideInterval
    rcases hp : P.vertex i with v | ξ
    · obtain ⟨w, hw, hm⟩ := σ.midParam_eq_avg hi hp
      rw [hp] at ht
      rw [hw]
      simp only [EdgeInterval.openSet, mem_Ioo] at ht ⊢
      exact ⟨ht.1, by linarith [startParam_lt_endParam hp hw, ht.2]⟩
    · have hq : P.vertex (i + 1) = .inr (σ.map i • ξ) := by
        simpa [hi, hp] using (σ.map_smul_vertex i).symm
      rw [hq]
      simp [EdgeInterval.openSet]
  · exact ht

private theorem geodesicLine_mem_side_of_mem_edgeInterval {i : Fin n} {t : ℝ}
    (ht : t ∈ (σ.edgeInterval i).openSet) :
    geodesicLine (P.sideGeodesic i) t ∈ P.side i ∧
      (∀ k, P.vertex k ≠ .inl (geodesicLine (P.sideGeodesic i) t)) ∧
      ∀ hi : σ.pair i = i, t < σ.midParam hi := by
  obtain ⟨hside, hne₁, hne₂⟩ :=
    mem_side_and_ne_endpoints_iff_mem_sideInterval.2
      ⟨t, σ.edgeInterval_subset_sideInterval i ht, rfl⟩
  refine ⟨hside, fun k hk ↦ ?_, fun hi ↦ ?_⟩
  · rcases P.eq_or_eq_add_one_of_vertex_eq_inl_of_mem_side hk hside with rfl | rfl
    · exact hne₁ hk
    · exact hne₂ hk
  · unfold edgeInterval at ht
    rw [dite_eq_left hi] at ht
    rcases hp : P.vertex i with v | ξ <;> rw [hp] at ht
    · exact ht.2
    · exact ht

/-! ### The public `edgeArc` API -/

/-- The open `1`-cell arc carried by side `i` of `(P, σ)`, parametrized on `Ioo (-1 : ℝ) 1` along
`P.sideGeodesic i`. When `σ.pair i ≠ i`, its image on `Ioo (-1) 1` is `P.side i` minus any finite
endpoints; when `σ.pair i = i`, its image is the open half-side between `P.vertex i` and
`σ.selfPairedSideFixedPoint ⟨i, hi⟩`. -/
def edgeArc (i : Fin n) (u : ℝ) : ℍ :=
  geodesicLine (P.sideGeodesic i) ((σ.edgeInterval i).param u)

private theorem param_mem_edgeInterval (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    (σ.edgeInterval i).param u ∈ (σ.edgeInterval i).openSet := by
  rw [← (σ.edgeInterval i).image_param_Ioo (σ.valid_edgeInterval i)]
  exact ⟨u, hu, rfl⟩

/-- `σ.edgeArc i` is continuous on `Ioo (-1) 1`. -/
theorem continuousOn_edgeArc (i : Fin n) : ContinuousOn (σ.edgeArc i) (Ioo (-1) 1) :=
  (isometry_geodesicLine _).continuous.comp_continuousOn (σ.edgeInterval i).continuousOn_param

/-- `σ.edgeArc i` is injective on `Ioo (-1) 1`. -/
theorem injOn_edgeArc (i : Fin n) : InjOn (σ.edgeArc i) (Ioo (-1) 1) :=
  (geodesicLine_injective _).comp_injOn
    ((σ.edgeInterval i).injOn_param (σ.valid_edgeInterval i))

/-- Every point of `σ.edgeArc i` on `Ioo (-1) 1` lies on `P.side i`. -/
theorem edgeArc_mem_side (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    σ.edgeArc i u ∈ P.side i :=
  (σ.geodesicLine_mem_side_of_mem_edgeInterval (σ.param_mem_edgeInterval i hu)).1

/-- No point of `σ.edgeArc i` on `Ioo (-1) 1` is a finite vertex of `P`. -/
theorem vertex_ne_inl_edgeArc (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1) (k : Fin n) :
    P.vertex k ≠ .inl (σ.edgeArc i u) :=
  (σ.geodesicLine_mem_side_of_mem_edgeInterval (σ.param_mem_edgeInterval i hu)).2.1 k

/-- No point of `σ.edgeArc i` on `Ioo (-1) 1` equals the fixed point of a self-paired side. -/
theorem edgeArc_ne_selfPairedSideFixedPoint (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1)
    (j : {k : Fin n // σ.pair k = k}) :
    σ.edgeArc i u ≠ σ.selfPairedSideFixedPoint j := by
  intro h
  rcases j with ⟨j, hjj⟩
  have hmem := σ.param_mem_edgeInterval i hu
  obtain ⟨hside, -, hmid⟩ := σ.geodesicLine_mem_side_of_mem_edgeInterval hmem
  obtain ⟨hs_j, hp_j, hq_j, -⟩ := σ.selfPairedSideFixedPoint_spec ⟨j, hjj⟩
  rw [edgeArc] at h
  have hside' : σ.selfPairedSideFixedPoint ⟨j, hjj⟩ ∈ P.side i := h ▸ hside
  obtain rfl := P.eq_of_mem_side_of_mem_side hs_j hp_j hq_j hside'
  rw [← σ.geodesicLine_midParam hjj] at h
  exact (hmid hjj).ne (geodesicLine_injective _ h)

/-- No side-paired image `σ.map i • σ.edgeArc i u` (`u ∈ Ioo (-1) 1`) equals the fixed point of a
self-paired side. -/
theorem map_smul_edgeArc_ne_selfPairedSideFixedPoint (i : Fin n) {u : ℝ} (hu : u ∈ Ioo (-1) 1)
    (j : {k : Fin n // σ.pair k = k}) :
    σ.map i • σ.edgeArc i u ≠ σ.selfPairedSideFixedPoint j := by
  intro h
  have hmem := σ.param_mem_edgeInterval i hu
  obtain ⟨hside, -, hmid⟩ := σ.geodesicLine_mem_side_of_mem_edgeInterval hmem
  obtain ⟨hs_j, hp_j, hq_j, -⟩ := σ.selfPairedSideFixedPoint_spec j
  have hms : σ.selfPairedSideFixedPoint j ∈ P.side (σ.pair i) :=
    h ▸ σ.map_smul_mem_side hside
  have hj_eq : j.1 = σ.pair i := P.eq_of_mem_side_of_mem_side hs_j hp_j hq_j hms
  have hij : j.1 = i := by
    have h1 := congrArg σ.pair hj_eq
    rwa [j.2, σ.pair_pair] at h1
  have hii : σ.pair i = i := hj_eq.symm.trans hij
  have hj_sub : j = ⟨i, hii⟩ := Subtype.ext hij
  rw [hj_sub, ← σ.geodesicLine_midParam hii, edgeArc, σ.map_smul_geodesicLine_of_pair_eq hii] at h
  linarith [geodesicLine_injective _ h, hmid hii]

/-- On a self-paired side `i`, the image of `Ioo (-1) 1` under `σ.edgeArc i` is disjoint from its
image under `σ.map i`. -/
theorem map_smul_edgeArc_ne_edgeArc_of_pair_eq {i : Fin n} (hi : σ.pair i = i) {u v : ℝ}
    (hu : u ∈ Ioo (-1) 1) (hv : v ∈ Ioo (-1) 1) :
    σ.map i • σ.edgeArc i u ≠ σ.edgeArc i v := by
  intro h
  rw [edgeArc, edgeArc, σ.map_smul_geodesicLine_of_pair_eq hi] at h
  have h1 := (σ.geodesicLine_mem_side_of_mem_edgeInterval (σ.param_mem_edgeInterval i hu)).2.2 hi
  have h2 := (σ.geodesicLine_mem_side_of_mem_edgeInterval (σ.param_mem_edgeInterval i hv)).2.2 hi
  linarith [geodesicLine_injective _ h]

/-- Every point of `P.side j` away from its finite endpoints lies on `σ.edgeArc j '' Ioo (-1) 1`,
equals `σ.selfPairedSideFixedPoint ⟨j, hj⟩`, or is sent into `σ.edgeArc j '' Ioo (-1) 1` by
`σ.map j`. -/
theorem mem_image_edgeArc_or_selfPaired_of_mem_side {j : Fin n} {z : ℍ}
    (hz : z ∈ P.side j) (hzp : P.vertex j ≠ .inl z) (hzq : P.vertex (j + 1) ≠ .inl z) :
    z ∈ σ.edgeArc j '' Ioo (-1) 1 ∨
      ∃ hj : σ.pair j = j, z = σ.selfPairedSideFixedPoint ⟨j, hj⟩ ∨
        σ.map j • z ∈ σ.edgeArc j '' Ioo (-1) 1 := by
  have hcomp : σ.edgeArc j = geodesicLine (P.sideGeodesic j) ∘ (σ.edgeInterval j).param := rfl
  have himg : σ.edgeArc j '' Ioo (-1) 1 =
      geodesicLine (P.sideGeodesic j) '' (σ.edgeInterval j).openSet := by
    rw [hcomp, image_comp, (σ.edgeInterval j).image_param_Ioo (σ.valid_edgeInterval j)]
  rw [himg]
  obtain ⟨t, ht, rfl⟩ := mem_side_and_ne_endpoints_iff_mem_sideInterval.1 ⟨hz, hzp, hzq⟩
  by_cases hj : σ.pair j = j
  · rcases lt_trichotomy t (σ.midParam hj) with hlt | rfl | hgt
    · left
      refine ⟨t, ?_, rfl⟩
      unfold edgeInterval
      rw [dite_eq_left hj]
      unfold sideInterval at ht
      rcases hp : P.vertex j with v | ξ
      · obtain ⟨w, hw, _⟩ := σ.midParam_eq_avg hj hp
        rw [hp, hw] at ht
        exact ⟨ht.1, hlt⟩
      · exact hlt
    · exact Or.inr ⟨hj, Or.inl (σ.geodesicLine_midParam hj)⟩
    · refine Or.inr ⟨hj, Or.inr ⟨2 * σ.midParam hj - t, ?_,
        (σ.map_smul_geodesicLine_of_pair_eq hj t).symm⟩⟩
      unfold edgeInterval
      rw [dite_eq_left hj]
      unfold sideInterval at ht
      rcases hp : P.vertex j with v | ξ
      · obtain ⟨w, hw, hm⟩ := σ.midParam_eq_avg hj hp
        rw [hp, hw] at ht
        exact ⟨by linarith [ht.2], by linarith⟩
      · simp only [EdgeInterval.openSet, mem_Iio]
        linarith
  · left
    exact ⟨t, by simpa [edgeInterval, hj] using ht, rfl⟩

/-- At a finite starting vertex `P.vertex i = .inl v`, `σ.edgeArc i u → v` as `u → -1` within
`Ioo (-1) 1`. -/
theorem tendsto_edgeArc_neg_one_of_eq_inl {i : Fin n} {v : ℍ} (hv : P.vertex i = .inl v) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] (-1)) (𝓝 v) := by
  rw [← geodesicLine_startParam hv]
  refine ((isometry_geodesicLine _).continuous.tendsto _).comp ?_
  unfold edgeInterval
  split_ifs with hi
  · rw [hv]
    exact EdgeInterval.tendsto_bounded_neg_one _ _
  · unfold sideInterval
    rw [hv]
    rcases P.vertex (i + 1) with _ | _
    · exact EdgeInterval.tendsto_bounded_neg_one _ _
    · exact EdgeInterval.tendsto_fromPoint_neg_one _

/-- At an ideal starting vertex `P.vertex i = .inr ξ` sent to `∞` by `g : PSL(2, ℝ)`, the horodisc
height `(g • σ.edgeArc i u).im` tends to `∞` as `u → -1` within `Ioo (-1) 1`. -/
theorem tendsto_edgeArc_neg_one_atImInfty_of_eq_inr {i : Fin n} {ξ : OnePoint ℝ} {g : PSL(2, ℝ)}
    (hξ : P.vertex i = .inr ξ) (hg : g • ξ = ∞) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] (-1))
      (Filter.comap (fun z : ℍ ↦ (g • z).im) Filter.atTop) := by
  have hbot : Filter.Tendsto (σ.edgeInterval i).param (𝓝[Ioo (-1) 1] (-1)) Filter.atBot := by
    unfold edgeInterval
    split_ifs with hi
    · rw [hξ]
      exact EdgeInterval.tendsto_toPoint_atBot _
    · unfold sideInterval
      rw [hξ]
      rcases P.vertex (i + 1) with _ | _
      · exact EdgeInterval.tendsto_toPoint_atBot _
      · exact EdgeInterval.tendsto_full_atBot
  have hside := P.isGeodesicFromTo_sideGeodesic i
  rw [hξ] at hside
  have hg0 : (g * P.sideGeodesic i) • ((0 : ℝ) : OnePoint ℝ) = ∞ := by
    rw [mul_smul, hside.smul_zero_eq, hg]
  have him : Filter.Tendsto (geodesicLine (P.sideGeodesic i)) Filter.atBot
      (Filter.comap (fun z : ℍ ↦ (g • z).im) Filter.atTop) := by
    rw [Filter.tendsto_comap_iff]
    exact (Filter.tendsto_comap_iff.1 (tendsto_geodesicLine_atBot_atImInfty hg0)).congr
      fun t ↦ by rw [Function.comp_apply, Function.comp_apply, smul_geodesicLine]
  exact him.comp hbot

/-- On a self-paired side `i`, `σ.edgeArc i u → σ.selfPairedSideFixedPoint ⟨i, hi⟩` as `u → 1`
within `Ioo (-1) 1`. -/
theorem tendsto_edgeArc_one_of_pair_eq {i : Fin n} (hi : σ.pair i = i) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] 1)
      (𝓝 (σ.selfPairedSideFixedPoint ⟨i, hi⟩)) := by
  rw [← σ.geodesicLine_midParam hi]
  refine ((isometry_geodesicLine _).continuous.tendsto _).comp ?_
  unfold edgeInterval
  rw [dite_eq_left hi]
  rcases P.vertex i with _ | _
  · exact EdgeInterval.tendsto_bounded_one _ _
  · exact EdgeInterval.tendsto_toPoint_one _

/-- On a non-self-paired side `i` with finite end vertex `P.vertex (i + 1) = .inl w`,
`σ.edgeArc i u → w` as `u → 1` within `Ioo (-1) 1`. -/
theorem tendsto_edgeArc_one_of_eq_inl {i : Fin n} {w : ℍ} (hi : σ.pair i ≠ i)
    (hw : P.vertex (i + 1) = .inl w) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] 1) (𝓝 w) := by
  rw [← geodesicLine_endParam hw]
  refine ((isometry_geodesicLine _).continuous.tendsto _).comp ?_
  unfold edgeInterval
  rw [dite_eq_right hi]
  unfold sideInterval
  rw [hw]
  rcases P.vertex i with _ | _
  · exact EdgeInterval.tendsto_bounded_one _ _
  · exact EdgeInterval.tendsto_toPoint_one _

/-- On a non-self-paired side `i` with ideal end vertex `P.vertex (i + 1) = .inr η` sent to `∞`
by `g : PSL(2, ℝ)`, `(g • σ.edgeArc i u).im → ∞` as `u → 1` within `Ioo (-1) 1`. -/
theorem tendsto_edgeArc_one_atImInfty_of_eq_inr {i : Fin n} {η : OnePoint ℝ} {g : PSL(2, ℝ)}
    (hi : σ.pair i ≠ i) (hη : P.vertex (i + 1) = .inr η) (hg : g • η = ∞) :
    Filter.Tendsto (σ.edgeArc i) (𝓝[Ioo (-1) 1] 1)
      (Filter.comap (fun z : ℍ ↦ (g • z).im) Filter.atTop) := by
  have htop : Filter.Tendsto (σ.edgeInterval i).param (𝓝[Ioo (-1) 1] 1) Filter.atTop := by
    unfold edgeInterval
    rw [dite_eq_right hi]
    unfold sideInterval
    rw [hη]
    rcases P.vertex i with _ | _
    · exact EdgeInterval.tendsto_fromPoint_atTop _
    · exact EdgeInterval.tendsto_full_atTop
  have hside := P.isGeodesicFromTo_sideGeodesic i
  rw [hη] at hside
  have hginf : (g * P.sideGeodesic i) • (∞ : OnePoint ℝ) = ∞ := by
    rw [mul_smul, hside.smul_infty_eq, hg]
  have him : Filter.Tendsto (geodesicLine (P.sideGeodesic i)) Filter.atTop
      (Filter.comap (fun z : ℍ ↦ (g • z).im) Filter.atTop) := by
    rw [Filter.tendsto_comap_iff]
    exact (Filter.tendsto_comap_iff.1 (tendsto_geodesicLine_atTop_atImInfty hginf)).congr
      fun t ↦ by rw [Function.comp_apply, Function.comp_apply, smul_geodesicLine]
  exact him.comp htop

end Intervals

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

end
