/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import Mathlib.Analysis.Complex.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.PlaneSeparation.TwoComponents
import TauCeti.Analysis.Contour.Winding.Separation

/-!
# Complementary components at a straight point of a Jordan curve

If a Jordan curve agrees locally with a line at one point, points on opposite sides of the
straight piece lie in different components of the complement, by the segment-crossing theorem
`TauCeti.Contour.notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton`, while points
on the same local side lie in the same component. Since the inside of a Jordan curve is a single
complementary component (`TauCeti.IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn`),
exactly one of the two sides lies inside the curve. This identifies the inside of a simple polygon
locally at any point of one of its sides.

An interior point of a nondegenerate straight segment has a ball in which the segment
agrees with its supporting line. This supplies the local line hypothesis for polygonal curves.

## Main results

* `TauCeti.exists_ball_openSegment_eq_line` -- near an interior point of a segment, the segment
  agrees with its supporting line.
* `TauCeti.IsJordanCurve.notMem_connectedComponentIn_of_locally_eq_line` -- points on opposite
  sides of a straight piece lie in different complementary components.
* `TauCeti.mem_connectedComponentIn_of_locally_subset_line_of_im_pos` -- points on the same local
  side of a line lie in the same complementary component.
* `TauCeti.IsJordanCurve.mem_filledHull_iff_notMem_filledHull_of_locally_eq_line` -- exactly one
  of the two sides lies inside the curve.

## References

* K. Borsuk, *Über Schnitte der euklidischen Räume*, Math. Ann. **106** (1932), 239–248.
* J. R. Munkres, *Topology*, Sections 61--63.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Bornology Complex Filter Metric Set Topology

namespace TauCeti

/-- Near an interior point of a nondegenerate complex line segment, the segment agrees with
its supporting real line. The line is expressed in the coordinate obtained by dividing by
`b - a`. -/
theorem exists_ball_openSegment_eq_line {a b w : ℂ}
    (hab : a ≠ b) (hw : w ∈ openSegment ℝ a b) :
    ∃ r > 0, ∀ z ∈ ball w r,
      (z ∈ openSegment ℝ a b ↔ (((b - a)⁻¹ * (z - w))).im = 0) := by
  obtain ⟨t, ht, hwt⟩ := (openSegment_eq_image' ℝ a b ▸ hw)
  let u : ℂ → ℝ := fun z => t + ((b - a)⁻¹ * (z - w)).re
  have hucont : Continuous u := by
    fun_prop
  have huw : u w = t := by simp [u]
  have hnhds : {z | u z ∈ Ioo (0 : ℝ) 1} ∈ 𝓝 w := by
    exact (isOpen_Ioo.preimage hucont).mem_nhds (by simpa [huw] using ht)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨r, hr, fun z hz => ?_⟩
  have huz : u z ∈ Ioo (0 : ℝ) 1 := hball hz
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hw' : w = a + (t : ℂ) * (b - a) := by
    simpa only [Complex.real_smul] using hwt.symm
  constructor
  · intro hseg
    obtain ⟨s, _, hzs⟩ := (openSegment_eq_image' ℝ a b ▸ hseg)
    have hz' : z = a + (s : ℂ) * (b - a) := by
      simpa only [Complex.real_smul] using hzs.symm
    rw [hz', hw']
    have heq : (b - a)⁻¹ * ((a + (s : ℂ) * (b - a)) -
        (a + (t : ℂ) * (b - a))) = ((s - t : ℝ) : ℂ) := by
      push_cast
      field_simp
      ring
    rw [heq]
    simp
  · intro hline
    have heq : (b - a)⁻¹ * (z - w) = (((b - a)⁻¹ * (z - w)).re : ℂ) :=
      Complex.ext (by simp) (by simpa using hline)
    have hz' : z = a + (u z : ℂ) * (b - a) := by
      have hm := congrArg (fun y : ℂ => y * (b - a)) heq
      have hm' : z - w = (((b - a)⁻¹ * (z - w)).re : ℂ) * (b - a) := by
        calc
          z - w = ((b - a)⁻¹ * (z - w)) * (b - a) := by
            field_simp
          _ = _ := hm
      calc
        z = w + (z - w) := by ring
        _ = w + (((b - a)⁻¹ * (z - w)).re : ℂ) * (b - a) :=
          congrArg (fun y : ℂ => w + y) hm'
        _ = a + (t : ℂ) * (b - a) +
            (((b - a)⁻¹ * (z - w)).re : ℂ) * (b - a) :=
          congrArg (fun y : ℂ => y + (((b - a)⁻¹ * (z - w)).re : ℂ) * (b - a)) hw'
        _ = a + (u z : ℂ) * (b - a) := by simp only [u, ofReal_add, add_mul]; ring
    rw [openSegment_eq_image']
    exact ⟨u z, huz, by simpa only [Complex.real_smul] using hz'.symm⟩

/-! ### A straight piece of a Jordan curve separates its two sides -/

/-- A point whose coordinate `v * (z - p)` is shorter than `r * ‖v‖` lies in `ball p r`. -/
private theorem mem_ball_of_norm_mul_sub_lt {p v z : ℂ} {r : ℝ}
    (hz : ‖v * (z - p)‖ < r * ‖v‖) : z ∈ ball p r := by
  rw [mem_ball, dist_eq_norm]
  rw [norm_mul, mul_comm] at hz
  exact lt_of_mul_lt_mul_right hz (norm_nonneg v)

/-- Two points of `ball p r` on the same open side of a line through `p` lie in the same
component of the complement of a curve contained in that line within `ball p r`: the open
half-ball between them is convex and misses the curve. -/
theorem mem_connectedComponentIn_of_locally_subset_line_of_im_pos
    {C : Set ℂ} {p v x y : ℂ} {r : ℝ}
    (hline : ∀ z ∈ ball p r, z ∈ C → (v * (z - p)).im = 0) (hx : x ∈ ball p r)
    (hy : y ∈ ball p r) (hx' : 0 < (v * (x - p)).im) (hy' : 0 < (v * (y - p)).im) :
    y ∈ connectedComponentIn Cᶜ x := by
  have hside : {z : ℂ | 0 < (v * (z - p)).im} = {z | (v * p).im < (v * z).im} := by
    ext z
    simp [mul_sub]
  have hS : Convex ℝ (ball p r ∩ {z : ℂ | 0 < (v * (z - p)).im}) := by
    rw [hside]
    exact (convex_ball p r).inter
      (convex_halfSpace_gt (Complex.imLm.comp (LinearMap.mulLeft ℝ v)).isLinear _)
  exact hS.isPreconnected.subset_connectedComponentIn ⟨hx, hx'⟩
    (by
      rintro z ⟨hz₁, hz₂⟩ hzC
      have hz₂' : 0 < (v * (z - p)).im := hz₂
      exact hz₂'.ne' (hline z hz₁ hzC)) ⟨hy, hy'⟩

/-- For `0 < s < r * ‖v‖`, the point `p + I * s / v` lies in `ball p r`, on the positive side of
the line `{z | (v * (z - p)).im = 0}`. -/
private theorem add_I_mul_div_mem_ball {v : ℂ} (hv : v ≠ 0) (p : ℂ) {r s : ℝ} (hs : 0 < s)
    (hsr : s < r * ‖v‖) : p + I * s / v ∈ ball p r ∧ 0 < (v * (p + I * s / v - p)).im := by
  have hζ : v * (p + I * s / v - p) = I * s := by
    field_simp
    ring
  refine ⟨mem_ball_of_norm_mul_sub_lt (v := v) ?_, ?_⟩ <;> rw [hζ]
  · simpa [abs_of_pos hs] using hsr
  · simpa using hs

/-- For `0 < s < r * ‖v‖`, the point `p - I * s / v` lies in `ball p r`, on the negative side of
the line `{z | (v * (z - p)).im = 0}`. -/
private theorem sub_I_mul_div_mem_ball {v : ℂ} (hv : v ≠ 0) (p : ℂ) {r s : ℝ} (hs : 0 < s)
    (hsr : s < r * ‖v‖) : p - I * s / v ∈ ball p r ∧ (v * (p - I * s / v - p)).im < 0 := by
  have hζ : v * (p - I * s / v - p) = -(I * s) := by
    field_simp
    ring
  refine ⟨mem_ball_of_norm_mul_sub_lt (v := v) ?_, ?_⟩ <;> rw [hζ]
  · simpa [abs_of_pos hs] using hsr
  · simpa using hs

/-- The short normal segment through a straight point of a Jordan curve satisfies the
segment-crossing criterion. -/
private theorem IsJordanCurve.notMem_model_connectedComponentIn_of_locally_eq_line {C : Set ℂ}
    (hC : IsJordanCurve C) {p v : ℂ} {r s : ℝ} (hv : v ≠ 0)
    (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0) (hs : 0 < s) (hsr : s < r * ‖v‖) :
    p - I * s / v ∉ connectedComponentIn Cᶜ (p + I * s / v) := by
  let d : ℂ := -(I / v)
  have hd : d ≠ 0 := neg_ne_zero.mpr (div_ne_zero I_ne_zero hv)
  have hcoord (t : ℝ) : v * (d * (t : ℂ) + p - p) = -(I * t) := by
    dsimp [d]
    field_simp [hv]
    ring
  have hseg : ∀ t ∈ Icc (-s) s, d * t + p ∈ C → t = 0 := by
    intro t ht htC
    have hnorm : ‖v * (d * (t : ℂ) + p - p)‖ < r * ‖v‖ := by
      rw [hcoord]
      simpa using (abs_le.mpr ⟨ht.1, ht.2⟩).trans_lt hsr
    have him := (hline _ (mem_ball_of_norm_mul_sub_lt hnorm)).mp htC
    rw [hcoord] at him
    simpa only [neg_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul,
      zero_add, sub_zero, neg_eq_zero] using him
  let φ : ℝ → ℂ := fun t => p + t / v
  have hφcont : Continuous φ := by fun_prop
  have hφ0 : Tendsto φ (𝓝 (0 : ℝ)) (𝓝 p) := by
    simpa [φ] using hφcont.tendsto 0
  have hφv (t : ℝ) : v * (φ t - p) = t := by
    dsimp [φ]
    field_simp [hv]
    ring
  have hφd (t : ℝ) : ((φ t - p) / d).im = t := by
    have heq : (φ t - p) / d = I * t := by
      dsimp [φ, d]
      field_simp [hv, I_ne_zero]
      simp [Complex.I_sq]
    rw [heq]
    simp
  have hr : 0 < r := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (norm_nonneg v)
    linarith
  have hφball : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ ball p r :=
    hφ0.eventually (ball_mem_nhds p hr)
  have hφC : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ C := by
    filter_upwards [hφball] with t ht
    exact (hline _ ht).mpr (by rw [hφv]; simp)
  have hleft : p ∈ closure (C ∩ {q | 0 < ((q - p) / d).im}) := by
    apply mem_closure_of_tendsto (b := 𝓝[>] (0 : ℝ))
      (hφ0.mono_left nhdsWithin_le_nhds)
    filter_upwards [hφC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t htC (ht : 0 < t)
    exact ⟨htC, by simpa [hφd] using ht⟩
  have hright : p ∈ closure (C ∩ {q | ((q - p) / d).im < 0}) := by
    apply mem_closure_of_tendsto (b := 𝓝[<] (0 : ℝ))
      (hφ0.mono_left nhdsWithin_le_nhds)
    filter_upwards [hφC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t htC (ht : t < 0)
    exact ⟨htC, by simpa [hφd] using ht⟩
  have hstart : d * ((-s : ℝ) : ℂ) + p = p + I * s / v := by
    dsimp [d]
    push_cast
    field_simp [hv]
    ring
  have hend : d * (s : ℂ) + p = p - I * s / v := by
    dsimp [d]
    field_simp [hv]
    ring
  have hzero : (0 : ℝ) ∈ Ioo (-s) s := by simp [hs]
  have hpre : IsPreconnected (C \ {d * (0 : ℂ) + p}) := by
    simpa only [mul_zero, zero_add] using
      (hC.isPathConnected_sdiff_singleton p).isConnected.isPreconnected
  have hleft' : d * (0 : ℂ) + p ∈
      closure (C ∩ {q | 0 < ((q - (d * (0 : ℂ) + p)) / d).im}) := by
    simpa only [mul_zero, zero_add] using hleft
  have hright' : d * (0 : ℂ) + p ∈
      closure (C ∩ {q | ((q - (d * (0 : ℂ) + p)) / d).im < 0}) := by
    simpa only [mul_zero, zero_add] using hright
  have hsep := Contour.notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton
    hC.isClosed hd hzero hseg hpre hleft' hright'
  simpa only [mul_zero, zero_add, hstart, hend] using hsep

/-- **A Jordan curve separates the two sides of a straight piece.** If a Jordan curve `C` agrees
in `ball p r` with the line `{z | (v * (z - p)).im = 0}`, then two points of that ball on opposite
sides of the line lie in different components of the complement of `C`. -/
theorem IsJordanCurve.notMem_connectedComponentIn_of_locally_eq_line {C : Set ℂ}
    (hC : IsJordanCurve C) {p v a b : ℂ} {r : ℝ}
    (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0)
    (ha : a ∈ ball p r) (hb : b ∈ ball p r)
    (ha' : 0 < (v * (a - p)).im) (hb' : (v * (b - p)).im < 0) :
    b ∉ connectedComponentIn Cᶜ a := by
  have hv : v ≠ 0 := by
    rintro rfl
    simp at ha'
  have hrv : 0 < r * ‖v‖ := mul_pos (pos_of_mem_ball ha) (norm_pos_iff.mpr hv)
  have hs : 0 < r * ‖v‖ / 2 := half_pos hrv
  have hsr : r * ‖v‖ / 2 < r * ‖v‖ := half_lt_self hrv
  -- `a` and `b` are joined off `C` to the model points `p ± I * s / v` on their sides
  obtain ⟨ha₀b, ha₀⟩ := add_I_mul_div_mem_ball hv p hs hsr
  obtain ⟨hb₀b, hb₀⟩ := sub_I_mul_div_mem_ball hv p hs hsr
  have haa₀ := mem_connectedComponentIn_of_locally_subset_line_of_im_pos
    (fun z hz => (hline z hz).mp) ha ha₀b ha' ha₀
  have hline' : ∀ z ∈ ball p r, z ∈ C → (-v * (z - p)).im = 0 := fun z hz hCz => by
    rw [neg_mul, neg_im, neg_eq_zero]
    exact (hline z hz).mp hCz
  have hbb₀ := mem_connectedComponentIn_of_locally_subset_line_of_im_pos hline' hb hb₀b
    (by rw [neg_mul, neg_im]; linarith) (by rw [neg_mul, neg_im]; linarith)
  intro hab
  exact (hC.notMem_model_connectedComponentIn_of_locally_eq_line hv hline hs hsr)
    (connectedComponentIn_eq haa₀ ▸ connectedComponentIn_eq hab ▸ hbb₀)

/-- **Exactly one side of a straight piece of a Jordan curve lies inside it.** If a Jordan curve
`C` agrees in `ball p r` with the line `{z | (v * (z - p)).im = 0}`, and `a`, `b` are points of
that ball on opposite sides of the line, then exactly one of them lies in the filled hull of `C`,
that is, in a bounded component of the complement of `C`. -/
theorem IsJordanCurve.mem_filledHull_iff_notMem_filledHull_of_locally_eq_line {C : Set ℂ}
    (hC : IsJordanCurve C) {p v a b : ℂ} {r : ℝ}
    (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0)
    (ha : a ∈ ball p r) (hb : b ∈ ball p r)
    (ha' : 0 < (v * (a - p)).im) (hb' : (v * (b - p)).im < 0) :
    a ∈ filledHull C ↔ b ∉ filledHull C := by
  have hab := hC.notMem_connectedComponentIn_of_locally_eq_line hline ha hb ha' hb'
  refine ⟨fun haH hbH => hab ?_, fun hbH => ?_⟩
  · have haC : a ∉ C := fun h => ha'.ne' ((hline a ha).mp h)
    have hbC : b ∉ C := fun h => hb'.ne ((hline b hb).mp h)
    rw [← hC.filledHull_sdiff_eq_connectedComponentIn ⟨haH, haC⟩]
    exact ⟨hbH, hbC⟩
  · have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact Cardinal.one_lt_two
    exact (mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn hrank
      hC.isCompact.isBounded hab).resolve_right hbH

end TauCeti
