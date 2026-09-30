/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import Mathlib.Analysis.Complex.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Contour.Winding.Separation

/-!
# Complementary components at a straight point of a Jordan curve

If a Jordan curve agrees locally with a line at one point, it has at most one bounded
complementary component. In particular, any bounded complementary component is the entire
filled hull minus the curve. This identifies the inside of a simple polygon from any one of
its bounded complementary components, without a convexity assumption.

An interior point of a nondegenerate straight segment has a ball in which the segment
agrees with its supporting line. This supplies the local line hypothesis for polygonal curves.

The more general local-cover result bounds the number of complementary components by two
whenever a neighbourhood of a curve point, minus the curve, is covered by two preconnected
subsets of the complement. Every complementary component approaches that point, so three
different components would have to meet the same local side.

Such a curve also has at least one bounded complementary component: this is the separation half
of the Jordan curve theorem for Jordan curves with a straight piece, polygons among them. Points
on opposite sides of the straight piece lie in different components of the complement by the
segment-crossing theorem
`TauCeti.Contour.notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton`.
Consequently exactly one of the two sides
lies inside the curve, the inside is nonempty, and its frontier is the whole curve.

## Main results

* `TauCeti.IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn_of_locally_eq_line` -- a Jordan
  curve that is straight near one of its points has at most one bounded complementary component.
* `TauCeti.IsJordanCurve.notMem_connectedComponentIn_of_locally_eq_line` -- points on opposite
  sides of a straight piece lie in different complementary components.
* `TauCeti.mem_connectedComponentIn_of_locally_eq_line_of_im_pos` -- points on the same local
  side of a line lie in the same complementary component.
* `TauCeti.IsJordanCurve.mem_filledHull_iff_notMem_filledHull_of_locally_eq_line` -- exactly one
  of the two sides lies inside the curve.
* `TauCeti.IsJordanCurve.nonempty_filledHull_sdiff_of_locally_eq_line` and
  `TauCeti.IsJordanCurve.frontier_filledHull_sdiff_of_locally_eq_line` -- the inside is nonempty
  and its frontier is the curve.

## References

* K. Borsuk, *Über Schnitte der euklidischen Räume*, Math. Ann. **106** (1932), 239–248.
* J. R. Munkres, *Topology*, Sections 61--63.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Bornology Complex Filter Metric Set Topology

namespace TauCeti

/-- If two preconnected subsets of the complement cover the complement locally at a point of
a Jordan curve, every complementary component is one of any two distinct components. -/
theorem IsJordanCurve.connectedComponentIn_eq_or_eq_of_local_cover
    {C W S T : Set ℂ} (hC : IsJordanCurve C) {p x y z : ℂ}
    (hp : p ∈ C) (hW : IsOpen W) (hpW : p ∈ W)
    (hcover : W \ C ⊆ S ∪ T) (hS : IsPreconnected S) (hT : IsPreconnected T)
    (hSC : S ⊆ Cᶜ) (hTC : T ⊆ Cᶜ)
    (hx : x ∉ C) (hy : y ∉ C) (hz : z ∉ C)
    (hxy : y ∉ connectedComponentIn Cᶜ x) :
    connectedComponentIn Cᶜ z = connectedComponentIn Cᶜ x ∨
      connectedComponentIn Cᶜ z = connectedComponentIn Cᶜ y := by
  by_contra! hne
  have hyx : x ∉ connectedComponentIn Cᶜ y := by
    intro h
    exact hxy (connectedComponentIn_eq h ▸ mem_connectedComponentIn hy)
  have hxz : x ∉ connectedComponentIn Cᶜ z := by
    intro h
    exact hne.1 (connectedComponentIn_eq h)
  obtain ⟨u, huW, hux⟩ := _root_.mem_closure_iff.mp
    (hC.subset_closure_connectedComponentIn hx hy hxy hp) W hW hpW
  obtain ⟨v, hvW, hvy⟩ := _root_.mem_closure_iff.mp
    (hC.subset_closure_connectedComponentIn hy hx hyx hp) W hW hpW
  obtain ⟨w, hwW, hwz⟩ := _root_.mem_closure_iff.mp
    (hC.subset_closure_connectedComponentIn hz hx hxz hp) W hW hpW
  have hu := hcover ⟨huW, connectedComponentIn_subset _ _ hux⟩
  have hv := hcover ⟨hvW, connectedComponentIn_subset _ _ hvy⟩
  have hw := hcover ⟨hwW, connectedComponentIn_subset _ _ hwz⟩
  have hcompu := connectedComponentIn_eq hux
  have hcompv := connectedComponentIn_eq hvy
  have hcompw := connectedComponentIn_eq hwz
  have hcompxy : connectedComponentIn Cᶜ x ≠ connectedComponentIn Cᶜ y := by
    intro h
    exact hxy (h ▸ mem_connectedComponentIn hy)
  have hsameS : ∀ u ∈ S, ∀ v ∈ S,
      connectedComponentIn Cᶜ u = connectedComponentIn Cᶜ v :=
    fun u hu v hv => connectedComponentIn_eq (hS.subset_connectedComponentIn hu hSC hv)
  have hsameT : ∀ u ∈ T, ∀ v ∈ T,
      connectedComponentIn Cᶜ u = connectedComponentIn Cᶜ v :=
    fun u hu v hv => connectedComponentIn_eq (hT.subset_connectedComponentIn hu hTC hv)
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rcases hw with hw | hw <;>
    grind

/-- If a Jordan curve agrees with a line in a neighbourhood of one of its points, its filled
hull minus the curve is any bounded complementary component. The point `x` selects such a
component; no convexity of the curve or of that component is required. -/
theorem IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn_of_locally_eq_line
    {C : Set ℂ} (hC : IsJordanCurve C) {p x : ℂ} {r : ℝ} (hr : 0 < r)
    (v : ℂ) (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0)
    (hx : x ∈ filledHull C \ C) :
    filledHull C \ C = connectedComponentIn Cᶜ x := by
  have hp : p ∈ C := (hline p (mem_ball_self hr)).mpr (by simp)
  -- The two half-balls are convex and cover the local complement of the line.
  let S := ball p r ∩ {z : ℂ | (v * p).im < (v * z).im}
  let T := ball p r ∩ {z : ℂ | (v * z).im < (v * p).im}
  have hS : IsPreconnected S :=
    ((convex_ball p r).inter
      (convex_halfSpace_gt (Complex.imLm.comp (LinearMap.mulLeft ℝ v)).isLinear
        (v * p).im)).isPreconnected
  have hT : IsPreconnected T :=
    ((convex_ball p r).inter
      (convex_halfSpace_lt (Complex.imLm.comp (LinearMap.mulLeft ℝ v)).isLinear
        (v * p).im)).isPreconnected
  have hSC : S ⊆ Cᶜ := by
    intro z hz hzC
    have heq := (hline z hz.1).mp hzC
    simp only [mul_sub, sub_im, sub_eq_zero] at heq
    exact hz.2.ne' heq
  have hTC : T ⊆ Cᶜ := by
    intro z hz hzC
    have heq := (hline z hz.1).mp hzC
    simp only [mul_sub, sub_im, sub_eq_zero] at heq
    exact hz.2.ne heq
  have hcover : ball p r \ C ⊆ S ∪ T := by
    intro z hz
    have hne := mt (hline z hz.1).mpr hz.2
    simp only [mul_sub, sub_im, sub_eq_zero] at hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inr ⟨hz.1, hlt⟩
    · exact Or.inl ⟨hz.1, hgt⟩
  -- There is an unbounded component, since the filled hull of the compact curve is bounded.
  obtain ⟨y, hy⟩ : ∃ y, y ∉ filledHull C := by
    by_contra! h
    exact NormedSpace.unbounded_univ ℝ ℂ
      ((isBounded_filledHull.mpr hC.isCompact.isBounded).subset fun z _ => h z)
  have hyC : y ∉ C := fun hyC => hy (subset_filledHull hyC)
  have hxy : y ∉ connectedComponentIn Cᶜ x := by
    intro h
    apply hy
    rw [mem_filledHull_iff, ← connectedComponentIn_eq h]
    exact mem_filledHull_iff.mp hx.1
  -- The local cover allows only the chosen bounded component and the unbounded one.
  apply Subset.antisymm
  · intro z hz
    rcases hC.connectedComponentIn_eq_or_eq_of_local_cover hp isOpen_ball
        (mem_ball_self hr) hcover hS hT hSC hTC hx.2 hyC hz.2 hxy with heq | heq
    · exact heq ▸ mem_connectedComponentIn hz.2
    · exact False.elim (hy (by
        rw [mem_filledHull_iff, ← heq]
        exact mem_filledHull_iff.mp hz.1))
  · intro z hz
    refine ⟨?_, connectedComponentIn_subset _ _ hz⟩
    rw [mem_filledHull_iff, ← connectedComponentIn_eq hz]
    exact mem_filledHull_iff.mp hx.1

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
    obtain ⟨s, hs, hzs⟩ := (openSegment_eq_image' ℝ a b ▸ hseg)
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
component of the complement of a curve that agrees with that line in `ball p r`: the open half-ball
between them is convex and misses the curve. -/
theorem mem_connectedComponentIn_of_locally_eq_line_of_im_pos
    {C : Set ℂ} {p v x y : ℂ} {r : ℝ}
    (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0) (hx : x ∈ ball p r)
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
    (fun z hz hzC => hz.2.ne' ((hline z hz.1).mp hzC)) ⟨hy, hy'⟩

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
  have haa₀ := mem_connectedComponentIn_of_locally_eq_line_of_im_pos hline ha ha₀b ha' ha₀
  have hline' : ∀ z ∈ ball p r, z ∈ C ↔ (-v * (z - p)).im = 0 := fun z hz => by
    rw [neg_mul, neg_im, neg_eq_zero]
    exact hline z hz
  have hbb₀ := mem_connectedComponentIn_of_locally_eq_line_of_im_pos hline' hb hb₀b
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
    rw [← hC.filledHull_sdiff_eq_connectedComponentIn_of_locally_eq_line (pos_of_mem_ball ha) v
      hline ⟨haH, haC⟩]
    exact ⟨hbH, hbC⟩
  · have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact Cardinal.one_lt_two
    exact (mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn hrank
      hC.isCompact.isBounded hab).resolve_right hbH

/-- If a Jordan curve agrees with a line near one of its points, it has points on both sides of
that line near the point: the line is a genuine line, `v ≠ 0`, because a Jordan curve has empty
interior. -/
private theorem IsJordanCurve.exists_im_pos_im_neg_of_locally_eq_line {C : Set ℂ}
    (hC : IsJordanCurve C) {p v : ℂ} {r : ℝ} (hr : 0 < r)
    (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0) :
    ∃ a ∈ ball p r, ∃ b ∈ ball p r, 0 < (v * (a - p)).im ∧ (v * (b - p)).im < 0 := by
  have hv : v ≠ 0 := by
    rintro rfl
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact Cardinal.one_lt_two
    have hball : ball p r ⊆ interior C :=
      interior_maximal (fun z hz => (hline z hz).mpr (by simp)) isOpen_ball
    rw [hC.interior_eq_empty hrank] at hball
    exact hball (mem_ball_self hr)
  have hrv : 0 < r * ‖v‖ := mul_pos hr (norm_pos_iff.mpr hv)
  obtain ⟨ha, ha'⟩ := add_I_mul_div_mem_ball hv p (half_pos hrv) (half_lt_self hrv)
  obtain ⟨hb, hb'⟩ := sub_I_mul_div_mem_ball hv p (half_pos hrv) (half_lt_self hrv)
  exact ⟨_, ha, _, hb, ha', hb'⟩

/-- **A Jordan curve with a straight piece has an inside.** If a Jordan curve `C` agrees with a
line in a ball about one of its points, then its filled hull minus `C` — the union of the bounded
components of the complement of `C` — is nonempty. -/
theorem IsJordanCurve.nonempty_filledHull_sdiff_of_locally_eq_line {C : Set ℂ}
    (hC : IsJordanCurve C) {p v : ℂ} {r : ℝ} (hr : 0 < r)
    (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0) :
    (filledHull C \ C).Nonempty := by
  obtain ⟨a, ha, b, hb, ha', hb'⟩ := hC.exists_im_pos_im_neg_of_locally_eq_line hr hline
  have hiff := hC.mem_filledHull_iff_notMem_filledHull_of_locally_eq_line hline ha hb ha' hb'
  by_cases haH : a ∈ filledHull C
  · exact ⟨a, haH, fun h => ha'.ne' ((hline a ha).mp h)⟩
  · exact ⟨b, not_not.mp (mt hiff.mpr haH), fun h => hb'.ne ((hline b hb).mp h)⟩

/-- **A Jordan curve with a straight piece bounds its inside.** If a Jordan curve `C` agrees with a
line in a ball about one of its points, then the frontier of its filled hull minus `C` is `C`. -/
theorem IsJordanCurve.frontier_filledHull_sdiff_of_locally_eq_line {C : Set ℂ}
    (hC : IsJordanCurve C) {p v : ℂ} {r : ℝ} (hr : 0 < r)
    (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0) :
    frontier (filledHull C \ C) = C := by
  obtain ⟨a, ha, b, hb, ha', hb'⟩ := hC.exists_im_pos_im_neg_of_locally_eq_line hr hline
  have hiff := hC.mem_filledHull_iff_notMem_filledHull_of_locally_eq_line hline ha hb ha' hb'
  have hab := hC.notMem_connectedComponentIn_of_locally_eq_line hline ha hb ha' hb'
  have haC : a ∉ C := fun h => ha'.ne' ((hline a ha).mp h)
  have hbC : b ∉ C := fun h => hb'.ne ((hline b hb).mp h)
  by_cases haH : a ∈ filledHull C
  · rw [hC.filledHull_sdiff_eq_connectedComponentIn_of_locally_eq_line hr v hline ⟨haH, haC⟩]
    exact hC.frontier_connectedComponentIn haC hbC hab
  · have hbH : b ∈ filledHull C := not_not.mp (mt hiff.mpr haH)
    rw [hC.filledHull_sdiff_eq_connectedComponentIn_of_locally_eq_line hr v hline ⟨hbH, hbC⟩]
    exact hC.frontier_connectedComponentIn hbC haC fun h =>
      hab (connectedComponentIn_eq h ▸ mem_connectedComponentIn hbC)

end TauCeti
