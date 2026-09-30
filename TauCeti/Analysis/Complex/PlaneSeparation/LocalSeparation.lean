/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import Mathlib.Analysis.Complex.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

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
on opposite sides of the straight piece lie in different components of the complement, by
Borsuk's criterion (`TauCeti.hasContinuousLogOn_sub_div_sub_iff`): for two such points `a` and
`b` close to the curve point `p`, the Borsuk map `z ↦ (z - a) / (z - b)` avoids the slit
`(-∞, 0]` on the curve minus `p`, so any continuous logarithm of it on the curve would differ from
the principal logarithm by a constant on the connected set `C \ {p}`. But along the straight piece
the principal logarithm jumps by `2 * π * I` at `p`. Consequently exactly one of the two sides
lies inside the curve, the inside is nonempty, and its frontier is the whole curve.

## Main results

* `TauCeti.IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn_of_locally_eq_line` -- a Jordan
  curve that is straight near one of its points has at most one bounded complementary component.
* `TauCeti.IsJordanCurve.notMem_connectedComponentIn_of_locally_eq_line` -- points on opposite
  sides of a straight piece lie in different complementary components.
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
private theorem mem_connectedComponentIn_of_im_pos {C : Set ℂ} {p v x y : ℂ} {r : ℝ}
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

/-- The Möbius map `ζ ↦ (ζ - I * s) / (ζ + I * s)` lands in the slit plane except on the segment
`[-I * s, I * s]`, which it sends to `(-∞, 0]`. -/
private theorem re_eq_zero_of_div_notMem_slitPlane {ζ : ℂ} {s : ℝ} (hs : 0 < s)
    (h : (ζ - I * s) / (ζ + I * s) ∉ slitPlane) : ζ.re = 0 ∧ |ζ.im| ≤ s := by
  rw [mem_slitPlane_iff, not_or, not_lt, not_not] at h
  obtain ⟨hre, him⟩ := h
  by_cases hN : ζ + I * s = 0
  · have h1 := congrArg re hN
    have h2 := congrArg im hN
    simp only [add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_re,
      zero_im, zero_mul, one_mul, sub_zero, mul_zero, add_zero] at h1 h2
    exact ⟨h1, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · have hN' : 0 < normSq (ζ + I * s) := normSq_pos.mpr hN
    rw [div_re] at hre
    rw [div_im] at him
    simp only [sub_re, add_re, sub_im, add_im, mul_re, mul_im, I_re, I_im, ofReal_re,
      ofReal_im] at hre him
    rw [← add_div] at hre
    rw [← sub_div, div_eq_zero_iff] at him
    have hN'' := hN'.ne'
    have hx : ζ.re = 0 := by
      rcases him with h | h
      · nlinarith
      · exact absurd h hN''
    refine ⟨hx, ?_⟩
    rw [div_nonpos_iff] at hre
    rcases hre with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · simp only [hx] at h
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The imaginary part of `(t - I * s) / (t + I * s)` for real `t` and `s`. -/
private theorem im_sub_div_add (t s : ℝ) :
    (((t : ℂ) - I * s) / ((t : ℂ) + I * s)).im = -(2 * t * s) / (t ^ 2 + s ^ 2) := by
  rw [div_im]
  simp only [sub_re, add_re, sub_im, add_im, mul_re, mul_im, I_re, I_im, ofReal_re,
    ofReal_im, normSq_apply]
  ring

/-- The principal logarithm of `(t - I * s) / (t + I * s)` has no limit as the real `t` tends
to `0`: the Möbius value tends to `-1` from below the slit `(-∞, 0]` as `t → 0⁺` and from above it
as `t → 0⁻`, so the logarithm tends to `-π * I` and to `π * I` respectively. -/
private theorem not_tendsto_log_sub_div_add {s : ℝ} (hs : 0 < s) (L : ℂ) :
    ¬ Tendsto (fun t : ℝ => log (((t : ℂ) - I * s) / ((t : ℂ) + I * s))) (𝓝[≠] 0) (𝓝 L) := by
  intro hL
  set G : ℝ → ℂ := fun t => ((t : ℂ) - I * s) / ((t : ℂ) + I * s) with hGdef
  have hIs : I * (s : ℂ) ≠ 0 := by simpa using hs.ne'
  have hG : Tendsto G (𝓝 (0 : ℝ)) (𝓝 (-1)) := by
    have hc : ContinuousAt G 0 := ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hIs)
    have h0 : G 0 = -1 := by
      simp only [hGdef, ofReal_zero, zero_sub, zero_add]
      rw [neg_div, div_self hIs]
    simpa [h0] using hc.tendsto
  have hright : Tendsto (fun t => log (G t)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log ‖(-1 : ℂ)‖ - Real.pi * I)) :=
    (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero (by norm_num) (by simp)).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hG.mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => by
          rw [mem_ofPred_eq, hGdef, im_sub_div_add]
          exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)⟩)
  have hleft : Tendsto (fun t => log (G t)) (𝓝[<] (0 : ℝ))
      (𝓝 (Real.log ‖(-1 : ℂ)‖ + Real.pi * I)) :=
    (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (by norm_num) (by simp)).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hG.mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun t (ht : t < 0) => by
          rw [mem_ofPred_eq, hGdef, im_sub_div_add]
          exact div_nonneg (by nlinarith) (by positivity)⟩)
  have h₁ := tendsto_nhds_unique (hL.mono_left (nhdsWithin_mono (0 : ℝ)
    (fun _ ht => ne_of_gt ht : Ioi (0 : ℝ) ⊆ {0}ᶜ))) hright
  have h₂ := tendsto_nhds_unique (hL.mono_left (nhdsWithin_mono (0 : ℝ)
    (fun _ ht => ne_of_lt ht : Iio (0 : ℝ) ⊆ {0}ᶜ))) hleft
  have : (2 * Real.pi : ℂ) * I = 0 := by linear_combination h₁ - h₂
  simp [Real.pi_ne_zero, I_ne_zero] at this

/-- In the coordinate `ζ = v * (z - p)`, the Borsuk map of `p + I * s / v` and `p - I * s / v` is
`(ζ - I * s) / (ζ + I * s)`. -/
private theorem sub_div_sub_eq {v : ℂ} (hv : v ≠ 0) (p z : ℂ) (s : ℝ) :
    (z - (p + I * s / v)) / (z - (p - I * s / v)) =
      (v * (z - p) - I * s) / (v * (z - p) + I * s) := by
  have h₁ : z - (p + I * s / v) = (v * (z - p) - I * s) / v := by
    field_simp
    ring
  have h₂ : z - (p - I * s / v) = (v * (z - p) + I * s) / v := by
    field_simp
    ring
  rw [h₁, h₂, div_div_div_cancel_right₀ hv]

/-- If a curve `C` agrees in `ball p r` with the line `{z | (v * (z - p)).im = 0}`, then off `p`
the Borsuk map of `p + I * s / v` and `p - I * s / v` lands in the slit plane on `C`, for
`0 < s < r * ‖v‖`: it takes values in `(-∞, 0]` only on the segment joining the two points, which
meets `C` only at `p`. -/
private theorem sub_div_sub_mem_slitPlane_of_locally_eq_line {C : Set ℂ} {p v z : ℂ} {r s : ℝ}
    (hv : v ≠ 0) (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0) (hs : 0 < s)
    (hsr : s < r * ‖v‖) (hzC : z ∈ C) (hzp : z ≠ p) :
    (z - (p + I * s / v)) / (z - (p - I * s / v)) ∈ slitPlane := by
  by_contra hns
  rw [sub_div_sub_eq hv] at hns
  obtain ⟨hre, him⟩ := re_eq_zero_of_div_notMem_slitPlane hs hns
  have hle : ‖v * (z - p)‖ ≤ s := by
    have hζ : v * (z - p) = (v * (z - p)).im * I := by
      apply Complex.ext <;> simp [hre]
    rw [hζ, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact him
  have hzim := (hline z (mem_ball_of_norm_mul_sub_lt (hle.trans_lt hsr))).mp hzC
  have h0 : v * (z - p) = 0 := Complex.ext hre hzim
  exact hzp (sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hv))

/-- **The core of the separation argument.** Let a Jordan curve `C` agree in `ball p r` with the
line `{z | (v * (z - p)).im = 0}`, and let `a = p + I * s / v` and `b = p - I * s / v` be the two
points at coordinate distance `s < r * ‖v‖` from `p` on either side of it. Then the Borsuk map of
`a` and `b` has no continuous logarithm on `C`.

Off `p` the Borsuk map avoids the slit `(-∞, 0]`, so a continuous logarithm on `C` would differ
from the principal one by a constant on the connected set `C \ {p}`. But along the line the
principal logarithm tends to `-π * I` on one side of `p` and to `π * I` on the other. -/
private theorem IsJordanCurve.not_hasContinuousLogOn_of_locally_eq_line {C : Set ℂ}
    (hC : IsJordanCurve C) {p v : ℂ} {r s : ℝ} (hv : v ≠ 0)
    (hline : ∀ z ∈ ball p r, z ∈ C ↔ (v * (z - p)).im = 0) (hs : 0 < s) (hsr : s < r * ‖v‖) :
    ¬ HasContinuousLogOn (fun z => (z - (p + I * s / v)) / (z - (p - I * s / v))) C := by
  intro hlog
  set g : ℂ → ℂ := fun z => (z - (p + I * s / v)) / (z - (p - I * s / v)) with hgdef
  have hgc : ContinuousOn g C := hlog.continuousOn
  obtain ⟨h, hh, hexp⟩ := hasContinuousLogOn_iff.mp hlog
  have hslit : ∀ z ∈ C \ {p}, g z ∈ slitPlane := fun z hz =>
    sub_div_sub_mem_slitPlane_of_locally_eq_line hv hline hs hsr hz.1 hz.2
  -- `h - log g` is continuous with values in `2 * π * I * ℤ` on the connected set `C \ {p}`
  set w : ℂ → ℂ := fun z => h z - log (g z) with hwdef
  have hwc : ContinuousOn w (C \ {p}) :=
    (hh.mono sdiff_subset).sub ((hgc.mono sdiff_subset).clog hslit)
  have hwexp : ∀ z ∈ C \ {p}, exp (w z) = 1 := fun z hz => by
    rw [hwdef, exp_sub, hexp z hz.1, exp_log (slitPlane_ne_zero (hslit z hz)),
      div_self (slitPlane_ne_zero (hslit z hz))]
  have hwconst : ∀ z ∈ C \ {p}, ∀ z' ∈ C \ {p}, w z = w z' := fun z hz z' hz' =>
    eq_of_isPreconnected_of_forall_exp_eq_one
      ((hC.isPathConnected_sdiff_singleton p).isConnected.isPreconnected.image w hwc)
      (by rintro _ ⟨y, hy, rfl⟩; exact hwexp y hy) (mem_image_of_mem w hz)
      (mem_image_of_mem w hz')
  -- walk along the straight piece `t ↦ p + t / v` of `C` through `p`
  set φ : ℝ → ℂ := fun t => p + t / v with hφdef
  have hφv : ∀ t : ℝ, v * (φ t - p) = t := fun t => by
    simp only [hφdef]
    field_simp
    ring
  have hrv : 0 < r * ‖v‖ := hs.trans hsr
  have hnhds : {t : ℝ | |t| < r * ‖v‖} ∈ 𝓝 0 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hrv)
  have hφC : ∀ t : ℝ, |t| < r * ‖v‖ → φ t ∈ C := fun t ht =>
    (hline _ (mem_ball_of_norm_mul_sub_lt (by rw [hφv]; simpa using ht))).mpr (by rw [hφv]; simp)
  have hφp : ∀ t : ℝ, t ≠ 0 → φ t ≠ p := fun t ht h0 => by
    have := hφv t
    rw [h0, sub_self, mul_zero] at this
    exact ht (by exact_mod_cast this.symm)
  have hsmem : φ s ∈ C \ {p} := ⟨hφC s (by rwa [abs_of_pos hs]), hφp s hs.ne'⟩
  -- along it, `h ∘ φ` is continuous at `0`, yet off `0` it is a shift of a jumping logarithm
  have hlim : Tendsto (fun t : ℝ => h (φ t)) (𝓝[≠] 0) (𝓝 (h p)) := by
    have hφ0 : Tendsto φ (𝓝 (0 : ℝ)) (𝓝 p) := by
      simpa [hφdef] using (show Continuous φ by fun_prop).tendsto 0
    refine (hh p (by simpa [hφdef] using hφC 0 (by simpa using hrv))).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hφ0.mono_left nhdsWithin_le_nhds, ?_⟩)
    filter_upwards [nhdsWithin_le_nhds hnhds] with t ht
    exact hφC t ht
  refine not_tendsto_log_sub_div_add hs (h p - w (φ s)) ((hlim.sub_const (w (φ s))).congr' ?_)
  filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with t ht h0
  have := hwconst _ ⟨hφC t ht, hφp t h0⟩ _ hsmem
  simp only [hwdef, hgdef, sub_div_sub_eq hv, hφv] at this ⊢
  linear_combination this

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
  have haa₀ := mem_connectedComponentIn_of_im_pos hline ha ha₀b ha' ha₀
  have hline' : ∀ z ∈ ball p r, z ∈ C ↔ (-v * (z - p)).im = 0 := fun z hz => by
    rw [neg_mul, neg_im, neg_eq_zero]
    exact hline z hz
  have hbb₀ := mem_connectedComponentIn_of_im_pos hline' hb hb₀b
    (by rw [neg_mul, neg_im]; linarith) (by rw [neg_mul, neg_im]; linarith)
  intro hab
  refine hC.not_hasContinuousLogOn_of_locally_eq_line hv hline hs hsr
    (hasContinuousLogOn_sub_div_sub hC.isClosed ?_)
  rw [← connectedComponentIn_eq haa₀, connectedComponentIn_eq hab]
  exact hbb₀

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
