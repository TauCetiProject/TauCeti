/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import Mathlib.Analysis.Complex.Convex

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

## References

* J. R. Munkres, *Topology*, Sections 61--63.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Bornology Complex Metric Set Topology

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

end TauCeti
