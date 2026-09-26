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

The more general local-cover result bounds the number of complementary components by two
whenever a neighbourhood of a curve point, minus the curve, is covered by two preconnected
subsets of the complement. Every complementary component approaches that point, so three
different components would have to meet the same local side.

## References

* J. R. Munkres, *Topology*, Sections 61--63.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Bornology Complex Metric Set

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

end TauCeti
