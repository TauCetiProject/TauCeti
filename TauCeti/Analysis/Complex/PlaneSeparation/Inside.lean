/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
-- Supplies the locally convex, hence locally connected, instance on the complex plane.
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.PlaneSeparation.RiemannSphere
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Compactification.OnePoint.FilledHull

/-!
# The Jordan curve theorem: the inside of a Jordan curve is connected

A Jordan curve `C ⊆ ℂ` separates the plane (`TauCeti.IsJordanCurve.not_isPreconnected_compl`), so
its complement has a bounded component, and every complementary component has the whole curve as
its frontier (`TauCeti.IsJordanCurve.frontier_connectedComponentIn`). This file proves the
remaining half of the **Jordan curve theorem**: there is only one bounded component. So the inside
`filledHull C \ C` of the curve is a single component of `Cᶜ`, hence open, bounded and connected
with frontier `C`, and `Cᶜ` has exactly two components, the inside and the unbounded outside.

The count comes from the Riemann sphere, where the Jordan–Brouwer separation theorem gives
exactly two path components for the complement of the image `J` of `C`
(`TauCeti.IsJordanCurve.natCard_zerothHomotopy_compl_eq_two_onePoint`). The image of a bounded
component `D` of `Cᶜ` is open in the sphere, and its closure there is the image of the compact set
`closure D ⊆ D ∪ C`, so it is clopen in `Jᶜ` and misses the point at infinity. Hence the images of
two different bounded components and the point at infinity would lie in three different path
components of `Jᶜ`.

## Main results

* `TauCeti.IsJordanCurve.mem_connectedComponentIn_of_mem_filledHull_sdiff` — two points inside a
  Jordan curve lie in the same component of its complement.
* `TauCeti.IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn` — the inside of a Jordan curve
  is the component of its complement containing any of its points.
* `TauCeti.IsJordanCurve.isConnected_filledHull_sdiff` — the inside of a Jordan curve is
  connected.
* `TauCeti.IsJordanCurve.frontier_filledHull_sdiff` — the frontier of the inside of a Jordan curve
  is the curve.
* `TauCeti.IsJordanCurve.natCard_connectedComponents_compl_eq_two` — **the Jordan curve theorem**:
  the complement of a Jordan curve in the plane has exactly two connected components.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.B, Corollary 2B.2.
* J. R. Munkres, *Topology*, §61–63.
-/

public section

namespace TauCeti

open Bornology Set
open scoped OnePoint

/-- **A Jordan curve has only one bounded complementary component.** Two points of the inside
`filledHull C \ C` of a Jordan curve `C ⊆ ℂ` lie in the same component of `Cᶜ`. -/
theorem IsJordanCurve.mem_connectedComponentIn_of_mem_filledHull_sdiff {C : Set ℂ}
    (hC : IsJordanCurve C) {x y : ℂ} (hx : x ∈ filledHull C \ C) (hy : y ∈ filledHull C \ C) :
    y ∈ connectedComponentIn Cᶜ x := by
  by_contra hxy
  set J : Set (OnePoint ℂ) := (↑) '' C
  have hJ : IsJordanCurve J :=
    hC.image OnePoint.continuous_coe.continuousOn OnePoint.coe_injective.injOn
  have hmem (z : ℂ) (hz : z ∉ C) : (z : OnePoint ℂ) ∈ Jᶜ :=
    fun ⟨w, hw, hwz⟩ => hz (OnePoint.coe_injective hwz ▸ hw)
  have hinf : ∞ ∈ Jᶜ := fun ⟨w, _, hw⟩ => OnePoint.coe_ne_infty w hw
  -- A point outside the image of the component of `z` is in another path component of `Jᶜ`.
  have hsep (z : ℂ) (hz : z ∈ filledHull C \ C) (w : OnePoint ℂ) (hw : w ∈ Jᶜ)
      (hwz : w ∉ ((↑) : ℂ → OnePoint ℂ) '' connectedComponentIn Cᶜ z) :
      ZerothHomotopy.mk (⟨w, hw⟩ : ↥Jᶜ) ≠ ZerothHomotopy.mk ⟨z, hmem z hz.2⟩ := fun heq => by
    have hj : ⟨w, hw⟩ ∈ pathComponent (⟨z, hmem z hz.2⟩ : ↥Jᶜ) := by
      rw [← ZerothHomotopy.preimage_singleton_eq_pathComponent, mem_preimage, heq,
        mem_singleton_iff]
    exact not_joinedIn_compl_image_coe hC.isClosed hz hwz ((joinedIn_iff_joined _ _).mpr hj)
  have hinfD (z : ℂ) : ∞ ∉ ((↑) : ℂ → OnePoint ℂ) '' connectedComponentIn Cᶜ z :=
    fun ⟨w, _, hw⟩ => OnePoint.coe_ne_infty w hw
  -- The images of `x` and `y` lie in the unique path component other than that of `∞`.
  obtain ⟨c, -, hc⟩ := (Nat.card_eq_two_iff' (ZerothHomotopy.mk (⟨∞, hinf⟩ : ↥Jᶜ))).mp
    hJ.natCard_zerothHomotopy_compl_eq_two_onePoint
  refine hsep x hx y (hmem y hy.2) (fun ⟨w, hw, hwy⟩ => hxy (OnePoint.coe_injective hwy ▸ hw)) ?_
  rw [hc _ (hsep x hx ∞ hinf (hinfD x)).symm, hc _ (hsep y hy ∞ hinf (hinfD y)).symm]

/-- **The inside of a Jordan curve is a single complementary component.** For a Jordan curve
`C ⊆ ℂ` and any point `x` of its inside, `filledHull C \ C` is the component of `Cᶜ` containing
`x`. -/
theorem IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn {C : Set ℂ} (hC : IsJordanCurve C)
    {x : ℂ} (hx : x ∈ filledHull C \ C) : filledHull C \ C = connectedComponentIn Cᶜ x := by
  refine Subset.antisymm (fun y hy => hC.mem_connectedComponentIn_of_mem_filledHull_sdiff hx hy)
    fun y hy => ⟨?_, connectedComponentIn_subset _ _ hy⟩
  rw [mem_filledHull_iff, ← connectedComponentIn_eq hy]
  exact mem_filledHull_iff.mp hx.1

/-- **The inside of a Jordan curve is connected.** -/
theorem IsJordanCurve.isConnected_filledHull_sdiff {C : Set ℂ} (hC : IsJordanCurve C) :
    IsConnected (filledHull C \ C) := by
  obtain ⟨x, hx⟩ := hC.nonempty_filledHull_sdiff
  rw [hC.filledHull_sdiff_eq_connectedComponentIn hx]
  exact isConnected_connectedComponentIn_iff.mpr hx.2

/-- **A Jordan curve bounds its inside.** The frontier of the inside `filledHull C \ C` of a Jordan
curve `C ⊆ ℂ` is `C`. -/
theorem IsJordanCurve.frontier_filledHull_sdiff {C : Set ℂ} (hC : IsJordanCurve C) :
    frontier (filledHull C \ C) = C := by
  obtain ⟨x, hx⟩ := hC.nonempty_filledHull_sdiff
  rw [hC.filledHull_sdiff_eq_connectedComponentIn hx]
  exact hC.frontier_connectedComponentIn hx.2

/-- **The Jordan curve theorem.** The complement of a Jordan curve in the plane has exactly two
connected components: its inside `filledHull C \ C` and its unbounded outside. -/
theorem IsJordanCurve.natCard_connectedComponents_compl_eq_two {C : Set ℂ}
    (hC : IsJordanCurve C) : Nat.card (ConnectedComponents ↥Cᶜ) = 2 := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  obtain ⟨x, hx⟩ := hC.nonempty_filledHull_sdiff
  -- the filled hull of the compact curve is bounded, so some point lies outside it
  obtain ⟨w, hw⟩ : ∃ w, w ∉ filledHull C := by
    by_contra! h
    exact NormedSpace.unbounded_univ ℝ ℂ
      ((isBounded_filledHull.mpr hC.isCompact.isBounded).subset fun z _ => h z)
  have hwC : w ∉ C := fun h => hw (subset_filledHull h)
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk ⟨x, hx.2⟩, ConnectedComponents.mk ⟨w, hwC⟩, fun h => hw ?_,
    eq_univ_of_forall fun c => ?_⟩
  · rw [mem_filledHull_iff,
      ← (ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq hx.2 hwC).mp h]
    exact mem_filledHull_iff.mp hx.1
  · obtain ⟨⟨z, hz⟩, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [mem_insert_iff, mem_singleton_iff,
      ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq hz hx.2,
      ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq hz hwC]
    by_cases hzH : z ∈ filledHull C
    · exact Or.inl (connectedComponentIn_eq
        (hC.mem_connectedComponentIn_of_mem_filledHull_sdiff hx ⟨hzH, hz⟩)).symm
    · exact Or.inr (connectedComponentIn_compl_eq_of_unbounded_component hrank
        hC.isCompact.isBounded (mt mem_filledHull_iff.mpr hzH) (mt mem_filledHull_iff.mpr hw))

end TauCeti
