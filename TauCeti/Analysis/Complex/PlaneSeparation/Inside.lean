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
import TauCeti.Analysis.Normed.Field.Inversion
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
* `TauCeti.IsJordanCurve.frontier_filledHull` — the curve is also the frontier of its filled hull,
  hence of its outside.
* `TauCeti.IsJordanCurve.interior_filledHull`, `TauCeti.IsJordanCurve.closure_filledHull_sdiff` and
  `TauCeti.IsJordanCurve.closure_compl_filledHull` — the inside is the interior of the filled hull,
  whose closure it is, and the closure of the outside is the complement of the inside.
* `TauCeti.IsJordanCurve.frontier_insert_zero_image_inv_sub_compl_filledHull` — the outside,
  inverted about a point `p` of the inside by `z ↦ (z - p)⁻¹` and completed by `0`, the image of
  infinity, is bounded by the inverted curve.
* `TauCeti.IsJordanCurve.connectedComponentIn_eq_filledHull_sdiff_or_compl` — every complementary
  component of a Jordan curve is its inside or its outside. The outside is connected for any
  bounded set, by `TauCeti.isConnected_compl_filledHull`.
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
    fun y hy => ⟨(mem_filledHull_iff_of_mem_connectedComponentIn hy).mpr hx.1,
      connectedComponentIn_subset _ _ hy⟩

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

/-- **A Jordan curve bounds its filled hull.** The frontier of `filledHull C` for a Jordan curve
`C ⊆ ℂ` is `C`; equivalently (`frontier_compl`) the curve is the frontier of its outside
`(filledHull C)ᶜ`. -/
@[simp]
theorem IsJordanCurve.frontier_filledHull {C : Set ℂ} (hC : IsJordanCurve C) :
    frontier (filledHull C) = C := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  obtain ⟨x, hx⟩ := nonempty_compl_filledHull hC.isCompact.isBounded
  rw [← frontier_compl, compl_filledHull_eq_connectedComponentIn hrank hC.isCompact.isBounded hx]
  exact hC.frontier_connectedComponentIn fun h => hx (subset_filledHull h)

/-- The interior of the filled hull of a Jordan curve `C ⊆ ℂ` is its inside `filledHull C \ C`. -/
@[simp]
theorem IsJordanCurve.interior_filledHull {C : Set ℂ} (hC : IsJordanCurve C) :
    interior (filledHull C) = filledHull C \ C := by
  rw [← self_sdiff_frontier, hC.frontier_filledHull]

/-- The closure of the inside `filledHull C \ C` of a Jordan curve `C ⊆ ℂ` is its filled hull. -/
@[simp]
theorem IsJordanCurve.closure_filledHull_sdiff {C : Set ℂ} (hC : IsJordanCurve C) :
    closure (filledHull C \ C) = filledHull C := by
  rw [closure_eq_self_union_frontier, hC.frontier_filledHull_sdiff, sdiff_union_self,
    union_eq_left.mpr subset_filledHull]

/-- The closure of the outside `(filledHull C)ᶜ` of a Jordan curve `C ⊆ ℂ` is the complement of its
inside. -/
theorem IsJordanCurve.closure_compl_filledHull {C : Set ℂ} (hC : IsJordanCurve C) :
    closure (filledHull C)ᶜ = (filledHull C \ C)ᶜ := by
  rw [closure_compl, hC.interior_filledHull]

/-- A point of the inside of a Jordan curve `C ⊆ ℂ` lies off the closure of its outside. -/
theorem IsJordanCurve.notMem_closure_compl_filledHull {C : Set ℂ} (hC : IsJordanCurve C) {p : ℂ}
    (hp : p ∈ filledHull C \ C) : p ∉ closure (filledHull C)ᶜ := by
  rw [hC.closure_compl_filledHull]
  exact not_not_intro hp

/-- **The inverted outside of a Jordan curve is bounded by the inverted curve.** Inverting the
outside `(filledHull C)ᶜ` of a Jordan curve `C ⊆ ℂ` about a point `p` of its inside and adding `0`,
the image of infinity, gives an open set whose frontier is the image of `C`. -/
theorem IsJordanCurve.frontier_insert_zero_image_inv_sub_compl_filledHull {C : Set ℂ}
    (hC : IsJordanCurve C) {p : ℂ} (hp : p ∈ filledHull C \ C) :
    frontier (insert 0 ((fun z : ℂ => (z - p)⁻¹) '' (filledHull C)ᶜ)) =
      (fun z : ℂ => (z - p)⁻¹) '' C := by
  have hUc : IsBounded (filledHull C)ᶜᶜ := by
    rw [compl_compl]
    exact isBounded_filledHull.mpr hC.isCompact.isBounded
  rw [frontier_insert_zero_image_inv_sub hC.isClosed.isClosed_filledHull.isOpen_compl
    (hC.notMem_closure_compl_filledHull hp) hUc, frontier_compl, hC.frontier_filledHull]

/-- Every complementary component of a Jordan curve `C ⊆ ℂ` is either its inside
`filledHull C \ C` or its outside `(filledHull C)ᶜ`. -/
theorem IsJordanCurve.connectedComponentIn_eq_filledHull_sdiff_or_compl {C : Set ℂ}
    (hC : IsJordanCurve C) {x : ℂ} (hx : x ∉ C) :
    connectedComponentIn Cᶜ x = filledHull C \ C ∨ connectedComponentIn Cᶜ x = (filledHull C)ᶜ := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  by_cases hxH : x ∈ filledHull C
  · exact Or.inl (hC.filledHull_sdiff_eq_connectedComponentIn ⟨hxH, hx⟩).symm
  · exact Or.inr (compl_filledHull_eq_connectedComponentIn hrank hC.isCompact.isBounded hxH).symm

/-- **The Jordan curve theorem.** The complement of a Jordan curve in the plane has exactly two
connected components: by `TauCeti.IsJordanCurve.connectedComponentIn_eq_filledHull_sdiff_or_compl`
they are its inside `filledHull C \ C` and its unbounded outside `(filledHull C)ᶜ`. -/
theorem IsJordanCurve.natCard_connectedComponents_compl_eq_two {C : Set ℂ}
    (hC : IsJordanCurve C) : Nat.card (ConnectedComponents ↥Cᶜ) = 2 := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  obtain ⟨x, hx⟩ := hC.nonempty_filledHull_sdiff
  -- the filled hull of the compact curve is bounded, so some point lies outside it
  obtain ⟨w, hw⟩ := nonempty_compl_filledHull hC.isCompact.isBounded
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
    rw [← hC.filledHull_sdiff_eq_connectedComponentIn hx,
      ← compl_filledHull_eq_connectedComponentIn hrank hC.isCompact.isBounded hw]
    exact hC.connectedComponentIn_eq_filledHull_sdiff_or_compl hz

end TauCeti
