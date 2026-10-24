/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.AlgebraicTopology.Singular.JordanBrouwer
import TauCeti.Topology.ConnectedComponents

/-!
# The Jordan curve theorem: a plane Jordan curve has exactly two complementary components

The Jordan separation theorem `TauCeti.IsJordanCurve.not_isPreconnected_compl` says that a Jordan
curve `C ⊆ ℂ` has at least two complementary components. This file proves the other half of the
**Jordan curve theorem**: there are exactly two, the inside `filledHull C \ C` and the outside
`(filledHull C)ᶜ`. Consequently the inside is open, bounded and connected, with frontier `C`.

The proof transports the problem to the round sphere `S²` through the one-point compactification
of `ℂ` (Mathlib's `onePointEquivSphereOfFinrankEq`). There the curve is an embedded circle, so its
complement has exactly two path components by the Jordan–Brouwer separation theorem
`TauCeti.natCard_zerothHomotopy_sphere_compl_range_eq_two`, proved with singular homology. A
bounded complementary component of `C` stays open and closed in the complement of `C` in `S²`,
because the point at infinity is not adherent to it. So two distinct bounded components, together
with the unbounded one, would give three path components in the sphere.

## Main results

* `TauCeti.IsJordanCurve.mem_connectedComponentIn_of_mem_filledHull_sdiff`: two points inside a
  Jordan curve lie in the same complementary component.
* `TauCeti.IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn`: the inside of a Jordan curve is
  the complementary component of any of its points.
* `TauCeti.IsJordanCurve.isConnected_filledHull_sdiff`: the inside is connected. The outside is
  connected for any bounded set, by `TauCeti.isConnected_compl_filledHull`.
* `TauCeti.IsJordanCurve.frontier_filledHull_sdiff`: the frontier of the inside is the curve.
* `TauCeti.IsJordanCurve.connectedComponentIn_eq_filledHull_sdiff_or_compl`: every complementary
  component is the inside or the outside.
* `TauCeti.IsJordanCurve.natCard_connectedComponents_compl_eq_two`: **the Jordan curve
  theorem**: the complement of a Jordan curve has exactly two connected components.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.B, Corollary 2B.2.
* J. R. Munkres, *Topology*, §63.
-/

public section

open Metric Set Topology

namespace TauCeti

/-- The plane inside the round `2`-sphere, through its one-point compactification. -/
private noncomputable def planeToSphere : ℂ → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  fun z => onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex]) (z : OnePoint ℂ)

private theorem isOpenEmbedding_planeToSphere : IsOpenEmbedding planeToSphere :=
  (Homeomorph.isOpenEmbedding _).comp OnePoint.isOpenEmbedding_coe

/-- The points of the plane off `C` land in the complement of the image of `C` in the sphere. -/
private theorem planeToSphere_mem_compl {C : Set ℂ} {z : ℂ} (hz : z ∉ C) :
    planeToSphere z ∈ (planeToSphere '' C)ᶜ := fun ⟨_, hz', hzz'⟩ =>
  hz (isOpenEmbedding_planeToSphere.injective hzz' ▸ hz')

/-- **Jordan–Brouwer in the sphere.** The complement of the image of a plane Jordan curve in the
sphere has exactly two path components. -/
private theorem IsJordanCurve.natCard_zerothHomotopy_compl_image_planeToSphere {C : Set ℂ}
    (h : IsJordanCurve C) : Nat.card (ZerothHomotopy ↥(planeToSphere '' C)ᶜ) = 2 := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  -- the curve in the sphere, parametrised by the unit circle of `ℂ`
  let g : sphere (0 : ℂ) 1 → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    planeToSphere ∘ jordanParam e ∘ sphereCircleHomeomorph 0 one_pos
  have hrange : range g = planeToSphere '' C := by
    simp only [g, range_comp, Homeomorph.range_coe, image_univ, range_jordanParam]
  rw [← hrange]
  exact natCard_zerothHomotopy_sphere_compl_range_eq_two (by simp [Complex.finrank_real_complex])
    (isOpenEmbedding_planeToSphere.continuous.comp
      ((continuous_jordanParam e).comp (Homeomorph.continuous _)))
    (isOpenEmbedding_planeToSphere.injective.comp
      ((jordanParam_injective e).comp (Homeomorph.injective _)))

/-- A bounded complementary component of a closed set `C ⊆ ℂ` stays clopen in the complement of
the image of `C` in the sphere: the point at infinity is not adherent to it. -/
private theorem isClopen_preimage_image_planeToSphere {C : Set ℂ} (hC : IsClosed C) {x : ℂ}
    (hx : x ∈ filledHull C \ C) :
    IsClopen ((↑) ⁻¹' (planeToSphere '' connectedComponentIn Cᶜ x) :
      Set ↥(planeToSphere '' C)ᶜ) := by
  set D := connectedComponentIn Cᶜ x
  have hDo : IsOpen D := hC.isOpen_compl.connectedComponentIn
  have hDc : IsCompact (closure D) := (mem_filledHull_iff.mp hx.1).isCompact_closure
  -- the closure of `D` adds only points of `C`, which the subspace omits
  have hcl : (↑) ⁻¹' (planeToSphere '' closure D) =
      ((↑) ⁻¹' (planeToSphere '' D) : Set ↥(planeToSphere '' C)ᶜ) := by
    refine Subset.antisymm (fun p ⟨z, hz, hzp⟩ => ?_) (preimage_mono (image_mono subset_closure))
    rw [closure_eq_interior_union_frontier, hDo.interior_eq] at hz
    rcases hz with hz | hz
    · exact ⟨z, hz, hzp⟩
    · have hzC : z ∈ C := by
        simpa using frontier_connectedComponentIn_subset_compl hC.isOpen_compl x hz
      exact absurd ⟨z, hzC, hzp⟩ p.2
  refine ⟨?_, ?_⟩
  · rw [← hcl]
    exact (hDc.image isOpenEmbedding_planeToSphere.continuous).isClosed.preimage
      continuous_subtype_val
  · exact (isOpenEmbedding_planeToSphere.isOpenMap D hDo).preimage continuous_subtype_val

/-- A point of the plane joined in the sphere, off a closed set `C`, to a point in a bounded
complementary component of `C` lies in that component. -/
private theorem mem_connectedComponentIn_of_zerothHomotopy_mk_eq {C : Set ℂ} (hC : IsClosed C)
    {u v : ℂ} (hu : u ∈ filledHull C \ C) (hv : v ∉ C)
    (huv : ZerothHomotopy.mk (⟨_, planeToSphere_mem_compl hu.2⟩ : ↥(planeToSphere '' C)ᶜ) =
      ZerothHomotopy.mk ⟨_, planeToSphere_mem_compl hv⟩) :
    v ∈ connectedComponentIn Cᶜ u := by
  have hcc : connectedComponent
      (⟨_, planeToSphere_mem_compl hu.2⟩ : ↥(planeToSphere '' C)ᶜ) =
        connectedComponent ⟨_, planeToSphere_mem_compl hv⟩ :=
    -- `toConnectedComponents` sends a path class to the class of its connected component
    ConnectedComponents.coe_eq_coe.mp (congrArg ZerothHomotopy.toConnectedComponents huv)
  obtain ⟨v', hv', hvv'⟩ := (isClopen_preimage_image_planeToSphere hC hu).connectedComponent_subset
    ⟨u, mem_connectedComponentIn hu.2, rfl⟩ (hcc.symm ▸ mem_connectedComponent)
  exact isOpenEmbedding_planeToSphere.injective hvv' ▸ hv'

/-- **The inside of a Jordan curve is connected.** Two points in bounded components of the
complement of a Jordan curve `C ⊆ ℂ` lie in the same component. -/
theorem IsJordanCurve.mem_connectedComponentIn_of_mem_filledHull_sdiff {C : Set ℂ}
    (h : IsJordanCurve C) {x y : ℂ} (hx : x ∈ filledHull C \ C) (hy : y ∈ filledHull C \ C) :
    y ∈ connectedComponentIn Cᶜ x := by
  by_contra hxy
  -- a point `w` in the unbounded component
  obtain ⟨w, hw⟩ := nonempty_compl_filledHull h.isCompact.isBounded
  have hwC : w ∉ C := fun hwC => hw (subset_filledHull hwC)
  have hout : ∀ {u : ℂ}, u ∈ filledHull C \ C → w ∉ connectedComponentIn Cᶜ u :=
    fun hu hwu => hw ((mem_filledHull_iff_of_mem_connectedComponentIn hwu).mpr hu.1)
  -- `x`, `y` and `w` lie in three different path components of the complement in the sphere
  have hsep := @mem_connectedComponentIn_of_zerothHomotopy_mk_eq C h.isClosed
  have hxy' := fun e => hxy (hsep hx hy.2 e)
  have hxw' := fun e => hout hx (hsep hx hwC e)
  have hyw' := fun e => hout hy (hsep hy hwC e)
  -- but there are only two
  obtain ⟨a, b, -, hab⟩ :=
    Nat.card_eq_two_iff.mp h.natCard_zerothHomotopy_compl_image_planeToSphere
  have hab' : ∀ c, c = a ∨ c = b := fun c => by simpa using eq_univ_iff_forall.mp hab c
  rcases hab' (.mk ⟨_, planeToSphere_mem_compl hx.2⟩) with h₁ | h₁ <;>
  rcases hab' (.mk ⟨_, planeToSphere_mem_compl hy.2⟩) with h₂ | h₂ <;>
  rcases hab' (.mk ⟨_, planeToSphere_mem_compl hwC⟩) with h₃ | h₃
  all_goals first
    | exact hxy' (h₁.trans h₂.symm)
    | exact hxw' (h₁.trans h₃.symm)
    | exact hyw' (h₂.trans h₃.symm)

/-- **The inside of a Jordan curve is a single complementary component**: the filled hull of a
Jordan curve `C ⊆ ℂ` minus `C` is the component of `Cᶜ` through any of its points. -/
theorem IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn {C : Set ℂ} (h : IsJordanCurve C)
    {x : ℂ} (hx : x ∈ filledHull C \ C) : filledHull C \ C = connectedComponentIn Cᶜ x := by
  refine Subset.antisymm (fun y hy => h.mem_connectedComponentIn_of_mem_filledHull_sdiff hx hy)
    fun y hy => ⟨(mem_filledHull_iff_of_mem_connectedComponentIn hy).mpr hx.1,
      connectedComponentIn_subset _ _ hy⟩

/-- The inside of a Jordan curve, its filled hull minus the curve, is connected. -/
theorem IsJordanCurve.isConnected_filledHull_sdiff {C : Set ℂ} (h : IsJordanCurve C) :
    IsConnected (filledHull C \ C) := by
  obtain ⟨x, hx⟩ := h.nonempty_filledHull_sdiff
  rw [h.filledHull_sdiff_eq_connectedComponentIn hx]
  exact isConnected_connectedComponentIn_iff.mpr hx.2

/-- **A Jordan curve bounds its inside**: the frontier of the filled hull of a Jordan curve
`C ⊆ ℂ` minus `C` is `C`. -/
theorem IsJordanCurve.frontier_filledHull_sdiff {C : Set ℂ} (h : IsJordanCurve C) :
    frontier (filledHull C \ C) = C := by
  obtain ⟨x, hx⟩ := h.nonempty_filledHull_sdiff
  rw [h.filledHull_sdiff_eq_connectedComponentIn hx]
  exact h.frontier_connectedComponentIn hx.2

/-- Every complementary component of a Jordan curve `C ⊆ ℂ` is either its inside
`filledHull C \ C` or its outside `(filledHull C)ᶜ`. -/
theorem IsJordanCurve.connectedComponentIn_eq_filledHull_sdiff_or_compl {C : Set ℂ}
    (h : IsJordanCurve C) {x : ℂ} (hx : x ∉ C) :
    connectedComponentIn Cᶜ x = filledHull C \ C ∨ connectedComponentIn Cᶜ x = (filledHull C)ᶜ := by
  have hrank : 1 < Module.rank ℝ ℂ := Complex.rank_real_complex ▸ Cardinal.one_lt_two
  by_cases hxH : x ∈ filledHull C
  · exact Or.inl (h.filledHull_sdiff_eq_connectedComponentIn ⟨hxH, hx⟩).symm
  · exact Or.inr
      (compl_filledHull_eq_connectedComponentIn hrank h.isCompact.isBounded hxH).symm

/-- **The Jordan curve theorem.** The complement of a Jordan curve in the plane has exactly two
connected components: by `TauCeti.IsJordanCurve.connectedComponentIn_eq_filledHull_sdiff_or_compl`
they are the bounded inside `filledHull C \ C` and the unbounded outside `(filledHull C)ᶜ`. -/
theorem IsJordanCurve.natCard_connectedComponents_compl_eq_two {C : Set ℂ} (h : IsJordanCurve C) :
    Nat.card (ConnectedComponents ↥Cᶜ) = 2 := by
  have hrank : 1 < Module.rank ℝ ℂ := Complex.rank_real_complex ▸ Cardinal.one_lt_two
  obtain ⟨x, hx⟩ := h.nonempty_filledHull_sdiff
  obtain ⟨w, hw⟩ := nonempty_compl_filledHull h.isCompact.isBounded
  have hwC : w ∉ C := fun hwC => hw (subset_filledHull hwC)
  -- components of the subspace `Cᶜ` are the components of `Cᶜ` in the plane
  have hcc : ∀ p q : ↥Cᶜ, (p : ConnectedComponents ↥Cᶜ) = q ↔
      connectedComponentIn Cᶜ p = connectedComponentIn Cᶜ q := fun p q => by
    rw [ConnectedComponents.coe_eq_coe, connectedComponentIn_eq_image p.2,
      connectedComponentIn_eq_image q.2]
    exact Subtype.val_injective.image_injective.eq_iff.symm
  refine Nat.card_eq_two_iff.mpr
    ⟨.mk ⟨x, hx.2⟩, .mk ⟨w, hwC⟩, fun he => hw ?_, ?_⟩
  · refine (mem_filledHull_iff_of_mem_connectedComponentIn (x := x) ?_).mpr hx.1
    rw [(hcc _ _).mp he]
    exact mem_connectedComponentIn hwC
  refine eq_univ_of_forall fun c => ?_
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rcases h.connectedComponentIn_eq_filledHull_sdiff_or_compl p.2 with hp | hp
  · exact Or.inl ((hcc _ _).mpr (hp.trans (h.filledHull_sdiff_eq_connectedComponentIn hx)))
  · exact Or.inr ((hcc _ _).mpr (hp.trans
      (compl_filledHull_eq_connectedComponentIn hrank h.isCompact.isBounded hw)))

end TauCeti
