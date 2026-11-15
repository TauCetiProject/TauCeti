/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Topology.FilledHull
import TauCeti.Topology.ConnectedComponents

/-!
# Bounded complementary components in the one-point compactification

For a closed set in a proper locally connected metric space, the closure of a bounded
complementary component in the one-point compactification adds only points of the closed set.
Consequently a path avoiding the closed set cannot leave such a component, even through infinity.

## Main results

* `TauCeti.closure_image_coe_connectedComponentIn_subset` describes that closure.
* `TauCeti.not_joinedIn_compl_image_coe` separates the component from every other point by paths.
* `TauCeti.mem_filledHull_iff_coe_notMem_connectedComponentIn_infty` characterizes membership in
  `filledHull K` as lying outside the component of `∞` in the complement of `(↑) '' K`.
-/

public section

namespace TauCeti

open Bornology Set Topology
open scoped OnePoint

variable {E : Type*} [MetricSpace E] [ProperSpace E] [LocallyConnectedSpace E]

/-- In the one-point compactification, the closure of a bounded component of the complement
of a closed set `K` adds only points of `K`. -/
theorem closure_image_coe_connectedComponentIn_subset {K : Set E} (hK : IsClosed K)
    {x : E} (hx : x ∈ filledHull K) :
    closure (((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x) ⊆
      (↑) '' (connectedComponentIn Kᶜ x ∪ K) := by
  have hD : IsCompact (closure (connectedComponentIn Kᶜ x)) :=
    (mem_filledHull_iff.mp hx).isCompact_closure
  refine (closure_minimal (image_mono subset_closure)
    (hD.image OnePoint.continuous_coe).isClosed).trans (image_mono fun y hy => ?_)
  by_contra hyD
  rw [mem_union, not_or] at hyD
  exact frontier_connectedComponentIn_subset_compl hK.isOpen_compl x
    ⟨hy, by rw [hK.isOpen_compl.connectedComponentIn.interior_eq]; exact hyD.1⟩ hyD.2

/-- A point of the one-point compactification outside the image of a bounded complementary
component of a closed set `K` cannot be joined to it by a path avoiding the image of `K`. -/
theorem not_joinedIn_compl_image_coe {K : Set E} (hK : IsClosed K) {x : E}
    (hx : x ∈ filledHull K \ K) {w : OnePoint E}
    (hw : w ∉ ((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x) :
    ¬ JoinedIn (((↑) : E → OnePoint E) '' K)ᶜ (x : OnePoint E) w := by
  intro h
  have hU : IsOpen (((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap _ hK.isOpen_compl.connectedComponentIn
  have hsub := (isConnected_range h.somePath.continuous).isPreconnected
    |>.subset_of_closure_inter_subset hU
      ⟨x, ⟨0, by simp⟩, mem_image_of_mem _ (mem_connectedComponentIn hx.2)⟩ ?_
  · exact hw (hsub ⟨1, by simp⟩)
  · rintro _ ⟨hcl, t, rfl⟩
    obtain ⟨y, hy | hy, hyt⟩ := closure_image_coe_connectedComponentIn_subset hK hx.1 hcl
    · exact ⟨y, hy, hyt⟩
    · exact absurd ⟨y, hy, hyt⟩ (h.somePath_mem t)

/-- **Filled hull via the one-point compactification.** For a closed set `K` in a proper locally
connected metric space `E`, a point `x : E` belongs to `filledHull K` if and only if
`(x : OnePoint E)` does not belong to the connected component of `∞` in the complement of
`(↑) '' K`. -/
theorem mem_filledHull_iff_coe_notMem_connectedComponentIn_infty {K : Set E} (hK : IsClosed K)
    {x : E} :
    x ∈ filledHull K ↔
      (x : OnePoint E) ∉ connectedComponentIn (((↑) : E → OnePoint E) '' K)ᶜ ∞ := by
  set K' : Set (OnePoint E) := ((↑) : E → OnePoint E) '' K
  refine ⟨fun hx hmem ↦ ?_, fun hnot ↦ by_contra fun hx ↦ hnot ?_⟩
  · by_cases hxK : x ∈ K
    · exact connectedComponentIn_subset K'ᶜ ∞ hmem ⟨x, hxK, rfl⟩
    · set W : Set (OnePoint E) := ((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x
      have hWo : IsOpen W :=
        OnePoint.isOpenEmbedding_coe.isOpenMap _ hK.isOpen_compl.connectedComponentIn
      have hcl := closure_image_coe_connectedComponentIn_subset hK hx
      have hinf : (∞ : OnePoint E) ∈ (closure W)ᶜ := fun h ↦
        OnePoint.infty_notMem_image_coe (hcl h)
      have hcov : K'ᶜ ⊆ (closure W)ᶜ ∪ W := fun z hz ↦ by
        by_cases hzc : z ∈ closure W
        · obtain ⟨y, hy | hy, rfl⟩ := hcl hzc
          · exact Or.inr ⟨y, hy, rfl⟩
          · exact (hz ⟨y, hy, rfl⟩).elim
        · exact Or.inl hzc
      have hsub : connectedComponentIn K'ᶜ ∞ ⊆ (closure W)ᶜ :=
        isPreconnected_connectedComponentIn.subset_left_of_subset_union
          isClosed_closure.isOpen_compl hWo
          (disjoint_compl_left.mono_right subset_closure)
          ((connectedComponentIn_subset K'ᶜ ∞).trans hcov)
          ⟨∞, mem_connectedComponentIn OnePoint.infty_notMem_image_coe, hinf⟩
      exact hsub hmem (subset_closure ⟨x, mem_connectedComponentIn hxK, rfl⟩)
  · have hxK : x ∉ K := fun h ↦ hx (subset_filledHull h)
    set C := connectedComponentIn Kᶜ x
    have hinf : (∞ : OnePoint E) ∈ closure (((↑) : E → OnePoint E) '' C) := by
      rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
      rintro s ⟨-, hs⟩
      obtain ⟨z, hzC, hzs⟩ : ∃ z ∈ C, z ∉ s :=
        not_subset.1 fun hCs ↦ (mem_filledHull_iff.not.1 hx) (hs.isBounded.subset hCs)
      exact ⟨z, ⟨z, hzC, rfl⟩, Or.inl ⟨z, hzs, rfl⟩⟩
    have hpre : IsPreconnected (insert (∞ : OnePoint E) (((↑) : E → OnePoint E) '' C)) :=
      (isPreconnected_connectedComponentIn.image _ OnePoint.continuous_coe.continuousOn)
        |>.subset_closure (subset_insert _ _) (insert_subset hinf subset_closure)
    have hsub : insert (∞ : OnePoint E) (((↑) : E → OnePoint E) '' C) ⊆ K'ᶜ := by
      rintro _ (rfl | ⟨y, hyC, rfl⟩)
      · exact OnePoint.infty_notMem_image_coe
      · rintro ⟨z, hzK, hzy⟩
        exact connectedComponentIn_subset Kᶜ x hyC (OnePoint.coe_injective hzy ▸ hzK)
    exact hpre.subset_connectedComponentIn (mem_insert _ _) hsub
      (mem_insert_of_mem _ ⟨x, mem_connectedComponentIn hxK, rfl⟩)

end TauCeti
