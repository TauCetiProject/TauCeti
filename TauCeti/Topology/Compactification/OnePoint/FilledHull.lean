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

Conversely, in any homeomorphic model `Φ : OnePoint E ≃ₜ S` of the one-point compactification, a
complementary component of `(Φ ∘ (↑)) '' K` that is disjoint from the component of `Φ ∞` and whose
closure adds only points of `(Φ ∘ (↑)) '' K` has closure contained in `range (Φ ∘ (↑))`. When that
component and the component of `Φ ∞` cover `((Φ ∘ (↑)) '' K)ᶜ`, the component pulls back to the
bounded inside `filledHull K \ K`, and when its closure equals the union with `(Φ ∘ (↑)) '' K`, its
closure pulls back to `filledHull K`.

## Main results

* `TauCeti.closure_image_coe_connectedComponentIn_subset` describes the closure of a bounded
  complementary component in `OnePoint E`.
* `TauCeti.connectedComponentIn_compl_image_coe` identifies the connected component in the
  complement of `(↑) '' K` of any point in `filledHull K \ K` with the image of its component in
  `Kᶜ`.
* `TauCeti.not_joinedIn_compl_image_coe` separates the component from every other point by paths.
* `TauCeti.closure_connectedComponentIn_subset_range_onePoint`: a complementary component disjoint
  from the component of `Φ ∞` whose closure adds only points of `(Φ ∘ (↑)) '' K` has closure inside
  `range (Φ ∘ (↑))`.
* `TauCeti.preimage_connectedComponentIn_onePoint` and
  `TauCeti.preimage_closure_connectedComponentIn_onePoint`: the complementary component missing
  `Φ ∞` pulls back to `filledHull K \ K`, and its closure pulls back to `filledHull K`.
-/

public section

namespace TauCeti

open Bornology Set Topology
open scoped OnePoint

/-- In a homeomorphic model `Φ : OnePoint E ≃ₜ S` of the one-point compactification, if a
complementary component `U₀` of `(Φ ∘ (↑)) '' K` is disjoint from the component of `Φ ∞` and its
closure adds only points of `(Φ ∘ (↑)) '' K`, then `closure U₀` misses `Φ ∞` and lies in
`range (Φ ∘ (↑))`. -/
theorem closure_connectedComponentIn_subset_range_onePoint {E S : Type*}
    [TopologicalSpace E] [TopologicalSpace S] {K : Set E} (Φ : OnePoint E ≃ₜ S) {q₀ : S}
    (hdisj : Disjoint (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ (Φ ∞))
      (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀))
    (hcl₀ : closure (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀) ⊆
      connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀ ∪
        (Φ ∘ ((↑) : E → OnePoint E)) '' K) :
    closure (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀) ⊆
      range (Φ ∘ ((↑) : E → OnePoint E)) := fun z hz ↦ by
  have hinf : Φ ∞ ∉ (Φ ∘ ((↑) : E → OnePoint E)) '' K := by
    rintro ⟨x, -, hx⟩
    exact OnePoint.coe_ne_infty x (Φ.injective hx)
  have hzne : z ≠ Φ ∞ := by
    rintro rfl
    exact (hcl₀ hz).elim (hdisj.notMem_of_mem_left (mem_connectedComponentIn hinf)) hinf
  have hmem : Φ.symm z ∈ range ((↑) : E → OnePoint E) :=
    not_not.1 fun hn ↦ hzne (Φ.symm_apply_eq.1 (OnePoint.notMem_range_coe_iff.1 hn))
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, by simp [hx]⟩

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

/-- In the one-point compactification, the connected component in `(((↑) : E → OnePoint E) '' K)ᶜ`
of a point in a bounded complementary component of a closed set `K` is the image of its component in
`Kᶜ`. -/
theorem connectedComponentIn_compl_image_coe {K : Set E} (hK : IsClosed K) {x : E}
    (hx : x ∈ filledHull K \ K) :
    connectedComponentIn (((↑) : E → OnePoint E) '' K)ᶜ (x : OnePoint E) =
      ((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x := by
  rcases hx with ⟨hxH, hxK⟩
  have hxS : (x : OnePoint E) ∈ (((↑) : E → OnePoint E) '' K)ᶜ :=
    fun ⟨_, hy, hyx⟩ ↦ hxK (OnePoint.coe_injective hyx ▸ hy)
  refine Subset.antisymm ?_
    ((OnePoint.continuous_coe.continuousOn.image_connectedComponentIn_subset hxK).trans
      (connectedComponentIn_mono _ (image_compl_subset OnePoint.coe_injective)))
  have hU : IsOpen (((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap _ hK.isOpen_compl.connectedComponentIn
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hU
    ⟨(x : OnePoint E), mem_connectedComponentIn hxS,
      mem_image_of_mem _ (mem_connectedComponentIn hxK)⟩ ?_
  rintro w ⟨hcl, hwS⟩
  obtain ⟨y, hy | hy, rfl⟩ := closure_image_coe_connectedComponentIn_subset hK hxH hcl
  · exact ⟨y, hy, rfl⟩
  · exact (connectedComponentIn_subset _ _ hwS (mem_image_of_mem _ hy)).elim

/-- A point of the one-point compactification outside the image of a bounded complementary
component of a closed set `K` cannot be joined to it by a path avoiding the image of `K`. -/
theorem not_joinedIn_compl_image_coe {K : Set E} (hK : IsClosed K) {x : E}
    (hx : x ∈ filledHull K \ K) {w : OnePoint E}
    (hw : w ∉ ((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x) :
    ¬ JoinedIn (((↑) : E → OnePoint E) '' K)ᶜ (x : OnePoint E) w := fun h ↦
  hw <| connectedComponentIn_compl_image_coe hK hx ▸
    (isConnected_range h.somePath.continuous).isPreconnected.subset_connectedComponentIn
      ⟨0, by simp⟩ (range_subset_iff.mpr h.somePath_mem) ⟨1, by simp⟩

/-- In a homeomorphic model `Φ : OnePoint E ≃ₜ S` of the one-point compactification of a proper
locally connected metric space `E`, if the complement of `(Φ ∘ (↑)) '' K` for a closed set `K`
splits into the component of `Φ ∞` and a disjoint component `U₀` whose closure adds only points of
`(Φ ∘ (↑)) '' K`, then `U₀` pulls back to `filledHull K \ K`. -/
theorem preimage_connectedComponentIn_onePoint {S : Type*} [TopologicalSpace S]
    {K : Set E} (hK : IsClosed K) (Φ : OnePoint E ≃ₜ S) {q₀ : S}
    (hdisj : Disjoint (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ (Φ ∞))
      (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀))
    (hcompl : ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ =
      connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ (Φ ∞) ∪
        connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀)
    (hcl₀ : closure (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀) ⊆
      connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀ ∪
        (Φ ∘ ((↑) : E → OnePoint E)) '' K) :
    (Φ ∘ ((↑) : E → OnePoint E)) ⁻¹'
        connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀ =
      filledHull K \ K := by
  let ψ : E → S := Φ ∘ ((↑) : E → OnePoint E)
  let U₀ : Set S := connectedComponentIn (ψ '' K)ᶜ q₀
  have hψ : IsOpenEmbedding ψ := Φ.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
  have hinf : Φ ∞ ∉ ψ '' K := by
    rintro ⟨x, -, hx⟩
    exact OnePoint.coe_ne_infty x (Φ.injective hx)
  have hcl_sub : closure U₀ ⊆ range ψ :=
    closure_connectedComponentIn_subset_range_onePoint Φ hdisj hcl₀
  have : CompactSpace S := Φ.compactSpace
  refine Subset.antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hxK : x ∉ K := fun h ↦ connectedComponentIn_subset _ _ hx ⟨x, h, rfl⟩
    have hU₀x : connectedComponentIn (ψ '' K)ᶜ (ψ x) = U₀ := (connectedComponentIn_eq hx).symm
    have himg := hψ.isInducing.image_connectedComponentIn_preimage
      (F := (ψ '' K)ᶜ) (y := x) (hU₀x.symm ▸ (subset_closure.trans hcl_sub))
    rw [preimage_compl, hψ.injective.preimage_image, hU₀x] at himg
    have : CompactSpace (closure U₀) := isCompact_iff_compactSpace.1 isClosed_closure.isCompact
    have hD_comp : IsCompact (ψ ⁻¹' closure U₀) := isCompact_iff_compactSpace.2
      (hψ.isEmbedding.homeomorphOfSubsetRange hcl_sub).symm.compactSpace
    have hsub : connectedComponentIn Kᶜ x ⊆ ψ ⁻¹' closure U₀ := by
      rw [← hψ.injective.preimage_image (connectedComponentIn Kᶜ x), himg]
      exact preimage_mono subset_closure
    exact ⟨mem_filledHull_iff.2 (hD_comp.isBounded.subset hsub), hxK⟩
  · have hxψ : ψ x ∈ (ψ '' K)ᶜ := fun ⟨w, hw, hwx⟩ ↦ hx.2 (hψ.injective hwx ▸ hw)
    refine (hcompl ▸ hxψ).resolve_left fun hxinf ↦ ?_
    set W : Set (OnePoint E) := ((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x
    have hW_open : IsOpen (Φ '' W) :=
      Φ.isOpenMap _ (OnePoint.isOpenEmbedding_coe.isOpenMap _
        hK.isOpen_compl.connectedComponentIn)
    have hW_cl : closure (Φ '' W) ⊆ Φ '' W ∪ ψ '' K := by
      rw [← Φ.image_closure]
      exact (image_mono (closure_image_coe_connectedComponentIn_subset hK hx.1)).trans
        (by simp only [W, ψ, image_union, image_image, Function.comp_apply]; exact Subset.rfl)
    have hsub := isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hW_open
      ⟨ψ x, hxinf, ⟨x, mem_image_of_mem _ (mem_connectedComponentIn hx.2), rfl⟩⟩ fun z hz ↦
        (hW_cl hz.1).resolve_right (connectedComponentIn_subset _ _ hz.2)
    obtain ⟨_, ⟨y, _, hy⟩, hΦ⟩ := hsub (mem_connectedComponentIn hinf)
    exact OnePoint.coe_ne_infty y (hy.trans (Φ.injective hΦ))

/-- Under the hypotheses of `TauCeti.preimage_connectedComponentIn_onePoint`, when the closure of
the complementary component `U₀` equals `U₀ ∪ (Φ ∘ (↑)) '' K`, its closure pulls back to
`filledHull K`. -/
theorem preimage_closure_connectedComponentIn_onePoint {S : Type*} [TopologicalSpace S]
    {K : Set E} (hK : IsClosed K) (Φ : OnePoint E ≃ₜ S) {q₀ : S}
    (hdisj : Disjoint (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ (Φ ∞))
      (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀))
    (hcompl : ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ =
      connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ (Φ ∞) ∪
        connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀)
    (hcl₀ : closure (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀) =
      connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀ ∪
        (Φ ∘ ((↑) : E → OnePoint E)) '' K) :
    (Φ ∘ ((↑) : E → OnePoint E)) ⁻¹'
        closure (connectedComponentIn ((Φ ∘ ((↑) : E → OnePoint E)) '' K)ᶜ q₀) =
      filledHull K := by
  have hψ : Function.Injective (Φ ∘ ((↑) : E → OnePoint E)) :=
    Φ.injective.comp OnePoint.coe_injective
  rw [hcl₀, preimage_union,
    preimage_connectedComponentIn_onePoint hK Φ hdisj hcompl hcl₀.subset,
    hψ.preimage_image, sdiff_union_self, union_eq_left.2 subset_filledHull]

end TauCeti
