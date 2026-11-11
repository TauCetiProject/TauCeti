/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Separated and locally injective maps

A continuous separated map `f : X → Y` separates the points of each fibre by disjoint open sets,
and continuity pulls back the separation of points with distinct images when `Y` is Hausdorff.
So the source of a continuous separated map to a Hausdorff space is Hausdorff. Covering maps are
separated (`IsCoveringMap.isSeparatedMap`), so the total space of a covering of a Hausdorff space
is Hausdorff.

The fibers of a locally injective map are discrete
(`IsLocallyInjective.isDiscrete_preimage_singleton`), so a compact subset of one fiber is finite
(`IsLocallyInjective.finite_preimage_singleton_inter`); this needs no topology on the codomain.
For a separated, locally injective map, such as a covering map or any locally injective map with
Hausdorff total space, two sections over a preconnected set that are continuous on that set and
agree at one of its points agree on all of it (`IsSeparatedMap.eqOn_of_leftInvOn`). The same
holds for two maps with equal composites with a map `p` that is only injective on an open set,
provided one of the two maps takes its values there (`Set.InjOn.eqOn_of_comp_eqOn`).
-/

public section

open Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {f : X → Y}

/-- The source of a continuous separated map to a Hausdorff space is Hausdorff. -/
theorem IsSeparatedMap.t2Space (sep : IsSeparatedMap f) (hf : Continuous f) : T2Space X := by
  refine t2Space_iff_disjoint_nhds.2 fun x y hxy ↦ ?_
  by_cases h : f x = f y
  · exact isSeparatedMap_iff_disjoint_nhds.1 sep x y h hxy
  · exact (Filter.disjoint_comap (disjoint_nhds_nhds.2 h)).mono (hf.tendsto x).le_comap
      (hf.tendsto y).le_comap

/-- The total space of a covering of a Hausdorff space is Hausdorff. -/
theorem IsCoveringMap.t2Space (hf : IsCoveringMap f) : T2Space X :=
  hf.isSeparatedMap.t2Space hf.continuous

section IsLocallyInjective

open Set

variable {E B : Type*} [TopologicalSpace E] {p : E → B}

/-- The fibers of a locally injective map, such as a local homeomorphism, are discrete. -/
theorem IsLocallyInjective.isDiscrete_preimage_singleton (hp : IsLocallyInjective p) (b : B) :
    IsDiscrete (p ⁻¹' {b}) := by
  -- `p` is constant on the fiber and locally injective.
  have hb : p ∘ ((↑) : ↥(p ⁻¹' {b}) → E) = fun _ ↦ b := funext fun e ↦ e.2
  exact ⟨(discreteTopology_iff_locallyInjective b).2 <|
    hb ▸ hp.comp_right continuous_subtype_val Subtype.val_injective⟩

/-- A compact set of points in one fiber of a locally injective map, such as a local
homeomorphism, is finite. -/
theorem IsLocallyInjective.finite_preimage_singleton_inter (hp : IsLocallyInjective p)
    {s : Set E} {b : B} (hs : IsCompact (p ⁻¹' {b} ∩ s)) : (p ⁻¹' {b} ∩ s).Finite :=
  hs.finite <| (hp.isDiscrete_preimage_singleton b).mono inter_subset_left

/-- Two sections of `p` over a preconnected set `S` that are continuous on `S` and agree at one
point of `S` agree on `S`, when `p` is separated and locally injective. Every map with Hausdorff
total space is separated (`T2Space.isSeparatedMap`), and so is every covering map
(`IsCoveringMap.isSeparatedMap`). -/
theorem IsSeparatedMap.eqOn_of_leftInvOn [TopologicalSpace B] (sep : IsSeparatedMap p)
    (hinj : IsLocallyInjective p) {S : Set B} {s s' : B → E} (hS : IsPreconnected S)
    (hs : ContinuousOn s S) (hs' : ContinuousOn s' S) (hl : LeftInvOn p s S)
    (hl' : LeftInvOn p s' S) {y : B} (hy : y ∈ S) (hee' : s y = s' y) : EqOn s s' S :=
  sep.eqOn_of_comp_eqOn hinj hS hs hs'
    (fun z hz ↦ by simp only [Function.comp_apply, hl hz, hl' hz]) hy hee'

/-- Two maps that are continuous on a preconnected set `S`, agree at one point of `S` and have the
same composite with `p` on `S` agree on `S`, when `p` is injective on an open set `W` containing
the values of the first map on `S`. The values of the second map need not lie in `W`. For
instance, two continuous paths of square roots of the same path of operators, starting at the same
point, agree when the first stays in an open set on which squaring is injective. -/
theorem Set.InjOn.eqOn_of_comp_eqOn [T2Space E] {A : Type*} [TopologicalSpace A] {W : Set E}
    (hp : InjOn p W) (hW : IsOpen W) {S : Set A} (hS : IsPreconnected S) {g₁ g₂ : A → E}
    (h₁ : ContinuousOn g₁ S) (h₂ : ContinuousOn g₂ S) (hg₁ : MapsTo g₁ S W)
    (he : EqOn (p ∘ g₁) (p ∘ g₂) S) {a : A} (ha : a ∈ S) (hga : g₁ a = g₂ a) :
    EqOn g₁ g₂ S := by
  rw [isPreconnected_iff_preconnectedSpace] at hS
  rw [continuousOn_iff_continuous_domRestrict] at h₁ h₂
  -- In `S`, the locus where the two maps agree is closed, and it is open: near a point of it the
  -- values of both maps lie in `W`, where `p` is injective.
  have hclosed : IsClosed {x : S | g₁ x = g₂ x} := by
    simpa only [Set.domRestrict_apply] using isClosed_eq h₁ h₂
  have hopen : IsOpen {x : S | g₁ x = g₂ x} := by
    refine isOpen_iff_mem_nhds.2 fun x (hx : g₁ x = g₂ x) ↦ ?_
    have hx₂ : g₂ x ∈ W := hx ▸ hg₁ x.2
    filter_upwards [h₂.continuousAt.preimage_mem_nhds (hW.mem_nhds hx₂)] with y hy
    exact hp (hg₁ y.2) hy (he y.2)
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨a, ha⟩, hga⟩
  exact fun x hx ↦ (huniv.symm ▸ mem_univ (⟨x, hx⟩ : S) : (⟨x, hx⟩ : S) ∈ {x : S | g₁ x = g₂ x})

end IsLocallyInjective
