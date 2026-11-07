/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Hausdorff spaces over Hausdorff spaces

A continuous separated map `f : X → Y` separates the points of each fibre by disjoint open sets,
and continuity pulls back the separation of points with distinct images when `Y` is Hausdorff.
So the source of a continuous separated map to a Hausdorff space is Hausdorff. Covering maps are
separated (`IsCoveringMap.isSeparatedMap`), so the total space of a covering of a Hausdorff space
is Hausdorff.

The fibers of a locally injective map are discrete, so a compact subset of one fiber is finite
(`IsLocallyInjective.finite_preimage_singleton_inter`). Sections of a locally injective map to a
Hausdorff space that agree at one point of a preconnected set agree on all of it
(`IsLocallyInjective.eqOn_of_leftInvOn`).
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

section FiniteFiber

variable {E B : Type*} [TopologicalSpace E] {p : E → B}

/-- A compact set of points in one fiber of a locally injective map, such as a local
homeomorphism, is finite. -/
theorem IsLocallyInjective.finite_preimage_singleton_inter (hp : IsLocallyInjective p)
    {s : Set E} {b : B} (hs : IsCompact (p ⁻¹' {b} ∩ s)) : (p ⁻¹' {b} ∩ s).Finite := by
  -- The fiber is discrete: `p` is constant on it and locally injective.
  have hb : p ∘ ((↑) : ↥(p ⁻¹' {b} ∩ s) → E) = fun _ ↦ b := funext fun e ↦ e.2.1
  exact hs.finite ⟨(discreteTopology_iff_locallyInjective b).2 <|
    hb ▸ hp.comp_right continuous_subtype_val Subtype.val_injective⟩

end FiniteFiber

section LeftInvOn

open Set

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- Two sections of `p` over a preconnected set `S` that are continuous on `S` and agree at one
point of `S` agree on `S`, when `p` is locally injective and the total space is Hausdorff. -/
theorem IsLocallyInjective.eqOn_of_leftInvOn [T2Space E] (hinj : IsLocallyInjective p)
    {S : Set X} {s s' : X → E} (hS : IsPreconnected S) (hs : ContinuousOn s S)
    (hs' : ContinuousOn s' S) (hl : LeftInvOn p s S) (hl' : LeftInvOn p s' S) {y : X} (hy : y ∈ S)
    (hee' : s y = s' y) : EqOn s s' S :=
  (T2Space.isSeparatedMap p).eqOn_of_comp_eqOn hinj hS hs hs'
    (fun z hz ↦ by simp only [Function.comp_apply, hl hz, hl' hz]) hy hee'

end LeftInvOn
