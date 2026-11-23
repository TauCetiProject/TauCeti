/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
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
(`IsLocallyInjective.finite_preimage_singleton_inter`), and every fiber of a locally injective map
out of a compact space is finite (`IsLocallyInjective.finite_preimage_singleton`); this needs no
topology on the codomain.
On a Hausdorff space, the neighbourhoods on which a locally injective map is injective can be
chosen pairwise disjoint over any finite set
(`IsLocallyInjective.exists_isOpen_injOn_pairwiseDisjoint`).
For a continuous locally injective map into a Hausdorff space, distinct equal-image pairs
form a closed set (`IsLocallyInjective.isClosed_setOf_apply_eq_and_ne`).
A continuous section of a continuous locally injective map over an open set has open image
(`IsLocallyInjective.isOpen_image_of_leftInvOn`).
For a separated, locally injective map, such as a covering map or any locally injective map with
Hausdorff total space, two sections over a preconnected set that are continuous on that set and
agree at one of its points agree on all of it (`IsSeparatedMap.eqOn_of_leftInvOn`).

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
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

/-- For a continuous locally injective map into a Hausdorff space, the set of distinct
pairs with the same image is closed. No separation assumption on the domain is needed. -/
theorem IsLocallyInjective.isClosed_setOf_apply_eq_and_ne
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {f : E → X} (hinj : IsLocallyInjective f) (hf : Continuous f) :
    IsClosed {z : E × E | f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
  have heq : IsClosed {z : E × E | f z.1 = f z.2} :=
    isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)
  have hopen : IsOpen {z : {z : E × E | f z.1 = f z.2} | z.val.1 = z.val.2} :=
    hinj.isOpen_eqLocus (by fun_prop) (by fun_prop) (funext fun z ↦ z.property)
  convert heq.isClosedMap_subtypeVal _ hopen.isClosed_compl using 1
  ext z
  constructor
  · rintro ⟨hz, hne⟩
    exact ⟨⟨z, hz⟩, hne, rfl⟩
  · rintro ⟨w, hne, rfl⟩
    exact ⟨w.property, hne⟩

variable {E B : Type*} [TopologicalSpace E] {p : E → B}

/-- The fibers of a locally injective map, such as a local homeomorphism, are discrete. -/
theorem IsLocallyInjective.isDiscrete_preimage_singleton (hp : IsLocallyInjective p) (b : B) :
    IsDiscrete (p ⁻¹' {b}) := by
  -- `p` is constant on the fiber and locally injective.
  have hb : p ∘ ((↑) : ↥(p ⁻¹' {b}) → E) = fun _ ↦ b := funext fun e ↦ e.property
  exact ⟨(discreteTopology_iff_locallyInjective b).2 <|
    hb ▸ hp.comp_right continuous_subtypeVal Subtype.val_injective⟩

/-- A compact set of points in one fiber of a locally injective map, such as a local
homeomorphism, is finite. -/
theorem IsLocallyInjective.finite_preimage_singleton_inter (hp : IsLocallyInjective p)
    {s : Set E} {b : B} (hs : IsCompact (p ⁻¹' {b} ∩ s)) : (p ⁻¹' {b} ∩ s).Finite :=
  hs.finite <| (hp.isDiscrete_preimage_singleton b).mono inter_subset_left

/-- Every fiber of a locally injective map out of a compact space, such as a local homeomorphism,
is finite. -/
theorem IsLocallyInjective.finite_preimage_singleton [CompactSpace E] (hp : IsLocallyInjective p)
    (b : B) : (p ⁻¹' {b}).Finite := by
  -- Finitely many open sets on which `p` is injective cover `E`, and each of them meets the fiber
  -- in at most one point.
  choose U hUo hxU hU using hp
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo fun x _ ↦ mem_iUnion.2 ⟨x, hxU x⟩
  refine (t.finite_toSet.biUnion fun x _ ↦ Set.Subsingleton.finite (s := U x ∩ p ⁻¹' {b})
    fun e he e' he' ↦ hU x he.1 he'.1 (he.2.trans he'.2.symm)).subset fun e he ↦ ?_
  obtain ⟨x, hx, hex⟩ := mem_iUnion₂.1 (ht (mem_univ e))
  exact mem_iUnion₂.2 ⟨x, hx, hex, he⟩

/-- A locally injective map `p` on a Hausdorff space, such as a local homeomorphism, is injective
on an open neighbourhood `W e` of each point `e`, and these neighbourhoods can be chosen pairwise
disjoint over the points of any given finite set `F`. -/
theorem IsLocallyInjective.exists_isOpen_injOn_pairwiseDisjoint [T2Space E]
    (hp : IsLocallyInjective p) {F : Set E} (hF : F.Finite) :
    ∃ W : E → Set E, (∀ e, IsOpen (W e)) ∧ (∀ e, e ∈ W e) ∧ (∀ e, InjOn p (W e)) ∧
      F.PairwiseDisjoint W := by
  obtain ⟨O, hO, hdisj⟩ := hF.t2_separation
  have hW (e : E) : ∃ W : Set E, IsOpen W ∧ e ∈ W ∧ W ⊆ O e ∧ InjOn p W := by
    obtain ⟨U, hU, heU, hinj⟩ := hp e
    exact ⟨O e ∩ U, (hO e).2.inter hU, ⟨(hO e).1, heU⟩, inter_subset_left,
      hinj.mono inter_subset_right⟩
  choose W hWo hWe hWO hWinj using hW
  exact ⟨W, hWo, hWe, hWinj, fun e he e' he' hne ↦ (hdisj he he' hne).mono (hWO e) (hWO e')⟩

/-- A continuous section of a continuous locally injective map `p` over an open set `V` has open
image. -/
theorem IsLocallyInjective.isOpen_image_of_leftInvOn [TopologicalSpace B]
    (hinj : IsLocallyInjective p)
    (hp : Continuous p) {V : Set B} (hV : IsOpen V) {s : B → E} (hs : ContinuousOn s V)
    (hps : LeftInvOn p s V) : IsOpen (s '' V) := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨U, hUo, hyU, hUinj⟩ := hinj (s y)
  have hsp : ContinuousAt (s ∘ p) (s y) := by
    refine ContinuousAt.comp ?_ hp.continuousAt
    rw [hps hy]
    exact hs.continuousAt (hV.mem_nhds hy)
  have hU' : s ∘ p ⁻¹' U ∈ 𝓝 (s y) := hsp.preimage_mem_nhds (by
    simpa only [Function.comp_apply, hps hy] using hUo.mem_nhds hyU)
  have hV' : p ⁻¹' V ∈ 𝓝 (s y) := hp.continuousAt.preimage_mem_nhds (by
    simpa only [hps hy] using hV.mem_nhds hy)
  filter_upwards [hUo.mem_nhds hyU, hU', hV'] with e heU hseU heV
  refine ⟨p e, heV, hUinj hseU heU ?_⟩
  exact hps heV

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

end IsLocallyInjective
