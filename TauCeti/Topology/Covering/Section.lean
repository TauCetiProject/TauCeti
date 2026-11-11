/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Topology.SeparatedMap

/-!
# Covering maps from local sections through every point

Let `p : E → X` be a local homeomorphism from a Hausdorff space to a locally connected space.
Suppose that every point `x` of `X` has a neighbourhood `U` such that every point `e` lying over
`U` is the value at `p e` of a continuous section of `p` over `U`. Then `p` is a covering map.

The sheets over a point `x` are the images, under the sections through the points of the fibre
over `x`, of a connected open neighbourhood `V ⊆ U` of `x`. Each such image is open because `p`
is locally injective. Two sections over `V` that agree at one point agree on all of `V`, since `p`
is locally injective and `E` is Hausdorff; hence distinct points of the fibre have disjoint sheets,
and a point `e'` over `V` lies on the sheet through the point of the fibre where the section
through `e'` passes.

In contrast with `IsCoveringMap.of_forall_exists_section`, no metric on `X` and no uniform radius
is required: the neighbourhood `U` may depend on `x`. This is the form in which coverings arise
from Riemannian exponential maps, whose sections live on uniformly normal neighbourhoods.

## Main results

* `IsLocallyInjective.isOpen_image_of_leftInvOn`: a continuous section of a continuous locally
  injective map over an open set has open image.
* `IsCoveringMap.of_isLocalHomeomorph_of_forall_exists_section`: a local homeomorphism from a
  Hausdorff space to a locally connected space with continuous local sections through every point
  is a covering map.

## References

* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (covering spaces).
-/

public section

open Set Topology

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- A continuous section of a continuous locally injective map `p` over an open set `V` has open
image. -/
theorem _root_.IsLocallyInjective.isOpen_image_of_leftInvOn (hinj : IsLocallyInjective p)
    (hp : Continuous p) {V : Set X} (hV : IsOpen V) {s : X → E} (hs : ContinuousOn s V)
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

/-- The trivialisation step: if `V` is a connected open neighbourhood of `x`, the fibre over `x`
is nonempty, the sections `s e` through the points `e` of that fibre are continuous over `V` with
open images, and every point over `V` lies on the sheet through some point of the fibre, then `x`
is evenly covered by `p`. -/
private lemma isEvenlyCovered_of_sections [T2Space E] (hp : Continuous p)
    (hinj : IsLocallyInjective p) {x : X} {V : Set X} (hVo : IsOpen V) (hxV : x ∈ V)
    (hVc : IsConnected V) (hF : (p ⁻¹' {x}).Nonempty) {s : E → X → E}
    (hsc : ∀ e ∈ p ⁻¹' {x}, ContinuousOn (s e) V) (hso : ∀ e ∈ p ⁻¹' {x}, IsOpen (s e '' V))
    (hps : ∀ e ∈ p ⁻¹' {x}, LeftInvOn p (s e) V) (hsx : ∀ e ∈ p ⁻¹' {x}, s e x = e)
    (hmem : ∀ e', p e' ∈ V → ∃ e ∈ p ⁻¹' {x}, e' ∈ s e '' V) :
    IsEvenlyCovered p x (p ⁻¹' {x}) := by
  have : DiscreteTopology (p ⁻¹' {x}) := (discreteTopology_iff_locallyInjective x).2 <| by
    convert hinj.comp_right continuous_subtype_val Subtype.val_injective using 1
    exact funext fun e ↦ (mem_singleton_iff.1 e.2).symm
  have : Nonempty (X → E) := ⟨fun _ ↦ hF.some⟩
  have : Nonempty (p ⁻¹' {x}) := hF.to_subtype
  refine .of_trivialization (t := hVo.trivializationDiscrete (fun e : p ⁻¹' {x} ↦ s e '' V) V
    (fun e W hWV ↦ ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩)
    (fun e ↦ (LeftInvOn.rightInvOn_image (hps e e.2)).injOn)
    (fun e y hy ↦ ⟨s e y, mem_image_of_mem _ hy, hps e e.2 hy⟩) ?_ ?_) hxV
  · have himg : s e '' V = p ⁻¹' V ∩ s e '' V := by
      simpa only [inter_self] using (hps e e.2).image_inter' (s₁ := V)
    exact (hp.isOpen_preimage W hW).inter (himg ▸ (hVo.preimage hp).inter (hso e e.2))
  · convert (hsc e e.2).isOpen_inter_preimage hVo hW using 1
    ext y
    constructor
    · intro hy
      refine ⟨hWV hy, ?_, mem_image_of_mem _ (hWV hy)⟩
      rwa [mem_preimage, hps e e.2 (hWV hy)]
    · rintro ⟨hyV, hyW, -⟩
      rwa [mem_preimage, hps e e.2 hyV] at hyW
  · intro e e' hee'
    refine disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    have hzy' : z = y := by
      rw [← hps e' e'.2 hz, hzy, hps e e.2 hy]
    subst hzy'
    refine hee' (Subtype.ext ?_)
    rw [← hsx e e.2, ← hsx e' e'.2]
    exact (T2Space.isSeparatedMap p).eqOn_of_leftInvOn hinj hVc.isPreconnected (hsc e e.2)
      (hsc e' e'.2) (hps e e.2) (hps e' e'.2) hy hzy.symm hxV
  · intro e' he'
    obtain ⟨e, he, he'e⟩ := hmem e' he'
    exact mem_iUnion.2 ⟨⟨e, he⟩, he'e⟩

/-- **A local homeomorphism with continuous local sections through every point is a covering
map.** Let `p : E → X` be a local homeomorphism from a Hausdorff space to a locally connected
space. If every point `x` of `X` has a neighbourhood `U` such that every point `e` with
`p e ∈ U` is the value at `p e` of a section of `p` over `U` which is continuous on `U`, then
`p` is a covering map. -/
theorem _root_.IsCoveringMap.of_isLocalHomeomorph_of_forall_exists_section [T2Space E]
    [LocallyConnectedSpace X] (hp : IsLocalHomeomorph p)
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ e, p e ∈ U → ∃ s : X → E,
      ContinuousOn s U ∧ LeftInvOn p s U ∧ s (p e) = e) :
    IsCoveringMap p := by
  have hinj := hp.isLocallyInjective
  have hpc := hp.continuous
  intro x
  obtain ⟨U, hU, hs⟩ := h x
  have hs' (e : E) : ∃ s : X → E, p e ∈ U →
      ContinuousOn s U ∧ LeftInvOn p s U ∧ s (p e) = e := by
    by_cases he : p e ∈ U
    · obtain ⟨s, hs⟩ := hs e he
      exact ⟨s, fun _ ↦ hs⟩
    · exact ⟨fun _ ↦ e, fun h ↦ absurd h he⟩
  choose s hs using hs'
  have hsc (e : E) (he : p e ∈ U) := (hs e he).1
  have hps (e : E) (he : p e ∈ U) := (hs e he).2.1
  have hse (e : E) (he : p e ∈ U) := (hs e he).2.2
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.1 hU
  have hsc' (e : E) (he : p e ∈ V) : ContinuousOn (s e) V := (hsc e (hVU he)).mono hVU
  have hps' (e : E) (he : p e ∈ V) : LeftInvOn p (s e) V := (hps e (hVU he)).mono hVU
  have hfib (e : E) (he : e ∈ p ⁻¹' {x}) : p e ∈ V := by
    rwa [mem_singleton_iff.1 (mem_preimage.1 he)]
  have hsx (e : E) (he : e ∈ p ⁻¹' {x}) : s e x = e := by
    rw [← mem_singleton_iff.1 (mem_preimage.1 he), hse e (hVU (hfib e he))]
  have hmem (e' : E) (he' : p e' ∈ V) : ∃ e ∈ p ⁻¹' {x}, e' ∈ s e '' V := by
    have hfx : s e' x ∈ p ⁻¹' {x} := hps' e' he' hxV
    refine ⟨s e' x, hfx, p e', he', ?_⟩
    rw [(T2Space.isSeparatedMap p).eqOn_of_leftInvOn hinj hVc.isPreconnected
      (hsc' _ (hfib _ hfx)) (hsc' e' he') (hps' _ (hfib _ hfx)) (hps' e' he') hxV (hsx _ hfx) he',
      hse e' (hVU he')]
  by_cases hF : (p ⁻¹' {x}).Nonempty
  · exact isEvenlyCovered_of_sections hpc hinj hVo hxV hVc hF
      (fun e he ↦ hsc' e (hfib e he))
      (fun e he ↦ hinj.isOpen_image_of_leftInvOn hpc hVo (hsc' e (hfib e he))
        (hps' e (hfib e he)))
      (fun e he ↦ hps' e (hfib e he)) hsx hmem
  · have : IsEmpty (p ⁻¹' {x}) := isEmpty_coe_sort.2 (not_nonempty_iff_eq_empty.1 hF)
    exact .of_preimage_eq_empty _ (hVo.mem_nhds hxV)
      (eq_empty_of_forall_notMem fun e' he' ↦ hF (by
        obtain ⟨e, he, -⟩ := hmem e' he'
        exact ⟨e, he⟩))

end TauCeti
