/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Covering maps from local sections of uniform radius

Let `p : E → X` be a continuous map from a Hausdorff space to a locally connected pseudometric
space. Suppose that there is one radius `ε > 0` such that every point `e : E` lies on a
continuous local section of `p` over the ball of radius `ε` about `p e`, and that the image of
that ball under the section is open. Then `p` is a covering map.

This is the form in which coverings arise from gluing constructions: the sections are written
down by hand, and the uniformity of their radius is the completeness that rules out a local
homeomorphism which is not a covering. A typical use is the covering of a homogeneous space by
a space glued from translates of a tile, as in Poincaré's polygon theorem.

The sheets over a point `x` are the images, under the sections through the points of the fibre
over `x`, of a connected open neighbourhood `V` of `x` inside the ball of radius `ε / 2`. Two
sections that agree at one point of `V` agree on all of `V`, because `p` is locally injective
and `E` is Hausdorff. Every point `e'` over `V` lies on its own section, whose ball contains
`V`, so `e'` lies on the sheet through the point of the fibre where that section passes.

## Main results

* `IsCoveringMap.of_forall_exists_section`: a continuous map with local sections of uniform
  radius and open image, from a Hausdorff space to a locally connected pseudometric space, is a
  covering map.

## References

* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (covering spaces).
-/

public section

open Set Metric Topology

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [PseudoMetricSpace X] {p : E → X}

/-- **A map with local sections of uniform radius is a covering map.** Let `p : E → X` be a
continuous map from a Hausdorff space to a locally connected pseudometric space, and let
`ε > 0`. If every point `e` is the value at `p e` of a section of `p` over the ball of radius
`ε` about `p e` which is continuous on that ball and maps it to an open set, then `p` is a
covering map. -/
theorem _root_.IsCoveringMap.of_forall_exists_section [T2Space E] [LocallyConnectedSpace X]
    (hp : Continuous p) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ e, ∃ s : X → E, ContinuousOn s (ball (p e) ε) ∧ IsOpen (s '' ball (p e) ε) ∧
      (∀ x ∈ ball (p e) ε, p (s x) = x) ∧ s (p e) = e) :
    IsCoveringMap p := by
  choose s hsc hso hps hse using h
  -- `p` is injective on the image of each section
  have hinjOn (e : E) {V : Set X} (hV : V ⊆ ball (p e) ε) : InjOn p (s e '' V) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
    rw [hps e y (hV hy), hps e z (hV hz)] at hyz
    rw [hyz]
  have hinj : IsLocallyInjective p := fun e ↦
    ⟨s e '' ball (p e) ε, hso e, ⟨p e, mem_ball_self hε, hse e⟩, hinjOn e subset_rfl⟩
  -- two sections agreeing at one point of a preconnected set inside both balls agree on it
  have hagree {V : Set X} {e e' : E} (hV : IsPreconnected V) (he : V ⊆ ball (p e) ε)
      (he' : V ⊆ ball (p e') ε) {y : X} (hy : y ∈ V) (hee' : s e y = s e' y) :
      EqOn (s e) (s e') V :=
    (T2Space.isSeparatedMap p).eqOn_of_comp_eqOn hinj hV ((hsc e).mono he) ((hsc e').mono he')
      (fun z hz ↦ by simp only [Function.comp_apply, hps e z (he hz), hps e' z (he' hz)]) hy hee'
  -- the image of an open part of a ball under its section is open
  have himage (e : E) {V : Set X} (hV : V ⊆ ball (p e) ε) (hVo : IsOpen V) :
      IsOpen (s e '' V) := by
    convert (hso e).inter (hVo.preimage hp) using 1
    ext e'
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hV hy, rfl⟩, by rwa [mem_preimage, hps e y (hV hy)]⟩
    · rintro ⟨⟨y, hy, rfl⟩, hy'⟩
      rw [mem_preimage, hps e y hy] at hy'
      exact ⟨y, hy', rfl⟩
  intro x
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVx⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.1 (ball_mem_nhds x (half_pos hε))
  -- `V` lies in the ball about each point over `V`
  have hVball (e : E) (he : p e ∈ V) : V ⊆ ball (p e) ε := fun y hy ↦ by
    have h₁ := mem_ball.1 (hVx hy)
    have h₂ := mem_ball'.1 (hVx he)
    rw [mem_ball]
    linarith [dist_triangle y x (p e)]
  have hfib (e : E) (he : e ∈ p ⁻¹' {x}) : V ⊆ ball (p e) ε :=
    hVball e (by rwa [mem_singleton_iff.1 (mem_preimage.1 he)])
  have hsx (e : E) (he : e ∈ p ⁻¹' {x}) : s e x = e := by
    rw [← mem_singleton_iff.1 (mem_preimage.1 he), hse]
  -- each point over `V` lies on the sheet through a point of the fibre
  have hmem (e' : E) (he' : p e' ∈ V) :
      s e' x ∈ p ⁻¹' {x} ∧ e' ∈ s (s e' x) '' V := by
    have hfx : s e' x ∈ p ⁻¹' {x} := hps e' x (hVball e' he' hxV)
    refine ⟨hfx, p e', he', ?_⟩
    rw [hagree hVc.isPreconnected (hfib _ hfx) (hVball e' he') hxV (hsx _ hfx) he', hse]
  by_cases hF : (p ⁻¹' {x}).Nonempty
  swap
  · have : IsEmpty (p ⁻¹' {x}) := isEmpty_coe_sort.2 (not_nonempty_iff_eq_empty.1 hF)
    exact .of_preimage_eq_empty _ (hVo.mem_nhds hxV)
      (eq_empty_of_forall_notMem fun e' he' ↦ hF ⟨_, (hmem e' he').1⟩)
  have : DiscreteTopology (p ⁻¹' {x}) := isDiscrete_iff_discreteTopology.1 <|
    isDiscrete_iff_forall_mem_exists_isOpen.2 fun e he ↦ ⟨s e '' ball (p e) ε, hso e, by
      refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨⟨p e, mem_ball_self hε, hse e⟩, he⟩)
      rintro _ ⟨⟨y, hy, rfl⟩, hy'⟩
      rw [mem_preimage, hps e y hy, mem_singleton_iff] at hy'
      rw [hy', hsx e he, mem_singleton_iff]⟩
  have : Nonempty (X → E) := ⟨fun _ ↦ hF.some⟩
  have : Nonempty (p ⁻¹' {x}) := hF.to_subtype
  refine .of_trivialization (t := hVo.trivializationDiscrete (fun e : p ⁻¹' {x} ↦ s e '' V) V
    (fun e W hWV ↦ ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩) (fun e ↦ hinjOn e (hfib e e.2))
    (fun e y hy ↦ ⟨s e y, mem_image_of_mem _ hy, hps e y (hfib e e.2 hy)⟩) ?_ ?_) hxV
  · -- an open subset of `V` has open preimage in each sheet
    exact (hp.isOpen_preimage W hW).inter (himage e (hfib e e.2) hVo)
  · -- conversely, an open trace on a sheet comes from an open subset of `V`
    convert ((hsc e).mono (hfib e e.2)).isOpen_inter_preimage hVo hW using 1
    ext y
    constructor
    · intro hy
      refine ⟨hWV hy, ?_, mem_image_of_mem _ (hWV hy)⟩
      rwa [mem_preimage, hps e y (hfib e e.2 (hWV hy))]
    · rintro ⟨hyV, hyW, -⟩
      rwa [mem_preimage, hps e y (hfib e e.2 hyV)] at hyW
  · -- distinct points of the fibre have disjoint sheets
    intro e e' hee'
    refine disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    have hzy' : z = y := by
      rw [← hps e' z (hfib e' e'.2 hz), hzy, hps e y (hfib e e.2 hy)]
    subst hzy'
    refine hee' (Subtype.ext ?_)
    rw [← hsx e e.2, ← hsx e' e'.2]
    exact hagree hVc.isPreconnected (hfib e e.2) (hfib e' e'.2) hy hzy.symm hxV
  · exact fun e' he' ↦ mem_iUnion.2 ⟨⟨_, (hmem e' he').1⟩, (hmem e' he').2⟩

end TauCeti
