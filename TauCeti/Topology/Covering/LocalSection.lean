/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import TauCeti.Topology.SeparatedMap

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

/-- The trivialisation step: if the fibre `p ⁻¹' {x}` is nonempty, and `V` is a connected open
neighbourhood of `x` lying in the ball of every point of the fibre over `x` (`hfib`), with every
point over `V` on the sheet `s e '' V` through some point `e` of the fibre (`hmem`), then `x` is
evenly covered by `p`. -/
private lemma isEvenlyCovered_of_sections [T2Space E] (hp : Continuous p) {ε : ℝ}
    {s : E → X → E} (hsc : ∀ e, ContinuousOn (s e) (ball (p e) ε))
    (hso : ∀ e, IsOpen (s e '' ball (p e) ε)) (hps : ∀ e, ∀ x ∈ ball (p e) ε, p (s e x) = x)
    (hinj : IsLocallyInjective p) {x : X} {V : Set X} (hVo : IsOpen V)
    (hxV : x ∈ V) (hVc : IsConnected V) (hF : (p ⁻¹' {x}).Nonempty)
    (hfib : ∀ e ∈ p ⁻¹' {x}, V ⊆ ball (p e) ε) (hsx : ∀ e ∈ p ⁻¹' {x}, s e x = e)
    (hmem : ∀ e', p e' ∈ V → s e' x ∈ p ⁻¹' {x} ∧ e' ∈ s (s e' x) '' V) :
    IsEvenlyCovered p x (p ⁻¹' {x}) := by
  have : DiscreteTopology (p ⁻¹' {x}) := (discreteTopology_iff_locallyInjective x).2 <| by
    convert hinj.comp_right continuous_subtype_val Subtype.val_injective using 1
    exact funext fun e ↦ (mem_singleton_iff.1 e.2).symm
  have : Nonempty (X → E) := ⟨fun _ ↦ hF.some⟩
  have : Nonempty (p ⁻¹' {x}) := hF.to_subtype
  refine .of_trivialization (t := hVo.trivializationDiscrete (fun e : p ⁻¹' {x} ↦ s e '' V) V
    (fun e W hWV ↦ ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩)
    (fun e ↦ (LeftInvOn.rightInvOn_image fun y hy ↦ hps e y (hfib e e.2 hy)).injOn)
    (fun e y hy ↦ ⟨s e y, mem_image_of_mem _ hy, hps e y (hfib e e.2 hy)⟩) ?_ ?_) hxV
  · -- an open subset of `V` has open preimage in each sheet
    have hl : LeftInvOn p (s e) (ball (p e) ε) := hps e
    have himg : s e '' V = p ⁻¹' V ∩ s e '' ball (p e) ε := by
      simpa only [inter_eq_left.mpr (hfib e e.2)] using hl.image_inter' (s₁ := V)
    exact (hp.isOpen_preimage W hW).inter (himg ▸ (hVo.preimage hp).inter (hso e))
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
    exact hinj.eqOn_of_leftInvOn hVc.isPreconnected ((hsc e).mono (hfib e e.2))
      ((hsc e').mono (hfib e' e'.2)) (fun y hy ↦ hps e y (hfib e e.2 hy))
      (fun y hy ↦ hps e' y (hfib e' e'.2 hy)) hy hzy.symm hxV
  · exact fun e' he' ↦ mem_iUnion.2 ⟨⟨_, (hmem e' he').1⟩, (hmem e' he').2⟩

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
  have hinj : IsLocallyInjective p := fun e ↦
    ⟨s e '' ball (p e) ε, hso e, ⟨p e, mem_ball_self hε, hse e⟩,
      (LeftInvOn.rightInvOn_image (hps e)).injOn⟩
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
    rw [hinj.eqOn_of_leftInvOn hVc.isPreconnected ((hsc _).mono (hfib _ hfx))
      ((hsc _).mono (hVball e' he')) (fun y hy ↦ hps _ y (hfib _ hfx hy))
      (fun y hy ↦ hps _ y (hVball e' he' hy)) hxV (hsx _ hfx) he', hse]
  by_cases hF : (p ⁻¹' {x}).Nonempty
  · exact isEvenlyCovered_of_sections hp hsc hso hps hinj hVo hxV hVc hF hfib hsx hmem
  · have : IsEmpty (p ⁻¹' {x}) := isEmpty_coe_sort.2 (not_nonempty_iff_eq_empty.1 hF)
    exact .of_preimage_eq_empty _ (hVo.mem_nhds hxV)
      (eq_empty_of_forall_notMem fun e' he' ↦ hF ⟨_, (hmem e' he').1⟩)

end TauCeti
