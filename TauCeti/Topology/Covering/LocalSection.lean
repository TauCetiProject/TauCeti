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
# Covering maps from local sections

A continuous separated, locally injective map to a locally connected space is a covering map
if every base point has a neighbourhood over which there are continuous sections through every
point of its preimage. The neighbourhood may depend on the base point; no metric is required.

The sheets over `x` are the images of a connected open neighbourhood under sections through
points of the fibre. Local injectivity makes these images open. Separatedness and local
injectivity make sections that agree at one point agree throughout a connected set, so distinct
points of the fibre give disjoint sheets and these sheets exhaust the preimage.

The uniform-radius metric criterion is a special case. Its sections have open images, which
supply local injectivity, and the half-radius ball fits inside the section domain of every point
lying over it. This form applies to gluing constructions such as Poincaré's polygon theorem.

## Main results

* `IsEvenlyCovered.of_leftInvOn_sections`: continuous sections through every point over a
  connected open neighbourhood give an evenly covered point for a continuous separated,
  locally injective map.
* `IsCoveringMap.of_isLocallyInjective_of_forall_exists_section`: the neighbourhood criterion
  for a continuous separated, locally injective map to a locally connected space.
* `IsCoveringMap.of_forall_exists_section`: the uniform-radius criterion for a continuous map
  from a Hausdorff space to a locally connected pseudometric space, with open section images.

## References

* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (covering spaces).
-/

public section

open Set Metric Topology

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- Continuous sections through every point over a connected open neighbourhood of `x` make
`x` evenly covered by a continuous separated, locally injective map. -/
theorem _root_.IsEvenlyCovered.of_leftInvOn_sections (hp : Continuous p)
    (hinj : IsLocallyInjective p) (hsep : IsSeparatedMap p) {x : X} {V : Set X}
    (hVo : IsOpen V) (hxV : x ∈ V) (hVc : IsConnected V) {s : E → X → E}
    (hsc : ∀ e, p e ∈ V → ContinuousOn (s e) V)
    (hps : ∀ e, p e ∈ V → LeftInvOn p (s e) V)
    (hse : ∀ e, p e ∈ V → s e (p e) = e) : IsEvenlyCovered p x (p ⁻¹' {x}) := by
  have hfib (e : E) (he : e ∈ p ⁻¹' {x}) : p e ∈ V := by
    rwa [mem_singleton_iff.1 he]
  have hsx (e : E) (he : e ∈ p ⁻¹' {x}) : s e x = e := by
    rw [← mem_singleton_iff.1 he, hse e (hfib e he)]
  have hrigid (e e' : E) (he : p e ∈ V) (he' : p e' ∈ V) {y : X}
      (hy : y ∈ V) (hee' : s e y = s e' y) : EqOn (s e) (s e') V :=
    hsep.eqOn_of_leftInvOn hinj hVc.isPreconnected (hsc e he) (hsc e' he')
      (hps e he) (hps e' he') hy hee'
  have hmem (e' : E) (he' : p e' ∈ V) : ∃ e ∈ p ⁻¹' {x}, e' ∈ s e '' V := by
    have hfx : s e' x ∈ p ⁻¹' {x} := hps e' he' hxV
    refine ⟨s e' x, hfx, p e', he', ?_⟩
    rw [hrigid _ e' (hfib _ hfx) he' hxV (hsx _ hfx) he', hse e' he']
  by_cases hF : (p ⁻¹' {x}).Nonempty
  swap
  · have : IsEmpty (p ⁻¹' {x}) := isEmpty_coe_sort.2 (not_nonempty_iff_eq_empty.1 hF)
    exact .of_preimage_eq_empty _ (hVo.mem_nhds hxV)
      (eq_empty_of_forall_notMem fun e' he' ↦ hF (by
        obtain ⟨e, he, -⟩ := hmem e' he'
        exact ⟨e, he⟩))
  have : DiscreteTopology (p ⁻¹' {x}) := (hinj.isDiscrete_preimage_singleton x).to_subtype
  have : Nonempty (X → E) := ⟨fun _ ↦ hF.some⟩
  have : Nonempty (p ⁻¹' {x}) := hF.to_subtype
  refine .of_trivialization (t := hVo.trivializationDiscrete (fun e : p ⁻¹' {x} ↦ s e '' V) V
    (fun e W hWV ↦ ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩)
    (fun e ↦ (LeftInvOn.rightInvOn_image (hps e (hfib e e.2))).injOn)
    (fun e y hy ↦ ⟨s e y, mem_image_of_mem _ hy, hps e (hfib e e.2) hy⟩) ?_ ?_) hxV
  · -- an open subset of `V` has open preimage in each sheet
    exact (hp.isOpen_preimage W hW).inter
      (hinj.isOpen_image_of_leftInvOn hp hVo (hsc e (hfib e e.2)) (hps e (hfib e e.2)))
  · -- conversely, an open trace on a sheet comes from an open subset of `V`
    convert (hsc e (hfib e e.2)).isOpen_inter_preimage hVo hW using 1
    ext y
    constructor
    · intro hy
      refine ⟨hWV hy, ?_, mem_image_of_mem _ (hWV hy)⟩
      rwa [mem_preimage, hps e (hfib e e.2) (hWV hy)]
    · rintro ⟨hyV, hyW, -⟩
      rwa [mem_preimage, hps e (hfib e e.2) hyV] at hyW
  · -- distinct points of the fibre have disjoint sheets
    intro e e' hee'
    refine disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    have hzy' : z = y := by
      rw [← hps e' (hfib e' e'.2) hz, hzy, hps e (hfib e e.2) hy]
    subst hzy'
    refine hee' (Subtype.ext ?_)
    rw [← hsx e e.2, ← hsx e' e'.2]
    exact hrigid e e' (hfib e e.2) (hfib e' e'.2) hy hzy.symm hxV
  · -- the sheets exhaust the preimage of `V`
    intro e' he'
    obtain ⟨e, he, he'e⟩ := hmem e' he'
    exact mem_iUnion.2 ⟨⟨e, he⟩, he'e⟩

/-- A continuous separated, locally injective map to a locally connected space is a covering
map if every base point has a neighbourhood admitting continuous sections through every point
of its preimage. -/
theorem _root_.IsCoveringMap.of_isLocallyInjective_of_forall_exists_section
    [LocallyConnectedSpace X] (hp : Continuous p) (hinj : IsLocallyInjective p)
    (hsep : IsSeparatedMap p)
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ e, p e ∈ U → ∃ s : X → E,
      ContinuousOn s U ∧ LeftInvOn p s U ∧ s (p e) = e) : IsCoveringMap p := by
  intro x
  obtain ⟨U, hU, hs⟩ := h x
  have hs' (e : E) : ∃ s : X → E, p e ∈ U →
      ContinuousOn s U ∧ LeftInvOn p s U ∧ s (p e) = e := by
    by_cases he : p e ∈ U
    · obtain ⟨s, hs⟩ := hs e he
      exact ⟨s, fun _ ↦ hs⟩
    · exact ⟨fun _ ↦ e, fun h ↦ absurd h he⟩
  choose s hs using hs'
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.1 hU
  exact .of_leftInvOn_sections hp hinj hsep hVo hxV hVc
    (fun e he ↦ ((hs e (hVU he)).1).mono hVU)
    (fun e he ↦ ((hs e (hVU he)).2.1).mono hVU)
    (fun e he ↦ (hs e (hVU he)).2.2)

/-- **A map with local sections of uniform radius is a covering map.** Let `p : E → X` be a
continuous map from a Hausdorff space to a locally connected pseudometric space, and let
`ε > 0`. If every point `e` is the value at `p e` of a section of `p` over the ball of radius
`ε` about `p e` which is continuous on that ball and maps it to an open set, then `p` is a
covering map. -/
theorem _root_.IsCoveringMap.of_forall_exists_section {X : Type*} [PseudoMetricSpace X]
    {p : E → X} [T2Space E] [LocallyConnectedSpace X] (hp : Continuous p) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ e, ∃ s : X → E, ContinuousOn s (ball (p e) ε) ∧ IsOpen (s '' ball (p e) ε) ∧
      (∀ x ∈ ball (p e) ε, p (s x) = x) ∧ s (p e) = e) : IsCoveringMap p := by
  choose s hsc hso hps hse using h
  have hinj : IsLocallyInjective p := fun e ↦
    ⟨s e '' ball (p e) ε, hso e, ⟨p e, mem_ball_self hε, hse e⟩,
      (LeftInvOn.rightInvOn_image (hps e)).injOn⟩
  refine .of_isLocallyInjective_of_forall_exists_section hp hinj (T2Space.isSeparatedMap p)
    fun x ↦ ⟨ball x (ε / 2), ball_mem_nhds x (half_pos hε), fun e he ↦ ?_⟩
  have hball : ball x (ε / 2) ⊆ ball (p e) ε := fun y hy ↦ by
    have h₁ := mem_ball.1 hy
    have h₂ := mem_ball'.1 he
    rw [mem_ball]
    linarith [dist_triangle y x (p e)]
  exact ⟨s e, (hsc e).mono hball, fun y hy ↦ hps e y (hball hy), hse e⟩

end TauCeti
