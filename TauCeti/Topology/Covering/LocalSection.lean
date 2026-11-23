/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.UniformSpace.Defs
public import TauCeti.Topology.SeparatedMap

/-!
# Covering maps from local sections

A continuous separated, locally injective map to a locally connected space is a covering map
if every base point has a neighbourhood over which there are continuous sections through every
point of its preimage. The neighbourhood may depend on the base point; no metric is required.

The sheets over `x` are the images of a connected open neighbourhood under sections through
points of the fibre. Local injectivity makes these images open. Separatedness and local
injectivity make sections that agree at one point agree throughout a connected set, so distinct
points of the fibre give disjoint sheets and these sheets exhaust the preimage. Mathlib's
`IsOpen.trivializationDiscrete` assembles these sheets into a trivialization over the interior
of the neighbourhood.

The uniform-size criterion on a uniform space is a special case. Its sections, over the balls
of one fixed entourage `U`, have images that are neighbourhoods of the points they pass through,
which supply local injectivity, and the ball of a symmetric entourage `V` with `V ○ V ⊆ U` fits
inside the section domain of every point lying over it. On a pseudometric space this is the
uniform-radius criterion with the half-radius ball, which applies to gluing constructions such
as Poincaré's polygon theorem.

## Main results

* `IsEvenlyCovered.of_leftInvOn_sections`: continuous sections through every point over a
  preconnected neighbourhood give an evenly covered point for a continuous separated,
  locally injective map.
* `IsCoveringMap.of_isLocallyInjective_of_forall_exists_section`: the neighbourhood criterion
  for a continuous separated, locally injective map to a locally connected space.
* `IsCoveringMap.of_forall_exists_section`: the uniform-size criterion for a continuous
  separated map to a locally connected uniform space, whose section images are neighbourhoods.

## References

* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (covering spaces).
-/

public section

open Set Topology Uniformity

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- Continuous sections through every point over a preconnected neighbourhood of `x` make
`x` evenly covered by a continuous separated, locally injective map. -/
theorem _root_.IsEvenlyCovered.of_leftInvOn_sections (hp : Continuous p)
    (hinj : IsLocallyInjective p) (hsep : IsSeparatedMap p) {x : X} {V : Set X}
    (hVx : V ∈ 𝓝 x) (hVc : IsPreconnected V) {s : E → X → E}
    (hsc : ∀ e, p e ∈ V → ContinuousOn (s e) V)
    (hps : ∀ e, p e ∈ V → LeftInvOn p (s e) V)
    (hse : ∀ e, p e ∈ V → s e (p e) = e) : IsEvenlyCovered p x (p ⁻¹' {x}) := by
  have hxV : x ∈ V := mem_of_mem_nhds hVx
  have hxI : x ∈ interior V := mem_interior_iff_mem_nhds.2 hVx
  have hfibx (e : E) : e ∈ p ⁻¹' {x} ↔ p e = x := mem_preimage.trans mem_singleton_iff
  have hfib (e : E) (he : e ∈ p ⁻¹' {x}) : p e ∈ V := ((hfibx e).1 he) ▸ hxV
  have hsx (e : E) (he : e ∈ p ⁻¹' {x}) : s e x = e := by
    rw [← (hfibx e).1 he, hse e (hfib e he)]
  -- the sections through the fibre over `x`, restricted to `interior V`
  have hsc' (e : p ⁻¹' {x}) : ContinuousOn (s e) (interior V) :=
    (hsc e (hfib e e.property)).mono interior_subset
  have hps' (e : p ⁻¹' {x}) : LeftInvOn p (s e) (interior V) :=
    (hps e (hfib e e.property)).mono interior_subset
  have hrigid (e e' : E) (he : p e ∈ V) (he' : p e' ∈ V) {y : X}
      (hy : y ∈ V) (hee' : s e y = s e' y) : EqOn (s e) (s e') V :=
    hsep.eqOn_of_leftInvOn hinj hVc (hsc e he) (hsc e' he')
      (hps e he) (hps e' he') hy hee'
  have hmem (e' : E) (he' : p e' ∈ V) : ∃ e ∈ p ⁻¹' {x}, s e (p e') = e' := by
    have hfx : s e' x ∈ p ⁻¹' {x} := (hfibx _).2 (hps e' he' hxV)
    refine ⟨s e' x, hfx, ?_⟩
    rw [hrigid _ e' (hfib _ hfx) he' hxV (hsx _ hfx) he', hse e' he']
  obtain hF | hF := (p ⁻¹' {x}).eq_empty_or_nonempty
  · have : IsEmpty (p ⁻¹' {x}) := isEmpty_coe_sort.2 hF
    exact .of_preimage_eq_empty _ hVx <| eq_empty_of_forall_notMem fun e' he' ↦
      (hmem e' (mem_preimage.1 he')).elim fun _ he ↦ notMem_empty _ (hF.subset he.1)
  have : DiscreteTopology (p ⁻¹' {x}) := (hinj.isDiscrete_preimage_singleton x).to_subtype
  have : Nonempty (X → E) := ⟨fun _ ↦ hF.some⟩
  have : Nonempty (p ⁻¹' {x}) := hF.to_subtype
  -- Trivialize over the interior; rigidity still uses the preconnected set `V`.
  refine .of_trivialization (t := isOpen_interior.trivializationDiscrete
    (fun e : p ⁻¹' {x} ↦ s e '' interior V) (interior V)
    (fun e W hWV ↦ ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩) (fun e ↦ (hps' e).rightInvOn_image.injOn)
    (fun e ↦ (hps' e).surjOn (mapsTo_image _ _)) ?_ ?_) hxI
  · -- an open subset of `interior V` has open preimage in each sheet
    exact (hp.isOpen_preimage W hW).inter
      (hinj.isOpen_image_of_leftInvOn hp isOpen_interior (hsc' e) (hps' e))
  · -- conversely, an open trace on a sheet comes from an open subset of `interior V`
    rw [← (hps' e).image_inter', inter_eq_left.2 hWV] at hW
    rw [← (hps' e).injOn.preimage_image_inter hWV, inter_comm]
    exact (hsc' e).isOpen_inter_preimage isOpen_interior hW
  · -- distinct points of the fibre have disjoint sheets
    refine fun e e' hee' ↦ disjoint_image_image fun y hy z hz hyz ↦ ?_
    obtain rfl : z = y := by rw [← hps' e' hz, ← hyz, hps' e hy]
    refine hee' (Subtype.ext ?_)
    rw [← hsx e e.property, ← hsx e' e'.property]
    exact hrigid e e' (hfib e e.property) (hfib e' e'.property) (interior_subset hy) hyz hxV
  · -- the sheets exhaust the preimage of `interior V`
    intro e' he'
    have hpI : p e' ∈ interior V := mem_preimage.1 he'
    exact (hmem e' (interior_subset hpI)).elim fun e he ↦
      mem_iUnion.2 ⟨⟨e, he.1⟩, p e', hpI, he.2⟩

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
  -- choose a section for every point, with junk values off the preimage of `U`
  have hs' (e : E) : ∃ s : X → E, p e ∈ U →
      ContinuousOn s U ∧ LeftInvOn p s U ∧ s (p e) = e := by
    by_cases he : p e ∈ U
    exacts [(hs e he).imp fun _ h _ ↦ h, ⟨fun _ ↦ e, (absurd · he)⟩]
  choose s hsc hps hse using hs'
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.1 hU
  exact .of_leftInvOn_sections hp hinj hsep (hVo.mem_nhds hxV) hVc.isPreconnected
    (fun e he ↦ (hsc e (hVU he)).mono hVU) (fun e he ↦ (hps e (hVU he)).mono hVU)
    (fun e he ↦ hse e (hVU he))

/-- **A map with local sections of uniform size is a covering map.** Let `p : E → X` be a
continuous separated map to a locally connected uniform space, and let `U` be an entourage of
`X`. If every point `e` has a section of `p` over the `U`-ball about `p e` which is continuous
on that ball and maps it onto a neighbourhood of `e`, then `p` is a covering map. Such a section
passes through `e`. For a pseudometric space, `U` may be the entourage `{q | dist q.1 q.2 < ε}`
for some `ε > 0`, whose balls are the open `ε`-balls (`Metric.ball_eq_ball'`). -/
theorem _root_.IsCoveringMap.of_forall_exists_section {X : Type*} [UniformSpace X]
    [LocallyConnectedSpace X] {p : E → X} (hp : Continuous p) (hsep : IsSeparatedMap p)
    {U : SetRel X X} (hU : U ∈ 𝓤 X)
    (h : ∀ e, ∃ s : X → E, ContinuousOn s (U.ball (p e)) ∧ s '' U.ball (p e) ∈ 𝓝 e ∧
      LeftInvOn p s (U.ball (p e))) : IsCoveringMap p := by
  choose s hsc hsn hps using h
  -- `e` lies in the image of its section, so the section passes through `e`
  have hse (e : E) : s e (p e) = e := (hps e).rightInvOn_image (mem_of_mem_nhds (hsn e))
  have hinj : IsLocallyInjective p := isLocallyInjective_iff_nhds.2 fun e ↦
    ⟨s e '' U.ball (p e), hsn e, (hps e).rightInvOn_image.injOn⟩
  obtain ⟨V, hV, hVs, hVU⟩ := comp_symm_mem_uniformity_sets hU
  refine .of_isLocallyInjective_of_forall_exists_section hp hinj hsep
    fun x ↦ ⟨SetRel.ball V x, SetRel.ball_mem_nhds x hV, fun e he ↦ ?_⟩
  -- the `V`-ball about `x` lies in the `U`-ball about each point `p e` of it
  have hball : SetRel.ball V x ⊆ U.ball (p e) :=
    SetRel.ball_subset_ball_of_comp_subset (SetRel.symm V (SetRel.mem_ball.1 he)) hVU
  exact ⟨s e, (hsc e).mono hball, (hps e).mono hball, hse e⟩

end TauCeti
