/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.LocalAtTarget

/-!
# Closed maps that cover an open set bijectively

A continuous closed map `f : X → Y` that sends the preimage of an open set `V` bijectively onto `V`
restricts to a homeomorphism `f⁻¹(V) ≃ₜ V`, so it is a local homeomorphism at every point of
`f⁻¹(V)` (`IsClosedMap.isLocalHomeomorphOn_preimage`). Every continuous map from a compact space to
a Hausdorff space is closed, so for such a map it suffices that each point of `V` have exactly one
preimage. This is how a map of compact manifolds is seen to be a local homeomorphism near a point
whose fibre is a single point, as the local degree computation of a map of spheres requires.
-/

public section

open Topology

/-- **A closed map is a local homeomorphism over an open set it covers bijectively.** If a
continuous closed map `f` sends the preimage of an open set `V` bijectively onto `V`, then it
restricts to a homeomorphism `f⁻¹(V) ≃ₜ V`, so it is a local homeomorphism at every point of
`f⁻¹(V)`. -/
theorem IsClosedMap.isLocalHomeomorphOn_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (hcl : IsClosedMap f) {V : Set Y}
    (hV : IsOpen V) (hbij : Set.BijOn f (f ⁻¹' V) V) : IsLocalHomeomorphOn f (f ⁻¹' V) := by
  -- The restriction `f⁻¹(V) → V` is a continuous closed bijection, hence a homeomorphism.
  have hres : Function.Bijective (V.restrictPreimage f) :=
    ⟨fun x y h ↦ Subtype.ext (hbij.injOn x.2 y.2 (congrArg Subtype.val h)),
      fun y ↦ by obtain ⟨x, hx, hxy⟩ := hbij.surjOn y.2; exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  let e := (Equiv.ofBijective _ hres).toHomeomorphOfContinuousClosed
    hf.restrictPreimage (hcl.restrictPreimage V)
  exact (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).2 fun x hx ↦
    ⟨f ⁻¹' V, (hV.preimage hf).mem_nhds hx, hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding⟩
