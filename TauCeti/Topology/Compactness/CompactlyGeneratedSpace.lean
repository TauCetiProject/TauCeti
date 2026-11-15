/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyCoherentSpace
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Instances.Shrink

/-!
# Continuity and universe-polymorphic transfer for compactly generated topologies

Mathlib's `TopologicalSpace.compactlyGenerated X` is the topology on `X` coinduced by continuous
maps from compact Hausdorff spaces in `Type u`, and `UCompactlyGeneratedSpace.{u} X` asserts that
the topology of `X` agrees with `TopologicalSpace.compactlyGenerated.{u} X` (with `u` independent
of the universe of `X`). This file provides basic continuity, transfer, and recognition lemmas for
`TopologicalSpace.compactlyGenerated.{u}`, `UCompactlyGeneratedSpace.{u}`, and `CompHaus.{u}` test
maps:

* `TauCeti.continuous_compactlyGenerated_iff`: a map out of
  `TopologicalSpace.compactlyGenerated.{u} X` is continuous if and only if its composites with the
  continuous maps from compact Hausdorff spaces in `Type u` are, complementing Mathlib's
  `continuous_from_compactlyGenerated`.
* `IsCompact.exists_compHaus_isCompact_image_eq`: every `u`-small compact subset of a Hausdorff
  space is the image of a compact subset of a compact Hausdorff space in `Type u` under a continuous
  map.
* `Homeomorph.uCompactlyGeneratedSpace` and `Homeomorph.uCompactlyGeneratedSpace_iff`:
  `u`-compact generation transfers across homeomorphisms between arbitrary universes.
* `TauCeti.uCompactlyGeneratedSpace_of_compactlyCoherentSpace`: every `u`-small Hausdorff
  compactly coherent space (in particular every `u`-small Hausdorff weakly locally compact space or
  `CompactlyGeneratedSpace`) is `u`-compactly generated.
-/

public section

universe u v w

/-- Every `u`-small compact subset of a Hausdorff space is the image of a compact subset of a
compact Hausdorff space in `Type u` under a continuous map. -/
theorem IsCompact.exists_compHaus_isCompact_image_eq {Y : Type w} [TopologicalSpace Y] [T2Space Y]
    {K : Set Y} (hK : IsCompact K) [Small.{u} K] :
    ∃ (S : CompHaus.{u}) (L : Set S) (f : C(S, Y)), IsCompact L ∧ f '' L = K := by
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  let e := Shrink.homeomorph.{u} ↑K
  have : CompactSpace (Shrink.{u} ↑K) := e.compactSpace
  have : T2Space (Shrink.{u} ↑K) :=
    T2Space.of_injective_continuous e.symm.injective e.symm.continuous
  refine ⟨CompHaus.of (Shrink.{u} ↑K), Set.univ,
    ⟨Subtype.val ∘ e.symm, continuous_subtype_val.comp e.symm.continuous⟩, isCompact_univ, ?_⟩
  ext x
  simpa using (e.symm.surjective.exists (p := fun z : ↑K ↦ (z : Y) = x)).symm

namespace Homeomorph

/-- Compact generation with test spaces in `Type u` transfers along homeomorphisms. -/
theorem uCompactlyGeneratedSpace {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [UCompactlyGeneratedSpace.{u} X] (e : X ≃ₜ Y) :
    UCompactlyGeneratedSpace.{u} Y :=
  uCompactlyGeneratedSpace_of_coinduced e.continuous e.isQuotientMap.eq_coinduced

/-- Homeomorphic spaces are `u`-compactly generated for the same universes `u`. -/
theorem uCompactlyGeneratedSpace_iff {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    UCompactlyGeneratedSpace.{u} X ↔ UCompactlyGeneratedSpace.{u} Y :=
  ⟨fun _ ↦ e.uCompactlyGeneratedSpace, fun _ ↦ e.symm.uCompactlyGeneratedSpace⟩

end Homeomorph

namespace TauCeti

open Topology

/-- A map out of the compactly generated topology is continuous if and only if its composites with
the continuous maps from compact Hausdorff spaces are. -/
theorem continuous_compactlyGenerated_iff {X : Type w} [TopologicalSpace X] {Y : Type v}
    [t : TopologicalSpace Y] {f : X → Y} :
    Continuous[TopologicalSpace.compactlyGenerated.{u} X, t] f ↔
      ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g) := by
  refine ⟨fun hf S g => ?_, continuous_from_compactlyGenerated f⟩
  rw [TopologicalSpace.compactlyGenerated, continuous_coinduced_dom, continuous_sigma_iff] at hf
  exact hf ⟨S, g⟩

/-- A `u`-small Hausdorff compactly coherent space is `u`-compactly generated. -/
theorem uCompactlyGeneratedSpace_of_compactlyCoherentSpace (X : Type w)
    [TopologicalSpace X] [Small.{u} X] [T2Space X] [CompactlyCoherentSpace X] :
    UCompactlyGeneratedSpace.{u} X := by
  refine uCompactlyGeneratedSpace_of_isOpen fun s hs ↦
    CompactlyCoherentSpace.isOpen_iff.2 fun K hK ↦ ?_
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  let e := Shrink.homeomorph.{u} ↑K
  have : CompactSpace (Shrink.{u} ↑K) := e.compactSpace
  have : T2Space (Shrink.{u} ↑K) :=
    T2Space.of_injective_continuous e.symm.injective e.symm.continuous
  convert (hs (CompHaus.of (Shrink.{u} ↑K))
    ⟨Subtype.val ∘ e.symm, continuous_subtype_val.comp e.symm.continuous⟩).preimage e.continuous
  ext x
  simp

end TauCeti
