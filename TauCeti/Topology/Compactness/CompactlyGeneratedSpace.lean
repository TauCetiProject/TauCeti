/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Instances.Shrink

/-!
# Continuity and universe-polymorphic transfer for compactly generated topologies

Mathlib's `TopologicalSpace.compactlyGenerated X` is the topology on `X` coinduced by continuous
maps from compact Hausdorff spaces in `Type u`, and `UCompactlyGeneratedSpace.{u} X` asserts that
the topology of `X` agrees with `TopologicalSpace.compactlyGenerated.{u} X` (with `u` independent
of the universe of `X`). This file provides basic continuity and transfer lemmas:

* `TauCeti.continuous_compactlyGenerated_iff`: a map out of
  `TopologicalSpace.compactlyGenerated.{u} X` is continuous if and only if its composites with the
  continuous maps from compact Hausdorff spaces in `Type u` are, complementing Mathlib's
  `continuous_from_compactlyGenerated`.
* `IsCompact.exists_compHaus_homeomorph`: every `u`-small Hausdorff compact subset is homeomorphic
  to a compact Hausdorff space in `Type u`.
* `Homeomorph.uCompactlyGeneratedSpace` and `Homeomorph.uCompactlyGeneratedSpace_iff`:
  `u`-compact generation transfers across homeomorphisms between arbitrary universes.
-/

public section

universe u v w

/-- Every `u`-small Hausdorff compact subset is homeomorphic to a compact Hausdorff space in
`Type u`. -/
theorem IsCompact.exists_compHaus_homeomorph {Y : Type w} [TopologicalSpace Y] {K : Set Y}
    (hK : IsCompact K) [T2Space K] [Small.{u} K] : ∃ S : CompHaus.{u}, Nonempty (S ≃ₜ K) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e := Shrink.homeomorph.{u} K
  have : CompactSpace (Shrink.{u} K) := e.compactSpace
  have : T2Space (Shrink.{u} K) := e.t2Space
  exact ⟨CompHaus.of (Shrink.{u} K), ⟨e.symm⟩⟩

namespace Homeomorph

variable {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- Compact generation with test spaces in `Type u` transfers along homeomorphisms. -/
theorem uCompactlyGeneratedSpace [UCompactlyGeneratedSpace.{u} X] (e : X ≃ₜ Y) :
    UCompactlyGeneratedSpace.{u} Y :=
  uCompactlyGeneratedSpace_of_coinduced e.continuous e.isQuotientMap.eq_coinduced

/-- Homeomorphic spaces are `u`-compactly generated for the same universes `u`. -/
theorem uCompactlyGeneratedSpace_iff (e : X ≃ₜ Y) :
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

end TauCeti
