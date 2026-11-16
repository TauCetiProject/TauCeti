/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Compactly generated topologies and products with compact Hausdorff spaces

Mathlib's `continuous_from_compactlyGenerated` shows that a map out of the compactly generated
topology `TopologicalSpace.compactlyGenerated X` is continuous when its composites with the
continuous maps from compact Hausdorff spaces are. Here we record the converse, giving the
characterization `TauCeti.continuous_compactlyGenerated_iff`, and prove that the product of a
compactly generated space with a compact Hausdorff space in the test-space universe remains
compactly generated (`TauCeti.uCompactlyGeneratedSpace_prod_of_compactSpace`).
-/

public section

universe u v w

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

/-- The product of a compactly generated space with a compact Hausdorff space in the test-space
universe is compactly generated. -/
theorem uCompactlyGeneratedSpace_prod_of_compactSpace {X : Type w} {K : Type u}
    [TopologicalSpace X] [TopologicalSpace K] [UCompactlyGeneratedSpace.{u} X]
    [CompactSpace K] [T2Space K] : UCompactlyGeneratedSpace.{u} (X × K) := by
  refine uCompactlyGeneratedSpace_of_continuous_maps fun f hf ↦ ?_
  let q : (Σ i : (S : CompHaus.{u}) × C(S, X), i.1) → X := fun ⟨⟨_, g⟩, s⟩ ↦ g s
  have hq : IsQuotientMap q :=
    ⟨⟨eq_compactlyGenerated (X := X)⟩,
      fun x ↦ ⟨⟨⟨CompHaus.of PUnit.{u + 1}, ContinuousMap.const _ x⟩, PUnit.unit⟩, rfl⟩⟩
  refine hq.continuous_lift_prod_left ?_
  have hsig : Continuous fun p : Σ i : (S : CompHaus.{u}) × C(S, X), i.1 × K ↦
      f (p.1.2 p.2.1, p.2.2) :=
    continuous_sigma fun ⟨S, g⟩ ↦
      hf (CompHaus.of (S × K)) ⟨fun p ↦ (g p.1, p.2), (g.continuous.comp continuous_fst).prodMk
        continuous_snd⟩
  exact hsig.comp Homeomorph.sigmaProdDistrib.continuous

end TauCeti
