/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

/-!
# Continuity out of and universe lifting for compactly generated topologies

Mathlib's `continuous_from_compactlyGenerated` shows that a map out of the compactly generated
topology `TopologicalSpace.compactlyGenerated X` is continuous when its composites with the
continuous maps from compact Hausdorff spaces are. Here we record the converse
(`TauCeti.continuous_compactlyGenerated_iff`), together with universe monotonicity of
`UCompactlyGeneratedSpace` (`UCompactlyGeneratedSpace.ulift`) and its consequence for Hausdorff
weakly locally compact spaces (`UCompactlyGeneratedSpace.of_t2Space_of_weaklyLocallyCompactSpace`).
-/

public section

universe u v w

/-- If `X` is `v`-compactly generated, then it is `(max v u)`-compactly generated for every
universe `u`. -/
theorem UCompactlyGeneratedSpace.ulift {X : Type w} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{v} X] : UCompactlyGeneratedSpace.{max v u} X :=
  uCompactlyGeneratedSpace_of_isClosed fun _ h ↦
    UCompactlyGeneratedSpace.isClosed.{v} fun S f ↦
      (h (CompHaus.of (ULift.{u} S)) (f.comp ⟨ULift.down, continuous_uliftDown⟩)).preimage
        continuous_uliftUp

/-- A Hausdorff weakly locally compact space `X : Type w` is `(max w u)`-compactly generated for
every universe `u`. -/
theorem UCompactlyGeneratedSpace.of_t2Space_of_weaklyLocallyCompactSpace
    (X : Type w) [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X] :
    UCompactlyGeneratedSpace.{max w u} X :=
  UCompactlyGeneratedSpace.ulift.{u, w} (X := X)

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
