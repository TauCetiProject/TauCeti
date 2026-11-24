/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Order

/-!
# Continuity out of and universe lifting for compactly generated topologies

Mathlib's `continuous_from_compactlyGenerated` shows that a map out of the compactly generated
topology `TopologicalSpace.compactlyGenerated X` is continuous when its composites with the
continuous maps from compact Hausdorff spaces are. Here we record the converse
(`TauCeti.continuous_compactlyGenerated_iff`), universe monotonicity of `UCompactlyGeneratedSpace`
(`UCompactlyGeneratedSpace.ulift`), and compact generation of the Sierpiński space `Prop`
(`TauCeti.compactlyGenerated_sierpinski`).
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

/-- A set is open in `TopologicalSpace.compactlyGenerated.{u} X` if and only if its preimage under
every continuous map from a `u`-small compact Hausdorff space into `X` is open. -/
theorem isOpen_compactlyGenerated_iff {X : Type w} [TopologicalSpace X] {U : Set X} :
    IsOpen[TopologicalSpace.compactlyGenerated.{u} X] U ↔
      ∀ (S : CompHaus.{u}) (g : C(S, X)), IsOpen (g ⁻¹' U) := by
  rw [TopologicalSpace.compactlyGenerated, isOpen_coinduced, isOpen_sigma_iff]
  exact Sigma.forall

/-- A set is closed in `TopologicalSpace.compactlyGenerated.{u} X` if and only if its preimage
under every continuous map from a `u`-small compact Hausdorff space into `X` is closed. -/
theorem isClosed_compactlyGenerated_iff {X : Type w} [TopologicalSpace X] {C : Set X} :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} X] C ↔
      ∀ (S : CompHaus.{u}) (g : C(S, X)), IsClosed (g ⁻¹' C) := by
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  exact Sigma.forall

/-- The Sierpiński space `Prop` is `u`-compactly generated for every universe `u`. -/
@[simp]
theorem compactlyGenerated_sierpinski :
    TopologicalSpace.compactlyGenerated.{u} Prop = sierpinskiSpace :=
  (eq_compactlyGenerated.{u} (X := Prop)).symm

end TauCeti
