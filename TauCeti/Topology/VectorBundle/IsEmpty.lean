/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.FiberBundle.Empty

/-!
# Vector bundles over an empty base

Over an empty base space, the canonical empty-atlas fibre bundle `TauCeti.fiberBundleOfIsEmpty` is
a topological vector bundle (`TauCeti.vectorBundleOfIsEmpty`).
-/

public section
open Bundle
namespace TauCeti
universe u v w
variable {B : Type u} [TopologicalSpace B] [IsEmpty B] (F : Type v) (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

/-- Over an empty base, `fiberBundleOfIsEmpty` is a `VectorBundle`. -/
theorem vectorBundleOfIsEmpty (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] :
    let _ : FiberBundle F E := fiberBundleOfIsEmpty F E
    VectorBundle 𝕜 F E := by
  let _ : FiberBundle F E := fiberBundleOfIsEmpty F E
  have h : ∀ e : Trivialization F (π F E), e ∉ trivializationAtlas F E := by
    rw [trivializationAtlas_fiberBundleOfIsEmpty]; exact fun e ↦ Set.notMem_empty e
  exact ⟨fun _ he ↦ (h _ he.out).elim, fun _ _ he _ ↦ (h _ he.out).elim⟩

end TauCeti
