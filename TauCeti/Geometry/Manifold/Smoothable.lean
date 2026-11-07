/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Smoothable spaces

A topological space `M` is **smoothable**, for a model with corners `I` on `H`, when it admits a
smooth structure compatible with its topology: some atlas of charts to `H` makes it a `C^∞`
manifold for `I` (`TauCeti.IsSmoothable I M`). The topology of `M` is fixed; only the atlas is
chosen. This is the predicate of the smoothing problems of four-dimensional topology, where a
closed topological `4`-manifold may or may not carry a smooth structure: Freedman's fake
projective plane `∗ℂℙ²` does not, and by Ruberman and Stern the connected sum `∗ℝℙ⁴ # ∗ℂℙ²`
does.

Every `C^∞` manifold is smoothable (`TauCeti.IsSmoothable.of_isManifold`), and smoothability is
invariant under homeomorphisms (`Homeomorph.isSmoothable_congr`): a smooth atlas of `M` is pulled
back along a homeomorphism `N ≃ₜ M` to a smooth atlas of `N` (`Homeomorph.pullback_isManifold`).

## Main definitions

* `TauCeti.IsSmoothable I M`: the space `M` admits a `C^∞` manifold structure modelled on `I`.

## Main results

* `TauCeti.isSmoothable_iff`: a smoothable space is one with a smooth atlas.
* `TauCeti.IsSmoothable.of_isManifold`: a `C^∞` manifold is smoothable.
* `TauCeti.IsSmoothable.of_homeomorph`, `Homeomorph.isSmoothable_congr`: smoothability is invariant
  under homeomorphisms.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (M : Type*) [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

/-- A topological space `M` is **smoothable** for the model `I` if it admits a smooth structure:
an atlas of charts to the model space for which `M` is a `C^∞` manifold. The topology of `M` is
the given one. -/
def IsSmoothable : Prop :=
  ∃ _ : ChartedSpace H M, IsManifold I ∞ M

variable {I M}

/-- A space is smoothable exactly when some atlas of charts to `H` makes it a `C^∞` manifold for
`I`. -/
theorem isSmoothable_iff : IsSmoothable I M ↔ ∃ _ : ChartedSpace H M, IsManifold I ∞ M :=
  Iff.rfl

/-- A `C^∞` manifold is smoothable. -/
theorem IsSmoothable.of_isManifold [ChartedSpace H M] [IsManifold I ∞ M] : IsSmoothable I M :=
  ⟨inferInstance, inferInstance⟩

/-- Smoothability is transported backwards along a homeomorphism: a smooth atlas of `M` pulls back
along `e : N ≃ₜ M` to a smooth atlas of `N`. -/
theorem IsSmoothable.of_homeomorph (h : IsSmoothable I M) (e : N ≃ₜ M) : IsSmoothable I N := by
  obtain ⟨_, _⟩ := h
  exact ⟨e.pullbackChartedSpace, Homeomorph.pullback_isManifold I ∞ e⟩

end TauCeti

namespace Homeomorph

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]

/-- Smoothability is invariant under homeomorphisms. -/
theorem isSmoothable_congr (e : N ≃ₜ M) : IsSmoothable I N ↔ IsSmoothable I M :=
  ⟨fun h => h.of_homeomorph e.symm, fun h => h.of_homeomorph e⟩

end Homeomorph
