/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
import TauCeti.Topology.Sets.Opens

/-!
# Partitions of unity subordinate to a finite bundle atlas

Let `A` be a finite bundle atlas of a vector bundle over a Hausdorff manifold modelled on a
finite-dimensional real normed space `E`. There is a smooth partition of unity `χ` indexed by the
charts, and in every chart `i` a chain of open sets `Q₀ ⋐ Q₁ ⋐ Q₂ ⋐ Q₃ ⋐ Aᵢ` of the chart image
`Aᵢ` with the support of `χᵢ` read in chart `i` inside `Q₀`
(`TauCeti.FiniteBundleAtlas.exists_nested_chart_sets`). Localization arguments use it to cut a
global object into pieces, each read in one chart with room for interior estimates.

## Main results

* `TauCeti.FiniteBundleAtlas.exists_nested_chart_sets`: a partition of unity with nested chart
  sets.
-/

public section

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace TauCeti

namespace FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

/-- **Nested chart sets.** There are a smooth partition of unity `χ` indexed by the charts and, in
every chart `i`, open sets `Q₀ ⋐ Q₁ ⋐ Q₂ ⋐ Q₃ ⋐ Aᵢ` of the chart image `Aᵢ`, the first two with
compact closure, with the support of `χᵢ` read in chart `i` inside `Q₀`. -/
theorem exists_nested_chart_sets :
    ∃ (χ : SmoothPartitionOfUnity (Fin A.n) 𝓘(ℝ, E) M univ) (Q₀ Q₁ Q₂ Q₃ : Fin A.n → Opens E),
      (∀ i, tsupport (χ i) ⊆ (A.chart i).symm '' Q₀ i) ∧
      (∀ i, IsCompact (closure (Q₀ i : Set E)) ∧ closure (Q₀ i : Set E) ⊆ Q₁ i) ∧
      (∀ i, IsCompact (closure (Q₁ i : Set E)) ∧ closure (Q₁ i : Set E) ⊆ Q₂ i) ∧
      (∀ i, closure (Q₂ i : Set E) ⊆ Q₃ i) ∧ (∀ i, closure (Q₃ i : Set E) ⊆ A.image i) ∧
      ∀ i, Q₀ i ≤ Q₃ i := by
  have := A.compactSpace
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ A.dom
    A.isOpen_dom (by rw [A.iUnion_dom])
  -- The support of `χᵢ` read in chart `i` is a compact subset of the chart image.
  have hK (i : Fin A.n) : IsCompact (A.chart i '' tsupport (χ i)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart i).continuousOn.mono ((hχ i).trans (A.dom_subset_chart_source i)))
  choose Q₃ hK₃ hQ₃ _ using fun i ↦ Opens.exists_between_and_isCompact_closure (hK i)
    fun _ hy ↦ A.mem_image.2 (image_mono (hχ i) hy)
  choose Q₂ hK₂ hQ₂ _ using fun i ↦ Opens.exists_between_and_isCompact_closure (hK i) (hK₃ i)
  choose Q₁ hK₁ hQ₁ hQ₁c using fun i ↦ Opens.exists_between_and_isCompact_closure (hK i) (hK₂ i)
  choose Q₀ hK₀ hQ₀ hQ₀c using fun i ↦ Opens.exists_between_and_isCompact_closure (hK i) (hK₁ i)
  refine ⟨χ, Q₀, Q₁, Q₂, Q₃, fun i x hx ↦ ⟨A.chart i x, hK₀ i (mem_image_of_mem _ hx),
    (A.chart i).left_inv (A.dom_subset_chart_source i (hχ i hx))⟩, fun i ↦ ⟨hQ₀c i, hQ₀ i⟩,
    fun i ↦ ⟨hQ₁c i, hQ₁ i⟩, hQ₂, hQ₃, fun i ↦ subset_closure.trans ((hQ₀ i).trans
      (subset_closure.trans ((hQ₁ i).trans (subset_closure.trans (hQ₂ i)))))⟩

end FiniteBundleAtlas

end TauCeti
