/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Compactness.Lindelof
import TauCeti.MeasureTheory.Function.LocalRepresentative

/-!
# Gluing local `Cⁿ` representatives on a manifold

A function on a manifold that agrees almost everywhere near each point of a Lindelöf set `Ω` with
a `Cⁿ` function into a Hausdorff manifold agrees almost everywhere on `Ω` with a single function
that is `Cⁿ` on `Ω`. Two local representatives are continuous and agree almost everywhere on their
common open domain, so for a measure that charges every nonempty open set they agree everywhere
there (`MeasureTheory.Measure.eqOn_open_of_ae_eq`). The value at `y` of any representative near
`y` therefore defines the glued function on `Ω`, and the Lindelöf property turns the local almost
everywhere equalities into a global one without assuming second countability of the ambient
manifold (`TauCeti.exists_eqOn_ae_eq_of_locally`).

This is how regularity proved in charts, for instance by Euclidean elliptic regularity, becomes
regularity of one representative on a Lindelöf subset or the whole manifold. The case `n = 0` glues
continuous representatives. It is the manifold counterpart of
`TauCeti.exists_contDiffOn_ae_eq_of_locally`.

## Main results

* `TauCeti.exists_contMDiffOn_ae_eq_of_locally`: local `Cⁿ` representatives on a Lindelöf subset
  glue to a single `Cⁿ` representative on that subset.
* `TauCeti.exists_contMDiff_ae_eq_of_locally`: local `Cⁿ` representatives on a Lindelöf manifold
  glue to a global `Cⁿ` representative.

## Attribution

Adapted from the manifold gluing lemma of
[TauCetiProject/TauCeti#40536](https://github.com/TauCetiProject/TauCeti/pull/40536).
-/

public section

open MeasureTheory Set Filter Topology
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]
  {μ : Measure M} [μ.IsOpenPosMeasure] {n : WithTop ℕ∞} {u : M → N}

/-- **Gluing local `Cⁿ` representatives on a manifold subset.** If near each point of a Lindelöf
set `Ω` the function `u` agrees almost everywhere with a function `Cⁿ` on a neighbourhood of that
point, then `u` agrees almost everywhere on `Ω` with a single function `Cⁿ` on `Ω`. The measure
must charge every nonempty open set. -/
theorem exists_contMDiffOn_ae_eq_of_locally {Ω : Set M} (hΩ : IsLindelof Ω)
    (h : ∀ x ∈ Ω, ∃ U ∈ 𝓝 x, ∃ g : M → N, ContMDiffOn I I' n g U ∧ u =ᵐ[μ.restrict U] g) :
    ∃ g : M → N, ContMDiffOn I I' n g Ω ∧ u =ᵐ[μ.restrict Ω] g := by
  obtain ⟨G, hG, huG⟩ := exists_eqOn_ae_eq_of_locally hΩ
    (P := fun s g ↦ ContMDiffOn I I' n g s)
    (fun hst hg ↦ hg.mono hst) (fun hg ↦ hg.continuousOn) h
  refine ⟨G, contMDiffOn_of_locally_contMDiffOn fun x hx ↦ ?_, huG⟩
  obtain ⟨U, hUo, hxU, g, hg, hGg⟩ := hG x hx
  exact ⟨U, hUo, hxU, (hg.mono inter_subset_right).congr hGg⟩

/-- **Gluing local `Cⁿ` representatives on a manifold.** If near each point of `M` the function
`u` agrees almost everywhere with a function that is `Cⁿ` on a neighbourhood of that point, then
`u` agrees almost everywhere with a single globally `Cⁿ` function. The measure must charge every
nonempty open set. -/
theorem exists_contMDiff_ae_eq_of_locally [LindelofSpace M]
    (h : ∀ x, ∃ U ∈ 𝓝 x, ∃ g : M → N, ContMDiffOn I I' n g U ∧ u =ᵐ[μ.restrict U] g) :
    ∃ g : M → N, ContMDiff I I' n g ∧ u =ᵐ[μ] g := by
  obtain ⟨g, hg, hug⟩ := exists_contMDiffOn_ae_eq_of_locally isLindelof_univ fun x _ ↦ h x
  exact ⟨g, contMDiffOn_univ.1 hg, by rwa [Measure.restrict_univ] at hug⟩

end TauCeti
