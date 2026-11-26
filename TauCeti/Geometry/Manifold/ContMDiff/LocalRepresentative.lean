/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Compactness.Lindelof
import TauCeti.MeasureTheory.Function.Gluing

/-!
# Gluing local `Cⁿ` representatives on a manifold

A function on a manifold that agrees almost everywhere near each point with a `Cⁿ` function
agrees almost everywhere with a single globally `Cⁿ` function. Two local representatives are
continuous and agree almost everywhere on their common open domain, so for a measure that charges
every nonempty open set they agree everywhere there, and on the Lindelöf manifold they glue to one
representative (`IsLindelof.exists_ae_eq_and_eqOn_of_forall_ae_eq_continuousOn`).

This is how regularity proved in charts, for instance by Euclidean elliptic regularity, becomes
regularity of one representative on the whole manifold. The case `n = 0` glues continuous
representatives. It is the manifold counterpart of `TauCeti.exists_contDiffOn_ae_eq_of_locally`.

## Main results

* `TauCeti.exists_contMDiff_ae_eq_of_locally`: local `Cⁿ` representatives glue to a global `Cⁿ`
  representative.

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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M] [MeasurableSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]
  {μ : Measure M} [μ.IsOpenPosMeasure] {n : WithTop ℕ∞} {u : M → N}

/-- **Gluing local `Cⁿ` representatives on a manifold.** If near each point of `M` the function
`u` agrees almost everywhere with a function that is `Cⁿ` on a neighbourhood of that point, then
`u` agrees almost everywhere with a single globally `Cⁿ` function. The measure must charge every
nonempty open set. -/
theorem exists_contMDiff_ae_eq_of_locally
    (h : ∀ x, ∃ U ∈ 𝓝 x, ∃ g : M → N, ContMDiffOn I I' n g U ∧ u =ᵐ[μ.restrict U] g) :
    ∃ g : M → N, ContMDiff I I' n g ∧ u =ᵐ[μ] g := by
  -- Shrink every neighbourhood to an open one.
  have h' : ∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧
      ∃ g : M → N, ContMDiffOn I I' n g U ∧ u =ᵐ[μ.restrict U] g := by
    intro x
    obtain ⟨U, hU, g, hg, hug⟩ := h x
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, g,
      hg.mono interior_subset, ae_restrict_of_ae_restrict_of_subset interior_subset hug⟩
  choose U hUo hxU g hg hug using h'
  -- The continuous local representatives agree on overlaps and glue to one representative.
  obtain ⟨G, huG, hG⟩ := isLindelof_univ.exists_ae_eq_and_eqOn_of_forall_ae_eq_continuousOn
    (μ := μ) (fun x _ ↦ hUo x) (fun x _ ↦ hxU x) (fun x _ ↦ (hg x).continuousOn) fun x _ ↦ hug x
  exact ⟨G, fun x ↦ ((hg x).congr fun y hy ↦ hG x trivial ⟨hy, trivial⟩).contMDiffAt
    ((hUo x).mem_nhds (hxU x)), huG⟩

end TauCeti
