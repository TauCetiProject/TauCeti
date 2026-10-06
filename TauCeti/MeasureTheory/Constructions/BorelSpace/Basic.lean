/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability through an inducing map

For an inducing map `f : α → β` between Borel spaces, the Borel σ-algebra of `α` is the
pullback of the Borel σ-algebra of `β` along `f`. Hence a map `g` into `α` is measurable exactly
when `f ∘ g` is. Unlike `MeasurableEmbedding.measurable_comp_iff`, this needs no measurability
of the range of `f`: a topological embedding with non-measurable range still detects
measurability of maps into its domain.

## Main results

* `Topology.IsInducing.measurable_comp_iff`
-/

public section

open MeasureTheory Topology

/-- For an inducing map `f` between Borel spaces, a map `g` into the domain of `f` is measurable
exactly when `f ∘ g` is. -/
theorem Topology.IsInducing.measurable_comp_iff {α β γ : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [MeasurableSpace γ] {f : α → β} (hf : IsInducing f) {g : γ → α} :
    Measurable (f ∘ g) ↔ Measurable g := by
  have hα : ‹MeasurableSpace α› = MeasurableSpace.comap f ‹MeasurableSpace β› := by
    rw [BorelSpace.measurable_eq (α := α), BorelSpace.measurable_eq (α := β), hf.eq_induced,
      borel_comap]
  rw [measurable_iff_comap_le, measurable_iff_comap_le, hα, MeasurableSpace.comap_comp]
