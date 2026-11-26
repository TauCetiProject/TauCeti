/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Rings with open units: the inverse and embeddings

A topological monoid `M` has open units (`IsOpenUnits M`) when `Units.val : Mˣ → M` is an open
embedding: the units are open and inversion is continuous on them for the subspace topology.
In a monoid with zero with open units, `Ring.inverse` is therefore continuous at every unit.
The property passes along embeddings: a monoid embedded in one with open units has open units as
soon as its own units form an open subset.

## Main declarations

* `IsOpenUnits.continuousAt_ringInverse`: `Ring.inverse` is continuous at every unit of a ring
  with open units.
* `IsOpenUnits.of_isEmbedding`: a monoid embedding into a monoid with open units whose units
  form an open subset has open units.
* `Units.instLocallyPathConnectedSpace`: the units of a locally path-connected monoid with open
  units are locally path connected; for instance the units of a real Banach algebra.
-/

public section

open Topology

/-- A topological monoid `M` has open units if it embeds, by a monoid homomorphism that is a
topological embedding, into a monoid with open units, and its units form an open subset of `M`.
For instance, the valuation ring of a field whose topology is defined by its valuation. -/
theorem IsOpenUnits.of_isEmbedding {M N : Type*} [Monoid M] [TopologicalSpace M] [Monoid N]
    [TopologicalSpace N] [IsOpenUnits N] {f : M →* N} (hf : IsEmbedding f)
    (h : IsOpen {x : M | IsUnit x}) : IsOpenUnits M where
  isOpenEmbedding_unitsVal := by
    refine ⟨?_, h⟩
    have e : (f : M → N) ∘ Units.val = Units.val ∘ Units.map f :=
      funext fun u ↦ (Units.coe_map f u).symm
    have : IsEmbedding ((f : M → N) ∘ Units.val) := by
      rw [e]
      exact IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.comp hf.units_map
    exact this.of_comp Units.continuous_val hf.continuous

/-- The units of a locally path-connected topological monoid with open units are locally path
connected, being an open subspace. For instance, the units of a real Banach algebra. -/
instance Units.instLocallyPathConnectedSpace {M : Type*} [Monoid M] [TopologicalSpace M]
    [IsOpenUnits M] [LocallyPathConnectedSpace M] : LocallyPathConnectedSpace Mˣ :=
  IsOpenUnits.isOpenEmbedding_unitsVal.locallyPathConnectedSpace

variable {R : Type*} [MonoidWithZero R] [TopologicalSpace R] [IsOpenUnits R]

/-- In a monoid with zero whose units are open with continuous inversion, `Ring.inverse` is
continuous at every unit. -/
theorem IsOpenUnits.continuousAt_ringInverse (u : Rˣ) : ContinuousAt Ring.inverse (u : R) := by
  rw [← IsOpenUnits.isOpenEmbedding_unitsVal.continuousAt_iff]
  have : (Ring.inverse ∘ Units.val : Rˣ → R) = fun v ↦ ↑v⁻¹ := by
    funext v
    exact Ring.inverse_unit v
  rw [this]
  exact Units.continuous_coe_inv.continuousAt
