/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Rings with open units: the inverse

A topological monoid `M` has open units (`IsOpenUnits M`) when `Units.val : Mˣ → M` is an open
embedding: the units are open and inversion is continuous on them for the subspace topology.
In a monoid with zero with open units, `Ring.inverse` is therefore continuous at every unit.

## Main declarations

* `IsOpenUnits.continuousAt_ringInverse`: `Ring.inverse` is continuous at every unit of a ring
  with open units.
-/

public section

open Topology

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
