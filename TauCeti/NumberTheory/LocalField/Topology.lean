/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import TauCeti.NumberTheory.LocalField.NormedField
public import TauCeti.Topology.Algebra.ValuativeRel.Nonarchimedean

/-!
# Point-set topology of a nonarchimedean local field

A nonarchimedean local field `K` is Hausdorff (Mathlib's `IsValuativeTopology.instT2Space`) and
locally compact (part of `IsNonarchimedeanLocalField K`). This file adds that it is second
countable, and records that it is totally disconnected: its valuative topology is nonarchimedean
(`TauCeti.instNonarchimedeanRingOfIsValuativeTopology`), so Mathlib's
`NonarchimedeanAddGroup.instTotallySeparated` applies.

These four properties are what the point topology on the rational points of an affine group over
`K` inherits (`TauCeti/Topology/Algebra/PointTopology/Separation.lean`).

Second countability is proved through the normalized absolute value
(`TauCeti.normalizedNontriviallyNormedField`): a locally compact nontrivially normed field is a
proper metric space, and proper metric spaces are second countable.

## Main declarations

* `TauCeti.instSecondCountableTopologyOfIsNonarchimedeanLocalField`: a nonarchimedean local field
  is second countable.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A nonarchimedean local field is second countable. -/
instance instSecondCountableTopologyOfIsNonarchimedeanLocalField : SecondCountableTopology K := by
  -- Work with the metric of the normalized absolute value, whose topology is the given one only
  -- propositionally, and transport the conclusion back along `normalizedNormedField_topology_eq`.
  let _ := normalizedNontriviallyNormedField K
  have : @WeaklyLocallyCompactSpace K (normalizedNormedFieldTopology K) := by
    rw [normalizedNormedField_topology_eq]
    infer_instance
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have h : @SecondCountableTopology K (normalizedNormedFieldTopology K) :=
    secondCountable_of_proper
  rwa [normalizedNormedField_topology_eq] at h

/- A nonarchimedean local field is totally disconnected, by
`TauCeti.instNonarchimedeanRingOfIsValuativeTopology`, Mathlib's
`NonarchimedeanAddGroup.instTotallySeparated` and `IsValuativeTopology.instT2Space`. -/
example : TotallyDisconnectedSpace K := inferInstance

end TauCeti
