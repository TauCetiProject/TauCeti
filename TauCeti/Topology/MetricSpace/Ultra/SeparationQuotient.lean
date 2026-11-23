/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric distance on separation quotients

The separation quotient `SeparationQuotient X` of a pseudometric space `X` carries the metric
satisfying `dist (mk x) (mk y) = dist x y`, with `mk : X → SeparationQuotient X` surjective.
Hence `SeparationQuotient X` is ultrametric if and only if `X` is ultrametric.

## Main results

* `SeparationQuotient.isUltrametricDist_iff`: `SeparationQuotient X` is ultrametric iff `X` is
  ultrametric.
* `SeparationQuotient.instIsUltrametricDist`: the separation quotient of an ultrametric
  pseudometric space is ultrametric.
-/

public section

namespace SeparationQuotient

/-- The separation quotient of a pseudometric space is ultrametric if and only if the space
itself is ultrametric. -/
@[simp]
theorem isUltrametricDist_iff {X : Type*} [PseudoMetricSpace X] :
    IsUltrametricDist (SeparationQuotient X) ↔ IsUltrametricDist X :=
  ⟨fun _ ↦ ⟨fun x y z ↦ by
    simpa only [dist_mk] using IsUltrametricDist.dist_triangle_max (mk x) (mk y) (mk z)⟩,
   fun _ ↦ ⟨surjective_mk.forall₃.2 fun a b c ↦ by
    simpa only [dist_mk] using IsUltrametricDist.dist_triangle_max a b c⟩⟩

/-- The separation quotient of an ultrametric pseudometric space is ultrametric. -/
instance instIsUltrametricDist {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X] :
    IsUltrametricDist (SeparationQuotient X) :=
  isUltrametricDist_iff.2 ‹_›

end SeparationQuotient
