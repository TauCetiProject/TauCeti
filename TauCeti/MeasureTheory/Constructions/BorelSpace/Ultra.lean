/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Closed balls generate the Borel σ-algebra of an ultrametric space

In an ultrametric space every closed ball of positive radius is open, and two closed balls are
nested or disjoint. Hence the closed balls of positive radius form a topological basis and a
π-system, and in a second-countable ultrametric space they generate the Borel σ-algebra.

## Main results

* `IsUltrametricDist.isTopologicalBasis_closedBall`: the closed balls of positive radius form a
  basis of the topology.
* `IsUltrametricDist.borel_eq_generateFrom_closedBall`: they generate the Borel σ-algebra of a
  second-countable ultrametric space.
* `IsUltrametricDist.isPiSystem_closedBall`: they form a π-system.
-/

public section

open Set Metric

namespace IsUltrametricDist

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

/-- In an ultrametric space, the closed balls of positive radius form a basis of the topology. -/
theorem isTopologicalBasis_closedBall :
    TopologicalSpace.IsTopologicalBasis {s : Set X | ∃ x, ∃ r > 0, s = closedBall x r} :=
  TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    (by rintro _ ⟨x, r, hr, rfl⟩; exact isOpen_closedBall _ hr.ne') fun x u hx hu ↦ by
      obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu x hx
      exact ⟨closedBall x (ε / 2), ⟨x, ε / 2, half_pos hε, rfl⟩,
        mem_closedBall_self (by positivity), (closedBall_subset_ball (half_lt_self hε)).trans hεu⟩

/-- In a second-countable ultrametric space, the closed balls of positive radius generate the
Borel σ-algebra. -/
theorem borel_eq_generateFrom_closedBall [SecondCountableTopology X] :
    borel X = MeasurableSpace.generateFrom {s | ∃ x, ∃ r > 0, s = closedBall x r} :=
  isTopologicalBasis_closedBall.borel_eq_generateFrom

/-- The closed balls of positive radius of an ultrametric space form a π-system: two of them are
nested or disjoint. -/
theorem isPiSystem_closedBall : IsPiSystem {s : Set X | ∃ x, ∃ r > 0, s = closedBall x r} := by
  rintro _ ⟨x, r, hr, rfl⟩ _ ⟨y, t, ht, rfl⟩ hne
  rcases closedBall_subset_trichotomy (x := x) (y := y) (r := r) (s := t) with h | h | h
  · exact ⟨x, r, hr, inter_eq_left.2 h⟩
  · exact ⟨y, t, ht, inter_eq_right.2 h⟩
  · exact absurd hne (not_nonempty_iff_eq_empty.2 h.inter_eq)

end IsUltrametricDist
