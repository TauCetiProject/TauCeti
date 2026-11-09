/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction

/-!
# Scalar actions on discrete spaces

Any scalar action of a discrete space on a discrete space is jointly continuous. This supplies
the continuity hypothesis for discrete coefficient modules without requiring algebraic laws
on the scalar action.

## Main results

* `TauCeti.continuousSMul_of_discreteTopology`: scalar actions between discrete spaces are
  continuous.
-/

public section

namespace TauCeti

/-- A scalar action between discrete spaces is jointly continuous, since the product of the
scalar space and the acted-on space is discrete. -/
instance (priority := 100) continuousSMul_of_discreteTopology {R M : Type*} [TopologicalSpace R]
    [TopologicalSpace M] [DiscreteTopology R] [DiscreteTopology M] [SMul R M] :
    ContinuousSMul R M :=
  ⟨continuous_of_discreteTopology⟩

end TauCeti
