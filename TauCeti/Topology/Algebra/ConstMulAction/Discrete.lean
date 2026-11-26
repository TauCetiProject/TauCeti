/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Scalar actions on discrete spaces

Every map out of a discrete space is continuous, so every scalar action on a discrete space has
continuous scalars. This is recorded as an instance, so that constructions asking for
`ContinuousConstSMul R M`, such as the `R`-module structure on the explicit continuous cohomology
groups, apply to discrete modules without further hypotheses.
-/

public section

namespace TauCeti

/-- Each scalar acts continuously on a discrete space. -/
instance (priority := 100) continuousConstSMul_of_discreteTopology {R M : Type*} [SMul R M]
    [TopologicalSpace M] [DiscreteTopology M] : ContinuousConstSMul R M :=
  ⟨fun _ ↦ continuous_of_discreteTopology⟩

end TauCeti
