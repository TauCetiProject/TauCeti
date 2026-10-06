/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.ZMod

/-!
# `ZMod n` acts continuously on discrete spaces

`ZMod n` carries the discrete topology, so its scalar action on any discrete space is continuous.
This is the topological hypothesis of a discrete module with `ZMod n` coefficients.

## Main results

* `TauCeti.ZMod.continuousSMul_of_discreteTopology`: `ZMod n` acts continuously on a discrete
  space.
-/

public section

namespace TauCeti.ZMod

/-- `ZMod n` acts continuously on a discrete space, both factors of `ZMod n × M` being
discrete. -/
instance continuousSMul_of_discreteTopology {n : ℕ} {M : Type*} [TopologicalSpace M]
    [DiscreteTopology M] [SMul (ZMod n) M] : ContinuousSMul (ZMod n) M :=
  ⟨continuous_of_discreteTopology⟩

end TauCeti.ZMod
