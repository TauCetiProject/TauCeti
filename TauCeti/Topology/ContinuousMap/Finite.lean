/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous maps on a finite space form a finite module

If `Y` is a finite topological space and `M` is a finite module over a Noetherian ring `R`, then
`C(Y, M)` is a finite `R`-module: it embeds linearly into the finite module `Y → M`. In particular,
over a field, `C(Y, M)` is finite-dimensional when `M` is.

## Main statements

* `ContinuousMap.instModuleFiniteOfFinite`: `C(Y, M)` is a finite `R`-module.
-/

public section

namespace ContinuousMap

/-- The continuous maps from a finite space to a finite module over a Noetherian ring form a finite
module. -/
instance instModuleFiniteOfFinite {Y R M : Type*} [TopologicalSpace Y] [Finite Y] [Ring R]
    [IsNoetherianRing R] [TopologicalSpace M] [AddCommGroup M] [ContinuousAdd M]
    [Module R M] [ContinuousConstSMul R M] [Module.Finite R M] : Module.Finite R C(Y, M) :=
  Module.Finite.of_injective (coeFnLinearMap R (α := Y) (M := M)) DFunLike.coe_injective

end ContinuousMap
