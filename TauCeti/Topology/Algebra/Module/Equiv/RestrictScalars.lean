/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Restriction of scalars for continuous linear equivalences

Mathlib's `ContinuousLinearEquiv.restrictScalars` restricts scalars for an automorphism.
Here `ContinuousLinearEquiv.restrictScalars'` allows distinct source and target modules,
using `LinearEquiv.restrictScalars` and preserving the original continuous maps.
-/

public section

namespace ContinuousLinearEquiv

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [Module R M] [Module S M] [TopologicalSpace M]
  [AddCommMonoid N] [Module R N] [Module S N] [TopologicalSpace N]
  [LinearMap.CompatibleSMul M N R S]

/-- Restrict scalars in a continuous linear equivalence between possibly distinct modules.
Both caller-provided scalar actions and both underlying continuous maps are preserved. -/
def restrictScalars' (e : M ≃L[S] N) : M ≃L[R] N where
  toLinearEquiv := e.toLinearEquiv.restrictScalars R
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

@[simp]
theorem restrictScalars'_toLinearEquiv (e : M ≃L[S] N) :
    (e.restrictScalars' R).toLinearEquiv = e.toLinearEquiv.restrictScalars R :=
  (rfl)

@[simp]
theorem coe_restrictScalars' (e : M ≃L[S] N) : ⇑(e.restrictScalars' R) = e :=
  (rfl)

@[simp]
theorem coe_restrictScalars'_symm (e : M ≃L[S] N) :
    ⇑(e.restrictScalars' R).symm = e.symm :=
  (rfl)

@[simp]
theorem restrictScalars'_symm [LinearMap.CompatibleSMul N M R S] (e : M ≃L[S] N) :
    (e.restrictScalars' R).symm = e.symm.restrictScalars' R :=
  (rfl)

end ContinuousLinearEquiv
