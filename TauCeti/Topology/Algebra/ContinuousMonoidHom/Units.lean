/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid

/-!
# Continuous homomorphisms of unit groups

A continuous monoid homomorphism `f : M →ₜ* N` induces the continuous homomorphism
`Units.map f : Mˣ →ₜ* Nˣ` of unit groups, continuous by Mathlib's `Continuous.units_map`. Mathlib
bundles the induced map only for continuous multiplicative equivalences
(`Units.mapContinuousMulEquiv`).

## Main definitions

* `ContinuousMonoidHom.unitsMap`: the continuous homomorphism of unit groups induced by a
  continuous monoid homomorphism.
-/

public section

namespace ContinuousMonoidHom

variable {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]

/-- The continuous homomorphism `Units.map f : Mˣ →ₜ* Nˣ` of unit groups induced by a continuous
monoid homomorphism `f : M →ₜ* N`. -/
def unitsMap (f : M →ₜ* N) : Mˣ →ₜ* Nˣ :=
  ⟨Units.map (f : M →* N), Continuous.units_map _ (map_continuous f)⟩

@[simp]
theorem coe_unitsMap_apply (f : M →ₜ* N) (u : Mˣ) : (f.unitsMap u : N) = f u :=
  (rfl)

end ContinuousMonoidHom
