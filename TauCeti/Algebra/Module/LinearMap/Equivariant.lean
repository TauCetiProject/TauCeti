/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Equivariant linear maps

Given semirings `R` and `A`, an `A`-linear map `f : M →ₗ[A] N` is `H`-equivariant for scalar
actions of a type `H` on `M` and `N` when `f (h • m) = h • f m` for all `h : H` and `m : M`.
When `H` acts distributively on `N` and commutes with the `R`-action on `N`, these maps form an
`R`-submodule `TauCeti.equivariantLinearMaps R H A M N` of `M →ₗ[A] N`.

## Main definitions

* `TauCeti.equivariantLinearMaps`: the `R`-submodule of `M →ₗ[A] N` consisting of
  `H`-equivariant `A`-linear maps.

## Main results

* `TauCeti.mem_equivariantLinearMaps`: characterization of membership in
  `TauCeti.equivariantLinearMaps` by `∀ (h : H) (m : M), f (h • m) = h • f m`.
-/

public section

namespace TauCeti

section

variable {R H A M N : Type*}
  [Semiring R] [Semiring A]
  [AddCommMonoid M] [Module A M] [SMul H M]
  [AddCommMonoid N] [Module R N] [Module A N] [SMulCommClass A R N]
  [DistribSMul H N] [SMulCommClass R H N]

variable (R H A M N) in
/-- The `R`-submodule of `M →ₗ[A] N` consisting of `H`-equivariant `A`-linear maps. -/
def equivariantLinearMaps : Submodule R (M →ₗ[A] N) where
  carrier := { f : M →ₗ[A] N | ∀ (h : H) (m : M), f (h • m) = h • f m }
  zero_mem' _ _ := by simp
  add_mem' hf hg h m := by simp [hf h m, hg h m, smul_add]
  smul_mem' r _ hf h m := by simp [hf h m, smul_comm r h]

/-- Membership in `TauCeti.equivariantLinearMaps` is commutation with the `H`-action. -/
@[simp]
theorem mem_equivariantLinearMaps (f : M →ₗ[A] N) :
    f ∈ equivariantLinearMaps R H A M N ↔ ∀ (h : H) (m : M), f (h • m) = h • f m :=
  Iff.rfl

end

end TauCeti
