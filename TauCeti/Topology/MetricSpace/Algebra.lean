/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.MetricSpace.Algebra

/-!
# Bounded scalar actions on subsets closed under the action

A bounded scalar action (`IsBoundedSMul`) restricts to a bounded scalar action on any `SetLike`
subobject that contains zero and is closed under the action (`SetLike.instIsBoundedSMul`), because
the subspace distance and the restricted action are the ambient ones.

Since the scalar type is an `outParam` of `SMulMemClass`, this instance only finds the scalars
that the subobject class itself records. For other scalars acting through a scalar tower, derive
the instance with `SMulMemClass.ofIsScalarTower`. This file does so for submodules and closed
submodules of a pseudometric `R`-module `M`: whenever scalars `𝕜` with a pseudometric act
boundedly on `M` (`IsBoundedSMul 𝕜 M`) compatibly with `R` (`IsScalarTower 𝕜 R M`), the restricted
action on any submodule or closed submodule is again bounded (`Submodule.instIsBoundedSMul`,
`ClosedSubmodule.instIsBoundedSMul`). These instances also apply to the restricted seminorm of a
seminormed module (`Submodule.seminormedAddCommGroup`, `ClosedSubmodule.seminormedAddCommGroup`),
whose distance is the restricted distance.
-/

public section

/-- A bounded scalar action restricts to a bounded scalar action on any subset that contains zero
and is closed under the action, with the subspace distance. -/
instance SetLike.instIsBoundedSMul {𝕜 M C : Type*} [Zero 𝕜] [PseudoMetricSpace 𝕜] [Zero M]
    [PseudoMetricSpace M] [SMul 𝕜 M] [IsBoundedSMul 𝕜 M] [SetLike C M] [ZeroMemClass C M]
    [SMulMemClass C 𝕜 M] (s : C) : IsBoundedSMul 𝕜 s where
  dist_smul_pair' c x y := dist_smul_pair c (x : M) y
  dist_pair_smul' c₁ c₂ x := dist_pair_smul c₁ c₂ (x : M)

variable {𝕜 R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [PseudoMetricSpace M]
  [Zero 𝕜] [PseudoMetricSpace 𝕜] [SMul 𝕜 R] [SMul 𝕜 M] [IsScalarTower 𝕜 R M]
  [IsBoundedSMul 𝕜 M]

/-- A bounded scalar action of `𝕜` on an `R`-module, compatible with `R`, restricts to a bounded
scalar action on any submodule under the subspace distance. -/
instance Submodule.instIsBoundedSMul (S : Submodule R M) : IsBoundedSMul 𝕜 S :=
  haveI := SMulMemClass.ofIsScalarTower (Submodule R M) 𝕜 R M
  SetLike.instIsBoundedSMul S

/-- A bounded scalar action of `𝕜` on an `R`-module, compatible with `R`, restricts to a bounded
scalar action on any closed submodule under the subspace distance. -/
instance ClosedSubmodule.instIsBoundedSMul (S : ClosedSubmodule R M) : IsBoundedSMul 𝕜 S :=
  haveI := SMulMemClass.ofIsScalarTower (ClosedSubmodule R M) 𝕜 R M
  SetLike.instIsBoundedSMul S
