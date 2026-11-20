/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Algebra

/-!
# Bounded scalar actions on subsets closed under the action

A bounded scalar action (`IsBoundedSMul`) restricts to a bounded scalar action on any `SetLike`
subobject that contains zero and is closed under the action (`SetLike.instIsBoundedSMul`), because
the subspace distance and the restricted action are the ambient ones.

Since the scalar type is an `outParam` of `SMulMemClass`, this instance only finds the scalars
that the subobject class itself records. For other scalars acting through a scalar tower, derive
the instance with `SMulMemClass.ofIsScalarTower`, as `Submodule.instIsBoundedSMul` does.
-/

public section

/-- A bounded scalar action restricts to a bounded scalar action on any subset that contains zero
and is closed under the action, with the subspace distance. -/
instance SetLike.instIsBoundedSMul {𝕜 M C : Type*} [Zero 𝕜] [PseudoMetricSpace 𝕜] [Zero M]
    [PseudoMetricSpace M] [SMul 𝕜 M] [IsBoundedSMul 𝕜 M] [SetLike C M] [ZeroMemClass C M]
    [SMulMemClass C 𝕜 M] (s : C) : IsBoundedSMul 𝕜 s where
  dist_smul_pair' c x y := dist_smul_pair c (x : M) y
  dist_pair_smul' c₁ c₂ x := dist_pair_smul c₁ c₂ (x : M)
