/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.FiberBundle.Empty

/-!
# Vector bundles over an empty base

Any `FiberBundle F E` of topological modules over an empty base `B` (`[IsEmpty B]`) is vacuously a
`VectorBundle 𝕜 F E` (`VectorBundle.ofIsEmpty`). Together with `FiberBundle.ofIsEmpty` from
`TauCeti.Topology.FiberBundle.Empty`, this equips empty rank strata of variable-rank vector
bundles with `FiberBundle` and `VectorBundle` instances.
-/

public section

open Bundle

/-- Any `FiberBundle F E` of topological modules over an empty base is vacuously a
`VectorBundle`. -/
theorem VectorBundle.ofIsEmpty {B : Type*} [TopologicalSpace B] [IsEmpty B] (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (E : B → Type*) [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] :
    VectorBundle 𝕜 F E where
  trivialization_linear' _ _ := ⟨isEmptyElim⟩
  continuousOn_coordChange' _ _ _ _ := isEmptyElim
