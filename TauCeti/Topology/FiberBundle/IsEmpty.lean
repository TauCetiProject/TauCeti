/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Fibre bundles over an empty base

Any family of topological spaces `E : B → Type*` over an empty base `B` (`[IsEmpty B]`) carries a
canonical vacuous `FiberBundle F E` structure `FiberBundle.ofIsEmpty` with empty trivialization
atlas (`FiberBundle.trivializationAtlas_ofIsEmpty`). This handles empty rank strata when assembling
bundles across locally constant strata.
-/

public section

open Bundle

/-- Any family of topological spaces over an empty base is vacuously a `FiberBundle`. -/
@[instance_reducible]
def FiberBundle.ofIsEmpty {B : Type*} [TopologicalSpace B] [IsEmpty B] (F : Type*)
    [TopologicalSpace F] (E : B → Type*) [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] : FiberBundle F E where
  totalSpaceMk_isInducing' := isEmptyElim
  trivializationAtlas' := ∅
  trivializationAt' := isEmptyElim
  mem_baseSet_trivializationAt' := isEmptyElim
  trivialization_mem_atlas' := isEmptyElim

/-- The trivialization atlas of `FiberBundle.ofIsEmpty` is empty. -/
@[simp] theorem FiberBundle.trivializationAtlas_ofIsEmpty {B : Type*} [TopologicalSpace B]
    [IsEmpty B] (F : Type*) [TopologicalSpace F] (E : B → Type*) [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] :
    letI := FiberBundle.ofIsEmpty F E
    trivializationAtlas F E = ∅ := (rfl)
