/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Fibre bundles and trivializations in the empty case

Two degenerate empty cases arise for fibre bundles:
* A map `p : Z → B` whose domain `Z` is empty is globally trivial with any empty model fibre `F`,
  with base set the whole of `B` (`Bundle.Trivialization.ofIsEmpty`). This handles bundle
  projections whose fibres become empty above a dimension threshold, such as Stiefel bundles of
  `k`-frames when `k` exceeds the rank of the vector bundle.
* Any family of topological spaces `E : B → Type*` over an empty base `B` (`[IsEmpty B]`) carries a
  canonical vacuous `FiberBundle F E` structure (`FiberBundle.ofIsEmpty`) with empty trivialization
  atlas (`FiberBundle.trivializationAtlas_ofIsEmpty`). This handles empty rank strata when
  assembling bundles across locally constant strata.

## Main declarations

* `Bundle.Trivialization.ofIsEmpty`: the global trivialization of `p : Z → B` with empty fibre `F`
  when `Z` and `F` are empty.
* `FiberBundle.ofIsEmpty`: the vacuous `FiberBundle F E` instance over an empty base `B`.
* `FiberBundle.trivializationAtlas_ofIsEmpty`: the trivialization atlas of `FiberBundle.ofIsEmpty`
  is empty.
-/

public section

open Set

namespace Bundle.Trivialization

variable {B Z : Type*} [TopologicalSpace B] [TopologicalSpace Z] [IsEmpty Z]
  (F : Type*) [TopologicalSpace F] [IsEmpty F] (p : Z → B)

/-- A map out of an empty space is globally trivial with any empty model fibre. -/
def ofIsEmpty : Trivialization F p where
  toFun := isEmptyElim
  invFun q := isEmptyElim q.2
  source := ∅
  target := ∅
  map_source' z := isEmptyElim z
  map_target' q := isEmptyElim q.2
  left_inv' z := isEmptyElim z
  right_inv' q := isEmptyElim q.2
  open_source := isOpen_empty
  open_target := isOpen_empty
  continuousOn_toFun := continuousOn_empty _
  continuousOn_invFun := continuousOn_empty _
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := (eq_empty_of_isEmpty _).symm
  target_eq := (eq_empty_of_isEmpty _).symm
  proj_toFun z := isEmptyElim z

@[simp]
theorem ofIsEmpty_baseSet : (ofIsEmpty F p).baseSet = univ :=
  (rfl)

end Bundle.Trivialization

namespace FiberBundle

open Bundle

/-- Any family of topological spaces over an empty base is vacuously a `FiberBundle`. -/
@[instance_reducible]
def ofIsEmpty {B : Type*} [TopologicalSpace B] [IsEmpty B] (F : Type*)
    [TopologicalSpace F] (E : B → Type*) [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] : FiberBundle F E where
  totalSpaceMk_isInducing' := isEmptyElim
  trivializationAtlas' := ∅
  trivializationAt' := isEmptyElim
  mem_baseSet_trivializationAt' := isEmptyElim
  trivialization_mem_atlas' := isEmptyElim

/-- The trivialization atlas of `FiberBundle.ofIsEmpty` is empty. -/
@[simp] theorem trivializationAtlas_ofIsEmpty {B : Type*} [TopologicalSpace B]
    [IsEmpty B] (F : Type*) [TopologicalSpace F] (E : B → Type*) [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] :
    letI := FiberBundle.ofIsEmpty F E
    trivializationAtlas F E = ∅ := (rfl)

end FiberBundle
