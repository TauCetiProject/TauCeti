/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Fibre bundles and trivializations with empty spaces

A map `p : Z → B` whose domain `Z` is empty is globally trivial with any empty model fibre `F`,
with base set the whole of `B`. This handles the degenerate range of bundle projections whose
fibres become empty above a dimension threshold, such as Stiefel bundles of `k`-frames when `k`
exceeds the rank of the vector bundle.

Any fibre family over an empty base space also carries a canonical `FiberBundle` structure with
empty trivialization atlas.

## Main declarations

* `Bundle.Trivialization.ofIsEmpty`: the global trivialization of `p : Z → B` with empty fibre `F`
  when `Z` and `F` are empty.
* `TauCeti.fiberBundleOfIsEmpty`: canonical `FiberBundle` structure over an empty base with empty
  trivialization atlas.
* `TauCeti.trivializationAtlas_fiberBundleOfIsEmpty`: the trivialization atlas of
  `fiberBundleOfIsEmpty` is empty.
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

namespace TauCeti

open Bundle

universe u v w

variable {B : Type u} [TopologicalSpace B] [IsEmpty B] (F : Type v) (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

/-- Any fibre family over an empty base is a `FiberBundle` with empty trivialization atlas. -/
@[instance_reducible] def fiberBundleOfIsEmpty [TopologicalSpace F] : FiberBundle F E where
  trivializationAtlas' := ∅
  trivializationAt' := isEmptyElim
  mem_baseSet_trivializationAt' := isEmptyElim
  trivialization_mem_atlas' := isEmptyElim
  totalSpaceMk_isInducing' := isEmptyElim

/-- The trivialization atlas of `fiberBundleOfIsEmpty` is empty. -/
@[simp] theorem trivializationAtlas_fiberBundleOfIsEmpty [TopologicalSpace F] :
    let _ : FiberBundle F E := fiberBundleOfIsEmpty F E
    trivializationAtlas F E = ∅ := (rfl)

end TauCeti
