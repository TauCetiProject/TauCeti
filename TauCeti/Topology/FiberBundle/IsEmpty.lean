/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Fibre bundles over an empty base

Any fibre family over an empty base space carries a canonical `FiberBundle` structure with empty
trivialization atlas (`TauCeti.fiberBundleOfIsEmpty`, `trivializationAtlas_fiberBundleOfIsEmpty`).
-/

public section
open Bundle
namespace TauCeti
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
