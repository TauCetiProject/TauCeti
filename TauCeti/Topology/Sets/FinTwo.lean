/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Defs.Basic

/-!
# Families of two sets

Two sets `U` and `V` give a family `![U, V]` indexed by `Fin 2`, the form in which a cover by two
sets is passed to results about covers indexed by an arbitrary type. This file shows that the
family consists of open sets when `U` and `V` are open (`IsOpen.vecCons`).
-/

public section

variable {X : Type*} [TopologicalSpace X] {U V : Set X}

/-- Two open sets form a family `![U, V]` of open sets. -/
theorem IsOpen.vecCons (hU : IsOpen U) (hV : IsOpen V) : ∀ i, IsOpen (![U, V] i) := by
  simp [Fin.forall_fin_two, hU, hV]
