/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Topology.Defs.Basic

/-!
# Families of two sets

Two sets `U` and `V` give a family `![U, V]` indexed by `Fin 2`, the form in which a cover by two
sets is passed to results about covers indexed by an arbitrary type. Its union is `U ∪ V`
(`TauCeti.iUnion_vecCons`), and it is a family of open sets when `U` and `V` are open
(`TauCeti.isOpen_vecCons`).
-/

public section

namespace TauCeti

variable {X : Type*}

/-- The union of the family `![U, V]` is `U ∪ V`. -/
theorem iUnion_vecCons (U V : Set X) : ⋃ i, ![U, V] i = U ∪ V := by
  ext
  simp [Fin.exists_fin_two]

variable [TopologicalSpace X] {U V : Set X}

/-- Two open sets form a family `![U, V]` of open sets. -/
theorem isOpen_vecCons (hU : IsOpen U) (hV : IsOpen V) : ∀ i, IsOpen (![U, V] i) := by
  simp [Fin.forall_fin_two, hU, hV]

end TauCeti
