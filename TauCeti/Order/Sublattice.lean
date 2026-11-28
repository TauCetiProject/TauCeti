/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.ModularLattice
public import Mathlib.Order.Sublattice

/-!
# Sublattices of a modular lattice

A sublattice of a modular lattice is modular, since its supremum and infimum are those of the
ambient lattice. For instance, the subspaces invariant under an endomorphism
(`Module.End.invtSubmodule`) form a modular lattice.

## Main results

* `Sublattice.instIsModularLatticeCoe`: a sublattice of a modular lattice is modular.
-/

public section

namespace Sublattice

/-- A sublattice of a modular lattice inherits a modular lattice structure. -/
instance instIsModularLatticeCoe {α : Type*} [Lattice α] [IsModularLattice α]
    (L : Sublattice α) : IsModularLattice L :=
  ⟨fun {_} y {_} h ↦ IsModularLattice.sup_inf_le_assoc_of_le (y : α) h⟩

end Sublattice
