/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# Dimension bounds and finite-dimensionality of CW complexes

A relative or absolute CW complex with no cells in dimensions strictly above `d` is
finite-dimensional (`Topology.RelCWComplex.finiteDimensional_of_isEmpty_cell_gt`,
`Topology.CWComplex.finiteDimensional_of_isEmpty_cell_gt`), regardless of how many cells lie in
dimensions at most `d`.
-/

public section

namespace Topology

/-- A relative CW complex with no cells in dimensions strictly above `d` is finite-dimensional,
regardless of how many cells lie in dimensions at most `d`. -/
@[alias_in CWComplex]
lemma RelCWComplex.finiteDimensional_of_isEmpty_cell_gt {X : Type*} [TopologicalSpace X]
    {D : Set X} (C : Set X) [RelCWComplex C D] {d : ℕ}
    (h : ∀ m, d < m → IsEmpty (RelCWComplex.cell C m)) :
    RelCWComplex.FiniteDimensional C :=
  ⟨Filter.eventually_atTop.2 ⟨d + 1, fun m hm ↦ h m (Nat.lt_of_succ_le hm)⟩⟩

end Topology
