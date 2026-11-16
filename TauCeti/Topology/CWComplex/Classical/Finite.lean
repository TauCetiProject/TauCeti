/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# Dimension bounds and compactness of CW complexes

A relative or absolute CW complex with no cells in dimensions strictly above `d` is
finite-dimensional (`Topology.RelCWComplex.finiteDimensional_of_isEmpty_cell_gt`,
`Topology.CWComplex.finiteDimensional_of_isEmpty_cell_gt`), regardless of how many cells lie in
dimensions at most `d`.

A finite relative CW complex `C` over a compact base `D` is compact
(`Topology.RelCWComplex.isCompact_of_finite`): it is the union of `D` and of its finitely many
closed cells, each of which is the image of a closed ball. In particular a finite CW complex is
compact (`Topology.CWComplex.isCompact_of_finite`), and a space carrying a finite CW structure on
`univ` is a compact space, hence normal when it is Hausdorff.
-/

public section

open Set

namespace Topology

/-- A relative CW complex with no cells in dimensions strictly above `d` is finite-dimensional,
regardless of how many cells lie in dimensions at most `d`. -/
@[alias_in CWComplex]
lemma RelCWComplex.finiteDimensional_of_isEmpty_cell_gt {X : Type*} [TopologicalSpace X]
    {D : Set X} (C : Set X) [RelCWComplex C D] {d : ℕ}
    (h : ∀ m, d < m → IsEmpty (RelCWComplex.cell C m)) :
    RelCWComplex.FiniteDimensional C :=
  ⟨Filter.eventually_atTop.2 ⟨d + 1, fun m hm ↦ h m (Nat.lt_of_succ_le hm)⟩⟩

variable {X : Type*} [TopologicalSpace X] {C D : Set X}

/-- **A finite relative CW complex over a compact base is compact.** -/
theorem RelCWComplex.isCompact_of_finite [RelCWComplex C D] [RelCWComplex.Finite C]
    (hD : IsCompact D) : IsCompact C := by
  have := RelCWComplex.finite_cells_of_finite (C := C)
  rw [← RelCWComplex.union (C := C), ← iUnion_sigma (fun p : Σ n, cell C n ↦ closedCell p.1 p.2)]
  exact hD.union (isCompact_iUnion fun _ ↦ isCompact_closedCell)

/-- **A finite CW complex is compact.** -/
theorem CWComplex.isCompact_of_finite [CWComplex C] [RelCWComplex.Finite C] : IsCompact C :=
  RelCWComplex.isCompact_of_finite isCompact_empty

end Topology
