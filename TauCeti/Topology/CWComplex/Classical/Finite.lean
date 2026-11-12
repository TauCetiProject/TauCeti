/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# Finite CW complexes are compact

A finite relative CW complex `C` over a compact base `D` is compact
(`Topology.RelCWComplex.isCompact_of_finite`): it is the union of `D` and of its finitely many
closed cells, each of which is the image of a closed ball. In particular a finite CW complex is
compact (`Topology.CWComplex.isCompact_of_finite`), and a space carrying a finite CW structure on
`univ` is a compact space, hence normal when it is Hausdorff.
-/

public section

open Set

namespace Topology

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
