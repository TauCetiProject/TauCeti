/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic

/-!
# Branch determination for the terminal-side recut

When the rectangle and pentagon share their terminal side, knowing which of the two recut
rectangles inherits the pentagon's terminal side determines the recut branch: the other
rectangle's initial side then lies strictly inside the inheriting rectangle's column interval.
This fixes the column geometry used by the turn-row transports, which must handle the two
cases separately.

## Main results


-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Common setup for the terminal-side branch determination: the pentagon's terminal side
is the common right side of the forgotten rectangle decomposition. -/
private theorem terminal_side_common_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right) :
    D.toRectangleDecomposition.first.right = D.toRectangleDecomposition.second.right ∧
      D.pentagon.right = D.toRectangleDecomposition.first.right := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  refine ⟨hcommon', ?_⟩
  rw [← toRectangleDecomposition_second_right D, ← hcommon']
end TauCeti
