/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Recut

/-!
# Recutting mixed-side commutation pentagon pairs

Let `C` be a column commutation and consider a pentagon for `C` followed by a pentagon for the
reverse commutation. When the two pentagons turn on opposite sides of the replaced grid line,
their underlying rectangles automatically share that line: it is terminal for the first and
initial for the second, or initial for the first and terminal for the second. Away from the
diagonal this is their unique common side, so the general empty-rectangle recut applies.

This file packages those two canonical recuts and records their common-side orientations. The
generic recut API then supplies emptiness and involutivity. These are the geometric inputs for
promoting one of the recut rectangles to a commutation hexagon and matching the mixed
pentagon-pair terms in the commutation homotopy equation.

## Main definitions

* `TauCeti.GridDiagram.recutTerminalInitialPentagonPair`: the recut of a terminal-side
  pentagon followed by an initial-side pentagon for the reverse commutation.
* `TauCeti.GridDiagram.recutInitialTerminalPentagonPair`: the recut in the opposite turn-side
  order.

## References

The recuts are the mixed turn-side cases in the hexagon homotopy argument of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Terminal-side followed by initial-side -/

/-- The underlying rectangles of a terminal-side pentagon and a following initial-side pentagon
for the reverse commutation share their intermediate grid line. Away from the diagonal it is
their unique common side. -/
theorem hasOneCommonSide_terminalInitialPentagonPair {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) :
    GridRectangleDecomposition.HasOneCommonSide
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z) := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hb : b ∈ D.commonSideColumns := by
    rw [D.mem_commonSideColumns]
    simp only [GridRectangleBetween.mem_sideColumns, D]
    exact ⟨Or.inr P.right_eq.symm,
      Or.inl ((congrArg (finRotate n) C.reverse_column).symm.trans Q.left_eq.symm)⟩
  exact D.hasOneCommonSide_of_mem_commonSideColumns hb hzx

/-- The common side of a terminal--initial pentagon pair is terminal for the first rectangle and
initial for the second. -/
private theorem terminalInitialPentagonPair_right_eq_left {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z) :
    P.right = Q.left := by
  rw [P.right_eq, Q.left_eq, C.reverse_column]

/-- The canonical empty-rectangle recut of an off-diagonal terminal--initial pentagon pair. -/
noncomputable def recutTerminalInitialPentagonPair {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    GridRectangleDecomposition x z :=
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  D.recut (G.hasOneCommonSide_terminalInitialPentagonPair C P Q hzx) hP hQ

/-- The terminal--initial construction is the canonical recut of the underlying rectangle
decomposition. -/
theorem recutTerminalInitialPentagonPair_def {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    let D : GridRectangleDecomposition x z :=
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
    G.recutTerminalInitialPentagonPair C P Q hzx hP hQ =
      D.recut (G.hasOneCommonSide_terminalInitialPentagonPair C P Q hzx) hP hQ :=
  (rfl)

/-- The terminal--initial recut is a repartition of the pentagon pair's two underlying
rectangles, through a different intermediate state. -/
theorem isRecut_recutTerminalInitialPentagonPair {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    GridRectangleDecomposition.IsRecut
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
      (G.recutTerminalInitialPentagonPair C P Q hzx hP hQ) := by
  rw [G.recutTerminalInitialPentagonPair_def C]
  exact GridRectangleDecomposition.isRecut_recut _
    (G.hasOneCommonSide_terminalInitialPentagonPair C P Q hzx) hP hQ

/-- The terminal--initial recut has the side-data orientation in which the terminal side of the
first pentagon is the initial side of the second. -/
theorem isRecutOfRightEqLeft_recutTerminalInitialPentagonPair {x y z : GridState n}
    (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    GridRectangleDecomposition.IsRecutOfRightEqLeft
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
      (G.recutTerminalInitialPentagonPair C P Q hzx hP hQ) := by
  rw [G.recutTerminalInitialPentagonPair_def C]
  exact GridRectangleDecomposition.isRecutOfRightEqLeft_recut _
    (G.terminalInitialPentagonPair_right_eq_left C P Q)
    (G.hasOneCommonSide_terminalInitialPentagonPair C P Q hzx) hP hQ

/-! ### Initial-side followed by terminal-side -/

/-- The underlying rectangles of an initial-side pentagon and a following terminal-side pentagon
for the reverse commutation share their intermediate grid line. Away from the diagonal it is
their unique common side. -/
theorem hasOneCommonSide_initialTerminalPentagonPair {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) :
    GridRectangleDecomposition.HasOneCommonSide
      (⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z) := by
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  have hb : b ∈ D.commonSideColumns := by
    rw [D.mem_commonSideColumns]
    simp only [GridRectangleBetween.mem_sideColumns, D]
    exact ⟨Or.inl P.left_eq.symm,
      Or.inr ((congrArg (finRotate n) C.reverse_column).symm.trans Q.right_eq.symm)⟩
  exact D.hasOneCommonSide_of_mem_commonSideColumns hb hzx

/-- The common side of an initial--terminal pentagon pair is initial for the first rectangle and
terminal for the second. -/
private theorem initialTerminalPentagonPair_left_eq_right {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z) :
    P.left = Q.right := by
  rw [P.left_eq, Q.right_eq, C.reverse_column]

/-- The canonical empty-rectangle recut of an off-diagonal initial--terminal pentagon pair. -/
noncomputable def recutInitialTerminalPentagonPair {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    GridRectangleDecomposition x z :=
  let D : GridRectangleDecomposition x z :=
    ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
  D.recut (G.hasOneCommonSide_initialTerminalPentagonPair C P Q hzx) hP hQ

/-- The initial--terminal construction is the canonical recut of the underlying rectangle
decomposition. -/
theorem recutInitialTerminalPentagonPair_def {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    let D : GridRectangleDecomposition x z :=
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
    G.recutInitialTerminalPentagonPair C P Q hzx hP hQ =
      D.recut (G.hasOneCommonSide_initialTerminalPentagonPair C P Q hzx) hP hQ :=
  (rfl)

/-- The initial--terminal recut is a repartition of the pentagon pair's two underlying
rectangles, through a different intermediate state. -/
theorem isRecut_recutInitialTerminalPentagonPair {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    GridRectangleDecomposition.IsRecut
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
      (G.recutInitialTerminalPentagonPair C P Q hzx hP hQ) := by
  rw [G.recutInitialTerminalPentagonPair_def C]
  exact GridRectangleDecomposition.isRecut_recut _
    (G.hasOneCommonSide_initialTerminalPentagonPair C P Q hzx) hP hQ

/-- The initial--terminal recut has the side-data orientation in which the initial side of the
first pentagon is the terminal side of the second. -/
theorem isRecutOfLeftEqRight_recutInitialTerminalPentagonPair {x y z : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hzx : z ≠ x) (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    GridRectangleDecomposition.IsRecutOfLeftEqRight
      ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩
      (G.recutInitialTerminalPentagonPair C P Q hzx hP hQ) := by
  rw [G.recutInitialTerminalPentagonPair_def C]
  exact GridRectangleDecomposition.isRecutOfLeftEqRight_recut _
    (G.initialTerminalPentagonPair_left_eq_right C P Q)
    (G.hasOneCommonSide_initialTerminalPentagonPair C P Q hzx) hP hQ

end TauCeti.GridDiagram
