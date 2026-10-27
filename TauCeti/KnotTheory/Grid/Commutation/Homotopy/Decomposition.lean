/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Basic
public import TauCeti.KnotTheory.Grid.TwoStepDecomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Repartition

/-!
# Composite domains in the grid-commutation homotopy equation

The homotopy equation for a column commutation compares three kinds of two-step domain. On its
left are a commutation hexagon followed by a rectangle and a rectangle followed by a commutation
hexagon. On its right are two commutation pentagons, the second for the reverse commutation. Each
commutation polygon may turn on either side of the replaced grid line.

This file packages those alternatives and rewrites the matrix-coefficient equation as sums over
finite families of composite domains. In this form every summand records the actual polygons it
counts, rather than only their intermediate grid state. This is the input for the geometric
pairing of juxtaposed domains in the proof of commutation invariance.

The two kinds of hexagon and pentagon are represented by sum types. This retains the distinction
between the two turn sides while avoiding four parallel decomposition types. All three composite
domain families specialize the generic two-step decomposition `TauCeti.GridTwoStepDecomposition`,
whose counted finite families have membership characterizations.

## Main results

* `TauCeti.GridDiagram.sum_commutationHexagonCoefficient_mul_unblockedCoefficient` and
  `TauCeti.GridDiagram.sum_unblockedCoefficient_mul_commutationHexagonCoefficient` rewrite the
  two rectangle--hexagon matrix products as composite-domain sums.
* `TauCeti.GridDiagram.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient`
  rewrites the round-trip commutation coefficient as a sum over pairs of pentagons.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff_decompositions`
  states the homotopy equation entirely in terms of the three finite domain families.
* `TauCeti.GridHexagonCompositeDecomposition` combines the two orders of hexagon--rectangle
  composition, with counted family `TauCeti.GridDiagram.hexagonCompositeDecompositions` and
  weight `TauCeti.GridDiagram.hexagonCompositeWeight`.
* `TauCeti.GridDiagram.XSet_inter_coveredSquares_of_mem_commutationHexagons` and
  `TauCeti.GridDiagram.X_cutColumn_mul_commutationHexagonWeight`: the rectangle under a counted
  commutation hexagon carries exactly one `X`-marking, in the column the hexagon cuts away
  (`TauCeti.GridCommutationHexagonBetween.cutColumn`), and its weight exceeds the hexagon weight by
  the variable of that column.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

/-- A commutation hexagon for column `a`, turn row `s` and opposite turn row `s'` is either a
hexagon turning on its terminal side or one turning on its initial side.

The two row parameters play opposite roles in the two cases: the terminal-side hexagon
`GridHexagonBetween a s' s` cuts away the bigon from `s'` up to `s`, while the initial-side hexagon
`GridInitialHexagonBetween a s s'` cuts away the bigon from `s` up to `s'`. -/
abbrev GridCommutationHexagonBetween {n : ℕ} (a s s' : Fin n) (x y : GridState n) :=
  GridHexagonBetween a s' s x y ⊕ GridInitialHexagonBetween a s s' x y

namespace GridCommutationHexagonBetween

variable {n : ℕ} {a s s' : Fin n} {x y : GridState n}

/-- Forget the two turns of a commutation hexagon, retaining its oriented rectangle. -/
def toGridRectangleBetween (P : GridCommutationHexagonBetween a s s' x y) :
    GridRectangleBetween x y :=
  P.elim GridHexagonBetween.toGridRectangleBetween
    GridInitialHexagonBetween.toGridRectangleBetween

/-- The toGridRectangleBetween accessor on a terminal-side hexagon. -/
@[simp]
theorem toGridRectangleBetween_inl (P : GridHexagonBetween a s' s x y) :
    toGridRectangleBetween (Sum.inl P) = P.toGridRectangleBetween := (rfl)

/-- The toGridRectangleBetween accessor on a initial-side hexagon. -/
@[simp]
theorem toGridRectangleBetween_inr (P : GridInitialHexagonBetween a s s' x y) :
    toGridRectangleBetween (Sum.inr P) = P.toGridRectangleBetween := (rfl)

/-- The underlying rectangle determines a commutation hexagon, including its turn side. -/
theorem toGridRectangleBetween_injective :
    Function.Injective (toGridRectangleBetween (a := a) (s := s) (s' := s')
      (x := x) (y := y)) := by
  unfold toGridRectangleBetween
  apply Sum.elim_injective.mpr
  refine ⟨Function.injective_of_subsingleton _, Function.injective_of_subsingleton _, ?_⟩
  intro P Q h
  have hl := congrArg GridRectangleBetween.left h
  exact P.left_ne (hl.trans Q.left_eq)

/-- The marking squares covered by a commutation hexagon of either turn-side kind. -/
noncomputable def coveredSquares (P : GridCommutationHexagonBetween a s s' x y) :
    Finset (Fin n × Fin n) :=
  P.elim GridHexagonBetween.coveredSquares GridInitialHexagonBetween.coveredSquares

/-- The coveredSquares accessor on a terminal-side hexagon. -/
@[simp]
theorem coveredSquares_inl (P : GridHexagonBetween a s' s x y) :
    coveredSquares (Sum.inl P) = P.coveredSquares := (rfl)

/-- The coveredSquares accessor on a initial-side hexagon. -/
@[simp]
theorem coveredSquares_inr (P : GridInitialHexagonBetween a s s' x y) :
    coveredSquares (Sum.inr P) = P.coveredSquares := (rfl)

/-- Transfer a commutation hexagon along an equality of underlying toroidal rectangles,
preserving the turn-side kind. -/
def ofToGridRectangleEq {u v : GridState n} (r : GridRectangleBetween u v)
    (P : GridCommutationHexagonBetween a s s' x y)
    (h : r.toGridRectangle = P.toGridRectangleBetween.toGridRectangle) :
    GridCommutationHexagonBetween a s s' u v :=
  match P with
  | Sum.inl P => Sum.inl (GridHexagonBetween.ofToGridRectangleEq r P h)
  | Sum.inr P => Sum.inr (GridInitialHexagonBetween.ofToGridRectangleEq r P h)

/-- Forgetting a transferred commutation hexagon returns the supplied rectangle. -/
@[simp]
theorem ofToGridRectangleEq_toGridRectangleBetween {u v : GridState n}
    (r : GridRectangleBetween u v) (P : GridCommutationHexagonBetween a s s' x y)
    (h : r.toGridRectangle = P.toGridRectangleBetween.toGridRectangle) :
    (ofToGridRectangleEq r P h).toGridRectangleBetween = r := by
  cases P with
  | inl P => exact GridHexagonBetween.ofToGridRectangleEq_toGridRectangleBetween r P h
  | inr P => exact GridInitialHexagonBetween.ofToGridRectangleEq_toGridRectangleBetween r P h

/-- Transferring a commutation hexagon preserves the marking squares it covers. -/
@[simp]
theorem ofToGridRectangleEq_coveredSquares {u v : GridState n}
    (r : GridRectangleBetween u v) (P : GridCommutationHexagonBetween a s s' x y)
    (h : r.toGridRectangle = P.toGridRectangleBetween.toGridRectangle) :
    (ofToGridRectangleEq r P h).coveredSquares = P.coveredSquares := by
  cases P with
  | inl P =>
    exact GridHexagonBetween.coveredSquares_eq_of_toGridRectangle_eq _ _
      ((congrArg GridRectangleBetween.toGridRectangle
        (GridHexagonBetween.ofToGridRectangleEq_toGridRectangleBetween r P h)).trans h)
  | inr P =>
    exact GridInitialHexagonBetween.coveredSquares_eq_of_toGridRectangle_eq _ _
      ((congrArg GridRectangleBetween.toGridRectangle
        (GridInitialHexagonBetween.ofToGridRectangleEq_toGridRectangleBetween r P h)).trans h)

/-- The column of the underlying rectangle that a commutation hexagon cuts away: column `a` for a
hexagon turning on its terminal side and the column after it for one turning on its initial side.
For a validated column commutation it is the column whose markings lie in the cut-away bigon. -/
def cutColumn (P : GridCommutationHexagonBetween a s s' x y) : Fin n :=
  P.elim (fun _ => a) fun _ => finRotate n a

/-- A hexagon turning on its terminal side cuts away column `a`. -/
@[simp]
theorem cutColumn_inl (P : GridHexagonBetween a s' s x y) :
    cutColumn (Sum.inl P : GridCommutationHexagonBetween a s s' x y) = a := (rfl)

/-- A hexagon turning on its initial side cuts away the column after `a`. -/
@[simp]
theorem cutColumn_inr (P : GridInitialHexagonBetween a s s' x y) :
    cutColumn (Sum.inr P : GridCommutationHexagonBetween a s s' x y) = finRotate n a := (rfl)

/-- A commutation hexagon has the replaced grid line as a side. -/
theorem left_eq_or_right_eq (P : GridCommutationHexagonBetween a s s' x y) :
    P.toGridRectangleBetween.left = finRotate n a ∨
      P.toGridRectangleBetween.right = finRotate n a := by
  cases P with
  | inl P => exact Or.inr P.right_eq
  | inr P => exact Or.inl P.left_eq

/-- Both intersection rows lie among the rows of a commutation hexagon. -/
theorem pair_subset_cIco_bottom_top (P : GridCommutationHexagonBetween a s s' x y) :
    {s, s'} ⊆ Grid.cIco P.toGridRectangleBetween.bottom P.toGridRectangleBetween.top := by
  cases P with
  | inl P =>
    refine Finset.insert_subset ?_ (Finset.singleton_subset_iff.mpr P.lower_mem)
    exact P.insert_cIco_subset_cIco_bottom_top (Finset.mem_insert_self _ _)
  | inr P =>
    refine Finset.insert_subset P.lower_mem (Finset.singleton_subset_iff.mpr ?_)
    exact P.insert_cIco_subset_cIco_bottom_top (Finset.mem_insert_self _ _)

/-- Away from the two columns next to the replaced line, a commutation hexagon covers the squares
of its underlying rectangle. -/
theorem mem_coveredSquares_iff_of_ne (P : GridCommutationHexagonBetween a s s' x y)
    {p : Fin n × Fin n} (ha : p.1 ≠ a) (hb : p.1 ≠ finRotate n a) :
    p ∈ P.coveredSquares ↔ p ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares := by
  cases P with
  | inl P => simp only [coveredSquares_inl, toGridRectangleBetween_inl, P.mem_coveredSquares,
      ne_eq, ha, not_false_eq_true, true_and]
  | inr P => simp only [coveredSquares_inr, toGridRectangleBetween_inr, P.mem_coveredSquares,
      ne_eq, hb, not_false_eq_true, true_and]

/-- A commutation hexagon covers no square of the column before the replaced line. -/
theorem mk_notMem_coveredSquares_left_column (P : GridCommutationHexagonBetween a s s' x y)
    (t : Fin n) : (a, t) ∉ P.coveredSquares := by
  cases P with
  | inl P => simp [P.mem_coveredSquares]
  | inr P =>
    have ha : a ∉ Grid.cIco (finRotate n a) P.right := by simp
    simp only [coveredSquares_inr, P.mem_coveredSquares, GridRectangle.mem_coveredSquares,
      GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, P.left_eq, ha, false_and, and_false,
      not_false_eq_true]

/-- A commutation hexagon covers no square of the column after the replaced line. -/
theorem mk_notMem_coveredSquares_right_column (P : GridCommutationHexagonBetween a s s' x y)
    (t : Fin n) : (finRotate n a, t) ∉ P.coveredSquares := by
  cases P with
  | inl P =>
    simp only [coveredSquares_inl, P.mem_coveredSquares, GridRectangle.mem_coveredSquares,
      GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_right, P.right_eq,
      Grid.right_notMem_cIco, false_and, and_false, not_false_eq_true]
  | inr P => simp [P.mem_coveredSquares]

end GridCommutationHexagonBetween

/-- A commutation pentagon is either a pentagon turning on its terminal side or one turning on its
initial side. -/
abbrev GridCommutationPentagonBetween {n : ℕ} (a s : Fin n) (x y : GridState n) :=
  GridPentagonBetween a s x y ⊕ GridInitialPentagonBetween a s x y

namespace GridCommutationPentagonBetween

variable {n : ℕ} {a s : Fin n} {x y : GridState n}

/-- Forget the turn of a commutation pentagon, retaining its oriented rectangle. -/
def toGridRectangleBetween (P : GridCommutationPentagonBetween a s x y) :
    GridRectangleBetween x y :=
  P.elim GridPentagonBetween.toGridRectangleBetween
    GridInitialPentagonBetween.toGridRectangleBetween

@[simp]
theorem toGridRectangleBetween_inl (P : GridPentagonBetween a s x y) :
    toGridRectangleBetween (Sum.inl P) = P.toGridRectangleBetween := (rfl)

@[simp]
theorem toGridRectangleBetween_inr (P : GridInitialPentagonBetween a s x y) :
    toGridRectangleBetween (Sum.inr P) = P.toGridRectangleBetween := (rfl)

/-- The underlying oriented rectangle determines a commutation pentagon, including its side. -/
theorem toGridRectangleBetween_injective :
    Function.Injective (toGridRectangleBetween (a := a) (s := s) (x := x) (y := y)) := by
  unfold toGridRectangleBetween
  apply Sum.elim_injective.mpr
  refine ⟨Function.injective_of_subsingleton _, Function.injective_of_subsingleton _, ?_⟩
  intro P Q h
  have hl := congrArg GridRectangleBetween.left h
  exact P.left_ne (hl.trans Q.left_eq)

end GridCommutationPentagonBetween

/-- A two-step domain consisting of a commutation hexagon followed by a rectangle. -/
abbrev GridHexagonRectangleDecomposition {n : ℕ} (a s s' : Fin n)
    (x z : GridState n) :=
  GridTwoStepDecomposition (GridCommutationHexagonBetween a s s') GridRectangleBetween x z

namespace GridHexagonRectangleDecomposition

/-- The commutation hexagon in a hexagon--rectangle decomposition. -/
abbrev hexagon {n : ℕ} {a s s' : Fin n} {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a s s' x z) := D.first

/-- The rectangle in a hexagon--rectangle decomposition. -/
abbrev rectangle {n : ℕ} {a s s' : Fin n} {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a s s' x z) := D.second

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Forget the turns of the hexagon in a hexagon--rectangle domain. -/
abbrev toRectangleDecomposition (D : GridHexagonRectangleDecomposition a s s' x z) :
    GridRectangleDecomposition x z :=
  ⟨D.middle, D.first.toGridRectangleBetween, D.second⟩

/-- Forgetting the hexagon turns is injective on two-step domains. -/
theorem toRectangleDecomposition_injective :
    Function.Injective (toRectangleDecomposition (a := a) (s := s) (s' := s')
      (x := x) (z := z)) := by
  rintro ⟨m, P, r⟩ ⟨m', Q, t⟩ h
  have hm : m = m' := congrArg GridTwoStepDecomposition.middle h
  subst m'
  have hp : P.toGridRectangleBetween = Q.toGridRectangleBetween := by injection h
  have hr : r = t := by injection h
  rw [GridCommutationHexagonBetween.toGridRectangleBetween_injective hp, hr]

end GridHexagonRectangleDecomposition

/-- A two-step domain consisting of a rectangle followed by a commutation hexagon. -/
abbrev GridRectangleHexagonDecomposition {n : ℕ} (a s s' : Fin n)
    (x z : GridState n) :=
  GridTwoStepDecomposition GridRectangleBetween (GridCommutationHexagonBetween a s s') x z

namespace GridRectangleHexagonDecomposition

/-- The rectangle in a rectangle--hexagon decomposition. -/
abbrev rectangle {n : ℕ} {a s s' : Fin n} {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a s s' x z) := D.first

/-- The commutation hexagon in a rectangle--hexagon decomposition. -/
abbrev hexagon {n : ℕ} {a s s' : Fin n} {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a s s' x z) := D.second

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Forget the turns of the hexagon in a rectangle--hexagon domain. -/
abbrev toRectangleDecomposition (D : GridRectangleHexagonDecomposition a s s' x z) :
    GridRectangleDecomposition x z :=
  ⟨D.middle, D.first, D.second.toGridRectangleBetween⟩

/-- Forgetting the hexagon turns is injective on two-step domains. -/
theorem toRectangleDecomposition_injective :
    Function.Injective (toRectangleDecomposition (a := a) (s := s) (s' := s')
      (x := x) (z := z)) := by
  rintro ⟨m, r, P⟩ ⟨m', t, Q⟩ h
  have hm : m = m' := congrArg GridTwoStepDecomposition.middle h
  subst m'
  have hr : r = t := by injection h
  have hp : P.toGridRectangleBetween = Q.toGridRectangleBetween := by injection h
  rw [hr, GridCommutationHexagonBetween.toGridRectangleBetween_injective hp]

end GridRectangleHexagonDecomposition

/-- A two-step domain on the left-hand side of the commutation homotopy equation: a commutation
hexagon followed by a rectangle, or a rectangle followed by a commutation hexagon. -/
abbrev GridHexagonCompositeDecomposition {n : ℕ} (a s s' : Fin n) (x z : GridState n) :=
  GridHexagonRectangleDecomposition a s s' x z ⊕ GridRectangleHexagonDecomposition a s s' x z

namespace GridHexagonCompositeDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Forget the turns of the hexagon in a hexagon composite. -/
def toRectangleDecomposition (D : GridHexagonCompositeDecomposition a s s' x z) :
    GridRectangleDecomposition x z :=
  D.elim GridHexagonRectangleDecomposition.toRectangleDecomposition
    GridRectangleHexagonDecomposition.toRectangleDecomposition

/-- The underlying rectangle decomposition of a hexagon followed by a rectangle. -/
@[simp]
theorem toRectangleDecomposition_inl (D : GridHexagonRectangleDecomposition a s s' x z) :
    toRectangleDecomposition (Sum.inl D : GridHexagonCompositeDecomposition a s s' x z) =
      D.toRectangleDecomposition := (rfl)

/-- The underlying rectangle decomposition of a rectangle followed by a hexagon. -/
@[simp]
theorem toRectangleDecomposition_inr (D : GridRectangleHexagonDecomposition a s s' x z) :
    toRectangleDecomposition (Sum.inr D : GridHexagonCompositeDecomposition a s s' x z) =
      D.toRectangleDecomposition := (rfl)

end GridHexagonCompositeDecomposition

/-- A two-step domain consisting of a commutation pentagon followed by a pentagon for the reverse
commutation. -/
abbrev GridPentagonPairDecomposition {n : ℕ} (a s b t : Fin n)
    (x z : GridState n) :=
  GridTwoStepDecomposition (GridCommutationPentagonBetween a s)
    (GridCommutationPentagonBetween b t) x z

namespace GridPentagonPairDecomposition

variable {n : ℕ} {a s b t : Fin n} {x z : GridState n}

/-- Forget both turns in a pair of commutation pentagons. -/
abbrev toRectangleDecomposition (D : GridPentagonPairDecomposition a s b t x z) :
    GridRectangleDecomposition x z :=
  ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩

/-- The underlying rectangle decomposition determines the pentagon pair. -/
theorem toRectangleDecomposition_injective :
    Function.Injective (toRectangleDecomposition (a := a) (s := s) (b := b) (t := t)
      (x := x) (z := z)) := by
  rintro ⟨m, P, Q⟩ ⟨m', P', Q'⟩ h
  have hm : m = m' := congrArg GridTwoStepDecomposition.middle h
  subst m'
  have hp : P.toGridRectangleBetween = P'.toGridRectangleBetween := by injection h
  have hq : Q.toGridRectangleBetween = Q'.toGridRectangleBetween := by injection h
  rw [GridCommutationPentagonBetween.toGridRectangleBetween_injective hp,
    GridCommutationPentagonBetween.toGridRectangleBetween_injective hq]

end GridPentagonPairDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

/-- The counted commutation hexagons of either turn-side kind. -/
noncomputable def commutationHexagons (x y : GridState n) :
    Finset (GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :=
  (G.hexagons C x y).disjSum (G.initialHexagons C x y)

/-- A commutation hexagon is counted exactly when its underlying rectangle is empty and
its marking squares avoid every `X`-marking. -/
@[simp]
theorem mem_commutationHexagons {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    P ∈ G.commutationHexagons C x y ↔
      P.toGridRectangleBetween.IsEmpty ∧ Disjoint P.coveredSquares G.XSet := by
  cases P <;> simp [commutationHexagons,
    GridCommutationHexagonBetween.toGridRectangleBetween,
    GridCommutationHexagonBetween.coveredSquares]

/-- The rectangle under a counted commutation hexagon carries exactly one `X`-marking, that of the
column the hexagon cuts away. -/
theorem XSet_inter_coveredSquares_of_mem_commutationHexagons {x y : GridState n}
    {P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y}
    (hP : P ∈ G.commutationHexagons C x y) :
    G.XSet ∩ P.toGridRectangleBetween.toGridRectangle.coveredSquares =
      {(P.cutColumn, G.X P.cutColumn)} := by
  have hX := ((G.mem_commutationHexagons C P).mp hP).2
  cases P with
  | inl P =>
    rw [GridCommutationHexagonBetween.coveredSquares_inl] at hX
    rw [GridCommutationHexagonBetween.cutColumn_inl,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl]
    exact G.XSet_inter_toGridRectangle_coveredSquares_of_disjoint_hexagon (C := C) hX
  | inr P =>
    rw [GridCommutationHexagonBetween.coveredSquares_inr] at hX
    rw [GridCommutationHexagonBetween.cutColumn_inr,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr]
    exact G.XSet_inter_toGridRectangle_coveredSquares_of_disjoint_initialHexagon (C := C) hX

/-- The rectangle under a commutation hexagon covers the `X`-marking of the column the hexagon cuts
away, whether or not the hexagon is counted. -/
theorem cutColumn_X_mem_toGridRectangle_coveredSquares {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    (P.cutColumn, G.X P.cutColumn) ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares := by
  cases P with
  | inl P => exact G.column_mem_toGridRectangle_coveredSquares P C.X_column_below
  | inr P => exact G.next_mem_toGridRectangle_coveredSquares P C.X_next_above

/-- The counted commutation pentagons of either turn-side kind. -/
noncomputable def commutationPentagons (x y : GridState n) :
    Finset (GridCommutationPentagonBetween C.column C.turnRow x y) :=
  (G.pentagons C x y).disjSum (G.initialPentagons C x y)

/-- A terminal-side commutation pentagon is counted exactly when it is a counted pentagon. -/
@[simp]
theorem inl_mem_commutationPentagons {x y : GridState n}
    (P : GridPentagonBetween C.column C.turnRow x y) :
    Sum.inl P ∈ G.commutationPentagons C x y ↔ P ∈ G.pentagons C x y :=
  Finset.inl_mem_disjSum

/-- An initial-side commutation pentagon is counted exactly when it is a counted initial-side
pentagon. -/
@[simp]
theorem inr_mem_commutationPentagons {x y : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y) :
    Sum.inr P ∈ G.commutationPentagons C x y ↔ P ∈ G.initialPentagons C x y :=
  Finset.inr_mem_disjSum

variable (R : Type*) [CommSemiring R]

/-- The weight of a commutation hexagon of either kind. -/
noncomputable def commutationHexagonWeight {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    MvPolynomial (Fin n) R :=
  P.elim (G.hexagonWeight R) (G.initialHexagonWeight R)

/-- The weight of a terminal-side commutation hexagon. -/
@[simp]
theorem commutationHexagonWeight_inl {x y : GridState n}
    (P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y) :
    G.commutationHexagonWeight C R (Sum.inl P) = G.hexagonWeight R P := (rfl)

/-- The weight of an initial-side commutation hexagon. -/
@[simp]
theorem commutationHexagonWeight_inr {x y : GridState n}
    (P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    G.commutationHexagonWeight C R (Sum.inr P) = G.initialHexagonWeight R P := (rfl)

/-- The weight of a commutation hexagon is the product of the per-square `O`-weights. -/
theorem commutationHexagonWeight_eq_prod_coveredSquares {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    G.commutationHexagonWeight C R P =
      ∏ p ∈ P.coveredSquares, if p ∈ G.OSet then MvPolynomial.X p.1 else 1 := by
  cases P with
  | inl P => exact G.hexagonWeight_eq_prod_coveredSquares R P
  | inr P => exact G.initialHexagonWeight_eq_prod_coveredSquares R P

/-- The weight of a commutation hexagon times the variable of its cut column is the weight of its
underlying rectangle. -/
theorem X_cutColumn_mul_commutationHexagonWeight {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    MvPolynomial.X P.cutColumn * G.commutationHexagonWeight C R P =
      G.OMonomial R P.toGridRectangleBetween.toGridRectangle := by
  cases P with
  | inl P =>
    rw [GridCommutationHexagonBetween.cutColumn_inl, commutationHexagonWeight_inl,
      GridCommutationHexagonBetween.toGridRectangleBetween_inl]
    exact G.X_mul_hexagonWeight R P
  | inr P =>
    rw [GridCommutationHexagonBetween.cutColumn_inr, commutationHexagonWeight_inr,
      GridCommutationHexagonBetween.toGridRectangleBetween_inr]
    exact G.X_mul_initialHexagonWeight R P

/-- The weight of a commutation pentagon of either kind. -/
noncomputable def commutationPentagonWeight {x y : GridState n}
    (P : GridCommutationPentagonBetween C.column C.turnRow x y) :
    MvPolynomial (Fin n) R :=
  P.elim (G.pentagonWeight R C) (G.initialPentagonWeight R C)

/-- The weight of a terminal-side commutation pentagon. -/
@[simp]
theorem commutationPentagonWeight_inl {x y : GridState n}
    (P : GridPentagonBetween C.column C.turnRow x y) :
    G.commutationPentagonWeight C R (Sum.inl P) = G.pentagonWeight R C P := (rfl)

/-- The weight of an initial-side commutation pentagon. -/
@[simp]
theorem commutationPentagonWeight_inr {x y : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y) :
    G.commutationPentagonWeight C R (Sum.inr P) = G.initialPentagonWeight R C P := (rfl)

/-- The hexagon--rectangle decompositions counted in the coefficient of the differential after
the commutation homotopy. -/
noncomputable def hexagonRectangleDecompositions (x z : GridState n) :
    Finset (GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.commutationHexagons C)
    G.unblockedRectangles x z

/-- Membership in the counted hexagon--rectangle family is countedness of both domains. -/
@[simp]
theorem mem_hexagonRectangleDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    D ∈ G.hexagonRectangleDecompositions C x z ↔
      D.hexagon ∈ G.commutationHexagons C x D.middle ∧
        D.rectangle ∈ G.unblockedRectangles D.middle z := by
  classical
  simp [hexagonRectangleDecompositions]

/-- The rectangle--hexagon decompositions counted in the coefficient of the commutation homotopy
after the differential. -/
noncomputable def rectangleHexagonDecompositions (x z : GridState n) :
    Finset (GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :=
  GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles
    (G.commutationHexagons C) x z

/-- Membership in the counted rectangle--hexagon family is countedness of both domains. -/
@[simp]
theorem mem_rectangleHexagonDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    D ∈ G.rectangleHexagonDecompositions C x z ↔
      D.rectangle ∈ G.unblockedRectangles x D.middle ∧
        D.hexagon ∈ G.commutationHexagons C D.middle z := by
  classical
  simp [rectangleHexagonDecompositions]

/-- The pairs of forward and reverse pentagons counted in the round-trip commutation map. -/
noncomputable def pentagonPairDecompositions (x z : GridState n) :
    Finset (GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.commutationPentagons C)
    ((G.swapColumns C.column b).commutationPentagons C.reverse) x z

/-- Membership in the counted pentagon-pair family is countedness of the forward and reverse
pentagons. -/
@[simp]
theorem mem_pentagonPairDecompositions {x z : GridState n}
    (D : GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z) :
    D ∈ G.pentagonPairDecompositions C x z ↔
      D.first ∈ G.commutationPentagons C x D.middle ∧
        D.second ∈ (G.swapColumns C.column b).commutationPentagons C.reverse D.middle z := by
  classical
  simp [pentagonPairDecompositions]

/-- Both underlying rectangles of a counted pentagon pair are empty. -/
theorem isEmpty_of_mem_pentagonPairDecompositions {x z : GridState n}
    {D : GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z} (hD : D ∈ G.pentagonPairDecompositions C x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨hP, hQ⟩ := (G.mem_pentagonPairDecompositions C D).mp hD
  rcases D with ⟨m, P, Q⟩
  cases P <;> cases Q <;>
    simp only [inl_mem_commutationPentagons, inr_mem_commutationPentagons,
      mem_pentagons, mem_initialPentagons] at hP hQ <;>
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using And.intro hP.1 hQ.1

/-- The weight of a counted hexagon followed by a rectangle. -/
noncomputable def hexagonRectangleWeight {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    MvPolynomial (Fin n) R :=
  G.commutationHexagonWeight C R D.hexagon * G.OMonomial R D.rectangle.toGridRectangle

/-- The weight of a hexagon--rectangle decomposition is the product of the two domain weights. -/
theorem hexagonRectangleWeight_def {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    G.hexagonRectangleWeight C R D =
      G.commutationHexagonWeight C R D.hexagon *
        G.OMonomial R D.rectangle.toGridRectangle := (rfl)

/-- The weight of a counted rectangle followed by a hexagon. -/
noncomputable def rectangleHexagonWeight {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    MvPolynomial (Fin n) R :=
  G.OMonomial R D.rectangle.toGridRectangle * G.commutationHexagonWeight C R D.hexagon

/-- The weight of a rectangle--hexagon decomposition is the product of the two domain weights. -/
theorem rectangleHexagonWeight_def {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    G.rectangleHexagonWeight C R D =
      G.OMonomial R D.rectangle.toGridRectangle *
        G.commutationHexagonWeight C R D.hexagon := (rfl)

/-! ### The counted hexagon composites -/

/-- The counted hexagon composites from `x` to `z`: the counted hexagon--rectangle and
rectangle--hexagon decompositions. -/
noncomputable def hexagonCompositeDecompositions (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z) :=
  (G.hexagonRectangleDecompositions C x z).disjSum (G.rectangleHexagonDecompositions C x z)

/-- A hexagon followed by a rectangle is a counted composite exactly when it is counted as a
hexagon--rectangle decomposition. -/
@[simp]
theorem inl_mem_hexagonCompositeDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    Sum.inl D ∈ G.hexagonCompositeDecompositions C x z ↔
      D ∈ G.hexagonRectangleDecompositions C x z :=
  Finset.inl_mem_disjSum

/-- A rectangle followed by a hexagon is a counted composite exactly when it is counted as a
rectangle--hexagon decomposition. -/
@[simp]
theorem inr_mem_hexagonCompositeDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    Sum.inr D ∈ G.hexagonCompositeDecompositions C x z ↔
      D ∈ G.rectangleHexagonDecompositions C x z :=
  Finset.inr_mem_disjSum

/-- The weight of a hexagon composite: that of its hexagon--rectangle or rectangle--hexagon
decomposition. -/
noncomputable def hexagonCompositeWeight {x z : GridState n}
    (D : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    MvPolynomial (Fin n) R :=
  D.elim (G.hexagonRectangleWeight C R) (G.rectangleHexagonWeight C R)

/-- The weight of a hexagon followed by a rectangle. -/
@[simp]
theorem hexagonCompositeWeight_inl {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    G.hexagonCompositeWeight C R (Sum.inl D) = G.hexagonRectangleWeight C R D := (rfl)

/-- The weight of a rectangle followed by a hexagon. -/
@[simp]
theorem hexagonCompositeWeight_inr {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    G.hexagonCompositeWeight C R (Sum.inr D) = G.rectangleHexagonWeight C R D := (rfl)

/-- Both rectangles under a counted composite are empty. -/
theorem isEmpty_of_mem_hexagonCompositeDecompositions {x z : GridState n}
    {D : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z}
    (hD : D ∈ G.hexagonCompositeDecompositions C x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  cases D with
  | inl D =>
    obtain ⟨hP, hr⟩ := (G.mem_hexagonRectangleDecompositions C D).mp
      ((G.inl_mem_hexagonCompositeDecompositions C D).mp hD)
    exact ⟨((G.mem_commutationHexagons C _).mp hP).1, G.isEmpty_of_mem_unblockedRectangles hr⟩
  | inr D =>
    obtain ⟨hr, hP⟩ := (G.mem_rectangleHexagonDecompositions C D).mp
      ((G.inr_mem_hexagonCompositeDecompositions C D).mp hD)
    exact ⟨G.isEmpty_of_mem_unblockedRectangles hr, ((G.mem_commutationHexagons C _).mp hP).1⟩

/-- A counted composite covers exactly one `X`-marking, that of the column its hexagon cuts away,
and its weight times the variable of that column is the product of the weights of its two
underlying rectangles. -/
private theorem exists_X_mul_hexagonCompositeWeight {x z : GridState n}
    {D : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z}
    (hD : D ∈ G.hexagonCompositeDecompositions C x z) :
    ∃ c : Fin n,
      MvPolynomial.X c * G.hexagonCompositeWeight C R D =
          G.OMonomial R D.toRectangleDecomposition.first.toGridRectangle *
            G.OMonomial R D.toRectangleDecomposition.second.toGridRectangle ∧
        G.XSet ∩ (D.toRectangleDecomposition.first.toGridRectangle.coveredSquares ∪
            D.toRectangleDecomposition.second.toGridRectangle.coveredSquares) =
          {(c, G.X c)} := by
  cases D with
  | inl D =>
    obtain ⟨hP, hr⟩ := (G.mem_hexagonRectangleDecompositions C D).mp
      ((G.inl_mem_hexagonCompositeDecompositions C D).mp hD)
    refine ⟨D.hexagon.cutColumn, ?_, ?_⟩
    · rw [hexagonCompositeWeight_inl, hexagonRectangleWeight_def, ← mul_assoc,
        G.X_cutColumn_mul_commutationHexagonWeight C R,
        GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
    · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        Finset.inter_union_distrib_left,
        G.XSet_inter_coveredSquares_of_mem_commutationHexagons C hP,
        Finset.disjoint_iff_inter_eq_empty.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr).symm,
        Finset.union_empty]
  | inr D =>
    obtain ⟨hr, hP⟩ := (G.mem_rectangleHexagonDecompositions C D).mp
      ((G.inr_mem_hexagonCompositeDecompositions C D).mp hD)
    refine ⟨D.hexagon.cutColumn, ?_, ?_⟩
    · rw [hexagonCompositeWeight_inr, rectangleHexagonWeight_def, mul_left_comm,
        G.X_cutColumn_mul_commutationHexagonWeight C R,
        GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
    · rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        Finset.inter_union_distrib_left,
        G.XSet_inter_coveredSquares_of_mem_commutationHexagons C hP,
        Finset.disjoint_iff_inter_eq_empty.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr).symm,
        Finset.empty_union]

/-- Two counted composites whose underlying rectangle decompositions repartition the same squares
have the same weight. -/
theorem hexagonCompositeWeight_eq_of_isRepartition {x z : GridState n}
    {D E : GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z}
    (hD : D ∈ G.hexagonCompositeDecompositions C x z)
    (hE : E ∈ G.hexagonCompositeDecompositions C x z)
    (h : D.toRectangleDecomposition.IsRepartition E.toRectangleDecomposition) :
    G.hexagonCompositeWeight C R D = G.hexagonCompositeWeight C R E := by
  obtain ⟨c, hcw, hcX⟩ := G.exists_X_mul_hexagonCompositeWeight C R hD
  obtain ⟨d, hdw, hdX⟩ := G.exists_X_mul_hexagonCompositeWeight C R hE
  -- Both composites cover the same squares, hence the same single `X`-marking.
  rw [h.coveredSquares_union_eq, hcX, Finset.singleton_inj] at hdX
  rw [← (Prod.mk.inj hdX).1] at hdw
  refine (MvPolynomial.X_mul_cancel_left_iff (i := c)).mp ?_
  rw [hcw, hdw, h.OMonomial_mul_OMonomial G R]

/-- A counted composite is determined by its underlying rectangle decomposition, including the
order of its hexagon and rectangle. -/
theorem injOn_toRectangleDecomposition_hexagonCompositeDecompositions (x z : GridState n) :
    Set.InjOn GridHexagonCompositeDecomposition.toRectangleDecomposition
      (G.hexagonCompositeDecompositions C x z : Set
        (GridHexagonCompositeDecomposition C.column C.turnRow C.oppositeTurnRow x z)) := by
  -- The first rectangle covers an `X`-marking exactly when the hexagon comes first: the rectangle
  -- under the hexagon covers an `X`-marking, while the counted rectangle covers none.
  have key : ∀ D ∈ G.hexagonCompositeDecompositions C x z, D.isLeft ↔
      (G.XSet ∩ D.toRectangleDecomposition.first.toGridRectangle.coveredSquares).Nonempty := by
    rintro (D | D) hD
    · obtain ⟨hP, -⟩ := (G.mem_hexagonRectangleDecompositions C D).mp
        ((G.inl_mem_hexagonCompositeDecompositions C D).mp hD)
      rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        G.XSet_inter_coveredSquares_of_mem_commutationHexagons C hP]
      simp
    · obtain ⟨hr, -⟩ := (G.mem_rectangleHexagonDecompositions C D).mp
        ((G.inr_mem_hexagonCompositeDecompositions C D).mp hD)
      rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        Finset.disjoint_iff_inter_eq_empty.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr).symm]
      simp
  intro D hD E hE h
  rw [Finset.mem_coe] at hD hE
  have hside : D.isLeft ↔ E.isLeft := by rw [key D hD, key E hE, h]
  rcases D with D | D <;> rcases E with E | E <;> simp at hside
  · exact congrArg Sum.inl (GridHexagonRectangleDecomposition.toRectangleDecomposition_injective h)
  · exact congrArg Sum.inr (GridRectangleHexagonDecomposition.toRectangleDecomposition_injective h)

/-- The weight of a forward pentagon followed by a reverse pentagon. The first factor is renamed
because the forward commutation map is semilinear. -/
noncomputable def pentagonPairWeight {x z : GridState n}
    (D : GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z) :
    MvPolynomial (Fin n) R :=
  MvPolynomial.rename (Equiv.swap C.column b) (G.commutationPentagonWeight C R D.first) *
    (G.swapColumns C.column b).commutationPentagonWeight C.reverse R D.second

/-- The weight of a pentagon pair is the product of the renamed forward weight and the reverse
weight. -/
theorem pentagonPairWeight_def {x z : GridState n}
    (D : GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z) :
    G.pentagonPairWeight C R D =
      MvPolynomial.rename (Equiv.swap C.column b) (G.commutationPentagonWeight C R D.first) *
        (G.swapColumns C.column b).commutationPentagonWeight C.reverse R D.second := (rfl)

/-- The sum of the two kinds of hexagon coefficients is the sum of their combined weights. -/
theorem commutationHexagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.commutationHexagonCoefficient R C x y =
      ∑ P ∈ G.commutationHexagons C x y, G.commutationHexagonWeight C R P := by
  rw [G.commutationHexagonCoefficient_def R C, G.hexagonCoefficient_def R C x y,
    G.initialHexagonCoefficient_def R C x y, commutationHexagons, Finset.sum_disjSum]
  simp only [commutationHexagonWeight_inl, commutationHexagonWeight_inr]

/-- The sum of the two kinds of pentagon coefficients is the sum of their combined weights. -/
theorem commutationPentagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.commutationPentagonCoefficient R C x y =
      ∑ P ∈ G.commutationPentagons C x y, G.commutationPentagonWeight C R P := by
  rw [G.commutationPentagonCoefficient_def R C, G.pentagonCoefficient_def R C x y,
    G.initialPentagonCoefficient_def R C x y, commutationPentagons, Finset.sum_disjSum]
  simp only [commutationPentagonWeight_inl, commutationPentagonWeight_inr]

/-- The hexagon--rectangle matrix product is the sum of the weights of the counted composite
domains. -/
theorem sum_commutationHexagonCoefficient_mul_unblockedCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        G.commutationHexagonCoefficient R C x y * G.unblockedCoefficient R y z =
      ∑ D ∈ G.hexagonRectangleDecompositions C x z, G.hexagonRectangleWeight C R D := by
  simp_rw [G.commutationHexagonCoefficient_eq_sum_weight C R,
    G.unblockedCoefficient_def R, Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf
    (G.commutationHexagons C) G.unblockedRectangles
    (fun _ P r => G.commutationHexagonWeight C R P * G.OMonomial R r.toGridRectangle)).symm

/-- The rectangle--hexagon matrix product is the sum of the weights of the counted composite
domains. -/
theorem sum_unblockedCoefficient_mul_commutationHexagonCoefficient (x z : GridState n) :
    ∑ y : GridState n, G.unblockedCoefficient R x y *
        G.commutationHexagonCoefficient R C y z =
      ∑ D ∈ G.rectangleHexagonDecompositions C x z, G.rectangleHexagonWeight C R D := by
  simp_rw [G.unblockedCoefficient_def R, G.commutationHexagonCoefficient_eq_sum_weight C R,
    Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf G.unblockedRectangles
    (G.commutationHexagons C)
    (fun _ r P => G.OMonomial R r.toGridRectangle * G.commutationHexagonWeight C R P)).symm

/-- The forward--reverse pentagon matrix product is the sum of the weights of the counted
pentagon pairs. -/
theorem sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient
    (x z : GridState n) :
    ∑ y : GridState n,
        MvPolynomial.rename (Equiv.swap C.column b)
            (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns C.column b).commutationPentagonCoefficient R C.reverse y z =
      ∑ D ∈ G.pentagonPairDecompositions C x z, G.pentagonPairWeight C R D := by
  simp_rw [G.commutationPentagonCoefficient_eq_sum_weight C R,
    (G.swapColumns C.column b).commutationPentagonCoefficient_eq_sum_weight C.reverse R,
    map_sum, Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf (G.commutationPentagons C)
    ((G.swapColumns C.column b).commutationPentagons C.reverse)
    (fun _ P Q => MvPolynomial.rename (Equiv.swap C.column b)
      (G.commutationPentagonWeight C R P) *
        (G.swapColumns C.column b).commutationPentagonWeight C.reverse R Q)).symm

/-- The commutation homotopy equation holds exactly when the three finite composite-domain sums
satisfy the coefficient identity for every source and target state. -/
theorem unblockedDifferential_commutationHomotopy_add_eq_iff_decompositions :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.commutationHomotopy R C c) +
          G.commutationHomotopy R C (G.unblockedDifferential R c) =
        c + (G.swapColumns C.column b).commutationMap R C.reverse (G.commutationMap R C c)) ↔
      ∀ x z : GridState n,
        (∑ D ∈ G.hexagonRectangleDecompositions C x z, G.hexagonRectangleWeight C R D) +
            ∑ D ∈ G.rectangleHexagonDecompositions C x z,
              G.rectangleHexagonWeight C R D =
          (if x = z then 1 else 0) +
            ∑ D ∈ G.pentagonPairDecompositions C x z, G.pentagonPairWeight C R D := by
  rw [G.unblockedDifferential_commutationHomotopy_add_eq_iff C R]
  simp_rw [Finset.sum_add_distrib,
    G.sum_commutationHexagonCoefficient_mul_unblockedCoefficient C R,
    G.sum_unblockedCoefficient_mul_commutationHexagonCoefficient C R,
    G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient C R]

end GridDiagram

end TauCeti
