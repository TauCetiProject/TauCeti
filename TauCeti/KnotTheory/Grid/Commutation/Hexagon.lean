/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Move
public import TauCeti.KnotTheory.Grid.Unblocked
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Hexagons of a column commutation, and the commutation homotopy

Let `b = finRotate n a` and draw a column commutation of `G` as in `Commutation/Pentagon.lean`:
the vertical grid line `β` with index `b` is replaced by a curve `γ` meeting it in two points. At
the turn point, in square row `t = C.turnRow`, the curve `γ` crosses from the left of `β` to its
right going upwards; at the other point, in square row `t' = C.oppositeTurnRow`, it crosses back.
Going up from `t'` to `t` the curve `γ` runs to the left of `β`, and this bigon contains both
markings of column `a`; going up from `t` to `t'` it runs to the right of `β`, and this bigon
contains both markings of column `b`.

The commutation map `Φ : GC⁻(G) → GC⁻(G')` counts pentagons turning at `t`, and the reverse map
`Ψ : GC⁻(G') → GC⁻(G)` counts pentagons turning at `t'`. The composite `Ψ ∘ Φ` is compared with
the identity by a homotopy `H : GC⁻(G) → GC⁻(G)` counting *hexagons*: embedded disks from a state
`x` of `G` to a state `y` of `G` bounded by arcs of horizontal circles, vertical circles, `β` and
`γ`, with convex corners at the four points of `x` and `y` and at both intersection points of `β`
and `γ`.

Convexity at the two intersection points leaves two kinds of hexagon.

* A hexagon whose terminal side runs up `β` to `t'`, up `γ` to `t` and up `β` again
  (`TauCeti.GridHexagonBetween`). It is the oriented rectangle from `x` to `y` with terminal side
  `b`, with the bigon from `t'` to `t` cut away; its rows must contain both intersection points,
  `t'` below `t`.
* A hexagon whose initial side runs up `β` to `t`, up `γ` to `t'` and up `β` again
  (`TauCeti.GridInitialHexagonBetween`). It is the oriented rectangle from `x` to `y` with initial
  side `b`, with the bigon from `t` to `t'` cut away; its rows must contain `t` below `t'`.

Both shapes are parametrised by the column `a` and the square rows `s`, `s'` of the lower and upper
ends of the bigon that is cut away. The interior lattice points of a hexagon are those of the
rectangle, so emptiness is `GridRectangleBetween.IsEmpty`. The markings a hexagon carries are those
of the rectangle except in the one column of the rectangle next to `β`: a hexagon of the first kind
carries no marking of column `a`, since the bigon it cuts away contains them all, and one of the
second kind carries no marking of column `b`. Its weight is the product of the variables of the
`O`-markings it carries; unlike for pentagons both states lie in `G`, so no renaming of variables
occurs.

Both kinds are needed, just as both kinds of pentagon are. For example, take the `5 × 5` diagram
with `O = (0, 3, 2, 1, 4)` and `X = (3, 0, 4, 2, 1)`, commute columns `2` and `3`, and use turn row
`4` with the other intersection in row `2`. Counting only hexagons of the first kind, the identity
state has diagonal coefficient `1` in `∂⁻ ∘ H + H ∘ ∂⁻ + 1 + Ψ ∘ Φ` over `𝔽₂`; counting both kinds
it vanishes.

`GridDiagram.hexagonMap` and `GridDiagram.initialHexagonMap` count the empty hexagons of the two
kinds carrying no `X`-marking, and `GridDiagram.commutationHomotopy` is their sum, the map `H`
above. That `∂⁻ ∘ H + H ∘ ∂⁻` is the identity plus `Ψ ∘ Φ` is not proved here;
`GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff` writes it as an identity
between matrix coefficients.

## Main definitions

* `TauCeti.GridHexagonBetween`, `TauCeti.GridInitialHexagonBetween`: the combinatorial shapes of
  the two kinds of hexagon.
* `TauCeti.GridHexagonBetween.coveredSquares`, `TauCeti.GridInitialHexagonBetween.coveredSquares`:
  the squares of `G` whose marking lies inside such a hexagon.
* `TauCeti.GridDiagram.hexagons`, `TauCeti.GridDiagram.initialHexagons`: the empty hexagons
  carrying no `X`-marking.
* `TauCeti.GridDiagram.hexagonWeight`, `TauCeti.GridDiagram.hexagonCoefficient` and their initial
  versions: the monomial weights and the matrix coefficients.
* `TauCeti.GridDiagram.hexagonMap`, `TauCeti.GridDiagram.initialHexagonMap`: the maps
  `GC⁻(G) → GC⁻(G)` counting each kind.
* `TauCeti.GridDiagram.commutationHomotopy`: their sum.

## Main results

* `TauCeti.GridHexagonBetween.nonempty_iff`, `TauCeti.GridInitialHexagonBetween.nonempty_iff`: a
  hexagon from `x` to `y` exists exactly when `y` is `x` with column `b` swapped against another
  column and the rows of `x` on the two columns enclose the bigon in the right order;
  `Subsingleton` records that it is then unique.
* `TauCeti.GridDiagram.OColumns_toGridRectangle_eq_insert_of_hexagon` and its initial version:
  the rectangle under a hexagon carries one more `O`-marking, that of the cut-off column.
* `TauCeti.GridDiagram.XSet_inter_toGridRectangle_coveredSquares_of_disjoint_hexagon` and its
  initial version: the rectangle under a hexagon carrying no `X`-marking carries exactly one
  `X`-marking, that of the cut-off column.
* `TauCeti.GridDiagram.commutationHomotopy_apply_apply`: the matrix coefficients of the
  commutation homotopy.

## References

The hexagons are those of the homotopy `H_{βγβ}` of Manolescu--Ozsváth--Szabó--Thurston, *On
combinatorial link Floer homology*, Section 3.1 (arXiv:math/0610559), and of the homotopy of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1. The orientation
convention matches the rectangles of `TauCeti.GridRectangleBetween`: the source state occupies the
lower-left and upper-right corners.
-/

public section

namespace TauCeti

open MvPolynomial

/-- The combinatorial shape of a hexagon whose terminal side turns at both intersection points, for
columns `a` and `finRotate n a`, cutting away the bigon from square row `s` up to square row `s'`,
from a grid state `x` to a grid state `y`.

It is recorded by the oriented rectangle from `x` to `y` with the same corners, whose terminal side
is the grid line `finRotate n a`; the rows that side spans must contain the lower intersection row
`s` and, above it, the upper intersection row `s'`. A hexagon-counting map only uses these shapes
through `GridDiagram.ColumnCommutationData`, which places the column-`a` markings in the bigon. -/
structure GridHexagonBetween {n : ℕ} (a s s' : Fin n) (x y : GridState n)
    extends GridRectangleBetween x y where
  /-- The terminal side lies on the grid line between column `a` and the next column. -/
  right_eq : right = finRotate n a
  /-- The lower intersection point lies on the terminal side. -/
  lower_mem : s ∈ Grid.cIco (x left) (x right)
  /-- The upper intersection point lies on the terminal side, above the lower one. -/
  upper_mem : s' ∈ Grid.cIoo s (x right)

namespace GridHexagonBetween

variable {n : ℕ} {a s s' : Fin n} {x y : GridState n}

/-- The initial side of a hexagon is not the line replaced by `γ`. -/
theorem left_ne (P : GridHexagonBetween a s s' x y) : P.left ≠ finRotate n a :=
  P.right_eq ▸ P.left_ne_right

/-- The rows of the bigon cut away by a hexagon, from its lower intersection row up to and
including its upper one, lie among the rows of the hexagon. -/
theorem insert_cIco_subset_cIco_bottom_top (P : GridHexagonBetween a s s' x y) :
    insert s' (Grid.cIco s s') ⊆ Grid.cIco P.bottom P.top :=
  Grid.insert_cIco_subset_cIco P.lower_mem P.upper_mem

/-- A hexagon is determined by its initial side. -/
theorem left_injective :
    Function.Injective fun P : GridHexagonBetween a s s' x y => P.left := by
  rintro ⟨P, _, _, _⟩ ⟨Q, _, _, _⟩ h
  obtain rfl : P = Q := GridRectangleBetween.left_injective h
  rfl

/-- There is at most one hexagon between two grid states: its initial side is the unique column
other than `finRotate n a` at which the two states differ. -/
instance : Subsingleton (GridHexagonBetween a s s' x y) where
  allEq P Q := left_injective <| by
    by_contra hPQ
    have hQ : y Q.left = x Q.left :=
      P.map_of_ne Q.left (Ne.symm hPQ) (P.right_eq ▸ Q.left_ne)
    have hQ' : y Q.left = x (finRotate n a) := Q.right_eq ▸ Q.map_left
    exact Q.left_ne (x.toPerm.injective (hQ.symm.trans hQ'))

/-- There are finitely many hexagons between two grid states. -/
noncomputable instance : Fintype (GridHexagonBetween a s s' x y) :=
  Fintype.ofInjective _ left_injective

/-- The target of a hexagon is its source with the initial side swapped against the line replaced
by `γ`. -/
theorem target_eq_swapColumns (P : GridHexagonBetween a s s' x y) :
    y = x.swapColumns P.left (finRotate n a) :=
  P.right_eq ▸ P.toGridRectangleBetween.target_eq_swapColumns

/-- The hexagon with initial side `j` from `x` to `x.swapColumns j (finRotate n a)`, when the rows
of `x` on the two sides enclose the bigon from `s` up to `s'`. -/
def ofSwapColumns (x : GridState n) (j : Fin n) (hj : j ≠ finRotate n a)
    (hs : s ∈ Grid.cIco (x j) (x (finRotate n a))) (hs' : s' ∈ Grid.cIoo s (x (finRotate n a))) :
    GridHexagonBetween a s s' x (x.swapColumns j (finRotate n a)) where
  left := j
  right := finRotate n a
  left_ne_right := hj
  map_left := by simp
  map_right := by simp
  map_of_ne c hc hb := by rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hc hb]
  right_eq := rfl
  lower_mem := hs
  upper_mem := hs'

/-- The initial side of the hexagon built from a column swap. -/
@[simp]
theorem ofSwapColumns_left (x : GridState n) (j : Fin n) (hj : j ≠ finRotate n a)
    (hs : s ∈ Grid.cIco (x j) (x (finRotate n a))) (hs' : s' ∈ Grid.cIoo s (x (finRotate n a))) :
    (ofSwapColumns x j hj hs hs').left = j :=
  (rfl)

/-- A hexagon from `x` to `y` exists exactly when `y` is `x` with some column `j` swapped against
the line replaced by `γ`, and the rows of `x` on `j` and on that line enclose the bigon from `s` up
to `s'`. -/
theorem nonempty_iff :
    Nonempty (GridHexagonBetween a s s' x y) ↔
      ∃ j, j ≠ finRotate n a ∧ s ∈ Grid.cIco (x j) (x (finRotate n a)) ∧
        s' ∈ Grid.cIoo s (x (finRotate n a)) ∧ y = x.swapColumns j (finRotate n a) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.left, P.left_ne, P.right_eq ▸ P.lower_mem, P.right_eq ▸ P.upper_mem,
      P.target_eq_swapColumns⟩
  · rintro ⟨j, hj, hs, hs', rfl⟩
    exact ⟨ofSwapColumns x j hj hs hs'⟩

/-- The squares of the original diagram whose marking lies inside a hexagon: the squares of the
underlying rectangle outside column `a`.

The hexagon agrees with the rectangle away from the bigon it cuts away, which lies in column `a`
between the rows `s` and `s'`. When the column-`a` markings lie in that bigon, as
`GridDiagram.ColumnCommutationData` guarantees, the hexagon carries none of them, so only the
marked squares matter and these are the correct squares for them. -/
noncomputable def coveredSquares (P : GridHexagonBetween a s s' x y) : Finset (Fin n × Fin n) :=
  (Grid.cIco P.left (finRotate n a)).erase a ×ˢ Grid.cIco P.bottom P.top

/-- A hexagon covers the squares of its underlying rectangle outside column `a`. -/
theorem mem_coveredSquares (P : GridHexagonBetween a s s' x y) (p : Fin n × Fin n) :
    p ∈ P.coveredSquares ↔ p.1 ≠ a ∧ p ∈ P.toGridRectangle.coveredSquares := by
  simp only [coveredSquares, Finset.mem_product, Finset.mem_erase, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    P.right_eq, and_assoc]

/-- A hexagon carries no `X`-marking exactly when its underlying rectangle carries none outside
column `a`. -/
theorem disjoint_coveredSquares_XSet_iff (P : GridHexagonBetween a s s' x y) (G : GridDiagram n) :
    Disjoint P.coveredSquares G.XSet ↔
      ∀ c, c ≠ a → c ∈ Grid.cIco P.left (finRotate n a) → G.X c ∉ Grid.cIco P.bottom P.top := by
  rw [Finset.disjoint_right]
  constructor
  · intro h c hca hc hX
    refine h ((G.mk_mem_XSet c _).mpr rfl) ?_
    simp only [coveredSquares, Finset.mem_product, Finset.mem_erase]
    exact ⟨⟨hca, hc⟩, hX⟩
  · rintro h p hp hmem
    simp only [coveredSquares, Finset.mem_product, Finset.mem_erase] at hmem
    rw [G.mem_XSet] at hp
    exact h p.1 hmem.1.1 hmem.1.2 (hp ▸ hmem.2)

end GridHexagonBetween

/-- The combinatorial shape of a hexagon whose initial side turns at both intersection points, for
columns `a` and `finRotate n a`, cutting away the bigon from square row `s` up to square row `s'`,
from a grid state `x` to a grid state `y`.

It is recorded by the oriented rectangle from `x` to `y` with the same corners, whose initial side
is the grid line `finRotate n a`; the rows that side spans must contain the lower intersection row
`s` and, above it, the upper intersection row `s'`. A hexagon-counting map only uses these shapes
through `GridDiagram.ColumnCommutationData`, which places the column-`finRotate n a` markings in the
bigon. -/
structure GridInitialHexagonBetween {n : ℕ} (a s s' : Fin n) (x y : GridState n)
    extends GridRectangleBetween x y where
  /-- The initial side lies on the grid line between column `a` and the next column. -/
  left_eq : left = finRotate n a
  /-- The lower intersection point lies on the initial side. -/
  lower_mem : s ∈ Grid.cIco (x left) (x right)
  /-- The upper intersection point lies on the initial side, above the lower one. -/
  upper_mem : s' ∈ Grid.cIoo s (x right)

namespace GridInitialHexagonBetween

variable {n : ℕ} {a s s' : Fin n} {x y : GridState n}

/-- The terminal side of a hexagon turning on its initial side is not the line replaced by `γ`. -/
theorem right_ne (P : GridInitialHexagonBetween a s s' x y) : P.right ≠ finRotate n a :=
  P.left_eq ▸ P.left_ne_right.symm

/-- The rows of the bigon cut away by a hexagon turning on its initial side lie among its rows. -/
theorem insert_cIco_subset_cIco_bottom_top (P : GridInitialHexagonBetween a s s' x y) :
    insert s' (Grid.cIco s s') ⊆ Grid.cIco P.bottom P.top :=
  Grid.insert_cIco_subset_cIco P.lower_mem P.upper_mem

/-- A hexagon turning on its initial side is determined by its underlying rectangle. -/
theorem toGridRectangleBetween_injective :
    Function.Injective (toGridRectangleBetween :
      GridInitialHexagonBetween a s s' x y → GridRectangleBetween x y) := by
  rintro ⟨P, _, _, _⟩ ⟨Q, _, _, _⟩ (rfl : P = Q)
  rfl

/-- There is at most one hexagon turning on its initial side between two grid states: its initial
side is the replaced line, which determines the underlying rectangle. -/
instance : Subsingleton (GridInitialHexagonBetween a s s' x y) where
  allEq P Q := toGridRectangleBetween_injective <|
    GridRectangleBetween.left_injective (P.left_eq.trans Q.left_eq.symm)

/-- There are finitely many hexagons turning on their initial side between two grid states. -/
noncomputable instance : Fintype (GridInitialHexagonBetween a s s' x y) :=
  Fintype.ofInjective _ toGridRectangleBetween_injective

/-- The target of a hexagon turning on its initial side is its source with the line replaced by
`γ` swapped against the terminal side. -/
theorem target_eq_swapColumns (P : GridInitialHexagonBetween a s s' x y) :
    y = x.swapColumns (finRotate n a) P.right :=
  P.left_eq ▸ P.toGridRectangleBetween.target_eq_swapColumns

/-- The hexagon turning on its initial side from `x` to `x.swapColumns (finRotate n a) j`, when the
rows of `x` on the two sides enclose the bigon from `s` up to `s'`. -/
def ofSwapColumns (x : GridState n) (j : Fin n) (hj : j ≠ finRotate n a)
    (hs : s ∈ Grid.cIco (x (finRotate n a)) (x j)) (hs' : s' ∈ Grid.cIoo s (x j)) :
    GridInitialHexagonBetween a s s' x (x.swapColumns (finRotate n a) j) where
  left := finRotate n a
  right := j
  left_ne_right := hj.symm
  map_left := by simp
  map_right := by simp
  map_of_ne c hb hc := by rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hb hc]
  left_eq := rfl
  lower_mem := hs
  upper_mem := hs'

/-- The terminal side of the hexagon built from a column swap. -/
@[simp]
theorem ofSwapColumns_right (x : GridState n) (j : Fin n) (hj : j ≠ finRotate n a)
    (hs : s ∈ Grid.cIco (x (finRotate n a)) (x j)) (hs' : s' ∈ Grid.cIoo s (x j)) :
    (ofSwapColumns x j hj hs hs').right = j :=
  (rfl)

/-- A hexagon turning on its initial side from `x` to `y` exists exactly when `y` is `x` with the
line replaced by `γ` swapped against some other column `j`, and the rows of `x` on that line and on
`j` enclose the bigon from `s` up to `s'`. -/
theorem nonempty_iff :
    Nonempty (GridInitialHexagonBetween a s s' x y) ↔
      ∃ j, j ≠ finRotate n a ∧ s ∈ Grid.cIco (x (finRotate n a)) (x j) ∧
        s' ∈ Grid.cIoo s (x j) ∧ y = x.swapColumns (finRotate n a) j := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.right, P.right_ne, P.left_eq ▸ P.lower_mem, P.upper_mem, P.target_eq_swapColumns⟩
  · rintro ⟨j, hj, hs, hs', rfl⟩
    exact ⟨ofSwapColumns x j hj hs hs'⟩

/-- The squares of the original diagram whose marking lies inside a hexagon turning on its initial
side: the squares of the underlying rectangle outside column `finRotate n a`.

As for `GridHexagonBetween.coveredSquares`, the bigon cut away lies in column `finRotate n a`
between the rows `s` and `s'`, and when the markings of that column lie in it the hexagon carries
none of them. -/
noncomputable def coveredSquares (P : GridInitialHexagonBetween a s s' x y) :
    Finset (Fin n × Fin n) :=
  (Grid.cIco (finRotate n a) P.right).erase (finRotate n a) ×ˢ Grid.cIco P.bottom P.top

/-- A hexagon turning on its initial side covers the squares of its underlying rectangle outside
column `finRotate n a`. -/
theorem mem_coveredSquares (P : GridInitialHexagonBetween a s s' x y) (p : Fin n × Fin n) :
    p ∈ P.coveredSquares ↔ p.1 ≠ finRotate n a ∧ p ∈ P.toGridRectangle.coveredSquares := by
  simp only [coveredSquares, Finset.mem_product, Finset.mem_erase, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    P.left_eq, and_assoc]

/-- A hexagon turning on its initial side carries no `X`-marking exactly when its underlying
rectangle carries none outside column `finRotate n a`. -/
theorem disjoint_coveredSquares_XSet_iff (P : GridInitialHexagonBetween a s s' x y)
    (G : GridDiagram n) :
    Disjoint P.coveredSquares G.XSet ↔
      ∀ c, c ≠ finRotate n a → c ∈ Grid.cIco (finRotate n a) P.right →
        G.X c ∉ Grid.cIco P.bottom P.top := by
  rw [Finset.disjoint_right]
  constructor
  · intro h c hcb hc hX
    refine h ((G.mk_mem_XSet c _).mpr rfl) ?_
    simp only [coveredSquares, Finset.mem_product, Finset.mem_erase]
    exact ⟨⟨hcb, hc⟩, hX⟩
  · rintro h p hp hmem
    simp only [coveredSquares, Finset.mem_product, Finset.mem_erase] at hmem
    rw [G.mem_XSet] at hp
    exact h p.1 hmem.1.1 hmem.1.2 (hp ▸ hmem.2)

end GridInitialHexagonBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### The hexagons counted by the commutation homotopy -/

/-- The hexagons turning on their terminal side from `x` to `y` counted by a validated column
commutation: the empty ones carrying no `X`-marking, cutting away the bigon from the opposite turn
row up to the turn row, which contains the markings of `C.column`. -/
noncomputable def hexagons (C : ColumnCommutationData G) (x y : GridState n) :
    Finset (GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y) := by
  classical
  exact Finset.univ.filter fun P => P.IsEmpty ∧ Disjoint P.coveredSquares G.XSet

/-- Membership in the counted hexagons is emptiness together with `X`-avoidance. -/
@[simp]
theorem mem_hexagons {C : ColumnCommutationData G} {x y : GridState n}
    (P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y) :
    P ∈ G.hexagons C x y ↔ P.IsEmpty ∧ Disjoint P.coveredSquares G.XSet := by
  classical
  simp [hexagons]

/-- The hexagons turning on their initial side from `x` to `y` counted by a validated column
commutation: the empty ones carrying no `X`-marking, cutting away the bigon from the turn row up to
the opposite turn row, which contains the markings of the column after `C.column`. -/
noncomputable def initialHexagons (C : ColumnCommutationData G) (x y : GridState n) :
    Finset (GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) := by
  classical
  exact Finset.univ.filter fun P => P.IsEmpty ∧ Disjoint P.coveredSquares G.XSet

/-- Membership in the counted hexagons turning on their initial side is emptiness together with
`X`-avoidance. -/
@[simp]
theorem mem_initialHexagons {C : ColumnCommutationData G} {x y : GridState n}
    (P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    P ∈ G.initialHexagons C x y ↔ P.IsEmpty ∧ Disjoint P.coveredSquares G.XSet := by
  classical
  simp [initialHexagons]

/-! ### The markings of the cut-off column -/

/-- The rectangle underlying a hexagon of a validated column commutation covers both markings of
`C.column`, since its rows contain the bigon holding them. -/
private theorem column_mem_toGridRectangle_coveredSquares {C : ColumnCommutationData G}
    {x y : GridState n} (P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y)
    {r : Fin n} (hr : r ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow)) :
    (C.column, r) ∈ P.toGridRectangle.coveredSquares := by
  rw [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, P.right_eq]
  exact ⟨Grid.self_mem_cIco_finRotate P.left_ne, P.insert_cIco_subset_cIco_bottom_top hr⟩

/-- The rectangle underlying a hexagon turning on its initial side covers both markings of the
column after `C.column`, since its rows contain the bigon holding them. -/
private theorem next_mem_toGridRectangle_coveredSquares {C : ColumnCommutationData G}
    {x y : GridState n} (P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y)
    {r : Fin n} (hr : r ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow)) :
    (finRotate n C.column, r) ∈ P.toGridRectangle.coveredSquares := by
  rw [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, P.left_eq]
  exact ⟨Grid.left_mem_cIco P.right_ne.symm, P.insert_cIco_subset_cIco_bottom_top hr⟩

/-- The rectangle underlying a hexagon carries the `O`-markings of the hexagon together with the
`O`-marking of `C.column`, which the hexagon cuts away. -/
theorem OColumns_toGridRectangle_eq_insert_of_hexagon {C : ColumnCommutationData G}
    {x y : GridState n} (P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y) :
    G.OColumns P.toGridRectangle = insert C.column (G.OColumnsOfSquares P.coveredSquares) := by
  ext c
  rw [mem_OColumns, Finset.mem_insert, mem_OColumnsOfSquares, P.mem_coveredSquares]
  rcases eq_or_ne c C.column with rfl | hc
  · simpa using column_mem_toGridRectangle_coveredSquares G P C.O_column_below
  · simp only [hc, false_or, ne_eq, not_false_eq_true, true_and]

/-- The rectangle underlying a hexagon turning on its initial side carries the `O`-markings of the
hexagon together with the `O`-marking of the column after `C.column`, which the hexagon cuts
away. -/
theorem OColumns_toGridRectangle_eq_insert_of_initialHexagon {C : ColumnCommutationData G}
    {x y : GridState n} (P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    G.OColumns P.toGridRectangle =
      insert (finRotate n C.column) (G.OColumnsOfSquares P.coveredSquares) := by
  ext c
  rw [mem_OColumns, Finset.mem_insert, mem_OColumnsOfSquares, P.mem_coveredSquares]
  rcases eq_or_ne c (finRotate n C.column) with rfl | hc
  · simpa using next_mem_toGridRectangle_coveredSquares G P C.O_next_above
  · simp only [hc, false_or, ne_eq, not_false_eq_true, true_and]

/-- The rectangle underlying a hexagon carrying no `X`-marking carries exactly one `X`-marking,
that of `C.column`. -/
theorem XSet_inter_toGridRectangle_coveredSquares_of_disjoint_hexagon
    {C : ColumnCommutationData G} {x y : GridState n}
    {P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y}
    (hP : Disjoint P.coveredSquares G.XSet) :
    G.XSet ∩ P.toGridRectangle.coveredSquares = {(C.column, G.X C.column)} := by
  have hX := Finset.disjoint_left.mp hP.symm
  ext p
  rw [Finset.mem_inter, Finset.mem_singleton, G.mem_XSet]
  constructor
  · rintro ⟨hp, hr⟩
    by_contra hne
    have hpa : p.1 ≠ C.column := fun h => hne (Prod.ext h (by rw [← h, hp]))
    exact hX ((G.mem_XSet p).mpr hp) ((P.mem_coveredSquares p).mpr ⟨hpa, hr⟩)
  · rintro rfl
    exact ⟨rfl, column_mem_toGridRectangle_coveredSquares G P C.X_column_below⟩

/-- The rectangle underlying a hexagon turning on its initial side and carrying no `X`-marking
carries exactly one `X`-marking, that of the column after `C.column`. -/
theorem XSet_inter_toGridRectangle_coveredSquares_of_disjoint_initialHexagon
    {C : ColumnCommutationData G} {x y : GridState n}
    {P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y}
    (hP : Disjoint P.coveredSquares G.XSet) :
    G.XSet ∩ P.toGridRectangle.coveredSquares =
      {(finRotate n C.column, G.X (finRotate n C.column))} := by
  have hX := Finset.disjoint_left.mp hP.symm
  ext p
  rw [Finset.mem_inter, Finset.mem_singleton, G.mem_XSet]
  constructor
  · rintro ⟨hp, hr⟩
    by_contra hne
    have hpb : p.1 ≠ finRotate n C.column := fun h => hne (Prod.ext h (by rw [← h, hp]))
    exact hX ((G.mem_XSet p).mpr hp) ((P.mem_coveredSquares p).mpr ⟨hpb, hr⟩)
  · rintro rfl
    exact ⟨rfl, next_mem_toGridRectangle_coveredSquares G P C.X_next_above⟩

/-! ### The hexagon maps -/

variable (R : Type*) [CommSemiring R]

/-- The weight of a hexagon: the product of the variables of the `O`-markings it carries. -/
noncomputable def hexagonWeight {a s s' : Fin n} {x y : GridState n}
    (P : GridHexagonBetween a s s' x y) : MvPolynomial (Fin n) R :=
  ∏ c ∈ G.OColumnsOfSquares P.coveredSquares, MvPolynomial.X c

/-- The weight of a hexagon is the squarefree monomial of the `O`-markings it carries. -/
theorem hexagonWeight_eq_monomial {a s s' : Fin n} {x y : GridState n}
    (P : GridHexagonBetween a s s' x y) :
    G.hexagonWeight R P =
      monomial (∑ c ∈ G.OColumnsOfSquares P.coveredSquares, Finsupp.single c 1) 1 := by
  classical
  rw [hexagonWeight, monomial_sum_one]
  simp only [← X_pow_eq_monomial, pow_one]

/-- The weight of a hexagon is the product, over the squares it covers, of the variable of the
square's column at the `O`-marked squares and of `1` elsewhere. -/
theorem hexagonWeight_eq_prod_coveredSquares {a s s' : Fin n} {x y : GridState n}
    (P : GridHexagonBetween a s s' x y) :
    G.hexagonWeight R P =
      ∏ p ∈ P.coveredSquares, if p ∈ G.OSet then MvPolynomial.X p.1 else 1 :=
  (G.prod_ite_OSet_eq_prod_OColumnsOfSquares MvPolynomial.X _).symm

/-- The weight of a hexagon of a validated column commutation times the variable of `C.column` is
the weight of its underlying rectangle. -/
theorem X_mul_hexagonWeight {C : ColumnCommutationData G} {x y : GridState n}
    (P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y) :
    MvPolynomial.X C.column * G.hexagonWeight R P = G.OMonomial R P.toGridRectangle := by
  rw [hexagonWeight_eq_monomial, OMonomial_eq_monomial,
    G.OColumns_toGridRectangle_eq_insert_of_hexagon P,
    Finset.sum_insert (by simp [P.mem_coveredSquares]), ← pow_one (MvPolynomial.X _),
    X_pow_eq_monomial, monomial_mul_monomial, one_mul]

/-- The weight of a hexagon turning on its initial side: the product of the variables of the
`O`-markings it carries. -/
noncomputable def initialHexagonWeight {a s s' : Fin n} {x y : GridState n}
    (P : GridInitialHexagonBetween a s s' x y) : MvPolynomial (Fin n) R :=
  ∏ c ∈ G.OColumnsOfSquares P.coveredSquares, MvPolynomial.X c

/-- The weight of a hexagon turning on its initial side is the squarefree monomial of the
`O`-markings it carries. -/
theorem initialHexagonWeight_eq_monomial {a s s' : Fin n} {x y : GridState n}
    (P : GridInitialHexagonBetween a s s' x y) :
    G.initialHexagonWeight R P =
      monomial (∑ c ∈ G.OColumnsOfSquares P.coveredSquares, Finsupp.single c 1) 1 := by
  classical
  rw [initialHexagonWeight, monomial_sum_one]
  simp only [← X_pow_eq_monomial, pow_one]

/-- The weight of a hexagon turning on its initial side is the product, over the squares it
covers, of the variable of the square's column at the `O`-marked squares and of `1` elsewhere. -/
theorem initialHexagonWeight_eq_prod_coveredSquares {a s s' : Fin n} {x y : GridState n}
    (P : GridInitialHexagonBetween a s s' x y) :
    G.initialHexagonWeight R P =
      ∏ p ∈ P.coveredSquares, if p ∈ G.OSet then MvPolynomial.X p.1 else 1 :=
  (G.prod_ite_OSet_eq_prod_OColumnsOfSquares MvPolynomial.X _).symm

/-- The weight of a hexagon turning on its initial side times the variable of the column after
`C.column` is the weight of its underlying rectangle. -/
theorem X_mul_initialHexagonWeight {C : ColumnCommutationData G} {x y : GridState n}
    (P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    MvPolynomial.X (finRotate n C.column) * G.initialHexagonWeight R P =
      G.OMonomial R P.toGridRectangle := by
  rw [initialHexagonWeight_eq_monomial, OMonomial_eq_monomial,
    G.OColumns_toGridRectangle_eq_insert_of_initialHexagon P,
    Finset.sum_insert (by simp [P.mem_coveredSquares]), ← pow_one (MvPolynomial.X _),
    X_pow_eq_monomial, monomial_mul_monomial, one_mul]

/-- The matrix coefficient from `x` to `y` of the map counting hexagons turning on their terminal
side: the sum of the weights of the counted ones. -/
noncomputable def hexagonCoefficient (C : ColumnCommutationData G) (x y : GridState n) :
    MvPolynomial (Fin n) R :=
  ∑ P ∈ G.hexagons C x y, G.hexagonWeight R P

/-- The matrix coefficient of the hexagon map is the sum of the weights of its counted
hexagons. -/
theorem hexagonCoefficient_def (C : ColumnCommutationData G) (x y : GridState n) :
    G.hexagonCoefficient R C x y = ∑ P ∈ G.hexagons C x y, G.hexagonWeight R P :=
  (rfl)

/-- The matrix coefficient from `x` to `y` of the map counting hexagons turning on their initial
side: the sum of the weights of the counted ones. -/
noncomputable def initialHexagonCoefficient (C : ColumnCommutationData G) (x y : GridState n) :
    MvPolynomial (Fin n) R :=
  ∑ P ∈ G.initialHexagons C x y, G.initialHexagonWeight R P

/-- The matrix coefficient of the initial-side hexagon map is the sum of the weights of its counted
hexagons. -/
theorem initialHexagonCoefficient_def (C : ColumnCommutationData G) (x y : GridState n) :
    G.initialHexagonCoefficient R C x y =
      ∑ P ∈ G.initialHexagons C x y, G.initialHexagonWeight R P :=
  (rfl)

/-- The map `GC⁻(G) → GC⁻(G)` of the validated column commutation `C` counting the hexagons that
turn on their terminal side, linear over the polynomial ring: a generator `x` goes to the sum over
the counted hexagons from `x` of their weights times their targets. -/
noncomputable def hexagonMap (C : ColumnCommutationData G) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  Finsupp.linearCombination (MvPolynomial (Fin n) R) fun x =>
    Finsupp.equivFunOnFinite.symm fun y => G.hexagonCoefficient R C x y

/-- The matrix coefficients of the hexagon map. -/
theorem hexagonMap_single_apply (C : ColumnCommutationData G) (x y : GridState n) :
    G.hexagonMap R C (Finsupp.single x 1) y = G.hexagonCoefficient R C x y := by
  rw [hexagonMap, Finsupp.linearCombination_single, one_smul,
    Finsupp.equivFunOnFinite_symm_apply_apply]

/-- The coefficient formula for the hexagon map on an arbitrary chain. -/
@[simp]
theorem hexagonMap_apply_apply (C : ColumnCommutationData G) (c : GridChainMinus R n)
    (y : GridState n) :
    G.hexagonMap R C c y = c.sum fun x p => p * G.hexagonCoefficient R C x y := by
  rw [hexagonMap, Finsupp.linearCombination_apply]
  simp [Finsupp.sum_apply]

/-- The map `GC⁻(G) → GC⁻(G)` of the validated column commutation `C` counting the hexagons that
turn on their initial side, linear over the polynomial ring. -/
noncomputable def initialHexagonMap (C : ColumnCommutationData G) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  Finsupp.linearCombination (MvPolynomial (Fin n) R) fun x =>
    Finsupp.equivFunOnFinite.symm fun y => G.initialHexagonCoefficient R C x y

/-- The matrix coefficients of the initial-side hexagon map. -/
theorem initialHexagonMap_single_apply (C : ColumnCommutationData G) (x y : GridState n) :
    G.initialHexagonMap R C (Finsupp.single x 1) y = G.initialHexagonCoefficient R C x y := by
  rw [initialHexagonMap, Finsupp.linearCombination_single, one_smul,
    Finsupp.equivFunOnFinite_symm_apply_apply]

/-- The coefficient formula for the initial-side hexagon map on an arbitrary chain. -/
@[simp]
theorem initialHexagonMap_apply_apply (C : ColumnCommutationData G) (c : GridChainMinus R n)
    (y : GridState n) :
    G.initialHexagonMap R C c y = c.sum fun x p => p * G.initialHexagonCoefficient R C x y := by
  rw [initialHexagonMap, Finsupp.linearCombination_apply]
  simp [Finsupp.sum_apply]

/-- The commutation homotopy `H : GC⁻(G) → GC⁻(G)` of the validated column commutation `C`: it
counts the empty hexagons carrying no `X`-marking with corners at both intersection points, both
those turning on their terminal side (`GridDiagram.hexagonMap`) and those turning on their initial
side (`GridDiagram.initialHexagonMap`). It is the map that compares the composite of the commutation
map with its reverse to the identity. -/
noncomputable def commutationHomotopy (C : ColumnCommutationData G) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  G.hexagonMap R C + G.initialHexagonMap R C

/-- The commutation homotopy is the sum of the two hexagon maps. -/
theorem commutationHomotopy_apply (C : ColumnCommutationData G) (c : GridChainMinus R n) :
    G.commutationHomotopy R C c = G.hexagonMap R C c + G.initialHexagonMap R C c :=
  LinearMap.add_apply _ _ _

/-- The coefficient formula for the commutation homotopy on an arbitrary chain: its matrix
coefficients are the sums of those of the two hexagon maps. -/
@[simp]
theorem commutationHomotopy_apply_apply (C : ColumnCommutationData G) (c : GridChainMinus R n)
    (y : GridState n) :
    G.commutationHomotopy R C c y =
      c.sum fun x p =>
        p * (G.hexagonCoefficient R C x y + G.initialHexagonCoefficient R C x y) := by
  simp only [commutationHomotopy_apply, Finsupp.add_apply, hexagonMap_apply_apply,
    initialHexagonMap_apply_apply, mul_add, Finsupp.sum_add]

end GridDiagram

end TauCeti
