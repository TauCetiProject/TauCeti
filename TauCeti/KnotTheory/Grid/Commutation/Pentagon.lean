/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Unblocked
public import TauCeti.KnotTheory.Grid.Commutation.Move
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Pentagons of a column commutation

Let `G` be a grid diagram and let `b = finRotate n a` be the column following column `a`. The
column commutation `G' = G.swapColumns a b` is compared with `G` by drawing both diagrams on one
torus: the vertical grid line `β` between columns `a` and `b` (the line with index `b`) is
replaced by a curve `γ` which meets `β` in two points and bounds with it two thin bigons. The
column-`a` markings of `G` lie in one bigon, on the right of `γ`, and the column-`b` markings in
the other, on the left of `γ`, so that reading the markings off with `γ` in place of `β` gives
`G'`. Every other grid line is shared by the two diagrams, so a grid state of `G'` is again a
permutation of `Fin n` whose value at the line index `b` is its row on `γ`.

A pentagon from a state `x` of `G` to a state `y` of `G'` is an embedded disk bounded by five
arcs: starting at the point of `x` on `β`, it runs left along a horizontal circle to a point of
`y`, down a vertical line to a point of `x`, right along a horizontal circle to the point of `y`
on `γ`, up `γ` to one of the two intersection points of `β` and `γ`, and up `β` back to the start.
All corners are convex, which forces the intersection point to be the one, called the *turn
point*, at which `γ` crosses from the left of `β` to its right going upwards. Just below the turn
point lies the bigon carrying the column-`a` markings, and just above it the bigon carrying the
column-`b` markings.

The combined diagram is recorded by `GridDiagram.ColumnCommutationData`. Besides the adjacent
non-interleaving columns, it records the rows of the two intersections and certifies that the
markings lie in the appropriate two bigons. Every elementary column commutation admits such data
(`GridDiagram.isColumnCommutation_iff_exists_columnCommutationData`), so the map below is
available for each of them. The combinatorics of a pentagon is then recorded
with no curve in sight. Its corners are those of the oriented rectangle from `x` to `y` whose
terminal side is the line `b` (`GridPentagonBetween`, which extends `GridRectangleBetween`); the
turn row must lie in the rows spanned by the terminal side. The lattice points strictly inside
the pentagon are those strictly inside that rectangle,
so emptiness is `GridRectangleBetween.IsEmpty`. The markings it carries differ from those of the
rectangle only in the two columns next to `β` (`GridPentagonBetween.coveredSquares`): a
column-`a` marking is inside exactly when it lies above the turn point, where the terminal side
runs along `β`, and a column-`b` marking exactly when it lies below the turn point, where the
terminal side runs along `γ` to the right of `β`. A column-`a` marking in the row of the turn
point lies below it and a column-`b` marking lies above it, since they lie in the bigons below
and above the turn point respectively.

The pentagon map `GC⁻(G) → GC⁻(G')` (`GridDiagram.pentagonMap`) counts the empty pentagons
carrying no `X`-marking, each weighted by the product of the variables of the `O`-markings it
carries. The variable of an `O`-marking is the one attached to its column in `G'`, so the weight
of a covered column-`c` marking of `G` is `V_{swap a b c}`, and the map is semilinear over the
renaming of the variables by `Equiv.swap a b`. The reverse comparison `GC⁻(G') → GC⁻(G)` counts
pentagons turning at the other intersection point; seen from `G'`, where `γ` is the grid line and
`β` the replacement curve, that is the same construction for `G'` with the square row of the
other intersection point as its turn row.

The pentagons here lie to the left of `β ∪ γ`. The commutation map `Φ` also counts the pentagons
lying to its right, whose initial side turns at the same point; those, and `Φ` itself
(`GridDiagram.commutationMap`), are in `Commutation/InitialPentagon/Basic.lean`. The map defined
here is only one part of `Φ` and is not a chain map on its own.

This file sets up the pentagons and the map. That `Φ` is a chain map, and that together with the
reverse map it is a chain homotopy equivalence via the hexagon-counting homotopies, is not proved
here.

## Main definitions

* `TauCeti.GridPentagonBetween`: the combinatorial shape of a pentagon, recorded by its corners
  and its turn row.
* `TauCeti.GridPentagonBetween.coveredSquares`: the squares of `G` whose marking lies inside the
  pentagon.
* `TauCeti.GridDiagram.pentagons`: the empty pentagons carrying no `X`-marking.
* `TauCeti.GridDiagram.pentagonWeight`: the monomial weighting a pentagon.
* `TauCeti.GridDiagram.pentagonCoefficient`: the matrix coefficients of the pentagon map.
* `TauCeti.GridDiagram.pentagonMap`: the map `GC⁻(G) → GC⁻(G.swapColumns a b)` counting these
  pentagons, the terminal-side part of the commutation map `Φ`.

## Main results

* `TauCeti.GridPentagonBetween.nonempty_iff`: a pentagon from `x` to `y` exists exactly when `y`
  is `x` with column `b` swapped against another column `j` and the turn row lies between the
  rows of `x` on `j` and on `b`; `Subsingleton` records that it is then unique.
* `TauCeti.GridPentagonBetween.mem_coveredSquares`,
  `TauCeti.GridPentagonBetween.mem_coveredSquares_iff_of_ne`: the covered squares, which agree
  with those of the underlying rectangle away from columns `a` and `b`.
* `TauCeti.GridPentagonBetween.coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom`:
  a pentagon spanning one row covers that row away from the first commuted column.
* `TauCeti.GridPentagonBetween.disjoint_coveredSquares_XSet_iff`: the `X`-avoidance condition
  column by column.
* `TauCeti.GridPentagonBetween.coveredSquares_subset_union_of_stacked`: a pentagon spanning a
  pentagon with a rectangle stacked on it covers only squares one of those two covers.
* `TauCeti.GridDiagram.pentagonWeight_eq_prod_coveredSquares`,
  `TauCeti.GridDiagram.pentagonWeight_eq_prod_swapColumns`: the weight as a product over the
  covered squares, and as the product of the variables of the covered `O`-markings of the
  commuted diagram.
* `TauCeti.GridDiagram.pentagonMap_single`, `TauCeti.GridDiagram.pentagonMap_apply_apply`: the
  action of the pentagon map on generators and its matrix coefficients.
* `TauCeti.GridDiagram.pentagonMapOnGenerator_support_subset`: the pentagon map moves a
  generator only by swapping its point on `β` against one other point.

## References

The pentagons are those of the chain map `Φ_{βγ}` of Manolescu--Ozsváth--Szabó--Thurston, *On
combinatorial link Floer homology*, Section 3.1 (arXiv:math/0610559), and of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, that lie to the left
of `β ∪ γ`. The orientation convention matches the rectangles of
`TauCeti.GridRectangleBetween`: the source state occupies the lower-left and upper-right
corners.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

end GridDiagram

/-- The combinatorial shape of a pentagon for columns `a` and `finRotate n a`, with turn point in
square row `s`, from a grid state `x` to a grid state `y`.

It is recorded by the oriented rectangle from `x` to `y` with the same corners, whose terminal
side is the grid line `finRotate n a` replaced by the curve `γ`; the rows that side spans must
contain the turn row. The points of `x` sit at the lower-left and upper-right corners and those of
`y` at the upper-left and lower-right corners, the latter on `γ`. A pentagon-counting map only
uses these shapes through `GridDiagram.ColumnCommutationData`, which validates the commutation and
the placement of the markings relative to the turn. -/
structure GridPentagonBetween {n : ℕ} (a s : Fin n) (x y : GridState n)
    extends GridRectangleBetween x y where
  /-- The terminal side lies on the grid line between column `a` and the next column. -/
  right_eq : right = finRotate n a
  /-- The turn point lies on the terminal side: its row is among the rows that side spans. -/
  turn_mem : s ∈ Grid.cIco (x left) (x right)

namespace GridPentagonBetween

variable {n : ℕ} {a s : Fin n} {x y : GridState n}

/-- The initial side of a pentagon is not the line replaced by `γ`. -/
theorem left_ne (P : GridPentagonBetween a s x y) : P.left ≠ finRotate n a :=
  P.right_eq ▸ P.left_ne_right

/-- The turn row lies in the rows spanned by the terminal side, from the row of `x` on the
initial side to its row on the terminal side. -/
theorem turn_mem_cIco (P : GridPentagonBetween a s x y) :
    s ∈ Grid.cIco (x P.left) (x (finRotate n a)) :=
  P.right_eq ▸ P.turn_mem

/-- The two columns next to the replaced grid line of a pentagon are distinct. -/
theorem ne_finRotate (P : GridPentagonBetween a s x y) : a ≠ finRotate n a := fun h =>
  Grid.right_notMem_cIco P.left (finRotate n a) (h ▸ Grid.self_mem_cIco_finRotate P.left_ne)

/-- The turn row of a pentagon lies among its rows. -/
theorem turn_mem_cIco_bottom_top (P : GridPentagonBetween a s x y) :
    s ∈ Grid.cIco P.bottom P.top := by
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def]
  exact P.turn_mem

/-- A pentagon spanning one cyclic row turns at its bottom row. -/
theorem turn_eq_bottom_of_top_eq_finRotate_bottom (P : GridPentagonBetween a s x y)
    (hthin : P.top = finRotate n P.bottom) : s = P.bottom := by
  have hrows := Grid.cIco_eq_singleton_iff.2 ⟨rfl, hthin, P.bottom_ne_top⟩
  have ht := P.turn_mem_cIco_bottom_top
  rw [hrows] at ht
  exact Finset.mem_singleton.mp ht

/-- The row interval of a thin pentagon consists exactly of its turn row. -/
theorem cIco_bottom_top_eq_singleton_of_top_eq_finRotate_bottom
    (P : GridPentagonBetween a s x y) (hthin : P.top = finRotate n P.bottom) :
    Grid.cIco P.bottom P.top = {s} := by
  simpa only [P.turn_eq_bottom_of_top_eq_finRotate_bottom hthin] using
    Grid.cIco_eq_singleton_iff.2 ⟨rfl, hthin, P.bottom_ne_top⟩

/-- A pentagon is determined by its initial side. -/
theorem left_injective :
    Function.Injective fun P : GridPentagonBetween a s x y => P.left := by
  intro P Q h
  obtain ⟨P, _, _⟩ := P
  obtain ⟨Q, _, _⟩ := Q
  obtain rfl : P = Q := GridRectangleBetween.left_injective h
  rfl

/-- There is at most one pentagon between two grid states: its initial side is the unique column
other than `finRotate n a` at which the two states differ. -/
instance : Subsingleton (GridPentagonBetween a s x y) where
  allEq P Q := left_injective <| by
    by_contra hPQ
    have hQ : y Q.left = x Q.left :=
      P.map_of_ne Q.left (Ne.symm hPQ) (P.right_eq ▸ Q.left_ne)
    have hQ' : y Q.left = x (finRotate n a) := Q.right_eq ▸ Q.map_left
    exact Q.left_ne (x.toPerm.injective (hQ.symm.trans hQ'))

/-- There are finitely many pentagons between two grid states. -/
noncomputable instance : Fintype (GridPentagonBetween a s x y) :=
  Fintype.ofInjective _ left_injective

/-- The target of a pentagon is its source with the initial side swapped against the line
replaced by `γ`. -/
theorem target_eq_swapColumns (P : GridPentagonBetween a s x y) :
    y = x.swapColumns P.left (finRotate n a) :=
  P.right_eq ▸ P.toGridRectangleBetween.target_eq_swapColumns

/-- The pentagon with initial side `j` from `x` to `x.swapColumns j (finRotate n a)`, when the
turn row lies between the rows of `x` on the two sides. -/
def ofSwapColumns (x : GridState n) (j : Fin n) (hj : j ≠ finRotate n a)
    (hs : s ∈ Grid.cIco (x j) (x (finRotate n a))) :
    GridPentagonBetween a s x (x.swapColumns j (finRotate n a)) where
  left := j
  right := finRotate n a
  left_ne_right := hj
  map_left := by simp
  map_right := by simp
  map_of_ne c hc hb := by rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hc hb]
  right_eq := rfl
  turn_mem := hs

/-- Regard an oriented rectangle as a pentagon: its terminal side must be the grid line replaced
by `γ`, and the turn row must lie among the rows that side spans. -/
def ofRightEq {u v : GridState n} (r : GridRectangleBetween u v)
    (hright : r.right = finRotate n a) (hs : s ∈ Grid.cIco r.bottom r.top) :
    GridPentagonBetween a s u v where
  toGridRectangleBetween := r
  right_eq := hright
  turn_mem := hs

/-- The rectangle underlying `ofRightEq` is the supplied rectangle. -/
@[simp]
theorem ofRightEq_toGridRectangleBetween {u v : GridState n} (r : GridRectangleBetween u v)
    (hright : r.right = finRotate n a) (hs : s ∈ Grid.cIco r.bottom r.top) :
    (ofRightEq r hright hs : GridPentagonBetween a s u v).toGridRectangleBetween = r := by
  unfold ofRightEq
  rfl

/-- The terminal side of `ofRightEq` is the grid line replaced by `γ`. -/
theorem ofRightEq_right {u v : GridState n} (r : GridRectangleBetween u v)
    (hright : r.right = finRotate n a) (hs : s ∈ Grid.cIco r.bottom r.top) :
    (ofRightEq r hright hs : GridPentagonBetween a s u v).right = finRotate n a := by
  unfold ofRightEq
  exact hright

/-- The initial side of `ofRightEq` is the rectangle's. -/
theorem ofRightEq_left {u v : GridState n} (r : GridRectangleBetween u v)
    (hright : r.right = finRotate n a) (hs : s ∈ Grid.cIco r.bottom r.top) :
    (ofRightEq r hright hs : GridPentagonBetween a s u v).left = r.left := by
  unfold ofRightEq
  rfl

/-- The bottom row of `ofRightEq` is the rectangle's. -/
theorem ofRightEq_bottom {u v : GridState n} (r : GridRectangleBetween u v)
    (hright : r.right = finRotate n a) (hs : s ∈ Grid.cIco r.bottom r.top) :
    (ofRightEq r hright hs : GridPentagonBetween a s u v).bottom = r.bottom := by
  unfold ofRightEq
  rfl

/-- The top row of `ofRightEq` is the rectangle's. -/
theorem ofRightEq_top {u v : GridState n} (r : GridRectangleBetween u v)
    (hright : r.right = finRotate n a) (hs : s ∈ Grid.cIco r.bottom r.top) :
    (ofRightEq r hright hs : GridPentagonBetween a s u v).top = r.top := by
  unfold ofRightEq
  rfl

/-- Regard a rectangle between possibly different endpoint states as a pentagon when its
underlying toroidal rectangle agrees with that of an existing pentagon. -/
def ofToGridRectangleEq {u v : GridState n} (r : GridRectangleBetween u v)
    (P : GridPentagonBetween a s x y) (h : r.toGridRectangle = P.toGridRectangle) :
    GridPentagonBetween a s u v :=
  ofRightEq r
    (by
      obtain ⟨-, hright, -, -⟩ := GridRectangle.ext_iff.mp h
      simpa only [GridRectangleBetween.toGridRectangle_right] using hright.trans P.right_eq)
    (by
      obtain ⟨-, -, hbottom, htop⟩ := GridRectangle.ext_iff.mp h
      simp only [GridRectangleBetween.toGridRectangle_bottom,
        GridRectangleBetween.toGridRectangle_top] at hbottom htop
      rw [hbottom, htop]
      exact P.turn_mem)

/-- The rectangle underlying `ofToGridRectangleEq` is the supplied rectangle. -/
@[simp]
theorem ofToGridRectangleEq_toGridRectangleBetween {u v : GridState n}
    (r : GridRectangleBetween u v) (P : GridPentagonBetween a s x y)
    (h : r.toGridRectangle = P.toGridRectangle) :
    (ofToGridRectangleEq r P h).toGridRectangleBetween = r := by
  unfold ofToGridRectangleEq
  exact ofRightEq_toGridRectangleBetween r _ _

/-- The initial side of the pentagon built from a column swap. -/
@[simp]
theorem ofSwapColumns_left (x : GridState n) (j : Fin n) (hj : j ≠ finRotate n a)
    (hs : s ∈ Grid.cIco (x j) (x (finRotate n a))) :
    (ofSwapColumns x j hj hs).left = j :=
  (rfl)

/-- A pentagon from `x` to `y` exists exactly when `y` is `x` with some column `j` swapped against
the line replaced by `γ`, and the turn row lies between the rows of `x` on `j` and on that
line. -/
theorem nonempty_iff :
    Nonempty (GridPentagonBetween a s x y) ↔
      ∃ j, j ≠ finRotate n a ∧ s ∈ Grid.cIco (x j) (x (finRotate n a)) ∧
        y = x.swapColumns j (finRotate n a) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.left, P.left_ne, P.turn_mem_cIco, P.target_eq_swapColumns⟩
  · rintro ⟨j, hj, hs, rfl⟩
    exact ⟨ofSwapColumns x j hj hs⟩

/-- The squares of the original diagram whose marking lies inside the pentagon.

Away from the two columns next to the replaced line these are the squares covered by the
underlying rectangle. In column `a` they are the rows strictly above the turn row, up to the top
side, where the terminal side runs along `β`; in column `finRotate n a` they are the rows from
the bottom side up to and excluding the turn row, where the terminal side runs along `γ` to the
right of `β`. The markings of these two columns in the turn row lie below and above the turn
point respectively, and neither is inside the pentagon.

These are the correct squares for the markings of columns `a` and `finRotate n a` when the
turn point is placed as in the combined diagram of the commutation: the column-`a` markings in the
bigon below it and the column-`finRotate n a` markings in the bigon above it. Only marked squares
of those two columns matter for the weights and the `X`-avoidance condition. -/
noncomputable def coveredSquares (P : GridPentagonBetween a s x y) : Finset (Fin n × Fin n) :=
  ((Grid.cIco P.left (finRotate n a)).erase a ×ˢ Grid.cIco P.bottom P.top) ∪
    (({a} ×ˢ Grid.cIoo s P.top) ∪ ({finRotate n a} ×ˢ Grid.cIco P.bottom s))

/-- Membership in the covered squares of a pentagon, column by column. -/
theorem mem_coveredSquares (P : GridPentagonBetween a s x y) (p : Fin n × Fin n) :
    p ∈ P.coveredSquares ↔
      (p.1 ≠ a ∧ p.1 ∈ Grid.cIco P.left (finRotate n a) ∧ p.2 ∈ Grid.cIco P.bottom P.top) ∨
        (p.1 = a ∧ p.2 ∈ Grid.cIoo s P.top) ∨
          (p.1 = finRotate n a ∧ p.2 ∈ Grid.cIco P.bottom s) := by
  simp only [coveredSquares, Finset.mem_union, Finset.mem_product, Finset.mem_erase,
    Finset.mem_singleton, and_assoc]

/-- Every square covered by a pentagon lies in the row arc of its underlying rectangle. -/
theorem mem_cIco_of_mem_coveredSquares (P : GridPentagonBetween a s x y)
    {p : Fin n × Fin n} (hp : p ∈ P.coveredSquares) :
    p.2 ∈ Grid.cIco P.bottom P.top := by
  have hsplit := Grid.ite_mem_cIco_eq_add_add P.turn_mem_cIco_bottom_top p.2
  rcases (P.mem_coveredSquares p).1 hp with h | h | h
  · exact h.2.2
  · split_ifs at hsplit <;> grind
  · split_ifs at hsplit <;> grind

/-- A pentagon covers no square in a set supported on the complementary row arc. -/
theorem disjoint_coveredSquares_of_forall_mem_cIco (P : GridPentagonBetween a s x y)
    {S : Finset (Fin n × Fin n)}
    (hS : ∀ p ∈ S, p.2 ∈ Grid.cIco P.top P.bottom) :
    Disjoint P.coveredSquares S := by
  refine Finset.disjoint_left.2 fun p hp h => ?_
  exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap P.bottom P.top)
    (P.mem_cIco_of_mem_coveredSquares hp) (hS p h)

/-- A pentagon spanning one cyclic row has its turn in that row and covers only the
columns of its underlying rectangle other than the first commuted column. -/
theorem coveredSquares_eq_product_singleton_of_top_eq_finRotate_bottom
    (P : GridPentagonBetween a s x y) (hthin : P.top = finRotate n P.bottom) :
    P.coveredSquares = (Grid.cIco P.left (finRotate n a)).erase a ×ˢ {s} := by
  have hs := P.turn_eq_bottom_of_top_eq_finRotate_bottom hthin
  ext p
  simp only [mem_coveredSquares, Finset.mem_product, Finset.mem_erase,
    hs, Grid.cIco_eq_singleton_iff.2 ⟨rfl, hthin, P.bottom_ne_top⟩, Finset.mem_singleton]
  simp only [hthin, Grid.cIoo_finRotate_eq_empty, Grid.cIco_self,
    Finset.notMem_empty, and_false, or_false, and_assoc]

/-- Pentagons with the same underlying toroidal rectangle cover the same squares. -/
theorem coveredSquares_eq_of_toGridRectangle_eq {u v : GridState n}
    (P : GridPentagonBetween a s x y) (Q : GridPentagonBetween a s u v)
    (h : P.toGridRectangle = Q.toGridRectangle) : P.coveredSquares = Q.coveredSquares := by
  obtain ⟨hleft, -, hbottom, htop⟩ := GridRectangle.ext_iff.mp h
  simp only [GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top] at hleft hbottom htop
  ext p
  rw [P.mem_coveredSquares, Q.mem_coveredSquares]
  simp only [hleft, hbottom, htop]

/-- Away from the two columns next to the replaced line, a pentagon covers the squares of its
underlying rectangle. -/
theorem mem_coveredSquares_iff_of_ne (P : GridPentagonBetween a s x y) {p : Fin n × Fin n}
    (ha : p.1 ≠ a) (hb : p.1 ≠ finRotate n a) :
    p ∈ P.coveredSquares ↔ p ∈ P.toGridRectangle.coveredSquares := by
  simpa only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, P.right_eq, ha, hb, ne_eq, not_false_eq_true,
    true_and, false_and, or_false] using P.mem_coveredSquares p

/-- A pentagon spanning a pentagon with a toroidal rectangle stacked on it covers only squares
one of those two covers.

The hypotheses place `P` directly below `r`, the top row of `P` being the bottom row of `r`, and
make `Q` span the two of them: the rows of `Q` run from the bottom row of `P` to the top row of
`r`, and its column arc lies inside both of theirs. The two columns next to the replaced grid
line are what makes this more than the corresponding statement about the underlying rectangles:
in column `a` the arc of `Q` above the turn row is cut into the arc of `P` above the turn row and
a band of rows of `r`, and in column `finRotate n a` the arc of `Q` below the turn row is the one
`P` covers, because the two pentagons share a bottom row. -/
theorem coveredSquares_subset_union_of_stacked {u v u' v' : GridState n}
    (Q : GridPentagonBetween a s u v) (P : GridPentagonBetween a s u' v') (r : GridRectangle n)
    (hbottom : Q.bottom = P.bottom) (htop : Q.top = r.top) (hcut : P.top = r.bottom)
    (hP : Grid.cIco Q.left (finRotate n a) ⊆ Grid.cIco P.left (finRotate n a))
    (hr : Grid.cIco Q.left (finRotate n a) ⊆ Grid.cIco r.left r.right) :
    Q.coveredSquares ⊆ P.coveredSquares ∪ r.coveredSquares := by
  have ha : a ∈ Grid.cIco r.left r.right := hr (Grid.self_mem_cIco_finRotate Q.left_ne)
  have hmem_r {p : Fin n × Fin n} (hcol : p.1 ∈ Grid.cIco r.left r.right)
      (hrow : p.2 ∈ Grid.cIco r.bottom r.top) : p ∈ r.coveredSquares :=
    (r.mem_coveredSquares p).2 ⟨(r.mem_coveredColumns p.1).2 hcol, (r.mem_coveredRows p.2).2 hrow⟩
  intro p hp
  rcases (Q.mem_coveredSquares p).mp hp with ⟨hne, hcol, hrow⟩ | ⟨hcol, hrow⟩ | ⟨hcol, hrow⟩
  · rw [hbottom, htop] at hrow
    rcases Finset.mem_union.mp
      (Grid.cIco_subset_cIco_union_cIco (w := r.bottom) hrow) with hrow' | hrow'
    · exact Finset.mem_union.mpr (Or.inr (hmem_r (hr hcol) hrow'))
    · refine Finset.mem_union.mpr (Or.inl ((P.mem_coveredSquares p).2 (Or.inl ⟨hne, hP hcol, ?_⟩)))
      rwa [hcut]
  · rw [htop] at hrow
    have hs : p.2 ≠ s := Grid.ne_left_of_mem_cIoo hrow
    rcases Finset.mem_union.mp (Grid.cIco_subset_cIco_union_cIco (w := r.bottom)
      (Grid.cIoo_subset_cIco _ _ hrow)) with hrow' | hrow'
    · refine Finset.mem_union.mpr (Or.inr (hmem_r ?_ hrow'))
      rwa [hcol]
    · refine Finset.mem_union.mpr (Or.inl
        ((P.mem_coveredSquares p).2 (Or.inr (Or.inl ⟨hcol, Grid.mem_cIoo_of_mem_cIco ?_ hs⟩))))
      rwa [hcut]
  · rw [hbottom] at hrow
    exact Finset.mem_union.mpr (Or.inl ((P.mem_coveredSquares p).2 (Or.inr (Or.inr ⟨hcol, hrow⟩))))

/-- A pentagon carries no `X`-marking exactly when the underlying rectangle carries none away
from columns `a` and `finRotate n a`, the `X`-marking of column `a` is not above the turn row,
and the `X`-marking of column `finRotate n a` is not below it. -/
theorem disjoint_coveredSquares_XSet_iff (P : GridPentagonBetween a s x y) (G : GridDiagram n) :
    Disjoint P.coveredSquares G.XSet ↔
      (∀ c, c ≠ a → c ∈ Grid.cIco P.left (finRotate n a) → G.X c ∉ Grid.cIco P.bottom P.top) ∧
        G.X a ∉ Grid.cIoo s P.top ∧ G.X (finRotate n a) ∉ Grid.cIco P.bottom s := by
  rw [Finset.disjoint_right]
  constructor
  · intro h
    refine ⟨fun c hca hc hX => h ((G.mk_mem_XSet c _).mpr rfl) ?_,
      fun hX => h ((G.mk_mem_XSet a _).mpr rfl) ?_,
      fun hX => h ((G.mk_mem_XSet (finRotate n a) _).mpr rfl) ?_⟩ <;>
      simp_all [mem_coveredSquares]
  · rintro ⟨h₁, h₂, h₃⟩ p hp hmem
    rw [G.mem_XSet] at hp
    rw [mem_coveredSquares, ← hp] at hmem
    rcases hmem with ⟨hca, hc, hr⟩ | ⟨hpa, hr⟩ | ⟨hpb, hr⟩
    · exact h₁ p.1 hca hc hr
    · exact h₂ (hpa ▸ hr)
    · exact h₃ (hpb ▸ hr)

end GridPentagonBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### The pentagons counted by the pentagon map -/

/-- The pentagons from `x` to `y` counted by a validated column commutation: the empty pentagons
carrying no `X`-marking. -/
noncomputable def pentagons (C : ColumnCommutationData G) (x y : GridState n) :
    Finset (GridPentagonBetween C.column C.turnRow x y) := by
  classical
  exact Finset.univ.filter fun P => P.IsEmpty ∧ Disjoint P.coveredSquares G.XSet

/-- Membership in the counted pentagons is emptiness together with `X`-avoidance. -/
@[simp]
theorem mem_pentagons {C : ColumnCommutationData G} {x y : GridState n}
    (P : GridPentagonBetween C.column C.turnRow x y) :
    P ∈ G.pentagons C x y ↔ P.IsEmpty ∧ Disjoint P.coveredSquares G.XSet := by
  classical
  simp [pentagons]

/-- At most one pentagon contributes to each matrix coefficient of the pentagon map. -/
theorem card_pentagons_le_one (C : ColumnCommutationData G) (x y : GridState n) :
    (G.pentagons C x y).card ≤ 1 :=
  Finset.card_le_one_of_subsingleton _

/-- The columns of the original diagram whose `O`-marking a pentagon carries. -/
noncomputable def pentagonOColumns {x y : GridState n} (C : ColumnCommutationData G)
    (P : GridPentagonBetween C.column C.turnRow x y) : Finset (Fin n) :=
  G.OColumnsOfSquares P.coveredSquares

/-- A column is a covered `O`-column of a pentagon exactly when its `O`-marking is a covered
square. -/
@[simp]
theorem mem_pentagonOColumns {x y : GridState n} {C : ColumnCommutationData G}
    {P : GridPentagonBetween C.column C.turnRow x y} {c : Fin n} :
    c ∈ G.pentagonOColumns C P ↔ (c, G.O c) ∈ P.coveredSquares := by
  simp [pentagonOColumns]

/-- The number of columns whose `O`-marking a pentagon carries is the number of `O`-markings among
the squares it covers. -/
theorem card_pentagonOColumns {x y : GridState n} (C : ColumnCommutationData G)
    (P : GridPentagonBetween C.column C.turnRow x y) :
    (G.pentagonOColumns C P).card = (G.OSet ∩ P.coveredSquares).card := by
  exact G.card_OColumnsOfSquares P.coveredSquares

variable (R : Type*) [CommSemiring R]

/-- The weight of a pentagon in the pentagon map: the product of the variables that the commuted
diagram `G.swapColumns a (finRotate n a)` attaches to the `O`-markings the pentagon carries.

The `O`-marking of column `c` of `G` is the `O`-marking of column `Equiv.swap a (finRotate n a) c`
of the commuted diagram, so it contributes the variable of that column. -/
noncomputable def pentagonWeight {x y : GridState n} (C : ColumnCommutationData G)
    (P : GridPentagonBetween C.column C.turnRow x y) : MvPolynomial (Fin n) R :=
  ∏ c ∈ G.pentagonOColumns C P,
    MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) c)

/-- The weight of a pentagon as a product over the squares it covers: the renamed variable of the
column at each `O`-marked square and `1` elsewhere. -/
theorem pentagonWeight_eq_prod_coveredSquares {x y : GridState n}
    (C : ColumnCommutationData G) (P : GridPentagonBetween C.column C.turnRow x y) :
    G.pentagonWeight R C P =
      ∏ p ∈ P.coveredSquares,
        if p ∈ G.OSet then MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) p.1)
        else (1 : MvPolynomial (Fin n) R) := by
  rw [pentagonWeight, pentagonOColumns, G.prod_ite_OSet_eq_prod_OColumnsOfSquares
    (fun c => (MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) c) :
      MvPolynomial (Fin n) R))]

/-- The weight of a pentagon is the product of the variables of the columns of the commuted
diagram whose `O`-marking the pentagon carries. -/
theorem pentagonWeight_eq_prod_swapColumns {x y : GridState n}
    (C : ColumnCommutationData G) (P : GridPentagonBetween C.column C.turnRow x y) :
    G.pentagonWeight R C P =
      ∏ c ∈ Finset.univ.filter (fun c =>
          (Equiv.swap C.column (finRotate n C.column) c,
            (G.swapColumns C.column (finRotate n C.column)).O c) ∈ P.coveredSquares),
        MvPolynomial.X c := by
  rw [pentagonWeight]
  exact Finset.prod_nbij' (Equiv.swap C.column (finRotate n C.column))
    (Equiv.swap C.column (finRotate n C.column))
    (by simp [swapColumns_O, GridState.swapColumns_apply])
    (by simp [swapColumns_O, GridState.swapColumns_apply]) (by simp) (by simp) (by simp)

/-- The pentagon weight is the squarefree monomial of its covered `O`-columns, with variables
renamed by the column swap. -/
theorem pentagonWeight_eq_monomial {x y : GridState n}
    (C : ColumnCommutationData G) (P : GridPentagonBetween C.column C.turnRow x y) :
    G.pentagonWeight R C P =
      MvPolynomial.monomial (∑ c ∈ G.pentagonOColumns C P,
        Finsupp.single (Equiv.swap C.column (finRotate n C.column) c) 1) 1 := by
  classical
  rw [pentagonWeight, MvPolynomial.monomial_sum_one]
  simp only [← MvPolynomial.X_pow_eq_monomial, pow_one]

/-- Renamed back by the column swap, the weight of a pentagon is the product, over the squares it
covers, of the variable of the square's column in `G` at the `O`-marked squares and of `1`
elsewhere: the weight a rectangle covering the same squares would have in `G`. -/
theorem rename_pentagonWeight {x y : GridState n} (C : ColumnCommutationData G)
    (P : GridPentagonBetween C.column C.turnRow x y) :
    MvPolynomial.rename (Equiv.swap C.column (finRotate n C.column)) (G.pentagonWeight R C P) =
      ∏ p ∈ P.coveredSquares,
        if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R) := by
  rw [pentagonWeight_eq_prod_coveredSquares, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  split_ifs <;> simp

/-- The weight of a pentagon of the reverse commutation, which turns at the opposite intersection
and is counted in the commuted diagram, is the product, over the squares it covers read in `G` by
exchanging the two commuted columns, of the variable of the square's column at the `O`-marked
squares of `G` and of `1` elsewhere. -/
theorem pentagonWeight_reverse {y z : GridState n} (C : ColumnCommutationData G)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z) :
    (G.swapColumns C.column (finRotate n C.column)).pentagonWeight R C.reverse Q =
      ∏ p ∈ Q.coveredSquares.map
          ((Equiv.swap C.column (finRotate n C.column)).prodCongr (Equiv.refl (Fin n))).toEmbedding,
        if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R) := by
  rw [pentagonWeight_eq_prod_coveredSquares, Finset.prod_map]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [ColumnCommutationData.reverse_column]

/-! ### The pentagon map -/

/-- The matrix coefficient of the pentagon map from `x` to `y`: the sum of the weights of the
empty pentagons from `x` to `y` carrying no `X`-marking. -/
noncomputable def pentagonCoefficient (C : ColumnCommutationData G) (x y : GridState n) :
    MvPolynomial (Fin n) R :=
  ∑ P ∈ G.pentagons C x y, G.pentagonWeight R C P

/-- The matrix coefficient of the pentagon map is the sum of the weights of its counted
pentagons. -/
theorem pentagonCoefficient_def (C : ColumnCommutationData G) (x y : GridState n) :
    G.pentagonCoefficient R C x y =
      ∑ P ∈ G.pentagons C x y, G.pentagonWeight R C P :=
  (rfl)

/-- The value of the pentagon map on a single grid-state generator. -/
noncomputable def pentagonMapOnGenerator (C : ColumnCommutationData G) (x : GridState n) :
    GridChainMinus R n :=
  Finset.univ.sum fun y : GridState n => Finsupp.single y (G.pentagonCoefficient R C x y)

/-- The `y`-coefficient of the pentagon map on the generator `x`. -/
@[simp]
theorem pentagonMapOnGenerator_apply (C : ColumnCommutationData G) (x y : GridState n) :
    G.pentagonMapOnGenerator R C x y = G.pentagonCoefficient R C x y := by
  rw [pentagonMapOnGenerator, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz.symm]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- The pentagon map moves a generator only by swapping its point on the replaced line against
one other point. -/
theorem pentagonMapOnGenerator_support_subset (C : ColumnCommutationData G) (x : GridState n) :
    (G.pentagonMapOnGenerator R C x).support ⊆
      Finset.univ.image fun j => x.swapColumns j (finRotate n C.column) := by
  intro y hy
  rw [Finsupp.mem_support_iff, pentagonMapOnGenerator_apply, pentagonCoefficient] at hy
  obtain ⟨P, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  exact Finset.mem_image.mpr ⟨P.left, Finset.mem_univ _, P.target_eq_swapColumns.symm⟩

/-- The pentagon map `GC⁻(G) → GC⁻(G.swapColumns C.column (finRotate n C.column))` of the
validated column commutation `C`, counting the pentagons whose turn lies on their terminal side.

A generator `x` goes to the sum over the counted pentagons from `x` of their weights times their
targets. The map is semilinear over the renaming of the variables by
`Equiv.swap C.column (finRotate n C.column)`, which carries the variable of each `O`-marking in
`G` to its variable in the commuted diagram. It is only one of the two parts of the commutation
map `Φ`; the other counts the pentagons turning on their initial side
(`TauCeti.GridDiagram.initialPentagonMap`). -/
noncomputable def pentagonMap (C : ColumnCommutationData G) :
    GridChainMinus R n →ₛₗ[((renameEquiv R
      (Equiv.swap C.column (finRotate n C.column))).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)] GridChainMinus R n :=
  GridChain.renameMatrixMap R (Equiv.swap C.column (finRotate n C.column))
    (G.pentagonCoefficient R C)

/-- The pentagon map sends a generator with coefficient `p` to the renamed coefficient times the
row of pentagon weights of the generator. -/
@[simp]
theorem pentagonMap_single (C : ColumnCommutationData G) (x : GridState n)
    (p : MvPolynomial (Fin n) R) :
    G.pentagonMap R C (Finsupp.single x p) =
      rename (Equiv.swap C.column (finRotate n C.column)) p •
        G.pentagonMapOnGenerator R C x := by
  rw [pentagonMap, GridChain.renameMatrixMap_single, pentagonMapOnGenerator]

/-- The coefficient formula for the pentagon map on an arbitrary chain. -/
@[simp]
theorem pentagonMap_apply_apply (C : ColumnCommutationData G) (c : GridChainMinus R n)
    (y : GridState n) :
    G.pentagonMap R C c y =
      c.sum fun x p =>
        rename (Equiv.swap C.column (finRotate n C.column)) p *
          G.pentagonCoefficient R C x y := by
  rw [pentagonMap, GridChain.renameMatrixMap_apply_apply]

end GridDiagram

end TauCeti
