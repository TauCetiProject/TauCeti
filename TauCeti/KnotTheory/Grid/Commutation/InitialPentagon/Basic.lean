/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Pentagon
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Pentagons turning on their initial side, and the commutation map

Let `b = finRotate n a`, and draw a column commutation of `G` as in `Commutation/Pentagon.lean`:
the vertical grid line `β` with index `b` is replaced by a curve `γ` meeting it at the turn point,
in square row `s`, where `γ` crosses from the left of `β` to its right going upwards, and at one
other point. The pentagons of `TauCeti.GridPentagonBetween` lie to the left of `β ∪ γ`: their
terminal side runs up `γ` to the turn point and then up `β`. The commutation map `Φ` of
Ozsváth--Stipsicz--Szabó also counts the empty pentagons lying to the right of `β ∪ γ`, whose
*initial* side runs up `β` to the turn point and then up `γ`.

Such a pentagon from a state `x` of `G` to a state `y` of `G'` starts at the point of `x` on
`β`, runs right along a horizontal circle to a point of `y`, up a vertical line to a point of `x`,
left along a horizontal circle to the point of `y` on `γ`, down `γ` to an intersection point of
`β` and `γ`, and down `β` back to the start. Convexity of the corner at the intersection point
forces it to be the same turn point as for the terminal-side pentagons. Its corners are those of
the oriented rectangle from `x` to `y` whose initial side is the line `b`, and the turn row must
lie among the rows that side spans (`TauCeti.GridInitialPentagonBetween`).

Away from columns `a` and `b` such a pentagon carries the markings of the underlying rectangle.
The column-`a` markings lie in the bigon below the turn point, between `γ` and `β`; the pentagon
contains such a marking exactly when it lies above the turn row, where its initial side runs
along `γ`. The column-`b` markings lie in the bigon above the turn point, between `β` and `γ`; the
pentagon contains such a marking exactly when it lies below the turn row, where its initial side
runs along `β`. These are the same two arcs as for a terminal-side pentagon
(`TauCeti.GridInitialPentagonBetween.coveredSquares`).

Both kinds of pentagon are needed. A rectangle followed by a terminal-side pentagon can make a
corner of angle `3π/2` at the turn point. Cutting that domain along the other curve through the
turn point decomposes it again, now as a rectangle followed by an initial-side pentagon. Without
the initial-side pentagons the pentagon-counting map is not a chain map. For example, take the
`4 × 4` diagram with `O = (0, 2, 1, 3)` and `X = (2, 3, 0, 1)`, commute columns `0` and `1`, and
use turn row `2` with the other intersection in row `0`. The identity state then has the diagonal
coefficient `V₁` in `Φ ∘ ∂⁻ - ∂⁻' ∘ Φ` when only terminal-side pentagons are counted. Counting
initial-side pentagons too gives a second rectangle--pentagon term with the same weight, so the
coefficient vanishes in characteristic two.

## Main definitions

* `TauCeti.GridInitialPentagonBetween`: the combinatorial shape of a pentagon turning on its
  initial side.
* `TauCeti.GridInitialPentagonBetween.coveredSquares`: the squares of `G` whose marking lies
  inside such a pentagon.
* `TauCeti.GridDiagram.initialPentagons`: the empty ones carrying no `X`-marking.
* `TauCeti.GridDiagram.initialPentagonWeight`, `TauCeti.GridDiagram.initialPentagonCoefficient`:
  their monomial weights and the resulting matrix coefficients.
* `TauCeti.GridDiagram.initialPentagonMap`: the map counting them.
* `TauCeti.GridDiagram.commutationMap`: the commutation map
  `Φ : GC⁻(G) → GC⁻(G.swapColumns a b)`, counting pentagons of both kinds.

## Main results

* `TauCeti.GridInitialPentagonBetween.nonempty_iff`: such a pentagon from `x` to `y` exists
  exactly when `y` is `x` with column `b` swapped against another column `j` and the turn row lies
  between the rows of `x` on `b` and on `j`; `Subsingleton` records that it is then unique.
* `TauCeti.GridInitialPentagonBetween.mem_coveredSquares_iff_of_ne`: away from columns `a` and `b`
  the covered squares are those of the underlying rectangle;
  `TauCeti.GridInitialPentagonBetween.mk_mem_coveredSquares_left_column` and
  `TauCeti.GridInitialPentagonBetween.mk_mem_coveredSquares_right_column` give them in those two
  columns.
* `TauCeti.GridInitialPentagonBetween.disjoint_coveredSquares_XSet_iff`: the `X`-avoidance
  condition column by column.
* `TauCeti.GridDiagram.commutationMap_apply_apply`: the matrix coefficients of `Φ` are the sums of
  those of the two pentagon maps.

## References

The commutation map is `P` of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Section 5.1, and `Φ_{βγ}` of Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer
homology*, Section 3.1 (arXiv:math/0610559), both of which count every empty pentagon with a
corner at the turn point.
-/

public section

namespace TauCeti

open MvPolynomial

/-- The combinatorial shape of a pentagon turning on its initial side, for columns `a` and
`finRotate n a`, with turn point in square row `s`, from a grid state `x` to a grid state `y`.

It is recorded by the oriented rectangle from `x` to `y` with the same corners, whose initial
side is the grid line `finRotate n a` together with the curve `γ` replacing it above the turn
point; the rows that side spans must contain the turn row. The points of `x` sit at the
lower-left corner, on `β`, and the upper-right corner; those of `y` at the upper-left corner, on
`γ`, and the lower-right corner. -/
structure GridInitialPentagonBetween {n : ℕ} (a s : Fin n) (x y : GridState n)
    extends GridRectangleBetween x y where
  /-- The initial side lies on the grid line between column `a` and the next column. -/
  left_eq : left = finRotate n a
  /-- The turn point lies on the initial side: its row is among the rows that side spans. -/
  turn_mem : s ∈ Grid.cIco (x left) (x right)

namespace GridInitialPentagonBetween

variable {n : ℕ} {a s : Fin n} {x y : GridState n}

/-- The terminal side of a pentagon turning on its initial side is not the line replaced by
`γ`. -/
theorem right_ne (P : GridInitialPentagonBetween a s x y) : P.right ≠ finRotate n a :=
  P.left_eq ▸ P.left_ne_right.symm

/-- The two columns next to the replaced line of a pentagon turning on its initial side are
distinct. -/
theorem ne_finRotate (P : GridInitialPentagonBetween a s x y) : a ≠ finRotate n a := fun h => by
  -- The initial side `finRotate n a` lies in the column arc, but `a` never does.
  have hmem : a ∈ Grid.cIco (finRotate n a) P.right :=
    Eq.subst (motive := fun c => c ∈ Grid.cIco (finRotate n a) P.right) h.symm
      (Grid.left_mem_cIco P.right_ne.symm)
  simp at hmem

/-- The turn row lies in the rows spanned by the initial side, from the row of `x` on the replaced
line to its row on the terminal side. -/
theorem turn_mem_cIco (P : GridInitialPentagonBetween a s x y) :
    s ∈ Grid.cIco (x (finRotate n a)) (x P.right) :=
  P.left_eq ▸ P.turn_mem

/-- The turn row of a pentagon turning on its initial side lies among its rows. -/
theorem turn_mem_cIco_bottom_top (P : GridInitialPentagonBetween a s x y) :
    s ∈ Grid.cIco P.bottom P.top := by
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def]
  exact P.turn_mem

/-- A pentagon turning on its initial side is determined by its underlying rectangle. -/
theorem toGridRectangleBetween_injective :
    Function.Injective
      (toGridRectangleBetween : GridInitialPentagonBetween a s x y → GridRectangleBetween x y) := by
  rintro ⟨P, _, _⟩ ⟨Q, _, _⟩ (rfl : P = Q)
  rfl

/-- There is at most one pentagon turning on its initial side between two grid states: its
initial side is the replaced line, which determines the underlying rectangle. -/
instance : Subsingleton (GridInitialPentagonBetween a s x y) where
  allEq P Q := toGridRectangleBetween_injective <|
    GridRectangleBetween.left_injective (P.left_eq.trans Q.left_eq.symm)

/-- There are finitely many pentagons turning on their initial side between two grid states. -/
noncomputable instance : Fintype (GridInitialPentagonBetween a s x y) :=
  Fintype.ofInjective _ toGridRectangleBetween_injective

/-- The target of a pentagon turning on its initial side is its source with the line replaced by
`γ` swapped against the terminal side. -/
theorem target_eq_swapColumns (P : GridInitialPentagonBetween a s x y) :
    y = x.swapColumns (finRotate n a) P.right :=
  P.left_eq ▸ P.toGridRectangleBetween.target_eq_swapColumns

/-- The pentagon turning on its initial side from `x` to `x.swapColumns (finRotate n a) j`, when
the turn row lies between the rows of `x` on the two sides. -/
def ofSwapColumns (x : GridState n) (j : Fin n) (hj : j ≠ finRotate n a)
    (hs : s ∈ Grid.cIco (x (finRotate n a)) (x j)) :
    GridInitialPentagonBetween a s x (x.swapColumns (finRotate n a) j) where
  left := finRotate n a
  right := j
  left_ne_right := hj.symm
  map_left := by simp
  map_right := by simp
  map_of_ne c hb hc := by rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hb hc]
  left_eq := rfl
  turn_mem := hs

/-- The terminal side of the pentagon built from a column swap. -/
@[simp]
theorem ofSwapColumns_right (x : GridState n) (j : Fin n) (hj : j ≠ finRotate n a)
    (hs : s ∈ Grid.cIco (x (finRotate n a)) (x j)) :
    (ofSwapColumns x j hj hs).right = j :=
  (rfl)

/-- A pentagon turning on its initial side from `x` to `y` exists exactly when `y` is `x` with
the line replaced by `γ` swapped against some other column `j`, and the turn row lies between the
rows of `x` on that line and on `j`. -/
theorem nonempty_iff :
    Nonempty (GridInitialPentagonBetween a s x y) ↔
      ∃ j, j ≠ finRotate n a ∧ s ∈ Grid.cIco (x (finRotate n a)) (x j) ∧
        y = x.swapColumns (finRotate n a) j := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.right, P.right_ne, P.turn_mem_cIco, P.target_eq_swapColumns⟩
  · rintro ⟨j, hj, hs, rfl⟩
    exact ⟨ofSwapColumns x j hj hs⟩

/-- The squares of the original diagram whose marking lies inside a pentagon turning on its
initial side.

Away from the two columns next to the replaced line these are the squares covered by the
underlying rectangle. In column `a` they are the rows strictly above the turn row, up to the top
side, where the initial side runs along `γ` to the left of `β`; in column `finRotate n a` they are
the rows from the bottom side up to and excluding the turn row, where the initial side runs along
`β`. The markings of these two columns in the turn row lie below and above the turn point
respectively, and neither is inside the pentagon. As for `GridPentagonBetween.coveredSquares`,
only the marked squares of those two columns matter. -/
noncomputable def coveredSquares (P : GridInitialPentagonBetween a s x y) :
    Finset (Fin n × Fin n) :=
  ((Grid.cIco (finRotate n a) P.right).erase (finRotate n a) ×ˢ Grid.cIco P.bottom P.top) ∪
    (({a} ×ˢ Grid.cIoo s P.top) ∪ ({finRotate n a} ×ˢ Grid.cIco P.bottom s))

/-- Membership in the covered squares of a pentagon turning on its initial side, column by
column. -/
theorem mem_coveredSquares (P : GridInitialPentagonBetween a s x y) (p : Fin n × Fin n) :
    p ∈ P.coveredSquares ↔
      (p.1 ≠ finRotate n a ∧ p.1 ∈ Grid.cIco (finRotate n a) P.right ∧
          p.2 ∈ Grid.cIco P.bottom P.top) ∨
        (p.1 = a ∧ p.2 ∈ Grid.cIoo s P.top) ∨
          (p.1 = finRotate n a ∧ p.2 ∈ Grid.cIco P.bottom s) := by
  simp only [coveredSquares, Finset.mem_union, Finset.mem_product, Finset.mem_erase,
    Finset.mem_singleton, and_assoc]

/-- Away from the two columns next to the replaced line, a pentagon turning on its initial side
covers the squares of its underlying rectangle. -/
theorem mem_coveredSquares_iff_of_ne (P : GridInitialPentagonBetween a s x y)
    {p : Fin n × Fin n} (ha : p.1 ≠ a) (hb : p.1 ≠ finRotate n a) :
    p ∈ P.coveredSquares ↔ p ∈ P.toGridRectangle.coveredSquares := by
  simpa only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_left,
    GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, P.left_eq, ha, hb, ne_eq, not_false_eq_true,
    true_and, false_and, or_false] using P.mem_coveredSquares p

/-- In the column before the replaced line an initial-side pentagon covers the rows strictly
between the turn row and its top row. -/
theorem mk_mem_coveredSquares_left_column (P : GridInitialPentagonBetween a s x y)
    (t : Fin n) : (a, t) ∈ P.coveredSquares ↔ t ∈ Grid.cIoo s P.top := by
  have ha : a ∉ Grid.cIco (finRotate n a) P.right := by simp
  simp only [P.mem_coveredSquares, ha, P.ne_finRotate, ne_eq, not_false_eq_true, true_and,
    false_and, false_or, or_false]

/-- In the column after the replaced line an initial-side pentagon covers the rows from its
bottom row up to the turn row. -/
theorem mk_mem_coveredSquares_right_column (P : GridInitialPentagonBetween a s x y)
    (t : Fin n) : (finRotate n a, t) ∈ P.coveredSquares ↔ t ∈ Grid.cIco P.bottom s := by
  simp only [P.mem_coveredSquares, P.ne_finRotate.symm, ne_eq, not_true_eq_false, false_and,
    true_and, false_or]

/-- A pentagon turning on its initial side carries no `X`-marking exactly when the underlying
rectangle carries none away from columns `a` and `finRotate n a`, the `X`-marking of column `a` is
not above the turn row, and the `X`-marking of column `finRotate n a` is not below it. -/
theorem disjoint_coveredSquares_XSet_iff (P : GridInitialPentagonBetween a s x y)
    (G : GridDiagram n) :
    Disjoint P.coveredSquares G.XSet ↔
      (∀ c, c ≠ finRotate n a → c ∈ Grid.cIco (finRotate n a) P.right →
          G.X c ∉ Grid.cIco P.bottom P.top) ∧
        G.X a ∉ Grid.cIoo s P.top ∧ G.X (finRotate n a) ∉ Grid.cIco P.bottom s := by
  rw [Finset.disjoint_right]
  constructor
  · intro h
    refine ⟨fun c hcb hc hX => h ((G.mk_mem_XSet c _).mpr rfl) ?_,
      fun hX => h ((G.mk_mem_XSet a _).mpr rfl) ?_,
      fun hX => h ((G.mk_mem_XSet (finRotate n a) _).mpr rfl) ?_⟩ <;>
      simp_all [mem_coveredSquares]
  · rintro ⟨h₁, h₂, h₃⟩ p hp hmem
    rw [G.mem_XSet] at hp
    rw [mem_coveredSquares, ← hp] at hmem
    rcases hmem with ⟨hcb, hc, hr⟩ | ⟨hpa, hr⟩ | ⟨hpb, hr⟩
    · exact h₁ p.1 hcb hc hr
    · exact h₂ (hpa ▸ hr)
    · exact h₃ (hpb ▸ hr)

/-- Initial-side pentagons with the same underlying toroidal rectangle cover the same squares. -/
theorem coveredSquares_eq_of_toGridRectangle_eq {u v : GridState n}
    (P : GridInitialPentagonBetween a s x y) (Q : GridInitialPentagonBetween a s u v)
    (h : P.toGridRectangle = Q.toGridRectangle) : P.coveredSquares = Q.coveredSquares := by
  obtain ⟨-, hright, hbottom, htop⟩ := GridRectangle.ext_iff.mp h
  simp only [GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top] at hright hbottom htop
  ext p
  rw [P.mem_coveredSquares, Q.mem_coveredSquares, hright, hbottom, htop]

end GridInitialPentagonBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### The pentagons turning on their initial side counted by the commutation map -/

/-- The pentagons turning on their initial side from `x` to `y` counted by a validated column
commutation: the empty ones carrying no `X`-marking. -/
noncomputable def initialPentagons (C : ColumnCommutationData G) (x y : GridState n) :
    Finset (GridInitialPentagonBetween C.column C.turnRow x y) := by
  classical
  exact Finset.univ.filter fun P => P.IsEmpty ∧ Disjoint P.coveredSquares G.XSet

/-- Membership in the counted pentagons turning on their initial side is emptiness together with
`X`-avoidance. -/
@[simp]
theorem mem_initialPentagons {C : ColumnCommutationData G} {x y : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y) :
    P ∈ G.initialPentagons C x y ↔ P.IsEmpty ∧ Disjoint P.coveredSquares G.XSet := by
  classical
  simp [initialPentagons]

/-- At most one pentagon turning on its initial side contributes to each matrix coefficient. -/
theorem card_initialPentagons_le_one (C : ColumnCommutationData G) (x y : GridState n) :
    (G.initialPentagons C x y).card ≤ 1 :=
  Finset.card_le_one_of_subsingleton _

variable (R : Type*) [CommSemiring R]

/-- The weight of a pentagon turning on its initial side: the product of the variables that the
commuted diagram `G.swapColumns a (finRotate n a)` attaches to the `O`-markings the pentagon
carries. As for `GridDiagram.pentagonWeight`, the `O`-marking of column `c` of `G` contributes the
variable of column `Equiv.swap a (finRotate n a) c`. -/
noncomputable def initialPentagonWeight {x y : GridState n} (C : ColumnCommutationData G)
    (P : GridInitialPentagonBetween C.column C.turnRow x y) : MvPolynomial (Fin n) R :=
  ∏ c ∈ G.OColumnsOfSquares P.coveredSquares,
    MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) c)

/-- The weight of an initial-side pentagon is the monomial with one renamed variable for each
covered `O`-marking. -/
theorem initialPentagonWeight_eq_monomial {x y : GridState n}
    (C : ColumnCommutationData G) (P : GridInitialPentagonBetween C.column C.turnRow x y) :
    G.initialPentagonWeight R C P =
      monomial (∑ c ∈ G.OColumnsOfSquares P.coveredSquares,
        Finsupp.single (Equiv.swap C.column (finRotate n C.column) c) 1) 1 := by
  classical
  rw [initialPentagonWeight, monomial_sum_one]
  simp only [← X_pow_eq_monomial, pow_one]

/-- The weight of a pentagon turning on its initial side as a product over the squares it covers:
the renamed variable of the column at each `O`-marked square and `1` elsewhere. -/
theorem initialPentagonWeight_eq_prod_coveredSquares {x y : GridState n}
    (C : ColumnCommutationData G) (P : GridInitialPentagonBetween C.column C.turnRow x y) :
    G.initialPentagonWeight R C P =
      ∏ p ∈ P.coveredSquares,
        if p ∈ G.OSet then MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) p.1)
        else (1 : MvPolynomial (Fin n) R) := by
  rw [initialPentagonWeight, G.prod_ite_OSet_eq_prod_OColumnsOfSquares
    (fun c => (MvPolynomial.X (Equiv.swap C.column (finRotate n C.column) c) :
      MvPolynomial (Fin n) R))]

/-- The matrix coefficient from `x` to `y` of the map counting pentagons turning on their initial
side: the sum of the weights of the counted ones. -/
noncomputable def initialPentagonCoefficient (C : ColumnCommutationData G) (x y : GridState n) :
    MvPolynomial (Fin n) R :=
  ∑ P ∈ G.initialPentagons C x y, G.initialPentagonWeight R C P

/-- The matrix coefficient of the initial-side pentagon map is the sum of the weights of its
counted pentagons. -/
theorem initialPentagonCoefficient_def (C : ColumnCommutationData G) (x y : GridState n) :
    G.initialPentagonCoefficient R C x y =
      ∑ P ∈ G.initialPentagons C x y, G.initialPentagonWeight R C P :=
  (rfl)

/-- The map `GC⁻(G) → GC⁻(G.swapColumns C.column (finRotate n C.column))` counting the
pentagons that turn on their initial side, semilinear over the renaming of the variables by
`Equiv.swap C.column (finRotate n C.column)`. -/
noncomputable def initialPentagonMap (C : ColumnCommutationData G) :
    GridChainMinus R n →ₛₗ[((renameEquiv R
      (Equiv.swap C.column (finRotate n C.column))).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)] GridChainMinus R n :=
  GridChain.renameMatrixMap R (Equiv.swap C.column (finRotate n C.column))
    (G.initialPentagonCoefficient R C)

/-- The initial-side pentagon map sends a generator with coefficient `p` to the renamed
coefficient times the row of its matrix coefficients. -/
@[simp]
theorem initialPentagonMap_single (C : ColumnCommutationData G) (x : GridState n)
    (p : MvPolynomial (Fin n) R) :
    G.initialPentagonMap R C (Finsupp.single x p) =
      rename (Equiv.swap C.column (finRotate n C.column)) p •
        ∑ y : GridState n, Finsupp.single y (G.initialPentagonCoefficient R C x y) := by
  rw [initialPentagonMap, GridChain.renameMatrixMap_single]

/-- The coefficient formula for the initial-side pentagon map on an arbitrary chain. -/
@[simp]
theorem initialPentagonMap_apply_apply (C : ColumnCommutationData G) (c : GridChainMinus R n)
    (y : GridState n) :
    G.initialPentagonMap R C c y =
      c.sum fun x p =>
        rename (Equiv.swap C.column (finRotate n C.column)) p *
          G.initialPentagonCoefficient R C x y := by
  rw [initialPentagonMap, GridChain.renameMatrixMap_apply_apply]

/-! ### The commutation map -/

/-- The commutation map `Φ : GC⁻(G) → GC⁻(G.swapColumns C.column (finRotate n C.column))` of the
validated column commutation `C`: it counts the empty pentagons carrying no `X`-marking with a
corner at the turn point, both those turning on their terminal side (`GridDiagram.pentagonMap`)
and those turning on their initial side (`GridDiagram.initialPentagonMap`). -/
noncomputable def commutationMap (C : ColumnCommutationData G) :
    GridChainMinus R n →ₛₗ[((renameEquiv R
      (Equiv.swap C.column (finRotate n C.column))).toRingEquiv :
      MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R)] GridChainMinus R n :=
  G.pentagonMap R C + G.initialPentagonMap R C

/-- The commutation map is the sum of the two pentagon maps. -/
theorem commutationMap_apply (C : ColumnCommutationData G) (c : GridChainMinus R n) :
    G.commutationMap R C c = G.pentagonMap R C c + G.initialPentagonMap R C c :=
  LinearMap.add_apply _ _ _

/-- The coefficient formula for the commutation map on an arbitrary chain: its matrix
coefficients are the sums of those of the two pentagon maps. -/
@[simp]
theorem commutationMap_apply_apply (C : ColumnCommutationData G) (c : GridChainMinus R n)
    (y : GridState n) :
    G.commutationMap R C c y =
      c.sum fun x p =>
        rename (Equiv.swap C.column (finRotate n C.column)) p *
          (G.pentagonCoefficient R C x y + G.initialPentagonCoefficient R C x y) := by
  simp only [commutationMap_apply, Finsupp.add_apply, pentagonMap_apply_apply,
    initialPentagonMap_apply_apply, mul_add, Finsupp.sum_add]

end GridDiagram

end TauCeti
