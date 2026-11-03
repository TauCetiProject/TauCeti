/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Hexagon
public import TauCeti.KnotTheory.Grid.CrossingChange.Basic
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain

/-!
# The hexagon homotopy of a crossing change

Let `b = finRotate n a` and let the marking segments of the columns `a` and `b` of a grid diagram
`G` interleave, so that `G' = G.swapColumns a b` differs from `G` by a cross-commutation. Draw
both diagrams on one torus, replacing the vertical grid line `β` with index `b` by a curve `γ`
which leaves the column-`a` markings of `G` on its right and the column-`b` markings on its left.
Since the segments interleave, `γ` meets `β` in four points, and each of the four thin bigons
between them contains exactly one marking. The crossing change maps of Ozsváth--Stipsicz--Szabó
are the pentagon-counting maps `Φ : GC⁻(G) → GC⁻(G')` (`GridDiagram.commutationMap`) turning at
one intersection point `s`, and `Ψ : GC⁻(G') → GC⁻(G)` turning at another intersection point
`t`. Going up the vertical circle the markings of the two columns alternate, in one of two
orders, which determine the rows of `s` and `t`.

* If `O_a` lies on the arc of column `b`, the order is `O_b, O_a, X_b, X_a`. Then `s` lies in
  the row of `O_a`, `t` in the row of `X_b`, and `Φ` preserves the bigrading
  (`GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc`).
* Otherwise the order is `O_b, X_a, X_b, O_a`. Then `s` lies in the row of `X_a` and `t` in the
  row of `O_b`, and `Φ` has bidegree `(-2, -1)`
  (`GridDiagram.commutationBidegree_eq_of_notMem_columnArc`).

Only the bidegree of `Φ` is proved by these lemmas. Following Ozsváth--Stipsicz--Szabó,
Section 6.1, `Ψ` has the complementary bidegree, `(-2, -1)` in the first order and `(0, 0)` in
the second, so that either way `Ψ ∘ Φ` has the bidegree `(-2, -1)` of multiplication by a
variable; the bidegree of `Ψ` is not proved here. `Ψ ∘ Φ` is compared with such a
multiplication by a homotopy `H : GC⁻(G) → GC⁻(G)` counting empty hexagons carrying
no `X`-marking, whose boundary turns at `t` and at `s`. These have the shapes
`TauCeti.GridHexagonBetween a t s` (terminal side running up `β` to `t`, up `γ` to `s` and up `β`
again) and `TauCeti.GridInitialHexagonBetween a s t` (initial side running up `β` to `s`, up `γ`
to `t` and up `β` again), exactly as for the commutation homotopy
`GridDiagram.commutationHomotopy`. They carry different markings, however: the arc of `γ` along a
hexagon may cross `β` again, and the bigons it passes contain markings of both columns.

Only the markings a hexagon carries matter. The arc of `γ` from the lower to the upper corner
leaves every marking of one column on the inside of the hexagon and every marking of the other
on the outside. So a hexagon of the first shape, cutting from row `s₀` up to row `s₁`, carries
the markings of its rectangle except the column-`a` markings in the rows from `s₀` up to `s₁`,
together with the column-`b` markings strictly between these rows
(`TauCeti.GridHexagonBetween.crossingCoveredSquares`); the second shape carries those of its
rectangle except the column-`b` markings in the cut rows, together with the column-`a` markings
strictly between them (`TauCeti.GridInitialHexagonBetween.crossingCoveredSquares`). A marking of
column `a` in the turn row of `Φ` lies below the turn point and a marking of column `b` above it,
as for pentagons, and the other way round at the turn point of `Ψ`.

`GridDiagram.crossingChangeHomotopy` counts both shapes, with turn row the turn row of a column
turn `C` and the other corner in a row `t`. In both orders of the markings, the rectangle under a
counted hexagon carries one more `X`-marking than the hexagon and as many `O`-markings, so `H` has
bidegree `(-1, -1)`, the bidegree compatible with `∂⁻ ∘ H + H ∘ ∂⁻ = V + Ψ ∘ Φ`
(`OddComponentGridDiagram.crossingChangeHomotopy_mem_bigradedChainMinusPiece_of_mem_columnArc`
and its counterpart for the other order). That homotopy equation itself is not proved here.

## Main definitions

* `TauCeti.GridHexagonBetween.crossingCoveredSquares`,
  `TauCeti.GridInitialHexagonBetween.crossingCoveredSquares`: the squares whose markings lie
  inside a hexagon of a crossing change.
* `TauCeti.GridDiagram.crossingChangeHexagons`,
  `TauCeti.GridDiagram.crossingChangeInitialHexagons`: the counted hexagons of each shape, the
  empty ones carrying no `X`-marking.
* `TauCeti.GridDiagram.crossingChangeHexagonWeight`,
  `TauCeti.GridDiagram.crossingChangeInitialHexagonWeight`: the monomials of the `O`-markings
  they carry.
* `TauCeti.GridDiagram.crossingChangeHexagonCoefficient`,
  `TauCeti.GridDiagram.crossingChangeHomotopy`: the matrix coefficients of the hexagon-counting
  map `H : GC⁻(G) → GC⁻(G)`, and the map itself.

## Main results

* `TauCeti.GridDiagram.crossingChangeHomotopy_single_apply` and
  `TauCeti.GridDiagram.crossingChangeHomotopy_apply_apply`: the matrix coefficients of `H`.
* `TauCeti.GridDiagram.XSet_inter_eq_of_hexagon` and
  `TauCeti.GridDiagram.XSet_inter_eq_of_initialHexagon`: the rectangle under a hexagon carrying
  no `X`-marking carries exactly the `X`-marking of the column it cuts away, when that marking
  lies in the cut rows.
* `crossingChangeHomotopy_mem_bigradedChainMinusPiece_of_mem_columnArc` and
  `crossingChangeHomotopy_mem_bigradedChainMinusPiece_of_notMem_columnArc`, in the namespace
  `TauCeti.OddComponentGridDiagram`: for interleaving columns, with the corners of the hexagons at
  the turn points of the crossing change maps, `H` has bidegree `(-1, -1)`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1: the crossing change maps and the hexagon homotopies
  showing that both composites are homotopic to multiplication by a variable.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  four intersection points of `β` and `γ`, the corners `s` and `t`, and the homotopy equations
  for the hexagons with consecutive corners at `t` and `s`.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridHexagonBetween

variable {n : ℕ} {a s s' : Fin n} {x y : GridState n}

/-- The squares whose marking lies inside a hexagon turning on its terminal side, cutting from row
`s` up to row `s'`, when `γ` leaves the column-`a` markings on its right and the column-`b`
markings on its left, `b` being `finRotate n a`: the squares of the underlying rectangle except
those of column `a` in the rows from `s` up to `s'`, together with the squares of column `b`
strictly between these rows.

Unlike `GridHexagonBetween.coveredSquares`, this does not assume that the column-`a` markings lie
in a bigon between `s` and `s'`, as they do not for a crossing change. -/
noncomputable def crossingCoveredSquares (P : GridHexagonBetween a s s' x y) :
    Finset (Fin n × Fin n) :=
  {p ∈ P.toGridRectangle.coveredSquares | ¬(p.1 = a ∧ p.2 ∈ insert s' (Grid.cIco s s'))} ∪
    {finRotate n a} ×ˢ Grid.cIoo s s'

/-- Membership in the squares covered by a crossing-change hexagon turning on its terminal
side. -/
theorem mem_crossingCoveredSquares (P : GridHexagonBetween a s s' x y) (p : Fin n × Fin n) :
    p ∈ P.crossingCoveredSquares ↔
      p ∈ P.toGridRectangle.coveredSquares ∧ ¬(p.1 = a ∧ p.2 ∈ insert s' (Grid.cIco s s')) ∨
        p.1 = finRotate n a ∧ p.2 ∈ Grid.cIoo s s' := by
  simp only [crossingCoveredSquares, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
    Finset.mem_singleton]

/-- The squares covered by a crossing-change hexagon turning on its terminal side depend only on
its underlying toroidal rectangle. -/
theorem crossingCoveredSquares_eq_of_toGridRectangle_eq {u v : GridState n}
    (P : GridHexagonBetween a s s' x y) (Q : GridHexagonBetween a s s' u v)
    (h : P.toGridRectangle = Q.toGridRectangle) :
    P.crossingCoveredSquares = Q.crossingCoveredSquares := by
  ext p
  simp only [mem_crossingCoveredSquares, h]

end GridHexagonBetween

namespace GridInitialHexagonBetween

variable {n : ℕ} {a s s' : Fin n} {x y : GridState n}

/-- The squares whose marking lies inside a hexagon turning on its initial side, cutting from row
`s` up to row `s'`, when `γ` leaves the column-`a` markings on its right and the column-`b`
markings on its left, `b` being `finRotate n a`: the squares of the underlying rectangle except
those of column `b` in the rows from `s` up to `s'`, together with the squares of column `a`
strictly between these rows.

Unlike `GridInitialHexagonBetween.coveredSquares`, this does not assume that the column-`b`
markings lie in a bigon between `s` and `s'`, as they do not for a crossing change. -/
noncomputable def crossingCoveredSquares (P : GridInitialHexagonBetween a s s' x y) :
    Finset (Fin n × Fin n) :=
  {p ∈ P.toGridRectangle.coveredSquares |
      ¬(p.1 = finRotate n a ∧ p.2 ∈ insert s' (Grid.cIco s s'))} ∪
    {a} ×ˢ Grid.cIoo s s'

/-- Membership in the squares covered by a crossing-change hexagon turning on its initial side. -/
theorem mem_crossingCoveredSquares (P : GridInitialHexagonBetween a s s' x y)
    (p : Fin n × Fin n) :
    p ∈ P.crossingCoveredSquares ↔
      p ∈ P.toGridRectangle.coveredSquares ∧
          ¬(p.1 = finRotate n a ∧ p.2 ∈ insert s' (Grid.cIco s s')) ∨
        p.1 = a ∧ p.2 ∈ Grid.cIoo s s' := by
  simp only [crossingCoveredSquares, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
    Finset.mem_singleton]

/-- The squares covered by a crossing-change hexagon turning on its initial side depend only on
its underlying toroidal rectangle. -/
theorem crossingCoveredSquares_eq_of_toGridRectangle_eq {u v : GridState n}
    (P : GridInitialHexagonBetween a s s' x y) (Q : GridInitialHexagonBetween a s s' u v)
    (h : P.toGridRectangle = Q.toGridRectangle) :
    P.crossingCoveredSquares = Q.crossingCoveredSquares := by
  ext p
  simp only [mem_crossingCoveredSquares, h]

end GridInitialHexagonBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### The hexagons counted by the crossing change homotopy -/

/-- The hexagons of a crossing change turning on their terminal side from `x` to `y`, for the
column turn `C` and a second intersection point in row `t`: the empty hexagons cutting from `t`
up to `C.turnRow` and carrying no `X`-marking. -/
noncomputable def crossingChangeHexagons (C : ColumnTurn n) (t : Fin n) (x y : GridState n) :
    Finset (GridHexagonBetween C.column t C.turnRow x y) := by
  classical
  exact Finset.univ.filter fun P => P.IsEmpty ∧ Disjoint P.crossingCoveredSquares G.XSet

/-- Membership in the counted terminal-side hexagons of a crossing change is emptiness together
with `X`-avoidance. -/
@[simp]
theorem mem_crossingChangeHexagons {C : ColumnTurn n} {t : Fin n} {x y : GridState n}
    (P : GridHexagonBetween C.column t C.turnRow x y) :
    P ∈ G.crossingChangeHexagons C t x y ↔
      P.IsEmpty ∧ Disjoint P.crossingCoveredSquares G.XSet := by
  classical
  simp [crossingChangeHexagons]

/-- The hexagons of a crossing change turning on their initial side from `x` to `y`, for the
column turn `C` and a second intersection point in row `t`: the empty hexagons cutting from
`C.turnRow` up to `t` and carrying no `X`-marking. -/
noncomputable def crossingChangeInitialHexagons (C : ColumnTurn n) (t : Fin n)
    (x y : GridState n) : Finset (GridInitialHexagonBetween C.column C.turnRow t x y) := by
  classical
  exact Finset.univ.filter fun P => P.IsEmpty ∧ Disjoint P.crossingCoveredSquares G.XSet

/-- Membership in the counted initial-side hexagons of a crossing change is emptiness together
with `X`-avoidance. -/
@[simp]
theorem mem_crossingChangeInitialHexagons {C : ColumnTurn n} {t : Fin n} {x y : GridState n}
    (P : GridInitialHexagonBetween C.column C.turnRow t x y) :
    P ∈ G.crossingChangeInitialHexagons C t x y ↔
      P.IsEmpty ∧ Disjoint P.crossingCoveredSquares G.XSet := by
  classical
  simp [crossingChangeInitialHexagons]

/-! ### The homotopy -/

variable (R : Type*) [CommSemiring R]

/-- The weight of a crossing-change hexagon turning on its terminal side: the product of the
variables of the `O`-markings it carries. -/
noncomputable def crossingChangeHexagonWeight {a s s' : Fin n} {x y : GridState n}
    (P : GridHexagonBetween a s s' x y) : MvPolynomial (Fin n) R :=
  ∏ c ∈ G.OColumnsOfSquares P.crossingCoveredSquares, MvPolynomial.X c

/-- The weight of a crossing-change hexagon turning on its terminal side is the squarefree
monomial of the `O`-markings it carries. -/
theorem crossingChangeHexagonWeight_eq_monomial {a s s' : Fin n} {x y : GridState n}
    (P : GridHexagonBetween a s s' x y) :
    G.crossingChangeHexagonWeight R P =
      monomial (∑ c ∈ G.OColumnsOfSquares P.crossingCoveredSquares, Finsupp.single c 1) 1 := by
  classical
  rw [crossingChangeHexagonWeight, monomial_sum_one]
  simp only [← X_pow_eq_monomial, pow_one]

/-- The weight of a crossing-change hexagon turning on its initial side: the product of the
variables of the `O`-markings it carries. -/
noncomputable def crossingChangeInitialHexagonWeight {a s s' : Fin n} {x y : GridState n}
    (P : GridInitialHexagonBetween a s s' x y) : MvPolynomial (Fin n) R :=
  ∏ c ∈ G.OColumnsOfSquares P.crossingCoveredSquares, MvPolynomial.X c

/-- The weight of a crossing-change hexagon turning on its initial side is the squarefree
monomial of the `O`-markings it carries. -/
theorem crossingChangeInitialHexagonWeight_eq_monomial {a s s' : Fin n} {x y : GridState n}
    (P : GridInitialHexagonBetween a s s' x y) :
    G.crossingChangeInitialHexagonWeight R P =
      monomial (∑ c ∈ G.OColumnsOfSquares P.crossingCoveredSquares, Finsupp.single c 1) 1 := by
  classical
  rw [crossingChangeInitialHexagonWeight, monomial_sum_one]
  simp only [← X_pow_eq_monomial, pow_one]

/-- The matrix coefficient from `x` to `y` of the crossing change homotopy: the sum of the
weights of the counted hexagons of both shapes. -/
noncomputable def crossingChangeHexagonCoefficient (C : ColumnTurn n) (t : Fin n)
    (x y : GridState n) : MvPolynomial (Fin n) R :=
  ∑ P ∈ G.crossingChangeHexagons C t x y, G.crossingChangeHexagonWeight R P +
    ∑ P ∈ G.crossingChangeInitialHexagons C t x y, G.crossingChangeInitialHexagonWeight R P

/-- The matrix coefficient of the crossing change homotopy is the sum of the weights of its
counted hexagons. -/
theorem crossingChangeHexagonCoefficient_def (C : ColumnTurn n) (t : Fin n) (x y : GridState n) :
    G.crossingChangeHexagonCoefficient R C t x y =
      ∑ P ∈ G.crossingChangeHexagons C t x y, G.crossingChangeHexagonWeight R P +
        ∑ P ∈ G.crossingChangeInitialHexagons C t x y, G.crossingChangeInitialHexagonWeight R P :=
  (rfl)

/-- The crossing change homotopy `H : GC⁻(G) → GC⁻(G)` of the column turn `C` with a second
intersection point in row `t`, linear over the polynomial ring: a generator `x` goes to the sum
over the counted hexagons from `x`, of both shapes, of their weights times their targets.

For interleaving columns, with `C.turnRow` and `t` the rows of the turn points of the crossing
change maps `Φ` and `Ψ`, it is meant to be the homotopy between `Ψ ∘ Φ` and multiplication by a
variable; only its bidegree is proved here. -/
noncomputable def crossingChangeHomotopy (C : ColumnTurn n) (t : Fin n) :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  Finsupp.linearCombination (MvPolynomial (Fin n) R) fun x =>
    Finsupp.equivFunOnFinite.symm fun y => G.crossingChangeHexagonCoefficient R C t x y

/-- The matrix coefficients of the crossing change homotopy. -/
theorem crossingChangeHomotopy_single_apply (C : ColumnTurn n) (t : Fin n) (x y : GridState n) :
    G.crossingChangeHomotopy R C t (Finsupp.single x 1) y =
      G.crossingChangeHexagonCoefficient R C t x y := by
  rw [crossingChangeHomotopy, Finsupp.linearCombination_single, one_smul,
    Finsupp.equivFunOnFinite_symm_apply_apply]

/-- The coefficient formula for the crossing change homotopy on an arbitrary chain. -/
@[simp]
theorem crossingChangeHomotopy_apply_apply (C : ColumnTurn n) (t : Fin n)
    (c : GridChainMinus R n) (y : GridState n) :
    G.crossingChangeHomotopy R C t c y =
      c.sum fun x p => p * G.crossingChangeHexagonCoefficient R C t x y := by
  rw [crossingChangeHomotopy, Finsupp.linearCombination_apply]
  simp [Finsupp.sum_apply]

/-! ### The markings of the rectangle under a hexagon -/

section Markings

variable {G} {a s s' : Fin n} {x y : GridState n}

/-- The rectangle under a crossing-change hexagon turning on its terminal side carries as many
`O`-markings as the hexagon, provided that the column-`a` `O`-marking lies in the cut rows exactly
when the column-`b` one lies strictly between them. -/
private theorem card_OColumns_eq_of_hexagon (P : GridHexagonBetween a s s' x y)
    (hO : G.O a ∈ insert s' (Grid.cIco s s') ↔ G.O (finRotate n a) ∈ Grid.cIoo s s') :
    (G.OColumnsOfSquares P.crossingCoveredSquares).card =
      (G.OColumns P.toGridRectangle).card := by
  have ha : a ∈ Grid.cIco P.left (finRotate n a) := Grid.self_mem_cIco_finRotate P.left_ne
  have hb : finRotate n a ∉ Grid.cIco P.left (finRotate n a) := Grid.right_notMem_cIco _ _
  have hab : a ≠ finRotate n a := fun h => hb (h ▸ ha)
  have hrows := P.insert_cIco_subset_cIco_bottom_top
  by_cases hOa : G.O a ∈ insert s' (Grid.cIco s s')
  · -- The hexagon trades the `O`-marking of column `a` for that of column `b`.
    have hOb := hO.mp hOa
    rw [← Finset.card_map (s := G.OColumns P.toGridRectangle)
      (Equiv.swap a (finRotate n a)).toEmbedding]
    congr 1
    ext c
    rw [Finset.mem_map_equiv, Equiv.symm_swap, mem_OColumnsOfSquares, mem_OColumns,
      P.mem_crossingCoveredSquares]
    rcases eq_or_ne c a with rfl | hca
    · rw [Equiv.swap_apply_left]
      exact iff_of_false (fun h => h.elim (fun h => h.2 ⟨rfl, hOa⟩) fun h => hab h.1)
        fun h => hb ((P.mem_toGridRectangle_coveredSquares _).mp h).1
    rcases eq_or_ne c (finRotate n a) with rfl | hcb
    · rw [Equiv.swap_apply_right]
      exact iff_of_true (Or.inr ⟨rfl, hOb⟩)
        ((P.mem_toGridRectangle_coveredSquares _).mpr ⟨ha, hrows hOa⟩)
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
      exact ⟨fun h => h.elim And.left fun h => (hcb h.1).elim,
        fun h => Or.inl ⟨h, fun h' => hca h'.1⟩⟩
  · -- The hexagon carries the same `O`-markings as its rectangle.
    have hOb : G.O (finRotate n a) ∉ Grid.cIoo s s' := fun h => hOa (hO.mpr h)
    congr 1
    ext c
    rw [mem_OColumnsOfSquares, mem_OColumns, P.mem_crossingCoveredSquares]
    rcases eq_or_ne c (finRotate n a) with rfl | hcb
    · exact iff_of_false
        (fun h => h.elim (fun h => hb ((P.mem_toGridRectangle_coveredSquares _).mp h.1).1)
          fun h => hOb h.2)
        fun h => hb ((P.mem_toGridRectangle_coveredSquares _).mp h).1
    · refine ⟨fun h => h.elim And.left fun h => (hcb h.1).elim, fun h => Or.inl ⟨h, ?_⟩⟩
      rintro ⟨rfl, h'⟩
      exact hOa h'

/-- The rectangle under a crossing-change hexagon turning on its terminal side and carrying no
`X`-marking carries exactly one `X`-marking, that of column `a`, provided that it lies in the cut
rows. -/
theorem XSet_inter_eq_of_hexagon {P : GridHexagonBetween a s s' x y}
    (hX : G.X a ∈ insert s' (Grid.cIco s s')) (hP : Disjoint P.crossingCoveredSquares G.XSet) :
    G.XSet ∩ P.toGridRectangle.coveredSquares = {(a, G.X a)} := by
  ext ⟨c, r⟩
  rw [Finset.mem_inter, Finset.mem_singleton, G.mk_mem_XSet]
  constructor
  · rintro ⟨rfl, hr⟩
    by_contra hne
    have hca : c ≠ a := fun h => hne (by rw [h])
    refine Finset.disjoint_left.mp hP ((P.mem_crossingCoveredSquares _).mpr
      (Or.inl ⟨hr, fun h => hca h.1⟩)) ((G.mk_mem_XSet c _).mpr rfl)
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, (P.mem_toGridRectangle_coveredSquares _).mpr
      ⟨Grid.self_mem_cIco_finRotate P.left_ne, P.insert_cIco_subset_cIco_bottom_top hX⟩⟩

/-- The rectangle under a crossing-change hexagon turning on its initial side carries as many
`O`-markings as the hexagon, provided that the column-`b` `O`-marking lies in the cut rows exactly
when the column-`a` one lies strictly between them. -/
private theorem card_OColumns_eq_of_initialHexagon (P : GridInitialHexagonBetween a s s' x y)
    (hO : G.O (finRotate n a) ∈ insert s' (Grid.cIco s s') ↔ G.O a ∈ Grid.cIoo s s') :
    (G.OColumnsOfSquares P.crossingCoveredSquares).card =
      (G.OColumns P.toGridRectangle).card := by
  have hb : finRotate n a ∈ Grid.cIco (finRotate n a) P.right :=
    Grid.left_mem_cIco P.right_ne.symm
  have ha : a ∉ Grid.cIco (finRotate n a) P.right := by simp
  have hab : a ≠ finRotate n a := fun h => ha (h ▸ hb)
  have hrows := P.insert_cIco_subset_cIco_bottom_top
  by_cases hOb : G.O (finRotate n a) ∈ insert s' (Grid.cIco s s')
  · -- The hexagon trades the `O`-marking of column `b` for that of column `a`.
    have hOa := hO.mp hOb
    rw [← Finset.card_map (s := G.OColumns P.toGridRectangle)
      (Equiv.swap a (finRotate n a)).toEmbedding]
    congr 1
    ext c
    rw [Finset.mem_map_equiv, Equiv.symm_swap, mem_OColumnsOfSquares, mem_OColumns,
      P.mem_crossingCoveredSquares]
    rcases eq_or_ne c a with rfl | hca
    · rw [Equiv.swap_apply_left]
      exact iff_of_true (Or.inr ⟨rfl, hOa⟩)
        ((P.mem_toGridRectangle_coveredSquares _).mpr ⟨hb, hrows hOb⟩)
    rcases eq_or_ne c (finRotate n a) with rfl | hcb
    · rw [Equiv.swap_apply_right]
      exact iff_of_false (fun h => h.elim (fun h => h.2 ⟨rfl, hOb⟩) fun h => hab h.1.symm)
        fun h => ha ((P.mem_toGridRectangle_coveredSquares _).mp h).1
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
      exact ⟨fun h => h.elim And.left fun h => (hca h.1).elim,
        fun h => Or.inl ⟨h, fun h' => hcb h'.1⟩⟩
  · -- The hexagon carries the same `O`-markings as its rectangle.
    have hOa : G.O a ∉ Grid.cIoo s s' := fun h => hOb (hO.mpr h)
    congr 1
    ext c
    rw [mem_OColumnsOfSquares, mem_OColumns, P.mem_crossingCoveredSquares]
    rcases eq_or_ne c a with rfl | hca
    · exact iff_of_false
        (fun h => h.elim (fun h => ha ((P.mem_toGridRectangle_coveredSquares _).mp h.1).1)
          fun h => hOa h.2)
        fun h => ha ((P.mem_toGridRectangle_coveredSquares _).mp h).1
    · refine ⟨fun h => h.elim And.left fun h => (hca h.1).elim, fun h => Or.inl ⟨h, ?_⟩⟩
      rintro ⟨rfl, h'⟩
      exact hOb h'

/-- The rectangle under a crossing-change hexagon turning on its initial side and carrying no
`X`-marking carries exactly one `X`-marking, that of column `b`, provided that it lies in the cut
rows. -/
theorem XSet_inter_eq_of_initialHexagon {P : GridInitialHexagonBetween a s s' x y}
    (hX : G.X (finRotate n a) ∈ insert s' (Grid.cIco s s'))
    (hP : Disjoint P.crossingCoveredSquares G.XSet) :
    G.XSet ∩ P.toGridRectangle.coveredSquares = {(finRotate n a, G.X (finRotate n a))} := by
  ext ⟨c, r⟩
  rw [Finset.mem_inter, Finset.mem_singleton, G.mk_mem_XSet]
  constructor
  · rintro ⟨rfl, hr⟩
    by_contra hne
    have hcb : c ≠ finRotate n a := fun h => hne (by rw [h])
    refine Finset.disjoint_left.mp hP ((P.mem_crossingCoveredSquares _).mpr
      (Or.inl ⟨hr, fun h => hcb h.1⟩)) ((G.mk_mem_XSet c _).mpr rfl)
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, (P.mem_toGridRectangle_coveredSquares _).mpr ⟨Grid.left_mem_cIco P.right_ne.symm,
      P.insert_cIco_subset_cIco_bottom_top hX⟩⟩

end Markings

/-! ### Grading changes across a hexagon -/

section Grading

variable {G} {a s s' : Fin n} {x y : GridState n}

/-- The `O`-Maslov grading across an empty crossing-change hexagon turning on its terminal side,
when the hexagon carries as many `O`-markings as its rectangle. -/
private theorem maslovOℤ_eq_of_hexagon {P : GridHexagonBetween a s s' x y}
    (hO : G.O a ∈ insert s' (Grid.cIco s s') ↔ G.O (finRotate n a) ∈ Grid.cIoo s s')
    (hP : P.IsEmpty) :
    G.maslovOℤ y =
      G.maslovOℤ x + -1 + 2 * ((G.OColumnsOfSquares P.crossingCoveredSquares).card : ℤ) := by
  have h := G.maslovOℤ_sub_two_mul_card_OColumns hP
  rw [← card_OColumns_eq_of_hexagon P hO] at h
  linarith

/-- The doubled Alexander grading across a crossing-change hexagon turning on its terminal side
and carrying no `X`-marking, under the hypotheses of the marking lemmas. -/
private theorem alexanderTwoℤ_eq_of_hexagon {P : GridHexagonBetween a s s' x y}
    (hX : G.X a ∈ insert s' (Grid.cIco s s'))
    (hO : G.O a ∈ insert s' (Grid.cIco s s') ↔ G.O (finRotate n a) ∈ Grid.cIoo s s')
    (hP : Disjoint P.crossingCoveredSquares G.XSet) :
    G.alexanderTwoℤ y =
      G.alexanderTwoℤ x + 2 * -1 +
        2 * ((G.OColumnsOfSquares P.crossingCoveredSquares).card : ℤ) := by
  have h := G.alexanderTwoℤ_eq_add_two_mul_card_sub_card P.toGridRectangleBetween
  rw [XSet_inter_eq_of_hexagon hX hP, Finset.card_singleton,
    ← card_OColumns_eq_of_hexagon P hO] at h
  push_cast at h
  linarith

/-- The `O`-Maslov grading across an empty crossing-change hexagon turning on its initial side,
when the hexagon carries as many `O`-markings as its rectangle. -/
private theorem maslovOℤ_eq_of_initialHexagon {P : GridInitialHexagonBetween a s s' x y}
    (hO : G.O (finRotate n a) ∈ insert s' (Grid.cIco s s') ↔ G.O a ∈ Grid.cIoo s s')
    (hP : P.IsEmpty) :
    G.maslovOℤ y =
      G.maslovOℤ x + -1 + 2 * ((G.OColumnsOfSquares P.crossingCoveredSquares).card : ℤ) := by
  have h := G.maslovOℤ_sub_two_mul_card_OColumns hP
  rw [← card_OColumns_eq_of_initialHexagon P hO] at h
  linarith

/-- The doubled Alexander grading across a crossing-change hexagon turning on its initial side
and carrying no `X`-marking, under the hypotheses of the marking lemmas. -/
private theorem alexanderTwoℤ_eq_of_initialHexagon {P : GridInitialHexagonBetween a s s' x y}
    (hX : G.X (finRotate n a) ∈ insert s' (Grid.cIco s s'))
    (hO : G.O (finRotate n a) ∈ insert s' (Grid.cIco s s') ↔ G.O a ∈ Grid.cIoo s s')
    (hP : Disjoint P.crossingCoveredSquares G.XSet) :
    G.alexanderTwoℤ y =
      G.alexanderTwoℤ x + 2 * -1 +
        2 * ((G.OColumnsOfSquares P.crossingCoveredSquares).card : ℤ) := by
  have h := G.alexanderTwoℤ_eq_add_two_mul_card_sub_card P.toGridRectangleBetween
  rw [XSet_inter_eq_of_initialHexagon hX hP, Finset.card_singleton,
    ← card_OColumns_eq_of_initialHexagon P hO] at h
  push_cast at h
  linarith

/-! ### The two orders of interleaving markings -/

/-- If the segments of columns `a` and `b = finRotate n a` interleave with `O_a` on the arc of
column `b`, so that the markings read `O_b, O_a, X_b, X_a` going up, then the hexagons with
corners in the rows of `X_b` and `O_a` carry the markings required by the grading lemmas. -/
private theorem rows_of_mem_columnArc (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∈ G.columnArc (finRotate n a)) :
    (G.X a ∈ insert (G.O a) (Grid.cIco (G.X (finRotate n a)) (G.O a)) ∧
      (G.O a ∈ insert (G.O a) (Grid.cIco (G.X (finRotate n a)) (G.O a)) ↔
        G.O (finRotate n a) ∈ Grid.cIoo (G.X (finRotate n a)) (G.O a))) ∧
    (G.X (finRotate n a) ∈ insert (G.X (finRotate n a)) (Grid.cIco (G.O a) (G.X (finRotate n a))) ∧
      (G.O (finRotate n a) ∈
          insert (G.X (finRotate n a)) (Grid.cIco (G.O a) (G.X (finRotate n a))) ↔
        G.O a ∈ Grid.cIoo (G.O a) (G.X (finRotate n a)))) := by
  have hX : G.X a ∈ Grid.cIoo (G.X (finRotate n a)) (G.O (finRotate n a)) := by
    rcases (columnsInterleaving_iff G _ _).mp h with ⟨-, h₂⟩ | ⟨h₁, -⟩
    · exact h₂
    · exact absurd h₁ (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hO)
  rw [mem_columnArc] at hO
  refine ⟨⟨?_, iff_of_true (Finset.mem_insert_self _ _) ?_⟩,
    ⟨Finset.mem_insert_self _ _, iff_of_false ?_ ?_⟩⟩ <;>
  -- Every remaining claim is a statement about the cyclic order of the four rows.
  · simp only [Finset.mem_insert, Grid.mem_cIco, Grid.mem_cIoo, Fin.ext_iff, ne_eq] at hO hX ⊢
    split_ifs at * <;> omega

/-- If the segments of columns `a` and `b = finRotate n a` interleave with `O_a` off the arc of
column `b`, so that the markings read `O_b, X_a, X_b, O_a` going up, then the hexagons with
corners in the rows of `O_b` and `X_a` carry the markings required by the grading lemmas. -/
private theorem rows_of_notMem_columnArc (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∉ G.columnArc (finRotate n a)) :
    (G.X a ∈ insert (G.X a) (Grid.cIco (G.O (finRotate n a)) (G.X a)) ∧
      (G.O a ∈ insert (G.X a) (Grid.cIco (G.O (finRotate n a)) (G.X a)) ↔
        G.O (finRotate n a) ∈ Grid.cIoo (G.O (finRotate n a)) (G.X a))) ∧
    (G.X (finRotate n a) ∈ insert (G.O (finRotate n a)) (Grid.cIco (G.X a) (G.O (finRotate n a))) ∧
      (G.O (finRotate n a) ∈
          insert (G.O (finRotate n a)) (Grid.cIco (G.X a) (G.O (finRotate n a))) ↔
        G.O a ∈ Grid.cIoo (G.X a) (G.O (finRotate n a)))) := by
  obtain ⟨h₁, h₂⟩ : G.O a ∈ Grid.cIoo (G.X (finRotate n a)) (G.O (finRotate n a)) ∧
      G.X a ∈ G.columnArc (finRotate n a) := by
    rcases (columnsInterleaving_iff G _ _).mp h with ⟨h₁, -⟩ | h'
    · exact absurd h₁ hO
    · exact h'
  rw [mem_columnArc] at h₂
  refine ⟨⟨Finset.mem_insert_self _ _, iff_of_false ?_ ?_⟩,
    ⟨?_, iff_of_true (Finset.mem_insert_self _ _) ?_⟩⟩ <;>
  -- Every remaining claim is a statement about the cyclic order of the four rows.
  · simp only [Finset.mem_insert, Grid.mem_cIco, Grid.mem_cIoo, Fin.ext_iff, ne_eq] at h₁ h₂ ⊢
    split_ifs at * <;> omega

end Grading

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (C : GridDiagram.ColumnTurn n) {t : Fin n}

/-- The crossing change homotopy has bidegree `(-1, -1)` once the rows of its corners make every
counted hexagon carry one `X`-marking fewer than its rectangle and as many `O`-markings. -/
private theorem crossingChangeHomotopy_mem_bigradedChainMinusPiece_of_rows (R : Type*)
    [CommSemiring R]
    (hX : G.1.X C.column ∈ insert C.turnRow (Grid.cIco t C.turnRow))
    (hO : G.1.O C.column ∈ insert C.turnRow (Grid.cIco t C.turnRow) ↔
      G.1.O (finRotate n C.column) ∈ Grid.cIoo t C.turnRow)
    (hX' : G.1.X (finRotate n C.column) ∈ insert t (Grid.cIco C.turnRow t))
    (hO' : G.1.O (finRotate n C.column) ∈ insert t (Grid.cIco C.turnRow t) ↔
      G.1.O C.column ∈ Grid.cIoo C.turnRow t)
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.crossingChangeHomotopy R C t c ∈ G.bigradedChainMinusPiece R (g + (-1, -1)) := by
  classical
  refine G.matrixMap_mem_bigradedChainMinusPiece_add R G (Equiv.refl _)
    (fun x y => G.1.crossingChangeHexagonCoefficient R C t x y) _
    (fun c y => by simp [G.1.crossingChangeHomotopy_apply_apply R C t]) (-1, -1)
    (fun x y w hw e => ?_) hc
  rw [GridDiagram.crossingChangeHexagonCoefficient_def] at hw
  rcases Finset.mem_union.mp (MvPolynomial.support_add hw) with hw | hw
  · obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hw)
    rw [GridDiagram.crossingChangeHexagonWeight_eq_monomial] at hwP
    obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hwP)
    obtain ⟨hPe, hPX⟩ := (G.1.mem_crossingChangeHexagons P).mp hP
    have hA := G.1.alexanderTwoℤ_eq_of_hexagon hX hO hPX
    rw [← two_mul_alexanderℤ, ← two_mul_alexanderℤ] at hA
    exact G.monomialBidegree_mapDomain_add_sum_eq_add G _ e _ (-1, -1)
      (G.1.maslovOℤ_eq_of_hexagon hO hPe) (by simp only; omega)
  · obtain ⟨P, hP, hwP⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hw)
    rw [GridDiagram.crossingChangeInitialHexagonWeight_eq_monomial] at hwP
    obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hwP)
    obtain ⟨hPe, hPX⟩ := (G.1.mem_crossingChangeInitialHexagons P).mp hP
    have hA := G.1.alexanderTwoℤ_eq_of_initialHexagon hX' hO' hPX
    rw [← two_mul_alexanderℤ, ← two_mul_alexanderℤ] at hA
    exact G.monomialBidegree_mapDomain_add_sum_eq_add G _ e _ (-1, -1)
      (G.1.maslovOℤ_eq_of_initialHexagon hO' hPe) (by simp only; omega)

/-- **The crossing change homotopy has bidegree `(-1, -1)`**, for markings in the order
`O_b, O_a, X_b, X_a`. If the segments of the columns `a = C.column` and `b = finRotate n a`
interleave with `O_a` on the arc of column `b`, then the hexagons with corners at the turn point
in the row of `O_a` and at the point in the row `t` of `X_b` make the hexagon-counting
map `H` send a chain of `GC⁻(G)` homogeneous of bidegree `g` to one homogeneous of bidegree
`g + (-1, -1)`. This is the bidegree of a homotopy between multiplication by a variable and the
composite of the crossing change maps, of bidegrees `(0, 0)` and `(-2, -1)`. -/
theorem crossingChangeHomotopy_mem_bigradedChainMinusPiece_of_mem_columnArc (R : Type*)
    [CommSemiring R] (h : G.1.ColumnsInterleaving C.column (finRotate n C.column))
    (hO : G.1.O C.column ∈ G.1.columnArc (finRotate n C.column))
    (hs : C.turnRow = G.1.O C.column) (ht : t = G.1.X (finRotate n C.column))
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.crossingChangeHomotopy R C t c ∈ G.bigradedChainMinusPiece R (g + (-1, -1)) := by
  obtain ⟨⟨hX, hO₁⟩, ⟨hX', hO₂⟩⟩ := GridDiagram.rows_of_mem_columnArc h hO
  subst ht
  exact G.crossingChangeHomotopy_mem_bigradedChainMinusPiece_of_rows C R (by rwa [hs])
    (by rwa [hs]) (by rwa [hs]) (by rwa [hs]) hc

/-- **The crossing change homotopy has bidegree `(-1, -1)`**, for markings in the order
`O_b, X_a, X_b, O_a`. If the segments of the columns `a = C.column` and `b = finRotate n a`
interleave with `O_a` off the arc of column `b`, then the hexagons with corners at the turn point
in the row of `X_a` and at the point in the row `t` of `O_b` make the hexagon-counting
map `H` send a chain of `GC⁻(G)` homogeneous of bidegree `g` to one homogeneous of bidegree
`g + (-1, -1)`. This is the bidegree of a homotopy between multiplication by a variable and the
composite of the crossing change maps, of bidegrees `(-2, -1)` and `(0, 0)`. -/
theorem crossingChangeHomotopy_mem_bigradedChainMinusPiece_of_notMem_columnArc (R : Type*)
    [CommSemiring R] (h : G.1.ColumnsInterleaving C.column (finRotate n C.column))
    (hO : G.1.O C.column ∉ G.1.columnArc (finRotate n C.column))
    (hs : C.turnRow = G.1.X C.column) (ht : t = G.1.O (finRotate n C.column))
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.crossingChangeHomotopy R C t c ∈ G.bigradedChainMinusPiece R (g + (-1, -1)) := by
  obtain ⟨⟨hX, hO₁⟩, ⟨hX', hO₂⟩⟩ := GridDiagram.rows_of_notMem_columnArc h hO
  subst ht
  exact G.crossingChangeHomotopy_mem_bigradedChainMinusPiece_of_rows C R (by rwa [hs])
    (by rwa [hs]) (by rwa [hs]) (by rwa [hs]) hc

end OddComponentGridDiagram

end TauCeti
