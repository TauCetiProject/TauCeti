/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Hexagon
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Basic
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Annulus
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.PentagonPair

/-!
# Returning domains of the crossing change homotopy equation

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t` be a second row. The crossing change homotopy
`GridDiagram.crossingChangeHomotopy` counts hexagons with corners in the rows `s` and `t`, and the
round trip `Ψ ∘ Φ` through `G' = G.swapColumns a b` counts pairs of pentagons, the first turning in
row `s` (`GridDiagram.commutationMap` of `C`) and the second in row `t` (the commutation map of `G'`
at `C.withTurnRow t`). This file studies the domains of these counts that return to their source:
an empty hexagon followed or preceded by an empty rectangle, and two empty pentagons turning on
the same side.

Each such domain is a thin vertical annulus in column `a` or in column `b`. Whatever the annulus,
the squares carrying the markings it covers (the `crossingCoveredSquares` of a hexagon, the
`coveredSquares` of a rectangle or pentagon, those of the second pentagon read in `G` by exchanging
the two columns) are, without overlap, exactly `GridDiagram.crossingChangeAnnulusSquares`: the
squares of column `a` strictly between `s` and `t` going up, and those of column `b` strictly
between `t` and `s`. Consequently, when these squares carry no `X`-marking, every empty returning
domain is counted, and its weight is `GridDiagram.crossingChangeAnnulusWeight`, the product of the
variables of the `O`-markings they carry.

For interleaving columns, with `s` and `t` the rows of the turn points of the crossing change maps,
the annulus squares carry exactly one marking: the `O`-marking of column `b` when the markings read
`O_b, O_a, X_b, X_a` going up, and that of column `a` when they read `O_b, X_a, X_b, O_a`. This is
the variable `V` of the crossing change homotopy equation `∂H + H∂ = V + ΨΦ` on its diagonal
coefficients.

## Main definitions

* `TauCeti.GridDiagram.ColumnTurn.withTurnRow`: the column turn at the same columns turning in
  another row, the turn of the reverse crossing change map.
* `TauCeti.GridDiagram.crossingChangeAnnulusSquares`: the marked squares covered by every returning
  domain.
* `TauCeti.GridDiagram.crossingChangeAnnulusWeight`: the monomial of their `O`-markings.

## Main results

* `TauCeti.GridDiagram.mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff` and
  `TauCeti.GridDiagram.mem_pentagons_and_mem_pentagons_withTurnRow_iff`, with their initial-side
  versions: a returning pair is counted exactly when it is empty.
* `TauCeti.GridDiagram.crossingChangeHexagonWeight_mul_OMonomial_eq_crossingChangeAnnulusWeight` and
  `TauCeti.GridDiagram.rename_pentagonWeight_mul_pentagonWeight_eq_crossingChangeAnnulusWeight`,
  with their initial-side versions: a returning pair has the annulus weight.
* `TauCeti.GridDiagram.crossingChangeAnnulusWeight_eq_X_next_of_mem_columnArc` and
  `TauCeti.GridDiagram.crossingChangeAnnulusWeight_eq_X_column_of_notMem_columnArc`: for
  interleaving columns the annulus weight is a single variable.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 5.1 and 6.1: the thin annuli in the homotopy equations of
  commutation and of a crossing change.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  corners `s` and `t` of the hexagons of a crossing change.
-/

public section

namespace TauCeti

namespace GridDiagram

open MvPolynomial

variable {n : ℕ}

/-! ### The reverse turn -/

/-- The column turn at the same pair of columns as `C`, turning in row `t` instead. For a crossing
change with the turn of `Φ` in row `C.turnRow`, the reverse crossing change map `Ψ` is the
commutation map of the exchanged diagram at `C.withTurnRow t`.

It is reducible, so that the pentagons of this turn are the pentagons at the column `C.column`
turning in row `t`. -/
abbrev ColumnTurn.withTurnRow (C : ColumnTurn n) (t : Fin n) : ColumnTurn n :=
  ⟨C.column, t, C.column_ne_next⟩

/-- The turn in another row exchanges the same columns. -/
@[simp]
theorem ColumnTurn.withTurnRow_column (C : ColumnTurn n) (t : Fin n) :
    (C.withTurnRow t).column = C.column :=
  (rfl)

/-- The turn in row `t` turns in row `t`. -/
@[simp]
theorem ColumnTurn.withTurnRow_turnRow (C : ColumnTurn n) (t : Fin n) :
    (C.withTurnRow t).turnRow = t :=
  (rfl)

variable (G : GridDiagram n) (R : Type*) [CommSemiring R] (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### The annulus weight -/

/-- The squares carrying the markings of every domain returning to its source in the crossing
change homotopy equation: those of column `a` strictly between the turn row `s` and the row `t`
going up, and those of column `b = finRotate n a` strictly between `t` and `s`. -/
noncomputable def crossingChangeAnnulusSquares : Finset (Fin n × Fin n) :=
  {a} ×ˢ Grid.cIoo C.turnRow t ∪ {b} ×ˢ Grid.cIoo t C.turnRow

/-- Membership in the squares carrying the markings of a returning domain. -/
theorem mem_crossingChangeAnnulusSquares (p : Fin n × Fin n) :
    p ∈ crossingChangeAnnulusSquares C t ↔
      p.1 = a ∧ p.2 ∈ Grid.cIoo C.turnRow t ∨ p.1 = b ∧ p.2 ∈ Grid.cIoo t C.turnRow := by
  simp only [crossingChangeAnnulusSquares, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton]

/-- The weight of every domain returning to its source in the crossing change homotopy equation:
the product of the variables of the `O`-markings in `crossingChangeAnnulusSquares`. -/
noncomputable def crossingChangeAnnulusWeight : MvPolynomial (Fin n) R :=
  ∏ c ∈ G.OColumnsOfSquares (crossingChangeAnnulusSquares C t), MvPolynomial.X c

/-- The annulus weight is the product of the variables of the `O`-markings in the annulus
squares. -/
theorem crossingChangeAnnulusWeight_def :
    G.crossingChangeAnnulusWeight R C t =
      ∏ c ∈ G.OColumnsOfSquares (crossingChangeAnnulusSquares C t), MvPolynomial.X c :=
  (rfl)

/-! ### Domains carrying the markings of the annulus squares -/

variable {G C t}

/-- Two sets of squares which together cover exactly the annulus squares, without overlap, carry
the `O`-markings of the annulus weight. -/
private theorem prod_OColumnsOfSquares_mul_prod_eq {S₁ S₂ : Finset (Fin n × Fin n)}
    (h : ∀ p, (p ∈ S₁ ∨ p ∈ S₂ ↔ p ∈ crossingChangeAnnulusSquares C t) ∧ ¬(p ∈ S₁ ∧ p ∈ S₂)) :
    (∏ c ∈ G.OColumnsOfSquares S₁, (MvPolynomial.X c : MvPolynomial (Fin n) R)) *
        ∏ c ∈ G.OColumnsOfSquares S₂, MvPolynomial.X c =
      G.crossingChangeAnnulusWeight R C t := by
  rw [crossingChangeAnnulusWeight_def, ← Finset.prod_union]
  · congr 1
    ext c
    simp only [Finset.mem_union, mem_OColumnsOfSquares, (h _).1]
  · rw [Finset.disjoint_left]
    intro c h₁ h₂
    exact (h _).2 ⟨(G.mem_OColumnsOfSquares).mp h₁, (G.mem_OColumnsOfSquares).mp h₂⟩

/-- Two sets of squares covering exactly the annulus squares carry no `X`-marking when the annulus
squares carry none. -/
private theorem disjoint_XSet_of_forall {S₁ S₂ : Finset (Fin n × Fin n)}
    (h : ∀ p, (p ∈ S₁ ∨ p ∈ S₂ ↔ p ∈ crossingChangeAnnulusSquares C t) ∧ ¬(p ∈ S₁ ∧ p ∈ S₂))
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) :
    Disjoint S₁ G.XSet ∧ Disjoint S₂ G.XSet :=
  ⟨Finset.disjoint_of_subset_left (fun p hp => (h p).1.mp (Or.inl hp)) hX,
    Finset.disjoint_of_subset_left (fun p hp => (h p).1.mp (Or.inr hp)) hX⟩

/-- The rows of a returning hexagon--rectangle annulus: the hexagon spans the rows from `B` up to
`T` and cuts away those from `t` up to `s`, and the rectangle spans the rows from `T` up to `B`.
Together they cover the rows strictly between `s` and `t` exactly once. -/
private theorem rows_of_hexagon {B T s t ρ : Fin n} (ht : t ∈ Grid.cIco B T)
    (hs : s ∈ Grid.cIoo t T) :
    (ρ ∈ Grid.cIco B T ∧ ρ ∉ insert s (Grid.cIco t s) ∨ ρ ∈ Grid.cIco T B ↔
        ρ ∈ Grid.cIoo s t) ∧
      ¬((ρ ∈ Grid.cIco B T ∧ ρ ∉ insert s (Grid.cIco t s)) ∧ ρ ∈ Grid.cIco T B) := by
  simp only [Finset.mem_insert, Grid.mem_cIco, Grid.mem_cIoo, Fin.ext_iff, ne_eq] at ht hs ⊢
  split_ifs at * <;> omega

/-- A terminal-side crossing-change hexagon and an empty rectangle returning to its source,
both empty, together cover exactly the annulus squares. -/
private theorem hexagon_squares {u v : GridState n}
    (P : GridHexagonBetween a t C.turnRow u v) (r : GridRectangleBetween v u)
    (h : P.IsEmpty ∧ r.IsEmpty) (p : Fin n × Fin n) :
    (p ∈ P.crossingCoveredSquares ∨ p ∈ r.toGridRectangle.coveredSquares ↔
        p ∈ crossingChangeAnnulusSquares C t) ∧
      ¬(p ∈ P.crossingCoveredSquares ∧ p ∈ r.toGridRectangle.coveredSquares) := by
  obtain ⟨hl, ha⟩ := (P.isEmpty_and_isEmpty_iff r).mp h
  have hr : r.right = b :=
    (P.toGridRectangleBetween.right_eq_right_of_left_eq_left r hl).trans P.right_eq
  have hcol : ∀ c, c ∈ Grid.cIco a b ↔ c = a := fun c => by
    rw [Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, C.column_ne_next⟩, Finset.mem_singleton]
  have ht := P.lower_mem
  have hs := P.upper_mem
  rw [P.right_eq] at ht hs
  rw [ha] at ht
  obtain ⟨c, ρ⟩ := p
  rw [P.mem_crossingCoveredSquares, P.mem_toGridRectangle_coveredSquares,
    GridRectangleBetween.mem_toGridRectangle_coveredSquares_target, hl, ha, hr,
    mem_crossingChangeAnnulusSquares, GridRectangleBetween.bottom_def,
    GridRectangleBetween.top_def, ha, P.right_eq]
  simp only [hcol]
  rcases eq_or_ne c a with rfl | hca
  · simpa only [C.column_ne_next, true_and, false_and, or_false] using rows_of_hexagon ht hs
  rcases eq_or_ne c b with rfl | hcb
  · simp only [hca, true_and, false_and, and_false, false_or, or_false, iff_self,
      not_false_eq_true, and_self]
  · simp only [hca, hcb, false_and, or_self, iff_self, not_false_eq_true, and_self]

/-- An initial-side crossing-change hexagon and an empty rectangle returning to its source, both
empty, together cover exactly the annulus squares. -/
private theorem initialHexagon_squares {u v : GridState n}
    (P : GridInitialHexagonBetween a C.turnRow t u v) (r : GridRectangleBetween v u)
    (h : P.IsEmpty ∧ r.IsEmpty) (p : Fin n × Fin n) :
    (p ∈ P.crossingCoveredSquares ∨ p ∈ r.toGridRectangle.coveredSquares ↔
        p ∈ crossingChangeAnnulusSquares C t) ∧
      ¬(p ∈ P.crossingCoveredSquares ∧ p ∈ r.toGridRectangle.coveredSquares) := by
  obtain ⟨hl, hc⟩ := (P.isEmpty_and_isEmpty_iff r).mp h
  have hr : r.right = finRotate n b :=
    (P.toGridRectangleBetween.right_eq_right_of_left_eq_left r hl).trans hc
  have hbc : b ≠ finRotate n b := (finRotate n).injective.ne C.column_ne_next
  have hcol : ∀ c, c ∈ Grid.cIco b (finRotate n b) ↔ c = b := fun c => by
    rw [Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, hbc⟩, Finset.mem_singleton]
  have hs := P.lower_mem
  have ht := P.upper_mem
  rw [hc] at hs ht
  rw [P.left_eq] at hs
  obtain ⟨c, ρ⟩ := p
  rw [P.mem_crossingCoveredSquares, P.mem_toGridRectangle_coveredSquares,
    GridRectangleBetween.mem_toGridRectangle_coveredSquares_target, hl, P.left_eq, hr,
    mem_crossingChangeAnnulusSquares, GridRectangleBetween.bottom_def,
    GridRectangleBetween.top_def, P.left_eq, hc]
  simp only [hcol]
  rcases eq_or_ne c b with rfl | hcb
  · simpa only [(C.column_ne_next).symm, true_and, false_and, or_false, false_or] using
      rows_of_hexagon hs ht
  rcases eq_or_ne c a with rfl | hca
  · simp only [hcb, true_and, false_and, and_false, false_or, or_false, iff_self,
      not_false_eq_true, and_self]
  · simp only [hca, hcb, false_and, or_self, iff_self, not_false_eq_true, and_self]

/-! ### Returning pentagon pairs -/

/-- The rows of a returning pentagon pair: the first pentagon spans the rows from `B` up to `T`
and turns in row `s`, the second spans those from `T` up to `B` and turns in row `t`. In the
column on the side of the turns, they cover the rows strictly between `s` and `t` exactly once. -/
private theorem rows_of_pentagon {B T s t ρ : Fin n} (hs : s ∈ Grid.cIco B T)
    (ht : t ∈ Grid.cIco T B) :
    (ρ ∈ Grid.cIoo s T ∨ ρ ∈ Grid.cIco T t ↔ ρ ∈ Grid.cIoo s t) ∧
      ¬(ρ ∈ Grid.cIoo s T ∧ ρ ∈ Grid.cIco T t) := by
  simp only [Grid.mem_cIco, Grid.mem_cIoo, Fin.ext_iff, ne_eq] at hs ht ⊢
  split_ifs at * <;> omega

/-- A pentagon whose rectangle is the single column `a` covers the squares of column `a` strictly
between its turn row and its top, and those of column `b` from its bottom up to its turn row. -/
private theorem mem_coveredSquares_of_left_eq {u v : GridState n} {s : Fin n}
    (P : GridPentagonBetween a s u v) (hP : P.left = a) (p : Fin n × Fin n) :
    p ∈ P.coveredSquares ↔
      p.1 = a ∧ p.2 ∈ Grid.cIoo s P.top ∨ p.1 = b ∧ p.2 ∈ Grid.cIco P.bottom s := by
  rw [P.mem_coveredSquares, hP, Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, C.column_ne_next⟩]
  simp only [Finset.mem_singleton]
  tauto

/-- An initial-side pentagon whose rectangle is the single column `b` covers the squares of
column `a` strictly between its turn row and its top, and those of column `b` from its bottom up
to its turn row. -/
private theorem mem_coveredSquares_of_right_eq {u v : GridState n} {s : Fin n}
    (P : GridInitialPentagonBetween a s u v) (hP : P.right = finRotate n b)
    (p : Fin n × Fin n) :
    p ∈ P.coveredSquares ↔
      p.1 = a ∧ p.2 ∈ Grid.cIoo s P.top ∨ p.1 = b ∧ p.2 ∈ Grid.cIco P.bottom s := by
  rw [P.mem_coveredSquares, hP, Grid.cIco_eq_singleton_iff.mpr
    ⟨rfl, rfl, (finRotate n).injective.ne C.column_ne_next⟩]
  simp only [Finset.mem_singleton]
  tauto

/-- A returning pair of thin pentagons, the second read in `G` by exchanging the columns `a` and
`b`, covers exactly the annulus squares. -/
private theorem pentagonPair_squares {S₁ S₂ : Finset (Fin n × Fin n)} {B T : Fin n}
    (h₁ : ∀ p, p ∈ S₁ ↔
      p.1 = a ∧ p.2 ∈ Grid.cIoo C.turnRow T ∨ p.1 = b ∧ p.2 ∈ Grid.cIco B C.turnRow)
    (h₂ : ∀ p, p ∈ S₂ ↔ p.1 = a ∧ p.2 ∈ Grid.cIoo t B ∨ p.1 = b ∧ p.2 ∈ Grid.cIco T t)
    (hs : C.turnRow ∈ Grid.cIco B T) (ht : t ∈ Grid.cIco T B) (p : Fin n × Fin n) :
    (p ∈ S₁ ∨ p ∈ S₂.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
        p ∈ crossingChangeAnnulusSquares C t) ∧
      ¬(p ∈ S₁ ∧ p ∈ S₂.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) := by
  obtain ⟨c, ρ⟩ := p
  rw [Finset.mem_map_equiv, h₁, h₂, mem_crossingChangeAnnulusSquares]
  simp only [Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm, Equiv.prodCongr_apply,
    Prod.map, Equiv.refl_apply]
  have hab := C.column_ne_next
  rcases eq_or_ne c a with rfl | hca
  · simpa only [Equiv.swap_apply_left, hab, hab.symm, true_and, false_and, or_false, false_or]
      using rows_of_pentagon hs ht
  rcases eq_or_ne c b with rfl | hcb
  · have h := rows_of_pentagon ht hs (ρ := ρ)
    simp only [Equiv.swap_apply_right, hca, hab, true_and, false_and, or_false, false_or]
    exact ⟨by rw [or_comm]; exact h.1, by rw [and_comm]; exact h.2⟩
  · simp only [Equiv.swap_apply_of_ne_of_ne hca hcb, hca, hcb, false_and, or_self, iff_self,
      not_false_eq_true, and_self]

/-- The weight of a pentagon of the exchanged diagram, read in `G` by exchanging the columns `a`
and `b`. -/
private theorem pentagonWeight_withTurnRow {u v : GridState n}
    (Q : GridPentagonBetween a t u v) :
    (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q =
      ∏ c ∈ G.OColumnsOfSquares
        (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding),
        MvPolynomial.X c := by
  rw [pentagonWeight_eq_prod_coveredSquares, ← G.prod_ite_OSet_eq_prod_OColumnsOfSquares,
    Finset.prod_map]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp

/-- The weight of an initial-side pentagon of the exchanged diagram, read in `G` by exchanging the
columns `a` and `b`. -/
private theorem initialPentagonWeight_withTurnRow {u v : GridState n}
    (Q : GridInitialPentagonBetween a t u v) :
    (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q =
      ∏ c ∈ G.OColumnsOfSquares
        (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding),
        MvPolynomial.X c := by
  rw [initialPentagonWeight_eq_prod_coveredSquares, ← G.prod_ite_OSet_eq_prod_OColumnsOfSquares,
    Finset.prod_map]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp

/-- Two empty returning terminal-side pentagons, the first turning in the turn row of `C` and the
second in row `t`, cover exactly the annulus squares. -/
private theorem pentagon_squares {u v : GridState n} (P : GridPentagonBetween a C.turnRow u v)
    (Q : GridPentagonBetween a t v u) (h : P.IsEmpty ∧ Q.IsEmpty) (p : Fin n × Fin n) :
    (p ∈ P.coveredSquares ∨
        p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
        p ∈ crossingChangeAnnulusSquares C t) ∧
      ¬(p ∈ P.coveredSquares ∧ p ∈
        Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) := by
  have hP := (P.isEmpty_and_isEmpty_iff Q).mp h
  have hQ : Q.left = P.left := by
    rcases P.toGridRectangleBetween.left_right_eq_cases Q.toGridRectangleBetween with h | h
    · exact h.1
    · exact absurd (h.2.symm.trans Q.right_eq) P.left_ne
  have hb := P.toGridRectangleBetween.bottom_eq_top_of_left_eq_left Q.toGridRectangleBetween hQ
  have ht := P.toGridRectangleBetween.top_eq_bottom_of_left_eq_left Q.toGridRectangleBetween hQ
  refine pentagonPair_squares (mem_coveredSquares_of_left_eq P hP)
    (by simpa only [hb, ht] using mem_coveredSquares_of_left_eq Q (hQ.trans hP))
    P.turn_mem_cIco_bottom_top (by simpa only [hb, ht] using Q.turn_mem_cIco_bottom_top) p

/-- Two empty returning initial-side pentagons, the first turning in the turn row of `C` and the
second in row `t`, cover exactly the annulus squares. -/
private theorem initialPentagon_squares {u v : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow u v) (Q : GridInitialPentagonBetween a t v u)
    (h : P.IsEmpty ∧ Q.IsEmpty) (p : Fin n × Fin n) :
    (p ∈ P.coveredSquares ∨
        p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
        p ∈ crossingChangeAnnulusSquares C t) ∧
      ¬(p ∈ P.coveredSquares ∧ p ∈
        Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding) := by
  have hP := (P.isEmpty_and_isEmpty_iff Q).mp h
  have hQ : Q.left = P.left := Q.left_eq.trans P.left_eq.symm
  have hQr : Q.right = P.right :=
    P.toGridRectangleBetween.right_eq_right_of_left_eq_left Q.toGridRectangleBetween hQ
  have hb := P.toGridRectangleBetween.bottom_eq_top_of_left_eq_left Q.toGridRectangleBetween hQ
  have ht := P.toGridRectangleBetween.top_eq_bottom_of_left_eq_left Q.toGridRectangleBetween hQ
  refine pentagonPair_squares (mem_coveredSquares_of_right_eq P hP)
    (by simpa only [hb, ht] using mem_coveredSquares_of_right_eq Q (hQr.trans hP))
    P.turn_mem_cIco_bottom_top (by simpa only [hb, ht] using Q.turn_mem_cIco_bottom_top) p


/-! ### Counted returning domains -/

variable (G C t)

/-- A returning terminal-side hexagon--rectangle pair is counted exactly when both domains are
empty, provided the annulus squares carry no `X`-marking. -/
theorem mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {u v : GridState n}
    (P : GridHexagonBetween a t C.turnRow u v) (r : GridRectangleBetween v u) :
    P ∈ G.crossingChangeHexagons C t u v ∧ r ∈ G.unblockedRectangles v u ↔
      P.IsEmpty ∧ r.IsEmpty := by
  rw [mem_crossingChangeHexagons, mem_unblockedRectangles]
  refine ⟨fun h => ⟨h.1.1, h.2.1⟩, fun h => ?_⟩
  obtain ⟨hP, hr⟩ := disjoint_XSet_of_forall (hexagon_squares P r h) hX
  exact ⟨⟨h.1, hP⟩, ⟨h.2, hr⟩⟩

/-- A returning initial-side hexagon--rectangle pair is counted exactly when both domains are
empty, provided the annulus squares carry no `X`-marking. -/
theorem mem_crossingChangeInitialHexagons_and_mem_unblockedRectangles_iff
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {u v : GridState n}
    (P : GridInitialHexagonBetween a C.turnRow t u v) (r : GridRectangleBetween v u) :
    P ∈ G.crossingChangeInitialHexagons C t u v ∧ r ∈ G.unblockedRectangles v u ↔
      P.IsEmpty ∧ r.IsEmpty := by
  rw [mem_crossingChangeInitialHexagons, mem_unblockedRectangles]
  refine ⟨fun h => ⟨h.1.1, h.2.1⟩, fun h => ?_⟩
  obtain ⟨hP, hr⟩ := disjoint_XSet_of_forall (initialHexagon_squares P r h) hX
  exact ⟨⟨h.1, hP⟩, ⟨h.2, hr⟩⟩

/-- An empty returning terminal-side hexagon--rectangle pair has the annulus weight. -/
theorem crossingChangeHexagonWeight_mul_OMonomial_eq_crossingChangeAnnulusWeight
    {u v : GridState n}
    (P : GridHexagonBetween a t C.turnRow u v) (r : GridRectangleBetween v u)
    (h : P.IsEmpty ∧ r.IsEmpty) :
    G.crossingChangeHexagonWeight R P * G.OMonomial R r.toGridRectangle =
      G.crossingChangeAnnulusWeight R C t := by
  rw [crossingChangeHexagonWeight_eq_monomial, monomial_sum_one, OMonomial_eq_prod_coveredSquares,
    prod_ite_OSet_eq_prod_OColumnsOfSquares]
  simp only [← X_pow_eq_monomial, pow_one]
  exact prod_OColumnsOfSquares_mul_prod_eq R (hexagon_squares P r h)

/-- An empty returning initial-side hexagon--rectangle pair has the annulus weight. -/
theorem crossingChangeInitialHexagonWeight_mul_OMonomial_eq_crossingChangeAnnulusWeight
    {u v : GridState n}
    (P : GridInitialHexagonBetween a C.turnRow t u v) (r : GridRectangleBetween v u)
    (h : P.IsEmpty ∧ r.IsEmpty) :
    G.crossingChangeInitialHexagonWeight R P * G.OMonomial R r.toGridRectangle =
      G.crossingChangeAnnulusWeight R C t := by
  rw [crossingChangeInitialHexagonWeight_eq_monomial, monomial_sum_one,
    OMonomial_eq_prod_coveredSquares, prod_ite_OSet_eq_prod_OColumnsOfSquares]
  simp only [← X_pow_eq_monomial, pow_one]
  exact prod_OColumnsOfSquares_mul_prod_eq R (initialHexagon_squares P r h)

/-- A returning pair of terminal-side pentagons, of `G` turning in the turn row of `C` and of the
exchanged diagram turning in row `t`, is counted exactly when both are empty, provided the annulus
squares carry no `X`-marking. -/
theorem mem_pentagons_and_mem_pentagons_withTurnRow_iff
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {u v : GridState n}
    (P : GridPentagonBetween a C.turnRow u v) (Q : GridPentagonBetween a t v u) :
    P ∈ G.pentagons C u v ∧ Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) v u ↔
      P.IsEmpty ∧ Q.IsEmpty := by
  rw [mem_pentagons, mem_pentagons, ← disjoint_map_swapColumns_XSet_iff]
  refine ⟨fun h => ⟨h.1.1, h.2.1⟩, fun h => ?_⟩
  obtain ⟨hP, hQ⟩ := disjoint_XSet_of_forall (pentagon_squares P Q h) hX
  exact ⟨⟨h.1, hP⟩, ⟨h.2, hQ⟩⟩

/-- A returning pair of initial-side pentagons, of `G` turning in the turn row of `C` and of the
exchanged diagram turning in row `t`, is counted exactly when both are empty, provided the annulus
squares carry no `X`-marking. -/
theorem mem_initialPentagons_and_mem_initialPentagons_withTurnRow_iff
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {u v : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow u v) (Q : GridInitialPentagonBetween a t v u) :
    P ∈ G.initialPentagons C u v ∧
        Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) v u ↔
      P.IsEmpty ∧ Q.IsEmpty := by
  rw [mem_initialPentagons, mem_initialPentagons, ← disjoint_map_swapColumns_XSet_iff]
  refine ⟨fun h => ⟨h.1.1, h.2.1⟩, fun h => ?_⟩
  obtain ⟨hP, hQ⟩ := disjoint_XSet_of_forall (initialPentagon_squares P Q h) hX
  exact ⟨⟨h.1, hP⟩, ⟨h.2, hQ⟩⟩

/-- An empty returning pair of terminal-side pentagons, of `G` turning in the turn row of `C` and
of the exchanged diagram turning in row `t`, has the annulus weight, the weight of the first
pentagon being renamed into the variables of `G`. -/
theorem rename_pentagonWeight_mul_pentagonWeight_eq_crossingChangeAnnulusWeight
    {u v : GridState n} (P : GridPentagonBetween a C.turnRow u v)
    (Q : GridPentagonBetween a t v u) (h : P.IsEmpty ∧ Q.IsEmpty) :
    rename (Equiv.swap a b) (G.pentagonWeight R C P) *
        (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q =
      G.crossingChangeAnnulusWeight R C t := by
  rw [rename_pentagonWeight, prod_ite_OSet_eq_prod_OColumnsOfSquares, pentagonWeight_withTurnRow]
  exact prod_OColumnsOfSquares_mul_prod_eq R (pentagon_squares P Q h)

/-- An empty returning pair of initial-side pentagons, of `G` turning in the turn row of `C` and
of the exchanged diagram turning in row `t`, has the annulus weight, the weight of the first
pentagon being renamed into the variables of `G`. -/
theorem rename_initialPentagonWeight_mul_initialPentagonWeight_eq_crossingChangeAnnulusWeight
    {u v : GridState n} (P : GridInitialPentagonBetween a C.turnRow u v)
    (Q : GridInitialPentagonBetween a t v u) (h : P.IsEmpty ∧ Q.IsEmpty) :
    rename (Equiv.swap a b) (G.initialPentagonWeight R C P) *
        (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q =
      G.crossingChangeAnnulusWeight R C t := by
  rw [rename_initialPentagonWeight, prod_ite_OSet_eq_prod_OColumnsOfSquares,
    initialPentagonWeight_withTurnRow]
  exact prod_OColumnsOfSquares_mul_prod_eq R (initialPentagon_squares P Q h)

/-! ### Interleaving columns -/

variable {G C t}

/-- The rows of interleaving markings in the order `O_b, O_a, X_b, X_a`. -/
private theorem rows_of_mem_columnArc (h : G.ColumnsInterleaving a b)
    (hO : G.O a ∈ G.columnArc b) :
    G.O a ∈ Grid.cIoo (G.O b) (G.X b) ∧ G.X a ∈ Grid.cIoo (G.X b) (G.O b) := by
  refine ⟨hO, ?_⟩
  rcases (columnsInterleaving_iff G _ _).mp h with ⟨-, h₂⟩ | ⟨h₁, -⟩
  · exact h₂
  · exact absurd h₁ (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hO)

/-- The rows of interleaving markings in the order `O_b, X_a, X_b, O_a`. -/
private theorem rows_of_notMem_columnArc (h : G.ColumnsInterleaving a b)
    (hO : G.O a ∉ G.columnArc b) :
    G.O a ∈ Grid.cIoo (G.X b) (G.O b) ∧ G.X a ∈ Grid.cIoo (G.O b) (G.X b) := by
  rcases (columnsInterleaving_iff G _ _).mp h with ⟨h₁, -⟩ | h'
  · exact absurd h₁ hO
  · exact h'

/-- For interleaving columns with markings in the order `O_b, O_a, X_b, X_a` going up, and the
rows `s` of `O_a` and `t` of `X_b`, the annulus squares carry no `X`-marking. -/
theorem disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (ht : t = G.X b) : Disjoint (crossingChangeAnnulusSquares C t) G.XSet := by
  obtain ⟨hOa, hXa⟩ := rows_of_mem_columnArc h hO
  rw [Finset.disjoint_left]
  rintro ⟨c, ρ⟩ hp hX
  rw [mem_crossingChangeAnnulusSquares, hs, ht] at hp
  rw [mk_mem_XSet] at hX
  rcases hp with ⟨rfl, hρ⟩ | ⟨rfl, hρ⟩
  · rw [← hX] at hρ
    simp only [Grid.mem_cIoo, Fin.ext_iff, ne_eq] at hOa hXa hρ
    split_ifs at hOa hXa hρ <;> omega
  · exact Grid.left_notMem_cIoo _ _ (hX ▸ hρ)

/-- For interleaving columns with markings in the order `O_b, O_a, X_b, X_a` going up, and the
rows `s` of `O_a` and `t` of `X_b`, the annulus weight is the variable of column `b`: the
annulus squares carry the `O`-marking of column `b` and no other. -/
theorem crossingChangeAnnulusWeight_eq_X_next_of_mem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (ht : t = G.X b) : G.crossingChangeAnnulusWeight R C t = MvPolynomial.X b := by
  obtain ⟨hOa, hXa⟩ := rows_of_mem_columnArc h hO
  rw [crossingChangeAnnulusWeight_def, ← Finset.prod_singleton (MvPolynomial.X (R := R)) b]
  congr 1
  ext c
  rw [mem_OColumnsOfSquares, mem_crossingChangeAnnulusSquares, hs, ht, Finset.mem_singleton]
  rcases eq_or_ne c a with rfl | hca
  · simp only [Grid.left_notMem_cIoo, and_false, false_or, C.column_ne_next, false_and]
  rcases eq_or_ne c b with rfl | hcb
  · simp only [hca, false_and, true_and, false_or, iff_true]
    simp only [Grid.mem_cIoo, Fin.ext_iff, ne_eq] at hOa hXa ⊢
    split_ifs at hOa hXa ⊢ <;> omega
  · simp only [hca, hcb, false_and, or_self]

/-- For interleaving columns with markings in the order `O_b, X_a, X_b, O_a` going up, and the
rows `s` of `X_a` and `t` of `O_b`, the annulus squares carry no `X`-marking. -/
theorem disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a)
    (ht : t = G.O b) : Disjoint (crossingChangeAnnulusSquares C t) G.XSet := by
  obtain ⟨hOa, hXa⟩ := rows_of_notMem_columnArc h hO
  rw [Finset.disjoint_left]
  rintro ⟨c, ρ⟩ hp hX
  rw [mem_crossingChangeAnnulusSquares, hs, ht] at hp
  rw [mk_mem_XSet] at hX
  rcases hp with ⟨rfl, hρ⟩ | ⟨rfl, hρ⟩
  · exact Grid.left_notMem_cIoo _ _ (hX ▸ hρ)
  · rw [← hX] at hρ
    simp only [Grid.mem_cIoo, Fin.ext_iff, ne_eq] at hOa hXa hρ
    split_ifs at hOa hXa hρ <;> omega

/-- For interleaving columns with markings in the order `O_b, X_a, X_b, O_a` going up, and the
rows `s` of `X_a` and `t` of `O_b`, the annulus weight is the variable of column `a`: the annulus
squares carry the `O`-marking of column `a` and no other. -/
theorem crossingChangeAnnulusWeight_eq_X_column_of_notMem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a)
    (ht : t = G.O b) : G.crossingChangeAnnulusWeight R C t = MvPolynomial.X a := by
  obtain ⟨hOa, hXa⟩ := rows_of_notMem_columnArc h hO
  rw [crossingChangeAnnulusWeight_def, ← Finset.prod_singleton (MvPolynomial.X (R := R)) a]
  congr 1
  ext c
  rw [mem_OColumnsOfSquares, mem_crossingChangeAnnulusSquares, hs, ht, Finset.mem_singleton]
  rcases eq_or_ne c a with rfl | hca
  · simp only [true_and, C.column_ne_next, false_and, or_false, iff_true]
    simp only [Grid.mem_cIoo, Fin.ext_iff, ne_eq] at hOa hXa ⊢
    split_ifs at hOa hXa ⊢ <;> omega
  rcases eq_or_ne c b with rfl | hcb
  · simp only [hca, false_and, true_and, false_or, Grid.left_notMem_cIoo]
  · simp only [hca, hcb, false_and, or_self]

end GridDiagram

end TauCeti
