/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Annulus
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Annulus
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.PentagonPair

/-!
# The diagonal of the crossing change homotopy equation

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t ≠ s` be a second row. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map
of `C`, where `G' = G.swapColumns a b`, `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` at
`C.withTurnRow t`, and `H : GC⁻(G) → GC⁻(G)` for the crossing change homotopy
`GridDiagram.crossingChangeHomotopy` with corners in the rows `s` and `t`. For interleaving
columns, with `s` and `t` the rows of the turn points of the crossing change maps, the homotopy
equation of Ozsváth--Stipsicz--Szabó, Section 6.1, reads `∂H + H∂ = V + ΨΦ` over `𝔽₂`, for the
variable `V` of one of the two columns. This file proves the diagonal part of that equation: the
coefficients from a grid state `x` to itself.

The domains contributing to these coefficients are the returning domains of
`TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Annulus`, thin vertical annuli in column `a` or
column `b`, all with the annulus weight `GridDiagram.crossingChangeAnnulusWeight` once the annulus
squares carry no `X`-marking. Whether each annulus exists is decided by the cyclic order of `s`,
`t` and the rows of `x` in the columns `a`, `b` and `finRotate n b`, exactly as for the
commutation homotopy (`GridDiagram.unblockedDifferential_commutationHomotopy_add_single_apply_self`
and `GridDiagram.reverse_commutationMap_commutationMap_single_apply_self`). Of the six possible
annuli, an odd number among the four hexagon annuli exist exactly when an even number among the
two pentagon annuli do, which gives the diagonal identity in characteristic two.

## Main results

* `TauCeti.GridDiagram.sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient_self` and
  `TauCeti.GridDiagram.sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient_self`: the
  diagonal coefficients of `∂H` and `H∂`.
* `TauCeti.GridDiagram.commutationMap_withTurnRow_commutationMap_single_apply_self`: the diagonal
  coefficient of `ΨΦ`.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_single_apply_self`: the
  diagonal coefficient of `∂H + H∂` is the annulus weight plus that of `ΨΦ`, in characteristic
  two.
* `unblockedDifferential_crossingChangeHomotopy_add_single_apply_self_of_mem_columnArc` and
  `unblockedDifferential_crossingChangeHomotopy_add_single_apply_self_of_notMem_columnArc`, in the
  namespace `TauCeti.GridDiagram`: for the crossing change maps of interleaving columns, the
  diagonal coefficient of `∂H + H∂` is `V_b`, respectively `V_a`, plus that of `ΨΦ`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 5.1 and 6.1: the hexagon homotopies of commutation and of a
  crossing change.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  homotopy equations for the hexagons with corners at the two turn points.
-/

public section

namespace TauCeti

namespace GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R] (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Matrix coefficients of the two sides -/

/-- On a grid-state generator, the coefficient of the unblocked differential after the crossing
change homotopy is the sum over intermediate states of the hexagon coefficient times the
rectangle coefficient. -/
theorem unblockedDifferential_crossingChangeHomotopy_single_apply (x z : GridState n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t (Finsupp.single x 1)) z =
      ∑ y : GridState n,
        G.crossingChangeHexagonCoefficient R C t x y * G.unblockedCoefficient R y z := by
  rw [unblockedDifferential_apply_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp_rw [crossingChangeHomotopy_single_apply]

/-- On a grid-state generator, the coefficient of the crossing change homotopy after the unblocked
differential is the sum over intermediate states of the rectangle coefficient times the hexagon
coefficient. -/
theorem crossingChangeHomotopy_unblockedDifferential_single_apply (x z : GridState n) :
    G.crossingChangeHomotopy R C t (G.unblockedDifferential R (Finsupp.single x 1)) z =
      ∑ y : GridState n,
        G.unblockedCoefficient R x y * G.crossingChangeHexagonCoefficient R C t y z := by
  rw [crossingChangeHomotopy_apply_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp

/-! ### Counting returning domains -/

/-- A diagonal coefficient counting two-step domains which all have the weight `w`, and of which
there is at most one, exactly when `p` holds. -/
private theorem sum_mul_sum_eq_ite {A B : GridState n → GridState n → Type*}
    (F₁ : ∀ u v, Finset (A u v)) (F₂ : ∀ u v, Finset (B u v)) (x : GridState n)
    (f : ∀ y, A x y → MvPolynomial (Fin n) R) (g : ∀ y, B y x → MvPolynomial (Fin n) R)
    (w : MvPolynomial (Fin n) R) (p : Prop) [Decidable p]
    (hw : ∀ D ∈ GridTwoStepDecomposition.decompositionsOf F₁ F₂ x x,
      f D.middle D.first * g D.middle D.second = w)
    (huniq : ∀ D ∈ GridTwoStepDecomposition.decompositionsOf F₁ F₂ x x,
      ∀ E ∈ GridTwoStepDecomposition.decompositionsOf F₁ F₂ x x, D = E)
    (hex : (GridTwoStepDecomposition.decompositionsOf F₁ F₂ x x).Nonempty ↔ p) :
    ∑ y, (∑ P ∈ F₁ x y, f y P) * ∑ Q ∈ F₂ y x, g y Q = if p then w else 0 := by
  simp_rw [Finset.sum_mul_sum]
  rw [← GridTwoStepDecomposition.sum_decompositionsOf F₁ F₂ (fun y P Q => f y P * g y Q),
    Finset.sum_congr rfl hw, Finset.sum_const]
  split_ifs with hp
  · obtain ⟨D, hD⟩ := hex.mpr hp
    rw [Finset.card_eq_one.mpr ⟨D, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hD, fun E hE => huniq E hE D hD⟩⟩, one_smul]
  · rw [Finset.not_nonempty_iff_eq_empty.mp (mt hex.mp hp), Finset.card_empty, zero_smul]

/-! ### Hexagon--rectangle annuli -/

/-- The returning terminal-side hexagon followed by a rectangle: it lies in column `a`, and exists
exactly when `t` and `s` occur in this order going up from the row of `x` in column `a` to its row
in column `b`. -/
private theorem sum_hexagonWeight_mul_unblockedCoefficient_self
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (x : GridState n) :
    ∑ y, (∑ P ∈ G.crossingChangeHexagons C t x y, G.crossingChangeHexagonWeight R P) *
        ∑ r ∈ G.unblockedRectangles y x, G.OMonomial R r.toGridRectangle =
      if t ∈ Grid.cIco (x a) (x b) ∧ C.turnRow ∈ Grid.cIoo t (x b) then
        G.crossingChangeAnnulusWeight R C t else 0 := by
  refine sum_mul_sum_eq_ite R _ _ x _ _ _ _ (fun D hD => ?_) (fun D hD E hE => ?_) ?_
  · rw [GridTwoStepDecomposition.mem_decompositionsOf] at hD
    exact G.crossingChangeHexagonWeight_mul_OMonomial_eq_crossingChangeAnnulusWeight R C t
      D.first D.second
      ((G.mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff C t hX _ _).mp hD)
  · obtain ⟨m, P, r⟩ := D
    obtain ⟨m', Q, r'⟩ := E
    rw [GridTwoStepDecomposition.mem_decompositionsOf,
      G.mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff C t hX] at hD hE
    cases P.sigma_target_eq_of_isEmpty_and_isEmpty r Q r' hD hE
    rfl
  · rw [← GridHexagonBetween.exists_target_isEmpty_and_isEmpty_iff C.column_ne_next]
    constructor
    · rintro ⟨⟨m, P, r⟩, hD⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf,
        G.mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff C t hX] at hD
      exact ⟨m, P, r, hD⟩
    · rintro ⟨m, P, r, h⟩
      refine ⟨⟨m, P, r⟩, ?_⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf,
        G.mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff C t hX]
      exact h

/-- The returning initial-side hexagon followed by a rectangle: it lies in column `b`, and exists
exactly when `s` and `t` occur in this order going up from the row of `x` in column `b` to its row
in the next column. -/
private theorem sum_initialHexagonWeight_mul_unblockedCoefficient_self
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (x : GridState n) :
    ∑ y, (∑ P ∈ G.crossingChangeInitialHexagons C t x y,
        G.crossingChangeInitialHexagonWeight R P) *
        ∑ r ∈ G.unblockedRectangles y x, G.OMonomial R r.toGridRectangle =
      if C.turnRow ∈ Grid.cIco (x b) (x (finRotate n b)) ∧
          t ∈ Grid.cIoo C.turnRow (x (finRotate n b)) then
        G.crossingChangeAnnulusWeight R C t else 0 := by
  refine sum_mul_sum_eq_ite R _ _ x _ _ _ _ (fun D hD => ?_) (fun D hD E hE => ?_) ?_
  · rw [GridTwoStepDecomposition.mem_decompositionsOf] at hD
    exact G.crossingChangeInitialHexagonWeight_mul_OMonomial_eq_crossingChangeAnnulusWeight R C t
      D.first D.second
      ((G.mem_crossingChangeInitialHexagons_and_mem_unblockedRectangles_iff C t hX _ _).mp hD)
  · obtain ⟨m, P, r⟩ := D
    obtain ⟨m', Q, r'⟩ := E
    rw [GridTwoStepDecomposition.mem_decompositionsOf,
      G.mem_crossingChangeInitialHexagons_and_mem_unblockedRectangles_iff C t hX] at hD hE
    cases P.sigma_target_eq_of_isEmpty_and_isEmpty r Q r' hD hE
    rfl
  · rw [← GridInitialHexagonBetween.exists_target_isEmpty_and_isEmpty_iff C.column_ne_next]
    constructor
    · rintro ⟨⟨m, P, r⟩, hD⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf,
        G.mem_crossingChangeInitialHexagons_and_mem_unblockedRectangles_iff C t hX] at hD
      exact ⟨m, P, r, hD⟩
    · rintro ⟨m, P, r, h⟩
      refine ⟨⟨m, P, r⟩, ?_⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf,
        G.mem_crossingChangeInitialHexagons_and_mem_unblockedRectangles_iff C t hX]
      exact h

/-- The returning rectangle followed by a terminal-side hexagon: it lies in column `a`, and exists
exactly when `t` and `s` occur in this order going up from the row of `x` in column `b` to its row
in column `a`. -/
private theorem sum_OMonomial_mul_hexagonWeight_self
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (x : GridState n) :
    ∑ y, (∑ r ∈ G.unblockedRectangles x y, G.OMonomial R r.toGridRectangle) *
        ∑ P ∈ G.crossingChangeHexagons C t y x, G.crossingChangeHexagonWeight R P =
      if t ∈ Grid.cIco (x b) (x a) ∧ C.turnRow ∈ Grid.cIoo t (x a) then
        G.crossingChangeAnnulusWeight R C t else 0 := by
  refine sum_mul_sum_eq_ite R _ _ x _ _ _ _ (fun D hD => ?_) (fun D hD E hE => ?_) ?_
  · rw [GridTwoStepDecomposition.mem_decompositionsOf, and_comm] at hD
    rw [mul_comm]
    exact G.crossingChangeHexagonWeight_mul_OMonomial_eq_crossingChangeAnnulusWeight R C t
      D.second D.first
      ((G.mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff C t hX _ _).mp hD)
  · obtain ⟨m, r, P⟩ := D
    obtain ⟨m', r', Q⟩ := E
    rw [GridTwoStepDecomposition.mem_decompositionsOf, and_comm,
      G.mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff C t hX] at hD hE
    cases P.sigma_source_eq_of_isEmpty_and_isEmpty r Q r' hD hE
    rfl
  · rw [← GridHexagonBetween.exists_source_isEmpty_and_isEmpty_iff C.column_ne_next]
    constructor
    · rintro ⟨⟨m, r, P⟩, hD⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf, and_comm,
        G.mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff C t hX] at hD
      exact ⟨m, r, P, hD⟩
    · rintro ⟨m, r, P, h⟩
      refine ⟨⟨m, r, P⟩, ?_⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf, and_comm,
        G.mem_crossingChangeHexagons_and_mem_unblockedRectangles_iff C t hX]
      exact h

/-- The returning rectangle followed by an initial-side hexagon: it lies in column `b`, and exists
exactly when `s` and `t` occur in this order going up from the row of `x` in the column after `b`
to its row in column `b`. -/
private theorem sum_OMonomial_mul_initialHexagonWeight_self
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (x : GridState n) :
    ∑ y, (∑ r ∈ G.unblockedRectangles x y, G.OMonomial R r.toGridRectangle) *
        ∑ P ∈ G.crossingChangeInitialHexagons C t y x, G.crossingChangeInitialHexagonWeight R P =
      if C.turnRow ∈ Grid.cIco (x (finRotate n b)) (x b) ∧ t ∈ Grid.cIoo C.turnRow (x b) then
        G.crossingChangeAnnulusWeight R C t else 0 := by
  refine sum_mul_sum_eq_ite R _ _ x _ _ _ _ (fun D hD => ?_) (fun D hD E hE => ?_) ?_
  · rw [GridTwoStepDecomposition.mem_decompositionsOf, and_comm] at hD
    rw [mul_comm]
    exact G.crossingChangeInitialHexagonWeight_mul_OMonomial_eq_crossingChangeAnnulusWeight R C t
      D.second D.first
      ((G.mem_crossingChangeInitialHexagons_and_mem_unblockedRectangles_iff C t hX _ _).mp hD)
  · obtain ⟨m, r, P⟩ := D
    obtain ⟨m', r', Q⟩ := E
    rw [GridTwoStepDecomposition.mem_decompositionsOf, and_comm,
      G.mem_crossingChangeInitialHexagons_and_mem_unblockedRectangles_iff C t hX] at hD hE
    cases P.sigma_source_eq_of_isEmpty_and_isEmpty r Q r' hD hE
    rfl
  · rw [← GridInitialHexagonBetween.exists_source_isEmpty_and_isEmpty_iff C.column_ne_next]
    constructor
    · rintro ⟨⟨m, r, P⟩, hD⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf, and_comm,
        G.mem_crossingChangeInitialHexagons_and_mem_unblockedRectangles_iff C t hX] at hD
      exact ⟨m, r, P, hD⟩
    · rintro ⟨m, r, P, h⟩
      refine ⟨⟨m, r, P⟩, ?_⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf, and_comm,
        G.mem_crossingChangeInitialHexagons_and_mem_unblockedRectangles_iff C t hX]
      exact h

/-- **The diagonal of `∂H`.** If the annulus squares carry no `X`-marking, the coefficient of
`∂ ∘ H` from a grid state `x` to itself counts the returning hexagon--rectangle annuli: one in
column `a` when `t` and the turn row `s` occur in this order going up from the row of `x` in
column `a` to its row in column `b`, and one in column `b` when `s` and `t` occur in this order
going up from the row of `x` in column `b` to its row in the next column. Each has the annulus
weight. -/
theorem sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient_self
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (x : GridState n) :
    ∑ y, G.crossingChangeHexagonCoefficient R C t x y * G.unblockedCoefficient R y x =
      (if t ∈ Grid.cIco (x a) (x b) ∧ C.turnRow ∈ Grid.cIoo t (x b) then
          G.crossingChangeAnnulusWeight R C t else 0) +
        if C.turnRow ∈ Grid.cIco (x b) (x (finRotate n b)) ∧
            t ∈ Grid.cIoo C.turnRow (x (finRotate n b)) then
          G.crossingChangeAnnulusWeight R C t else 0 := by
  simp_rw [crossingChangeHexagonCoefficient_def, unblockedCoefficient_def, add_mul,
    Finset.sum_add_distrib]
  rw [sum_hexagonWeight_mul_unblockedCoefficient_self G R C t hX x,
    sum_initialHexagonWeight_mul_unblockedCoefficient_self G R C t hX x]

/-- **The diagonal of `H∂`.** If the annulus squares carry no `X`-marking, the coefficient of
`H ∘ ∂` from a grid state `x` to itself counts the returning rectangle--hexagon annuli: one in
column `a` when `t` and the turn row `s` occur in this order going up from the row of `x` in
column `b` to its row in column `a`, and one in column `b` when `s` and `t` occur in this order
going up from the row of `x` in the column after `b` to its row in column `b`. Each has the
annulus weight. -/
theorem sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient_self
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (x : GridState n) :
    ∑ y, G.unblockedCoefficient R x y * G.crossingChangeHexagonCoefficient R C t y x =
      (if t ∈ Grid.cIco (x b) (x a) ∧ C.turnRow ∈ Grid.cIoo t (x a) then
          G.crossingChangeAnnulusWeight R C t else 0) +
        if C.turnRow ∈ Grid.cIco (x (finRotate n b)) (x b) ∧ t ∈ Grid.cIoo C.turnRow (x b) then
          G.crossingChangeAnnulusWeight R C t else 0 := by
  simp_rw [crossingChangeHexagonCoefficient_def, unblockedCoefficient_def, mul_add,
    Finset.sum_add_distrib]
  rw [sum_OMonomial_mul_hexagonWeight_self G R C t hX x,
    sum_OMonomial_mul_initialHexagonWeight_self G R C t hX x]

/-! ### Pentagon pairs -/

/-- The returning pair of terminal-side pentagons: it lies in column `a`, and exists exactly when
the turn row `s` lies between the rows of `x` in the columns `a` and `b`, and `t` between those in
the columns `b` and `a`. -/
private theorem sum_pentagonWeight_mul_pentagonWeight_self
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (x : GridState n) :
    ∑ y, (∑ P ∈ G.pentagons C x y, rename (Equiv.swap a b) (G.pentagonWeight R C P)) *
        ∑ Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y x,
          (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q =
      if C.turnRow ∈ Grid.cIco (x a) (x b) ∧ t ∈ Grid.cIco (x b) (x a) then
        G.crossingChangeAnnulusWeight R C t else 0 := by
  refine sum_mul_sum_eq_ite R _ _ x _ _ _ _ (fun D hD => ?_) (fun D hD E hE => ?_) ?_
  · rw [GridTwoStepDecomposition.mem_decompositionsOf,
      G.mem_pentagons_and_mem_pentagons_withTurnRow_iff C t hX] at hD
    exact G.rename_pentagonWeight_mul_pentagonWeight_eq_crossingChangeAnnulusWeight R C t
      D.first D.second hD
  · obtain ⟨m, P, Q⟩ := D
    obtain ⟨m', P', Q'⟩ := E
    rw [GridTwoStepDecomposition.mem_decompositionsOf,
      G.mem_pentagons_and_mem_pentagons_withTurnRow_iff C t hX] at hD hE
    cases P.sigma_eq_of_left_eq Q P' Q' ((P.isEmpty_and_isEmpty_iff Q).mp hD)
      ((P'.isEmpty_and_isEmpty_iff Q').mp hE)
    rfl
  · rw [← GridPentagonBetween.exists_left_eq_iff C.column_ne_next rfl]
    constructor
    · rintro ⟨⟨m, P, Q⟩, hD⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf,
        G.mem_pentagons_and_mem_pentagons_withTurnRow_iff C t hX] at hD
      exact ⟨m, P, Q, (P.isEmpty_and_isEmpty_iff Q).mp hD⟩
    · rintro ⟨m, P, Q, hP⟩
      refine ⟨⟨m, P, Q⟩, ?_⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf,
        G.mem_pentagons_and_mem_pentagons_withTurnRow_iff C t hX]
      exact (P.isEmpty_and_isEmpty_iff Q).mpr hP

/-- The returning pair of initial-side pentagons: it lies in column `b`, and exists exactly when
the turn row `s` lies between the rows of `x` in column `b` and the next column, and `t` between
those in the next column and column `b`. -/
private theorem sum_initialPentagonWeight_mul_initialPentagonWeight_self
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (x : GridState n) :
    ∑ y, (∑ P ∈ G.initialPentagons C x y,
        rename (Equiv.swap a b) (G.initialPentagonWeight R C P)) *
        ∑ Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y x,
          (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q =
      if C.turnRow ∈ Grid.cIco (x b) (x (finRotate n b)) ∧
          t ∈ Grid.cIco (x (finRotate n b)) (x b) then
        G.crossingChangeAnnulusWeight R C t else 0 := by
  refine sum_mul_sum_eq_ite R _ _ x _ _ _ _ (fun D hD => ?_) (fun D hD E hE => ?_) ?_
  · rw [GridTwoStepDecomposition.mem_decompositionsOf,
      G.mem_initialPentagons_and_mem_initialPentagons_withTurnRow_iff C t hX] at hD
    exact G.rename_initialPentagonWeight_mul_initialPentagonWeight_eq_crossingChangeAnnulusWeight
      R C t D.first D.second hD
  · obtain ⟨m, P, Q⟩ := D
    obtain ⟨m', P', Q'⟩ := E
    rw [GridTwoStepDecomposition.mem_decompositionsOf,
      G.mem_initialPentagons_and_mem_initialPentagons_withTurnRow_iff C t hX] at hD hE
    cases P.sigma_eq_of_right_eq Q P' Q' ((P.isEmpty_and_isEmpty_iff Q).mp hD)
      ((P'.isEmpty_and_isEmpty_iff Q').mp hE)
    rfl
  · rw [← GridInitialPentagonBetween.exists_right_eq_iff C.column_ne_next rfl]
    constructor
    · rintro ⟨⟨m, P, Q⟩, hD⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf,
        G.mem_initialPentagons_and_mem_initialPentagons_withTurnRow_iff C t hX] at hD
      exact ⟨m, P, Q, (P.isEmpty_and_isEmpty_iff Q).mp hD⟩
    · rintro ⟨m, P, Q, hP⟩
      refine ⟨⟨m, P, Q⟩, ?_⟩
      rw [GridTwoStepDecomposition.mem_decompositionsOf,
        G.mem_initialPentagons_and_mem_initialPentagons_withTurnRow_iff C t hX]
      exact (P.isEmpty_and_isEmpty_iff Q).mpr hP

/-- Pentagons turning on opposite sides never return to their source when the two turn rows
differ: together they would form a thin horizontal annulus, whose single row contains both turn
points. -/
private theorem sum_pentagonWeight_mul_initialPentagonWeight_self (hst : C.turnRow ≠ t)
    (x : GridState n) :
    ∑ y, (∑ P ∈ G.pentagons C x y, rename (Equiv.swap a b) (G.pentagonWeight R C P)) *
        ∑ Q ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) y x,
          (G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t) Q = 0 := by
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun P hP => Finset.sum_eq_zero fun Q hQ => ?_
  rw [mem_pentagons] at hP
  rw [mem_initialPentagons] at hQ
  exact absurd (P.turn_eq_of_isEmpty_and_isEmpty_initial Q ⟨hP.1, hQ.1⟩) hst

/-- Pentagons turning on opposite sides never return to their source when the two turn rows
differ, in the other order. -/
private theorem sum_initialPentagonWeight_mul_pentagonWeight_self (hst : C.turnRow ≠ t)
    (x : GridState n) :
    ∑ y, (∑ P ∈ G.initialPentagons C x y,
        rename (Equiv.swap a b) (G.initialPentagonWeight R C P)) *
        ∑ Q ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) y x,
          (G.swapColumns a b).pentagonWeight R (C.withTurnRow t) Q = 0 := by
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun P hP => Finset.sum_eq_zero fun Q hQ => ?_
  rw [mem_initialPentagons] at hP
  rw [mem_pentagons] at hQ
  exact absurd (Q.turn_eq_of_isEmpty_and_isEmpty_initial P ⟨hQ.1, hP.1⟩).symm hst

/-- **The diagonal of `ΨΦ`.** If the turn rows `s` and `t` differ and the annulus squares carry no
`X`-marking, the coefficient of `Ψ ∘ Φ` from a grid state `x` to itself counts the returning
pentagon pairs: two pentagons turning on the same side, forming an annulus in column `a` when `s`
lies between the rows of `x` in the columns `a` and `b` and `t` between those in `b` and `a`, and
an annulus in column `b` under the same condition for the columns `b` and the next one. Each has
the annulus weight. -/
theorem commutationMap_withTurnRow_commutationMap_single_apply_self (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (x : GridState n) :
    (G.swapColumns a b).commutationMap R (C.withTurnRow t)
        (G.commutationMap R C (Finsupp.single x 1)) x =
      (if C.turnRow ∈ Grid.cIco (x a) (x b) ∧ t ∈ Grid.cIco (x b) (x a) then
          G.crossingChangeAnnulusWeight R C t else 0) +
        if C.turnRow ∈ Grid.cIco (x b) (x (finRotate n b)) ∧
            t ∈ Grid.cIco (x (finRotate n b)) (x b) then
          G.crossingChangeAnnulusWeight R C t else 0 := by
  rw [commutationMap_withTurnRow_commutationMap_single_apply]
  simp_rw [commutationPentagonCoefficient_def, pentagonCoefficient_def,
    initialPentagonCoefficient_def, map_add, map_sum, add_mul, mul_add, Finset.sum_add_distrib]
  rw [sum_pentagonWeight_mul_pentagonWeight_self G R C t hX x,
    sum_pentagonWeight_mul_initialPentagonWeight_self G R C t hst x,
    sum_initialPentagonWeight_mul_pentagonWeight_self G R C t hst x,
    sum_initialPentagonWeight_mul_initialPentagonWeight_self G R C t hX x, add_zero, zero_add]

/-! ### The diagonal identity -/

/-- **The diagonal of the crossing change homotopy equation.** If the turn rows `s` and `t`
differ and the annulus squares carry no `X`-marking, then over a commutative semiring of
characteristic two the coefficient of `∂H + H∂` from a grid state to itself is the annulus weight
plus the coefficient of `ΨΦ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_single_apply_self [CharP R 2]
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    (x : GridState n) :
    (G.unblockedDifferential R (G.crossingChangeHomotopy R C t (Finsupp.single x 1)) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R (Finsupp.single x 1))) x =
      G.crossingChangeAnnulusWeight R C t +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t)
          (G.commutationMap R C (Finsupp.single x 1)) x := by
  rw [Finsupp.add_apply, unblockedDifferential_crossingChangeHomotopy_single_apply,
    crossingChangeHomotopy_unblockedDifferential_single_apply,
    sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient_self G R C t hX,
    sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient_self G R C t hX,
    commutationMap_withTurnRow_commutationMap_single_apply_self G R C t hst hX]
  -- Cutting the circle at the rows of `x` in two consecutive columns splits the event that the
  -- row of `x` in column `b` lies after one turn row and at or before the other into three
  -- cyclic orders, and the two such events partition the circle.
  have huv : x a ≠ x b := x.toPerm.injective.ne C.column_ne_next
  have hvw : x b ≠ x (finRotate n b) :=
    x.toPerm.injective.ne ((finRotate n).injective.ne C.column_ne_next)
  have hleft := (Grid.ite_eq_or_mem_cIoo_eq_add_add huv hst).symm
  have hright := (Grid.ite_eq_or_mem_cIoo_eq_add_add hvw.symm hst.symm).symm
  have hpartition :
      ((if x b = t ∨ x b ∈ Grid.cIoo C.turnRow t then 1 else 0) : ℕ) +
        (if x b = C.turnRow ∨ x b ∈ Grid.cIoo t C.turnRow then 1 else 0) = 1 := by
    simp only [Grid.mem_cIoo, Fin.ext_iff] at hst ⊢
    split_ifs <;> omega
  have hsum := congrArg (fun k : ℕ => (k : MvPolynomial (Fin n) R) *
    G.crossingChangeAnnulusWeight R C t)
    ((congrArg₂ (fun k l : ℕ => k + l) hleft hright).trans hpartition)
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul, ite_mul, one_mul,
    zero_mul] at hsum
  simp only [@and_comm (t ∈ Grid.cIco (x (finRotate n b)) (x b))] at hsum
  apply CharTwo.eq_add_iff_add_eq.mpr
  convert hsum using 1
  ac_rfl

/-! ### The crossing change maps of interleaving columns -/

variable {G C t}

/-- **The diagonal of the crossing change homotopy equation**, for markings in the order
`O_b, O_a, X_b, X_a`. If the segments of the columns `a` and `b = finRotate n a` interleave with
`O_a` on the arc of column `b`, the crossing change maps turn in the rows of `O_a` and `X_b`, and
`R` has characteristic two, then the coefficient of `∂H + H∂` from a grid state to itself is
`V_b` plus that of `ΨΦ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_single_apply_self_of_mem_columnArc
    [CharP R 2] (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b)
    (hs : C.turnRow = G.O a) (ht : t = G.X b) (x : GridState n) :
    (G.unblockedDifferential R (G.crossingChangeHomotopy R C t (Finsupp.single x 1)) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R (Finsupp.single x 1))) x =
      MvPolynomial.X b +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t)
          (G.commutationMap R C (Finsupp.single x 1)) x := by
  rw [unblockedDifferential_crossingChangeHomotopy_add_single_apply_self G R C t
      (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
      (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht),
    crossingChangeAnnulusWeight_eq_X_next_of_mem_columnArc R h hO hs ht]

/-- **The diagonal of the crossing change homotopy equation**, for markings in the order
`O_b, X_a, X_b, O_a`. If the segments of the columns `a` and `b = finRotate n a` interleave with
`O_a` off the arc of column `b`, the crossing change maps turn in the rows of `X_a` and `O_b`, and
`R` has characteristic two, then the coefficient of `∂H + H∂` from a grid state to itself is
`V_a` plus that of `ΨΦ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_single_apply_self_of_notMem_columnArc
    [CharP R 2] (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b)
    (hs : C.turnRow = G.X a) (ht : t = G.O b) (x : GridState n) :
    (G.unblockedDifferential R (G.crossingChangeHomotopy R C t (Finsupp.single x 1)) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R (Finsupp.single x 1))) x =
      MvPolynomial.X a +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t)
          (G.commutationMap R C (Finsupp.single x 1)) x := by
  rw [unblockedDifferential_crossingChangeHomotopy_add_single_apply_self G R C t
      (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
      (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht),
    crossingChangeAnnulusWeight_eq_X_column_of_notMem_columnArc R h hO hs ht]

end GridDiagram

end TauCeti
