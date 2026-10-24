/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Recut
import TauCeti.Data.Finset.Basic
import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Geometry

/-!
# Mixed-side commutation pentagon pairs

Let `C` be a column commutation and consider a pentagon for `C` followed by a pentagon for the
reverse commutation. When the two pentagons turn on opposite sides of the replaced grid line,
their underlying rectangles automatically share that line: it is terminal for the first and
initial for the second, or initial for the first and terminal for the second. Away from the
diagonal this is their unique common side, so the general empty-rectangle recut applies.

In the homotopy equation of the commutation, such a pair is matched with a hexagon composite
through the same intermediate state and with the same two rectangles, not with its recut. The two
rectangles share a corner row on the replaced line: the bottom row for a terminal--initial pair
and the top row for an initial--terminal pair. Both turn rows lie on the replaced-line side of
the rectangle of the pentagon whose turn row is farther from that shared row. That rectangle is a
commutation hexagon cutting away the bigon between the two turn points, and the other one is an
ordinary rectangle. Column by column, the bigon markings that the two
pentagons cover are the ones the hexagon and the rectangle cover, so the composite is counted and
has the weight of the pair. Its recut underlies no hexagon composite: one recut rectangle has no
side on the replaced line, and the other misses one of the turn rows. Hence the composite is
unpaired, and it is the only counted composite with these two rectangles.

## Main definitions

* `TauCeti.GridDiagram.recutTerminalInitialPentagonPair`: the recut of a terminal-side
  pentagon followed by an initial-side pentagon for the reverse commutation.
* `TauCeti.GridDiagram.recutInitialTerminalPentagonPair`: the recut in the opposite turn-side
  order.

## Main results

* `TauCeti.GridDiagram.existsUnique_unpairedHexagonComposite_of_terminalInitialPentagonPair` and
  `TauCeti.GridDiagram.existsUnique_unpairedHexagonComposite_of_initialTerminalPentagonPair`: a
  counted off-diagonal mixed-side pentagon pair has the same underlying rectangle decomposition
  as exactly one unpaired hexagon composite, and their weights agree.

## References

The mixed turn-side cases of the hexagon homotopy argument of Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Section 5.1, and Manolescu--Ozsváth--Szabó--Thurston, *On
combinatorial link Floer homology*, Section 3.1, Proposition 3.2 (arXiv:math/0610559).
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

/-! ### Square bookkeeping for the matching composites -/

/-- The squares covered by a reverse pentagon read in `G`, given the squares `S` it covers and
those `T` of its rectangle: away from the two commuted columns they are the squares of `T`, and in
those columns exchanging the columns exchanges the squares of `S`. -/
private theorem map_swapColumns_reverse_squares {S T : Finset (Fin n × Fin n)} {Qb Qt : Fin n}
    (hST : ∀ {p : Fin n × Fin n}, p.1 ≠ C.reverse.column → p.1 ≠ finRotate n C.reverse.column →
      (p ∈ S ↔ p ∈ T))
    (hSa : ∀ t, (C.reverse.column, t) ∈ S ↔ t ∈ Grid.cIoo C.reverse.turnRow Qt)
    (hSb : ∀ t, (finRotate n C.reverse.column, t) ∈ S ↔ t ∈ Grid.cIco Qb C.reverse.turnRow) :
    (∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b →
      (p ∈ S.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔ p ∈ T)) ∧
    ∀ r : Fin n,
      ((a, r) ∈ S.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
          r ∈ Grid.cIco Qb C.oppositeTurnRow) ∧
        ((b, r) ∈ S.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding ↔
          r ∈ Grid.cIoo C.oppositeTurnRow Qt) := by
  refine ⟨fun p ha hb => (Finset.mem_map_swap_prodCongr_refl_iff_of_ne _ ha hb).trans
    (hST (by rwa [C.reverse_column]) (by rwa [C.reverse_column])), fun r => ?_⟩
  simp only [C.reverse_column, C.reverse_turnRow] at hSa hSb
  simp only [Finset.mk_mem_map_swap_prodCongr_refl_iff, Equiv.swap_apply_left,
    Equiv.swap_apply_right, hSa, hSb, and_self]

/-- One of the two rectangles under a hexagon composite has the replaced grid line as a side and
both intersection rows among its rows. -/
private theorem toRectangleDecomposition_side_turns {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) :
    ((F.toRectangleDecomposition.first.left = b ∨ F.toRectangleDecomposition.first.right = b) ∧
        C.turnRow ∈ Grid.cIco F.toRectangleDecomposition.first.bottom
          F.toRectangleDecomposition.first.top ∧
        C.oppositeTurnRow ∈ Grid.cIco F.toRectangleDecomposition.first.bottom
          F.toRectangleDecomposition.first.top) ∨
      ((F.toRectangleDecomposition.second.left = b ∨
          F.toRectangleDecomposition.second.right = b) ∧
        C.turnRow ∈ Grid.cIco F.toRectangleDecomposition.second.bottom
          F.toRectangleDecomposition.second.top ∧
        C.oppositeTurnRow ∈ Grid.cIco F.toRectangleDecomposition.second.bottom
          F.toRectangleDecomposition.second.top) := by
  have key {u v : GridState n}
      (H : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow u v) :=
    And.intro H.left_eq_or_right_eq <| And.intro
      (H.pair_subset_cIco_bottom_top (Finset.mem_insert_self _ _))
      (H.pair_subset_cIco_bottom_top (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  cases F with
  | inl F =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
    exact Or.inl (key F.hexagon)
  | inr F =>
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
    exact Or.inr (key F.hexagon)

variable (R : Type*) [CommSemiring R]

/-- Two pairs of finite sets of squares carry the same total `O`-weight when, away from the two
commuted columns, the first sets agree and the second sets agree, and, in those two columns, each
pair covers the `O`-marking at most once and the two pairs cover the same ones. -/
private theorem prod_mul_prod_eq_of_markings (A B E F : Finset (Fin n × Fin n))
    (hA : ∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b → (p ∈ A ↔ p ∈ E))
    (hB : ∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b → (p ∈ B ↔ p ∈ F))
    (hcol : ∀ c, c = a ∨ c = b →
      (((c, G.O c) ∈ A ∨ (c, G.O c) ∈ B) ↔ ((c, G.O c) ∈ E ∨ (c, G.O c) ∈ F)) ∧
        ¬((c, G.O c) ∈ A ∧ (c, G.O c) ∈ B) ∧ ¬((c, G.O c) ∈ E ∧ (c, G.O c) ∈ F)) :
    (∏ p ∈ A, if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R)) *
        (∏ p ∈ B, if p ∈ G.OSet then MvPolynomial.X p.1 else 1) =
      (∏ p ∈ E, if p ∈ G.OSet then MvPolynomial.X p.1 else 1) *
        ∏ p ∈ F, if p ∈ G.OSet then MvPolynomial.X p.1 else 1 := by
  have key : ∀ c, (((c, G.O c) ∈ A ∨ (c, G.O c) ∈ B) ↔ ((c, G.O c) ∈ E ∨ (c, G.O c) ∈ F)) ∧
      (((c, G.O c) ∈ A ∧ (c, G.O c) ∈ B) ↔ ((c, G.O c) ∈ E ∧ (c, G.O c) ∈ F)) := by
    intro c
    by_cases hc : c = a ∨ c = b
    · have := hcol c hc
      tauto
    · have h₁ := hA (c, G.O c) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))
      have h₂ := hB (c, G.O c) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))
      tauto
  have hfilter : ∀ S T : Finset (Fin n × Fin n),
      (∀ c, (c, G.O c) ∈ S ↔ (c, G.O c) ∈ T) →
      (∏ p ∈ S, if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R)) =
        ∏ p ∈ T, if p ∈ G.OSet then MvPolynomial.X p.1 else 1 := by
    intro S T h
    rw [← Finset.prod_filter, ← Finset.prod_filter]
    congr 1
    ext ⟨c, r⟩
    simp only [Finset.mem_filter, G.mk_mem_OSet]
    constructor
    · rintro ⟨hp, rfl⟩
      exact ⟨(h c).mp hp, rfl⟩
    · rintro ⟨hp, rfl⟩
      exact ⟨(h c).mpr hp, rfl⟩
  rw [← Finset.prod_union_inter (s₁ := A), ← Finset.prod_union_inter (s₁ := E)]
  congr 1 <;> apply hfilter <;> intro c <;> simp only [Finset.mem_union, Finset.mem_inter]
  exacts [(key c).1, (key c).2]

/-- Two sets of squares carry no `X`-marking when two other sets carrying none cover the same
squares as them away from the two commuted columns, and cover every `X`-marking of those two
columns that they cover. -/
private theorem disjoint_XSet_of_markings (A B E F : Finset (Fin n × Fin n))
    (hA : ∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b → (p ∈ A ↔ p ∈ E))
    (hB : ∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b → (p ∈ B ↔ p ∈ F))
    (hcol : ∀ c, c = a ∨ c = b →
      (c, G.X c) ∈ E ∨ (c, G.X c) ∈ F → (c, G.X c) ∈ A ∨ (c, G.X c) ∈ B)
    (hAX : Disjoint A G.XSet) (hBX : Disjoint B G.XSet) :
    Disjoint E G.XSet ∧ Disjoint F G.XSet := by
  have key : ∀ c, (c, G.X c) ∈ E ∨ (c, G.X c) ∈ F → (c, G.X c) ∈ A ∨ (c, G.X c) ∈ B := by
    intro c
    by_cases hc : c = a ∨ c = b
    · exact hcol c hc
    · have h₁ := hA (c, G.X c) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))
      have h₂ := hB (c, G.X c) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))
      tauto
  have hmem : ∀ p ∈ G.XSet, p ∈ E ∨ p ∈ F → False := by
    rintro ⟨c, r⟩ hX hp
    obtain rfl : G.X c = r := (G.mk_mem_XSet c r).mp hX
    rcases key c hp with h | h
    · exact Finset.disjoint_left.mp hAX h hX
    · exact Finset.disjoint_left.mp hBX h hX
  exact ⟨Finset.disjoint_right.mpr fun _ hX hp => hmem _ hX (Or.inl hp),
    Finset.disjoint_right.mpr fun _ hX hp => hmem _ hX (Or.inr hp)⟩

/-- The two pieces of a composite carry no `X`-marking and have the total `O`-weight of a pentagon
pair, when the pieces cover the same squares as the pentagons away from the two commuted columns,
and the markings of those columns, which lie in the two bigons, are covered at most once and
equally often by the pieces and by the pentagons. -/
private theorem disjoint_XSet_and_prod_eq_of_markings (A B E F : Finset (Fin n × Fin n))
    (hA : ∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b → (p ∈ A ↔ p ∈ E))
    (hB : ∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b → (p ∈ B ↔ p ∈ F))
    (hcol : ∀ M : GridState n, M a ∈ insert C.turnRow (Grid.cIco C.oppositeTurnRow C.turnRow) →
      M b ∈ insert C.oppositeTurnRow (Grid.cIco C.turnRow C.oppositeTurnRow) →
      ∀ c, c = a ∨ c = b →
        (((c, M c) ∈ A ∨ (c, M c) ∈ B) ↔ ((c, M c) ∈ E ∨ (c, M c) ∈ F)) ∧
          ¬((c, M c) ∈ A ∧ (c, M c) ∈ B) ∧ ¬((c, M c) ∈ E ∧ (c, M c) ∈ F))
    (hAX : Disjoint A G.XSet) (hBX : Disjoint B G.XSet) :
    Disjoint E G.XSet ∧ Disjoint F G.XSet ∧
      (∏ p ∈ A, if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R)) *
          (∏ p ∈ B, if p ∈ G.OSet then MvPolynomial.X p.1 else 1) =
        (∏ p ∈ E, if p ∈ G.OSet then MvPolynomial.X p.1 else 1) *
          ∏ p ∈ F, if p ∈ G.OSet then MvPolynomial.X p.1 else 1 :=
  ⟨(G.disjoint_XSet_of_markings C A B E F hA hB
      (fun c hc h => (hcol G.X C.X_column_below C.X_next_above c hc).1.mpr h) hAX hBX).1,
    (G.disjoint_XSet_of_markings C A B E F hA hB
      (fun c hc h => (hcol G.X C.X_column_below C.X_next_above c hc).1.mpr h) hAX hBX).2,
    G.prod_mul_prod_eq_of_markings C R A B E F hA hB (hcol G.O C.O_column_below C.O_next_above)⟩

/-- An empty commutation hexagon followed by an empty rectangle, neither covering an `X`-marking,
is a counted composite whose weight is the product of the `O`-weights of their squares. -/
private theorem inl_mem_hexagonCompositeDecompositions_and_weight {x y z : GridState n}
    (H : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow x y)
    (S : GridRectangleBetween y z) (hH : H.toGridRectangleBetween.IsEmpty) (hS : S.IsEmpty)
    (hHX : Disjoint H.coveredSquares G.XSet)
    (hSX : Disjoint S.toGridRectangle.coveredSquares G.XSet) :
    let F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z := .inl ⟨y, H, S⟩
    F ∈ G.hexagonCompositeDecompositions C x z ∧
      F.toRectangleDecomposition = ⟨y, H.toGridRectangleBetween, S⟩ ∧
        G.hexagonCompositeWeight C R F =
          (∏ p ∈ H.coveredSquares,
              if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R)) *
            ∏ p ∈ S.toGridRectangle.coveredSquares, if p ∈ G.OSet then MvPolynomial.X p.1 else 1 :=
  ⟨(G.inl_mem_hexagonCompositeDecompositions C _).mpr
      ((G.mem_hexagonRectangleDecompositions C _).mpr
        ⟨(G.mem_commutationHexagons C _).mpr ⟨hH, hHX⟩,
          (G.mem_unblockedRectangles _).mpr ⟨hS, hSX⟩⟩),
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inl _,
    by rw [G.hexagonCompositeWeight_inl, G.hexagonRectangleWeight_def,
      G.OMonomial_eq_prod_coveredSquares, G.commutationHexagonWeight_eq_prod_coveredSquares]⟩

/-- An empty rectangle followed by an empty commutation hexagon, neither covering an `X`-marking,
is a counted composite whose weight is the product of the `O`-weights of their squares. -/
private theorem inr_mem_hexagonCompositeDecompositions_and_weight {x y z : GridState n}
    (S : GridRectangleBetween x y)
    (H : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow y z) (hS : S.IsEmpty)
    (hH : H.toGridRectangleBetween.IsEmpty)
    (hSX : Disjoint S.toGridRectangle.coveredSquares G.XSet)
    (hHX : Disjoint H.coveredSquares G.XSet) :
    let F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z := .inr ⟨y, S, H⟩
    F ∈ G.hexagonCompositeDecompositions C x z ∧
      F.toRectangleDecomposition = ⟨y, S, H.toGridRectangleBetween⟩ ∧
        G.hexagonCompositeWeight C R F =
          (∏ p ∈ S.toGridRectangle.coveredSquares,
              if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R)) *
            ∏ p ∈ H.coveredSquares, if p ∈ G.OSet then MvPolynomial.X p.1 else 1 :=
  ⟨(G.inr_mem_hexagonCompositeDecompositions C _).mpr
      ((G.mem_rectangleHexagonDecompositions C _).mpr
        ⟨(G.mem_unblockedRectangles _).mpr ⟨hS, hSX⟩,
          (G.mem_commutationHexagons C _).mpr ⟨hH, hHX⟩⟩),
    GridHexagonCompositeDecomposition.toRectangleDecomposition_inr _,
    by rw [G.hexagonCompositeWeight_inr, G.rectangleHexagonWeight_def,
      G.OMonomial_eq_prod_coveredSquares, G.commutationHexagonWeight_eq_prod_coveredSquares]⟩

/-! ### Cyclic order of the turns and the markings -/

/-- Marking rows for a terminal--initial pair whose reverse turn lies above the forward one: a
row `r` of the bigon below the forward turn is covered once by the two pentagons exactly when it
lies in the rows of the first one, and a row `r'` of the bigon above it is not covered. -/
private theorem terminalInitial_marking_rows_of_lt {B Pt Qt s s' r r' : Fin n}
    (hs : s ∈ Grid.cIco B Pt) (hs' : s' ∈ Grid.cIco B Qt)
    (hturn : s ∈ Grid.cIco B Qt ∧ s' ∈ Grid.cIoo s Qt)
    (hr : r ∈ insert s (Grid.cIco s' s)) (hr' : r' ∈ insert s' (Grid.cIco s s')) :
    ((r ∈ Grid.cIoo s Pt ∨ r ∈ Grid.cIco B s') ↔ r ∈ Grid.cIco B Pt) ∧
      ¬(r ∈ Grid.cIoo s Pt ∧ r ∈ Grid.cIco B s') ∧
        r' ∉ Grid.cIco B s ∧ r' ∉ Grid.cIoo s' Qt := by
  obtain ⟨hsQ, hs'Q⟩ := hturn
  simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq, ← Fin.val_inj] at *
  split_ifs at * <;> omega

/-- Marking rows for a terminal--initial pair whose forward turn lies above the reverse one: a
row `r` of the bigon below the forward turn is not covered, and a row `r'` of the bigon above it
is covered once by the two pentagons exactly when it lies in the rows of the second one. -/
private theorem terminalInitial_marking_rows_of_gt {B Pt Qt s s' r r' : Fin n}
    (hs : s ∈ Grid.cIco B Pt) (hs' : s' ∈ Grid.cIco B Qt)
    (hturn : s' ∈ Grid.cIco B Pt ∧ s ∈ Grid.cIoo s' Pt)
    (hr : r ∈ insert s (Grid.cIco s' s)) (hr' : r' ∈ insert s' (Grid.cIco s s')) :
    r ∉ Grid.cIoo s Pt ∧ r ∉ Grid.cIco B s' ∧
      ((r' ∈ Grid.cIco B s ∨ r' ∈ Grid.cIoo s' Qt) ↔ r' ∈ Grid.cIco B Qt) ∧
        ¬(r' ∈ Grid.cIco B s ∧ r' ∈ Grid.cIoo s' Qt) := by
  obtain ⟨hs'P, hsP⟩ := hturn
  simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq, ← Fin.val_inj] at *
  split_ifs at * <;> omega

/-- Marking rows for an initial--terminal pair whose reverse turn lies above the forward one: a
row `r` of the bigon below the forward turn is covered once by the two pentagons exactly when it
lies in the rows of the second one, and a row `r'` of the bigon above it is not covered. -/
private theorem initialTerminal_marking_rows_of_lt {Pb Qb T s s' r r' : Fin n}
    (hs : s ∈ Grid.cIco Pb T) (hs' : s' ∈ Grid.cIco Qb T) (hturn : s' ∈ Grid.cIoo s T)
    (hr : r ∈ insert s (Grid.cIco s' s)) (hr' : r' ∈ insert s' (Grid.cIco s s')) :
    ((r ∈ Grid.cIoo s T ∨ r ∈ Grid.cIco Qb s') ↔ r ∈ Grid.cIco Qb T) ∧
      ¬(r ∈ Grid.cIoo s T ∧ r ∈ Grid.cIco Qb s') ∧
        r' ∉ Grid.cIco Pb s ∧ r' ∉ Grid.cIoo s' T := by
  simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq, ← Fin.val_inj] at *
  split_ifs at * <;> omega

/-- Marking rows for an initial--terminal pair whose forward turn lies above the reverse one: a
row `r` of the bigon below the forward turn is not covered, and a row `r'` of the bigon above it
is covered once by the two pentagons exactly when it lies in the rows of the first one. -/
private theorem initialTerminal_marking_rows_of_gt {Pb Qb T s s' r r' : Fin n}
    (hs : s ∈ Grid.cIco Pb T) (hs' : s' ∈ Grid.cIco Qb T) (hturn : s ∈ Grid.cIoo s' T)
    (hr : r ∈ insert s (Grid.cIco s' s)) (hr' : r' ∈ insert s' (Grid.cIco s s')) :
    r ∉ Grid.cIoo s T ∧ r ∉ Grid.cIco Qb s' ∧
      ((r' ∈ Grid.cIco Pb s ∨ r' ∈ Grid.cIoo s' T) ↔ r' ∈ Grid.cIco Pb T) ∧
        ¬(r' ∈ Grid.cIco Pb s ∧ r' ∈ Grid.cIoo s' T) := by
  simp only [Grid.mem_cIco, Grid.mem_cIoo, Finset.mem_insert, ne_eq, ← Fin.val_inj] at *
  split_ifs at * <;> omega

/-! ### The matching composite of a terminal--initial pair -/

section TerminalInitial

variable {x y z : GridState n} (P : GridPentagonBetween C.column C.turnRow x y)
  (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)

/-- A terminal-side pentagon and a following initial-side reverse pentagon share their bottom
row. -/
private theorem terminalInitial_bottom_eq : Q.bottom = P.bottom := by
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.bottom_def, Q.left_eq,
    C.reverse_column, ← P.right_eq, P.map_right]

/-- The reverse turn row of a terminal--initial pentagon pair lies in the rows from the common
bottom row up to the top row of the reverse pentagon. -/
private theorem terminalInitial_oppositeTurnRow_mem_cIco :
    C.oppositeTurnRow ∈ Grid.cIco P.bottom Q.top := by
  simpa only [C.reverse_turnRow, G.terminalInitial_bottom_eq C P Q] using
    Q.turn_mem_cIco_bottom_top

/-- The weight of a terminal--initial pentagon pair is the product of the `O`-weights of the
squares of the forward pentagon and of the reverse pentagon read in `G`. -/
private theorem pentagonPairWeight_terminalInitial :
    G.pentagonPairWeight C R ⟨y, .inl P, .inr Q⟩ =
      (∏ p ∈ P.coveredSquares,
          if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R)) *
        ∏ p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding,
          if p ∈ G.OSet then MvPolynomial.X p.1 else 1 := by
  rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inl,
    (G.swapColumns a b).commutationPentagonWeight_inr, G.rename_pentagonWeight,
    G.initialPentagonWeight_reverse]

/-- When the reverse turn lies above the forward one, a counted terminal--initial pair has the
same underlying rectangles as a counted rectangle--hexagon composite of the same weight, whose
hexagon is the rectangle of the reverse pentagon. -/
private theorem terminalInitial_rectangleHexagon
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons C.reverse y z)
    (hturn : C.turnRow ∈ Grid.cIco Q.bottom Q.top ∧ C.oppositeTurnRow ∈ Grid.cIoo C.turnRow Q.top) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.hexagonCompositeDecompositions C x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inl P, .inr Q⟩ := by
  obtain ⟨hp, hpX⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_initialPentagons Q).mp hQ
  let H : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow y z :=
    .inr ⟨Q.toGridRectangleBetween, Q.left_eq.trans (congrArg (finRotate n) C.reverse_column),
      hturn.1, hturn.2⟩
  have hH : H.toGridRectangleBetween = Q.toGridRectangleBetween :=
    GridCommutationHexagonBetween.toGridRectangleBetween_inr _
  have hbottom := G.terminalInitial_bottom_eq C P Q
  have hs := P.turn_mem_cIco_bottom_top
  have hs' := G.terminalInitial_oppositeTurnRow_mem_cIco C P Q
  obtain ⟨hQoff, hQcol⟩ := G.map_swapColumns_reverse_squares C Q.mem_coveredSquares_iff_of_ne
    Q.mk_mem_coveredSquares_left_column Q.mk_mem_coveredSquares_right_column
  rw [hbottom] at hturn
  obtain ⟨hPX, hHX, hweight⟩ := G.disjoint_XSet_and_prod_eq_of_markings C R P.coveredSquares
    (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding)
    P.toGridRectangle.coveredSquares H.coveredSquares
    (fun p ha hb => P.mem_coveredSquares_iff_of_ne ha hb)
    (fun p ha hb => by rw [H.mem_coveredSquares_iff_of_ne ha hb, hH]; exact hQoff p ha hb)
    (fun M ha hb c hc => by
      obtain ⟨hrow, hdisj, hb₁, hb₂⟩ := terminalInitial_marking_rows_of_lt hs hs' hturn ha hb
      obtain ⟨hQa, hQb⟩ := hQcol (M c)
      have hHa := H.mk_notMem_coveredSquares_left_column (M c)
      have hHb := H.mk_notMem_coveredSquares_right_column (M c)
      have hPa := P.mk_mem_coveredSquares_left_column (M c)
      have hPb := P.mk_mem_coveredSquares_right_column (M c)
      rcases hc with rfl | rfl
      · simp only [hPa, hQa, hbottom, P.mk_mem_toGridRectangle_coveredSquares_left_column, hHa,
          or_false, and_false, not_false_eq_true, and_true]
        exact ⟨hrow, hdisj⟩
      · simp only [hPb, hQb, P.mk_notMem_toGridRectangle_coveredSquares_right_column, hHb, hb₁,
          hb₂, or_self, and_self, not_false_eq_true])
    hpX ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX)
  obtain ⟨hF, hFD, hFw⟩ := G.inr_mem_hexagonCompositeDecompositions_and_weight C R
    P.toGridRectangleBetween H hp (hH ▸ hq) hPX hHX
  exact ⟨_, hF, by rw [hFD, hH], by rw [hFw, G.pentagonPairWeight_terminalInitial C R, hweight]⟩

/-- When the forward turn lies above the reverse one, a counted terminal--initial pair has the
same underlying rectangles as a counted hexagon--rectangle composite of the same weight, whose
hexagon is the rectangle of the forward pentagon. -/
private theorem terminalInitial_hexagonRectangle
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons C.reverse y z)
    (hturn : C.oppositeTurnRow ∈ Grid.cIco P.bottom P.top ∧
      C.turnRow ∈ Grid.cIoo C.oppositeTurnRow P.top) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.hexagonCompositeDecompositions C x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inl P, .inr Q⟩ := by
  obtain ⟨hp, hpX⟩ := (G.mem_pentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_initialPentagons Q).mp hQ
  let H : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow x y :=
    .inl ⟨P.toGridRectangleBetween, P.right_eq, hturn.1, hturn.2⟩
  have hH : H.toGridRectangleBetween = P.toGridRectangleBetween :=
    GridCommutationHexagonBetween.toGridRectangleBetween_inl _
  have hbottom := G.terminalInitial_bottom_eq C P Q
  have hs := P.turn_mem_cIco_bottom_top
  have hs' := G.terminalInitial_oppositeTurnRow_mem_cIco C P Q
  obtain ⟨hQoff, hQcol⟩ := G.map_swapColumns_reverse_squares C Q.mem_coveredSquares_iff_of_ne
    Q.mk_mem_coveredSquares_left_column Q.mk_mem_coveredSquares_right_column
  obtain ⟨hHX, hQX, hweight⟩ := G.disjoint_XSet_and_prod_eq_of_markings C R P.coveredSquares
    (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding)
    H.coveredSquares Q.toGridRectangle.coveredSquares
    (fun p ha hb => by
      rw [H.mem_coveredSquares_iff_of_ne ha hb, hH]
      exact P.mem_coveredSquares_iff_of_ne ha hb)
    hQoff
    (fun M ha hb c hc => by
      obtain ⟨ha₁, ha₂, hrow, hdisj⟩ := terminalInitial_marking_rows_of_gt hs hs' hturn ha hb
      obtain ⟨hQa, hQb⟩ := hQcol (M c)
      have hHa := H.mk_notMem_coveredSquares_left_column (M c)
      have hHb := H.mk_notMem_coveredSquares_right_column (M c)
      have hPa := P.mk_mem_coveredSquares_left_column (M c)
      have hPb := P.mk_mem_coveredSquares_right_column (M c)
      have hRb := Q.mk_mem_toGridRectangle_coveredSquares_right_column (M c)
      have hRa := Q.mk_notMem_toGridRectangle_coveredSquares_left_column (M c)
      simp only [C.reverse_column] at hRb hRa
      rcases hc with rfl | rfl
      · simp only [hPa, hQa, hbottom, hRa, hHa, ha₁, ha₂, or_self, and_self, not_false_eq_true]
      · simp only [hPb, hQb, hbottom, hRb, hHb, false_or, false_and, not_false_eq_true, and_true]
        exact ⟨hrow, hdisj⟩)
    hpX ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX)
  obtain ⟨hF, hFD, hFw⟩ := G.inl_mem_hexagonCompositeDecompositions_and_weight C R
    H Q.toGridRectangleBetween (hH ▸ hp) hq hHX hQX
  exact ⟨_, hF, by rw [hFD, hH], by rw [hFw, G.pentagonPairWeight_terminalInitial C R, hweight]⟩

/-- The recut of an off-diagonal terminal--initial pair underlies no hexagon composite: one of its
rectangles has no side on the replaced grid line, and the other misses one of the turn rows. -/
private theorem terminalInitial_ne_recut (hzx : z ≠ x) (hp : P.IsEmpty) (hq : Q.IsEmpty)
    (F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) :
    F.toRectangleDecomposition ≠ G.recutTerminalInitialPentagonPair C P Q hzx hp hq := by
  intro hF
  have hdata := G.isRecutOfRightEqLeft_recutTerminalInitialPentagonPair C P Q hzx hp hq
  rw [← hF] at hdata
  have hs := P.turn_mem_cIco_bottom_top
  have hs' := G.terminalInitial_oppositeTurnRow_mem_cIco C P Q
  have hQright : Q.right ≠ b := by simpa only [C.reverse_column] using Q.right_ne
  rcases hdata.recut_geometry (G.hasOneCommonSide_terminalInitialPentagonPair C P Q hzx) with
      ⟨hrow, h1l, h1r, h2l, h2r, h1b, h1t, -, -⟩ | ⟨hrow, h1l, h1r, h2l, h2r, -, -, h2b, h2t⟩ <;>
    rcases G.toRectangleDecomposition_side_turns C F with
      ⟨hside, hturn, hturn'⟩ | ⟨hside, hturn, hturn'⟩
  · rw [h1b, h1t] at hturn
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hs hturn
  · rw [h2l, h2r] at hside
    exact hside.elim P.left_ne hQright
  · rw [h1l, h1r] at hside
    exact hside.elim P.left_ne hQright
  · rw [h2b, h2t] at hturn'
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hs' hturn'

end TerminalInitial

/-! ### The matching composite of an initial--terminal pair -/

section InitialTerminal

variable {x y z : GridState n} (P : GridInitialPentagonBetween C.column C.turnRow x y)
  (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)

/-- An initial-side pentagon and a following terminal-side reverse pentagon share their top
row. -/
private theorem initialTerminal_top_eq : Q.top = P.top := by
  rw [GridRectangleBetween.top_def, GridRectangleBetween.top_def, Q.right_eq,
    C.reverse_column, ← P.left_eq, P.map_left]

/-- The reverse turn row of an initial--terminal pentagon pair lies in the rows from the bottom row
of the reverse pentagon up to the common top row. -/
private theorem initialTerminal_oppositeTurnRow_mem_cIco :
    C.oppositeTurnRow ∈ Grid.cIco Q.bottom P.top := by
  simpa only [C.reverse_turnRow, G.initialTerminal_top_eq C P Q] using
    Q.turn_mem_cIco_bottom_top

/-- The weight of an initial--terminal pentagon pair is the product of the `O`-weights of the
squares of the forward pentagon and of the reverse pentagon read in `G`. -/
private theorem pentagonPairWeight_initialTerminal :
    G.pentagonPairWeight C R ⟨y, .inr P, .inl Q⟩ =
      (∏ p ∈ P.coveredSquares,
          if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R)) *
        ∏ p ∈ Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding,
          if p ∈ G.OSet then MvPolynomial.X p.1 else 1 := by
  rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inr,
    (G.swapColumns a b).commutationPentagonWeight_inl, G.rename_initialPentagonWeight,
    G.pentagonWeight_reverse]

/-- When the reverse turn lies above the forward one, a counted initial--terminal pair has the
same underlying rectangles as a counted hexagon--rectangle composite of the same weight, whose
hexagon is the rectangle of the forward pentagon. -/
private theorem initialTerminal_hexagonRectangle
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons C.reverse y z)
    (hturn : C.oppositeTurnRow ∈ Grid.cIoo C.turnRow P.top) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.hexagonCompositeDecompositions C x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inr P, .inl Q⟩ := by
  obtain ⟨hp, hpX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_pentagons Q).mp hQ
  have hs := P.turn_mem_cIco_bottom_top
  let H : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow x y :=
    .inr ⟨P.toGridRectangleBetween, P.left_eq, hs, hturn⟩
  have hH : H.toGridRectangleBetween = P.toGridRectangleBetween :=
    GridCommutationHexagonBetween.toGridRectangleBetween_inr _
  have htop := G.initialTerminal_top_eq C P Q
  have hs' := G.initialTerminal_oppositeTurnRow_mem_cIco C P Q
  obtain ⟨hQoff, hQcol⟩ := G.map_swapColumns_reverse_squares C Q.mem_coveredSquares_iff_of_ne
    Q.mk_mem_coveredSquares_left_column Q.mk_mem_coveredSquares_right_column
  obtain ⟨hHX, hQX, hweight⟩ := G.disjoint_XSet_and_prod_eq_of_markings C R P.coveredSquares
    (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding)
    H.coveredSquares Q.toGridRectangle.coveredSquares
    (fun p ha hb => by
      rw [H.mem_coveredSquares_iff_of_ne ha hb, hH]
      exact P.mem_coveredSquares_iff_of_ne ha hb)
    hQoff
    (fun M ha hb c hc => by
      obtain ⟨hrow, hdisj, hb₁, hb₂⟩ := initialTerminal_marking_rows_of_lt hs hs' hturn ha hb
      obtain ⟨hQa, hQb⟩ := hQcol (M c)
      have hHa := H.mk_notMem_coveredSquares_left_column (M c)
      have hHb := H.mk_notMem_coveredSquares_right_column (M c)
      have hPa := P.mk_mem_coveredSquares_left_column (M c)
      have hPb := P.mk_mem_coveredSquares_right_column (M c)
      have hRa := Q.mk_mem_toGridRectangle_coveredSquares_left_column (M c)
      have hRb := Q.mk_notMem_toGridRectangle_coveredSquares_right_column (M c)
      simp only [C.reverse_column] at hRa hRb
      rcases hc with rfl | rfl
      · simp only [hPa, hQa, htop, hRa, hHa, false_or, false_and, not_false_eq_true, and_true]
        exact ⟨hrow, hdisj⟩
      · simp only [hPb, hQb, htop, hRb, hHb, hb₁, hb₂, or_self, and_self, not_false_eq_true])
    hpX ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX)
  obtain ⟨hF, hFD, hFw⟩ := G.inl_mem_hexagonCompositeDecompositions_and_weight C R
    H Q.toGridRectangleBetween (hH ▸ hp) hq hHX hQX
  exact ⟨_, hF, by rw [hFD, hH], by rw [hFw, G.pentagonPairWeight_initialTerminal C R, hweight]⟩

/-- When the forward turn lies above the reverse one, a counted initial--terminal pair has the
same underlying rectangles as a counted rectangle--hexagon composite of the same weight, whose
hexagon is the rectangle of the reverse pentagon. -/
private theorem initialTerminal_rectangleHexagon
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons C.reverse y z)
    (hturn : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow P.top) :
    ∃ F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.hexagonCompositeDecompositions C x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inr P, .inl Q⟩ := by
  obtain ⟨hp, hpX⟩ := (G.mem_initialPentagons P).mp hP
  obtain ⟨hq, hqX⟩ := ((G.swapColumns a b).mem_pentagons Q).mp hQ
  have hs := P.turn_mem_cIco_bottom_top
  have htop := G.initialTerminal_top_eq C P Q
  have hs' := G.initialTerminal_oppositeTurnRow_mem_cIco C P Q
  have hs'Q : C.oppositeTurnRow ∈ Grid.cIco Q.bottom Q.top := by rwa [htop]
  have hturnQ : C.turnRow ∈ Grid.cIoo C.oppositeTurnRow Q.top := by rwa [htop]
  let H : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow y z :=
    .inl ⟨Q.toGridRectangleBetween, Q.right_eq.trans (congrArg (finRotate n) C.reverse_column),
      hs'Q, hturnQ⟩
  have hH : H.toGridRectangleBetween = Q.toGridRectangleBetween :=
    GridCommutationHexagonBetween.toGridRectangleBetween_inl _
  obtain ⟨hQoff, hQcol⟩ := G.map_swapColumns_reverse_squares C Q.mem_coveredSquares_iff_of_ne
    Q.mk_mem_coveredSquares_left_column Q.mk_mem_coveredSquares_right_column
  obtain ⟨hPX, hHX, hweight⟩ := G.disjoint_XSet_and_prod_eq_of_markings C R P.coveredSquares
    (Q.coveredSquares.map ((Equiv.swap a b).prodCongr (Equiv.refl (Fin n))).toEmbedding)
    P.toGridRectangle.coveredSquares H.coveredSquares
    (fun p ha hb => P.mem_coveredSquares_iff_of_ne ha hb)
    (fun p ha hb => by rw [H.mem_coveredSquares_iff_of_ne ha hb, hH]; exact hQoff p ha hb)
    (fun M ha hb c hc => by
      obtain ⟨ha₁, ha₂, hrow, hdisj⟩ := initialTerminal_marking_rows_of_gt hs hs' hturn ha hb
      obtain ⟨hQa, hQb⟩ := hQcol (M c)
      have hHa := H.mk_notMem_coveredSquares_left_column (M c)
      have hHb := H.mk_notMem_coveredSquares_right_column (M c)
      have hPa := P.mk_mem_coveredSquares_left_column (M c)
      have hPb := P.mk_mem_coveredSquares_right_column (M c)
      have hRb := P.mk_mem_toGridRectangle_coveredSquares_right_column (M c)
      have hRa := P.mk_notMem_toGridRectangle_coveredSquares_left_column (M c)
      rcases hc with rfl | rfl
      · simp only [hPa, hQa, hRa, hHa, ha₁, ha₂, or_self, and_self, not_false_eq_true]
      · simp only [hPb, hQb, htop, hRb, hHb, or_false, and_false, not_false_eq_true, and_true]
        exact ⟨hrow, hdisj⟩)
    hpX ((G.disjoint_map_swapColumns_XSet_iff a b _).mpr hqX)
  obtain ⟨hF, hFD, hFw⟩ := G.inr_mem_hexagonCompositeDecompositions_and_weight C R
    P.toGridRectangleBetween H hp (hH ▸ hq) hPX hHX
  exact ⟨_, hF, by rw [hFD, hH], by rw [hFw, G.pentagonPairWeight_initialTerminal C R, hweight]⟩

/-- The recut of an off-diagonal initial--terminal pair underlies no hexagon composite: one of its
rectangles has no side on the replaced grid line, and the other misses one of the turn rows. -/
private theorem initialTerminal_ne_recut (hzx : z ≠ x) (hp : P.IsEmpty) (hq : Q.IsEmpty)
    (F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) :
    F.toRectangleDecomposition ≠ G.recutInitialTerminalPentagonPair C P Q hzx hp hq := by
  intro hF
  have hdata := G.isRecutOfLeftEqRight_recutInitialTerminalPentagonPair C P Q hzx hp hq
  rw [← hF] at hdata
  have hs := P.turn_mem_cIco_bottom_top
  have hs' := G.initialTerminal_oppositeTurnRow_mem_cIco C P Q
  have hQleft : Q.left ≠ b := by simpa only [C.reverse_column] using Q.left_ne
  rcases hdata.recut_geometry (G.hasOneCommonSide_initialTerminalPentagonPair C P Q hzx) with
      ⟨hrow, h1l, h1r, h2l, h2r, h1b, h1t, -, -⟩ | ⟨hrow, h1l, h1r, h2l, h2r, -, -, h2b, h2t⟩ <;>
    rcases G.toRectangleDecomposition_side_turns C F with
      ⟨hside, hturn, hturn'⟩ | ⟨hside, hturn, hturn'⟩
  · rw [h1b, h1t] at hturn
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hturn hs
  · rw [h2l, h2r] at hside
    exact hside.elim hQleft P.right_ne
  · rw [h1l, h1r] at hside
    exact hside.elim hQleft P.right_ne
  · rw [h2b, h2t] at hturn'
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hturn' hs'

end InitialTerminal

/-! ### The matching -/

/-- A counted off-diagonal pair of a terminal-side pentagon and an initial-side reverse pentagon
has the same underlying rectangles as exactly one unpaired hexagon composite, and their polynomial
weights agree. Its hexagon is the rectangle of the pentagon whose turn row is farther from the
common bottom row. -/
theorem existsUnique_unpairedHexagonComposite_of_terminalInitialPentagonPair
    {x y z : GridState n} (P : GridPentagonBetween a C.turnRow x y)
    (Q : GridInitialPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hP : P ∈ G.pentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).initialPentagons C.reverse y z) (hzx : z ≠ x) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.unpairedHexagonComposites C x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
        G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inl P, .inr Q⟩ := by
  have hp := ((G.mem_pentagons P).mp hP).1
  have hq := (((G.swapColumns a b).mem_initialPentagons Q).mp hQ).1
  obtain ⟨F, hF, hFD, hFw⟩ :
      ∃ F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
        F ∈ G.hexagonCompositeDecompositions C x z ∧
          F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inl P, .inr Q⟩ := by
    rcases Grid.mem_cIco_and_mem_cIoo_or_mem_cIco_and_mem_cIoo_of_ne P.turn_mem_cIco_bottom_top
        (G.terminalInitial_oppositeTurnRow_mem_cIco C P Q) C.turnRow_ne_oppositeTurnRow with
      hturn | hturn
    · rw [← G.terminalInitial_bottom_eq C P Q] at hturn
      exact G.terminalInitial_rectangleHexagon C R P Q hP hQ hturn
    · exact G.terminalInitial_hexagonRectangle C R P Q hP hQ hturn
  rw [← hFw]
  exact G.existsUnique_unpairedHexagonComposite_of_toRectangleDecomposition_eq C R
    (G.hasOneCommonSide_terminalInitialPentagonPair C P Q hzx) hp hq
    (fun E _ => G.terminalInitial_ne_recut C P Q hzx hp hq E) hF hFD

/-- A counted off-diagonal pair of an initial-side pentagon and a terminal-side reverse pentagon
has the same underlying rectangles as exactly one unpaired hexagon composite, and their polynomial
weights agree. Its hexagon is the rectangle of the pentagon whose turn row is farther from the
common top row. -/
theorem existsUnique_unpairedHexagonComposite_of_initialTerminalPentagonPair
    {x y z : GridState n} (P : GridInitialPentagonBetween a C.turnRow x y)
    (Q : GridPentagonBetween C.reverse.column C.reverse.turnRow y z)
    (hP : P ∈ G.initialPentagons C x y)
    (hQ : Q ∈ (G.swapColumns a b).pentagons C.reverse y z) (hzx : z ≠ x) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.unpairedHexagonComposites C x z ∧
        F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
        G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inr P, .inl Q⟩ := by
  have hp := ((G.mem_initialPentagons P).mp hP).1
  have hq := (((G.swapColumns a b).mem_pentagons Q).mp hQ).1
  obtain ⟨F, hF, hFD, hFw⟩ :
      ∃ F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
        F ∈ G.hexagonCompositeDecompositions C x z ∧
          F.toRectangleDecomposition = ⟨y, P.toGridRectangleBetween, Q.toGridRectangleBetween⟩ ∧
          G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R ⟨y, .inr P, .inl Q⟩ := by
    rcases Grid.mem_cIoo_or_mem_cIoo_of_ne P.turn_mem_cIco_bottom_top
        (G.initialTerminal_oppositeTurnRow_mem_cIco C P Q) C.turnRow_ne_oppositeTurnRow with
      hturn | hturn
    · exact G.initialTerminal_hexagonRectangle C R P Q hP hQ hturn
    · exact G.initialTerminal_rectangleHexagon C R P Q hP hQ hturn
  rw [← hFw]
  exact G.existsUnique_unpairedHexagonComposite_of_toRectangleDecomposition_eq C R
    (G.hasOneCommonSide_initialTerminalPentagonPair C P Q hzx) hp hq
    (fun E _ => G.initialTerminal_ne_recut C P Q hzx hp hq E) hF hFD

end TauCeti.GridDiagram
