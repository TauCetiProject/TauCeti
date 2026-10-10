/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Recutting an initial-side pentagon from a mixed terminal--initial side

Consider a rectangle followed by a commutation pentagon turning on its initial side. This file
treats the mixed overlap in which the rectangle's terminal side is the pentagon's initial side.
If the rectangle itself does not contain the turn row, the generic empty-rectangle recut has its
first rectangle starting on the replaced grid line and containing the turn row. It therefore
promotes to an initial-side pentagon followed by a rectangle.

The excluded case, where both original pieces contain the turn row, is the turn-point cut: the
same two underlying rectangles are instead read using the two different kinds of commutation
pentagon. Thus this file supplies the recut for the remaining branch of the `right = left` mixed
overlap in the grid-commutation chain-map equation.

Write `c` for the rectangle's initial side, `b` for the replaced line and `f` for the pentagon's
terminal side, and `p`, `q`, `r` for the rows of the source state on `c`, `b` and `f`. Emptiness
and the position of the turn row force `q` strictly between `p` and `r`
(`first_top_mem_cIoo_of_right_eq_left`). The recut consists of the new initial-side pentagon
from `b` to `f` over the rows from `q` to `r`, followed by the rectangle from `c` to `f` over the
rows from `p` to `q`. In the column before `b`, the new rectangle covers the squares of the
original rectangle and the two pentagons cover the same squares above the turn row. In the column
after `b`, the rows of the new rectangle followed by those of the new pentagon below the turn row
are the rows of the original pentagon below the turn row. So both composite domains cover the
same squares with the same multiplicities (`coveredSquares_val_add_val_recutRightEqLeft`). Hence
the recut of a counted domain is counted with the same monomial weight, and these terms cancel
between the rectangle--initial-pentagon and initial-pentagon--rectangle sums of the chain-map
equation
(`GridDiagram.add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_rightLeftOverlap`).

## Main definitions

* `TauCeti.GridRectangleInitialPentagonDecomposition.recutRightEqLeft`: the promoted
  initial-side-pentagon--rectangle recut of the mixed `right = left` overlap.
* `TauCeti.GridDiagram.initialPentagonRightLeftOverlapSources`: the counted
  rectangle--initial-side pentagon domains with this mixed overlap, outside the turn-point cut.
* `TauCeti.GridDiagram.initialPentagonRightLeftOverlapPartners`: their recuts.

## Main results

* `TauCeti.GridRectangleInitialPentagonDecomposition.isRecut_recutRightEqLeft`: it is an
  empty-rectangle recut of the original domain.
* `TauCeti.GridRectangleInitialPentagonDecomposition.recutRightEqLeft_geometry`: its row
  geometry; its pentagon starts on the replaced line.
* `TauCeti.GridRectangleInitialPentagonDecomposition.coveredSquares_val_add_val_recutRightEqLeft`:
  both decompositions cover the same squares with the same multiplicities.
* `TauCeti.GridDiagram.recutRightEqLeft_mem_initialPentagonRectangleDecompositions` and
  `TauCeti.GridDiagram.initialPentagonRectangleWeight_recutRightEqLeft`: the recut of a counted
  domain is counted, with the same weight.
* `TauCeti.GridDiagram.sum_rectangleInitialPentagonWeight_rightLeftOverlapSources_eq_sum_partners`
  and `TauCeti.GridDiagram.
  add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_rightLeftOverlap`: the sources and
  their recuts contribute equally and can be removed from the chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/
public section

namespace TauCeti.GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

private theorem underlying_second_isEmpty
    (D : GridRectangleInitialPentagonDecomposition a s x z) (h : D.pentagon.IsEmpty) :
    D.toGridRectangleDecomposition.second.IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] at h ⊢
  simpa only [D.pentagon_toGridRectangleBetween] using h

private theorem second_bottom_eq_first_bottom
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left) :
    D.second.bottom = D.first.bottom := by
  rw [GridRectangleBetween.bottom_def, ← hcommon, D.first.map_right,
    GridRectangleBetween.bottom_def]

/-- If the rectangle avoids the turn row, the noncommon sides of a mixed `right = left` overlap
differ: otherwise the pentagon would span the rectangle's rows and contain the turn row. -/
theorem first_left_ne_second_right_of_right_eq_left
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    D.first.left ≠ D.second.right := by
  intro hother
  have htop : D.second.top = D.first.top := by
    rw [GridRectangleBetween.top_def, ← hother, D.first.map_left,
      GridRectangleBetween.top_def]
  exact hturn (by
    simpa only [D.second_bottom_eq_first_bottom hcommon, htop] using D.second_turn_mem)

private noncomputable def rightLeftRecut
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    GridRectangleDecomposition x z :=
  D.toGridRectangleDecomposition.recut
    (D.toGridRectangleDecomposition.hasOneCommonSide_of_right_eq_left hcommon
      (D.first_left_ne_second_right_of_right_eq_left hcommon hturn))
    hfirst (D.underlying_second_isEmpty hsecond)

private theorem rightLeftRecut_geometry
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    let E := D.rightLeftRecut hcommon hfirst hsecond hturn
    E.middle = x.swapRows D.first.top D.second.top ∧
      E.first.left = D.second.left ∧
        E.first.bottom = D.first.top ∧ E.first.top = D.second.top ∧
          E.second.bottom = D.first.bottom ∧ E.second.top = D.first.top ∧
            s ∈ Grid.cIco E.first.bottom E.first.top := by
  let E := D.rightLeftRecut hcommon hfirst hsecond hturn
  have hdata := D.toGridRectangleDecomposition.isRecutOfRightEqLeft_recut hcommon
    (D.toGridRectangleDecomposition.hasOneCommonSide_of_right_eq_left hcommon
      (D.first_left_ne_second_right_of_right_eq_left hcommon hturn))
    hfirst (D.underlying_second_isEmpty hsecond)
  have hturnWhole : s ∈ Grid.cIco D.first.bottom D.second.top := by
    simpa only [D.second_bottom_eq_first_bottom hcommon] using D.second_turn_mem
  rcases hdata.recut_branch with hbranch | hbranch
  · have hfirstLeft : E.first.left = D.second.left := by
      apply x.toPerm.injective
      rw [← GridRectangleBetween.bottom_def]
      simp only [E, rightLeftRecut, hbranch.2.2.1, ← hcommon,
        GridRectangleBetween.top_def]
    have hfirstBottom : E.first.bottom = D.first.top := by
      simpa only [E, rightLeftRecut] using hbranch.2.2.1
    have hfirstTop : E.first.top = D.second.top := by
      simpa only [E, rightLeftRecut] using hdata.recut_sides.1
    have hsecondTop : E.second.top = D.first.top := by
      simpa only [E, rightLeftRecut] using hdata.recut_sides.2
    have hturnParts :
        s ∈ Grid.cIco D.first.bottom D.first.top ∪
          Grid.cIco D.first.top D.second.top := by
      rw [Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hbranch.1]
      exact hturnWhole
    have hturnFirst : s ∈ Grid.cIco E.first.bottom E.first.top := by
      rw [Finset.mem_union] at hturnParts
      rcases hturnParts with hleft | hright
      · exact (hturn hleft).elim
      · rw [hfirstBottom, hfirstTop]
        exact hright
    exact ⟨hbranch.2.1, hfirstLeft, hbranch.2.2.1, hfirstTop,
      hbranch.2.2.2, hsecondTop, hturnFirst⟩
  · have : s ∈ Grid.cIco D.first.bottom D.first.top :=
      Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hturnWhole hbranch.1
    exact (hturn this).elim

private theorem rightLeftRecut_first_left
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    (D.rightLeftRecut hcommon hfirst hsecond hturn).first.left = D.second.left := by
  obtain ⟨_, hleft, _⟩ :=
    D.rightLeftRecut_geometry hcommon hfirst hsecond hturn
  exact hleft

private theorem rightLeftRecut_first_turn_mem
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    s ∈ Grid.cIco (D.rightLeftRecut hcommon hfirst hsecond hturn).first.bottom
      (D.rightLeftRecut hcommon hfirst hsecond hturn).first.top := by
  obtain ⟨_, _, _, _, _, _, hturn'⟩ :=
    D.rightLeftRecut_geometry hcommon hfirst hsecond hturn
  exact hturn'

/-- Promote the first generic recut rectangle to an initial-side pentagon. This is the recut of
a mixed `right = left` overlap outside the turn-point-cut family. -/
noncomputable def recutRightEqLeft
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    GridInitialPentagonRectangleDecomposition a s x z where
  toGridTwoStepDecomposition := D.rightLeftRecut hcommon hfirst hsecond hturn
  first_left_eq := (D.rightLeftRecut_first_left hcommon hfirst hsecond hturn).trans
    D.second_left_eq
  first_turn_mem := D.rightLeftRecut_first_turn_mem hcommon hfirst hsecond hturn

/-- Forgetting the turn row of the promoted decomposition recovers the generic recut. -/
@[simp]
theorem recutRightEqLeft_toGridRectangleDecomposition
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    (D.recutRightEqLeft hcommon hfirst hsecond hturn).toGridRectangleDecomposition =
      D.toGridRectangleDecomposition.recut
        (D.toGridRectangleDecomposition.hasOneCommonSide_of_right_eq_left hcommon
          (D.first_left_ne_second_right_of_right_eq_left hcommon hturn))
        hfirst (by
          rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] at hsecond ⊢
          simpa only [D.pentagon_toGridRectangleBetween] using hsecond) :=
  (rfl)

/-- The promoted decomposition is an empty-rectangle recut of the original composite domain. -/
theorem isRecut_recutRightEqLeft
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    D.toGridRectangleDecomposition.IsRecut
      (D.recutRightEqLeft hcommon hfirst hsecond hturn).toGridRectangleDecomposition := by
  rw [recutRightEqLeft_toGridRectangleDecomposition]
  exact D.toGridRectangleDecomposition.isRecut_recut _ _ _

/-- The promoted recut of a mixed `right = left` overlap swaps the rows of the two original top
sides. Its initial-side pentagon starts on the replaced grid line and spans the rows from the
original rectangle's top to the original pentagon's top, while its rectangle spans the rows of the
original rectangle. -/
theorem recutRightEqLeft_geometry
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    let E := D.recutRightEqLeft hcommon hfirst hsecond hturn
    E.middle = x.swapRows D.first.top D.second.top ∧
      E.first.left = D.second.left ∧
        E.first.bottom = D.first.top ∧ E.first.top = D.second.top ∧
          E.second.bottom = D.first.bottom ∧ E.second.top = D.first.top := by
  obtain ⟨hmiddle, hleft, hbottom, htop, hsecondBottom, hsecondTop, _⟩ :=
    D.rightLeftRecut_geometry hcommon hfirst hsecond hturn
  exact ⟨hmiddle, hleft, hbottom, htop, hsecondBottom, hsecondTop⟩

/-- In a mixed `right = left` overlap whose rectangle avoids the turn row, the rectangle's top row
lies strictly between its bottom row and the pentagon's top row: emptiness allows the reverse
order only when the pentagon's rows lie inside the rectangle's, which would put the turn row in
the rectangle. -/
theorem first_top_mem_cIoo_of_right_eq_left
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    D.first.top ∈ Grid.cIoo D.first.bottom D.second.top := by
  rcases (D.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_right_eq_left hcommon
      (D.first_left_ne_second_right_of_right_eq_left hcommon hturn) hfirst
      (D.underlying_second_isEmpty hsecond)).2 with h | h
  · exact h
  · have hturnWhole : s ∈ Grid.cIco D.first.bottom D.second.top := by
      simpa only [D.second_bottom_eq_first_bottom hcommon] using D.second_turn_mem
    exact (hturn (Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hturnWhole h)).elim

/-- The promoted recut of a mixed `right = left` overlap covers the squares of the original
domain with the same multiplicities, the rectangle of the commuted diagram being read in the
original diagram with the two columns next to the replaced line exchanged. -/
theorem coveredSquares_val_add_val_recutRightEqLeft
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco D.first.bottom D.first.top) :
    (D.recutRightEqLeft hcommon hfirst hsecond hturn).pentagon.coveredSquares.val +
        ((D.recutRightEqLeft hcommon hfirst hsecond hturn).second.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  obtain ⟨-, hEleft, hEbottom, hEtop, hE2bottom, hE2top⟩ :=
    D.recutRightEqLeft_geometry hcommon hfirst hsecond hturn
  have hrep := (D.isRecut_recutRightEqLeft hcommon hfirst hsecond hturn).isRepartition
  have hEturn := (D.recutRightEqLeft hcommon hfirst hsecond hturn).first_turn_mem
  set E := D.recutRightEqLeft hcommon hfirst hsecond hturn
  rw [hEbottom, hEtop] at hEturn
  have hrow := D.first_top_mem_cIoo_of_right_eq_left hcommon hfirst hsecond hturn
  have hD2bottom := D.second_bottom_eq_first_bottom hcommon
  have hb : D.second.left = finRotate n a := D.second_left_eq
  -- Both pentagons start on the replaced line and the rectangle ends there, so the rectangle
  -- covers the column before that line but not the column after it, while the pentagons cover
  -- the column after it but not the column before it.
  have haD1 : a ∈ Grid.cIco D.first.left D.first.right := by
    rw [hcommon, hb]
    exact Grid.self_mem_cIco_finRotate (by rw [← hb, ← hcommon]; exact D.first.left_ne_right)
  have hbD1 : finRotate n a ∉ Grid.cIco D.first.left D.first.right := by
    rw [hcommon, hb]
    exact Grid.right_notMem_cIco _ _
  have haD2 : a ∉ Grid.cIco D.second.left D.second.right := by
    rw [hb]
    simp
  have hbD2 : finRotate n a ∈ Grid.cIco D.second.left D.second.right := by
    rw [← hb]
    exact Grid.left_mem_cIco D.second.left_ne_right
  have haE1 : a ∉ Grid.cIco E.first.left E.first.right := by
    rw [hEleft, hb]
    simp
  have hbE1 : finRotate n a ∈ Grid.cIco E.first.left E.first.right := by
    rw [← hb, ← hEleft]
    exact Grid.left_mem_cIco E.first.left_ne_right
  -- The pentagon's rows are those of the rectangle followed by those of the new pentagon.
  have hsplit (t : Fin n) :
      (if t ∈ Grid.cIco D.first.bottom D.second.top then 1 else 0 : ℕ) =
        (if t ∈ Grid.cIco D.first.bottom D.first.top then 1 else 0) +
          if t ∈ Grid.cIco D.first.top D.second.top then 1 else 0 := by
    have hrow' := hrow
    simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hrow' ⊢
    split_ifs at hrow' ⊢ <;> omega
  have hcounts := fun q => congrArg (Multiset.count q) hrep.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _),
    Finset.mem_val] at hcounts
  dsimp only [toGridRectangleDecomposition,
    GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition] at hcounts
  refine D.coveredSquares_val_add_val_eq_of_isRepartition E hrep (fun t => ?_) (fun t => ?_)
  -- In the column before the replaced line, the new rectangle covers the rows of the original
  -- rectangle.
  · have h := hcounts (finRotate n a, t)
    simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares,
      ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, haD1, hbD1, hbD2, hbE1,
      true_and, false_and, hEbottom, hEtop, hD2bottom, ↓reduceIte] at h ⊢
    have := hsplit t
    omega
  -- In the column after it, the new rectangle again covers the rows of the original rectangle,
  -- and the two pentagons meet the rows below the turn row in complementary parts.
  · have h := hcounts (a, t)
    simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares,
      ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, haD1, hbD1, haD2, haE1,
      true_and, false_and, hEbottom, hD2bottom, ↓reduceIte] at h ⊢
    have := Grid.ite_mem_cIco_eq_add_of_mem_cIoo hrow hEturn t
    omega

end TauCeti.GridRectangleInitialPentagonDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

section Weights

variable (R : Type*) [CommSemiring R]

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.right = D.second.left)
  (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
  (hturn : C.turnRow ∉ Grid.cIco D.first.bottom D.first.top)

/-- Recutting a mixed `right = left` overlap outside the turn-point cut preserves the weight. -/
@[simp]
theorem initialPentagonRectangleWeight_recutRightEqLeft :
    G.initialPentagonRectangleWeight C R (D.recutRightEqLeft hcommon hfirst hsecond hturn) =
      G.rectangleInitialPentagonWeight C R D :=
  G.initialPentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_val_recutRightEqLeft hcommon hfirst hsecond hturn)

end Weights

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.right = D.second.left)
  (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
  (hturn : C.turnRow ∉ Grid.cIco D.first.bottom D.first.top)

/-- The recut of a counted mixed `right = left` overlap outside the turn-point cut is a counted
initial-side pentagon--rectangle domain. -/
theorem recutRightEqLeft_mem_initialPentagonRectangleDecompositions
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) :
    D.recutRightEqLeft hcommon hfirst hsecond hturn ∈
      G.initialPentagonRectangleDecompositions C x z :=
  have hrecut := D.isRecut_recutRightEqLeft hcommon hfirst hsecond hturn
  G.mem_initialPentagonRectangleDecompositions_of_val_add_val_eq C hD hrecut.isEmpty_first
    hrecut.isEmpty_second
    (D.coveredSquares_val_add_val_recutRightEqLeft hcommon hfirst hsecond hturn)

/-! ### Cancelling the mixed `right = left` terms -/

variable (x z) in
/-- The counted rectangle--initial-side pentagon decompositions whose rectangle ends where the
pentagon starts and does not span the turn row: the mixed `right = left` overlaps outside the
turn-point cut. -/
noncomputable def initialPentagonRightLeftOverlapSources :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectangleInitialPentagonDecompositions C x z).filter fun D =>
    D.first.right = D.second.left ∧ C.turnRow ∉ Grid.cIco D.first.bottom D.first.top

/-- Membership in the mixed `right = left` source family records counting, the common side and
that the rectangle avoids the turn row. -/
@[simp]
theorem mem_initialPentagonRightLeftOverlapSources :
    D ∈ G.initialPentagonRightLeftOverlapSources C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧
        D.first.right = D.second.left ∧ C.turnRow ∉ Grid.cIco D.first.bottom D.first.top := by
  classical
  simp [initialPentagonRightLeftOverlapSources]

private theorem initialPentagonRightLeftOverlapSource_data
    (hD : D ∈ G.initialPentagonRightLeftOverlapSources C x z) :
    D.first.right = D.second.left ∧ C.turnRow ∉ Grid.cIco D.first.bottom D.first.top ∧
      D.first.IsEmpty ∧ D.pentagon.IsEmpty := by
  obtain ⟨hcounted, hcommon, hturn⟩ := (G.mem_initialPentagonRightLeftOverlapSources C D).1 hD
  rw [G.mem_rectangleInitialPentagonDecompositions, G.mem_unblockedRectangles,
    G.mem_initialPentagons] at hcounted
  exact ⟨hcommon, hturn, hcounted.1.1, hcounted.2.1⟩

private noncomputable def initialPentagonRightLeftOverlapPartner
    (D : {D // D ∈ G.initialPentagonRightLeftOverlapSources C x z}) :
    GridInitialPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutRightEqLeft
    (G.initialPentagonRightLeftOverlapSource_data C D.val D.property).1
    (G.initialPentagonRightLeftOverlapSource_data C D.val D.property).2.2.1
    (G.initialPentagonRightLeftOverlapSource_data C D.val D.property).2.2.2
    (G.initialPentagonRightLeftOverlapSource_data C D.val D.property).2.1

private theorem initialPentagonRightLeftOverlapPartner_isRecut
    (D : {D // D ∈ G.initialPentagonRightLeftOverlapSources C x z}) :
    D.val.toGridRectangleDecomposition.IsRecut
      (G.initialPentagonRightLeftOverlapPartner C D).toGridRectangleDecomposition :=
  D.val.isRecut_recutRightEqLeft _ _ _ _

/-- A source has exactly one common side and two empty underlying rectangles, so it has a unique
recut. -/
private theorem initialPentagonRightLeftOverlapSource_recut_data
    (hD : D ∈ G.initialPentagonRightLeftOverlapSources C x z) :
    D.toGridRectangleDecomposition.HasOneCommonSide ∧ D.first.IsEmpty ∧ D.second.IsEmpty := by
  obtain ⟨hcommon, hturn, hfirst, hsecond⟩ :=
    G.initialPentagonRightLeftOverlapSource_data C D hD
  refine ⟨D.toGridRectangleDecomposition.hasOneCommonSide_of_right_eq_left hcommon
    (D.first_left_ne_second_right_of_right_eq_left hcommon hturn), hfirst, ?_⟩
  rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] at hsecond ⊢
  simpa only [D.pentagon_toGridRectangleBetween] using hsecond

private theorem initialPentagonRightLeftOverlapPartner_injective :
    Function.Injective (G.initialPentagonRightLeftOverlapPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.initialPentagonRightLeftOverlapPartner_isRecut C D
  have hE := G.initialPentagonRightLeftOverlapPartner_isRecut C E
  rw [← h] at hE
  obtain ⟨honeD, hfD, hsD⟩ :=
    G.initialPentagonRightLeftOverlapSource_recut_data C D.val D.property
  obtain ⟨honeE, hfE, hsE⟩ :=
    G.initialPentagonRightLeftOverlapSource_recut_data C E.val E.property
  have hbackD := hD.symm honeD hfD hsD
  have hbackE := hE.symm honeE hfE hsE
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

variable (x z) in
/-- The initial-side pentagon--rectangle partners obtained by recutting the mixed `right = left`
sources: the exact recut image of `GridDiagram.initialPentagonRightLeftOverlapSources`. -/
noncomputable def initialPentagonRightLeftOverlapPartners :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonRightLeftOverlapSources C x z).attach.map
    ⟨G.initialPentagonRightLeftOverlapPartner C,
      G.initialPentagonRightLeftOverlapPartner_injective C⟩

/-- An initial-side pentagon--rectangle term is a partner exactly when its underlying rectangles
are the recut of a mixed `right = left` source. -/
@[simp]
theorem mem_initialPentagonRightLeftOverlapPartners
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonRightLeftOverlapPartners C x z ↔
      ∃ D ∈ G.initialPentagonRightLeftOverlapSources C x z,
        D.toGridRectangleDecomposition.IsRecut E.toGridRectangleDecomposition := by
  classical
  simp only [initialPentagonRightLeftOverlapPartners, Finset.mem_map, Finset.mem_attach,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.initialPentagonRightLeftOverlapPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨hone, hf, hs⟩ := G.initialPentagonRightLeftOverlapSource_recut_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    exact (D.toGridRectangleDecomposition.existsUnique_isRecut hone hf hs).unique
      (G.initialPentagonRightLeftOverlapPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Each mixed `right = left` source belongs to the rectangle--initial-side pentagon sum. -/
theorem initialPentagonRightLeftOverlapSources_subset :
    G.initialPentagonRightLeftOverlapSources C x z ⊆
      G.rectangleInitialPentagonDecompositions C x z := fun D hD =>
  ((G.mem_initialPentagonRightLeftOverlapSources C D).1 hD).1

/-- Each partner belongs to the initial-side pentagon--rectangle sum. -/
theorem initialPentagonRightLeftOverlapPartners_subset :
    G.initialPentagonRightLeftOverlapPartners C x z ⊆
      G.initialPentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [initialPentagonRightLeftOverlapPartners] at hE
  obtain ⟨D, _, rfl⟩ := Finset.mem_map.mp hE
  exact G.recutRightEqLeft_mem_initialPentagonRectangleDecompositions C D.val _ _ _ _
    ((G.mem_initialPentagonRightLeftOverlapSources C D.val).1 D.property).1

variable (R : Type*) [CommSemiring R]

variable (x z) in
/-- Recutting identifies the total contribution of the mixed `right = left` sources with the
total contribution of their partners. -/
theorem sum_rectangleInitialPentagonWeight_rightLeftOverlapSources_eq_sum_partners :
    ∑ D ∈ G.initialPentagonRightLeftOverlapSources C x z,
        G.rectangleInitialPentagonWeight C R D =
      ∑ E ∈ G.initialPentagonRightLeftOverlapPartners C x z,
        G.initialPentagonRectangleWeight C R E := by
  classical
  rw [initialPentagonRightLeftOverlapPartners, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, initialPentagonRightLeftOverlapPartner,
    initialPentagonRectangleWeight_recutRightEqLeft, Finset.sum_attach]

variable (x z) in
open scoped Classical in
/-- In an equation between the rectangle--initial-side pentagon sum and the initial-side
pentagon--rectangle sum, each augmented by further terms, the mixed `right = left` sources and
their partners can be removed. -/
theorem add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_rightLeftOverlap
    [IsCancelAdd R] (A B : MvPolynomial (Fin n) R) :
    A + ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
          G.rectangleInitialPentagonWeight C R D =
        B + ∑ E ∈ G.initialPentagonRectangleDecompositions C x z,
          G.initialPentagonRectangleWeight C R E ↔
      A + ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z \
            G.initialPentagonRightLeftOverlapSources C x z,
          G.rectangleInitialPentagonWeight C R D =
        B + ∑ E ∈ G.initialPentagonRectangleDecompositions C x z \
            G.initialPentagonRightLeftOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E := by
  rw [← Finset.sum_sdiff (G.initialPentagonRightLeftOverlapSources_subset C)
      (f := G.rectangleInitialPentagonWeight C R),
    ← Finset.sum_sdiff (G.initialPentagonRightLeftOverlapPartners_subset C)
      (f := G.initialPentagonRectangleWeight C R),
    G.sum_rectangleInitialPentagonWeight_rightLeftOverlapSources_eq_sum_partners C x z R,
    ← add_assoc, ← add_assoc]
  exact add_right_cancel_iff

end TauCeti.GridDiagram
