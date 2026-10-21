/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Recutting an initial-side pentagon across a mixed common side

Consider a rectangle followed by a commutation pentagon turning on its initial side. This file
treats the mixed overlap in which the rectangle's initial side is the pentagon's terminal side.
The generic empty-rectangle recut always starts on the replaced grid line. If its first rectangle
contains the turn row, it promotes to an initial-side pentagon followed by a rectangle. Otherwise
the second recut rectangle also starts on the replaced line and contains the turn row, so it
promotes to a rectangle followed by an initial-side pentagon.

Thus every such mixed overlap stays among the two coefficient sums involving initial-side
pentagons. When the first recut rectangle contains the turn row, both composite domains cover the
same squares with multiplicity after exchanging the two commuted columns in the final rectangle.
The recut is therefore counted with the same monomial weight. The finite source and partner
families below cancel this cross-sum branch in the grid-commutation chain-map equation. The other
branch stays in the rectangle--initial-side-pentagon sum and is paired from its common-initial-side
orientation in `TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.SameSum`.

## Main definitions

* `TauCeti.GridRectangleInitialPentagonDecomposition.recutLeftEqRightFirst` and
  `recutLeftEqRightSecond`: the two promoted recuts.
* `TauCeti.GridDiagram.initialPentagonLeftRightOverlapSources`: the counted mixed overlaps whose
  recut promotes its first rectangle to an initial-side pentagon.
* `TauCeti.GridDiagram.initialPentagonLeftRightOverlapPartners`: their recuts in the opposite
  coefficient sum.

## Main results

* `TauCeti.GridRectangleInitialPentagonDecomposition.recutLeftEqRight_turn`: the turn row lies
  in the first recut rectangle, or it lies in the second and that rectangle starts on the
  replaced line.
* `TauCeti.GridRectangleInitialPentagonDecomposition.
  coveredSquares_val_add_val_recutLeftEqRightFirst`: both composite domains cover the same squares
  with multiplicity.
* `TauCeti.GridDiagram.initialPentagonRectangleWeight_recutLeftEqRightFirst` and
  `recutLeftEqRightFirst_mem_initialPentagonRectangleDecompositions`: the recut has the same
  weight and is counted.
* `TauCeti.GridDiagram.
  add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_leftRightOverlap`: the sources and
  their recuts can be removed from the two sides of the coefficient equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

private theorem underlying_first_isEmpty
    (D : GridRectangleInitialPentagonDecomposition a s x z) (h : D.first.IsEmpty) :
    D.toGridRectangleDecomposition.first.IsEmpty :=
  h

private theorem underlying_second_isEmpty
    (D : GridRectangleInitialPentagonDecomposition a s x z) (h : D.pentagon.IsEmpty) :
    D.toGridRectangleDecomposition.second.IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] at h ⊢
  simpa only [D.pentagon_toGridRectangleBetween] using h

/-- The generic empty-rectangle recut of a mixed overlap whose first initial side is the second
terminal side. -/
noncomputable def leftRightRecut
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    GridRectangleDecomposition x z :=
  D.toGridRectangleDecomposition.recut
    (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_right hcommon hother)
    (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)

/-- The generic construction is an empty-rectangle recut of the original composite domain. -/
theorem isRecut_leftRightRecut
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    D.toGridRectangleDecomposition.IsRecut (D.leftRightRecut hcommon hother hfirst hsecond) :=
  D.toGridRectangleDecomposition.isRecut_recut _ _ _

private theorem second_bottom_eq
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left) :
    D.second.bottom = x D.second.left := by
  rw [GridRectangleBetween.bottom_def]
  exact D.first.map_of_ne D.second.left
    (fun h => D.second.left_ne_right (h.trans hcommon)) hother.symm

private theorem second_top_eq_first_top
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right) : D.second.top = D.first.top := by
  rw [GridRectangleBetween.top_def, hcommon.symm, GridRectangleBetween.top_def]
  exact D.first.map_left

/-- The first rectangle in the generic recut starts on the replaced grid line. -/
@[simp]
theorem leftRightRecut_first_left
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    (D.leftRightRecut hcommon hother hfirst hsecond).first.left = D.second.left := by
  let E := D.leftRightRecut hcommon hother hfirst hsecond
  have hdata := D.toGridRectangleDecomposition.isRecutOfLeftEqRight_recut hcommon
    (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_right hcommon hother)
    (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)
  have hbottom : E.first.bottom = D.second.bottom := by
    simpa only [E, leftRightRecut] using hdata.recut_sides.1
  apply x.toPerm.injective
  rw [← GridRectangleBetween.bottom_def, hbottom, D.second_bottom_eq hcommon hother]

/-- In a mixed `left = right` overlap, either the first recut rectangle contains the turn row,
or the second recut rectangle starts on the replaced line and contains the turn row. -/
theorem recutLeftEqRight_turn
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    let E := D.leftRightRecut hcommon hother hfirst hsecond
    (s ∈ Grid.cIco E.first.bottom E.first.top) ∨
      (E.second.left = D.second.left ∧ s ∈ Grid.cIco E.second.bottom E.second.top) := by
  let E := D.leftRightRecut hcommon hother hfirst hsecond
  by_cases hturn : s ∈ Grid.cIco E.first.bottom E.first.top
  · exact Or.inl hturn
  · right
    have hdata := D.toGridRectangleDecomposition.isRecutOfLeftEqRight_recut hcommon
      (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_right hcommon hother)
      (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)
    have hfirstBottom : E.first.bottom = D.second.bottom := by
      simpa only [E, leftRightRecut] using hdata.recut_sides.1
    have hsecondBottom : E.second.bottom = D.first.bottom := by
      simpa only [E, leftRightRecut] using hdata.recut_sides.2
    rcases hdata.recut_branch with hbranch | hbranch
    · have hmiddle : E.middle = x.swapRows D.second.bottom D.first.bottom := by
        simpa only [E, leftRightRecut] using hbranch.2.1
      have hfirstTop : E.first.top = D.first.bottom := by
        simpa only [E, leftRightRecut] using hbranch.2.2.1
      have hsecondTop : E.second.top = D.first.top := by
        simpa only [E, leftRightRecut] using hbranch.2.2.2
      have hsecondLeft : E.second.left = D.second.left := by
        apply E.middle.toPerm.injective
        rw [← GridRectangleBetween.bottom_def, hsecondBottom, hmiddle,
          GridState.swapRows_apply, D.second_bottom_eq hcommon hother,
          Equiv.swap_apply_left]
      refine ⟨hsecondLeft, ?_⟩
      have hturnWhole : s ∈ Grid.cIco D.second.bottom D.first.top := by
        simpa only [D.second_top_eq_first_top hcommon] using D.second_turn_mem
      have hparts := Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hbranch.1
      have hturnParts :
          s ∈ Grid.cIco D.second.bottom D.first.bottom ∪
            Grid.cIco D.first.bottom D.first.top := by
        rw [hparts]
        exact hturnWhole
      rw [Finset.mem_union] at hturnParts
      rcases hturnParts with hleft | hright
      · exact (hturn (by simpa only [hfirstBottom, hfirstTop] using hleft)).elim
      · rw [hsecondBottom, hsecondTop]
        exact hright
    · have hfirstTop : E.first.top = D.first.top := by
        simpa only [E, leftRightRecut] using hbranch.2.2.1
      have hturnWhole : s ∈ Grid.cIco D.second.bottom D.first.top := by
        simpa only [D.second_top_eq_first_top hcommon] using D.second_turn_mem
      exact (hturn (by simpa only [hfirstBottom, hfirstTop] using hturnWhole)).elim

/-- Promote the first generic recut rectangle to an initial-side pentagon when it contains the
turn row. -/
noncomputable def recutLeftEqRightFirst
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
      (D.leftRightRecut hcommon hother hfirst hsecond).first.top) :
    GridInitialPentagonRectangleDecomposition a s x z where
  toGridTwoStepDecomposition := D.leftRightRecut hcommon hother hfirst hsecond
  first_left_eq := (D.leftRightRecut_first_left hcommon hother hfirst hsecond).trans
    D.second_left_eq
  first_turn_mem := hturn

/-- Promote the second generic recut rectangle to an initial-side pentagon when the first does
not contain the turn row. -/
noncomputable def recutLeftEqRightSecond
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
      (D.leftRightRecut hcommon hother hfirst hsecond).first.top) :
    GridRectangleInitialPentagonDecomposition a s x z where
  toGridTwoStepDecomposition := D.leftRightRecut hcommon hother hfirst hsecond
  second_left_eq := (D.recutLeftEqRight_turn hcommon hother hfirst hsecond).resolve_left hturn |>.1
    |>.trans D.second_left_eq
  second_turn_mem :=
    (D.recutLeftEqRight_turn hcommon hother hfirst hsecond).resolve_left hturn |>.2

/-- Forgetting the first promoted pentagon gives the generic recut. -/
@[simp]
theorem recutLeftEqRightFirst_toGridRectangleDecomposition
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
      (D.leftRightRecut hcommon hother hfirst hsecond).first.top) :
    (D.recutLeftEqRightFirst hcommon hother hfirst hsecond hturn).toGridRectangleDecomposition =
      D.leftRightRecut hcommon hother hfirst hsecond :=
  (rfl)

/-- Forgetting the second promoted pentagon gives the generic recut. -/
@[simp]
theorem recutLeftEqRightSecond_toGridRectangleDecomposition
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∉ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
      (D.leftRightRecut hcommon hother hfirst hsecond).first.top) :
    (D.recutLeftEqRightSecond hcommon hother hfirst hsecond hturn).toGridRectangleDecomposition =
      D.leftRightRecut hcommon hother hfirst hsecond :=
  (rfl)

/-- When the first rectangle of the mixed `left = right` recut contains the turn row, promoting
it to an initial-side pentagon preserves the composite domain with multiplicity. The rectangle
of the commuted diagram is read in the original diagram with the two columns next to the
replaced line exchanged. -/
theorem coveredSquares_val_add_val_recutLeftEqRightFirst
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.right)
    (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hturn : s ∈ Grid.cIco
      (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
      (D.leftRightRecut hcommon hother hfirst hsecond).first.top) :
    (D.recutLeftEqRightFirst hcommon hother hfirst hsecond hturn).pentagon.coveredSquares.val +
        ((D.recutLeftEqRightFirst hcommon hother hfirst hsecond hturn).second.toGridRectangle
          |>.coveredSquares.map
            ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  let E := D.recutLeftEqRightFirst hcommon hother hfirst hsecond hturn
  have hrecut := D.isRecut_leftRightRecut hcommon hother hfirst hsecond
  have hEunder : E.toGridRectangleDecomposition =
      D.leftRightRecut hcommon hother hfirst hsecond := by
    exact D.recutLeftEqRightFirst_toGridRectangleDecomposition
      hcommon hother hfirst hsecond hturn
  have hrep : D.toGridRectangleDecomposition.IsRepartition E.toGridRectangleDecomposition := by
    rw [hEunder]
    exact hrecut.isRepartition
  have hEbottom : E.first.bottom = D.second.bottom := by
    -- `toGridRectangleDecomposition` is the abbreviation for the parent two-step decomposition,
    -- so `E.first` is its first rectangle; restate the goal through it for `hEunder` to rewrite.
    change E.toGridRectangleDecomposition.first.bottom = _
    rw [hEunder]
    exact (D.toGridRectangleDecomposition.isRecutOfLeftEqRight_recut hcommon
      (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_right hcommon hother)
      (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)).recut_sides.1
  -- The original rectangle has neither endpoint on the replaced line, so it covers the two
  -- adjacent commuted columns together or misses them together.
  have hD1ab :
      finRotate n a ∈ Grid.cIco D.first.left D.first.right ↔
        a ∈ Grid.cIco D.first.left D.first.right :=
    Grid.mem_cIco_finRotate_iff_of_ne
      (by simpa only [← D.second_left_eq, hcommon] using D.second.left_ne_right.symm)
      (by simpa only [← D.second_left_eq] using hother)
  have haD2 : a ∉ Grid.cIco D.second.left D.second.right := by
    rw [D.second_left_eq]
    simp
  have hbD2 : finRotate n a ∈ Grid.cIco D.second.left D.second.right := by
    rw [← D.second_left_eq]
    exact Grid.left_mem_cIco D.second.left_ne_right
  have haE1 : a ∉ Grid.cIco E.first.left E.first.right := by
    rw [E.first_left_eq]
    simp
  have hbE1 : finRotate n a ∈ Grid.cIco E.first.left E.first.right := by
    rw [← E.first_left_eq]
    exact Grid.left_mem_cIco E.first.left_ne_right
  have hcounts := fun q => congrArg (Multiset.count q) hrep.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _),
    Finset.mem_val] at hcounts
  dsimp only [toGridRectangleDecomposition,
    GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition] at hcounts
  -- Away from the two commuted columns the generic repartition already proves the claim. In
  -- these columns, split each pentagon's row interval at the common turn row.
  refine D.coveredSquares_val_add_val_eq_of_isRepartition E hrep (fun t => ?_) (fun t => ?_)
  -- Column `finRotate n a`: both underlying pentagons cover the column, and the two whole row
  -- intervals split into their below-turn and above-turn pieces.
  · have h := hcounts (finRotate n a, t)
    have hD1count :
        (if (finRotate n a, t) ∈ D.first.toGridRectangle.coveredSquares then 1 else 0 : ℕ) =
          if (a, t) ∈ D.first.toGridRectangle.coveredSquares then 1 else 0 := by
      simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares,
        ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, hD1ab]
    have hD1b :
        (if (finRotate n a, t) ∈ D.first.toGridRectangle.coveredSquares then 1 else 0 : ℕ) =
          if finRotate n a ∈ Grid.cIco D.first.left D.first.right ∧
              t ∈ Grid.cIco D.first.bottom D.first.top then 1 else 0 := by
      simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares,
        ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def]
    have hE2b :
        (if (finRotate n a, t) ∈ E.second.toGridRectangle.coveredSquares then 1 else 0 : ℕ) =
          if finRotate n a ∈ Grid.cIco E.second.left E.second.right ∧
              t ∈ Grid.cIco E.second.bottom E.second.top then 1 else 0 := by
      simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares,
        ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def]
    have hsplitE := Grid.ite_mem_cIco_eq_add_add E.first_turn_mem t
    have hsplitD := Grid.ite_mem_cIco_eq_add_add D.second_turn_mem t
    rw [hEbottom] at hsplitE
    simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares,
      ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, hbD2, hbE1,
      true_and, hEbottom] at h
    omega
  -- Column `a`: neither underlying pentagon rectangle covers the column, so repartition and
  -- adjacency identify the two rectangle contributions directly.
  · have h := hcounts (a, t)
    have hD1expanded :
        (if finRotate n a ∈ Grid.cIco D.first.left D.first.right ∧
              t ∈ Grid.cIco D.first.bottom D.first.top then 1 else 0 : ℕ) =
          if a ∈ Grid.cIco D.first.left D.first.right ∧
              t ∈ Grid.cIco D.first.bottom D.first.top then 1 else 0 := by
      simp only [hD1ab]
    simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares,
      ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, haD2, haE1,
      false_and, hEbottom] at h ⊢
    omega

end TauCeti.GridRectangleInitialPentagonDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

section Weights

variable (R : Type*) [CommSemiring R]

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.left = D.second.right)
  (hother : D.first.right ≠ D.second.left)
  (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
  (hturn : C.turnRow ∈ Grid.cIco
    (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
    (D.leftRightRecut hcommon hother hfirst hsecond).first.top)

/-- Promoting the first recut rectangle in a mixed `left = right` overlap preserves the
monomial contribution. -/
@[simp]
theorem initialPentagonRectangleWeight_recutLeftEqRightFirst :
    G.initialPentagonRectangleWeight C R
        (D.recutLeftEqRightFirst hcommon hother hfirst hsecond hturn) =
      G.rectangleInitialPentagonWeight C R D :=
  G.initialPentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_val_recutLeftEqRightFirst
      hcommon hother hfirst hsecond hturn)

end Weights

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.left = D.second.right)
  (hother : D.first.right ≠ D.second.left)
  (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
  (hturn : C.turnRow ∈ Grid.cIco
    (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
    (D.leftRightRecut hcommon hother hfirst hsecond).first.top)

/-- A counted mixed `left = right` domain whose first recut rectangle contains the turn row has
a counted initial-side-pentagon--rectangle recut. -/
theorem recutLeftEqRightFirst_mem_initialPentagonRectangleDecompositions
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) :
    D.recutLeftEqRightFirst hcommon hother hfirst hsecond hturn ∈
      G.initialPentagonRectangleDecompositions C x z := by
  have hrecut : D.toGridRectangleDecomposition.IsRecut
      (D.recutLeftEqRightFirst hcommon hother hfirst hsecond hturn).toGridRectangleDecomposition :=
    by
      rw [D.recutLeftEqRightFirst_toGridRectangleDecomposition]
      exact D.isRecut_leftRightRecut hcommon hother hfirst hsecond
  exact G.mem_initialPentagonRectangleDecompositions_of_val_add_val_eq C hD
    hrecut.isEmpty_first hrecut.isEmpty_second
    (D.coveredSquares_val_add_val_recutLeftEqRightFirst
      hcommon hother hfirst hsecond hturn)

/-! ### Cancelling the mixed `left = right` cross terms -/

variable (x z) in
/-- The counted mixed `left = right` rectangle--initial-side-pentagon domains whose recut has the
turn row in its first rectangle, so that it promotes to an initial-side pentagon followed by a
rectangle. -/
noncomputable def initialPentagonLeftRightOverlapSources :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectangleInitialPentagonDecompositions C x z).filter fun D =>
    D.first.left = D.second.right ∧ D.first.right ≠ D.second.left ∧
      ∃ E : GridRectangleDecomposition x z,
        D.toGridRectangleDecomposition.IsRecut E ∧ C.turnRow ∈ Grid.cIco E.first.bottom E.first.top

/-- Membership in the mixed `left = right` source family records counting, the common-side
orientation, and that the unique recut has the turn row in its first rectangle. -/
@[simp]
theorem mem_initialPentagonLeftRightOverlapSources :
    D ∈ G.initialPentagonLeftRightOverlapSources C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧
        D.first.left = D.second.right ∧ D.first.right ≠ D.second.left ∧
          ∃ E : GridRectangleDecomposition x z,
            D.toGridRectangleDecomposition.IsRecut E ∧
              C.turnRow ∈ Grid.cIco E.first.bottom E.first.top := by
  classical
  simp [initialPentagonLeftRightOverlapSources]

private theorem initialPentagonLeftRightOverlapSource_data
    (hD : D ∈ G.initialPentagonLeftRightOverlapSources C x z) :
    ∃ (hcommon : D.first.left = D.second.right)
      (hother : D.first.right ≠ D.second.left)
      (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty),
      C.turnRow ∈ Grid.cIco
        (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
        (D.leftRightRecut hcommon hother hfirst hsecond).first.top := by
  obtain ⟨hcounted, hcommon, hother, E, hE, hturnE⟩ :=
    (G.mem_initialPentagonLeftRightOverlapSources C D).1 hD
  obtain ⟨hR, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D).1 hcounted
  have hfirst := ((G.mem_unblockedRectangles _).1 hR).1
  have hsecond := ((G.mem_initialPentagons _).1 hP).1
  have hcanonical := D.isRecut_leftRightRecut hcommon hother hfirst hsecond
  have heq : E = D.leftRightRecut hcommon hother hfirst hsecond :=
    (D.toGridRectangleDecomposition.existsUnique_isRecut
      (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_right hcommon hother)
      (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)).unique
      hE hcanonical
  subst E
  exact ⟨hcommon, hother, hfirst, hsecond, hturnE⟩

private structure InitialPentagonLeftRightOverlapData
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) where
  hcommon : D.first.left = D.second.right
  hother : D.first.right ≠ D.second.left
  hfirst : D.first.IsEmpty
  hsecond : D.pentagon.IsEmpty
  hturn : C.turnRow ∈ Grid.cIco
    (D.leftRightRecut hcommon hother hfirst hsecond).first.bottom
    (D.leftRightRecut hcommon hother hfirst hsecond).first.top

private theorem initialPentagonLeftRightOverlapData
    (D : {D // D ∈ G.initialPentagonLeftRightOverlapSources C x z}) :
    InitialPentagonLeftRightOverlapData G C D.val := by
  obtain ⟨hcommon, hother, hfirst, hsecond, hturn⟩ :=
    G.initialPentagonLeftRightOverlapSource_data C D.val D.property
  exact ⟨hcommon, hother, hfirst, hsecond, hturn⟩

private noncomputable def initialPentagonLeftRightOverlapPartner
    (D : {D // D ∈ G.initialPentagonLeftRightOverlapSources C x z}) :
    GridInitialPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutLeftEqRightFirst
    (G.initialPentagonLeftRightOverlapData C D).hcommon
    (G.initialPentagonLeftRightOverlapData C D).hother
    (G.initialPentagonLeftRightOverlapData C D).hfirst
    (G.initialPentagonLeftRightOverlapData C D).hsecond
    (G.initialPentagonLeftRightOverlapData C D).hturn

private theorem initialPentagonLeftRightOverlapPartner_isRecut
    (D : {D // D ∈ G.initialPentagonLeftRightOverlapSources C x z}) :
    D.val.toGridRectangleDecomposition.IsRecut
      (G.initialPentagonLeftRightOverlapPartner C D).toGridRectangleDecomposition := by
  unfold initialPentagonLeftRightOverlapPartner
  rw [D.val.recutLeftEqRightFirst_toGridRectangleDecomposition]
  exact D.val.isRecut_leftRightRecut _ _ _ _

private theorem initialPentagonLeftRightOverlapSource_recut_data
    (hD : D ∈ G.initialPentagonLeftRightOverlapSources C x z) :
    D.toGridRectangleDecomposition.HasOneCommonSide ∧ D.first.IsEmpty ∧ D.second.IsEmpty := by
  obtain ⟨hcommon, hother, hfirst, hsecond, -⟩ :=
    G.initialPentagonLeftRightOverlapSource_data C D hD
  refine ⟨D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_right hcommon hother,
    hfirst, ?_⟩
  rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] at hsecond ⊢
  simpa only [D.pentagon_toGridRectangleBetween] using hsecond

private theorem initialPentagonLeftRightOverlapPartner_injective :
    Function.Injective (G.initialPentagonLeftRightOverlapPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.initialPentagonLeftRightOverlapPartner_isRecut C D
  have hE := G.initialPentagonLeftRightOverlapPartner_isRecut C E
  rw [← h] at hE
  obtain ⟨honeD, hfD, hsD⟩ :=
    G.initialPentagonLeftRightOverlapSource_recut_data C D.val D.property
  obtain ⟨honeE, hfE, hsE⟩ :=
    G.initialPentagonLeftRightOverlapSource_recut_data C E.val E.property
  have hbackD := hD.symm honeD hfD hsD
  have hbackE := hE.symm honeE hfE hsE
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

variable (x z) in
/-- The initial-side-pentagon--rectangle recuts of the mixed `left = right` cross sources. -/
noncomputable def initialPentagonLeftRightOverlapPartners :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonLeftRightOverlapSources C x z).attach.map
    ⟨G.initialPentagonLeftRightOverlapPartner C,
      G.initialPentagonLeftRightOverlapPartner_injective C⟩

/-- An initial-side-pentagon--rectangle term is a partner exactly when its underlying rectangles
are the recut of a mixed `left = right` cross source. -/
@[simp]
theorem mem_initialPentagonLeftRightOverlapPartners
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonLeftRightOverlapPartners C x z ↔
      ∃ D ∈ G.initialPentagonLeftRightOverlapSources C x z,
        D.toGridRectangleDecomposition.IsRecut E.toGridRectangleDecomposition := by
  classical
  simp only [initialPentagonLeftRightOverlapPartners, Finset.mem_map, Finset.mem_attach,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.initialPentagonLeftRightOverlapPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨hone, hf, hs⟩ := G.initialPentagonLeftRightOverlapSource_recut_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    exact (D.toGridRectangleDecomposition.existsUnique_isRecut hone hf hs).unique
      (G.initialPentagonLeftRightOverlapPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Every mixed `left = right` cross source is counted in the
rectangle--initial-side-pentagon sum. -/
theorem initialPentagonLeftRightOverlapSources_subset :
    G.initialPentagonLeftRightOverlapSources C x z ⊆
      G.rectangleInitialPentagonDecompositions C x z := fun D hD =>
  ((G.mem_initialPentagonLeftRightOverlapSources C D).1 hD).1

/-- Every mixed `left = right` cross partner is counted in the
initial-side-pentagon--rectangle sum. -/
theorem initialPentagonLeftRightOverlapPartners_subset :
    G.initialPentagonLeftRightOverlapPartners C x z ⊆
      G.initialPentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [initialPentagonLeftRightOverlapPartners] at hE
  obtain ⟨D, _, rfl⟩ := Finset.mem_map.mp hE
  unfold initialPentagonLeftRightOverlapPartner
  exact G.recutLeftEqRightFirst_mem_initialPentagonRectangleDecompositions C D.val _ _ _ _ _
    ((G.mem_initialPentagonLeftRightOverlapSources C D.val).1 D.property).1

variable (R : Type*) [CommSemiring R]

variable (x z) in
/-- Recutting identifies the total contribution of the mixed `left = right` cross sources with
the total contribution of their partners. -/
theorem sum_rectangleInitialPentagonWeight_leftRightOverlapSources_eq_sum_partners :
    ∑ D ∈ G.initialPentagonLeftRightOverlapSources C x z,
        G.rectangleInitialPentagonWeight C R D =
      ∑ E ∈ G.initialPentagonLeftRightOverlapPartners C x z,
        G.initialPentagonRectangleWeight C R E := by
  classical
  rw [initialPentagonLeftRightOverlapPartners, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, initialPentagonLeftRightOverlapPartner,
    initialPentagonRectangleWeight_recutLeftEqRightFirst, Finset.sum_attach]

variable (x z) in
open scoped Classical in
/-- Remove the mixed `left = right` cross sources and their recut partners from an equation
between the two initial-side-pentagon composite sums. -/
theorem add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_leftRightOverlap
    [IsCancelAdd R] (A B : MvPolynomial (Fin n) R) :
    A + ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
          G.rectangleInitialPentagonWeight C R D =
        B + ∑ E ∈ G.initialPentagonRectangleDecompositions C x z,
          G.initialPentagonRectangleWeight C R E ↔
      A + ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z \
            G.initialPentagonLeftRightOverlapSources C x z,
          G.rectangleInitialPentagonWeight C R D =
        B + ∑ E ∈ G.initialPentagonRectangleDecompositions C x z \
            G.initialPentagonLeftRightOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E := by
  rw [← Finset.sum_sdiff (G.initialPentagonLeftRightOverlapSources_subset C)
      (f := G.rectangleInitialPentagonWeight C R),
    ← Finset.sum_sdiff (G.initialPentagonLeftRightOverlapPartners_subset C)
      (f := G.initialPentagonRectangleWeight C R),
    G.sum_rectangleInitialPentagonWeight_leftRightOverlapSources_eq_sum_partners C x z R,
    ← add_assoc, ← add_assoc]
  exact add_right_cancel_iff

end TauCeti.GridDiagram
