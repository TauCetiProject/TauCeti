/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.PentagonInitial.Basic

/-!
# Mixed partners of initial-side pentagon--rectangle self-pairs

An initial-side pentagon followed by a rectangle can recut within the same coefficient sum.
The common-initial-side sources have their rectangle's terminal side strictly inside the
pentagon's column interval. Their partners have a mixed common side: terminal for the pentagon
and initial for the rectangle. The turn row lies outside the arc from the rectangle's top row
to the pentagon's top row.

`GridDiagram.mem_initialPentagonRectangleInitialSelfPairs_iff_sides` characterizes the entire
self-pair family by these two geometric alternatives, without quantifying over recut sources.
This permits a partition of the pentagon--rectangle coefficient sum using side and row data;
the self-pair contribution cancels in characteristic two by the existing weighted pairing.

For the converse, the turn-row exclusion selects the branch of the generic empty-rectangle
recut in which both pieces start on the replaced line. Its first rectangle contains the turn
row and promotes to an initial-side pentagon. Recut uniqueness identifies its self-recut with
the original domain, so covered-square equality transfers counting in the reverse direction.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The argument uses the existing initial-side self-recut formalization in
`PentagonInitial.Basic`.
-/

public section

namespace TauCeti.GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The turn row of an empty common-initial-side pentagon--rectangle domain lies outside the
rectangle's rows. -/
theorem turn_notMem_cIco_second_of_left_eq_left
    (D : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : D.first.left = D.second.left) (hother : D.first.right ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    s ∉ Grid.cIco D.second.bottom D.second.top := by
  have hrow := (D.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
    hother hfirst hsecond).2
  rw [D.toGridRectangleDecomposition.second_bottom_eq_first_top_of_left_eq_left hcommon]
  exact fun hs => Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow)
    D.first_turn_mem hs

private theorem rightLeftSelfRecut_geometry
    (D : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hone : D.toGridRectangleDecomposition.HasOneCommonSide)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hturn : s ∉ Grid.cIco D.second.top D.first.top) :
    let E := D.toGridRectangleDecomposition.recut hone hfirst hsecond
    E.first.left = D.first.left ∧ E.second.left = D.first.left ∧
      E.first.bottom = D.first.bottom ∧ E.first.top = D.second.top := by
  intro E
  have hdata :=
    D.toGridRectangleDecomposition.isRecutOfRightEqLeft_recut hcommon hone hfirst hsecond
  obtain ⟨htop, -⟩ := hdata.recut_sides
  have hbottom := D.first.bottom_def
  rcases hdata.recut_branch with ⟨hrow, -, -, -⟩ | ⟨-, hmiddle, hfb, hsb⟩
  · -- This branch puts the entire pentagon row interval in the excluded arc.
    exact (hturn (Grid.cIco_subset_of_mem_cIoo (Grid.mem_cIoo_cyclic_right hrow)
      D.first_turn_mem)).elim
  · have hleft : E.first.left = D.first.left :=
      x.toPerm.injective (E.first.bottom_def.symm.trans (hfb.trans hbottom))
    have hsecondLeft : E.second.left = D.first.left := by
      apply x.toPerm.injective
      have h : x.swapRows D.first.bottom D.second.top E.second.left = D.second.top :=
        (congrArg (fun y : GridState n => y E.second.left) hmiddle).symm.trans
          (E.second.bottom_def.symm.trans hsb)
      rw [GridState.swapRows_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
      exact h.trans hbottom
    exact ⟨hleft, hsecondLeft, hfb, htop⟩

private theorem rightLeftSelfRecut_turn
    (D : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hone : D.toGridRectangleDecomposition.HasOneCommonSide)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hturn : s ∉ Grid.cIco D.second.top D.first.top) :
    s ∈ Grid.cIco (D.toGridRectangleDecomposition.recut hone hfirst hsecond).first.bottom
      (D.toGridRectangleDecomposition.recut hone hfirst hsecond).first.top := by
  obtain ⟨-, -, hbottom, htop⟩ :=
    D.rightLeftSelfRecut_geometry hcommon hone hfirst hsecond hturn
  rw [hbottom, htop]
  exact (Finset.mem_union.mp (Grid.cIco_subset_cIco_union_cIco
    (w := D.second.top) D.first_turn_mem)).resolve_left hturn

private noncomputable def rightLeftSelfRecut
    (D : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : D.first.right = D.second.left)
    (hone : D.toGridRectangleDecomposition.HasOneCommonSide)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hturn : s ∉ Grid.cIco D.second.top D.first.top) :
    GridInitialPentagonRectangleDecomposition a s x z where
  toGridTwoStepDecomposition := D.toGridRectangleDecomposition.recut hone hfirst hsecond
  first_left_eq := (D.rightLeftSelfRecut_geometry hcommon hone hfirst hsecond hturn).1.trans
    D.first_left_eq
  first_turn_mem := D.rightLeftSelfRecut_turn hcommon hone hfirst hsecond hturn

end TauCeti.GridInitialPentagonRectangleDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- A counted mixed pentagon--rectangle overlap whose turn row lies outside the arc from the
rectangle's top to the pentagon's top belongs to an initial-side self-pair. -/
theorem mem_initialPentagonRectangleInitialSelfPairs_of_right_eq_left
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.initialPentagonRectangleDecompositions C x z)
    (hcommon : D.first.right = D.second.left)
    (hone : D.toGridRectangleDecomposition.HasOneCommonSide)
    (hturn : C.turnRow ∉ Grid.cIco D.second.top D.first.top) :
    D ∈ G.initialPentagonRectangleInitialSelfPairs C x z := by
  obtain ⟨hfirst, hsecond⟩ := G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hD
  let E := D.rightLeftSelfRecut hcommon hone hfirst hsecond hturn
  -- The promotion only adds proof fields to the generic rectangle recut.
  have hErect :
      E.toGridRectangleDecomposition = D.toGridRectangleDecomposition.recut hone hfirst hsecond :=
    rfl
  have hrecut : D.toGridRectangleDecomposition.IsRecut E.toGridRectangleDecomposition := by
    rw [hErect]
    exact D.toGridRectangleDecomposition.isRecut_recut hone hfirst hsecond
  have hback := hrecut.symm hone hfirst hsecond
  have hEone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (D.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
  obtain ⟨hleft, hsecondLeft, -, -⟩ :=
    D.rightLeftSelfRecut_geometry hcommon hone hfirst hsecond hturn
  rw [← hErect] at hleft hsecondLeft
  have hEcommon : E.first.left = E.second.left := hleft.trans hsecondLeft.symm
  have hEcol : E.second.right ∈ Grid.cIoo E.first.left E.first.right := by
    have hdata := hback.isRecutOfLeftEqLeft hEone hEcommon
    rcases hdata.recut_branch with ⟨-, -, hright, -⟩ | ⟨hcol, -⟩
    · exact (E.first.left_ne_right (hleft.trans hright)).elim
    · exact hcol
  have hEq : E.recutInitialSelf hEcommon hEcol hrecut.isEmpty_first hrecut.isEmpty_second = D := by
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    exact (E.toGridRectangleDecomposition.existsUnique_isRecut hEone hrecut.isEmpty_first
      hrecut.isEmpty_second).unique
      (E.isRecut_recutInitialSelf hEcommon hEcol hrecut.isEmpty_first hrecut.isEmpty_second) hback
  have hsquares := E.coveredSquares_val_add_val_recutInitialSelf hEcommon hEcol
    hrecut.isEmpty_first hrecut.isEmpty_second
  rw [hEq] at hsquares
  have hEcounted :=
    G.mem_initialPentagonRectangleDecompositions_of_val_add_val_eq_initialPentagonRectangle C
      hD hrecut.isEmpty_first hrecut.isEmpty_second hsquares.symm
  exact (G.mem_initialPentagonRectangleInitialSelfPairs C D).2 (Or.inr
    ⟨E, (G.mem_initialPentagonRectangleInitialSelfSources C E).2 ⟨hEcounted, hEcommon, hEcol⟩,
      hback⟩)

/-- The initial-side pentagon--rectangle self-pairs are exactly the counted common-initial-side
sources and the counted mixed overlaps sharing one side whose turn row lies outside the arc from
the rectangle's top to the pentagon's top. -/
@[grind =]
theorem mem_initialPentagonRectangleInitialSelfPairs_iff_sides
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    D ∈ G.initialPentagonRectangleInitialSelfPairs C x z ↔
      D ∈ G.initialPentagonRectangleDecompositions C x z ∧
        ((D.first.left = D.second.left ∧
            D.second.right ∈ Grid.cIoo D.first.left D.first.right) ∨
          (D.first.right = D.second.left ∧ D.toGridRectangleDecomposition.HasOneCommonSide ∧
            C.turnRow ∉ Grid.cIco D.second.top D.first.top)) := by
  constructor
  · intro hpair
    refine ⟨G.initialPentagonRectangleInitialSelfPairs_subset C hpair, ?_⟩
    rcases (G.mem_initialPentagonRectangleInitialSelfPairs C D).1 hpair with
      hsource | ⟨S, hS, hrecut⟩
    · exact Or.inl ((G.mem_initialPentagonRectangleInitialSelfSources C D).1 hsource).2
    obtain ⟨hcounted, hcommon, hcol⟩ :=
      (G.mem_initialPentagonRectangleInitialSelfSources C S).1 hS
    obtain ⟨hfirst, hsecond⟩ :=
      G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hcounted
    have hone :=
      S.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hcol
    have hEq : S.recutInitialSelf hcommon hcol hfirst hsecond = D := by
      apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
      exact (S.toGridRectangleDecomposition.existsUnique_isRecut hone hfirst hsecond).unique
        (S.isRecut_recutInitialSelf hcommon hcol hfirst hsecond) hrecut
    obtain ⟨hright, -, htop, hleft, -⟩ :=
      S.recutInitialSelf_geometry hcommon hcol hfirst hsecond
    rw [hEq] at hright htop hleft
    have hback := hrecut.symm hone hfirst hsecond
    have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
      (S.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
    right
    refine ⟨hright.trans hleft.symm, hDone, ?_⟩
    have hsecondTop := S.recutInitialSelf_second_top hcommon hcol hfirst hsecond
    rw [hEq] at hsecondTop
    rw [hsecondTop, htop,
      ← S.toGridRectangleDecomposition.second_bottom_eq_first_top_of_left_eq_left hcommon]
    exact S.turn_notMem_cIco_second_of_left_eq_left hcommon
      (Grid.ne_right_of_mem_cIoo hcol).symm hfirst hsecond
  · rintro ⟨hD, hsource | ⟨hcommon, hone, hturn⟩⟩
    · exact (G.mem_initialPentagonRectangleInitialSelfPairs C D).2 (Or.inl
        ((G.mem_initialPentagonRectangleInitialSelfSources C D).2 ⟨hD, hsource⟩))
    · exact G.mem_initialPentagonRectangleInitialSelfPairs_of_right_eq_left C D hD hcommon
        hone hturn

end TauCeti.GridDiagram
