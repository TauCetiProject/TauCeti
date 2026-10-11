/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Common-terminal-side recuts of a rectangle followed by an initial-side pentagon

Let `b = finRotate n a` be the grid line replaced in a column commutation. A pentagon turning on
its initial side starts on the line `b`. Take a rectangle of the original diagram followed by
such a pentagon, sharing exactly one side column, namely their terminal side `e`, and let `c` be
the initial side of the rectangle. Forgetting the turn point, the two domains form an L-shaped
domain of two empty rectangles sharing their terminal side, and the generic recut of
`Differential/Square/Recut` cuts it the other way. In that recut the *first* rectangle starts on
the line `b`, whichever of the two column orders `c ∈ (b, e)` or `b ∈ (c, e)` emptiness forces.
Its rows are those of the original pentagon, in the first order, or extend them past the
original pentagon's top row through the original rectangle's rows, in the second order, where
emptiness puts the rows of `x` on `b`, `c` and `e` in this cyclic order. Either way they still
contain the turn row, so the first rectangle is again an initial-side pentagon, and the recut
is an initial-side pentagon followed by a rectangle of the commuted diagram
(`GridRectangleInitialPentagonDecomposition.recutRightEqRight`).

The two composite domains are the same once the pentagon squares in the two columns next to `b`
are accounted for, and the rectangle of the commuted diagram is read in the original diagram with
those two columns exchanged (`coveredSquares_val_add_val_recutRightEqRight`). Hence the recut is
counted by the commutation map's chain-map equation whenever the original domain is, and it has
the same monomial weight. These terms therefore cancel between the rectangle--initial-pentagon
and initial-pentagon--rectangle sums of that equation
(`GridDiagram.add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_terminalOverlap`).
This is the initial-side counterpart of the common-initial-side recut of
`Commutation/Overlap/Basic.lean`, for pentagons turning on their terminal side.

## Main definitions

* `TauCeti.GridRectangleInitialPentagonDecomposition.recutRightEqRight`: the recut, promoted to an
  initial-side pentagon followed by a rectangle.
* `TauCeti.GridDiagram.initialPentagonTerminalOverlapSources`: the counted rectangle--initial-side
  pentagon domains with exactly one common side, terminal for both.
* `TauCeti.GridDiagram.initialPentagonTerminalOverlapPartners`: their recuts.

## Main results

* `TauCeti.GridRectangleInitialPentagonDecomposition.isRecut_recutRightEqRight`: forgetting the
  turn row, the promoted decomposition is the generic recut.
* `TauCeti.GridRectangleInitialPentagonDecomposition.coveredSquares_val_add_val_recutRightEqRight`:
  both decompositions cover the same squares with the same multiplicities.
* `TauCeti.GridDiagram.recutRightEqRight_mem_initialPentagonRectangleDecompositions` and
  `TauCeti.GridDiagram.initialPentagonRectangleWeight_recutRightEqRight`: the recut of a counted
  domain is counted, with the same weight.
* `TauCeti.GridDiagram.sum_rectangleInitialPentagonWeight_terminalOverlapSources_eq_sum_partners`
  and `TauCeti.GridDiagram.
  add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_terminalOverlap`: the sources and
  their recuts contribute equally and can be removed from the chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

variable (D : GridRectangleInitialPentagonDecomposition a s x z)
  (hcommon : D.first.right = D.second.right) (hone : D.HasOneCommonSide)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

include hcommon in
/-- In the common-terminal-side overlap, the first rectangle of the recut starts on the replaced
grid line, like the original pentagon. -/
theorem recut_first_left_of_right_eq_right :
    (D.recut hone hfirst hsecond).first.left = finRotate n a :=
  (D.isRecutOfRightEqRight_recut hcommon hone hfirst hsecond).recut_sides.1.trans
    D.second_left_eq

include hcommon hone in
/-- The rectangle and the pentagon of a common-terminal-side overlap have different initial
sides. -/
private theorem first_left_ne_second_left : D.first.left ≠ D.second.left := by
  intro h
  apply D.sideColumns_ne_of_hasOneCommonSide hone
  rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, h, hcommon]

include hcommon hone in
/-- In a common-terminal-side overlap the pentagon's bottom row is the row of the source state on
the replaced line. -/
private theorem second_bottom_eq : D.second.bottom = x (finRotate n a) := by
  rw [GridRectangleBetween.bottom_def, D.first.map_of_ne _
    (D.first_left_ne_second_left hcommon hone).symm (hcommon ▸ D.second.left_ne_right),
    D.second_left_eq]

include hcommon in
/-- The pentagon's top row in a common-terminal-side overlap is the row of the source state on
the rectangle's initial side. -/
private theorem second_top_eq : D.second.top = x D.first.left := by
  rw [GridRectangleBetween.top_def, ← hcommon, D.first.map_right]

include hcommon in
/-- In the common-terminal-side overlap, the first rectangle of the recut still contains the
turn row on its initial side. -/
theorem turn_mem_recut_first_of_right_eq_right :
    s ∈ Grid.cIco (D.recut hone hfirst hsecond).first.bottom
      (D.recut hone hfirst hsecond).first.top := by
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hfirst hsecond
  have hturn := D.second_turn_mem
  have hbottom := D.second_bottom_eq hcommon hone
  have hEbottom : (D.recut hone hfirst hsecond).first.bottom = x (finRotate n a) := by
    rw [GridRectangleBetween.bottom_def, D.recut_first_left_of_right_eq_right hcommon]
  have htop := D.second_top_eq hcommon
  rw [hbottom, htop] at hturn
  rw [hEbottom, GridRectangleBetween.top_def]
  rcases hdata.recut_branch with ⟨-, -, hright, -⟩ | ⟨hcol, -, hright, -⟩
  -- The new pentagon has the original pentagon's rows.
  · rwa [hright]
  -- The new pentagon extends the original pentagon's rows through those of the rectangle, in
  -- the cyclic order forced by emptiness.
  · have hrow := (D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon
      (Grid.ne_left_of_mem_cIoo hcol).symm hfirst hsecond).2
    rw [hbottom, GridRectangleBetween.bottom_def, GridRectangleBetween.top_def] at hrow
    rw [hright]
    exact Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hturn hrow

include hcommon in
/-- Recut a rectangle followed by an initial-side pentagon when their unique common side is
terminal for both, and promote the first new rectangle to an initial-side pentagon. -/
noncomputable def recutRightEqRight : GridInitialPentagonRectangleDecomposition a s x z where
  toGridRectangleDecomposition := D.recut hone hfirst hsecond
  first_left_eq := D.recut_first_left_of_right_eq_right hcommon hone hfirst hsecond
  first_turn_mem := D.turn_mem_recut_first_of_right_eq_right hcommon hone hfirst hsecond

/-- Forgetting the turn row of the promoted decomposition recovers the generic recut. -/
@[simp]
theorem recutRightEqRight_toGridRectangleDecomposition :
    (D.recutRightEqRight hcommon hone hfirst hsecond).toGridRectangleDecomposition =
      D.recut hone hfirst hsecond :=
  (rfl)

/-- The promoted decomposition carries the generic recut relation. In particular its two
underlying rectangles are empty and repartition the squares of the original two. -/
theorem isRecut_recutRightEqRight :
    D.IsRecut (D.recutRightEqRight hcommon hone hfirst hsecond).toGridRectangleDecomposition :=
  D.isRecut_recut hone hfirst hsecond

include hcommon in
/-- The promoted decomposition covers the squares of the original one with the same
multiplicities, the rectangle of the commuted diagram being read in the original diagram with the
two columns next to the replaced line exchanged. -/
theorem coveredSquares_val_add_val_recutRightEqRight :
    (D.recutRightEqRight hcommon hone hfirst hsecond).pentagon.coveredSquares.val +
        ((D.recutRightEqRight hcommon hone hfirst hsecond).second.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  set E := D.recutRightEqRight hcommon hone hfirst hsecond
  have hdata : D.IsRecutOfRightEqRight E.toGridRectangleDecomposition :=
    D.isRecutOfRightEqRight_recut hcommon hone hfirst hsecond
  have hrep : D.IsRepartition E.toGridRectangleDecomposition :=
    (D.isRecut_recutRightEqRight hcommon hone hfirst hsecond).isRepartition
  have hbottom := D.second_bottom_eq hcommon hone
  have hEbottom : E.first.bottom = D.second.bottom := by
    rw [GridRectangleBetween.bottom_def, E.first_left_eq, hbottom]
  have htop := D.second_top_eq hcommon
  have hEleft : E.second.left = D.first.left := hdata.recut_sides.2
  have hb : D.second.left = finRotate n a := D.second_left_eq
  rcases hdata.recut_branch with ⟨hcol, -, hright, hEright⟩ | ⟨hcol, hmiddle, hright, hEright⟩
  -- In the first column order neither rectangle meets the two columns next to the replaced line,
  -- and the new pentagon has the original pentagon's rows.
  · rw [hb] at hcol
    have ha : a ∉ Grid.cIco D.first.left D.first.right := fun h => by
      simpa using Grid.cIco_subset_of_mem_cIoo hcol h
    have hb' : finRotate n a ∉ Grid.cIco D.first.left D.first.right := fun h =>
      Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol)
        (Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol).symm) h
    refine D.coveredSquares_val_add_val_eq_of_isRepartition E hrep (fun t => ?_) (fun t => ?_)
    · have hEtop : E.first.top = x D.first.left := by rw [GridRectangleBetween.top_def, hright]
      simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright, ha,
        hb', false_and, hEtop, htop]
      omega
    · simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright, ha,
        hb', false_and, hEbottom]
      omega
  -- In the second column order both rectangles cover column `a` over the same rows, only the
  -- original rectangle covers the column after the replaced line, and the new pentagon reaches
  -- through the rows of the original rectangle.
  · rw [hb] at hcol hmiddle hEright
    have hunion := Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol
    have hcb : D.first.left ≠ finRotate n a := (Grid.ne_left_of_mem_cIoo hcol).symm
    have ha : a ∈ Grid.cIco D.first.left D.first.right :=
      hunion ▸ Finset.mem_union_left _ (Grid.self_mem_cIco_finRotate hcb)
    have hb' : finRotate n a ∈ Grid.cIco D.first.left D.first.right :=
      hunion ▸ Finset.mem_union_right _ (Grid.left_mem_cIco (Grid.ne_right_of_mem_cIoo hcol))
    have hmidc : E.middle D.first.left = x D.first.left := by
      rw [hmiddle, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcb
        D.first.left_ne_right]
    have hmidb : E.middle (finRotate n a) = x D.first.right := by
      rw [hmiddle, GridState.swapColumns_apply, Equiv.swap_apply_left]
    refine D.coveredSquares_val_add_val_eq_of_isRepartition E hrep (fun t => ?_) (fun t => ?_)
    · have hrow := (D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon
        (hb ▸ hcb) hfirst hsecond).2
      have hturn := D.second_turn_mem
      rw [hbottom, GridRectangleBetween.bottom_def, GridRectangleBetween.top_def] at hrow
      rw [hbottom, htop] at hturn
      have hEtop : E.first.top = x D.first.right := by rw [GridRectangleBetween.top_def, hright]
      simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright,
        Grid.right_notMem_cIco, ha, false_and, true_and, hEtop, htop]
      rw [Grid.ite_mem_cIoo_eq_add_of_mem_cIoo hrow hturn t]
      simp only [↓reduceIte]
      omega
    · simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright,
        Grid.self_mem_cIco_finRotate hcb, hb', true_and, hmidc, hmidb, hEbottom]
      omega

end GridRectangleInitialPentagonDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

section Weights

variable (R : Type*) [CommSemiring R]

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.right = D.second.right) (hone : D.HasOneCommonSide)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

/-- Recutting a rectangle followed by an initial-side pentagon along their common terminal side
preserves the weight. -/
@[simp]
theorem initialPentagonRectangleWeight_recutRightEqRight :
    G.initialPentagonRectangleWeight C R (D.recutRightEqRight hcommon hone hfirst hsecond) =
      G.rectangleInitialPentagonWeight C R D :=
  G.initialPentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_val_recutRightEqRight hcommon hone hfirst hsecond)

end Weights

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.right = D.second.right) (hone : D.HasOneCommonSide)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

/-- The recut of a counted rectangle--initial-side pentagon domain with exactly one common side,
terminal for both, is a counted initial-side pentagon--rectangle domain. -/
theorem recutRightEqRight_mem_initialPentagonRectangleDecompositions
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) :
    D.recutRightEqRight hcommon hone hfirst hsecond ∈
      G.initialPentagonRectangleDecompositions C x z :=
  have hrecut := D.isRecut_recutRightEqRight hcommon hone hfirst hsecond
  G.mem_initialPentagonRectangleDecompositions_of_val_add_val_eq C hD hrecut.isEmpty_first
    hrecut.isEmpty_second
    (D.coveredSquares_val_add_val_recutRightEqRight hcommon hone hfirst hsecond)

/-! ### Cancelling the common-terminal-side terms -/

variable (x z) in
/-- The counted rectangle--initial-side pentagon decompositions with exactly one common side
column, terminal for both domains. -/
noncomputable def initialPentagonTerminalOverlapSources :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectangleInitialPentagonDecompositions C x z).filter fun D =>
    D.first.right = D.second.right ∧ D.HasOneCommonSide

/-- Membership in the common-terminal-side source family records counting and exactly one common
side column, terminal for both domains. -/
@[simp]
theorem mem_initialPentagonTerminalOverlapSources :
    D ∈ G.initialPentagonTerminalOverlapSources C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧
        D.first.right = D.second.right ∧ D.HasOneCommonSide := by
  classical
  simp [initialPentagonTerminalOverlapSources]

private theorem initialPentagonTerminalOverlapSource_data
    (hD : D ∈ G.initialPentagonTerminalOverlapSources C x z) :
    D.first.right = D.second.right ∧ D.HasOneCommonSide ∧ D.first.IsEmpty ∧ D.second.IsEmpty := by
  obtain ⟨hcounted, hcommon, hone⟩ := (G.mem_initialPentagonTerminalOverlapSources C D).1 hD
  rw [G.mem_rectangleInitialPentagonDecompositions, G.mem_unblockedRectangles,
    G.mem_initialPentagons,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] at hcounted
  exact ⟨hcommon, hone, hcounted.1.1, hcounted.2.1⟩

private noncomputable def initialPentagonTerminalOverlapPartner
    (D : {D // D ∈ G.initialPentagonTerminalOverlapSources C x z}) :
    GridInitialPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutRightEqRight
    (G.initialPentagonTerminalOverlapSource_data C D.val D.property).1
    (G.initialPentagonTerminalOverlapSource_data C D.val D.property).2.1
    (G.initialPentagonTerminalOverlapSource_data C D.val D.property).2.2.1
    (G.initialPentagonTerminalOverlapSource_data C D.val D.property).2.2.2

private theorem initialPentagonTerminalOverlapPartner_isRecut
    (D : {D // D ∈ G.initialPentagonTerminalOverlapSources C x z}) :
    D.val.IsRecut (G.initialPentagonTerminalOverlapPartner C D).toGridRectangleDecomposition :=
  D.val.isRecut_recutRightEqRight _ _ _ _

private theorem initialPentagonTerminalOverlapPartner_injective :
    Function.Injective (G.initialPentagonTerminalOverlapPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.initialPentagonTerminalOverlapPartner_isRecut C D
  have hE := G.initialPentagonTerminalOverlapPartner_isRecut C E
  rw [← h] at hE
  obtain ⟨-, honeD, hfD, hsD⟩ := G.initialPentagonTerminalOverlapSource_data C D.val D.property
  obtain ⟨-, honeE, hfE, hsE⟩ := G.initialPentagonTerminalOverlapSource_data C E.val E.property
  have hbackD := hD.symm honeD hfD hsD
  have hbackE := hE.symm honeE hfE hsE
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

private theorem initialPentagonTerminalOverlapPartner_mem
    (D : {D // D ∈ G.initialPentagonTerminalOverlapSources C x z}) :
    G.initialPentagonTerminalOverlapPartner C D ∈
      G.initialPentagonRectangleDecompositions C x z := by
  unfold initialPentagonTerminalOverlapPartner
  exact G.recutRightEqRight_mem_initialPentagonRectangleDecompositions C D.val _ _ _ _
    ((G.mem_initialPentagonTerminalOverlapSources C D.val).1 D.property).1

variable (x z) in
/-- The initial-side pentagon--rectangle partners obtained by recutting the counted
common-terminal-side sources: the exact recut image of
`GridDiagram.initialPentagonTerminalOverlapSources`. -/
noncomputable def initialPentagonTerminalOverlapPartners :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonTerminalOverlapSources C x z).attach.map
    ⟨G.initialPentagonTerminalOverlapPartner C, G.initialPentagonTerminalOverlapPartner_injective C⟩

/-- An initial-side pentagon--rectangle term is a partner exactly when its underlying rectangles
are the recut of a counted common-terminal-side source. -/
@[simp]
theorem mem_initialPentagonTerminalOverlapPartners
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonTerminalOverlapPartners C x z ↔
      ∃ D ∈ G.initialPentagonTerminalOverlapSources C x z,
        D.IsRecut E.toGridRectangleDecomposition := by
  classical
  simp only [initialPentagonTerminalOverlapPartners, Finset.mem_map, Finset.mem_attach,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.initialPentagonTerminalOverlapPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨-, hone, hf, hs⟩ := G.initialPentagonTerminalOverlapSource_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    exact (D.existsUnique_isRecut hone hf hs).unique
      (G.initialPentagonTerminalOverlapPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Each common-terminal-side source belongs to the rectangle--initial-side pentagon sum. -/
theorem initialPentagonTerminalOverlapSources_subset :
    G.initialPentagonTerminalOverlapSources C x z ⊆
      G.rectangleInitialPentagonDecompositions C x z := fun D hD =>
  ((G.mem_initialPentagonTerminalOverlapSources C D).1 hD).1

/-- Each partner belongs to the initial-side pentagon--rectangle sum. -/
theorem initialPentagonTerminalOverlapPartners_subset :
    G.initialPentagonTerminalOverlapPartners C x z ⊆
      G.initialPentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [initialPentagonTerminalOverlapPartners] at hE
  obtain ⟨D, _, rfl⟩ := Finset.mem_map.mp hE
  exact G.initialPentagonTerminalOverlapPartner_mem C D

variable (R : Type*) [CommSemiring R]

variable (x z) in
/-- Recutting identifies the total contribution of the common-terminal-side sources with the
total contribution of their partners. -/
theorem sum_rectangleInitialPentagonWeight_terminalOverlapSources_eq_sum_partners :
    ∑ D ∈ G.initialPentagonTerminalOverlapSources C x z, G.rectangleInitialPentagonWeight C R D =
      ∑ E ∈ G.initialPentagonTerminalOverlapPartners C x z,
        G.initialPentagonRectangleWeight C R E := by
  classical
  have hweight (D : {D // D ∈ G.initialPentagonTerminalOverlapSources C x z}) :
      G.initialPentagonRectangleWeight C R (G.initialPentagonTerminalOverlapPartner C D) =
        G.rectangleInitialPentagonWeight C R D.val :=
    G.initialPentagonRectangleWeight_recutRightEqRight C R D.val _ _ _ _
  rw [initialPentagonTerminalOverlapPartners, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, hweight, Finset.sum_attach]

variable (x z) in
open scoped Classical in
/-- In an equation between the rectangle--initial-side pentagon sum and the initial-side
pentagon--rectangle sum, each augmented by further terms, the common-terminal-side sources and
their partners can be removed. -/
theorem add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_terminalOverlap
    [IsCancelAdd R] (A B : MvPolynomial (Fin n) R) :
    A + ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
          G.rectangleInitialPentagonWeight C R D =
        B + ∑ E ∈ G.initialPentagonRectangleDecompositions C x z,
          G.initialPentagonRectangleWeight C R E ↔
      A + ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z \
            G.initialPentagonTerminalOverlapSources C x z,
          G.rectangleInitialPentagonWeight C R D =
        B + ∑ E ∈ G.initialPentagonRectangleDecompositions C x z \
            G.initialPentagonTerminalOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E := by
  rw [← Finset.sum_sdiff (G.initialPentagonTerminalOverlapSources_subset C)
      (f := G.rectangleInitialPentagonWeight C R),
    ← Finset.sum_sdiff (G.initialPentagonTerminalOverlapPartners_subset C)
      (f := G.initialPentagonRectangleWeight C R),
    G.sum_rectangleInitialPentagonWeight_terminalOverlapSources_eq_sum_partners C x z R,
    ← add_assoc, ← add_assoc]
  exact add_right_cancel_iff

end GridDiagram

end TauCeti
