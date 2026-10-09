/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Common-initial-side recuts of a rectangle followed by an initial-side pentagon

Let `b = finRotate n a` be the grid line replaced in a column commutation. A pentagon turning on
its initial side starts on the line `b`. Take a rectangle of the original diagram followed by
such a pentagon, sharing exactly one side column, namely their initial side, which is therefore
`b` itself. Let `d` and `f` be the terminal sides of the rectangle and of the pentagon. Forgetting
the turn point, the two domains form an L-shaped domain of two empty rectangles sharing their
initial side, and the generic recut of `Differential/Square/Recut` cuts it the other way.
Which way depends on the column order.

When `f ∈ (b, d)`, the column interval of the pentagon lies inside that of the rectangle. The
first recut rectangle then runs from `b` to `f`, with rows from the row of `x` on `b` up to the
pentagon's top row. Emptiness of the original rectangle puts the rows of `x` on `b`, `d` and `f`
in this cyclic order, so these rows contain the original pentagon's rows, hence the turn row.
The first recut rectangle is therefore again an initial-side pentagon, and the recut is an
initial-side pentagon followed by a rectangle of the commuted diagram, from `f` to `d`
(`GridRectangleInitialPentagonDecomposition.recutLeftEqLeft`). That rectangle meets neither of
the two columns next to `b`. In the column after `b`, the squares below the turn row covered by
the original rectangle and the original pentagon are exactly those covered by the new pentagon,
and in the column before `b` both pentagons cover the rows strictly above the turn row up to the
row of `x` on `f`. So the two composite domains cover the same squares with the same multiplicities
(`coveredSquares_val_add_val_recutLeftEqLeft`). Hence the recut is counted by the commutation
map's chain-map equation whenever the original domain is, and it has the same monomial weight.
These terms therefore cancel between the rectangle--initial-pentagon and
initial-pentagon--rectangle sums of that equation
(`GridDiagram.add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_initialCrossOverlap`).

In the other column order, `d ∈ (b, f)`, the recut instead has its *second* rectangle starting
on `b`, while its first rectangle starts on the terminal side of the second; that case is not
treated here.

## Main definitions

* `TauCeti.GridRectangleInitialPentagonDecomposition.recutLeftEqLeft`: the recut in the column
  order `f ∈ (b, d)`, promoted to an initial-side pentagon followed by a rectangle.
* `TauCeti.GridDiagram.initialPentagonInitialCrossOverlapSources`: the counted
  rectangle--initial-side pentagon domains with a common initial side whose pentagon's terminal
  side lies strictly inside the rectangle's column interval.
* `TauCeti.GridDiagram.initialPentagonInitialCrossOverlapPartners`: their recuts.

## Main results

* `TauCeti.GridRectangleInitialPentagonDecomposition.isRecut_recutLeftEqLeft`: forgetting the
  turn row, the promoted decomposition is the generic recut.
* `TauCeti.GridRectangleInitialPentagonDecomposition.coveredSquares_val_add_val_recutLeftEqLeft`:
  both decompositions cover the same squares with the same multiplicities.
* `TauCeti.GridDiagram.recutLeftEqLeft_mem_initialPentagonRectangleDecompositions` and
  `TauCeti.GridDiagram.initialPentagonRectangleWeight_recutLeftEqLeft`: the recut of a counted
  domain is counted, with the same weight.
* `TauCeti.GridDiagram.
  sum_rectangleInitialPentagonWeight_initialCrossOverlapSources_eq_sum_partners` and
  `TauCeti.GridDiagram.
  add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_initialCrossOverlap`: the sources
  and their recuts contribute equally and can be removed from the chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- A common-initial-side overlap whose pentagon's terminal side lies strictly inside the
rectangle's column interval shares exactly one side column. -/
theorem hasOneCommonSide_of_initial_overlap (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right) :
    D.toGridRectangleDecomposition.HasOneCommonSide := by
  apply D.toGridRectangleDecomposition.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨D.first.left, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, ← hcommon] at hc
    have hne := Grid.ne_right_of_mem_cIoo hcol
    have := D.first.left_ne_right
    grind

variable (D : GridRectangleInitialPentagonDecomposition a s x z)
  (hcommon : D.first.left = D.second.left)
  (hcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

include hcommon hcol in
/-- In the common-initial-side overlap whose pentagon's terminal side lies inside the rectangle's
column interval, the two rectangles of the recut start on the common side and on the pentagon's
terminal side. -/
private theorem recut_lefts_of_left_eq_left :
    (D.toGridRectangleDecomposition.recut
        (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond).first.left =
        D.first.left ∧
      (D.toGridRectangleDecomposition.recut
          (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond).second.left =
        D.second.right := by
  rcases (D.toGridRectangleDecomposition.isRecutOfLeftEqLeft_recut hcommon
      (D.hasOneCommonSide_of_initial_overlap hcommon hcol)
      hfirst hsecond).recut_branch with
    ⟨h, -⟩ | ⟨-, -, h⟩
  · exact False.elim (Finset.disjoint_left.mp
      (Grid.disjoint_cIoo_swap D.first.left D.second.right) h (Grid.mem_cIoo_cyclic_left hcol))
  · exact h

include hcommon hcol in
/-- In the common-initial-side overlap whose pentagon's terminal side lies inside the rectangle's
column interval, the first rectangle of the recut starts on the replaced grid line, like the
original pentagon. -/
theorem recut_first_left_of_left_eq_left :
    (D.toGridRectangleDecomposition.recut
        (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond).first.left =
      finRotate n a :=
  (D.recut_lefts_of_left_eq_left hcommon hcol hfirst hsecond).1.trans
    (hcommon.trans D.second_left_eq)

include hcommon in
/-- In a common-initial-side overlap the pentagon's bottom row is the rectangle's top row. -/
private theorem second_bottom_eq_first_top : D.second.bottom = D.first.top := by
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, ← hcommon, D.first.map_left]

include hcol in
/-- In a common-initial-side overlap whose pentagon's terminal side lies inside the rectangle's
column interval, the pentagon's top row is the row of the source state on that terminal side. -/
private theorem second_top_eq : D.second.top = x D.second.right := by
  rw [GridRectangleBetween.top_def, D.first.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol)
    (Grid.ne_right_of_mem_cIoo hcol)]

include hcommon hcol in
/-- In the common-initial-side overlap whose pentagon's terminal side lies inside the rectangle's
column interval, the first rectangle of the recut has the rectangle's bottom row and the
pentagon's top row. -/
private theorem recut_first_bottom_top :
    (D.toGridRectangleDecomposition.recut
        (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond).first.bottom =
        D.first.bottom ∧
      (D.toGridRectangleDecomposition.recut
          (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond).first.top =
        D.second.top := by
  have hdata := D.toGridRectangleDecomposition.isRecutOfLeftEqLeft_recut hcommon
    (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.bottom_def,
    GridRectangleBetween.top_def, hdata.recut_sides.1, D.second_top_eq hcol,
    (D.recut_lefts_of_left_eq_left hcommon hcol hfirst hsecond).1]
  exact ⟨rfl, rfl⟩

include hcommon hcol hfirst hsecond in
/-- In a common-initial-side overlap of empty domains whose pentagon's terminal side lies inside
the rectangle's column interval, the rectangle's top row lies strictly between its bottom row and
the pentagon's top row. -/
private theorem first_top_mem_cIoo :
    D.first.top ∈ Grid.cIoo D.first.bottom D.second.top :=
  (D.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
      (Grid.ne_right_of_mem_cIoo hcol).symm
    hfirst hsecond).2

include hcommon hcol in
/-- In the common-initial-side overlap whose pentagon's terminal side lies inside the rectangle's
column interval, the first rectangle of the recut contains the turn row on its initial side: its
rows contain those of the original pentagon. -/
theorem turn_mem_recut_first_of_left_eq_left :
    s ∈ Grid.cIco
      (D.toGridRectangleDecomposition.recut
          (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond).first.bottom
      (D.toGridRectangleDecomposition.recut
          (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond).first.top := by
  have hturn := D.second_turn_mem
  rw [D.second_bottom_eq_first_top hcommon] at hturn
  obtain ⟨hbottom, htop⟩ := D.recut_first_bottom_top hcommon hcol hfirst hsecond
  rw [hbottom, htop]
  exact Grid.cIco_subset_of_mem_cIoo (D.first_top_mem_cIoo hcommon hcol hfirst hsecond) hturn

include hcommon hcol in
/-- Recut a rectangle followed by an initial-side pentagon when their unique common side is
initial for both and the pentagon's terminal side lies inside the rectangle's column interval,
and promote the first new rectangle to an initial-side pentagon. -/
noncomputable def recutLeftEqLeft : GridInitialPentagonRectangleDecomposition a s x z where
  toGridTwoStepDecomposition :=
    D.toGridRectangleDecomposition.recut
        (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond
  first_left_eq := D.recut_first_left_of_left_eq_left hcommon hcol hfirst hsecond
  first_turn_mem := D.turn_mem_recut_first_of_left_eq_left hcommon hcol hfirst hsecond

/-- Forgetting the turn row of the promoted decomposition recovers the generic recut. -/
@[simp]
theorem recutLeftEqLeft_toGridRectangleDecomposition :
    (D.recutLeftEqLeft hcommon hcol hfirst hsecond).toGridRectangleDecomposition =
      D.toGridRectangleDecomposition.recut
          (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond :=
  (rfl)

/-- The promoted decomposition carries the generic recut relation. In particular its two
underlying rectangles are empty and repartition the squares of the original two. -/
theorem isRecut_recutLeftEqLeft :
    D.toGridRectangleDecomposition.IsRecut
        (D.recutLeftEqLeft hcommon hcol hfirst hsecond).toGridRectangleDecomposition :=
  D.toGridRectangleDecomposition.isRecut_recut
      (D.hasOneCommonSide_of_initial_overlap hcommon hcol) hfirst hsecond

/-- The promoted decomposition covers the squares of the original one with the same
multiplicities, the rectangle of the commuted diagram being read in the original diagram with the
two columns next to the replaced line exchanged. -/
theorem coveredSquares_val_add_val_recutLeftEqLeft :
    (D.recutLeftEqLeft hcommon hcol hfirst hsecond).pentagon.coveredSquares.val +
        ((D.recutLeftEqLeft hcommon hcol hfirst hsecond).second.toGridRectangle.coveredSquares
          |>.map ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  set E := D.recutLeftEqLeft hcommon hcol hfirst hsecond
  have hdata : D.toGridRectangleDecomposition.IsRecutOfLeftEqLeft E.toGridRectangleDecomposition :=
    D.toGridRectangleDecomposition.isRecutOfLeftEqLeft_recut hcommon
        (D.hasOneCommonSide_of_initial_overlap hcommon hcol)
      hfirst hsecond
  have hEleft : E.second.left = D.second.right :=
    (D.recut_lefts_of_left_eq_left hcommon hcol hfirst hsecond).2
  have hEbottom : E.first.bottom = D.first.bottom :=
    (D.recut_first_bottom_top hcommon hcol hfirst hsecond).1
  have hEtop : E.first.top = D.second.top :=
    (D.recut_first_bottom_top hcommon hcol hfirst hsecond).2
  have hEright : E.second.right = D.first.right := hdata.recut_sides.2
  have hrow := D.first_top_mem_cIoo hcommon hcol hfirst hsecond
  have hturn := D.second_turn_mem
  rw [D.second_bottom_eq_first_top hcommon] at hturn
  have hb : D.first.left = finRotate n a := hcommon.trans D.second_left_eq
  have hcol' := hb ▸ hcol
  -- The rectangle of the commuted diagram runs between the two terminal sides, so it meets
  -- neither of the two columns next to the replaced line, and the original rectangle starts on
  -- the replaced line, so it misses the column before it.
  have ha : a ∉ Grid.cIco D.second.right D.first.right := fun h => by
    simpa using Grid.cIco_subset_of_mem_cIoo hcol' h
  have hb' : finRotate n a ∉ Grid.cIco D.second.right D.first.right := fun h =>
    Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol')
      (Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol').symm) h
  have ha' : a ∉ Grid.cIco D.first.left D.first.right := by simp [hb]
  have hbmem : finRotate n a ∈ Grid.cIco D.first.left D.first.right :=
    hb ▸ Grid.left_mem_cIco D.first.left_ne_right
  refine D.coveredSquares_val_add_val_eq_of_isRepartition E
    (D.isRecut_recutLeftEqLeft hcommon hcol hfirst hsecond).isRepartition
    (fun t => ?_) (fun t => ?_)
  -- In column `a` neither rectangle covers anything, and the two pentagons have the same top.
  · simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright, hb',
      ha', false_and, hEtop]
    omega
  -- In the column after the replaced line, the original rectangle and pentagon split the rows
  -- covered by the new pentagon at the original rectangle's top row.
  · simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright, ha,
      hbmem, false_and, true_and, hEbottom, D.second_bottom_eq_first_top hcommon,
      ← D.first.bottom_def, ← D.first.top_def]
    rw [Grid.ite_mem_cIco_eq_add_of_mem_cIoo hrow hturn t]
    simp only [↓reduceIte]
    omega

end GridRectangleInitialPentagonDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

section Weights

variable (R : Type*) [CommSemiring R]

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.left = D.second.left)
  (hcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

/-- Recutting a rectangle followed by an initial-side pentagon along their common initial side,
when the pentagon's terminal side lies inside the rectangle's column interval, preserves the
weight. -/
@[simp]
theorem initialPentagonRectangleWeight_recutLeftEqLeft :
    G.initialPentagonRectangleWeight C R (D.recutLeftEqLeft hcommon hcol hfirst hsecond) =
      G.rectangleInitialPentagonWeight C R D :=
  G.initialPentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_val_recutLeftEqLeft hcommon hcol hfirst hsecond)

end Weights

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.left = D.second.left)
  (hcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

/-- The recut of a counted rectangle--initial-side pentagon domain with a common initial side,
whose pentagon's terminal side lies inside the rectangle's column interval, is a counted
initial-side pentagon--rectangle domain. -/
theorem recutLeftEqLeft_mem_initialPentagonRectangleDecompositions
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) :
    D.recutLeftEqLeft hcommon hcol hfirst hsecond ∈
      G.initialPentagonRectangleDecompositions C x z :=
  have hrecut := D.isRecut_recutLeftEqLeft hcommon hcol hfirst hsecond
  G.mem_initialPentagonRectangleDecompositions_of_val_add_val_eq C hD hrecut.isEmpty_first
    hrecut.isEmpty_second
    (D.coveredSquares_val_add_val_recutLeftEqLeft hcommon hcol hfirst hsecond)

/-! ### Cancelling the common-initial-side cross terms -/

variable (x z) in
/-- The counted rectangle--initial-side pentagon decompositions with a common initial side whose
pentagon's terminal side lies strictly inside the rectangle's column interval. -/
noncomputable def initialPentagonInitialCrossOverlapSources :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectangleInitialPentagonDecompositions C x z).filter fun D =>
    D.first.left = D.second.left ∧ D.second.right ∈ Grid.cIoo D.first.left D.first.right

/-- Membership in the common-initial-side cross source family records counting, the common
initial side and the column order. -/
@[simp]
theorem mem_initialPentagonInitialCrossOverlapSources :
    D ∈ G.initialPentagonInitialCrossOverlapSources C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧
        D.first.left = D.second.left ∧ D.second.right ∈ Grid.cIoo D.first.left D.first.right := by
  classical
  simp [initialPentagonInitialCrossOverlapSources]

private theorem initialPentagonInitialCrossOverlapSource_data
    (hD : D ∈ G.initialPentagonInitialCrossOverlapSources C x z) :
    D.first.left = D.second.left ∧ D.second.right ∈ Grid.cIoo D.first.left D.first.right ∧
      D.toGridRectangleDecomposition.HasOneCommonSide ∧ D.first.IsEmpty ∧ D.second.IsEmpty := by
  obtain ⟨hcounted, hcommon, hcol⟩ := (G.mem_initialPentagonInitialCrossOverlapSources C D).1 hD
  rw [G.mem_rectangleInitialPentagonDecompositions, G.mem_unblockedRectangles,
    G.mem_initialPentagons,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] at hcounted
  exact ⟨hcommon, hcol, D.hasOneCommonSide_of_initial_overlap hcommon hcol, hcounted.1.1,
    hcounted.2.1⟩

private noncomputable def initialPentagonInitialCrossOverlapPartner
    (D : {D // D ∈ G.initialPentagonInitialCrossOverlapSources C x z}) :
    GridInitialPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutLeftEqLeft
    (G.initialPentagonInitialCrossOverlapSource_data C D.val D.property).1
    (G.initialPentagonInitialCrossOverlapSource_data C D.val D.property).2.1
    (G.initialPentagonInitialCrossOverlapSource_data C D.val D.property).2.2.2.1
    (G.initialPentagonInitialCrossOverlapSource_data C D.val D.property).2.2.2.2

private theorem initialPentagonInitialCrossOverlapPartner_isRecut
    (D : {D // D ∈ G.initialPentagonInitialCrossOverlapSources C x z}) :
    D.val.toGridRectangleDecomposition.IsRecut
      (G.initialPentagonInitialCrossOverlapPartner C D).toGridRectangleDecomposition :=
  D.val.isRecut_recutLeftEqLeft _ _ _ _

private theorem initialPentagonInitialCrossOverlapPartner_injective :
    Function.Injective (G.initialPentagonInitialCrossOverlapPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.initialPentagonInitialCrossOverlapPartner_isRecut C D
  have hE := G.initialPentagonInitialCrossOverlapPartner_isRecut C E
  rw [← h] at hE
  obtain ⟨-, -, honeD, hfD, hsD⟩ :=
    G.initialPentagonInitialCrossOverlapSource_data C D.val D.property
  obtain ⟨-, -, honeE, hfE, hsE⟩ :=
    G.initialPentagonInitialCrossOverlapSource_data C E.val E.property
  have hbackD := hD.symm honeD hfD hsD
  have hbackE := hE.symm honeE hfE hsE
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

private theorem initialPentagonInitialCrossOverlapPartner_mem
    (D : {D // D ∈ G.initialPentagonInitialCrossOverlapSources C x z}) :
    G.initialPentagonInitialCrossOverlapPartner C D ∈
      G.initialPentagonRectangleDecompositions C x z := by
  unfold initialPentagonInitialCrossOverlapPartner
  exact G.recutLeftEqLeft_mem_initialPentagonRectangleDecompositions C D.val _ _ _ _
    ((G.mem_initialPentagonInitialCrossOverlapSources C D.val).1 D.property).1

variable (x z) in
/-- The initial-side pentagon--rectangle partners obtained by recutting the counted
common-initial-side cross sources: the exact recut image of
`GridDiagram.initialPentagonInitialCrossOverlapSources`. -/
noncomputable def initialPentagonInitialCrossOverlapPartners :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonInitialCrossOverlapSources C x z).attach.map
    ⟨G.initialPentagonInitialCrossOverlapPartner C,
      G.initialPentagonInitialCrossOverlapPartner_injective C⟩

/-- An initial-side pentagon--rectangle term is a partner exactly when its underlying rectangles
are the recut of a counted common-initial-side cross source. -/
@[simp]
theorem mem_initialPentagonInitialCrossOverlapPartners
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonInitialCrossOverlapPartners C x z ↔
      ∃ D ∈ G.initialPentagonInitialCrossOverlapSources C x z,
        D.toGridRectangleDecomposition.IsRecut E.toGridRectangleDecomposition := by
  classical
  simp only [initialPentagonInitialCrossOverlapPartners, Finset.mem_map, Finset.mem_attach,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.initialPentagonInitialCrossOverlapPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨-, -, hone, hf, hs⟩ := G.initialPentagonInitialCrossOverlapSource_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    exact (D.toGridRectangleDecomposition.existsUnique_isRecut hone hf hs).unique
      (G.initialPentagonInitialCrossOverlapPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Each common-initial-side cross source belongs to the rectangle--initial-side pentagon sum. -/
theorem initialPentagonInitialCrossOverlapSources_subset :
    G.initialPentagonInitialCrossOverlapSources C x z ⊆
      G.rectangleInitialPentagonDecompositions C x z := fun D hD =>
  ((G.mem_initialPentagonInitialCrossOverlapSources C D).1 hD).1

/-- Each partner belongs to the initial-side pentagon--rectangle sum. -/
theorem initialPentagonInitialCrossOverlapPartners_subset :
    G.initialPentagonInitialCrossOverlapPartners C x z ⊆
      G.initialPentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [initialPentagonInitialCrossOverlapPartners] at hE
  obtain ⟨D, _, rfl⟩ := Finset.mem_map.mp hE
  exact G.initialPentagonInitialCrossOverlapPartner_mem C D

variable (R : Type*) [CommSemiring R]

variable (x z) in
/-- Recutting identifies the total contribution of the common-initial-side cross sources with
the total contribution of their partners. -/
theorem sum_rectangleInitialPentagonWeight_initialCrossOverlapSources_eq_sum_partners :
    ∑ D ∈ G.initialPentagonInitialCrossOverlapSources C x z,
        G.rectangleInitialPentagonWeight C R D =
      ∑ E ∈ G.initialPentagonInitialCrossOverlapPartners C x z,
        G.initialPentagonRectangleWeight C R E := by
  classical
  have hweight (D : {D // D ∈ G.initialPentagonInitialCrossOverlapSources C x z}) :
      G.initialPentagonRectangleWeight C R (G.initialPentagonInitialCrossOverlapPartner C D) =
        G.rectangleInitialPentagonWeight C R D.val :=
    G.initialPentagonRectangleWeight_recutLeftEqLeft C R D.val _ _ _ _
  rw [initialPentagonInitialCrossOverlapPartners, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, hweight, Finset.sum_attach]

variable (x z) in
open scoped Classical in
/-- In an equation between the rectangle--initial-side pentagon sum and the initial-side
pentagon--rectangle sum, each augmented by further terms, the common-initial-side cross sources
and their partners can be removed. -/
theorem add_sum_rectangleInitialPentagonWeight_eq_add_sum_iff_sdiff_initialCrossOverlap
    [IsCancelAdd R] (A B : MvPolynomial (Fin n) R) :
    A + ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
          G.rectangleInitialPentagonWeight C R D =
        B + ∑ E ∈ G.initialPentagonRectangleDecompositions C x z,
          G.initialPentagonRectangleWeight C R E ↔
      A + ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z \
            G.initialPentagonInitialCrossOverlapSources C x z,
          G.rectangleInitialPentagonWeight C R D =
        B + ∑ E ∈ G.initialPentagonRectangleDecompositions C x z \
            G.initialPentagonInitialCrossOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E := by
  rw [← Finset.sum_sdiff (G.initialPentagonInitialCrossOverlapSources_subset C)
      (f := G.rectangleInitialPentagonWeight C R),
    ← Finset.sum_sdiff (G.initialPentagonInitialCrossOverlapPartners_subset C)
      (f := G.initialPentagonRectangleWeight C R),
    G.sum_rectangleInitialPentagonWeight_initialCrossOverlapSources_eq_sum_partners C x z R,
    ← add_assoc, ← add_assoc]
  exact add_right_cancel_iff

end GridDiagram

end TauCeti
