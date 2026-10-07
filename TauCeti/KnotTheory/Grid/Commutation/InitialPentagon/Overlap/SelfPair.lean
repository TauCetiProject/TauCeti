/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Pairing
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Common-initial-side self pairs of a rectangle followed by an initial-side pentagon

Let `b = finRotate n a` be the grid line replaced in a column commutation. A pentagon turning on
its initial side starts on the line `b`. Take a rectangle of the original diagram followed by
such a pentagon, sharing exactly one side column, namely their initial side, which is therefore
`b` itself. Let `d` and `f` be the terminal sides of the rectangle and of the pentagon. Forgetting
the turn point, the two domains form an L-shaped domain of two empty rectangles sharing their
initial side, and the generic recut of `Differential/Square/Recut` cuts it the other way.

This file treats the column order `d ∈ (b, f)`, where the column interval of the rectangle lies
inside that of the pentagon. The recut then has its first rectangle running from `d` to `f`, with
the rows of the original pentagon, and its second rectangle running from `b` to `d`, with rows
from the row of `x` on `b` up to the pentagon's top row. Emptiness puts the rows of `x` on `b`,
`d` and `f` in this cyclic order, so the second rectangle contains the original pentagon's rows
and the turn row, and it promotes to an initial-side pentagon: the recut is again a rectangle
followed by an initial-side pentagon
(`GridRectangleInitialPentagonDecomposition.recutLeftEqLeftSecond`). Its first rectangle lies in
the columns where the original pentagon covers exactly the squares of its underlying rectangle,
and in the column after `b` the original rectangle and pentagon split the squares covered by the
new pentagon, so the composite domains cover the same squares with the same multiplicities
(`coveredSquares_val_add_val_recutLeftEqLeftSecond`). The partner is therefore counted, with the
same weight, and since it has a mixed common side (its rectangle starts on `d`, where its
pentagon ends) it is not itself a source. Each such pair cancels within the
rectangle--initial-side pentagon sum of the commutation chain-map equation in characteristic two.

In the other column order, `f ∈ (b, d)`, the recut is instead an initial-side pentagon followed
by a rectangle of the commuted diagram, so it pairs terms across the chain-map equation rather
than within one sum; that case is not treated here.

## Main definitions

* `TauCeti.GridRectangleInitialPentagonDecomposition.recutLeftEqLeftSecond`: the recut in the
  column order `d ∈ (b, f)`, promoted to a rectangle followed by an initial-side pentagon.
* `TauCeti.GridDiagram.initialPentagonInitialSelfPairSources`: the counted
  rectangle--initial-side pentagon domains with a common initial side whose rectangle's terminal
  side lies strictly inside the pentagon's column interval.
* `TauCeti.GridDiagram.initialPentagonInitialSelfPairs`: these sources together with their recuts.

## Main results

* `TauCeti.GridRectangleInitialPentagonDecomposition.isRecut_recutLeftEqLeftSecond`: forgetting
  the turn row, the promoted decomposition is the generic recut.
* `TauCeti.GridRectangleInitialPentagonDecomposition.
  coveredSquares_val_add_val_recutLeftEqLeftSecond`: both decompositions cover the same squares
  with the same multiplicities.
* `TauCeti.GridDiagram.recutLeftEqLeftSecond_mem_rectangleInitialPentagonDecompositions` and
  `TauCeti.GridDiagram.rectangleInitialPentagonWeight_recutLeftEqLeftSecond`: the recut of a
  counted domain is counted in the same sum, with the same weight.
* `TauCeti.GridDiagram.sum_rectangleInitialPentagonWeight_initialSelfPairs_eq_zero` and
  `TauCeti.GridDiagram.sum_rectangleInitialPentagonWeight_eq_sum_sdiff_initialSelfPairs`: in
  characteristic two the self pairs cancel and can be removed from the rectangle--initial-side
  pentagon sum.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition a s x z)
  (hcommon : D.first.left = D.second.left)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

include hcommon in
/-- In a common-initial-side overlap the pentagon's bottom row is the rectangle's top row. -/
private theorem second_bottom_eq_first_top : D.second.bottom = D.first.top := by
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, ← hcommon, D.first.map_left]

variable (hself : D.first.right ∈ Grid.cIoo D.first.left D.second.right)

include hcommon hself in
/-- In the common-initial-side overlap whose rectangle's terminal side lies inside the pentagon's
column interval, the two rectangles of the recut start on the rectangle's terminal side and on the
common side. -/
private theorem recut_lefts_of_left_eq_left_self :
    (D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
        hfirst hsecond).first.left = D.first.right ∧
      (D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
        hfirst hsecond).second.left = D.first.left := by
  rcases (D.isRecutOfLeftEqLeft_recut hcommon
      (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
      hfirst hsecond).recut_branch with ⟨-, -, h⟩ | ⟨h, -⟩
  · exact h
  · exact False.elim (Finset.disjoint_left.mp
      (Grid.disjoint_cIoo_swap D.first.left D.first.right) h (Grid.mem_cIoo_cyclic_left hself))

include hcommon hself in
/-- In the common-initial-side overlap whose rectangle's terminal side lies inside the pentagon's
column interval, the second rectangle of the recut has the rectangle's bottom row and the
pentagon's top row. -/
private theorem recut_second_bottom_top_of_left_eq_left_self :
    (D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
        hfirst hsecond).second.bottom = D.first.bottom ∧
      (D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
        hfirst hsecond).second.top = D.second.top := by
  set E := D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
    hfirst hsecond
  have hdata : D.IsRecutOfLeftEqLeft E := D.isRecutOfLeftEqLeft_recut hcommon _ hfirst hsecond
  obtain ⟨hEfl, hEsl⟩ := D.recut_lefts_of_left_eq_left_self hcommon hfirst hsecond hself
  have hfr : D.first.right ≠ D.second.right := Grid.ne_right_of_mem_cIoo hself
  have hDfr : D.second.right ≠ D.first.left := fun h => D.second.left_ne_right (hcommon ▸ h.symm)
  -- The first rectangle of the recut runs from the rectangle's terminal side to the pentagon's,
  -- so it fixes the row of the common side, and it moves the row of its own initial side.
  constructor
  · rw [GridRectangleBetween.bottom_def, GridRectangleBetween.bottom_def, hEsl,
      E.first.map_of_ne _ (hEfl ▸ D.first.left_ne_right) (hdata.recut_sides.1 ▸ hDfr.symm)]
  · rw [GridRectangleBetween.top_def, GridRectangleBetween.top_def, hdata.recut_sides.2, ← hEfl,
      E.first.map_left, hdata.recut_sides.1,
      D.first.map_of_ne _ (hcommon ▸ D.second.left_ne_right).symm hfr.symm]

include hcommon hself in
/-- In the common-initial-side overlap whose rectangle's terminal side lies inside the pentagon's
column interval, the second rectangle of the recut starts on the replaced grid line. -/
theorem recut_second_left_of_left_eq_left :
    (D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
      hfirst hsecond).second.left = finRotate n a :=
  (D.recut_lefts_of_left_eq_left_self hcommon hfirst hsecond hself).2.trans
    (hcommon.trans D.second_left_eq)

include hcommon hself in
/-- In the common-initial-side overlap whose rectangle's terminal side lies inside the pentagon's
column interval, the second rectangle of the recut contains the turn row on its initial side: its
rows contain those of the original pentagon. -/
theorem turn_mem_recut_second_of_left_eq_left :
    s ∈ Grid.cIco
      (D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
        hfirst hsecond).second.bottom
      (D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
        hfirst hsecond).second.top := by
  have hturn := D.second_turn_mem
  rw [D.second_bottom_eq_first_top hcommon] at hturn
  obtain ⟨hbottom, htop⟩ := D.recut_second_bottom_top_of_left_eq_left_self hcommon hfirst hsecond
    hself
  rw [hbottom, htop]
  exact Grid.cIco_subset_of_mem_cIoo (D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
    (Grid.ne_right_of_mem_cIoo hself) hfirst hsecond).2 hturn

include hcommon hself in
/-- Recut a rectangle followed by an initial-side pentagon when their unique common side is
initial for both and the rectangle's terminal side lies inside the pentagon's column interval,
and promote the second new rectangle to an initial-side pentagon. The result is again a
rectangle followed by an initial-side pentagon. -/
noncomputable def recutLeftEqLeftSecond : GridRectangleInitialPentagonDecomposition a s x z where
  toGridRectangleDecomposition :=
    D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
      hfirst hsecond
  second_left_eq := D.recut_second_left_of_left_eq_left hcommon hfirst hsecond hself
  second_turn_mem := D.turn_mem_recut_second_of_left_eq_left hcommon hfirst hsecond hself

/-- Forgetting the turn row of the promoted decomposition recovers the generic recut. -/
@[simp]
theorem recutLeftEqLeftSecond_toGridRectangleDecomposition :
    (D.recutLeftEqLeftSecond hcommon hfirst hsecond hself).toGridRectangleDecomposition =
      D.recut (D.hasOneCommonSide_of_left_eq_left hcommon (Grid.ne_right_of_mem_cIoo hself))
        hfirst hsecond :=
  (rfl)

/-- The promoted decomposition carries the generic recut relation. In particular its two
underlying rectangles are empty and repartition the squares of the original two. -/
theorem isRecut_recutLeftEqLeftSecond :
    D.IsRecut (D.recutLeftEqLeftSecond hcommon hfirst hsecond hself).toGridRectangleDecomposition :=
  D.isRecut_recut _ hfirst hsecond

/-- The promoted decomposition starts on the original rectangle's terminal side. -/
@[simp]
theorem recutLeftEqLeftSecond_first_left :
    (D.recutLeftEqLeftSecond hcommon hfirst hsecond hself).first.left = D.first.right :=
  (D.recut_lefts_of_left_eq_left_self hcommon hfirst hsecond hself).1

/-- The promoted pentagon ends on the original rectangle's terminal side, so the promoted
decomposition has a mixed common side. -/
@[simp]
theorem recutLeftEqLeftSecond_second_right :
    (D.recutLeftEqLeftSecond hcommon hfirst hsecond hself).second.right = D.first.right :=
  (D.isRecutOfLeftEqLeft_recut hcommon _ hfirst hsecond).recut_sides.2

/-- The promoted decomposition covers the squares of the original one with the same
multiplicities. -/
theorem coveredSquares_val_add_val_recutLeftEqLeftSecond :
    ((D.recutLeftEqLeftSecond hcommon hfirst hsecond hself).first.toGridRectangle.coveredSquares
        |>.val) +
        (D.recutLeftEqLeftSecond hcommon hfirst hsecond hself).pentagon.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  set E := D.recutLeftEqLeftSecond hcommon hfirst hsecond hself
  have hdata : D.IsRecutOfLeftEqLeft E.toGridRectangleDecomposition :=
    D.isRecutOfLeftEqLeft_recut hcommon _ hfirst hsecond
  have hEleft : E.first.left = D.first.right :=
    D.recutLeftEqLeftSecond_first_left hcommon hfirst hsecond hself
  have hEright : E.first.right = D.second.right := hdata.recut_sides.1
  have hEbottom : E.second.bottom = D.first.bottom :=
    (D.recut_second_bottom_top_of_left_eq_left_self hcommon hfirst hsecond hself).1
  have hEtop : E.second.top = D.second.top :=
    (D.recut_second_bottom_top_of_left_eq_left_self hcommon hfirst hsecond hself).2
  have hrow := (D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
    (Grid.ne_right_of_mem_cIoo hself) hfirst hsecond).2
  have hturn := D.second_turn_mem
  rw [D.second_bottom_eq_first_top hcommon] at hturn
  have hb : D.first.left = finRotate n a := hcommon.trans D.second_left_eq
  have hself' := hb ▸ hself
  -- The first rectangle of the recut runs between the two terminal sides, so it meets neither
  -- of the two columns next to the replaced line, and the original rectangle starts on the
  -- replaced line, so it misses the column before it.
  have ha : a ∉ Grid.cIco D.first.right D.second.right := fun h => by
    simpa using Grid.cIco_subset_of_mem_cIoo hself' h
  have hb' : finRotate n a ∉ Grid.cIco D.first.right D.second.right := fun h =>
    Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hself')
      (Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hself').symm) h
  have ha' : a ∉ Grid.cIco D.first.left D.first.right := by simp [hb]
  have hbmem : finRotate n a ∈ Grid.cIco D.first.left D.first.right :=
    hb ▸ Grid.left_mem_cIco D.first.left_ne_right
  have hrep := fun q => congrArg (Multiset.count q)
    (D.isRecut_recutLeftEqLeftSecond hcommon hfirst hsecond hself).isRepartition.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _),
    Finset.mem_val] at hrep
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val]
  obtain ⟨c, t⟩ := p
  by_cases hca : c = a
  -- In column `a` neither rectangle covers anything, and the two pentagons have the same top.
  · subst hca
    simp only [GridInitialPentagonBetween.mk_mem_coveredSquares_left_column,
      GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright, ha, ha',
      false_and, pentagon_toGridRectangleBetween, hEtop]
  by_cases hcb : c = finRotate n a
  -- In the column after the replaced line, the original rectangle and pentagon split the rows
  -- covered by the new pentagon at the original rectangle's top row.
  · subst hcb
    simp only [GridInitialPentagonBetween.mk_mem_coveredSquares_right_column,
      GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright, hb', hbmem,
      false_and, true_and, pentagon_toGridRectangleBetween, hEbottom,
      D.second_bottom_eq_first_top hcommon, ← D.first.bottom_def, ← D.first.top_def]
    rw [Grid.ite_mem_cIco_eq_add_of_mem_cIoo hrow hturn t]
    simp only [↓reduceIte]
    omega
  -- Away from these two columns the pentagons cover the squares of their underlying rectangles.
  · have h := hrep (c, t)
    simp only [E.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      D.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      pentagon_toGridRectangleBetween]
    omega

end GridRectangleInitialPentagonDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

section Weights

variable (R : Type*) [CommSemiring R]

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.left = D.second.left)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
  (hself : D.first.right ∈ Grid.cIoo D.first.left D.second.right)

/-- Recutting a rectangle followed by an initial-side pentagon along their common initial side,
when the rectangle's terminal side lies inside the pentagon's column interval, preserves the
weight. -/
@[simp]
theorem rectangleInitialPentagonWeight_recutLeftEqLeftSecond :
    G.rectangleInitialPentagonWeight C R (D.recutLeftEqLeftSecond hcommon hfirst hsecond hself) =
      G.rectangleInitialPentagonWeight C R D :=
  G.rectangleInitialPentagonWeight_eq_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_val_recutLeftEqLeftSecond hcommon hfirst hsecond hself)

end Weights

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.left = D.second.left)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
  (hself : D.first.right ∈ Grid.cIoo D.first.left D.second.right)

/-- The recut of a counted rectangle--initial-side pentagon domain with a common initial side,
whose rectangle's terminal side lies inside the pentagon's column interval, is again a counted
rectangle--initial-side pentagon domain. -/
theorem recutLeftEqLeftSecond_mem_rectangleInitialPentagonDecompositions
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) :
    D.recutLeftEqLeftSecond hcommon hfirst hsecond hself ∈
      G.rectangleInitialPentagonDecompositions C x z :=
  have hrecut := D.isRecut_recutLeftEqLeftSecond hcommon hfirst hsecond hself
  G.mem_rectangleInitialPentagonDecompositions_of_val_add_val_eq C hD hrecut.isEmpty_first
    hrecut.isEmpty_second
    (D.coveredSquares_val_add_val_recutLeftEqLeftSecond hcommon hfirst hsecond hself)

variable (x z) in
/-- The counted rectangle--initial-side pentagon decompositions with a common initial side whose
rectangle's terminal side lies strictly inside the pentagon's column interval. -/
noncomputable def initialPentagonInitialSelfPairSources :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectangleInitialPentagonDecompositions C x z).filter fun D =>
    D.first.left = D.second.left ∧ D.first.right ∈ Grid.cIoo D.first.left D.second.right

/-- Membership in the common-initial-side self-pair source family records counting, the common
initial side and the column order. -/
@[simp]
theorem mem_initialPentagonInitialSelfPairSources :
    D ∈ G.initialPentagonInitialSelfPairSources C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧
        D.first.left = D.second.left ∧ D.first.right ∈ Grid.cIoo D.first.left D.second.right := by
  classical
  simp [initialPentagonInitialSelfPairSources]

private theorem initialPentagonInitialSelfPairSource_data
    (hD : D ∈ G.initialPentagonInitialSelfPairSources C x z) :
    D.first.left = D.second.left ∧ D.first.IsEmpty ∧ D.second.IsEmpty ∧
      D.first.right ∈ Grid.cIoo D.first.left D.second.right := by
  obtain ⟨hcounted, hcommon, hself⟩ := (G.mem_initialPentagonInitialSelfPairSources C D).1 hD
  rw [G.mem_rectangleInitialPentagonDecompositions, G.mem_unblockedRectangles,
    G.mem_initialPentagons,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] at hcounted
  exact ⟨hcommon, hcounted.1.1, hcounted.2.1, hself⟩

private noncomputable def initialPentagonInitialSelfPairPartner
    (D : {D // D ∈ G.initialPentagonInitialSelfPairSources C x z}) :
    GridRectangleInitialPentagonDecomposition C.column C.turnRow x z :=
  D.val.recutLeftEqLeftSecond
    (G.initialPentagonInitialSelfPairSource_data C D.val D.property).1
    (G.initialPentagonInitialSelfPairSource_data C D.val D.property).2.1
    (G.initialPentagonInitialSelfPairSource_data C D.val D.property).2.2.1
    (G.initialPentagonInitialSelfPairSource_data C D.val D.property).2.2.2

private theorem initialPentagonInitialSelfPairPartner_isRecut
    (D : {D // D ∈ G.initialPentagonInitialSelfPairSources C x z}) :
    D.val.IsRecut
      (G.initialPentagonInitialSelfPairPartner C D).toGridRectangleDecomposition :=
  D.val.isRecut_recutLeftEqLeftSecond _ _ _ _

private theorem initialPentagonInitialSelfPairSource_hasOneCommonSide
    (hD : D ∈ G.initialPentagonInitialSelfPairSources C x z) : D.HasOneCommonSide :=
  have hdata := G.initialPentagonInitialSelfPairSource_data C D hD
  D.hasOneCommonSide_of_left_eq_left hdata.1 (Grid.ne_right_of_mem_cIoo hdata.2.2.2)

private theorem initialPentagonInitialSelfPairPartner_injective :
    Function.Injective (G.initialPentagonInitialSelfPairPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.initialPentagonInitialSelfPairPartner_isRecut C D
  have hE := G.initialPentagonInitialSelfPairPartner_isRecut C E
  rw [← h] at hE
  obtain ⟨-, hfD, hsD, -⟩ := G.initialPentagonInitialSelfPairSource_data C D.val D.property
  obtain ⟨-, hfE, hsE, -⟩ := G.initialPentagonInitialSelfPairSource_data C E.val E.property
  have honeD := G.initialPentagonInitialSelfPairSource_hasOneCommonSide C D.val D.property
  have honeE := G.initialPentagonInitialSelfPairSource_hasOneCommonSide C E.val E.property
  have hbackD := hD.symm honeD hfD hsD
  have hbackE := hE.symm honeE hfE hsE
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

private theorem initialPentagonInitialSelfPairPartner_mem
    (D : {D // D ∈ G.initialPentagonInitialSelfPairSources C x z}) :
    G.initialPentagonInitialSelfPairPartner C D ∈
      G.rectangleInitialPentagonDecompositions C x z := by
  unfold initialPentagonInitialSelfPairPartner
  exact G.recutLeftEqLeftSecond_mem_rectangleInitialPentagonDecompositions C D.val _ _ _ _
    ((G.mem_initialPentagonInitialSelfPairSources C D.val).1 D.property).1

/-- A partner starts on the source rectangle's terminal side, not on the replaced grid line where
its pentagon starts, so it is not itself a source. -/
private theorem initialPentagonInitialSelfPairPartner_notMem
    (D : {D // D ∈ G.initialPentagonInitialSelfPairSources C x z}) :
    G.initialPentagonInitialSelfPairPartner C D ∉
      G.initialPentagonInitialSelfPairSources C x z := by
  intro h
  have hcommon := ((G.mem_initialPentagonInitialSelfPairSources C _).1 h).2.1
  obtain ⟨hDcommon, -, -, -⟩ := G.initialPentagonInitialSelfPairSource_data C D.val D.property
  unfold initialPentagonInitialSelfPairPartner at hcommon
  rw [GridRectangleInitialPentagonDecomposition.recutLeftEqLeftSecond_first_left,
    GridRectangleInitialPentagonDecomposition.second_left_eq, ← D.val.second_left_eq,
    ← hDcommon] at hcommon
  exact D.val.first.left_ne_right hcommon.symm

variable (x z) in
/-- All common-initial-side self pairs: the sources together with their distinct counted
rectangle--initial-side pentagon recuts. -/
noncomputable def initialPentagonInitialSelfPairs :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonInitialSelfPairSources C x z).withPartners
    ⟨G.initialPentagonInitialSelfPairPartner C, G.initialPentagonInitialSelfPairPartner_injective C⟩

/-- The common-initial-side self pairs consist of the sources and the recuts of sources, the
recut relation on the underlying rectangles specifying the partner uniquely. -/
@[simp]
theorem mem_initialPentagonInitialSelfPairs
    (E : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonInitialSelfPairs C x z ↔
      E ∈ G.initialPentagonInitialSelfPairSources C x z ∨
        ∃ D ∈ G.initialPentagonInitialSelfPairSources C x z,
          D.IsRecut E.toGridRectangleDecomposition := by
  classical
  simp only [initialPentagonInitialSelfPairs, Finset.mem_withPartners,
    Function.Embedding.coeFn_mk]
  apply or_congr_right
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.initialPentagonInitialSelfPairPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨-, hf, hs, -⟩ := G.initialPentagonInitialSelfPairSource_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
    exact (D.existsUnique_isRecut
      (G.initialPentagonInitialSelfPairSource_hasOneCommonSide C D hD) hf hs).unique
      (G.initialPentagonInitialSelfPairPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Every term of a common-initial-side self pair is counted in the rectangle--initial-side
pentagon sum. -/
theorem initialPentagonInitialSelfPairs_subset :
    G.initialPentagonInitialSelfPairs C x z ⊆ G.rectangleInitialPentagonDecompositions C x z := by
  classical
  intro E hE
  rw [initialPentagonInitialSelfPairs, Finset.mem_withPartners] at hE
  rcases hE with hE | ⟨D, rfl⟩
  · exact ((G.mem_initialPentagonInitialSelfPairSources C E).1 hE).1
  · exact G.initialPentagonInitialSelfPairPartner_mem C D

variable (R : Type*) [CommSemiring R]

variable (x z) in
/-- The contributions of the common-initial-side self pairs cancel in characteristic two: each
source and its recut are distinct terms with the same weight. -/
theorem sum_rectangleInitialPentagonWeight_initialSelfPairs_eq_zero [CharP R 2] :
    ∑ D ∈ G.initialPentagonInitialSelfPairs C x z, G.rectangleInitialPentagonWeight C R D = 0 := by
  classical
  have hweight (D : {D // D ∈ G.initialPentagonInitialSelfPairSources C x z}) :
      G.rectangleInitialPentagonWeight C R (G.initialPentagonInitialSelfPairPartner C D) =
        G.rectangleInitialPentagonWeight C R D.val :=
    G.rectangleInitialPentagonWeight_recutLeftEqLeftSecond C R D.val _ _ _ _
  apply Finset.sum_withPartners_eq_zero (G.initialPentagonInitialSelfPairSources C x z)
    ⟨G.initialPentagonInitialSelfPairPartner C, G.initialPentagonInitialSelfPairPartner_injective C⟩
    (G.rectangleInitialPentagonWeight C R) (G.initialPentagonInitialSelfPairPartner_notMem C)
  intro D
  simpa only [Function.Embedding.coeFn_mk, hweight] using
    CharTwo.add_self_eq_zero (G.rectangleInitialPentagonWeight C R D.val)

variable (x z) in
open scoped Classical in
/-- Over a coefficient semiring of characteristic two, the common-initial-side self pairs can be
removed from the rectangle--initial-side pentagon sum. -/
theorem sum_rectangleInitialPentagonWeight_eq_sum_sdiff_initialSelfPairs [CharP R 2] :
    ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z, G.rectangleInitialPentagonWeight C R D =
      ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z \
          G.initialPentagonInitialSelfPairs C x z,
        G.rectangleInitialPentagonWeight C R D := by
  rw [← Finset.sum_sdiff (G.initialPentagonInitialSelfPairs_subset C)
      (f := G.rectangleInitialPentagonWeight C R),
    G.sum_rectangleInitialPentagonWeight_initialSelfPairs_eq_zero C x z R, add_zero]

end GridDiagram

end TauCeti
