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
# Initial-side self-recuts of an initial-side pentagon followed by a rectangle

Let `b = finRotate n a` be the grid line replaced in a column commutation. A pentagon turning on
its initial side starts on `b`. Take such a pentagon, from `b` to `f`, followed by a rectangle of
the commuted diagram sharing exactly its initial side `b`, and ending on a line `d` strictly
inside the column interval from `b` to `f`. Forgetting the turn point, the two domains form an
L-shaped domain of two empty rectangles sharing their initial side, and the generic recut of
`Differential/Square/Recut` cuts it the other way: first from `b` to `d`, then from `d` to `f`.
Emptiness puts the rows of `x` on `b`, `f` and `d` in this cyclic order, so the first recut
rectangle has the rows of the original pentagon and more, hence contains the turn row. It is
again an initial-side pentagon, and the recut is an initial-side pentagon followed by a rectangle
of the commuted diagram (`GridInitialPentagonRectangleDecomposition.recutInitialSelf`), now with
a mixed common side.

The second recut rectangle meets neither of the two columns next to `b`. In the column after `b`
both pentagons cover the rows from the row of `x` on `b` up to the turn row. In the column before
`b`, the new pentagon covers the rows strictly above the turn row up to the row of `x` on `d`,
which the original pentagon and the original rectangle, read in the original diagram with the two
commuted columns exchanged, split at the row of `x` on `f`. So the two composite domains cover the
same squares with the same multiplicities (`coveredSquares_val_add_val_recutInitialSelf`): a
counted domain recuts to a counted domain of the same monomial weight. These are fixed-point-free
pairs within the initial-side pentagon--rectangle coefficient sum of the commutation chain-map
equation, and they cancel over coefficients of characteristic two. This is the counterpart, for
pentagons turning on their initial side, of the terminal self-pairs of
`Commutation/Overlap/PentagonTerminal`.

## Main definitions

* `TauCeti.GridInitialPentagonRectangleDecomposition.recutInitialSelf`: the recut, promoted to an
  initial-side pentagon followed by a rectangle.
* `TauCeti.GridDiagram.initialPentagonRectangleInitialSelfSources`: the counted initial-side
  pentagon--rectangle domains with a common initial side whose rectangle ends strictly inside the
  pentagon's column interval.
* `TauCeti.GridDiagram.initialPentagonRectangleInitialSelfPairs`: these sources together with
  their recuts.

## Main results

* `TauCeti.GridInitialPentagonRectangleDecomposition.coveredSquares_val_add_val_recutInitialSelf`:
  both decompositions cover the same squares with the same multiplicities.
* `TauCeti.GridDiagram.recutInitialSelf_mem_initialPentagonRectangleDecompositions` and
  `TauCeti.GridDiagram.initialPentagonRectangleWeight_recutInitialSelf`: the recut of a counted
  domain is counted, with the same weight.
* `TauCeti.GridDiagram.sum_initialPentagonRectangleWeight_initialSelfPairs_eq_zero` and
  `TauCeti.GridDiagram.sum_initialPentagonRectangleWeight_eq_sum_sdiff_initialSelfPairs`: the
  pairs cancel in characteristic two and can be removed from the coefficient sum.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

variable (D : GridInitialPentagonRectangleDecomposition a s x z)
  (hcommon : D.first.left = D.second.left)
  (hcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

include hcommon hcol in
/-- The first recut rectangle contains the turn row: its rows contain those of the original
pentagon. -/
private theorem turn_mem_recut_first :
    s ∈ Grid.cIco
      (D.toGridRectangleDecomposition.recut
          (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hcol)
            hfirst hsecond).first.bottom
      (D.toGridRectangleDecomposition.recut
          (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hcol)
            hfirst hsecond).first.top := by
  obtain ⟨hbottom, htop⟩ :=
    D.toGridRectangleDecomposition.recut_first_bottom_top_of_left_eq_left_of_mem_cIoo hcommon hcol
      hfirst hsecond
  rw [hbottom, htop, ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo
    (D.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
      (Grid.ne_right_of_mem_cIoo hcol).symm hfirst hsecond).2]
  exact Finset.mem_union_left _ D.first_turn_mem

include hcommon hcol in
/-- Recut an initial-side pentagon followed by a rectangle sharing their initial side, when the
rectangle ends strictly inside the pentagon's column interval. The first recut rectangle again
starts on the replaced grid line and contains the turn row, so it is an initial-side pentagon. -/
noncomputable def recutInitialSelf : GridInitialPentagonRectangleDecomposition a s x z where
  toGridTwoStepDecomposition :=
    D.toGridRectangleDecomposition.recut
        (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hcol)
          hfirst hsecond
  first_left_eq :=
    (D.toGridRectangleDecomposition.recut_sides_of_left_eq_left_of_mem_cIoo hcommon hcol hfirst
      hsecond).1.trans D.first_left_eq
  first_turn_mem := D.turn_mem_recut_first hcommon hcol hfirst hsecond

/-- Forgetting the turn row of the promoted decomposition recovers the generic recut. -/
@[simp]
theorem recutInitialSelf_toGridRectangleDecomposition :
    (D.recutInitialSelf hcommon hcol hfirst hsecond).toGridRectangleDecomposition =
      D.toGridRectangleDecomposition.recut
          (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hcol)
            hfirst hsecond :=
  (rfl)

/-- The promoted decomposition carries the generic recut relation. In particular its two
underlying rectangles are empty and repartition the squares of the original two. -/
theorem isRecut_recutInitialSelf :
    D.toGridRectangleDecomposition.IsRecut
        (D.recutInitialSelf hcommon hcol hfirst hsecond).toGridRectangleDecomposition :=
  D.toGridRectangleDecomposition.isRecut_recut
      (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hcol)
        hfirst hsecond

/-- The recut extends the pentagon up to the rectangle's top row and cuts off the remaining
rectangle between the two terminal sides. The new common side is terminal for the pentagon and
initial for the rectangle. -/
theorem recutInitialSelf_geometry :
    let E := D.recutInitialSelf hcommon hcol hfirst hsecond
    E.first.right = D.second.right ∧ E.first.bottom = D.first.bottom ∧
      E.first.top = D.second.top ∧ E.second.left = D.second.right ∧
        E.second.right = D.first.right := by
  obtain ⟨-, hright, hsecondLeft, hsecondRight⟩ :=
    D.toGridRectangleDecomposition.recut_sides_of_left_eq_left_of_mem_cIoo hcommon hcol hfirst
      hsecond
  obtain ⟨hbottom, htop⟩ :=
    D.toGridRectangleDecomposition.recut_first_bottom_top_of_left_eq_left_of_mem_cIoo hcommon hcol
      hfirst hsecond
  exact ⟨hright, hbottom, htop, hsecondLeft, hsecondRight⟩

/-- The original and recut initial-side pentagon--rectangle domains cover the same squares with
the same multiplicities, the rectangles of the commuted diagram being read in the original diagram
with the two columns next to the replaced line exchanged. -/
theorem coveredSquares_val_add_val_recutInitialSelf :
    let E := D.recutInitialSelf hcommon hcol hfirst hsecond
    E.pentagon.coveredSquares.val +
        (E.second.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.pentagon.coveredSquares.val +
        (D.second.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val := by
  intro E
  obtain ⟨-, hEbottom, hEtop, hEleft, hEright⟩ :
      E.first.right = D.second.right ∧ E.first.bottom = D.first.bottom ∧
        E.first.top = D.second.top ∧ E.second.left = D.second.right ∧
          E.second.right = D.first.right :=
    D.recutInitialSelf_geometry hcommon hcol hfirst hsecond
  have hrow := (D.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
    (Grid.ne_right_of_mem_cIoo hcol).symm hfirst hsecond).2
  have hb : D.first.left = finRotate n a := D.first_left_eq
  have hcol' := hb ▸ hcol
  -- The rectangle of the recut runs between the two terminal sides, so it meets neither of the
  -- two columns next to the replaced line; the original rectangle starts on the replaced line, so
  -- it covers the column after it and misses the column before it.
  have haE : a ∉ Grid.cIco D.second.right D.first.right := fun h => by
    simpa using Grid.cIco_subset_of_mem_cIoo hcol' h
  have hbE : finRotate n a ∉ Grid.cIco D.second.right D.first.right := fun h =>
    Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol')
      (Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol').symm) h
  have haD : a ∉ Grid.cIco D.second.left D.second.right := by simp [← hcommon, hb]
  have hbD : finRotate n a ∈ Grid.cIco D.second.left D.second.right := by
    rw [← hcommon, hb]
    exact Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol').symm
  have hrep := fun q => congrArg (Multiset.count q)
    (D.isRecut_recutInitialSelf hcommon hcol hfirst hsecond).isRepartition.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _),
    Finset.mem_val] at hrep
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply]
  obtain ⟨c, t⟩ := p
  simp only [Prod.map_apply, Equiv.refl_apply]
  by_cases hca : c = a
  -- In the column before the replaced line, the new pentagon covers the rows the original
  -- pentagon and rectangle cover there, split at the original pentagon's top row.
  · subst c
    have hsplit := Grid.ite_mem_cIoo_eq_add_of_mem_cIoo hrow D.first_turn_mem t
    simp only [GridInitialPentagonBetween.mk_mem_coveredSquares_left_column,
      Equiv.swap_apply_left, pentagon_toGridRectangleBetween,
      GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright, hbE, hbD,
      false_and, true_and, ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def,
      hEtop, D.toGridRectangleDecomposition.second_bottom_eq_first_top_of_left_eq_left hcommon]
    simpa only [↓reduceIte, add_zero] using hsplit
  -- In the column after the replaced line, both pentagons cover the rows from their common
  -- bottom row up to the turn row, and neither rectangle covers anything.
  by_cases hcb : c = finRotate n a
  · subst c
    simp only [GridInitialPentagonBetween.mk_mem_coveredSquares_right_column,
      Equiv.swap_apply_right, pentagon_toGridRectangleBetween,
      GridRectangleBetween.mem_toGridRectangle_coveredSquares, hEleft, hEright, haE, haD,
      false_and, hEbottom]
  -- On every other column the pentagons are their underlying rectangles, which repartition the
  -- same squares.
  · have h := hrep (c, t)
    simp only [Equiv.swap_apply_of_ne_of_ne hca hcb,
      E.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      D.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      pentagon_toGridRectangleBetween]
    omega

end GridInitialPentagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

section Recut

variable (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
  (hcommon : D.first.left = D.second.left)
  (hcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

/-- The initial-side self-recut of a counted initial-side pentagon--rectangle domain is counted:
both emptiness and `X`-avoidance transfer from the original composite domain. -/
theorem recutInitialSelf_mem_initialPentagonRectangleDecompositions
    (hD : D ∈ G.initialPentagonRectangleDecompositions C x z) :
    D.recutInitialSelf hcommon hcol hfirst hsecond ∈
      G.initialPentagonRectangleDecompositions C x z := by
  classical
  let E := D.recutInitialSelf hcommon hcol hfirst hsecond
  let e := ((Equiv.swap C.column (finRotate n C.column)).prodCongr
    (Equiv.refl (Fin n))).toEmbedding
  rw [mem_initialPentagonRectangleDecompositions, mem_initialPentagons,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween,
    (G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles,
    ← G.disjoint_map_swapColumns_XSet_iff] at hD ⊢
  have hunion := congrArg Multiset.toFinset
    (D.coveredSquares_val_add_val_recutInitialSelf hcommon hcol hfirst hsecond)
  simp only [Multiset.toFinset_add, Finset.val_toFinset] at hunion
  have hnew : Disjoint (E.pentagon.coveredSquares ∪
      E.second.toGridRectangle.coveredSquares.map e) G.XSet := by
    rw [hunion]
    exact Finset.disjoint_union_left.mpr ⟨hD.1.2, hD.2.2⟩
  have hrecut := D.isRecut_recutInitialSelf hcommon hcol hfirst hsecond
  exact ⟨⟨hrecut.isEmpty_first, (Finset.disjoint_union_left.mp hnew).1⟩, hrecut.isEmpty_second,
    (Finset.disjoint_union_left.mp hnew).2⟩

/-- The initial-side self-recut preserves the monomial contribution to the initial-side
pentagon--rectangle coefficient sum over any commutative semiring. -/
@[simp]
theorem initialPentagonRectangleWeight_recutInitialSelf (R : Type*) [CommSemiring R] :
    G.initialPentagonRectangleWeight C R (D.recutInitialSelf hcommon hcol hfirst hsecond) =
      G.initialPentagonRectangleWeight C R D :=
  G.initialPentagonRectangleWeight_eq_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_val_recutInitialSelf hcommon hcol hfirst hsecond)

end Recut

/-! ### Cancelling the initial-side self-pairs -/

/-- The counted initial-side pentagon--rectangle domains with a common initial side whose
rectangle ends strictly inside the pentagon's column interval: their recuts stay in the same
coefficient sum. -/
noncomputable def initialPentagonRectangleInitialSelfSources (x z : GridState n) :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonRectangleDecompositions C x z).filter fun D =>
    D.first.left = D.second.left ∧ D.second.right ∈ Grid.cIoo D.first.left D.first.right

/-- Membership in the initial-side self source family records counting and the column order
selecting the self-recut. -/
@[simp]
theorem mem_initialPentagonRectangleInitialSelfSources
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    D ∈ G.initialPentagonRectangleInitialSelfSources C x z ↔
      D ∈ G.initialPentagonRectangleDecompositions C x z ∧
        D.first.left = D.second.left ∧ D.second.right ∈ Grid.cIoo D.first.left D.first.right := by
  classical
  simp [initialPentagonRectangleInitialSelfSources]

private theorem initialPentagonRectangleInitialSelfSource_data
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.initialPentagonRectangleInitialSelfSources C x z) :
    D.first.left = D.second.left ∧ D.second.right ∈ Grid.cIoo D.first.left D.first.right ∧
      D.first.IsEmpty ∧ D.second.IsEmpty := by
  obtain ⟨hcounted, hcommon, hcol⟩ :=
    (G.mem_initialPentagonRectangleInitialSelfSources C D).1 hD
  obtain ⟨hP, hR⟩ := (G.mem_initialPentagonRectangleDecompositions C D).1 hcounted
  rw [mem_initialPentagons,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween] at hP
  exact ⟨hcommon, hcol, hP.1,
    (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1⟩

private noncomputable def initialPentagonRectangleInitialSelfPartner
    (D : {D // D ∈ G.initialPentagonRectangleInitialSelfSources C x z}) :
    GridInitialPentagonRectangleDecomposition C.column C.turnRow x z :=
  D.val.recutInitialSelf (G.initialPentagonRectangleInitialSelfSource_data C D.val D.property).1
    (G.initialPentagonRectangleInitialSelfSource_data C D.val D.property).2.1
    (G.initialPentagonRectangleInitialSelfSource_data C D.val D.property).2.2.1
    (G.initialPentagonRectangleInitialSelfSource_data C D.val D.property).2.2.2

private theorem initialPentagonRectangleInitialSelfPartner_isRecut
    (D : {D // D ∈ G.initialPentagonRectangleInitialSelfSources C x z}) :
    D.val.toGridRectangleDecomposition.IsRecut
      (G.initialPentagonRectangleInitialSelfPartner C D).toGridRectangleDecomposition :=
  D.val.isRecut_recutInitialSelf _ _ _ _

private theorem initialPentagonRectangleInitialSelfPartner_injective :
    Function.Injective (G.initialPentagonRectangleInitialSelfPartner C (x := x) (z := z)) := by
  intro D F h
  have hD := G.initialPentagonRectangleInitialSelfPartner_isRecut C D
  have hF := G.initialPentagonRectangleInitialSelfPartner_isRecut C F
  rw [← h] at hF
  obtain ⟨hcommonD, hcolD, hfirstD, hsecondD⟩ :=
    G.initialPentagonRectangleInitialSelfSource_data C D.val D.property
  obtain ⟨hcommonF, hcolF, hfirstF, hsecondF⟩ :=
    G.initialPentagonRectangleInitialSelfSource_data C F.val F.property
  have honeD :=
    D.val.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommonD hcolD
  have hbackD := hD.symm honeD hfirstD hsecondD
  have hbackF := hF.symm
    (F.val.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommonF
      hcolF) hfirstF hsecondF
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackF

private theorem initialPentagonRectangleInitialSelfPartner_mem
    (D : {D // D ∈ G.initialPentagonRectangleInitialSelfSources C x z}) :
    G.initialPentagonRectangleInitialSelfPartner C D ∈
      G.initialPentagonRectangleDecompositions C x z :=
  G.recutInitialSelf_mem_initialPentagonRectangleDecompositions C D.val _ _ _ _
    ((G.mem_initialPentagonRectangleInitialSelfSources C D.val).1 D.property).1

private theorem initialPentagonRectangleInitialSelfPartner_notMem
    (D : {D // D ∈ G.initialPentagonRectangleInitialSelfSources C x z}) :
    G.initialPentagonRectangleInitialSelfPartner C D ∉
      G.initialPentagonRectangleInitialSelfSources C x z := by
  intro h
  have hcommon := ((G.mem_initialPentagonRectangleInitialSelfSources C _).1 h).2.1
  obtain ⟨hcommonD, hcolD, hfirstD, hsecondD⟩ :=
    G.initialPentagonRectangleInitialSelfSource_data C D.val D.property
  obtain ⟨-, -, -, hleft, -⟩ := D.val.recutInitialSelf_geometry hcommonD hcolD hfirstD hsecondD
  -- The partner's rectangle starts on the original rectangle's terminal side, which is not the
  -- replaced line on which its pentagon starts.
  exact Grid.ne_left_of_mem_cIoo hcolD
    (hleft.symm.trans (hcommon.symm.trans ((G.initialPentagonRectangleInitialSelfPartner C
      D).first_left_eq.trans D.val.first_left_eq.symm)))

/-- All initial-side self-pairs of the initial-side pentagon--rectangle coefficient sum: each
source together with its distinct recut. -/
noncomputable def initialPentagonRectangleInitialSelfPairs (x z : GridState n) :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonRectangleInitialSelfSources C x z).withPartners
    ⟨G.initialPentagonRectangleInitialSelfPartner C,
      G.initialPentagonRectangleInitialSelfPartner_injective C⟩

/-- The initial-side self-pair family consists exactly of the sources and their recuts. -/
@[simp]
theorem mem_initialPentagonRectangleInitialSelfPairs
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonRectangleInitialSelfPairs C x z ↔
      E ∈ G.initialPentagonRectangleInitialSelfSources C x z ∨
        ∃ D ∈ G.initialPentagonRectangleInitialSelfSources C x z,
          D.toGridRectangleDecomposition.IsRecut E.toGridRectangleDecomposition := by
  classical
  simp only [initialPentagonRectangleInitialSelfPairs, Finset.mem_withPartners,
    Function.Embedding.coeFn_mk]
  apply or_congr_right
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.initialPentagonRectangleInitialSelfPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨hcommon, hcol, hfirst, hsecond⟩ :=
      G.initialPentagonRectangleInitialSelfSource_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    exact (D.toGridRectangleDecomposition.existsUnique_isRecut
      (D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hcol)
      hfirst hsecond).unique (G.initialPentagonRectangleInitialSelfPartner_isRecut C ⟨D, hD⟩)
      hrecut

/-- Every term of an initial-side self-pair is counted in the initial-side pentagon--rectangle
coefficient sum. -/
theorem initialPentagonRectangleInitialSelfPairs_subset :
    G.initialPentagonRectangleInitialSelfPairs C x z ⊆
      G.initialPentagonRectangleDecompositions C x z := by
  classical
  intro E hE
  rw [initialPentagonRectangleInitialSelfPairs, Finset.mem_withPartners] at hE
  rcases hE with hE | ⟨D, rfl⟩
  · exact ((G.mem_initialPentagonRectangleInitialSelfSources C E).1 hE).1
  · exact G.initialPentagonRectangleInitialSelfPartner_mem C D

/-- The contributions of the initial-side self-pairs cancel in characteristic two. -/
theorem sum_initialPentagonRectangleWeight_initialSelfPairs_eq_zero
    (R : Type*) [CommSemiring R] [CharP R 2] (x z : GridState n) :
    ∑ D ∈ G.initialPentagonRectangleInitialSelfPairs C x z,
      G.initialPentagonRectangleWeight C R D = 0 := by
  classical
  have hweight (D : {D // D ∈ G.initialPentagonRectangleInitialSelfSources C x z}) :
      G.initialPentagonRectangleWeight C R (G.initialPentagonRectangleInitialSelfPartner C D) =
        G.initialPentagonRectangleWeight C R D.val :=
    G.initialPentagonRectangleWeight_recutInitialSelf C D.val _ _ _ _ R
  apply Finset.sum_withPartners_eq_zero (G.initialPentagonRectangleInitialSelfSources C x z)
    ⟨G.initialPentagonRectangleInitialSelfPartner C,
      G.initialPentagonRectangleInitialSelfPartner_injective C⟩
    (G.initialPentagonRectangleWeight C R)
    (G.initialPentagonRectangleInitialSelfPartner_notMem C)
  intro D
  simpa only [Function.Embedding.coeFn_mk, hweight] using
    (CharTwo.add_self_eq_zero (G.initialPentagonRectangleWeight C R D.val))

open scoped Classical in
/-- Remove all initial-side self-pairs from the initial-side pentagon--rectangle coefficient sum
over a semiring of characteristic two. -/
theorem sum_initialPentagonRectangleWeight_eq_sum_sdiff_initialSelfPairs
    (R : Type*) [CommSemiring R] [CharP R 2] (x z : GridState n) :
    (∑ D ∈ G.initialPentagonRectangleDecompositions C x z,
        G.initialPentagonRectangleWeight C R D) =
      ∑ D ∈ G.initialPentagonRectangleDecompositions C x z \
          G.initialPentagonRectangleInitialSelfPairs C x z,
        G.initialPentagonRectangleWeight C R D := by
  classical
  have h := Finset.sum_sdiff (G.initialPentagonRectangleInitialSelfPairs_subset C (x := x)
    (z := z)) (f := G.initialPentagonRectangleWeight C R)
  rw [G.sum_initialPentagonRectangleWeight_initialSelfPairs_eq_zero C R x z, add_zero] at h
  exact h.symm

end GridDiagram

end TauCeti
