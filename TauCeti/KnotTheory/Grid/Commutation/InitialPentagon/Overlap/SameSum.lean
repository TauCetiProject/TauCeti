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
# Same-sum recuts of initial-side pentagons

Consider a rectangle followed by a commutation pentagon turning on its initial side, with both
domains starting on the replaced grid line. If the rectangle's terminal side lies strictly inside
the pentagon's column interval, the generic rectangle recut again has its second rectangle starting
on the replaced line. The recut therefore promotes to another rectangle followed by an initial-side
pentagon. Its pentagon extends down through the rows of the original rectangle, while its first
rectangle occupies the complementary upper-right part of the domain.

The two decompositions cover the same squares with the same multiplicities, so counted terms recut
to counted terms of the same monomial weight. They form fixed-point-free pairs within the
rectangle--initial-side-pentagon coefficient sum and cancel over coefficients of characteristic
two. This is the same-sum branch of the common-initial-side overlap in the commutation chain-map
equation.

## Main definitions

* `TauCeti.GridRectangleInitialPentagonDecomposition.recutInitialSelf`: the promoted recut.
* `TauCeti.GridDiagram.initialPentagonInitialSelfPairs`: the finite family of sources and their
  recut partners.

## Main results

* `TauCeti.GridDiagram.recutInitialSelf_mem_rectangleInitialPentagonDecompositions`: counted
  sources have counted recuts.
* `TauCeti.GridDiagram.sum_rectangleInitialPentagonWeight_initialSelfPairs_eq_zero`: the paired
  contribution vanishes in characteristic two.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- A common-initial-side overlap whose rectangle ends strictly inside the pentagon's column
interval shares exactly one side column. -/
theorem hasOneCommonSide_of_initial_self (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right) :
    D.HasOneCommonSide := by
  apply D.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨D.first.left, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, hcommon] at hc
    have _ := Grid.ne_right_of_mem_cIoo hcol
    grind

private theorem underlying_first_isEmpty
    (D : GridRectangleInitialPentagonDecomposition a s x z) (h : D.first.IsEmpty) :
    D.toGridRectangleDecomposition.first.IsEmpty := by
  exact h

private theorem underlying_second_isEmpty
    (D : GridRectangleInitialPentagonDecomposition a s x z) (h : D.pentagon.IsEmpty) :
    D.toGridRectangleDecomposition.second.IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] at h ⊢
  simpa only [D.pentagon_toGridRectangleBetween] using h

private noncomputable def initialSelfRecut
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    GridRectangleDecomposition x z :=
  D.toGridRectangleDecomposition.recut (D.hasOneCommonSide_of_initial_self hcommon hcol)
    (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)

private theorem initialSelfRecut_data
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    let E := D.initialSelfRecut hcommon hcol hfirst hsecond
    E.middle = x.swapColumns D.first.right D.second.right ∧
      E.first.left = D.first.right ∧ E.first.right = D.second.right ∧
        E.second.left = D.first.left ∧ E.second.right = D.first.right := by
  have hdata := D.toGridRectangleDecomposition.isRecutOfLeftEqLeft_recut hcommon
    (D.hasOneCommonSide_of_initial_self hcommon hcol)
    (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)
  obtain ⟨hfirstRight, hsecondRight⟩ := hdata.recut_sides
  rcases hdata.recut_branch with h | h
  · simpa only [initialSelfRecut] using
      And.intro h.2.1 (And.intro h.2.2.1 (And.intro hfirstRight
        (And.intro h.2.2.2 hsecondRight)))
  · have hcol' : D.second.right ∈ Grid.cIoo D.second.left D.first.right := by
      simpa only [hcommon] using h.1
    exact False.elim (Finset.disjoint_left.mp
      (Grid.disjoint_cIoo_swap D.second.left D.second.right)
      hcol (Grid.mem_cIoo_cyclic_left hcol'))

private theorem initial_row_order
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    D.first.top ∈ Grid.cIoo D.first.bottom D.second.top := by
  have h := D.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
    (Grid.ne_right_of_mem_cIoo hcol)
    (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)
  exact h.2

private theorem initialSelfRecut_second_rows
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    (D.initialSelfRecut hcommon hcol hfirst hsecond).second.bottom = D.first.bottom ∧
      (D.initialSelfRecut hcommon hcol hfirst hsecond).second.top = D.second.top := by
  obtain ⟨hmiddle, _, _, hleft, hright⟩ :=
    D.initialSelfRecut_data hcommon hcol hfirst hsecond
  have hbd : D.first.left ≠ D.first.right := D.first.left_ne_right
  have hbf : D.first.left ≠ D.second.right := by
    rw [hcommon]
    exact D.second.left_ne_right
  have hfleft : D.second.right ≠ D.first.left := by
    intro h
    exact D.second.left_ne_right (hcommon.symm.trans h.symm)
  constructor
  · rw [GridRectangleBetween.bottom_def, hleft, hmiddle, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne hbd hbf, GridRectangleBetween.bottom_def]
  · rw [GridRectangleBetween.top_def, hright, hmiddle, GridState.swapColumns_apply,
      Equiv.swap_apply_left, GridRectangleBetween.top_def,
      D.first.map_of_ne D.second.right hfleft
        (Grid.ne_right_of_mem_cIoo hcol).symm]

private theorem initialSelfRecut_turn_mem
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    s ∈ Grid.cIco (D.initialSelfRecut hcommon hcol hfirst hsecond).second.bottom
      (D.initialSelfRecut hcommon hcol hfirst hsecond).second.top := by
  obtain ⟨hbottom, htop⟩ := D.initialSelfRecut_second_rows hcommon hcol hfirst hsecond
  rw [hbottom, htop]
  have hturn := D.second_turn_mem
  rw [D.second_bottom_eq_first_top_of_left_eq_left hcommon] at hturn
  exact Grid.cIco_subset_of_mem_cIoo (D.initial_row_order hcommon hcol hfirst hsecond) hturn

/-- Recut a rectangle followed by an initial-side pentagon sharing its initial side, when the
rectangle ends inside the pentagon's column interval. The second recut rectangle again starts on
the replaced grid line and contains the turn row. -/
noncomputable def recutInitialSelf
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    GridRectangleInitialPentagonDecomposition a s x z where
  toGridRectangleDecomposition := D.initialSelfRecut hcommon hcol hfirst hsecond
  second_left_eq := (D.initialSelfRecut_data hcommon hcol hfirst hsecond).2.2.2.1.trans
    (hcommon.trans D.second_left_eq)
  second_turn_mem := D.initialSelfRecut_turn_mem hcommon hcol hfirst hsecond

/-- The promoted decomposition is the generic recut of the original two-step domain. -/
theorem isRecut_recutInitialSelf
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    D.toGridRectangleDecomposition.IsRecut
      (D.recutInitialSelf hcommon hcol hfirst hsecond).toGridRectangleDecomposition := by
  exact D.toGridRectangleDecomposition.isRecut_recut _ _ _

/-- The self-recut cuts off the upper-right rectangle and extends the initial-side pentagon
downward through the rows of the original rectangle. -/
theorem recutInitialSelf_geometry
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    let E := D.recutInitialSelf hcommon hcol hfirst hsecond
    E.middle = x.swapColumns D.first.right D.second.right ∧
      E.first.left = D.first.right ∧ E.first.right = D.second.right ∧
        E.second.left = D.first.left ∧ E.second.right = D.first.right ∧
          E.second.bottom = D.first.bottom ∧ E.second.top = D.second.top := by
  obtain ⟨hmiddle, hfirstLeft, hfirstRight, hsecondLeft, hsecondRight⟩ :=
    D.initialSelfRecut_data hcommon hcol hfirst hsecond
  obtain ⟨hbottom, htop⟩ := D.initialSelfRecut_second_rows hcommon hcol hfirst hsecond
  exact ⟨hmiddle, hfirstLeft, hfirstRight, hsecondLeft, hsecondRight, hbottom, htop⟩

private theorem recutInitialSelf_first_notMem_columns
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    a ∉ (D.recutInitialSelf hcommon hcol hfirst hsecond).first.toGridRectangle.coveredColumns ∧
      finRotate n a ∉
        (D.recutInitialSelf hcommon hcol hfirst hsecond).first.toGridRectangle.coveredColumns := by
  obtain ⟨_, hleft, hright, _, _, _, _⟩ :=
    D.recutInitialSelf_geometry hcommon hcol hfirst hsecond
  constructor
  · intro ha
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hleft, hright] at ha
    have ha' := Grid.cIco_subset_of_mem_cIoo hcol ha
    rw [D.second_left_eq] at ha'
    simp at ha'
  · intro hb
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hleft, hright] at hb
    have hb' : finRotate n a ∈ Grid.cIco D.second.left D.first.right := by
      rw [← D.second_left_eq]
      exact Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol).symm
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol) hb' hb

/-- The original and recut rectangle--initial-side-pentagon domains cover the same squares with
the same multiplicities. -/
theorem coveredSquares_val_add_recutInitialSelf
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    let E := D.recutInitialSelf hcommon hcol hfirst hsecond
    E.first.toGridRectangle.coveredSquares.val + E.pentagon.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  classical
  let E := D.recutInitialSelf hcommon hcol hfirst hsecond
  obtain ⟨_, _, _, _, _, hbottom, htop⟩ :=
    D.recutInitialSelf_geometry hcommon hcol hfirst hsecond
  have hPbottom : E.pentagon.bottom = D.first.bottom := by
    simpa only [E.pentagon_toGridRectangleBetween] using hbottom
  have hPtop : E.pentagon.top = D.second.top := by
    simpa only [E.pentagon_toGridRectangleBetween] using htop
  obtain ⟨haE, hbE⟩ := D.recutInitialSelf_first_notMem_columns
    hcommon hcol hfirst hsecond
  have hrow := D.initial_row_order hcommon hcol hfirst hsecond
  have hjoin : D.first.top = D.pentagon.bottom := by
    simpa only [D.pentagon_toGridRectangleBetween] using
      (D.second_bottom_eq_first_top_of_left_eq_left hcommon).symm
  have hDtop : D.pentagon.top = D.second.top := by
    simp only [D.pentagon_toGridRectangleBetween]
  have haD : a ∉ D.first.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hcommon, D.second_left_eq]
    simp
  have hbD : finRotate n a ∈ D.first.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hcommon, D.second_left_eq]
    rw [← D.second_left_eq]
    exact Grid.left_mem_cIco (Grid.ne_left_of_mem_cIoo hcol).symm
  have hrep := (D.isRecut_recutInitialSelf hcommon hcol hfirst hsecond).isRepartition.val_add_val_eq
  have hcount := fun q => congrArg (Multiset.count q) hrep
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _),
    Finset.mem_val] at hcount
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val]
  obtain ⟨c, t⟩ := p
  by_cases hca : c = a
  · subst c
    simp only [GridRectangle.mem_coveredSquares, haE, haD, false_and,
      GridInitialPentagonBetween.mk_mem_coveredSquares_left_column]
    simp only [ite_false, zero_add]
    exact congrArg (fun u => if t ∈ Grid.cIoo s u then 1 else 0)
      (hPtop.trans hDtop.symm)
  by_cases hcb : c = finRotate n a
  · subst c
    have hturn := D.pentagon.turn_mem_cIco_bottom_top
    rw [← hjoin, hDtop] at hturn
    have hsplit := Grid.ite_mem_cIco_eq_add_of_mem_cIoo hrow hturn t
    simp only [GridRectangle.mem_coveredSquares, hbE, hbD, false_and, true_and,
      GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top,
      GridInitialPentagonBetween.mk_mem_coveredSquares_right_column]
    rw [hPbottom, ← hjoin]
    simpa only [↓reduceIte, zero_add, add_comm] using hsplit
  · have h := hcount (c, t)
    simpa only [
      (D.recutInitialSelf hcommon hcol hfirst hsecond).pentagon.mem_coveredSquares_iff_of_ne
        (p := (c, t)) hca hcb,
      D.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      (D.recutInitialSelf hcommon hcol hfirst hsecond).pentagon_toGridRectangleBetween,
      D.pentagon_toGridRectangleBetween] using h

end GridRectangleInitialPentagonDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- A counted common-initial-side source has a counted same-sum recut. -/
theorem recutInitialSelf_mem_rectangleInitialPentagonDecompositions
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty)
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) :
    D.recutInitialSelf hcommon hcol hfirst hsecond ∈
      G.rectangleInitialPentagonDecompositions C x z := by
  have hrecut := D.isRecut_recutInitialSelf hcommon hcol hfirst hsecond
  refine G.mem_rectangleInitialPentagonDecompositions_of_val_add_val_eq C hD hrecut.isEmpty_first
    ?_ (D.coveredSquares_val_add_recutInitialSelf hcommon hcol hfirst hsecond)
  simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] using
    hrecut.isEmpty_second

/-- The same-sum initial-side recut preserves the monomial contribution over any commutative
semiring. -/
theorem rectangleInitialPentagonWeight_recutInitialSelf
    (R : Type*) [CommSemiring R]
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.first.left = D.second.left)
    (hcol : D.first.right ∈ Grid.cIoo D.second.left D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.pentagon.IsEmpty) :
    G.rectangleInitialPentagonWeight C R (D.recutInitialSelf hcommon hcol hfirst hsecond) =
      G.rectangleInitialPentagonWeight C R D :=
  G.rectangleInitialPentagonWeight_eq_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_recutInitialSelf hcommon hcol hfirst hsecond)

/-- The counted common-initial-side rectangle--initial-side-pentagon domains whose recuts stay
in the same coefficient sum. -/
noncomputable def initialPentagonInitialSelfSources (x z : GridState n) :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectangleInitialPentagonDecompositions C x z).filter fun D =>
    D.first.left = D.second.left ∧ D.first.right ∈ Grid.cIoo D.second.left D.second.right

/-- Membership in the common-initial-side self source family records counting and the strict
column order selecting the same-sum recut. -/
@[simp]
theorem mem_initialPentagonInitialSelfSources
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.initialPentagonInitialSelfSources C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧
        D.first.left = D.second.left ∧
          D.first.right ∈ Grid.cIoo D.second.left D.second.right := by
  classical
  simp [initialPentagonInitialSelfSources]

private theorem initialPentagonInitialSelfSource_data
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.initialPentagonInitialSelfSources C x z) :
    D.first.left = D.second.left ∧
      D.first.right ∈ Grid.cIoo D.second.left D.second.right ∧
        D.HasOneCommonSide ∧ D.first.IsEmpty ∧ D.pentagon.IsEmpty := by
  obtain ⟨hcounted, hcommon, hcol⟩ := (G.mem_initialPentagonInitialSelfSources C D).1 hD
  obtain ⟨hR, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D).1 hcounted
  exact ⟨hcommon, hcol, D.hasOneCommonSide_of_initial_self hcommon hcol,
    ((G.mem_unblockedRectangles _).1 hR).1, ((G.mem_initialPentagons _).1 hP).1⟩

private noncomputable def initialPentagonInitialSelfPartner
    (D : {D // D ∈ G.initialPentagonInitialSelfSources C x z}) :
    GridRectangleInitialPentagonDecomposition C.column C.turnRow x z :=
  D.val.recutInitialSelf
    (G.initialPentagonInitialSelfSource_data C D.val D.property).1
    (G.initialPentagonInitialSelfSource_data C D.val D.property).2.1
    (G.initialPentagonInitialSelfSource_data C D.val D.property).2.2.2.1
    (G.initialPentagonInitialSelfSource_data C D.val D.property).2.2.2.2

private theorem initialPentagonInitialSelfPartner_isRecut
    (D : {D // D ∈ G.initialPentagonInitialSelfSources C x z}) :
    D.val.toGridRectangleDecomposition.IsRecut
      (G.initialPentagonInitialSelfPartner C D).toGridRectangleDecomposition := by
  unfold initialPentagonInitialSelfPartner
  exact D.val.isRecut_recutInitialSelf _ _ _ _

private theorem initialPentagonInitialSelfPartner_injective :
    Function.Injective (G.initialPentagonInitialSelfPartner C (x := x) (z := z)) := by
  intro D E h
  have hD := G.initialPentagonInitialSelfPartner_isRecut C D
  have hE := G.initialPentagonInitialSelfPartner_isRecut C E
  rw [← h] at hE
  obtain ⟨_, _, honeD, hfirstD, hsecondD⟩ :=
    G.initialPentagonInitialSelfSource_data C D.val D.property
  obtain ⟨_, _, honeE, hfirstE, hsecondE⟩ :=
    G.initialPentagonInitialSelfSource_data C E.val E.property
  have hbackD := hD.symm honeD (D.val.underlying_first_isEmpty hfirstD)
    (D.val.underlying_second_isEmpty hsecondD)
  have hbackE := hE.symm honeE (E.val.underlying_first_isEmpty hfirstE)
    (E.val.underlying_second_isEmpty hsecondE)
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
    (D.val.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
  apply Subtype.ext
  apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
  exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
    hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE

private theorem initialPentagonInitialSelfPartner_mem
    (D : {D // D ∈ G.initialPentagonInitialSelfSources C x z}) :
    G.initialPentagonInitialSelfPartner C D ∈
      G.rectangleInitialPentagonDecompositions C x z := by
  obtain ⟨hcounted, _, _⟩ := (G.mem_initialPentagonInitialSelfSources C D.val).1 D.property
  obtain ⟨hR, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D.val).1 hcounted
  unfold initialPentagonInitialSelfPartner
  exact G.recutInitialSelf_mem_rectangleInitialPentagonDecompositions C D.val _ _
    ((G.mem_unblockedRectangles _).1 hR).1 ((G.mem_initialPentagons _).1 hP).1 hcounted

private theorem initialPentagonInitialSelfPartner_notMem
    (D : {D // D ∈ G.initialPentagonInitialSelfSources C x z}) :
    G.initialPentagonInitialSelfPartner C D ∉ G.initialPentagonInitialSelfSources C x z := by
  intro h
  have hcommon := ((G.mem_initialPentagonInitialSelfSources C _).1 h).2.1
  obtain ⟨hsourceCommon, hcol, _, hfirst, hsecond⟩ :=
    G.initialPentagonInitialSelfSource_data C D.val D.property
  obtain ⟨_, hleft, _, hsecondLeft, _, _, _⟩ :=
    D.val.recutInitialSelf_geometry hsourceCommon hcol hfirst hsecond
  exact (Grid.ne_left_of_mem_cIoo hcol)
    ((hleft.symm.trans (hcommon.trans hsecondLeft)).trans hsourceCommon)

/-- All common-initial-side same-sum pairs: each source together with its distinct recut. -/
noncomputable def initialPentagonInitialSelfPairs (x z : GridState n) :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonInitialSelfSources C x z).withPartners
    ⟨G.initialPentagonInitialSelfPartner C, G.initialPentagonInitialSelfPartner_injective C⟩

/-- The common-initial-side same-sum family consists exactly of sources and their recuts. -/
@[simp]
theorem mem_initialPentagonInitialSelfPairs
    (E : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonInitialSelfPairs C x z ↔
      E ∈ G.initialPentagonInitialSelfSources C x z ∨
        ∃ D ∈ G.initialPentagonInitialSelfSources C x z,
          D.toGridRectangleDecomposition.IsRecut E.toGridRectangleDecomposition := by
  classical
  simp only [initialPentagonInitialSelfPairs, Finset.mem_withPartners,
    Function.Embedding.coeFn_mk]
  apply or_congr_right
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨D.val, D.property, G.initialPentagonInitialSelfPartner_isRecut C D⟩
  · rintro ⟨D, hD, hrecut⟩
    obtain ⟨_, _, hone, hfirst, hsecond⟩ :=
      G.initialPentagonInitialSelfSource_data C D hD
    refine ⟨⟨D, hD⟩, ?_⟩
    apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
    exact (D.toGridRectangleDecomposition.existsUnique_isRecut hone
      (D.underlying_first_isEmpty hfirst) (D.underlying_second_isEmpty hsecond)).unique
      (G.initialPentagonInitialSelfPartner_isRecut C ⟨D, hD⟩) hrecut

/-- Every term in a common-initial-side same-sum pair belongs to the full
rectangle--initial-side-pentagon coefficient family. -/
theorem initialPentagonInitialSelfPairs_subset :
    G.initialPentagonInitialSelfPairs C x z ⊆
      G.rectangleInitialPentagonDecompositions C x z := by
  classical
  intro E hE
  rw [initialPentagonInitialSelfPairs, Finset.mem_withPartners] at hE
  rcases hE with hE | hE
  · exact ((G.mem_initialPentagonInitialSelfSources C E).1 hE).1
  · obtain ⟨D, rfl⟩ := hE
    exact G.initialPentagonInitialSelfPartner_mem C D

/-- The contributions of the common-initial-side same-sum pairs cancel in characteristic two. -/
theorem sum_rectangleInitialPentagonWeight_initialSelfPairs_eq_zero
    (R : Type*) [CommSemiring R] [CharP R 2] (x z : GridState n) :
    ∑ D ∈ G.initialPentagonInitialSelfPairs C x z,
      G.rectangleInitialPentagonWeight C R D = 0 := by
  classical
  have hweight (D : {D // D ∈ G.initialPentagonInitialSelfSources C x z}) :
      G.rectangleInitialPentagonWeight C R (G.initialPentagonInitialSelfPartner C D) =
        G.rectangleInitialPentagonWeight C R D.val := by
    unfold initialPentagonInitialSelfPartner
    exact G.rectangleInitialPentagonWeight_recutInitialSelf C R D.val _ _ _ _
  apply Finset.sum_withPartners_eq_zero (G.initialPentagonInitialSelfSources C x z)
    ⟨G.initialPentagonInitialSelfPartner C, G.initialPentagonInitialSelfPartner_injective C⟩
    (G.rectangleInitialPentagonWeight C R) (G.initialPentagonInitialSelfPartner_notMem C)
  intro D
  simpa only [Function.Embedding.coeFn_mk, hweight] using
    (CharTwo.add_self_eq_zero (G.rectangleInitialPentagonWeight C R D.val))

open scoped Classical in
/-- Remove all common-initial-side same-sum pairs from the rectangle--initial-side-pentagon
coefficient sum over a semiring of characteristic two. -/
theorem sum_rectangleInitialPentagonWeight_eq_sum_sdiff_initialSelfPairs
    (R : Type*) [CommSemiring R] [CharP R 2] (x z : GridState n) :
    (∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
        G.rectangleInitialPentagonWeight C R D) =
      ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z \
          G.initialPentagonInitialSelfPairs C x z,
        G.rectangleInitialPentagonWeight C R D := by
  classical
  have h := Finset.sum_sdiff (G.initialPentagonInitialSelfPairs_subset C (x := x) (z := z))
    (f := G.rectangleInitialPentagonWeight C R)
  rw [G.sum_rectangleInitialPentagonWeight_initialSelfPairs_eq_zero C R x z, add_zero] at h
  exact h.symm

end GridDiagram

end TauCeti
