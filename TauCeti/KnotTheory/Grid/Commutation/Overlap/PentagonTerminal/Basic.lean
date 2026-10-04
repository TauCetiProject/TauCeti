/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic

/-!
# Terminal-side recuts of a pentagon followed by a rectangle

When a pentagon and a following rectangle share their terminal side, and the initial side
of the rectangle lies inside the pentagon's column interval, the recut stays in the
pentagon--rectangle family. The first recut rectangle contains the original pentagon's
row interval, so it contains its turn row and can be promoted to a pentagon. The partner
has a mixed common side. This construction is the geometric part of their cancellation
in the commutation chain-map equation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1.
-/

public section

namespace TauCeti.GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- A terminal-side overlap with the rectangle's initial side strictly inside the pentagon's
column interval shares exactly one side column. -/
theorem hasOneCommonSide_of_terminal_overlap (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right) :
    D.toRectangleDecomposition.HasOneCommonSide := by
  apply D.toRectangleDecomposition.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨D.pentagon.right, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right, toRectangleDecomposition_second_left,
      toRectangleDecomposition_second_right, hcommon] at hc
    have hne := Grid.ne_left_of_mem_cIoo hcol
    grind

private theorem underlying_first_isEmpty (D : GridPentagonRectangleDecomposition a s x z)
    (hp : D.pentagon.IsEmpty) : D.toRectangleDecomposition.first.IsEmpty := by
  simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
    toRectangleDecomposition_first_toGridRectangle] using hp

private theorem underlying_second_isEmpty (D : GridPentagonRectangleDecomposition a s x z)
    (hr : D.rectangle.IsEmpty) : D.toRectangleDecomposition.second.IsEmpty := by
  simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
    toRectangleDecomposition_middle, toRectangleDecomposition_second_toGridRectangle] using hr

private noncomputable def terminalRecut (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) : GridRectangleDecomposition x z :=
  D.toRectangleDecomposition.recut (D.hasOneCommonSide_of_terminal_overlap hcommon hcol)
    (D.underlying_first_isEmpty hp) (D.underlying_second_isEmpty hr)

private theorem terminalRecut_data (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    let E := D.terminalRecut hcommon hcol hp hr
    E.middle = x.swapColumns D.rectangle.left D.pentagon.right ∧
      E.first.left = D.rectangle.left ∧ E.first.right = D.pentagon.right ∧
        E.second.left = D.pentagon.left ∧ E.second.right = D.rectangle.left := by
  have hdata := D.toRectangleDecomposition.isRecutOfRightEqRight_recut
    (by simpa using hcommon.symm) (D.hasOneCommonSide_of_terminal_overlap hcommon hcol)
    (D.underlying_first_isEmpty hp) (D.underlying_second_isEmpty hr)
  obtain ⟨hleft, hsecondleft⟩ := hdata.recut_sides
  rcases hdata.recut_branch with h | h
  · have hcol' : D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right := by
      simpa using h.1
    exact False.elim (Finset.disjoint_left.mp
      (Grid.disjoint_cIoo_swap D.pentagon.left D.pentagon.right)
      hcol (Grid.mem_cIoo_cyclic_right hcol'))
  · simpa only [terminalRecut, toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right, toRectangleDecomposition_second_left] using
      And.intro h.2.1 (And.intro hleft (And.intro h.2.2.1
        (And.intro hsecondleft h.2.2.2)))

private theorem terminal_row_order (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    D.pentagon.bottom ∈ Grid.cIoo D.rectangle.bottom D.pentagon.top := by
  have h := D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_right_eq_right
    (by simpa using hcommon.symm)
    (by simpa using (Grid.ne_left_of_mem_cIoo hcol).symm)
    (D.underlying_first_isEmpty hp) (D.underlying_second_isEmpty hr)
  simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
    toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left, toRectangleDecomposition_middle] using h.2

private theorem terminalRecut_first_rows (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    (D.terminalRecut hcommon hcol hp hr).first.bottom = D.rectangle.bottom ∧
      (D.terminalRecut hcommon hcol hp hr).first.top = D.pentagon.top := by
  obtain ⟨_, hl, hright, _, _⟩ := D.terminalRecut_data hcommon hcol hp hr
  constructor
  · rw [GridRectangleBetween.bottom_def, hl, GridRectangleBetween.bottom_def]
    exact (D.pentagon.map_of_ne _ (Grid.ne_left_of_mem_cIoo hcol)
      (Grid.ne_right_of_mem_cIoo hcol)).symm
  · rw [GridRectangleBetween.top_def, hright, GridRectangleBetween.top_def]

private theorem terminalRecut_turn_mem (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    s ∈ Grid.cIco (D.terminalRecut hcommon hcol hp hr).first.bottom
      (D.terminalRecut hcommon hcol hp hr).first.top := by
  obtain ⟨hb, ht⟩ := D.terminalRecut_first_rows hcommon hcol hp hr
  rw [hb, ht]
  exact Grid.cIco_subset_of_mem_cIoo (D.terminal_row_order hcommon hcol hp hr)
    D.pentagon.turn_mem

/-- Recut a pentagon followed by a rectangle sharing their terminal side, when the rectangle's
initial side is inside the pentagon's column interval. The first recut rectangle inherits
the terminal side and contains the turn row, so the result is again a pentagon followed by
a rectangle. -/
noncomputable def recutTerminal (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    GridPentagonRectangleDecomposition a s x z where
  middle := (D.terminalRecut hcommon hcol hp hr).middle
  pentagon := GridPentagonBetween.ofRightEq (D.terminalRecut hcommon hcol hp hr).first
    ((D.terminalRecut_data hcommon hcol hp hr).2.2.1.trans D.pentagon.right_eq)
    (D.terminalRecut_turn_mem hcommon hcol hp hr)
  rectangle := (D.terminalRecut hcommon hcol hp hr).second

/-- Forgetting the promoted pentagon gives the generic recut of the original rectangles. -/
private theorem recutTerminal_toRectangleDecomposition
    (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    (D.recutTerminal hcommon hcol hp hr).toRectangleDecomposition =
      D.toRectangleDecomposition.recut (D.hasOneCommonSide_of_terminal_overlap hcommon hcol)
        (D.underlying_first_isEmpty hp) (D.underlying_second_isEmpty hr) := by
  unfold recutTerminal
  apply GridRectangleDecomposition.ext
  · simp only [toRectangleDecomposition_first_left, GridPentagonBetween.ofRightEq_left]
    rfl
  · simp only [toRectangleDecomposition_first_right, GridPentagonBetween.ofRightEq_right]
    exact ((D.terminalRecut_data hcommon hcol hp hr).2.2.1.trans
      D.pentagon.right_eq).symm
  · simp only [toRectangleDecomposition_second_left]
    rfl
  · simp only [toRectangleDecomposition_second_right]
    rfl

/-- The terminal promotion really recuts the underlying two-step domain. -/
theorem isRecut_recutTerminal (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    D.toRectangleDecomposition.IsRecut
      (D.recutTerminal hcommon hcol hp hr).toRectangleDecomposition := by
  rw [D.recutTerminal_toRectangleDecomposition]
  exact D.toRectangleDecomposition.isRecut_recut _ _ _

/-- The recut enlarges the pentagon downwards, leaves its top row fixed, and cuts the remaining
rectangle along the old pentagon's initial side. The new common side is terminal for the
rectangle and initial for the pentagon. -/
theorem recutTerminal_geometry (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    let E := D.recutTerminal hcommon hcol hp hr
    E.middle = x.swapColumns D.rectangle.left D.pentagon.right ∧
      E.pentagon.left = D.rectangle.left ∧
        E.pentagon.bottom = D.rectangle.bottom ∧ E.pentagon.top = D.pentagon.top ∧
          E.rectangle.left = D.pentagon.left ∧ E.rectangle.right = D.rectangle.left := by
  obtain ⟨hm, hl, _, hrl, hrr⟩ := D.terminalRecut_data hcommon hcol hp hr
  obtain ⟨hb, ht⟩ := D.terminalRecut_first_rows hcommon hcol hp hr
  unfold recutTerminal
  simp only [GridPentagonBetween.ofRightEq_left, GridPentagonBetween.ofRightEq_bottom,
    GridPentagonBetween.ofRightEq_top]
  exact ⟨hm, hl, hb, ht, hrl, hrr⟩

private theorem recutTerminal_rectangle_notMem_columns
    (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    a ∉ (D.recutTerminal hcommon hcol hp hr).rectangle.toGridRectangle.coveredColumns ∧
      finRotate n a ∉
        (D.recutTerminal hcommon hcol hp hr).rectangle.toGridRectangle.coveredColumns := by
  obtain ⟨_, _, _, _, hl, hright⟩ := D.recutTerminal_geometry hcommon hcol hp hr
  have ha := Grid.self_mem_cIco_finRotate
    (D.pentagon.right_eq ▸ Grid.ne_right_of_mem_cIoo hcol)
  have hd := Grid.disjoint_cIco_cIco_of_mem_cIoo hcol
  constructor
  · intro h
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hl, hright] at h
    exact Finset.disjoint_left.mp hd h (D.pentagon.right_eq ▸ ha)
  · intro h
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hl, hright] at h
    have hh := Finset.mem_union_left (Grid.cIco D.rectangle.left D.pentagon.right) h
    rw [Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol, D.pentagon.right_eq] at hh
    exact Grid.right_notMem_cIco _ _ hh

/-- The terminal self-recut preserves the squares counted with multiplicity. Rectangles of the
commuted diagram are read in the original diagram by exchanging the two commuted columns.
This identity accounts for the change of the pentagon's bottom row at the replaced line. -/
theorem coveredSquares_val_add_recutTerminal
    (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    let E := D.recutTerminal hcommon hcol hp hr
    E.pentagon.coveredSquares.val +
        (E.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.pentagon.coveredSquares.val +
        (D.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val := by
  classical
  let E := D.recutTerminal hcommon hcol hp hr
  obtain ⟨_, _, hb, ht, _, _⟩ := D.recutTerminal_geometry hcommon hcol hp hr
  obtain ⟨haE, hbE⟩ := D.recutTerminal_rectangle_notMem_columns hcommon hcol hp hr
  have hrow := D.terminal_row_order hcommon hcol hp hr
  have htop : D.rectangle.top = D.pentagon.bottom := by
    rw [GridRectangleBetween.top_def, hcommon]
    exact D.pentagon.map_right
  have haD : a ∈ D.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hcommon, D.pentagon.right_eq]
    exact Grid.self_mem_cIco_finRotate
      (D.pentagon.right_eq ▸ Grid.ne_right_of_mem_cIoo hcol)
  have hbD : finRotate n a ∉ D.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_right,
      hcommon, D.pentagon.right_eq]
    exact Grid.right_notMem_cIco _ _
  have hrep := (D.isRecut_recutTerminal hcommon hcol hp hr).isRepartition.val_add_val_eq
  have hcount := fun q => congrArg (Multiset.count q) hrep
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _),
    Finset.mem_val, toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle] at hcount
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _),
    Finset.mem_val, Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap,
    Equiv.refl_symm, Equiv.prodCongr_apply]
  obtain ⟨c, t⟩ := p
  simp only [Prod.map_apply, Equiv.refl_apply]
  have hab : a ≠ finRotate n a := fun h =>
    Grid.right_notMem_cIco D.pentagon.left (finRotate n a)
      (h ▸ Grid.self_mem_cIco_finRotate D.pentagon.left_ne)
  -- At the column before the replaced line, the unchanged top row fixes the pentagon arc.
  by_cases hca : c = a
  · subst c
    simp only [GridPentagonBetween.mem_coveredSquares, hab,
      ht, ne_eq, not_true_eq_false, false_and, false_or, true_and,
      Equiv.swap_apply_left, GridRectangle.mem_coveredSquares, hbE, hbD]
  -- At the replaced line, the old rectangle supplies the new lower part of the pentagon.
  by_cases hcb : c = finRotate n a
  · subst c
    have hsplit := Grid.ite_mem_cIco_eq_add_of_mem_cIoo hrow D.pentagon.turn_mem t
    simp only [GridPentagonBetween.mem_coveredSquares, hab.symm, Grid.right_notMem_cIco,
      ne_eq, not_false_eq_true, false_and, and_false, false_or, true_and, hb,
      Equiv.swap_apply_right, GridRectangle.mem_coveredSquares, haE, haD,
      GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, htop]
    simpa only [↓reduceIte, add_zero, zero_add, add_comm] using hsplit
  -- On ordinary columns, the corrected domains coincide with the generic repartition.
  · have h := hcount (c, t)
    simp only [Equiv.swap_apply_of_ne_of_ne hca hcb,
      (D.recutTerminal hcommon hcol hp hr).pentagon.mem_coveredSquares_iff_of_ne
        (p := (c, t)) hca hcb,
      D.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb]
    exact h

end TauCeti.GridPentagonRectangleDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- A counted terminal-side pentagon--rectangle source has a counted self-recut. Both emptiness
and marking avoidance are transported from the original composite domain. -/
theorem recutTerminal_mem_pentagonRectangleDecompositions
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty)
    (hD : D ∈ G.pentagonRectangleDecompositions C x z) :
    D.recutTerminal hcommon hcol hp hr ∈ G.pentagonRectangleDecompositions C x z := by
  classical
  let E := D.recutTerminal hcommon hcol hp hr
  let e := ((Equiv.swap C.column (finRotate n C.column)).prodCongr
    (Equiv.refl (Fin n))).toEmbedding
  obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C D).1 hD
  have hPX := ((G.mem_pentagons _).1 hP).2
  have hRX := (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).2
  have hmapX : Disjoint (D.rectangle.toGridRectangle.coveredSquares.map e) G.XSet := by
    rw [Finset.disjoint_left]
    intro p hp' hX
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp'
    apply Finset.disjoint_left.mp hRX hq
    simpa only [mem_XSet_swapColumns, e, Equiv.coe_toEmbedding, Equiv.prodCongr_apply,
      Prod.map_apply', Equiv.refl_apply] using hX
  have hunion := congrArg Multiset.toFinset
    (D.coveredSquares_val_add_recutTerminal hcommon hcol hp hr)
  simp only [Multiset.toFinset_add, Finset.val_toFinset] at hunion
  have hnew : Disjoint (E.pentagon.coveredSquares ∪
      E.rectangle.toGridRectangle.coveredSquares.map e) G.XSet := by
    rw [hunion]
    exact Finset.disjoint_union_left.mpr ⟨hPX, hmapX⟩
  obtain ⟨hEP, hER⟩ := Finset.disjoint_union_left.mp hnew
  have hrecut := D.isRecut_recutTerminal hcommon hcol hp hr
  refine (G.mem_pentagonRectangleDecompositions C _).2
    ⟨(G.mem_pentagons _).2 ⟨?_, hEP⟩,
      ((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).2 ⟨?_, ?_⟩⟩
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle]
      using hrecut.isEmpty_first
  · simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_middle,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle]
      using hrecut.isEmpty_second
  · rw [Finset.disjoint_left]
    intro q hq hX
    apply Finset.disjoint_left.mp hER (Finset.mem_map.mpr ⟨q, hq, rfl⟩)
    simpa only [mem_XSet_swapColumns, e, Equiv.coe_toEmbedding, Equiv.prodCongr_apply,
      Prod.map_apply', Equiv.refl_apply] using hX

/-- The terminal self-recut preserves the monomial contribution to the pentagon--rectangle
coefficient sum over any commutative semiring. -/
theorem pentagonRectangleWeight_recutTerminal
    (R : Type*) [CommSemiring R]
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    G.pentagonRectangleWeight C R (D.recutTerminal hcommon hcol hp hr) =
      G.pentagonRectangleWeight C R D :=
  G.pentagonRectangleWeight_eq_of_val_add_val_eq C R D _
    (D.coveredSquares_val_add_recutTerminal hcommon hcol hp hr)

end TauCeti.GridDiagram
