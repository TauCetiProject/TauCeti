/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Actions on the cells of a relative CW complex

A monoid action carrying each open cell onto an open cell of the same dimension induces an
action on the cells. Continuous translations also carry closed cells onto the corresponding
closed cells when the ambient space is Hausdorff. For a group action, trivial stabilizers of
open cells give a free action on cells.

## Main results

* `TauCeti.cellMulAction`: the induced monoid action on cells.
* `TauCeti.smul_openCell` and `TauCeti.smul_mem_openCell_smul`: compatibility with open cells.
* `TauCeti.smul_closedCell`: compatibility with closed cells for continuous translations.
* `TauCeti.isCancelSMul_cell`: freeness of the induced group action on cells.

## References

* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1 (free `G`-CW complexes).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Topology of Cell Complexes.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex
open scoped Pointwise

universe u

namespace TauCeti

variable {E : Type u} [TopologicalSpace E] {G : Type*}

section CellAction

variable {C D : Set E} [RelCWComplex C D] [Monoid G] [MulAction G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n),
    ∃ j : cell C n, g • openCell n i = openCell n j)

/-- The `n`-cell onto whose open cell `g` carries the open cell of `i`. -/
private def cellSMul {n : ℕ} (g : G) (i : cell C n) : cell C n :=
  (hcell g n i).choose

private theorem openCell_cellSMul {n : ℕ} (g : G) (i : cell C n) :
    openCell n (cellSMul hcell g i) = g • openCell n i :=
  (hcell g n i).choose_spec.symm

/-- If a monoid `G` acts on `E` and carries every open `n`-cell of the relative CW complex
`(C, D)` onto an open `n`-cell, this translation of open cells is an action of `G` on the
`n`-cells. It is the unique such action, since a cell is determined by its open cell
(`TauCeti.smul_openCell`). -/
@[implicit_reducible]
def cellMulAction (n : ℕ) : MulAction G (cell C n) where
  smul := cellSMul hcell
  one_smul i := openCell_congr n <| (openCell_cellSMul hcell 1 i).trans (one_smul G _)
  mul_smul g h i := by
    have : openCell n (cellSMul hcell (g * h) i) =
        openCell n (cellSMul hcell g (cellSMul hcell h i)) := by
      rw [openCell_cellSMul, openCell_cellSMul, openCell_cellSMul, mul_smul]
    exact openCell_congr n this

/-- **The action on cells translates open cells.** -/
theorem smul_openCell {n : ℕ} (g : G) (i : cell C n) :
    letI := cellMulAction hcell n
    g • openCell n i = openCell n (g • i) :=
  (openCell_cellSMul hcell g i).symm

/-- The translate by `g` of a point of the open cell of `i` lies in the open cell of `g • i`. -/
theorem smul_mem_openCell_smul {n : ℕ} (g : G) {i : cell C n} {y : E}
    (hy : y ∈ openCell n i) :
    letI := cellMulAction hcell n
    g • y ∈ openCell n (g • i) :=
  smul_openCell hcell g i ▸ smul_mem_smul_set hy

/-- The action on cells translates closed cells. -/
theorem smul_closedCell [T2Space E] [ContinuousConstSMul G E] {n : ℕ} (g : G)
    (i : cell C n) :
    letI := cellMulAction hcell n
    g • closedCell n i = closedCell n (g • i) := by
  have hcompact : IsCompact (closure (openCell n i)) := by
    rw [closure_openCell_eq_closedCell]
    exact isCompact_closedCell
  simpa only [image_smul, smul_openCell hcell, closure_openCell_eq_closedCell] using
    image_closure_of_isCompact hcompact (continuous_const_smul g).continuousOn

end CellAction

section FreeCellAction

variable {C D : Set E} [RelCWComplex C D] [Group G] [MulAction G E]
  (hcell : ∀ (g : G) (n : ℕ) (i : cell C n),
    ∃ j : cell C n, g • openCell n i = openCell n j)

/-- If `g` carries an open cell onto itself only when `g = 1`, then `G` acts freely on the
cells. -/
theorem isCancelSMul_cell
    (hfree : ∀ (g : G) (n : ℕ) (i : cell C n), g • openCell n i = openCell n i → g = 1)
    (n : ℕ) :
    letI := cellMulAction hcell n
    IsCancelSMul G (cell C n) := by
  let := cellMulAction hcell n
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun g i hi ↦ ?_
  exact hfree g n i (by rw [smul_openCell hcell, hi])

end FreeCellAction

end TauCeti
