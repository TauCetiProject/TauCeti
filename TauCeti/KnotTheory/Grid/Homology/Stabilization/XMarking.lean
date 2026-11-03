/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.NonTorsion
public import TauCeti.KnotTheory.Grid.Stabilization.Homology

/-!
# The stabilization map on the `X`-marking state

The `X`-marking state `G.X` of a grid diagram, whose point in each column is the lower-left corner
of the `X`-marked square, is the grid state `x⁻(G)` of Ozsváth--Szabó--Thurston, and its class
`XMarkingClass` in `GH⁻` is their class `λ⁻(G)`. This file shows that the chain map of the
`X`-stabilization `G' = G.stabilizeX s.castSucc (G.X s).castSucc s` carries `x⁻(G')` to `x⁻(G)`,
so that the induced isomorphism `GH⁻(G') ≅ GH⁻(G)` carries `λ⁻(G')` to `λ⁻(G)`. This is the
stabilization counterpart of `TauCeti.GridDiagram.unblockedHomologyCommutationMap_XMarkingClass`;
only this one stabilization type is treated, and nothing about Legendrian knots is formalised
here.

In `G'` the new `2 × 2` block is centered at `c = (s.succ, (G.X s).succ)`, with its two
`X`-markings northwest and southeast of `c` and its new `O`-marking southwest of `c`. The state
`x⁻(G')` does not contain `c`: its points in the block are the lower-left corners
`(s.castSucc, (G.X s).succ)` and `(s.succ, (G.X s).castSucc)` of the two `X`-marked squares. The
stabilization chain map applies to such an off-center state the component `H_I^N` of the
`X`-marking homotopy of the southeast marking `X₂`, which counts the empty rectangles into states
containing `c` whose only covered `X`-marking is `X₂`.

Every rectangle leaving the `X`-marking state covers the `X`-marking of its initial side column,
since its initial lower corner is the lower-left corner of that marking's square; so a rectangle
counted by the `X`-marking homotopy of column `k` from `G.X` has initial side `k`
(`left_eq_of_mem_XHomotopyRectangles_X`). From `x⁻(G')` the only such rectangle for `X₂` is the
rectangle of height one from column `s.succ` around the torus to column `s.castSucc`, in the row
`(G.X s).castSucc` of `X₂`. That row carries only `X₂` and the new `O`-marking, which lies in the
excluded column `s.castSucc`, so the rectangle has weight `1`. Its target is `x⁻(G)` with the
center `c` inserted (`XHomotopyCoefficient_stabilizeX_X_insertPoint`).

## Main results

* `TauCeti.GridDiagram.XHomotopyCoefficient_stabilizeX_X_insertPoint`: the matrix coefficients of
  `H_I^N` at `x⁻(G')`.
* `TauCeti.GridDiagram.stabilizeXChainMap_single_X`: the stabilization chain map sends `x⁻(G')`
  to `x⁻(G)`.
* `TauCeti.GridDiagram.stabilizeXHomologyMap_XMarkingClass`: the induced map on `GH⁻` sends
  `λ⁻(G')` to `λ⁻(G)`, and `TauCeti.GridDiagram.stabilizeXHomologyEquiv_symm_XMarkingClass`: its
  inverse sends `λ⁻(G)` to `λ⁻(G')`.

## References

* P. Ozsváth, Z. Szabó, D. Thurston, *Legendrian knots, transverse knots and combinatorial Floer
  homology*, Geom. Topol. 12 (2008), arXiv:math/0611841: the grid states `x⁺` and `x⁻`, their
  classes `λ⁺` and `λ⁻`, and their behaviour under stabilization.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 12: the same material in the conventions of the grid book,
  where the stabilization map is the one of Section 5.2.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ}

variable (G : GridDiagram n) (s : Fin n)

section Coefficient

variable (R : Type*) [CommSemiring R]

/-- **The component `H_I^N` at the `X`-marking state of a stabilization.** The `X`-marking homotopy
of the southeast `X`-marking of the new block has coefficient `1` from the `X`-marking state of
the stabilization to the `X`-marking state of `G` with the center `(s.succ, (G.X s).succ)` of the
block inserted, and coefficient `0` to every other state containing the center. -/
theorem XHomotopyCoefficient_stabilizeX_X_insertPoint (x : GridState n) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyCoefficient R s.succ
        (G.stabilizeX s.castSucc (G.X s).castSucc s).X (x.insertPoint s.succ (G.X s).succ) =
      if x = G.X then 1 else 0 := by
  set G' := G.stabilizeX s.castSucc (G.X s).castSucc s with hG'
  rw [XHomotopyCoefficient_def]
  split_ifs with hx
  · subst hx
    -- The one counted rectangle has height one: from column `s.succ` around the torus to column
    -- `s.castSucc`, in the row `(G.X s).castSucc` of the southeast `X`-marking.
    let r₀ : GridRectangleBetween G'.X (G.X.insertPoint s.succ (G.X s).succ) :=
      .ofSwapColumns _ _ s.succ s.castSucc Fin.castSucc_lt_succ.ne'
        (G.stabilizeX_X_swapColumns s).symm
    have hbottom : G'.X s.succ = (G.X s).castSucc := by
      rw [hG', stabilizeX_X, GridState.splitPoint_castSucc_apply_succ]
    have hrows : Grid.cIco (G'.X s.succ) (G'.X s.castSucc) = {(G.X s).castSucc} := by
      rw [hbottom, hG', stabilizeX_X_castSucc, Grid.cIco_of_ne Fin.castSucc_lt_succ.ne,
        Grid.cIoo_castSucc_succ, insert_empty_eq]
    have hcov (p : Fin (n + 1) × Fin (n + 1)) : p ∈ r₀.toGridRectangle.coveredSquares ↔
        p.1 ∈ Grid.cIco s.succ s.castSucc ∧ p.2 = (G.X s).castSucc := by
      rw [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
        GridRectangle.mem_coveredRows, GridRectangleBetween.ofSwapColumns_toGridRectangle, hrows,
        Finset.mem_singleton]
    have hr₀ : r₀ ∈ G'.XHomotopyRectangles s.succ G'.X (G.X.insertPoint s.succ (G.X s).succ) := by
      refine (G'.mem_XHomotopyRectangles s.succ r₀).mpr ⟨?_, ?_⟩
      · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo, GridRectangleBetween.bottom_def,
          GridRectangleBetween.top_def, GridRectangleBetween.ofSwapColumns_left,
          GridRectangleBetween.ofSwapColumns_right, hbottom, hG', stabilizeX_X_castSucc,
          Grid.cIoo_castSucc_succ]
        exact fun _ _ => Finset.notMem_empty _
      · -- The row of the southeast `X`-marking carries no other `X`-marking.
        ext p
        rw [Finset.mem_inter, hcov, G'.mem_XSet, Finset.mem_singleton, hbottom]
        constructor
        · rintro ⟨⟨-, h2⟩, hX⟩
          rw [h2, hG', stabilizeX_X, stabilizeX_X_eq_castSucc_iff] at hX
          exact Prod.ext hX h2
        · rintro rfl
          exact ⟨⟨Grid.left_mem_cIco Fin.castSucc_lt_succ.ne', rfl⟩, hbottom⟩
    rw [Finset.eq_singleton_iff_unique_mem.mpr ⟨hr₀, fun r hr =>
        GridRectangleBetween.left_injective ((G'.left_eq_of_mem_XHomotopyRectangles_X hr).trans
          (GridRectangleBetween.ofSwapColumns_left _ _ _ _ _ _).symm)⟩,
      Finset.sum_singleton]
    -- The row of the southeast `X`-marking carries its `O`-marking in the excluded column.
    refine G'.OMonomial_eq_one_of_disjoint R (Finset.disjoint_left.mpr fun p hp hO => ?_)
    obtain ⟨h1, h2⟩ := (hcov p).mp hp
    rw [G'.mem_OSet, h2, hG', stabilizeX_O, stabilizeX_O_eq_castSucc_iff] at hO
    exact Grid.right_notMem_cIco _ _ (hO ▸ h1)
  · refine Finset.sum_eq_zero fun r hr => absurd ?_ hx
    have hl := G'.left_eq_of_mem_XHomotopyRectangles_X hr
    -- The terminal side is the column `s.castSucc` where `G'.X` has the row of the center.
    have hright : r.right = s.castSucc := by
      refine G'.X.toPerm.injective ?_
      have h := r.map_left
      rw [hl, GridState.insertPoint_apply_newColumn] at h
      exact h.symm.trans (G.stabilizeX_X_castSucc s).symm
    have ht := r.target_eq_swapColumns
    rw [hl, hright, hG', stabilizeX_X_swapColumns] at ht
    exact GridState.insertPoint_injective _ _ ht

/-- **`H_I^N` sends the `X`-marking state of the stabilization to that of `G`.** -/
theorem stabilizeXOffCenterToCenter_single_X :
    G.stabilizeXOffCenterToCenter s R
        (Finsupp.single ⟨(G.stabilizeX s.castSucc (G.X s).castSucc s).X, G.stabilizeX_X_succ_ne s⟩
          1) =
      Finsupp.single G.X 1 := by
  refine Finsupp.ext fun x => ?_
  rw [stabilizeXOffCenterToCenter_single_apply, XHomotopyCoefficient_stabilizeX_X_insertPoint,
    Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

end Coefficient

/-! ### The stabilization map on the `X`-marking state -/

section Chain

variable (R : Type*) [CommRing R]

/-- **The stabilization chain map preserves the `X`-marking state.** The chain map
`GC⁻(G') → GC⁻(G)` of the stabilization `G' = G.stabilizeX s.castSucc (G.X s).castSucc s` sends
the `X`-marking state of `G'` to the `X`-marking state of `G`. -/
theorem stabilizeXChainMap_single_X :
    G.stabilizeXChainMap s R
        (Finsupp.single (G.stabilizeX s.castSucc (G.X s).castSucc s).X 1) =
      Finsupp.single G.X 1 := by
  rw [← G.stabilizeXOffCenterInclusion_single s R ⟨_, G.stabilizeX_X_succ_ne s⟩,
    stabilizeXChainMap_apply, stabilizeXOffCenterProjection_inclusion,
    stabilizeXOffCenterToCenter_single_X, Finsupp.mapRange_single, map_one]

end Chain

section Homology

variable (R : Type*) [CommRing R] [CharP R 2]

/-- **The stabilization map on `GH⁻` preserves the class of the `X`-marking state.** The map
`GH⁻(G') → GH⁻(G)` of the stabilization `G' = G.stabilizeX s.castSucc (G.X s).castSucc s` sends
the class of the `X`-marking state of `G'` to the class of the `X`-marking state of `G`. -/
@[simp]
theorem stabilizeXHomologyMap_XMarkingClass :
    G.stabilizeXHomologyMap s R ((G.stabilizeX s.castSucc (G.X s).castSucc s).XMarkingClass R) =
      G.XMarkingClass R := by
  rw [XMarkingClass_def, stabilizeXHomologyMap_unblockedHomologyClass, XMarkingClass_def]
  congr 1
  exact Subtype.ext (by simp only [coe_XMarkingCycle, G.stabilizeXChainMap_single_X s R])

/-- The inverse of the stabilization isomorphism `GH⁻(G') ≃ GH⁻(G)` sends the class of the
`X`-marking state of `G` to the class of the `X`-marking state of `G'`. -/
@[simp]
theorem stabilizeXHomologyEquiv_symm_XMarkingClass :
    (G.stabilizeXHomologyEquiv s R).symm (G.XMarkingClass R) =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).XMarkingClass R := by
  rw [LinearEquiv.symm_apply_eq, stabilizeXHomologyEquiv_apply,
    stabilizeXHomologyMap_XMarkingClass]

end Homology

end GridDiagram

end TauCeti
