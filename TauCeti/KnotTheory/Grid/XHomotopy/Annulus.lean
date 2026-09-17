/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.XHomotopy.Basic

/-!
# The diagonal of the `X`-marking anticommutator

This file computes the diagonal matrix entries of `∂⁻ ∘ H_k + H_k ∘ ∂⁻`, where `H_k` is the
`X`-marking homotopy of `TauCeti.KnotTheory.Grid.XHomotopy.Basic`.

A two-step decomposition from a grid state `x` back to `x` covers a full vertical or horizontal
band of the torus, and its two rectangles cover disjoint squares. The decomposition is counted
exactly when both rectangles are empty and the band carries a single `X`-marking, namely `X_k`. A
vertical band carries one `X`-marking in each column it covers, and a horizontal band one in
each row it covers, so it must be the column annulus of column `k` or the row annulus of the row
of `X_k`, each one square thick. On a
grid of size at least two, each thin annulus is cut by `x` into exactly one pair of rectangles,
both automatically empty. The column annulus covers the single `O`-marking of column `k`, and the
row annulus covers the `O`-marking in the row of `X_k`, so the diagonal entry is
`V_k + V_j`, where `O_j` is the `O`-marking in the row of `X_k`
(`sum_XHomotopyDecompositions_self`).

## Main results

* `TauCeti.GridDiagram.unblockedDecompositionWeight_eq_prod_union`: the weight of a returning
  pair of rectangles is a product over the band it covers.
* `TauCeti.GridDiagram.sum_XHomotopyDecompositions_self`: on a grid of size at least two, the
  diagonal entries of `∂⁻ ∘ H_k + H_k ∘ ∂⁻` are `V_k + V_j`.

## References

The annular terms follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridDiagram

open GridRectangleDecomposition GridRectangleBetween

variable {n : ℕ} (G : GridDiagram n)

/-- The weight of a returning pair of rectangles is the product, over the band of squares they
cover together, of the variable of the column of each `O`-marked square. -/
theorem unblockedDecompositionWeight_eq_prod_union (R : Type*) [CommSemiring R]
    {x : GridState n} (D : GridRectangleDecomposition x x) :
    G.unblockedDecompositionWeight R D =
      ∏ p ∈ D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares,
        if p ∈ G.OSet then MvPolynomial.X p.1 else (1 : MvPolynomial (Fin n) R) := by
  rw [unblockedDecompositionWeight_def, OMonomial_eq_prod_coveredSquares,
    OMonomial_eq_prod_coveredSquares,
    Finset.prod_union (D.first.disjoint_coveredSquares D.second)]

/-! ### The two thin annuli -/

section Annuli

variable (x : GridState n)

/-- The decomposition from `x` back to `x` whose two rectangles cover the column annulus of
column `k`. -/
private def columnAnnulus (k : Fin n) (hk : k ≠ finRotate n k) :
    GridRectangleDecomposition x x where
  middle := x.swapColumns k (finRotate n k)
  first := ofSwapColumns x _ k (finRotate n k) hk rfl
  second := ofSwapColumns _ x k (finRotate n k) hk (GridState.swapColumns_swapColumns _ _ _).symm

/-- The decomposition from `x` back to `x` whose two rectangles cover the row annulus of row
`r`. -/
private def rowAnnulus (r : Fin n) (hr : r ≠ finRotate n r) :
    GridRectangleDecomposition x x where
  middle := x.swapColumns (x.columnOfRow r) (x.columnOfRow (finRotate n r))
  first := ofSwapColumns x _ (x.columnOfRow r) (x.columnOfRow (finRotate n r))
    (x.columnOfRow_injective.ne hr) rfl
  second := ofSwapColumns _ x (x.columnOfRow (finRotate n r)) (x.columnOfRow r)
    (x.columnOfRow_injective.ne hr).symm
    (by rw [GridState.swapColumns_comm, GridState.swapColumns_swapColumns])

private theorem columnAnnulus_coveredSquares (k : Fin n) (hk : k ≠ finRotate n k) :
    (columnAnnulus x k hk).first.toGridRectangle.coveredSquares ∪
        (columnAnnulus x k hk).second.toGridRectangle.coveredSquares =
      {k} ×ˢ Finset.univ := by
  rw [coveredSquares_union_coveredSquares_of_left_eq_left _ _
    (by simp only [columnAnnulus, ofSwapColumns_left]), GridRectangle.coveredColumns_def,
    toGridRectangle_left, toGridRectangle_right]
  simp only [columnAnnulus, ofSwapColumns_left, ofSwapColumns_right]
  rw [Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, hk⟩]

private theorem rowAnnulus_coveredSquares (r : Fin n) (hr : r ≠ finRotate n r) :
    (rowAnnulus x r hr).first.toGridRectangle.coveredSquares ∪
        (rowAnnulus x r hr).second.toGridRectangle.coveredSquares =
      Finset.univ ×ˢ {r} := by
  rw [coveredSquares_union_coveredSquares_of_left_eq_right _ _
    (by simp only [rowAnnulus, ofSwapColumns_left, ofSwapColumns_right]),
    GridRectangle.coveredRows_def, toGridRectangle_bottom, toGridRectangle_top]
  simp only [rowAnnulus, ofSwapColumns_bottom, ofSwapColumns_top, GridState.apply_columnOfRow]
  rw [Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, hr⟩]

private theorem columnAnnulus_isEmpty (k : Fin n) (hk : k ≠ finRotate n k) :
    (columnAnnulus x k hk).first.IsEmpty ∧ (columnAnnulus x k hk).second.IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo, isEmpty_iff_forall_notMem_cIoo]
  simp only [columnAnnulus, ofSwapColumns_left, ofSwapColumns_right,
    Grid.cIoo_finRotate_eq_empty]
  exact ⟨fun c hc => absurd hc (Finset.notMem_empty c),
    fun c hc => absurd hc (Finset.notMem_empty c)⟩

private theorem rowAnnulus_isEmpty (r : Fin n) (hr : r ≠ finRotate n r) :
    (rowAnnulus x r hr).first.IsEmpty ∧ (rowAnnulus x r hr).second.IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo, isEmpty_iff_forall_notMem_cIoo]
  simp only [rowAnnulus, ofSwapColumns_bottom, ofSwapColumns_top, GridState.swapColumns_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right, GridState.apply_columnOfRow,
    Grid.cIoo_finRotate_eq_empty]
  exact ⟨fun _ _ hc => Finset.notMem_empty _ hc, fun _ _ hc => Finset.notMem_empty _ hc⟩

private theorem columnAnnulus_ne_rowAnnulus (k : Fin n) (hk : k ≠ finRotate n k) (r : Fin n)
    (hr : r ≠ finRotate n r) : columnAnnulus x k hk ≠ rowAnnulus x r hr := by
  intro h
  have h₁ := congrArg (fun D : GridRectangleDecomposition x x => D.first.left) h
  have h₂ := congrArg (fun D : GridRectangleDecomposition x x => D.second.left) h
  simp only [columnAnnulus, rowAnnulus, ofSwapColumns_left] at h₁ h₂
  exact x.columnOfRow_injective.ne hr (h₁.symm.trans h₂)

end Annuli

/-! ### The diagonal entries -/

/-- The covered `X`-markings of a column band are the markings of its columns. -/
private theorem product_univ_inter_XSet_eq_singleton_iff (k : Fin n) (s : Finset (Fin n)) :
    s ×ˢ Finset.univ ∩ G.XSet = {(k, G.X k)} ↔ s = {k} := by
  constructor
  · intro h
    ext c
    have hc := congrArg (fun t => (c, G.X c) ∈ t) h
    simpa using hc
  · rintro rfl
    ext p
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
      and_true, mem_XSet]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact Prod.ext h₁ (h₁ ▸ h₂.symm)
    · rintro rfl
      exact ⟨rfl, rfl⟩

/-- The covered `X`-markings of a row band are the markings of its rows. -/
private theorem univ_product_inter_XSet_eq_singleton_iff (k : Fin n) (s : Finset (Fin n)) :
    Finset.univ ×ˢ s ∩ G.XSet = {(k, G.X k)} ↔ s = {G.X k} := by
  constructor
  · intro h
    ext r
    have hr := congrArg (fun t => (G.X.columnOfRow r, r) ∈ t) h
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_univ, true_and, mem_XSet,
      GridState.apply_columnOfRow, and_true, Finset.mem_singleton, Prod.mk.injEq] at hr
    rw [hr, Finset.mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩
      rfl
    · rintro rfl
      exact ⟨G.X.columnOfRow_apply k, rfl⟩
  · rintro rfl
    ext p
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_singleton, mem_XSet]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact Prod.ext (G.X.toPerm.injective (h₂.trans h₁)) h₁
    · rintro rfl
      exact ⟨rfl, rfl⟩

/-- On a grid of size at least two, the decompositions from `x` back to `x` counted by
`∂⁻ ∘ H_k + H_k ∘ ∂⁻` are exactly the two thin annuli through `X_k`. -/
private theorem XHomotopyDecompositions_self (hn : 1 < n) (k : Fin n) (x : GridState n) :
    G.XHomotopyDecompositions k x x =
      {columnAnnulus x k (Grid.finRotate_ne_self hn k).symm,
        rowAnnulus x (G.X k) (Grid.finRotate_ne_self hn (G.X k)).symm} := by
  ext D
  rw [G.mem_XHomotopyDecompositions_iff_of_disjoint k D
    (D.first.disjoint_coveredSquares D.second), Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, -, hX⟩
    rcases D.first.left_eq_left_or_left_eq_right D.second with h | h
    · -- a column band: it is the column annulus of column `k`
      rw [coveredSquares_union_coveredSquares_of_left_eq_left _ _ h,
        product_univ_inter_XSet_eq_singleton_iff, GridRectangle.coveredColumns_def,
        toGridRectangle_left, toGridRectangle_right, Grid.cIco_eq_singleton_iff] at hX
      obtain ⟨hl, hr, -⟩ := hX
      left
      refine GridRectangleDecomposition.ext ?_ ?_ ?_ ?_ <;>
        simp only [columnAnnulus, ofSwapColumns_left, ofSwapColumns_right]
      · exact hl
      · exact hr
      · rw [h]
        exact hl
      · rw [D.first.right_eq_right_of_left_eq_left D.second h]
        exact hr
    · -- a row band: it is the row annulus of the row of `X_k`
      rw [coveredSquares_union_coveredSquares_of_left_eq_right _ _ h,
        univ_product_inter_XSet_eq_singleton_iff, GridRectangle.coveredRows_def,
        Grid.cIco_eq_singleton_iff] at hX
      obtain ⟨hb, ht, -⟩ := hX
      rw [toGridRectangle_bottom, bottom_def] at hb
      rw [toGridRectangle_top, top_def] at ht
      have hl : D.first.left = x.columnOfRow (G.X k) := by
        rw [← hb, GridState.columnOfRow_apply]
      have hr : D.first.right = x.columnOfRow (finRotate n (G.X k)) := by
        rw [← ht, GridState.columnOfRow_apply]
      right
      refine GridRectangleDecomposition.ext ?_ ?_ ?_ ?_ <;>
        simp only [rowAnnulus, ofSwapColumns_left, ofSwapColumns_right]
      · exact hl
      · exact hr
      · rw [h]
        exact hr
      · rw [D.first.right_eq_left_of_left_eq_right D.second h]
        exact hl
  · rintro (rfl | rfl)
    · refine ⟨(columnAnnulus_isEmpty x k _).1, (columnAnnulus_isEmpty x k _).2, ?_⟩
      rw [columnAnnulus_coveredSquares, product_univ_inter_XSet_eq_singleton_iff]
    · refine ⟨(rowAnnulus_isEmpty x _ _).1, (rowAnnulus_isEmpty x _ _).2, ?_⟩
      rw [rowAnnulus_coveredSquares, univ_product_inter_XSet_eq_singleton_iff]

/-- On a grid of size at least two, the diagonal matrix entries of `∂⁻ ∘ H_k + H_k ∘ ∂⁻` are
`V_k + V_j`, where `O_j` is the `O`-marking in the row of `X_k`: the column annulus through
`X_k` covers `O_k` and the row annulus through `X_k` covers `O_j`. -/
theorem sum_XHomotopyDecompositions_self (R : Type*) [CommSemiring R] (hn : 1 < n) (k : Fin n)
    (x : GridState n) :
    ∑ D ∈ G.XHomotopyDecompositions k x x, G.unblockedDecompositionWeight R D =
      MvPolynomial.X k + MvPolynomial.X (G.O.columnOfRow (G.X k)) := by
  rw [G.XHomotopyDecompositions_self hn k x,
    Finset.sum_pair (columnAnnulus_ne_rowAnnulus x _ _ _ _),
    unblockedDecompositionWeight_eq_prod_union, unblockedDecompositionWeight_eq_prod_union,
    columnAnnulus_coveredSquares, rowAnnulus_coveredSquares, Finset.prod_product,
    Finset.prod_product]
  simp only [Finset.prod_singleton]
  congr 1
  · rw [Finset.prod_eq_single (G.O k) (fun r _ hr => by simp [mem_OSet, Ne.symm hr])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp [mem_OSet]
  · rw [Finset.prod_eq_single (G.O.columnOfRow (G.X k))
      (fun c _ hc => by
        simp only [mem_OSet, ite_eq_right_iff]
        intro h
        exact absurd (by rw [← h, GridState.columnOfRow_apply]) hc)
      (fun h => absurd (Finset.mem_univ _) h)]
    simp [mem_OSet]

end GridDiagram

end TauCeti
