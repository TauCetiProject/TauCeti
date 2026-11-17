/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing
import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Geometry
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Basic

/-!
# Uniqueness of two-step empty rectangle decompositions of a domain

For the juxtaposition proof of `∂² = 0` over `𝔽₂`, it suffices to construct a fixed-point-free
involution on two-step decompositions: commuting the two rectangles in the disjoint-side case
(`GridRectangleDecomposition.commute`) and recutting the L-shaped hexagon in the one-common-side
case (`GridRectangleDecomposition.recut`). Over `ℤ`, however, the square rule of a
`GridSignAssignment` quantifies over *every* pair of distinct two-step empty decompositions covering
the same domain (as a multiset of squares). Verifying that a constructed sign assignment satisfies
the square rule therefore requires knowing that no third decomposition of the same domain exists,
and that an annular domain admits no distinct second decomposition at all.

This file establishes that uniqueness: whenever two distinct two-step empty decompositions `D` and
`E` from `x` to `z` cover the same multiset of squares,

* `z ≠ x` (an annular domain uniquely determines its two rectangles),
* if `D` has disjoint side columns then `E = D.commute h`, and
* if `D` shares one side column then `E = D.recut hone hD₁ hD₂`.

## Main results

* `TauCeti.GridRectangleDecomposition.hasSameSideOverlap_recut_iff`: recutting swaps same-side and
  mixed-side overlaps.
* `TauCeti.GridRectangleDecomposition.target_ne_source_of_val_add_val_eq_of_ne`: two distinct
  decompositions covering the same multiset of squares cannot return to the source state.
* `TauCeti.GridRectangleDecomposition.eq_commute_of_val_add_val_eq_of_ne`: in the disjoint-side
  case, commuting is the unique other empty decomposition with the same covered-square multiset.
* `TauCeti.GridRectangleDecomposition.eq_recut_of_val_add_val_eq_of_ne`: in the one-common-side
  case, recutting is the unique other empty decomposition with the same covered-square multiset.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapters 4.6 and 15.2.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-! ### Helper lemmas on cyclic intervals, side columns, and multisets of squares -/

/-- A nondegenerate half-open cyclic interval uniquely determines both of its endpoints. -/
private theorem endpoints_eq_of_cIco_eq {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (h : Grid.cIco a b = Grid.cIco c d) : a = c ∧ b = d := by
  cases n with
  | zero => exact a.elim0
  | succ m =>
    have hac : a = c := by
      let p := (finRotate (m + 1))⁻¹ a
      have hp : finRotate (m + 1) p = a := Equiv.apply_symm_apply _ a
      have hpa : p ∉ Grid.cIco a b := by
        rw [← hp, finRotate_apply]
        exact Grid.notMem_cIco_finRotate_left p b
      have hmem : finRotate (m + 1) p ∈ Grid.cIco c d := by
        rw [hp, ← h]
        exact Grid.left_mem_cIco hab
      have hnot : p ∉ Grid.cIco c d := h ▸ hpa
      have hcd_eq : c = a ∨ d = a := by
        by_contra hne
        push Not at hne
        rw [← hp] at hne
        exact hnot ((Grid.mem_cIco_finRotate_iff_of_ne hne.1 hne.2).mp hmem)
      rcases hcd_eq with hca | hda
      · exact hca.symm
      · rw [hp, ← hda] at hmem
        exact absurd hmem (Grid.right_notMem_cIco c d)
    have hbd : b = d := by
      let q := (finRotate (m + 1))⁻¹ b
      have hq : finRotate (m + 1) q = b := Equiv.apply_symm_apply _ b
      have hmem : q ∈ Grid.cIco c d := by
        rw [← h, ← hq]
        exact Grid.self_mem_cIco_finRotate (by rw [hq]; exact hab)
      have hnot : finRotate (m + 1) q ∉ Grid.cIco c d := by
        rw [hq, ← h]
        exact Grid.right_notMem_cIco a b
      have hcd_eq : c = b ∨ d = b := by
        by_contra hne
        push Not at hne
        rw [← hq] at hne
        exact hnot ((Grid.mem_cIco_finRotate_iff_of_ne hne.1 hne.2).mpr hmem)
      rcases hcd_eq with hcb | hdb
      · rw [hq, ← hcb] at hnot
        exact absurd (Grid.left_mem_cIco hcd) hnot
      · exact hdb.symm
    exact ⟨hac, hbd⟩

/-- If two finite sets are disjoint and another pair of finite sets has the same multiset sum, then
the second pair is also disjoint and has the same union. -/
private theorem disjoint_and_union_eq_of_val_add_val_eq {α : Type*} [DecidableEq α]
    {A₁ A₂ B₁ B₂ : Finset α} (hA : Disjoint A₁ A₂) (hval : B₁.val + B₂.val = A₁.val + A₂.val) :
    Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = A₁ ∪ A₂ := by
  have hAnodup : (A₁.val + A₂.val).Nodup :=
    Multiset.nodup_add.mpr ⟨A₁.nodup, A₂.nodup, Finset.disjoint_val.mpr hA⟩
  refine ⟨Finset.disjoint_val.mp (Multiset.nodup_add.mp (hval ▸ hAnodup)).2.2, ?_⟩
  ext p
  have hmem : p ∈ B₁.val + B₂.val ↔ p ∈ A₁.val + A₂.val := hval ▸ Iff.rfl
  simpa only [Finset.mem_union, Multiset.mem_add, Finset.mem_val] using hmem

/-- An empty rectangle does not cover the source state's point in any column outside its side
columns. -/
private theorem notMem_coveredSquares_of_isEmpty_of_notMem_sideColumns
    {x y : GridState n} {r : GridRectangleBetween x y} (hr : r.IsEmpty) {c : Fin n}
    (hc : c ∉ r.sideColumns) : (c, x c) ∉ r.toGridRectangle.coveredSquares := by
  intro hmem
  rw [GridRectangleBetween.mem_sideColumns, not_or] at hc
  rw [r.mem_toGridRectangle_coveredSquares] at hmem
  have hc_oo : c ∈ Grid.cIoo r.left r.right := Grid.mem_cIoo_of_mem_cIco hmem.1 hc.1
  have hr_ne : x c ≠ r.bottom := fun heq => hc.1 (x.toPerm.injective (heq.trans r.bottom_def))
  have hr_oo : x c ∈ Grid.cIoo r.bottom r.top := Grid.mem_cIoo_of_mem_cIco hmem.2 hr_ne
  exact (r.isEmpty_iff_forall_notMem_cIoo.mp hr c hc_oo) hr_oo

/-- Disjointness of side-column sets extracted from `HasDisjointSides`. -/
private theorem disjoint_sideColumns_of_hasDisjointSides {D : GridRectangleDecomposition x z}
    (hD : D.HasDisjointSides) : Disjoint D.first.sideColumns D.second.sideColumns := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp hD
  simp only [GridRectangleBetween.sideColumns, Finset.disjoint_insert_left,
    Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨⟨hll, hlr⟩, hrl, hrr⟩

/-- Rebuilding `HasDisjointSides` from disjointness of side-column sets. -/
private theorem hasDisjointSides_of_disjoint_sideColumns {D : GridRectangleDecomposition x z}
    (h : Disjoint D.first.sideColumns D.second.sideColumns) : D.HasDisjointSides := by
  rw [D.hasDisjointSides_iff]
  simp only [GridRectangleBetween.sideColumns, Finset.disjoint_insert_left,
    Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

/-! ### Overlap orientation under recutting -/

/-- Recutting exchanges same-side overlaps and mixed-side overlaps. -/
theorem hasSameSideOverlap_recut_iff (D : GridRectangleDecomposition x z)
    (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    (D.recut hone hfirst hsecond).HasSameSideOverlap ↔ D.HasMixedSideOverlap := by
  have hone' := D.hasOneCommonSide_recut hone hfirst hsecond
  constructor
  · intro hsame'
    rcases D.hasSameSideOverlap_or_hasMixedSideOverlap hone with hsame | hmixed
    · exfalso
      apply (D.recut hone hfirst hsecond).not_hasMixedSideOverlap_of_hasSameSideOverlap hsame'
      rw [GridRectangleDecomposition.hasMixedSideOverlap_iff]
      rcases (D.hasSameSideOverlap_iff.mp hsame).2 with hleft | hright
      · have hdata := D.isRecutOfLeftEqLeft_recut hleft hone hfirst hsecond
        obtain ⟨hE₁, hE₂⟩ := hdata.recut_sides
        rcases hdata.recut_branch with ⟨-, -, hEl₁, -⟩ | ⟨-, -, -, hEl₂⟩
        · exact ⟨hone', Or.inl (hEl₁.trans hE₂.symm)⟩
        · exact ⟨hone', Or.inr (hE₁.trans hEl₂.symm)⟩
      · have hdata := D.isRecutOfRightEqRight_recut hright hone hfirst hsecond
        obtain ⟨hE₁, hE₂⟩ := hdata.recut_sides
        rcases hdata.recut_branch with ⟨-, -, hEr₁, -⟩ | ⟨-, -, -, hEr₂⟩
        · exact ⟨hone', Or.inr (hEr₁.trans hE₂.symm)⟩
        · exact ⟨hone', Or.inl (hE₁.trans hEr₂.symm)⟩
    · exact hmixed
  · intro hmixed
    rw [GridRectangleDecomposition.hasSameSideOverlap_iff]
    rcases (D.hasMixedSideOverlap_iff.mp hmixed).2 with hlr | hrl
    · rcases D.recut_geometry_of_left_eq_right hlr hone hfirst hsecond with
          ⟨-, hEl₁, -, hEl₂, -, -⟩ | ⟨-, -, hEr₁, -, hEr₂, -⟩
      · exact ⟨hone', Or.inl (hEl₁.trans hEl₂.symm)⟩
      · exact ⟨hone', Or.inr (hEr₁.trans hEr₂.symm)⟩
    · rcases D.recut_geometry_of_right_eq_left hrl hone hfirst hsecond with
          ⟨-, -, hEr₁, -, hEr₂, -⟩ | ⟨-, hEl₁, -, hEl₂, -, -⟩
      · exact ⟨hone', Or.inr (hEr₁.trans hEr₂.symm)⟩
      · exact ⟨hone', Or.inl (hEl₁.trans hEl₂.symm)⟩

/-! ### Annular domains -/

/-- Two distinct two-step decompositions covering the same multiset of squares cannot return to
their source state: an annular domain uniquely determines its two rectangles. -/
theorem target_ne_source_of_val_add_val_eq_of_ne {D E : GridRectangleDecomposition x z}
    (hne : E ≠ D)
    (hdom : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val) :
    z ≠ x := by
  rintro rfl
  have hunion :
      E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares =
        D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares :=
    (disjoint_and_union_eq_of_val_add_val_eq
      (D.first.disjoint_coveredSquares D.second) hdom).2
  rcases D.first.left_right_eq_cases D.second with ⟨hDl, hDr⟩ | ⟨hDl, hDr⟩ <;>
    rcases E.first.left_right_eq_cases E.second with ⟨hEl, hEr⟩ | ⟨hEl, hEr⟩
  · -- Both vertical bands.
    rw [D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hDl,
      E.first.coveredSquares_union_coveredSquares_of_left_eq_left E.second hEl] at hunion
    have hcols : Grid.cIco E.first.left E.first.right = Grid.cIco D.first.left D.first.right := by
      ext c
      have hmem := eq_iff_iff.mp (congrArg (fun S => (c, D.first.bottom) ∈ S) hunion)
      simpa only [Finset.mem_product, Finset.mem_univ, and_true,
        GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right] using hmem
    obtain ⟨hl, hr⟩ := endpoints_eq_of_cIco_eq E.first.left_ne_right D.first.left_ne_right hcols
    exact hne (GridRectangleDecomposition.ext hl hr (hEl.trans (hl.trans hDl.symm)))
  · -- `D` vertical, `E` horizontal: `(D.first.right, E.first.bottom)` separates them.
    rw [D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hDl,
      E.first.coveredSquares_union_coveredSquares_of_left_eq_right E.second hEl] at hunion
    have hmem : (D.first.right, E.first.bottom) ∈
        (Finset.univ : Finset (Fin n)) ×ˢ E.first.toGridRectangle.coveredRows := by
      simp only [Finset.mem_product, Finset.mem_univ, true_and, GridRectangle.mem_coveredRows,
        GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top]
      exact Grid.left_mem_cIco E.first.bottom_ne_top
    rw [hunion] at hmem
    simp only [Finset.mem_product, Finset.mem_univ, and_true, GridRectangle.mem_coveredColumns,
      GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right] at hmem
    exact Grid.right_notMem_cIco _ _ hmem
  · -- `D` horizontal, `E` vertical: `(E.first.right, D.first.bottom)` separates them.
    rw [D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hDl,
      E.first.coveredSquares_union_coveredSquares_of_left_eq_left E.second hEl] at hunion
    have hmem : (E.first.right, D.first.bottom) ∈
        (Finset.univ : Finset (Fin n)) ×ˢ D.first.toGridRectangle.coveredRows := by
      simp only [Finset.mem_product, Finset.mem_univ, true_and, GridRectangle.mem_coveredRows,
        GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top]
      exact Grid.left_mem_cIco D.first.bottom_ne_top
    rw [← hunion] at hmem
    simp only [Finset.mem_product, Finset.mem_univ, and_true, GridRectangle.mem_coveredColumns,
      GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right] at hmem
    exact Grid.right_notMem_cIco _ _ hmem
  · -- Both horizontal bands.
    rw [D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hDl,
      E.first.coveredSquares_union_coveredSquares_of_left_eq_right E.second hEl] at hunion
    have hrows : Grid.cIco E.first.bottom E.first.top = Grid.cIco D.first.bottom D.first.top := by
      ext r
      have hmem := eq_iff_iff.mp (congrArg (fun S => (D.first.left, r) ∈ S) hunion)
      simpa only [Finset.mem_product, Finset.mem_univ, true_and,
        GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
        GridRectangleBetween.toGridRectangle_top] using hmem
    obtain ⟨hb, ht⟩ := endpoints_eq_of_cIco_eq E.first.bottom_ne_top D.first.bottom_ne_top hrows
    have hl : E.first.left = D.first.left :=
      z.toPerm.injective (E.first.bottom_def.symm.trans (hb.trans D.first.bottom_def))
    have hr : E.first.right = D.first.right :=
      z.toPerm.injective (E.first.top_def.symm.trans (ht.trans D.first.top_def))
    exact hne (GridRectangleDecomposition.ext hl hr (hEl.trans (hr.trans hDl.symm)))

/-! ### Disjoint-side decompositions -/

/-- Two empty disjoint-side decompositions with the same ordered pair of side-column sets and the
same covered-square multiset are equal. -/
private theorem eq_of_hasDisjointSides_of_sideColumns_eq {D E : GridRectangleDecomposition x z}
    (hD : D.HasDisjointSides) (hE₁ : E.first.IsEmpty)
    (hs₁ : E.first.sideColumns = D.first.sideColumns)
    (hs₂ : E.second.sideColumns = D.second.sideColumns)
    (hdom : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val) :
    E = D := by
  have hdisj := disjoint_sideColumns_of_hasDisjointSides hD
  have hnot_mem : D.second.left ∉ E.first.sideColumns := by
    rw [hs₁]
    exact Finset.disjoint_right.mp hdisj (by simp)
  have hD₂bot : D.second.bottom = x D.second.left := by
    rw [GridRectangleBetween.bottom_def]
    have hnot₁ : D.second.left ∉ D.first.sideColumns := hs₁ ▸ hnot_mem
    rw [GridRectangleBetween.mem_sideColumns, not_or] at hnot₁
    exact D.first.map_of_ne D.second.left hnot₁.1 hnot₁.2
  have hp₂_mem : (D.second.left, x D.second.left) ∈
      E.first.toGridRectangle.coveredSquares.val + E.second.toGridRectangle.coveredSquares.val := by
    rw [hdom, Multiset.mem_add]
    exact Or.inr (hD₂bot ▸ D.second.left_bottom_mem_coveredSquares)
  have hp₂_not₁ : (D.second.left, x D.second.left) ∉ E.first.toGridRectangle.coveredSquares :=
    notMem_coveredSquares_of_isEmpty_of_notMem_sideColumns hE₁ hnot_mem
  have hp₂_in₂ : (D.second.left, x D.second.left) ∈ E.second.toGridRectangle.coveredSquares := by
    rcases Multiset.mem_add.mp hp₂_mem with h₁ | h₂
    · exact absurd h₁ hp₂_not₁
    · exact h₂
  have hE₂_lmem : D.second.left ∈ E.second.sideColumns := by
    rw [hs₂]; simp
  have hE₂_rmem : D.second.right ∈ E.second.sideColumns := by
    rw [hs₂]; simp
  rw [GridRectangleBetween.mem_sideColumns] at hE₂_lmem hE₂_rmem
  have hl₂ : E.second.left = D.second.left := by
    rcases hE₂_lmem with hl | hr
    · exact hl.symm
    · exfalso
      have hc := (E.second.mem_toGridRectangle_coveredSquares.mp hp₂_in₂).1
      rw [hr] at hc
      exact Grid.right_notMem_cIco _ _ hc
  have hr₂ : E.second.right = D.second.right := by
    rcases hE₂_rmem with hl | hr
    · exact absurd (hl₂.symm.trans hl.symm) D.second.left_ne_right
    · exact hr.symm
  have hmid : E.middle = D.middle := by
    have hEl : E.first.left ∈ D.first.sideColumns := hs₁ ▸ by simp
    have hEr : E.first.right ∈ D.first.sideColumns := hs₁ ▸ by simp
    rw [GridRectangleBetween.mem_sideColumns] at hEl hEr
    have hEm := E.first.target_eq_swapColumns
    have hDm := D.first.target_eq_swapColumns
    rcases hEl with h₁ | h₁ <;> rcases hEr with h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
    · exact hEm.trans (by rw [h₁, h₂]; exact hDm.symm)
    · exact hEm.trans (by rw [h₁, h₂, GridState.swapColumns_comm]; exact hDm.symm)
    · exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
  have hcov₂ : E.second.toGridRectangle.coveredSquares =
      D.second.toGridRectangle.coveredSquares := by
    simp only [GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def,
      GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.bottom_def,
      GridRectangleBetween.top_def, hl₂, hr₂, hmid]
  rw [hcov₂] at hdom
  have hcov₁_val : E.first.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val := add_right_cancel hdom
  have hp₁_in₁ : (D.first.left, D.first.bottom) ∈ E.first.toGridRectangle.coveredSquares := by
    change (D.first.left, D.first.bottom) ∈ E.first.toGridRectangle.coveredSquares.val
    rw [hcov₁_val]
    exact D.first.left_bottom_mem_coveredSquares
  have hE₁_lmem : D.first.left ∈ E.first.sideColumns := hs₁ ▸ by simp
  have hE₁_rmem : D.first.right ∈ E.first.sideColumns := hs₁ ▸ by simp
  rw [GridRectangleBetween.mem_sideColumns] at hE₁_lmem hE₁_rmem
  have hl₁ : E.first.left = D.first.left := by
    rcases hE₁_lmem with hl | hr
    · exact hl.symm
    · exfalso
      have hc := (E.first.mem_toGridRectangle_coveredSquares.mp hp₁_in₁).1
      rw [hr] at hc
      exact Grid.right_notMem_cIco _ _ hc
  have hr₁ : E.first.right = D.first.right := by
    rcases hE₁_rmem with hl | hr
    · exact absurd (hl₁.symm.trans hl.symm) D.first.left_ne_right
    · exact hr.symm
  exact GridRectangleDecomposition.ext hl₁ hr₁ hl₂

/-- In the disjoint-side case, the two unordered side-column pairs of any other decomposition with
the same endpoints must agree with those of `D` in either the same or the reversed order. -/
private theorem sideColumns_eq_or_swap_of_hasDisjointSides {D E : GridRectangleDecomposition x z}
    (hD : D.HasDisjointSides) :
    (E.first.sideColumns = D.first.sideColumns ∧ E.second.sideColumns = D.second.sideColumns) ∨
      (E.first.sideColumns = D.second.sideColumns ∧
        E.second.sideColumns = D.first.sideColumns) := by
  have hzD : z = (x.swapColumns D.first.left D.first.right).swapColumns D.second.left
      D.second.right :=
    D.second.target_eq_swapColumns.trans
      (congrArg (·.swapColumns D.second.left D.second.right) D.first.target_eq_swapColumns)
  have hDdisj := D.hasDisjointSides_iff.mp hD
  have hE : E.HasDisjointSides := by
    have hdisj_pair : Disjoint ({D.first.left, D.first.right} : Finset (Fin n))
        {D.second.left, D.second.right} := disjoint_sideColumns_of_hasDisjointSides hD
    have key : ∀ (z' : GridState n) (E' : GridRectangleDecomposition x z'),
        z' = (x.swapColumns D.first.left D.first.right).swapColumns D.second.left
          D.second.right → E'.HasDisjointSides := by
      rintro z' E' rfl
      exact hasDisjointSides_of_disjoint x D.first.left_ne_right D.second.left_ne_right
        hdisj_pair E'
    exact key z E hzD
  -- Both `D` and `E` factor the same permutation `x⁻¹ * z` into two disjoint transpositions.
  have hperm : Equiv.swap E.first.left E.first.right * Equiv.swap E.second.left E.second.right =
      Equiv.swap D.first.left D.first.right * Equiv.swap D.second.left D.second.right := by
    have hD_toPerm : z.toPerm = x.toPerm *
        (Equiv.swap D.first.left D.first.right * Equiv.swap D.second.left D.second.right) := by
      have h1 := congrArg GridState.toPerm D.second.target_eq_swapColumns
      have h2 := congrArg GridState.toPerm D.first.target_eq_swapColumns
      rw [GridState.swapColumns_toPerm] at h1 h2
      rw [h1, h2, mul_assoc]
    have hE_toPerm : z.toPerm = x.toPerm *
        (Equiv.swap E.first.left E.first.right * Equiv.swap E.second.left E.second.right) := by
      have h1 := congrArg GridState.toPerm E.second.target_eq_swapColumns
      have h2 := congrArg GridState.toPerm E.first.target_eq_swapColumns
      rw [GridState.swapColumns_toPerm] at h1 h2
      rw [h1, h2, mul_assoc]
    exact mul_left_cancel (hE_toPerm.symm.trans hD_toPerm)
  have hEdisj := E.hasDisjointSides_iff.mp hE
  -- Evaluate both sides of `hperm` at `E.first.left` and `E.second.left`.
  have hpair : ∀ {a b : Fin n},
      (Equiv.swap D.first.left D.first.right * Equiv.swap D.second.left D.second.right) a = b →
      a ≠ b → ({a, b} : Finset (Fin n)) = D.first.sideColumns ∨
        ({a, b} : Finset (Fin n)) = D.second.sideColumns := by
    intro a b hab hne
    by_cases ha₁ : a = D.first.left
    · subst ha₁
      have hb : b = D.first.right := by
        rw [← hab, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hDdisj.1 hDdisj.2.1, Equiv.swap_apply_left]
      exact Or.inl (by simp [hb, GridRectangleBetween.sideColumns])
    · by_cases ha₂ : a = D.first.right
      · subst ha₂
        have hb : b = D.first.left := by
          rw [← hab, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne hDdisj.2.2.1 hDdisj.2.2.2, Equiv.swap_apply_right]
        exact Or.inl (by simp [hb, GridRectangleBetween.sideColumns, Finset.pair_comm])
      · by_cases ha₃ : a = D.second.left
        · subst ha₃
          have hb : b = D.second.right := by
            rw [← hab, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
              Equiv.swap_apply_of_ne_of_ne hDdisj.2.1.symm hDdisj.2.2.2.symm]
          exact Or.inr (by simp [hb, GridRectangleBetween.sideColumns])
        · by_cases ha₄ : a = D.second.right
          · subst ha₄
            have hb : b = D.second.left := by
              rw [← hab, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
                Equiv.swap_apply_of_ne_of_ne hDdisj.1.symm hDdisj.2.2.1.symm]
            exact Or.inr (by simp [hb, GridRectangleBetween.sideColumns, Finset.pair_comm])
          · exfalso
            have hfix : b = a := by
              rw [← hab, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne ha₃ ha₄,
                Equiv.swap_apply_of_ne_of_ne ha₁ ha₂]
            exact hne hfix.symm
  have h1 : E.first.sideColumns = D.first.sideColumns ∨
      E.first.sideColumns = D.second.sideColumns := by
    apply hpair (a := E.first.left) (b := E.first.right) _ E.first.left_ne_right
    rw [← hperm, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hEdisj.1 hEdisj.2.1,
      Equiv.swap_apply_left]
  have h2 : E.second.sideColumns = D.first.sideColumns ∨
      E.second.sideColumns = D.second.sideColumns := by
    apply hpair (a := E.second.left) (b := E.second.right) _ E.second.left_ne_right
    rw [← hperm, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hEdisj.2.1.symm hEdisj.2.2.2.symm]
  have hEne : E.first.sideColumns ≠ E.second.sideColumns := fun heq =>
    Finset.disjoint_left.mp (disjoint_sideColumns_of_hasDisjointSides hE)
      (by simp : E.first.left ∈ E.first.sideColumns) (heq ▸ by simp)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hEne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hEne

/-- When `D` has disjoint side columns, the unique other empty two-step decomposition with the same
covered-square multiset is `D.commute hD`. -/
theorem eq_commute_of_val_add_val_eq_of_ne {D E : GridRectangleDecomposition x z}
    (hD : D.HasDisjointSides) (hE₁ : E.first.IsEmpty) (hE₂ : E.second.IsEmpty) (hne : E ≠ D)
    (hdom : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val) :
    E = D.commute hD := by
  rcases sideColumns_eq_or_swap_of_hasDisjointSides hD with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact absurd (eq_of_hasDisjointSides_of_sideColumns_eq hD hE₁ h₁ h₂ hdom) hne
  · have hE : E.HasDisjointSides := hasDisjointSides_of_disjoint_sideColumns (by
      rw [h₁, h₂]
      exact (disjoint_sideColumns_of_hasDisjointSides hD).symm)
    have hcs₁ : (E.commute hE).first.sideColumns = D.first.sideColumns := by
      rw [GridRectangleBetween.sideColumns, E.commute_first_left hE, E.commute_first_right hE,
        ← GridRectangleBetween.sideColumns, h₂]
    have hcs₂ : (E.commute hE).second.sideColumns = D.second.sideColumns := by
      rw [GridRectangleBetween.sideColumns, E.commute_second_left hE, E.commute_second_right hE,
        ← GridRectangleBetween.sideColumns, h₁]
    have hdom' : (E.commute hE).first.toGridRectangle.coveredSquares.val +
        (E.commute hE).second.toGridRectangle.coveredSquares.val =
        D.first.toGridRectangle.coveredSquares.val +
          D.second.toGridRectangle.coveredSquares.val := by
      rw [E.commute_first_toGridRectangle hE, E.commute_second_toGridRectangle hE, add_comm, hdom]
    have heq : E.commute hE = D := eq_of_hasDisjointSides_of_sideColumns_eq hD
      (E.isEmpty_commute_first hE hE₁ hE₂) hcs₁ hcs₂ hdom'
    have hcomm : ∀ {F₁ F₂ : GridRectangleDecomposition x z} (h₁ : F₁.HasDisjointSides)
        (h₂ : F₂.HasDisjointSides), F₁ = F₂ → F₁.commute h₁ = F₂.commute h₂ := by
      rintro F₁ _ h₁ h₂ rfl
      rfl
    exact (E.commute_commute hE).symm.trans (hcomm (E.hasDisjointSides_commute hE) hD heq)

/-! ### One-common-side decompositions -/

/-- Two repartition-equivalent one-common-side decompositions with the same intermediate state are
equal. -/
private theorem eq_of_isRepartition_of_middle_eq {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hrep : D.IsRepartition E) (hmid : E.middle = D.middle) :
    E = D := by
  have h1 : (E.first.left = D.first.left ∧ E.first.right = D.first.right) ∨
      (E.first.left = D.first.right ∧ E.first.right = D.first.left) := by
    have hswap : x.swapColumns E.first.left E.first.right =
        x.swapColumns D.first.left D.first.right :=
      E.first.target_eq_swapColumns.symm.trans (hmid.trans D.first.target_eq_swapColumns)
    exact Sym2.eq_iff.mp (GridState.sym2_mk_eq_of_swapColumns_eq E.first.left_ne_right hswap)
  have h2 : (E.second.left = D.second.left ∧ E.second.right = D.second.right) ∨
      (E.second.left = D.second.right ∧ E.second.right = D.second.left) := by
    have hswap : D.middle.swapColumns E.second.left E.second.right =
        D.middle.swapColumns D.second.left D.second.right :=
      calc D.middle.swapColumns E.second.left E.second.right
          = E.middle.swapColumns E.second.left E.second.right :=
              congrArg (·.swapColumns E.second.left E.second.right) hmid.symm
        _ = z := E.second.target_eq_swapColumns.symm
        _ = D.middle.swapColumns D.second.left D.second.right := D.second.target_eq_swapColumns
    exact Sym2.eq_iff.mp (GridState.sym2_mk_eq_of_swapColumns_eq E.second.left_ne_right hswap)
  rcases h1 with ⟨hl₁, hr₁⟩ | ⟨hl₁, hr₁⟩ <;> rcases h2 with ⟨hl₂, hr₂⟩ | ⟨hl₂, hr₂⟩
  · exact GridRectangleDecomposition.ext hl₁ hr₁ hl₂
  · exfalso
    have hcov₁ : E.first.toGridRectangle.coveredSquares =
        D.first.toGridRectangle.coveredSquares := by
      simp only [GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def,
        GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
        GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.bottom_def,
        GridRectangleBetween.top_def, hl₁, hr₁]
    have hmem : (D.second.left, D.second.bottom) ∈
        E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares := by
      rw [hrep.coveredSquares_union_eq]
      exact Finset.mem_union_right _ D.second.left_bottom_mem_coveredSquares
    rcases Finset.mem_union.mp hmem with hmem₁ | hmem₂
    · exact Finset.disjoint_left.mp hrep.disjoint_coveredSquares_left
        (hcov₁ ▸ hmem₁) D.second.left_bottom_mem_coveredSquares
    · have hc := (E.second.mem_toGridRectangle_coveredSquares.mp hmem₂).1
      rw [hr₂] at hc
      exact Grid.right_notMem_cIco _ _ hc
  · exfalso
    have hcov₂ : E.second.toGridRectangle.coveredSquares =
        D.second.toGridRectangle.coveredSquares := by
      simp only [GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def,
        GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_left,
        GridRectangleBetween.toGridRectangle_right, GridRectangleBetween.toGridRectangle_bottom,
        GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.bottom_def,
        GridRectangleBetween.top_def, hl₂, hr₂, hmid]
    have hmem : (D.first.left, D.first.bottom) ∈
        E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares := by
      rw [hrep.coveredSquares_union_eq]
      exact Finset.mem_union_left _ D.first.left_bottom_mem_coveredSquares
    rcases Finset.mem_union.mp hmem with hmem₁ | hmem₂
    · have hc := (E.first.mem_toGridRectangle_coveredSquares.mp hmem₁).1
      rw [hr₁] at hc
      exact Grid.right_notMem_cIco _ _ hc
    · exact Finset.disjoint_left.mp hrep.disjoint_coveredSquares_left
        D.first.left_bottom_mem_coveredSquares (hcov₂ ▸ hmem₂)
  · -- Both rectangles flipped: opposite column intervals force equal side-column pairs.
    exfalso
    have hsub₁ : Grid.cIco D.first.left D.first.right ⊆ Grid.cIco D.second.right D.second.left := by
      intro c hc
      have hmem : (c, D.first.bottom) ∈
          E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares := by
        rw [hrep.coveredSquares_union_eq]
        refine Finset.mem_union_left _ ?_
        exact D.first.mem_toGridRectangle_coveredSquares.mpr
          ⟨hc, Grid.left_mem_cIco D.first.bottom_ne_top⟩
      rcases Finset.mem_union.mp hmem with hE₁ | hE₂
      · have hc' := (E.first.mem_toGridRectangle_coveredSquares.mp hE₁).1
        rw [hl₁, hr₁] at hc'
        exact absurd hc' (Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hc)
      · have hc' := (E.second.mem_toGridRectangle_coveredSquares.mp hE₂).1
        rwa [hl₂, hr₂] at hc'
    have hsub₂ : Grid.cIco D.first.right D.first.left ⊆ Grid.cIco D.second.left D.second.right := by
      intro c hc
      have hmem : (c, E.first.bottom) ∈
          D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares := by
        rw [← hrep.coveredSquares_union_eq]
        refine Finset.mem_union_left _ ?_
        exact E.first.mem_toGridRectangle_coveredSquares.mpr
          ⟨hl₁ ▸ hr₁ ▸ hc, Grid.left_mem_cIco E.first.bottom_ne_top⟩
      rcases Finset.mem_union.mp hmem with hD₁ | hD₂
      · have hc' := (D.first.mem_toGridRectangle_coveredSquares.mp hD₁).1
        exact absurd hc (Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hc')
      · exact (D.second.mem_toGridRectangle_coveredSquares.mp hD₂).1
    have heq : Grid.cIco D.first.left D.first.right = Grid.cIco D.second.right D.second.left := by
      refine Finset.Subset.antisymm hsub₁ fun c hc => ?_
      have huniv : c ∈ Grid.cIco D.first.left D.first.right ∪
          Grid.cIco D.first.right D.first.left := by
        rw [Grid.cIco_union_swap D.first.left_ne_right]
        exact Finset.mem_univ c
      rcases Finset.mem_union.mp huniv with h | h
      · exact h
      · exact absurd (hsub₂ h)
          (Finset.disjoint_right.mp (Grid.disjoint_cIco_swap _ _) hc)
    obtain ⟨hl, hr⟩ := endpoints_eq_of_cIco_eq D.first.left_ne_right D.second.left_ne_right.symm heq
    exact D.sideColumns_ne_of_hasOneCommonSide hone
      (by simp [GridRectangleBetween.sideColumns, hl, hr, Finset.pair_comm])

/-- A decomposition with `left = left` overlap admits only itself and its canonical recut as empty
repartitions. -/
private theorem eq_or_eq_recut_of_left_eq_left {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.left = D.second.left) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hrep : D.IsRepartition E) :
    E = D ∨ E = D.recut hone hD₁ hD₂ := by
  have hother : D.first.right ≠ D.second.right := fun hr =>
    D.sideColumns_ne_of_hasOneCommonSide hone
      (by simp [GridRectangleBetween.sideColumns, hcommon, hr])
  have hca : D.second.right ≠ D.first.left := by
    rw [hcommon]; exact D.second.left_ne_right.symm
  have hD₂top : D.second.top = x D.second.right := by
    rw [GridRectangleBetween.top_def, D.first.map_of_ne D.second.right hca hother.symm]
  have hD₂bot : D.second.bottom = D.first.top :=
    D.second_bottom_eq_first_top_of_left_eq_left hcommon
  have hord := D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon hother hD₁ hD₂
  -- Every square in `D₁ ∪ D₂` has row in `cIco (x a) (x c)`, hence misses row `x c`.
  have hrow_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
      p.2 ∈ Grid.cIco D.first.bottom D.second.top := by
    intro p hp
    have hmem : p ∈ D.first.toGridRectangle.coveredSquares ∪
        D.second.toGridRectangle.coveredSquares :=
      hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hord.2]
    rcases Finset.mem_union.mp hmem with h₁ | h₂
    · exact Finset.mem_union_left _ (D.first.mem_toGridRectangle_coveredSquares.mp h₁).2
    · exact Finset.mem_union_right _
        (hD₂bot ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).2)
  -- `E.first`'s side columns lie in `{a, b, c}`.
  have hunion : E.first.sideColumns ∪ E.second.sideColumns =
      D.first.sideColumns ∪ D.second.sideColumns :=
    (sideColumns_union_eq_of_hasOneCommonSide D E hone).symm
  have hE₁sub : ∀ k ∈ E.first.sideColumns,
      k = D.first.left ∨ k = D.first.right ∨ k = D.second.right := by
    intro k hk
    have hk' : k ∈ D.first.sideColumns ∪ D.second.sideColumns :=
      hunion ▸ Finset.mem_union_left _ hk
    simp only [Finset.mem_union, GridRectangleBetween.mem_sideColumns, ← hcommon] at hk'
    tauto
  have hEl := hE₁sub E.first.left (by simp)
  have hEr := hE₁sub E.first.right (by simp)
  have hdata := D.isRecutOfLeftEqLeft_recut hcommon hone hD₁ hD₂
  have hrecut_rep : (D.recut hone hD₁ hD₂).IsRepartition E :=
    ⟨(D.isRecut_recut hone hD₁ hD₂).isRepartition.disjoint_coveredSquares_right,
      hrep.disjoint_coveredSquares_right,
      hrep.coveredSquares_union_eq.trans
        (D.isRecut_recut hone hD₁ hD₂).isRepartition.coveredSquares_union_eq.symm⟩
  -- Case split on the unordered pair of sides of `E.first`.
  have hmid_cases : E.middle = D.middle ∨
      E.middle = x.swapColumns D.first.right D.second.right ∨
      E.middle = x.swapColumns D.first.left D.second.right := by
    have hEm := E.first.target_eq_swapColumns
    have hDm := D.first.target_eq_swapColumns
    rcases hEl with h₁ | h₁ | h₁ <;> rcases hEr with h₂ | h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
    · exact Or.inl (hEm.trans (by rw [h₁, h₂]; exact hDm.symm))
    · exact Or.inr (Or.inr (hEm.trans (by rw [h₁, h₂])))
    · exact Or.inl (hEm.trans (by rw [h₁, h₂, GridState.swapColumns_comm]; exact hDm.symm))
    · exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
    · exact Or.inr (Or.inl (hEm.trans (by rw [h₁, h₂])))
    · exact Or.inr (Or.inr (hEm.trans (by rw [h₁, h₂, GridState.swapColumns_comm])))
    · exact Or.inr (Or.inl (hEm.trans (by rw [h₁, h₂, GridState.swapColumns_comm])))
    · exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
  rcases hmid_cases with hmid | hmid | hmid
  · exact Or.inl (eq_of_isRepartition_of_middle_eq hone hrep hmid)
  · rcases hdata.recut_branch with ⟨-, hRmid, -⟩ | ⟨hcol, -⟩
    · exact Or.inr (eq_of_isRepartition_of_middle_eq
        (D.hasOneCommonSide_recut hone hD₁ hD₂) hrecut_rep (hmid.trans hRmid.symm))
    · -- `c ∈ cIoo a b`: columns of `D₁ ∪ D₂` lie in `cIco a b` (missing `b`), rows miss `x c`.
      exfalso
      have hcol_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
          p.1 ∈ Grid.cIco D.first.left D.first.right := by
        intro p hp
        have hmem : p ∈ D.first.toGridRectangle.coveredSquares ∪
            D.second.toGridRectangle.coveredSquares :=
          hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp
        rcases Finset.mem_union.mp hmem with h₁ | h₂
        · exact (D.first.mem_toGridRectangle_coveredSquares.mp h₁).1
        · exact Grid.mem_cIco_of_mem_cIco_of_mem_cIoo
            (hcommon ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).1) hcol
      have hpair := Sym2.eq_iff.mp (GridState.sym2_mk_eq_of_swapColumns_eq E.first.left_ne_right
        (E.first.target_eq_swapColumns.symm.trans hmid))
      rcases hpair with ⟨hl, _⟩ | ⟨hl, _⟩
      · have hc := hcol_mem E.first.left_bottom_mem_coveredSquares
        dsimp only at hc
        rw [hl] at hc
        exact Grid.right_notMem_cIco _ _ hc
      · have hr := hrow_mem E.first.left_bottom_mem_coveredSquares
        dsimp only at hr
        rw [E.first.bottom_def, hl, ← hD₂top] at hr
        exact Grid.right_notMem_cIco _ _ hr
  · rcases hdata.recut_branch with ⟨hcol, -⟩ | ⟨-, hRmid, -⟩
    · -- `b ∈ cIoo a c`: columns lie in `cIco a c` (missing `c`), and `(a, c)` contains `(b, x b)`.
      exfalso
      have hcol_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
          p.1 ∈ Grid.cIco D.first.left D.second.right := by
        intro p hp
        have hmem : p ∈ D.first.toGridRectangle.coveredSquares ∪
            D.second.toGridRectangle.coveredSquares :=
          hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp
        rcases Finset.mem_union.mp hmem with h₁ | h₂
        · exact Grid.mem_cIco_of_mem_cIco_of_mem_cIoo
            (D.first.mem_toGridRectangle_coveredSquares.mp h₁).1 hcol
        · exact hcommon ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).1
      have hpair := Sym2.eq_iff.mp (GridState.sym2_mk_eq_of_swapColumns_eq E.first.left_ne_right
        (E.first.target_eq_swapColumns.symm.trans hmid))
      rcases hpair with ⟨hl, hr⟩ | ⟨hl, _⟩
      · have hnot := E.first.isEmpty_iff_forall_notMem_cIoo.mp hE₁ D.first.right
          (by rw [hl, hr]; exact hcol)
        apply hnot
        rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hl, hr,
          ← D.first.bottom_def, ← hD₂top]
        exact D.first.top_def ▸ hord.2
      · have hc := hcol_mem E.first.left_bottom_mem_coveredSquares
        dsimp only at hc
        rw [hl] at hc
        exact Grid.right_notMem_cIco _ _ hc
    · exact Or.inr (eq_of_isRepartition_of_middle_eq
        (D.hasOneCommonSide_recut hone hD₁ hD₂) hrecut_rep (hmid.trans hRmid.symm))

/-- A decomposition with `right = right` overlap admits only itself and its canonical recut as
empty repartitions. -/
private theorem eq_or_eq_recut_of_right_eq_right {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.right = D.second.right) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hrep : D.IsRepartition E) :
    E = D ∨ E = D.recut hone hD₁ hD₂ := by
  have hother : D.first.left ≠ D.second.left := fun hl =>
    D.sideColumns_ne_of_hasOneCommonSide hone
      (by simp [GridRectangleBetween.sideColumns, hcommon, hl])
  have hca : D.second.left ≠ D.first.right := by
    rw [hcommon]; exact D.second.left_ne_right
  have hD₂bot : D.second.bottom = x D.second.left := by
    rw [GridRectangleBetween.bottom_def, D.first.map_of_ne D.second.left hother.symm hca]
  have hD₂top : D.second.top = D.first.bottom := by
    rw [GridRectangleBetween.top_def, GridRectangleBetween.bottom_def, ← hcommon, D.first.map_right]
  have hord := D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon hother hD₁ hD₂
  -- Every square in `D₁ ∪ D₂` has row in `cIco (x c) (x a)`, hence misses row `x a`.
  have hrow_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
      p.2 ∈ Grid.cIco D.second.bottom D.first.top := by
    intro p hp
    have hmem : p ∈ D.first.toGridRectangle.coveredSquares ∪
        D.second.toGridRectangle.coveredSquares :=
      hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hord.2]
    rcases Finset.mem_union.mp hmem with h₁ | h₂
    · exact Finset.mem_union_right _ (D.first.mem_toGridRectangle_coveredSquares.mp h₁).2
    · exact Finset.mem_union_left _
        (hD₂top ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).2)
  have hunion : E.first.sideColumns ∪ E.second.sideColumns =
      D.first.sideColumns ∪ D.second.sideColumns :=
    (sideColumns_union_eq_of_hasOneCommonSide D E hone).symm
  have hE₁sub : ∀ k ∈ E.first.sideColumns,
      k = D.first.left ∨ k = D.first.right ∨ k = D.second.left := by
    intro k hk
    have hk' : k ∈ D.first.sideColumns ∪ D.second.sideColumns :=
      hunion ▸ Finset.mem_union_left _ hk
    simp only [Finset.mem_union, GridRectangleBetween.mem_sideColumns, ← hcommon] at hk'
    tauto
  have hEl := hE₁sub E.first.left (by simp)
  have hEr := hE₁sub E.first.right (by simp)
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hD₁ hD₂
  have hrecut_rep : (D.recut hone hD₁ hD₂).IsRepartition E :=
    ⟨(D.isRecut_recut hone hD₁ hD₂).isRepartition.disjoint_coveredSquares_right,
      hrep.disjoint_coveredSquares_right,
      hrep.coveredSquares_union_eq.trans
        (D.isRecut_recut hone hD₁ hD₂).isRepartition.coveredSquares_union_eq.symm⟩
  have hmid_cases : E.middle = D.middle ∨
      E.middle = x.swapColumns D.second.left D.first.left ∨
      E.middle = x.swapColumns D.second.left D.first.right := by
    have hEm := E.first.target_eq_swapColumns
    have hDm := D.first.target_eq_swapColumns
    rcases hEl with h₁ | h₁ | h₁ <;> rcases hEr with h₂ | h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
    · exact Or.inl (hEm.trans (by rw [h₁, h₂]; exact hDm.symm))
    · exact Or.inr (Or.inl (hEm.trans (by rw [h₁, h₂, GridState.swapColumns_comm])))
    · exact Or.inl (hEm.trans (by rw [h₁, h₂, GridState.swapColumns_comm]; exact hDm.symm))
    · exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
    · exact Or.inr (Or.inr (hEm.trans (by rw [h₁, h₂, GridState.swapColumns_comm])))
    · exact Or.inr (Or.inl (hEm.trans (by rw [h₁, h₂])))
    · exact Or.inr (Or.inr (hEm.trans (by rw [h₁, h₂])))
    · exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
  rcases hmid_cases with hmid | hmid | hmid
  · exact Or.inl (eq_of_isRepartition_of_middle_eq hone hrep hmid)
  · rcases hdata.recut_branch with ⟨-, hRmid, -⟩ | ⟨hcol, -⟩
    · exact Or.inr (eq_of_isRepartition_of_middle_eq
        (D.hasOneCommonSide_recut hone hD₁ hD₂) hrecut_rep (hmid.trans hRmid.symm))
    · -- `c ∈ cIoo b a`, so columns of `D₁ ∪ D₂` lie in `cIco b a` (missing `a`).
      exfalso
      have hcol_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
          p.1 ∈ Grid.cIco D.first.left D.first.right := by
        intro p hp
        have hmem : p ∈ D.first.toGridRectangle.coveredSquares ∪
            D.second.toGridRectangle.coveredSquares :=
          hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp
        rcases Finset.mem_union.mp hmem with h₁ | h₂
        · exact (D.first.mem_toGridRectangle_coveredSquares.mp h₁).1
        · exact Grid.cIco_subset_of_mem_cIoo hcol
            (hcommon ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).1)
      have hpair := Sym2.eq_iff.mp (GridState.sym2_mk_eq_of_swapColumns_eq E.first.left_ne_right
        (E.first.target_eq_swapColumns.symm.trans hmid))
      rcases hpair with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · -- `E₁ = (c, b)`: `a ∈ cIoo c b`, so `(a, E₁.bottom) ∈ E₁`, contradicting `col ≠ a`.
        have ha_mem : (D.first.right, E.first.bottom) ∈ E.first.toGridRectangle.coveredSquares := by
          refine E.first.mem_toGridRectangle_coveredSquares.mpr ⟨?_, ?_⟩
          · rw [hl, hr]
            exact Grid.cIoo_subset_cIco _ _ (Grid.mem_cIoo_cyclic_left hcol)
          · exact Grid.left_mem_cIco E.first.bottom_ne_top
        exact Grid.right_notMem_cIco _ _ (hcol_mem ha_mem)
      · -- `E₁ = (b, c)`: `x a ∈ cIoo (x b) (x c)`, so `(E₁.left, x a) ∈ E₁`, impossible.
        have hxa_mem : (E.first.left, D.first.top) ∈ E.first.toGridRectangle.coveredSquares := by
          refine E.first.mem_toGridRectangle_coveredSquares.mpr ⟨?_, ?_⟩
          · exact Grid.left_mem_cIco E.first.left_ne_right
          · dsimp only
            rw [hl, hr, ← D.first.bottom_def, ← hD₂bot]
            exact Grid.cIoo_subset_cIco _ _ (Grid.mem_cIoo_cyclic_left hord.2)
        exact Grid.right_notMem_cIco _ _ (hrow_mem hxa_mem)
  · rcases hdata.recut_branch with ⟨hcol, -⟩ | ⟨-, hRmid, -⟩
    · -- `b ∈ cIoo c a`: columns lie in `cIco c a` (missing `a`), and `(c, a)` contains `(b, x b)`.
      exfalso
      have hcol_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
          p.1 ∈ Grid.cIco D.second.left D.first.right := by
        intro p hp
        have hmem : p ∈ D.first.toGridRectangle.coveredSquares ∪
            D.second.toGridRectangle.coveredSquares :=
          hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp
        rcases Finset.mem_union.mp hmem with h₁ | h₂
        · exact Grid.cIco_subset_of_mem_cIoo hcol
            (D.first.mem_toGridRectangle_coveredSquares.mp h₁).1
        · exact hcommon ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).1
      have hpair := Sym2.eq_iff.mp (GridState.sym2_mk_eq_of_swapColumns_eq E.first.left_ne_right
        (E.first.target_eq_swapColumns.symm.trans hmid))
      rcases hpair with ⟨hl, hr⟩ | ⟨hl, _⟩
      · have hnot := E.first.isEmpty_iff_forall_notMem_cIoo.mp hE₁ D.first.left
          (by rw [hl, hr]; exact hcol)
        apply hnot
        rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hl, hr,
          ← hD₂bot, ← D.first.top_def]
        exact D.first.bottom_def ▸ hord.2
      · have hc := hcol_mem E.first.left_bottom_mem_coveredSquares
        dsimp only at hc
        rw [hl] at hc
        exact Grid.right_notMem_cIco _ _ hc
    · exact Or.inr (eq_of_isRepartition_of_middle_eq
        (D.hasOneCommonSide_recut hone hD₁ hD₂) hrecut_rep (hmid.trans hRmid.symm))

/-- When `D` shares exactly one side column, the unique other empty two-step decomposition with
the same covered-square multiset is `D.recut hone hD₁ hD₂`. -/
theorem eq_recut_of_val_add_val_eq_of_ne {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hE₁ : E.first.IsEmpty) (hne : E ≠ D)
    (hdom : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val) :
    E = D.recut hone hD₁ hD₂ := by
  have hDdisj : Disjoint D.first.toGridRectangle.coveredSquares
      D.second.toGridRectangle.coveredSquares :=
    (D.isRecut_recut hone hD₁ hD₂).isRepartition.disjoint_coveredSquares_left
  obtain ⟨hEdisj, hunion⟩ := disjoint_and_union_eq_of_val_add_val_eq hDdisj hdom
  have hrep : D.IsRepartition E := ⟨hDdisj, hEdisj, hunion⟩
  rcases D.hasSameSideOverlap_or_hasMixedSideOverlap hone with hsame | hmixed
  · rcases (D.hasSameSideOverlap_iff.mp hsame).2 with hleft | hright
    · exact (eq_or_eq_recut_of_left_eq_left hleft hone hD₁ hD₂ hE₁ hrep).resolve_left hne
    · exact (eq_or_eq_recut_of_right_eq_right hright hone hD₁ hD₂ hE₁ hrep).resolve_left hne
  · let D' := D.recut hone hD₁ hD₂
    have hrecut := D.isRecut_recut hone hD₁ hD₂
    have hone' := D.hasOneCommonSide_recut hone hD₁ hD₂
    have hsame' : D'.HasSameSideOverlap :=
      (D.hasSameSideOverlap_recut_iff hone hD₁ hD₂).mpr hmixed
    have hrep' : D'.IsRepartition E :=
      ⟨hrecut.isRepartition.disjoint_coveredSquares_right, hEdisj,
        hunion.trans hrecut.isRepartition.coveredSquares_union_eq.symm⟩
    have hcases : E = D' ∨ E = D'.recut hone' hrecut.isEmpty_first hrecut.isEmpty_second := by
      rcases (D'.hasSameSideOverlap_iff.mp hsame').2 with hleft | hright
      · exact eq_or_eq_recut_of_left_eq_left hleft hone' hrecut.isEmpty_first
          hrecut.isEmpty_second hE₁ hrep'
      · exact eq_or_eq_recut_of_right_eq_right hright hone' hrecut.isEmpty_first
          hrecut.isEmpty_second hE₁ hrep'
    rw [D.recut_recut hone hD₁ hD₂] at hcases
    exact hcases.resolve_right hne

end GridRectangleDecomposition

end TauCeti
