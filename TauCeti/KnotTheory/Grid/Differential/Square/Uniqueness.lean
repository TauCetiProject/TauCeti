/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing
import TauCeti.Data.Finset.Basic
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

/-! ### Helper lemmas on side columns and covered squares -/

/-- An empty rectangle does not cover the source state's point outside its side columns. -/
private theorem notMem_coveredSquares_of_isEmpty_of_notMem_sideColumns
    {x y : GridState n} {r : GridRectangleBetween x y} (hr : r.IsEmpty) {c : Fin n}
    (hc : c ∉ r.sideColumns) : (c, x c) ∉ r.toGridRectangle.coveredSquares := by
  intro hmem
  rw [GridRectangleBetween.mem_sideColumns, not_or] at hc
  rw [r.mem_toGridRectangle_coveredSquares] at hmem
  have hr_ne : x c ≠ r.bottom := fun heq => hc.1 (x.toPerm.injective (heq.trans r.bottom_def))
  exact (r.isEmpty_iff_forall_notMem_cIoo.mp hr c (Grid.mem_cIoo_of_mem_cIco hmem.1 hc.1))
    (Grid.mem_cIoo_of_mem_cIco hmem.2 hr_ne)

/-- `HasDisjointSides` is equivalent to disjointness of side-column sets. -/
private theorem hasDisjointSides_iff_disjoint_sideColumns {D : GridRectangleDecomposition x z} :
    D.HasDisjointSides ↔ Disjoint D.first.sideColumns D.second.sideColumns := by
  rw [D.hasDisjointSides_iff]
  simp only [GridRectangleBetween.sideColumns, Finset.disjoint_insert_left,
    Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or, and_assoc]

/-- Two rectangles with the same source state and side endpoints cover the same squares. -/
private theorem coveredSquares_eq {x₁ y₁ x₂ y₂ : GridState n}
    {r₁ : GridRectangleBetween x₁ y₁} {r₂ : GridRectangleBetween x₂ y₂}
    (hx : x₁ = x₂) (hl : r₁.left = r₂.left) (hr : r₁.right = r₂.right) :
    r₁.toGridRectangle.coveredSquares = r₂.toGridRectangle.coveredSquares := by
  subst hx
  obtain rfl : y₁ = y₂ := by rw [r₁.target_eq_swapColumns, r₂.target_eq_swapColumns, hl, hr]
  rw [GridRectangleBetween.ext hl hr]

/-- Equal unordered side-column pairs plus membership of `r₁.left` in `cIco r₂.left r₂.right`
forces matching ordered endpoints. -/
private theorem left_right_eq_of_sideColumns_eq {x₁ y₁ x₂ y₂ : GridState n}
    {r₁ : GridRectangleBetween x₁ y₁} {r₂ : GridRectangleBetween x₂ y₂}
    (hs : r₂.sideColumns = r₁.sideColumns) (hc : r₁.left ∈ Grid.cIco r₂.left r₂.right) :
    r₂.left = r₁.left ∧ r₂.right = r₁.right := by
  have hmem : ∀ c ∈ r₁.sideColumns, c = r₂.left ∨ c = r₂.right := fun c h => by
    rwa [← hs, GridRectangleBetween.mem_sideColumns] at h
  have hl : r₂.left = r₁.left :=
    ((hmem _ (by simp)).resolve_right fun h => Grid.right_notMem_cIco _ _ (h ▸ hc)).symm
  exact ⟨hl, ((hmem _ (by simp)).resolve_left fun h => r₁.left_ne_right (h.trans hl).symm).symm⟩

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
    (Finset.disjoint_and_union_eq_of_val_add_val_eq
      (D.first.disjoint_coveredSquares D.second) hdom).2
  have hvh : ∀ {a b c d : Fin n}, c ≠ d →
      Grid.cIco a b ×ˢ (Finset.univ : Finset (Fin n)) ≠
        (Finset.univ : Finset (Fin n)) ×ˢ Grid.cIco c d := fun {a b c d} hcd h => by
    have hmem : (b, c) ∈ Grid.cIco a b ×ˢ (Finset.univ : Finset (Fin n)) :=
      h ▸ Finset.mem_product.mpr ⟨Finset.mem_univ b, Grid.left_mem_cIco hcd⟩
    exact Grid.right_notMem_cIco a b (Finset.mem_product.mp hmem).1
  rcases D.first.left_right_eq_cases D.second with ⟨hDl, _⟩ | ⟨hDl, _⟩ <;>
    rcases E.first.left_right_eq_cases E.second with ⟨hEl, _⟩ | ⟨hEl, _⟩
  · rw [D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hDl,
      E.first.coveredSquares_union_coveredSquares_of_left_eq_left E.second hEl] at hunion
    have hcols : Grid.cIco E.first.left E.first.right = Grid.cIco D.first.left D.first.right := by
      ext c; simpa [GridRectangle.mem_coveredColumns] using
        eq_iff_iff.mp (congrArg (fun S => (c, D.first.bottom) ∈ S) hunion)
    obtain ⟨hl, hr⟩ := (Grid.cIco_eq_cIco_iff (Or.inl E.first.left_ne_right)).mp hcols
    exact hne (GridRectangleDecomposition.ext hl hr (hEl.trans (hl.trans hDl.symm)))
  · rw [D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hDl,
      E.first.coveredSquares_union_coveredSquares_of_left_eq_right E.second hEl] at hunion
    exact hvh E.first.bottom_ne_top hunion.symm
  · rw [D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hDl,
      E.first.coveredSquares_union_coveredSquares_of_left_eq_left E.second hEl] at hunion
    exact hvh D.first.bottom_ne_top hunion
  · rw [D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hDl,
      E.first.coveredSquares_union_coveredSquares_of_left_eq_right E.second hEl] at hunion
    have hrows : Grid.cIco E.first.bottom E.first.top = Grid.cIco D.first.bottom D.first.top := by
      ext r; simpa [GridRectangle.mem_coveredRows] using
        eq_iff_iff.mp (congrArg (fun S => (D.first.left, r) ∈ S) hunion)
    obtain ⟨hb, ht⟩ := (Grid.cIco_eq_cIco_iff (Or.inl E.first.bottom_ne_top)).mp hrows
    have hl := z.toPerm.injective (E.first.bottom_def.symm.trans (hb.trans D.first.bottom_def))
    have hr := z.toPerm.injective (E.first.top_def.symm.trans (ht.trans D.first.top_def))
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
  have hnot_mem : D.second.left ∉ E.first.sideColumns :=
    hs₁ ▸ Finset.disjoint_right.mp (hasDisjointSides_iff_disjoint_sideColumns.mp hD) (by simp)
  have hD₂bot : D.second.bottom = x D.second.left := by
    have hnot₁ : D.second.left ∉ D.first.sideColumns := hs₁ ▸ hnot_mem
    rw [GridRectangleBetween.mem_sideColumns, not_or] at hnot₁
    exact D.second.bottom_def.trans (D.first.map_of_ne D.second.left hnot₁.1 hnot₁.2)
  have hp₂_mem : (D.second.left, x D.second.left) ∈
      E.first.toGridRectangle.coveredSquares.val + E.second.toGridRectangle.coveredSquares.val :=
    hdom ▸ Multiset.mem_add.mpr (Or.inr (hD₂bot ▸ D.second.left_bottom_mem_coveredSquares))
  have hp₂_in₂ : (D.second.left, x D.second.left) ∈ E.second.toGridRectangle.coveredSquares :=
    (Multiset.mem_add.mp hp₂_mem).resolve_left
      (notMem_coveredSquares_of_isEmpty_of_notMem_sideColumns hE₁ hnot_mem)
  obtain ⟨hl₂, hr₂⟩ := left_right_eq_of_sideColumns_eq hs₂
    (E.second.mem_toGridRectangle_coveredSquares.mp hp₂_in₂).1
  have hmid : E.middle = D.middle := by
    have hmem : ∀ c ∈ E.first.sideColumns, c = D.first.left ∨ c = D.first.right := fun c h => by
      rw [hs₁, GridRectangleBetween.mem_sideColumns] at h; exact h
    rw [E.first.target_eq_swapColumns, D.first.target_eq_swapColumns]
    rcases hmem E.first.left (by simp) with h₁ | h₁ <;>
      rcases hmem E.first.right (by simp) with h₂ | h₂ <;>
      first | exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
            | simp [h₁, h₂, GridState.swapColumns_comm]
  rw [coveredSquares_eq hmid hl₂ hr₂] at hdom
  have hp₁_in₁ : (D.first.left, D.first.bottom) ∈ E.first.toGridRectangle.coveredSquares := by
    rw [← Finset.mem_val, add_right_cancel hdom, Finset.mem_val]
    exact D.first.left_bottom_mem_coveredSquares
  obtain ⟨hl₁, hr₁⟩ := left_right_eq_of_sideColumns_eq hs₁
    (E.first.mem_toGridRectangle_coveredSquares.mp hp₁_in₁).1
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
  have hE : E.HasDisjointSides :=
    (hzD ▸ hasDisjointSides_of_disjoint x D.first.left_ne_right D.second.left_ne_right
      (hasDisjointSides_iff_disjoint_sideColumns.mp hD) :
      ∀ F : GridRectangleDecomposition x z, F.HasDisjointSides) E
  have hperm_of : ∀ F : GridRectangleDecomposition x z, z.toPerm = x.toPerm *
      (Equiv.swap F.first.left F.first.right * Equiv.swap F.second.left F.second.right) := fun F =>
    (congrArg GridState.toPerm F.second.target_eq_swapColumns).trans <| by
      rw [GridState.swapColumns_toPerm, congrArg GridState.toPerm F.first.target_eq_swapColumns,
        GridState.swapColumns_toPerm, mul_assoc]
  have hperm := mul_left_cancel ((hperm_of E).symm.trans (hperm_of D))
  have hDdisj := D.hasDisjointSides_iff.mp hD
  have hEdisj := E.hasDisjointSides_iff.mp hE
  have hpair : ∀ {a b : Fin n},
      (Equiv.swap D.first.left D.first.right * Equiv.swap D.second.left D.second.right) a = b →
      a ≠ b → ({a, b} : Finset (Fin n)) = D.first.sideColumns ∨
        ({a, b} : Finset (Fin n)) = D.second.sideColumns := fun {a b} hab hne => by
    rcases hDdisj with ⟨hll, hlr, hrl, hrr⟩
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Equiv.swap_apply_def] at hab
    split_ifs at hab <;> subst_vars <;>
      simp_all [GridRectangleBetween.sideColumns, Finset.pair_comm]
  have h1 := hpair (by rw [← hperm, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hEdisj.1 hEdisj.2.1, Equiv.swap_apply_left]) E.first.left_ne_right
  have h2 := hpair (by rw [← hperm, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hEdisj.2.1.symm hEdisj.2.2.2.symm]) E.second.left_ne_right
  have hEne : E.first.sideColumns ≠ E.second.sideColumns := fun heq =>
    Finset.disjoint_left.mp (hasDisjointSides_iff_disjoint_sideColumns.mp hE)
      (by simp : E.first.left ∈ E.first.sideColumns) (heq ▸ by simp)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first | exact absurd (h1.trans h2.symm) hEne | exact Or.inl ⟨h1, h2⟩ | exact Or.inr ⟨h1, h2⟩

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
  · have hE : E.HasDisjointSides := hasDisjointSides_iff_disjoint_sideColumns.mpr
      (h₁ ▸ h₂ ▸ (hasDisjointSides_iff_disjoint_sideColumns.mp hD).symm)
    have heq : E.commute hE = D := eq_of_hasDisjointSides_of_sideColumns_eq hD
      (E.isEmpty_commute_first hE hE₁ hE₂)
      (by rw [GridRectangleBetween.sideColumns, E.commute_first_left hE, E.commute_first_right hE,
            ← GridRectangleBetween.sideColumns, h₂])
      (by rw [GridRectangleBetween.sideColumns, E.commute_second_left hE, E.commute_second_right hE,
            ← GridRectangleBetween.sideColumns, h₁])
      (by rw [E.commute_first_toGridRectangle hE, E.commute_second_toGridRectangle hE, add_comm,
        hdom])
    exact (E.commute_commute hE).symm.trans (by subst heq; rfl)

/-! ### One-common-side decompositions -/

/-- Two-way endpoint matching from `E.middle = x.swapColumns a b`. -/
private theorem first_sides_eq_of_middle_eq {E : GridRectangleDecomposition x z} {a b : Fin n}
    (hmid : E.middle = x.swapColumns a b) :
    (E.first.left = a ∧ E.first.right = b) ∨ (E.first.left = b ∧ E.first.right = a) :=
  Sym2.eq_iff.mp (GridState.sym2_mk_eq_of_swapColumns_eq E.first.left_ne_right
    (E.first.target_eq_swapColumns.symm.trans hmid))

/-- Two repartition-equivalent one-common-side decompositions with the same intermediate state are
equal. -/
private theorem eq_of_isRepartition_of_middle_eq {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hrep : D.IsRepartition E) (hmid : E.middle = D.middle) :
    E = D := by
  have h1 := first_sides_eq_of_middle_eq (hmid.trans D.first.target_eq_swapColumns)
  have h2 := Sym2.eq_iff.mp (GridState.sym2_mk_eq_of_swapColumns_eq E.second.left_ne_right
    ((congrArg (·.swapColumns E.second.left E.second.right) hmid.symm).trans
      (E.second.target_eq_swapColumns.symm.trans D.second.target_eq_swapColumns)))
  rcases h1 with ⟨hl₁, hr₁⟩ | ⟨hl₁, hr₁⟩ <;> rcases h2 with ⟨hl₂, hr₂⟩ | ⟨hl₂, hr₂⟩
  · exact GridRectangleDecomposition.ext hl₁ hr₁ hl₂
  · exfalso
    rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸
        Finset.mem_union_right _ D.second.left_bottom_mem_coveredSquares) with hmem₁ | hmem₂
    · exact Finset.disjoint_left.mp hrep.disjoint_coveredSquares_left
        (coveredSquares_eq rfl hl₁ hr₁ ▸ hmem₁) D.second.left_bottom_mem_coveredSquares
    · exact Grid.right_notMem_cIco _ _
        (hr₂ ▸ (E.second.mem_toGridRectangle_coveredSquares.mp hmem₂).1)
  · exfalso
    rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸
        Finset.mem_union_left _ D.first.left_bottom_mem_coveredSquares) with hmem₁ | hmem₂
    · exact Grid.right_notMem_cIco _ _
        (hr₁ ▸ (E.first.mem_toGridRectangle_coveredSquares.mp hmem₁).1)
    · exact Finset.disjoint_left.mp hrep.disjoint_coveredSquares_left
        D.first.left_bottom_mem_coveredSquares (coveredSquares_eq hmid hl₂ hr₂ ▸ hmem₂)
  · exfalso
    have hsub₁ : Grid.cIco D.first.left D.first.right ⊆ Grid.cIco D.second.right D.second.left :=
      fun c hc => (Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _
        (D.first.mem_toGridRectangle_coveredSquares (p := (c, D.first.bottom)) |>.mpr
          ⟨hc, Grid.left_mem_cIco D.first.bottom_ne_top⟩))).elim
        (fun hE₁ => absurd (hl₁ ▸ hr₁ ▸ (E.first.mem_toGridRectangle_coveredSquares.mp hE₁).1)
          (Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hc))
        (fun hE₂ => hl₂ ▸ hr₂ ▸ (E.second.mem_toGridRectangle_coveredSquares.mp hE₂).1)
    have hsub₂ : Grid.cIco D.first.right D.first.left ⊆ Grid.cIco D.second.left D.second.right :=
      fun c hc => (Finset.mem_union.mp (hrep.coveredSquares_union_eq.symm ▸ Finset.mem_union_left _
        (E.first.mem_toGridRectangle_coveredSquares (p := (c, E.first.bottom)) |>.mpr
          ⟨hl₁ ▸ hr₁ ▸ hc, Grid.left_mem_cIco E.first.bottom_ne_top⟩))).elim
        (fun hD₁ => absurd hc (Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _)
          (D.first.mem_toGridRectangle_coveredSquares.mp hD₁).1))
        (fun hD₂ => (D.second.mem_toGridRectangle_coveredSquares.mp hD₂).1)
    have heq : Grid.cIco D.first.left D.first.right = Grid.cIco D.second.right D.second.left :=
      Finset.Subset.antisymm hsub₁ fun c hc =>
        (Finset.mem_union.mp ((Grid.cIco_union_swap D.first.left_ne_right).symm ▸
          Finset.mem_univ c)).resolve_right fun h =>
            Finset.disjoint_right.mp (Grid.disjoint_cIco_swap _ _) hc (hsub₂ h)
    obtain ⟨hl, hr⟩ := (Grid.cIco_eq_cIco_iff (Or.inl D.first.left_ne_right)).mp heq
    exact D.sideColumns_ne_of_hasOneCommonSide hone
      (by simp [GridRectangleBetween.sideColumns, hl, hr, Finset.pair_comm])

/-- If `E.first`'s side columns lie in `{a, b, c}` where `D.first` swaps `{a, b}`, then `E.middle`
is one of `D.middle`, `x.swapColumns b c`, or `x.swapColumns a c`. -/
private theorem middle_cases_of_sideColumns_subset {D E : GridRectangleDecomposition x z}
    {a b c : Fin n} (hsub : ∀ k ∈ E.first.sideColumns, k = a ∨ k = b ∨ k = c)
    (hD : D.first.left = a ∧ D.first.right = b ∨ D.first.left = b ∧ D.first.right = a) :
    E.middle = D.middle ∨ E.middle = x.swapColumns b c ∨ E.middle = x.swapColumns a c := by
  have hDm : D.middle = x.swapColumns a b := by
    rcases hD with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
      simp [D.first.target_eq_swapColumns, hl, hr, GridState.swapColumns_comm]
  rw [hDm, E.first.target_eq_swapColumns]
  rcases hsub E.first.left (by simp) with h₁ | h₁ | h₁ <;>
    rcases hsub E.first.right (by simp) with h₂ | h₂ | h₂ <;>
    first | exact absurd (h₁.trans h₂.symm) E.first.left_ne_right
          | simp [h₁, h₂, GridState.swapColumns_comm]

/-- In a one-common-side hexagon with side-column sets `{a, b}` and `{a, c}`, every side column of
`E.first` is one of `a`, `b`, or `c`. -/
private theorem first_sideColumns_three_cases {D : GridRectangleDecomposition x z}
    (E : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide) {a b c : Fin n}
    (h₁ : D.first.sideColumns = {a, b}) (h₂ : D.second.sideColumns = {a, c}) :
    ∀ k ∈ E.first.sideColumns, k = a ∨ k = b ∨ k = c := fun k hk => by
  have hk' : k ∈ D.first.sideColumns ∪ D.second.sideColumns :=
    (sideColumns_union_eq_of_hasOneCommonSide D E hone) ▸ Finset.mem_union_left _ hk
  rw [h₁, h₂] at hk'
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk'
  tauto

/-- Every square of `E.first` has its row in the combined row span `cIco u w` when `D`'s two
rectangles partition `cIco u w` at an interior row `v`. -/
private theorem mem_cIco_rows_of_isRepartition {D E : GridRectangleDecomposition x z}
    (hrep : D.IsRepartition E) {u v w : Fin n} (hord : v ∈ Grid.cIoo u w)
    (hrows : (D.first.bottom = u ∧ D.first.top = v ∧ D.second.bottom = v ∧ D.second.top = w) ∨
      (D.second.bottom = u ∧ D.second.top = v ∧ D.first.bottom = v ∧ D.first.top = w)) :
    ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares → p.2 ∈ Grid.cIco u w :=
  fun hp => by
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hord]
    rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp) with
      h₁ | h₂
    · have hr := (D.first.mem_toGridRectangle_coveredSquares.mp h₁).2
      exact hrows.elim (fun ⟨hb, ht, _, _⟩ => Finset.mem_union_left _ (hb ▸ ht ▸ hr))
        (fun ⟨_, _, hb, ht⟩ => Finset.mem_union_right _ (hb ▸ ht ▸ hr))
    · have hr := (D.second.mem_toGridRectangle_coveredSquares.mp h₂).2
      exact hrows.elim (fun ⟨_, _, hb, ht⟩ => Finset.mem_union_right _ (hb ▸ ht ▸ hr))
        (fun ⟨hb, ht, _, _⟩ => Finset.mem_union_left _ (hb ▸ ht ▸ hr))

/-- Every square of `E.first` has its column in `cIco l r` whenever both rectangles of `D` have
their covered columns contained in `cIco l r`. -/
private theorem mem_cIco_cols_of_isRepartition {D E : GridRectangleDecomposition x z}
    (hrep : D.IsRepartition E) {l r : Fin n}
    (h₁ : Grid.cIco D.first.left D.first.right ⊆ Grid.cIco l r)
    (h₂ : Grid.cIco D.second.left D.second.right ⊆ Grid.cIco l r) :
    ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares → p.1 ∈ Grid.cIco l r :=
  fun hp => (Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp)).elim
    (fun h => h₁ (D.first.mem_toGridRectangle_coveredSquares.mp h).1)
    (fun h => h₂ (D.second.mem_toGridRectangle_coveredSquares.mp h).1)

/-- When every square of `E.first` lies in `cIco l r` and an interior column `m ∈ cIoo l r` has
`x m ∈ cIoo (x l) (x r)`, `E.first` cannot swap `l` and `r`: orientation `(l, r)` puts `(m, x m)`
in the interior of `E.first`, while orientation `(r, l)` puts column `r` in `cIco l r`. -/
private theorem not_middle_eq_swapColumns_of_mem_cIoo {E : GridRectangleDecomposition x z}
    (hE₁ : E.first.IsEmpty) {l m r : Fin n} (hcol : m ∈ Grid.cIoo l r)
    (hrow : x m ∈ Grid.cIoo (x l) (x r))
    (hcols : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
      p.1 ∈ Grid.cIco l r) : E.middle ≠ x.swapColumns l r := fun hmid => by
  rcases first_sides_eq_of_middle_eq hmid with ⟨hl, hr⟩ | ⟨hl, _⟩
  · exact E.first.isEmpty_iff_forall_notMem_cIoo.mp hE₁ m (hl ▸ hr ▸ hcol)
      (by simpa [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hl, hr] using hrow)
  · exact Grid.right_notMem_cIco l r (hl ▸ hcols E.first.left_bottom_mem_coveredSquares)

/-- Repartitioning is transitive from a decomposition to its canonical recut. -/
private theorem recut_isRepartition {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hrep : D.IsRepartition E) : (D.recut hone hD₁ hD₂).IsRepartition E :=
  ⟨(D.isRecut_recut hone hD₁ hD₂).isRepartition.disjoint_coveredSquares_right,
    hrep.disjoint_coveredSquares_right, hrep.coveredSquares_union_eq.trans
      (D.isRecut_recut hone hD₁ hD₂).isRepartition.coveredSquares_union_eq.symm⟩

private theorem eq_recut_of_middle_eq {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hrep : D.IsRepartition E) (hmid : E.middle = (D.recut hone hD₁ hD₂).middle) :
    E = D.recut hone hD₁ hD₂ :=
  eq_of_isRepartition_of_middle_eq (D.hasOneCommonSide_recut hone hD₁ hD₂)
    (recut_isRepartition hone hD₁ hD₂ hrep) hmid

/-- A decomposition with `left = left` overlap admits only itself and its canonical recut as empty
repartitions. -/
private theorem eq_or_eq_recut_of_left_eq_left {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.left = D.second.left) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hrep : D.IsRepartition E) : E = D ∨ E = D.recut hone hD₁ hD₂ := by
  have hother : D.first.right ≠ D.second.right := fun hr =>
    D.sideColumns_ne_of_hasOneCommonSide hone
      (by simp [GridRectangleBetween.sideColumns, hcommon, hr])
  have hD₂top : D.second.top = x D.second.right := by
    rw [GridRectangleBetween.top_def,
      D.first.map_of_ne D.second.right (hcommon ▸ D.second.left_ne_right.symm) hother.symm]
  have hord := D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon hother hD₁ hD₂
  have hrow_mem {p} := mem_cIco_rows_of_isRepartition (p := p) hrep hord.2
    (Or.inl ⟨rfl, rfl, D.second_bottom_eq_first_top_of_left_eq_left hcommon, rfl⟩)
  have hE₁sub := first_sideColumns_three_cases E hone rfl
    (by rw [GridRectangleBetween.sideColumns, ← hcommon])
  have hdata := D.isRecutOfLeftEqLeft_recut hcommon hone hD₁ hD₂
  -- Split on the three unordered column pairs that `E.first` can swap among `{a, b, c}`:
  -- `{a, b}` gives `D`, while `{b, c}` and `{a, c}` match `D.recut` in one column order and
  -- violate the hexagon bounds or emptiness of `E.first` in the opposite column order.
  rcases middle_cases_of_sideColumns_subset hE₁sub (Or.inl ⟨rfl, rfl⟩) with hmid | hmid | hmid
  · exact Or.inl (eq_of_isRepartition_of_middle_eq hone hrep hmid)
  · rcases hdata.recut_branch with ⟨-, hRmid, -⟩ | ⟨hcol, -⟩
    · exact Or.inr (eq_recut_of_middle_eq hone hD₁ hD₂ hrep (hmid.trans hRmid.symm))
    · exfalso
      have hcol_mem {p} := mem_cIco_cols_of_isRepartition (p := p) hrep Finset.Subset.rfl
        fun _ hc => Grid.mem_cIco_of_mem_cIco_of_mem_cIoo (hcommon ▸ hc) hcol
      rcases first_sides_eq_of_middle_eq hmid with ⟨hl, _⟩ | ⟨hl, _⟩
      · exact Grid.right_notMem_cIco _ _ (hl ▸ hcol_mem E.first.left_bottom_mem_coveredSquares)
      · have hr := hrow_mem E.first.left_bottom_mem_coveredSquares
        rw [E.first.bottom_def, hl, ← hD₂top] at hr; exact Grid.right_notMem_cIco _ _ hr
  · rcases hdata.recut_branch with ⟨hcol, -⟩ | ⟨-, hRmid, -⟩
    · exact absurd hmid <| not_middle_eq_swapColumns_of_mem_cIoo hE₁ hcol
        (by simpa [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, ← hD₂top]
          using hord.2)
        (fun hp => mem_cIco_cols_of_isRepartition hrep
          (fun _ hc => Grid.mem_cIco_of_mem_cIco_of_mem_cIoo hc hcol)
          (hcommon ▸ Finset.Subset.rfl) hp)
    · exact Or.inr (eq_recut_of_middle_eq hone hD₁ hD₂ hrep (hmid.trans hRmid.symm))

/-- A decomposition with `right = right` overlap admits only itself and its canonical recut as
empty repartitions. -/
private theorem eq_or_eq_recut_of_right_eq_right {D E : GridRectangleDecomposition x z}
    (hcommon : D.first.right = D.second.right) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hrep : D.IsRepartition E) : E = D ∨ E = D.recut hone hD₁ hD₂ := by
  have hother : D.first.left ≠ D.second.left := fun hl =>
    D.sideColumns_ne_of_hasOneCommonSide hone
      (by simp [GridRectangleBetween.sideColumns, hcommon, hl])
  have hD₂bot : D.second.bottom = x D.second.left := by
    rw [GridRectangleBetween.bottom_def,
      D.first.map_of_ne D.second.left hother.symm (hcommon ▸ D.second.left_ne_right)]
  have hD₂top : D.second.top = D.first.bottom := by
    rw [GridRectangleBetween.top_def, GridRectangleBetween.bottom_def, ← hcommon, D.first.map_right]
  have hord := D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon hother hD₁ hD₂
  have hrow_mem {p} := mem_cIco_rows_of_isRepartition (p := p) hrep hord.2
    (Or.inr ⟨rfl, hD₂top, rfl, rfl⟩)
  have hE₁sub := first_sideColumns_three_cases E hone
    (Finset.pair_comm D.first.left D.first.right)
    (by rw [GridRectangleBetween.sideColumns, ← hcommon, Finset.pair_comm])
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hD₁ hD₂
  -- Split on the three unordered column pairs that `E.first` can swap among `{r, l₁, l₂}`:
  -- `{l₁, r}` gives `D`, while `{l₁, l₂}` and `{l₂, r}` match `D.recut` in one column order and
  -- violate the hexagon bounds or emptiness of `E.first` in the opposite column order.
  rcases middle_cases_of_sideColumns_subset hE₁sub (Or.inr ⟨rfl, rfl⟩) with hmid | hmid | hmid
  · exact Or.inl (eq_of_isRepartition_of_middle_eq hone hrep hmid)
  · rw [GridState.swapColumns_comm] at hmid
    rcases hdata.recut_branch with ⟨-, hRmid, -⟩ | ⟨hcol, -⟩
    · exact Or.inr (eq_recut_of_middle_eq hone hD₁ hD₂ hrep (hmid.trans hRmid.symm))
    · exfalso
      have hcol_mem {p} := mem_cIco_cols_of_isRepartition (p := p) hrep Finset.Subset.rfl
        (hcommon ▸ Grid.cIco_subset_of_mem_cIoo hcol)
      rcases first_sides_eq_of_middle_eq hmid with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact Grid.right_notMem_cIco _ _ (hcol_mem (p := (D.first.right, E.first.bottom))
          (E.first.mem_toGridRectangle_coveredSquares.mpr
            ⟨by rw [hl, hr]; exact Grid.cIoo_subset_cIco _ _ (Grid.mem_cIoo_cyclic_left hcol),
              Grid.left_mem_cIco E.first.bottom_ne_top⟩))
      · exact Grid.right_notMem_cIco _ _ (hrow_mem (p := (E.first.left, D.first.top))
          (E.first.mem_toGridRectangle_coveredSquares.mpr ⟨Grid.left_mem_cIco E.first.left_ne_right,
            by dsimp only; rw [hl, hr, ← D.first.bottom_def, ← hD₂bot]
               exact Grid.cIoo_subset_cIco _ _ (Grid.mem_cIoo_cyclic_left hord.2)⟩))
  · rw [GridState.swapColumns_comm] at hmid
    rcases hdata.recut_branch with ⟨hcol, -⟩ | ⟨-, hRmid, -⟩
    · exact absurd hmid <| not_middle_eq_swapColumns_of_mem_cIoo hE₁ hcol
        (by simpa [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, ← hD₂bot]
          using hord.2)
        (fun hp => mem_cIco_cols_of_isRepartition hrep (Grid.cIco_subset_of_mem_cIoo hcol)
          (hcommon ▸ Finset.Subset.rfl) hp)
    · exact Or.inr (eq_recut_of_middle_eq hone hD₁ hD₂ hrep (hmid.trans hRmid.symm))

private theorem eq_or_eq_recut_of_hasSameSideOverlap {D E : GridRectangleDecomposition x z}
    (hsame : D.HasSameSideOverlap) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hrep : D.IsRepartition E) : E = D ∨ E = D.recut hone hD₁ hD₂ :=
  ((D.hasSameSideOverlap_iff.mp hsame).2).elim
    (fun h => eq_or_eq_recut_of_left_eq_left h hone hD₁ hD₂ hE₁ hrep)
    (fun h => eq_or_eq_recut_of_right_eq_right h hone hD₁ hD₂ hE₁ hrep)

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
  obtain ⟨hEdisj, hunion⟩ := Finset.disjoint_and_union_eq_of_val_add_val_eq hDdisj hdom
  have hrep : D.IsRepartition E := ⟨hDdisj, hEdisj, hunion⟩
  rcases D.hasSameSideOverlap_or_hasMixedSideOverlap hone with hsame | hmixed
  · exact (eq_or_eq_recut_of_hasSameSideOverlap hsame hone hD₁ hD₂ hE₁ hrep).resolve_left hne
  · have hrecut := D.isRecut_recut hone hD₁ hD₂
    have hcases := eq_or_eq_recut_of_hasSameSideOverlap
      ((D.hasSameSideOverlap_recut_iff hone hD₁ hD₂).mpr hmixed)
      (D.hasOneCommonSide_recut hone hD₁ hD₂) hrecut.isEmpty_first hrecut.isEmpty_second hE₁
      (recut_isRepartition hone hD₁ hD₂ hrep)
    rw [D.recut_recut hone hD₁ hD₂] at hcases
    exact hcases.resolve_right hne

end GridRectangleDecomposition

end TauCeti
