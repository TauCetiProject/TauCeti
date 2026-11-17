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
    have hstep : ∀ {p : Fin (m + 1)},
        (finRotate (m + 1) p ∈ Grid.cIco c d ↔ p ∉ Grid.cIco c d) →
        c = finRotate (m + 1) p ∨ d = finRotate (m + 1) p := by
      intro p hp
      by_contra hne
      push Not at hne
      have hiff := Grid.mem_cIco_finRotate_iff_of_ne hne.1 hne.2
      tauto
    have hac : a = c := by
      let p := (finRotate (m + 1))⁻¹ a
      have hp : finRotate (m + 1) p = a := Equiv.apply_symm_apply _ a
      have hpa : p ∉ Grid.cIco c d := h ▸ by
        rw [← hp, finRotate_apply]; exact Grid.notMem_cIco_finRotate_left p b
      have ha : finRotate (m + 1) p ∈ Grid.cIco c d := hp ▸ h ▸ Grid.left_mem_cIco hab
      rcases hstep ⟨fun _ => hpa, fun _ => ha⟩ with hca | hda
      · exact (hca.trans hp).symm
      · exact absurd (hp ▸ ha) (hda.trans hp ▸ Grid.right_notMem_cIco c d)
    have hbd : b = d := by
      let q := (finRotate (m + 1))⁻¹ b
      have hq : finRotate (m + 1) q = b := Equiv.apply_symm_apply _ b
      have hqb : q ∈ Grid.cIco c d := by
        rw [← h, ← hq]; exact Grid.self_mem_cIco_finRotate (by rw [hq]; exact hab)
      have hb : finRotate (m + 1) q ∉ Grid.cIco c d := hq ▸ h ▸ Grid.right_notMem_cIco a b
      rcases hstep ⟨fun h' => absurd h' hb, fun h' => absurd hqb h'⟩ with hcb | hdb
      · exact absurd (Grid.left_mem_cIco hcd) (hcb ▸ hb)
      · exact (hdb.trans hq).symm
    exact ⟨hac, hbd⟩

/-- If two finite sets are disjoint and another pair has the same multiset sum, then the second
pair is also disjoint and has the same union. -/
private theorem disjoint_and_union_eq_of_val_add_val_eq {α : Type*} [DecidableEq α]
    {A₁ A₂ B₁ B₂ : Finset α} (hA : Disjoint A₁ A₂) (hval : B₁.val + B₂.val = A₁.val + A₂.val) :
    Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = A₁ ∪ A₂ := by
  have hAnodup : (A₁.val + A₂.val).Nodup :=
    Multiset.nodup_add.mpr ⟨A₁.nodup, A₂.nodup, Finset.disjoint_val.mpr hA⟩
  refine ⟨Finset.disjoint_val.mp (Multiset.nodup_add.mp (hval ▸ hAnodup)).2.2, ?_⟩
  ext p
  simpa only [Finset.mem_union, Multiset.mem_add, Finset.mem_val] using
    show p ∈ B₁.val + B₂.val ↔ p ∈ A₁.val + A₂.val from hval ▸ Iff.rfl

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
  have hy : y₁ = y₂ :=
    r₁.target_eq_swapColumns.trans (by rw [hl, hr, ← r₂.target_eq_swapColumns])
  subst hy
  rw [GridRectangleBetween.ext hl hr]

/-- Equal unordered side-column pairs plus membership of `r₁.left` in `cIco r₂.left r₂.right`
forces matching ordered endpoints. -/
private theorem left_right_eq_of_sideColumns_eq {x₁ y₁ x₂ y₂ : GridState n}
    {r₁ : GridRectangleBetween x₁ y₁} {r₂ : GridRectangleBetween x₂ y₂}
    (hs : r₂.sideColumns = r₁.sideColumns) (hc : r₁.left ∈ Grid.cIco r₂.left r₂.right) :
    r₂.left = r₁.left ∧ r₂.right = r₁.right := by
  have hmem : ∀ c ∈ r₁.sideColumns, c = r₂.left ∨ c = r₂.right := fun c h => by
    rw [← hs, GridRectangleBetween.mem_sideColumns] at h
    exact h
  have hl : r₂.left = r₁.left :=
    ((hmem _ (by simp)).resolve_right fun h => Grid.right_notMem_cIco _ _ (h ▸ hc)).symm
  have hr : r₂.right = r₁.right :=
    ((hmem _ (by simp)).resolve_left fun h => r₁.left_ne_right (h.trans hl).symm).symm
  exact ⟨hl, hr⟩

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
  have hvh : ∀ {a b c d : Fin n}, c ≠ d →
      Grid.cIco a b ×ˢ (Finset.univ : Finset (Fin n)) ≠
        (Finset.univ : Finset (Fin n)) ×ˢ Grid.cIco c d := fun {a b c d} hcd h => by
    have hmem : (b, c) ∈ Grid.cIco a b ×ˢ (Finset.univ : Finset (Fin n)) :=
      h ▸ Finset.mem_product.mpr ⟨Finset.mem_univ _, Grid.left_mem_cIco hcd⟩
    exact Grid.right_notMem_cIco a b (Finset.mem_product.mp hmem).1
  rcases D.first.left_right_eq_cases D.second with ⟨hDl, _⟩ | ⟨hDl, _⟩ <;>
    rcases E.first.left_right_eq_cases E.second with ⟨hEl, _⟩ | ⟨hEl, _⟩
  · rw [D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hDl,
      E.first.coveredSquares_union_coveredSquares_of_left_eq_left E.second hEl] at hunion
    have hcols : Grid.cIco E.first.left E.first.right = Grid.cIco D.first.left D.first.right := by
      ext c
      simpa [GridRectangle.mem_coveredColumns] using
        eq_iff_iff.mp (congrArg (fun S => (c, D.first.bottom) ∈ S) hunion)
    obtain ⟨hl, hr⟩ := endpoints_eq_of_cIco_eq E.first.left_ne_right D.first.left_ne_right hcols
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
      ext r
      simpa [GridRectangle.mem_coveredRows] using
        eq_iff_iff.mp (congrArg (fun S => (D.first.left, r) ∈ S) hunion)
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
    change (D.first.left, D.first.bottom) ∈ E.first.toGridRectangle.coveredSquares.val
    rw [add_right_cancel hdom]
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
  have hDdisj := D.hasDisjointSides_iff.mp hD
  have hE : E.HasDisjointSides := by
    have key : ∀ {z' : GridState n} (E' : GridRectangleDecomposition x z'),
        z' = (x.swapColumns D.first.left D.first.right).swapColumns D.second.left
          D.second.right → E'.HasDisjointSides := by
      rintro _ E' rfl
      exact hasDisjointSides_of_disjoint x D.first.left_ne_right D.second.left_ne_right
        (hasDisjointSides_iff_disjoint_sideColumns.mp hD) E'
    exact key E hzD
  have hperm_of : ∀ F : GridRectangleDecomposition x z, z.toPerm = x.toPerm *
      (Equiv.swap F.first.left F.first.right * Equiv.swap F.second.left F.second.right) := fun F =>
    (congrArg GridState.toPerm F.second.target_eq_swapColumns).trans <| by
      rw [GridState.swapColumns_toPerm, congrArg GridState.toPerm F.first.target_eq_swapColumns,
        GridState.swapColumns_toPerm, mul_assoc]
  have hperm : Equiv.swap E.first.left E.first.right * Equiv.swap E.second.left E.second.right =
      Equiv.swap D.first.left D.first.right * Equiv.swap D.second.left D.second.right :=
    mul_left_cancel ((hperm_of E).symm.trans (hperm_of D))
  have hEdisj := E.hasDisjointSides_iff.mp hE
  have hpair : ∀ {a b : Fin n},
      (Equiv.swap D.first.left D.first.right * Equiv.swap D.second.left D.second.right) a = b →
      a ≠ b → ({a, b} : Finset (Fin n)) = D.first.sideColumns ∨
        ({a, b} : Finset (Fin n)) = D.second.sideColumns := by
    intro a b hab hne
    rcases hDdisj with ⟨hll, hlr, hrl, hrr⟩
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Equiv.swap_apply_def] at hab
    split_ifs at hab <;> subst_vars <;>
      simp_all [GridRectangleBetween.sideColumns, Finset.pair_comm]
  have h1 : E.first.sideColumns = D.first.sideColumns ∨
      E.first.sideColumns = D.second.sideColumns :=
    hpair (by rw [← hperm, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hEdisj.1 hEdisj.2.1, Equiv.swap_apply_left])
      E.first.left_ne_right
  have h2 : E.second.sideColumns = D.first.sideColumns ∨
      E.second.sideColumns = D.second.sideColumns :=
    hpair (by rw [← hperm, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
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
      (by rw [h₁, h₂]; exact (hasDisjointSides_iff_disjoint_sideColumns.mp hD).symm)
    have heq : E.commute hE = D := eq_of_hasDisjointSides_of_sideColumns_eq hD
      (E.isEmpty_commute_first hE hE₁ hE₂)
      (by rw [GridRectangleBetween.sideColumns, E.commute_first_left hE, E.commute_first_right hE,
        ← GridRectangleBetween.sideColumns, h₂])
      (by rw [GridRectangleBetween.sideColumns, E.commute_second_left hE,
        E.commute_second_right hE, ← GridRectangleBetween.sideColumns, h₁])
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
      fun c hc => by
        rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _
          (D.first.mem_toGridRectangle_coveredSquares (p := (c, D.first.bottom)) |>.mpr
            ⟨hc, Grid.left_mem_cIco D.first.bottom_ne_top⟩)) with hE₁ | hE₂
        · exact absurd (hl₁ ▸ hr₁ ▸ (E.first.mem_toGridRectangle_coveredSquares.mp hE₁).1)
            (Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hc)
        · exact hl₂ ▸ hr₂ ▸ (E.second.mem_toGridRectangle_coveredSquares.mp hE₂).1
    have hsub₂ : Grid.cIco D.first.right D.first.left ⊆ Grid.cIco D.second.left D.second.right :=
      fun c hc => by
        rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq.symm ▸ Finset.mem_union_left _
          (E.first.mem_toGridRectangle_coveredSquares (p := (c, E.first.bottom)) |>.mpr
            ⟨hl₁ ▸ hr₁ ▸ hc, Grid.left_mem_cIco E.first.bottom_ne_top⟩)) with hD₁ | hD₂
        · exact absurd hc (Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _)
            (D.first.mem_toGridRectangle_coveredSquares.mp hD₁).1)
        · exact (D.second.mem_toGridRectangle_coveredSquares.mp hD₂).1
    have heq : Grid.cIco D.first.left D.first.right = Grid.cIco D.second.right D.second.left :=
      Finset.Subset.antisymm hsub₁ fun c hc =>
        (Finset.mem_union.mp ((Grid.cIco_union_swap D.first.left_ne_right).symm ▸
          Finset.mem_univ c)).resolve_right fun h =>
            Finset.disjoint_right.mp (Grid.disjoint_cIco_swap _ _) hc (hsub₂ h)
    obtain ⟨hl, hr⟩ := endpoints_eq_of_cIco_eq D.first.left_ne_right D.second.left_ne_right.symm heq
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

/-- Repartitioning is transitive from a decomposition to its canonical recut. -/
private theorem recut_isRepartition {D E : GridRectangleDecomposition x z}
    (hone : D.HasOneCommonSide) (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hrep : D.IsRepartition E) : (D.recut hone hD₁ hD₂).IsRepartition E :=
  ⟨(D.isRecut_recut hone hD₁ hD₂).isRepartition.disjoint_coveredSquares_right,
    hrep.disjoint_coveredSquares_right,
    hrep.coveredSquares_union_eq.trans
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
    (hrep : D.IsRepartition E) :
    E = D ∨ E = D.recut hone hD₁ hD₂ := by
  have hother : D.first.right ≠ D.second.right := fun hr =>
    D.sideColumns_ne_of_hasOneCommonSide hone
      (by simp [GridRectangleBetween.sideColumns, hcommon, hr])
  have hca : D.second.right ≠ D.first.left := hcommon ▸ D.second.left_ne_right.symm
  have hD₂top : D.second.top = x D.second.right := by
    rw [GridRectangleBetween.top_def, D.first.map_of_ne D.second.right hca hother.symm]
  have hD₂bot : D.second.bottom = D.first.top :=
    D.second_bottom_eq_first_top_of_left_eq_left hcommon
  have hord := D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon hother hD₁ hD₂
  have hrow_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
      p.2 ∈ Grid.cIco D.first.bottom D.second.top := fun hp => by
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hord.2]
    rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp) with
      h₁ | h₂
    · exact Finset.mem_union_left _ (D.first.mem_toGridRectangle_coveredSquares.mp h₁).2
    · exact Finset.mem_union_right _
        (hD₂bot ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).2)
  have hE₁sub : ∀ k ∈ E.first.sideColumns,
      k = D.first.left ∨ k = D.first.right ∨ k = D.second.right := fun k hk => by
    have hk' : k ∈ D.first.sideColumns ∪ D.second.sideColumns :=
      (sideColumns_union_eq_of_hasOneCommonSide D E hone) ▸ Finset.mem_union_left _ hk
    simp only [Finset.mem_union, GridRectangleBetween.mem_sideColumns, ← hcommon] at hk'; tauto
  have hdata := D.isRecutOfLeftEqLeft_recut hcommon hone hD₁ hD₂
  rcases middle_cases_of_sideColumns_subset hE₁sub (Or.inl ⟨rfl, rfl⟩) with hmid | hmid | hmid
  · exact Or.inl (eq_of_isRepartition_of_middle_eq hone hrep hmid)
  · rcases hdata.recut_branch with ⟨-, hRmid, -⟩ | ⟨hcol, -⟩
    · exact Or.inr (eq_recut_of_middle_eq hone hD₁ hD₂ hrep (hmid.trans hRmid.symm))
    · exfalso
      have hcol_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
          p.1 ∈ Grid.cIco D.first.left D.first.right := fun hp => by
        rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp) with
          h₁ | h₂
        · exact (D.first.mem_toGridRectangle_coveredSquares.mp h₁).1
        · exact Grid.mem_cIco_of_mem_cIco_of_mem_cIoo
            (hcommon ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).1) hcol
      rcases first_sides_eq_of_middle_eq hmid with ⟨hl, _⟩ | ⟨hl, _⟩
      · exact Grid.right_notMem_cIco _ _ (hl ▸ hcol_mem E.first.left_bottom_mem_coveredSquares)
      · have hr := hrow_mem E.first.left_bottom_mem_coveredSquares
        rw [E.first.bottom_def, hl, ← hD₂top] at hr
        exact Grid.right_notMem_cIco _ _ hr
  · rcases hdata.recut_branch with ⟨hcol, -⟩ | ⟨-, hRmid, -⟩
    · exfalso
      have hcol_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
          p.1 ∈ Grid.cIco D.first.left D.second.right := fun hp => by
        rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp) with
          h₁ | h₂
        · exact Grid.mem_cIco_of_mem_cIco_of_mem_cIoo
            (D.first.mem_toGridRectangle_coveredSquares.mp h₁).1 hcol
        · exact hcommon ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).1
      rcases first_sides_eq_of_middle_eq hmid with ⟨hl, hr⟩ | ⟨hl, _⟩
      · refine E.first.isEmpty_iff_forall_notMem_cIoo.mp hE₁ D.first.right
          (by rw [hl, hr]; exact hcol) ?_
        rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hl, hr,
          ← D.first.bottom_def, ← hD₂top]
        exact D.first.top_def ▸ hord.2
      · exact Grid.right_notMem_cIco _ _ (hl ▸ hcol_mem E.first.left_bottom_mem_coveredSquares)
    · exact Or.inr (eq_recut_of_middle_eq hone hD₁ hD₂ hrep (hmid.trans hRmid.symm))

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
  have hca : D.second.left ≠ D.first.right := hcommon ▸ D.second.left_ne_right
  have hD₂bot : D.second.bottom = x D.second.left := by
    rw [GridRectangleBetween.bottom_def, D.first.map_of_ne D.second.left hother.symm hca]
  have hD₂top : D.second.top = D.first.bottom := by
    rw [GridRectangleBetween.top_def, GridRectangleBetween.bottom_def, ← hcommon, D.first.map_right]
  have hord := D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon hother hD₁ hD₂
  have hrow_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
      p.2 ∈ Grid.cIco D.second.bottom D.first.top := fun hp => by
    rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hord.2]
    rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp) with
      h₁ | h₂
    · exact Finset.mem_union_right _ (D.first.mem_toGridRectangle_coveredSquares.mp h₁).2
    · exact Finset.mem_union_left _
        (hD₂top ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).2)
  have hE₁sub : ∀ k ∈ E.first.sideColumns,
      k = D.first.right ∨ k = D.first.left ∨ k = D.second.left := fun k hk => by
    have hk' : k ∈ D.first.sideColumns ∪ D.second.sideColumns :=
      (sideColumns_union_eq_of_hasOneCommonSide D E hone) ▸ Finset.mem_union_left _ hk
    simp only [Finset.mem_union, GridRectangleBetween.mem_sideColumns, ← hcommon] at hk'; tauto
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hD₁ hD₂
  rcases middle_cases_of_sideColumns_subset hE₁sub (Or.inr ⟨rfl, rfl⟩) with hmid | hmid | hmid
  · exact Or.inl (eq_of_isRepartition_of_middle_eq hone hrep hmid)
  · rw [GridState.swapColumns_comm] at hmid
    rcases hdata.recut_branch with ⟨-, hRmid, -⟩ | ⟨hcol, -⟩
    · exact Or.inr (eq_recut_of_middle_eq hone hD₁ hD₂ hrep (hmid.trans hRmid.symm))
    · exfalso
      have hcol_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
          p.1 ∈ Grid.cIco D.first.left D.first.right := fun hp => by
        rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp) with
          h₁ | h₂
        · exact (D.first.mem_toGridRectangle_coveredSquares.mp h₁).1
        · exact Grid.cIco_subset_of_mem_cIoo hcol
            (hcommon ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).1)
      rcases first_sides_eq_of_middle_eq hmid with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact Grid.right_notMem_cIco _ _
          (hcol_mem (p := (D.first.right, E.first.bottom))
            (E.first.mem_toGridRectangle_coveredSquares.mpr
              ⟨by rw [hl, hr]; exact Grid.cIoo_subset_cIco _ _ (Grid.mem_cIoo_cyclic_left hcol),
                Grid.left_mem_cIco E.first.bottom_ne_top⟩))
      · exact Grid.right_notMem_cIco _ _
          (hrow_mem (p := (E.first.left, D.first.top))
            (E.first.mem_toGridRectangle_coveredSquares.mpr
              ⟨Grid.left_mem_cIco E.first.left_ne_right, by
                dsimp only; rw [hl, hr, ← D.first.bottom_def, ← hD₂bot]
                exact Grid.cIoo_subset_cIco _ _ (Grid.mem_cIoo_cyclic_left hord.2)⟩))
  · rw [GridState.swapColumns_comm] at hmid
    rcases hdata.recut_branch with ⟨hcol, -⟩ | ⟨-, hRmid, -⟩
    · exfalso
      have hcol_mem : ∀ {p : Fin n × Fin n}, p ∈ E.first.toGridRectangle.coveredSquares →
          p.1 ∈ Grid.cIco D.second.left D.first.right := fun hp => by
        rcases Finset.mem_union.mp (hrep.coveredSquares_union_eq ▸ Finset.mem_union_left _ hp) with
          h₁ | h₂
        · exact Grid.cIco_subset_of_mem_cIoo hcol
            (D.first.mem_toGridRectangle_coveredSquares.mp h₁).1
        · exact hcommon ▸ (D.second.mem_toGridRectangle_coveredSquares.mp h₂).1
      rcases first_sides_eq_of_middle_eq hmid with ⟨hl, hr⟩ | ⟨hl, _⟩
      · refine E.first.isEmpty_iff_forall_notMem_cIoo.mp hE₁ D.first.left
          (by rw [hl, hr]; exact hcol) ?_
        rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hl, hr,
          ← hD₂bot, ← D.first.top_def]
        exact D.first.bottom_def ▸ hord.2
      · exact Grid.right_notMem_cIco _ _ (hl ▸ hcol_mem E.first.left_bottom_mem_coveredSquares)
    · exact Or.inr (eq_recut_of_middle_eq hone hD₁ hD₂ hrep (hmid.trans hRmid.symm))

private theorem eq_or_eq_recut_of_hasSameSideOverlap {D E : GridRectangleDecomposition x z}
    (hsame : D.HasSameSideOverlap) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hE₁ : E.first.IsEmpty)
    (hrep : D.IsRepartition E) : E = D ∨ E = D.recut hone hD₁ hD₂ := by
  rcases (D.hasSameSideOverlap_iff.mp hsame).2 with hleft | hright
  · exact eq_or_eq_recut_of_left_eq_left hleft hone hD₁ hD₂ hE₁ hrep
  · exact eq_or_eq_recut_of_right_eq_right hright hone hD₁ hD₂ hE₁ hrep

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
