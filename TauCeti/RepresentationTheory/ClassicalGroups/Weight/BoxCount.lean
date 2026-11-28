/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight

/-!
# Box counts of determinant-normalized weights

A full-height column contributes only a determinant factor. Counting boxes in the
polynomial part `λ - λₙ` therefore gives the exponent contribution of the columns of
height strictly less than the rank. For a family of source weights with a single
nonzero row at the selected places, this count is the order times the number of selected
places (and is zero in ranks zero and one).

The source-weight application follows `New.Data.sum_height_mul_columnCount_le` of
[lsernau/grh-lean, `New/UpperBound/Size/ShortColumns.lean`][short-proof]. Here the count
uses Young diagrams of the determinant-normalized dominant weights directly.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/UpperBound/Size/ShortColumns.lean
-/

public section

open Finset

namespace TauCeti.DominantWeight

/-- The number of boxes in the polynomial part is the total weight minus the contribution
of the determinant twist. This includes the empty weight. -/
theorem natCast_card_detShiftShape {n : ℕ} (l : DominantWeight n) :
    (l.detShiftShape.card : ℤ) = (∑ i, l.val i) - n * l.detShift := by
  rw [l.detShiftShape.card_eq_sum_range_rowLen l.colLen_zero_detShiftShape_le,
    ← Fin.sum_univ_eq_sum_range]
  push_cast
  calc
    ∑ i : Fin n, (l.detShiftShape.rowLen i : ℤ) = ∑ i : Fin n, (l.val i - l.detShift) :=
      sum_congr rfl fun i _ ↦ eq_sub_of_add_eq (l.natCast_rowLen_detShiftShape_add_detShift i)
    _ = _ := by simp [sum_sub_distrib]

/-- For a weight constant except for an increment `a` in its first entry, the increment counts
all boxes in columns shorter than the rank. In rank zero or one the polynomial part is empty. -/
theorem card_detShiftShape_of_val_eq_add_ite {n : ℕ} (l : DominantWeight n) (a : ℕ) (c : ℤ)
    (hl : ∀ i, l.val i = c + if i.val = 0 then (a : ℤ) else 0) :
    l.detShiftShape.card = if 1 < n then a else 0 := by
  rcases n with _ | n
  · simp only [show ¬ 1 < 0 by decide, ite_false]
    exact_mod_cast (by simpa using l.natCast_card_detShiftShape : (l.detShiftShape.card : ℤ) = 0)
  rcases n with _ | n
  · simp only [show ¬ 1 < 1 by decide, ite_false]
    exact_mod_cast (by simpa [Fin.sum_univ_one] using l.natCast_card_detShiftShape :
      (l.detShiftShape.card : ℤ) = 0)
  have hshift : l.detShift = c := by simp [hl]
  have hcard : (l.detShiftShape.card : ℤ) = (a : ℤ) := by
    rw [natCast_card_detShiftShape, hshift]
    simp only [hl, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- The increment occurs at exactly the first index.
    have hs : (∑ i : Fin (n + 2), if i.val = 0 then (a : ℤ) else 0) = a := by simp
    rw [hs, add_comm, add_sub_cancel_right]
  simpa only [show 1 < n + 1 + 1 by omega, ite_true] using (Int.ofNat_inj.mp hcard)

/-- In a finite family of weights with first-row order `a` at places in `A` and zero polynomial
weight elsewhere, the total box count is `a` times the number of selected places, provided the
rank exceeds one. The constants `c` allow independent determinant twists at the places. -/
theorem sum_card_detShiftShape_of_val_eq_add_ite {ι : Type*} [DecidableEq ι] {n : ℕ}
    (s A : Finset ι) (l : ι → DominantWeight n) (a : ℕ) (c : ι → ℤ)
    (hl : ∀ τ ∈ s, ∀ i, (l τ).val i = c τ + if i.val = 0 ∧ τ ∈ A then (a : ℤ) else 0) :
    (∑ τ ∈ s, (l τ).detShiftShape.card) = if 1 < n then #(s ∩ A) * a else 0 := by
  have hcard (τ : ι) (hτ : τ ∈ s) :
      (l τ).detShiftShape.card = if 1 < n then (if τ ∈ A then a else 0) else 0 := by
    apply (l τ).card_detShiftShape_of_val_eq_add_ite _ (c τ)
    intro i
    by_cases hA : τ ∈ A <;> simp [hl τ hτ, hA]
  rw [sum_congr rfl hcard]
  split_ifs with hn
  · rw [← sum_filter]
    simp [filter_mem_eq_inter]
  · simp

end TauCeti.DominantWeight
