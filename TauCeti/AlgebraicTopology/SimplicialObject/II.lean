/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.II
import Mathlib.Order.Interval.Finset.Fin

/-!
# Cut-counting and Galois properties of `SimplexCategory.II`

This file supplements `Mathlib.AlgebraicTopology.SimplicialObject.II` with characterizations of
Gabriel–Zisman's cut map `SimplexCategory.II.map'` and `SimplexCategory.II.map`:

* `SimplexCategory.II.val_map'_eq_card`: `(SimplexCategory.II.map' α x : ℕ)` equals the
  cardinality of `{i | (α i).castSucc < x}`.
* `SimplexCategory.II.map'_le_castSucc_iff`:
  `SimplexCategory.II.map' α x ≤ y.castSucc ↔ x ≤ (α y).castSucc`, showing that
  `SimplexCategory.II.map' α` is left adjoint to `α` across the `castSucc` embedding.
* `SimplexCategory.II_map_unop_toOrderHom_apply`:
  `(SimplexCategory.II.map α).unop.toOrderHom t = SimplexCategory.II.map' α.toOrderHom t`.
-/

public section

namespace SimplexCategory.II

/-- Cut-counting formula for `SimplexCategory.II.map'`: for `α : Fin (k + 1) →o Fin (m + 1)` and
cut `x : Fin (m + 2)`, `(II.map' α x : ℕ)` counts the indices `i` with `(α i).castSucc < x`. -/
theorem val_map'_eq_card {k m : ℕ} (α : Fin (k + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    (map' α x : ℕ) = (Finset.univ.filter fun i : Fin (k + 1) ↦ (α i).castSucc < x).card := by
  obtain ⟨y, hy⟩ | hx := Fin.eq_castSucc_or_eq_last (map' α x)
  · rw [hy, Fin.val_castSucc]
    rw [map'_eq_castSucc_iff] at hy
    have hfilt : Finset.univ.filter (fun i : Fin (k + 1) ↦ (α i).castSucc < x) =
        Finset.Iio y := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
      refine ⟨fun hi ↦ ?_, fun hi ↦ hy.2 i hi⟩
      by_contra hnot
      have hle : y ≤ i := Fin.le_def.mpr (not_lt.mp hnot)
      exact hi.not_ge (hy.1.trans (Fin.castSucc_le_castSucc_iff.mpr (α.monotone hle)))
    rw [hfilt, Fin.card_Iio]
  · rw [hx, Fin.val_last]
    rw [map'_eq_last_iff] at hx
    rw [Finset.filter_eq_self.mpr (fun i _ ↦ hx i), Finset.card_univ, Fintype.card_fin]

/-- Galois characterization of `SimplexCategory.II.map'`:
`II.map' α x ≤ y.castSucc ↔ x ≤ (α y).castSucc`. -/
theorem map'_le_castSucc_iff {k m : ℕ} (α : Fin (k + 1) →o Fin (m + 1)) (x : Fin (m + 2))
    (y : Fin (k + 1)) :
    map' α x ≤ y.castSucc ↔ x ≤ (α y).castSucc := by
  constructor
  · intro h
    have hmem := Finset.min'_mem (finset α x) (nonempty_finset α x)
    rcases (mem_finset_iff α x (map' α x)).mp hmem with hlast | ⟨hne, hx⟩
    · exact absurd (hlast ▸ h) (Fin.castSucc_lt_last y).not_ge
    · have hle : (map' α x).castPred hne ≤ y :=
        Fin.castSucc_le_castSucc_iff.mp (by simpa [Fin.castSucc_castPred] using h)
      exact hx.trans (Fin.castSucc_le_castSucc_iff.mpr (α.monotone hle))
  · intro h
    exact Finset.min'_le (finset α x) y.castSucc ((castSucc_mem_finset_iff α x y).mpr h)

end SimplexCategory.II

namespace SimplexCategory

/-- Underlying monotone-map evaluation of `(SimplexCategory.II.map α).unop`. -/
@[simp]
theorem II_map_unop_toOrderHom_apply {x y : SimplexCategory} (α : x ⟶ y) (t : Fin (y.len + 2)) :
    (II.map α).unop.toOrderHom t = II.map' α.toOrderHom t :=
  rfl

end SimplexCategory
