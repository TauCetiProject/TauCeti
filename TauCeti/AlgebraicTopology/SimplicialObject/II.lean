/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.II

/-!
# Cut-counting and Galois properties of `SimplexCategory.II`

This file supplements `Mathlib.AlgebraicTopology.SimplicialObject.II` with the Galois condition,
cut-counting formula, and evaluation lemma for Gabriel–Zisman's cut map
`SimplexCategory.II.map'` and `SimplexCategory.II.map`:

* `SimplexCategory.II.castSucc_lt_map'_iff`: `i.castSucc < map' f x ↔ (f i).castSucc < x`.
* `SimplexCategory.II.val_map'_eq_card`: `(SimplexCategory.II.map' α x : ℕ)` equals the
  cardinality of `{i | (α i).castSucc < x}`.
* `SimplexCategory.II_map_unop_toOrderHom_apply`:
  `(SimplexCategory.II.map α).unop.toOrderHom t = SimplexCategory.II.map' α.toOrderHom t`.
-/

public section

namespace SimplexCategory.II

/-- The Galois condition characterizing `II.map' f`: the elements below `II.map' f x` are the
`i` with `f i < x`. -/
@[simp]
lemma castSucc_lt_map'_iff {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2))
    (i : Fin (n + 1)) : i.castSucc < map' f x ↔ (f i).castSucc < x := by
  constructor
  · intro h
    by_contra! hx
    rw [map'] at h
    exact h.not_ge (Finset.min'_le _ _ ((castSucc_mem_finset_iff f x i).2 hx))
  · intro h
    by_contra! hle
    obtain ⟨y, hy⟩ := Fin.eq_castSucc_of_ne_last (hle.trans_lt (Fin.castSucc_lt_last i)).ne
    rw [← hy, Fin.castSucc_le_castSucc_iff] at hle
    exact h.not_ge (((map'_eq_castSucc_iff f x y).1 hy.symm).1.trans
      (Fin.castSucc_le_castSucc_iff.2 (f.monotone hle)))

/-- Cut-counting formula for `SimplexCategory.II.map'`: for `α : Fin (k + 1) →o Fin (m + 1)` and
cut `x : Fin (m + 2)`, `(II.map' α x : ℕ)` counts the indices `i` with `(α i).castSucc < x`. -/
theorem val_map'_eq_card {k m : ℕ} (α : Fin (k + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    (map' α x : ℕ) = (Finset.univ.filter fun i : Fin (k + 1) ↦ (α i).castSucc < x).card := by
  rw [← Finset.card_range (map' α x : ℕ)]
  symm
  refine Finset.card_bij (fun i _ ↦ (i : ℕ)) (fun i hi ↦ ?_) (fun _ _ _ _ h ↦ Fin.ext h)
    fun j hj ↦ ⟨⟨j, (Finset.mem_range.mp hj).trans_le (Nat.lt_succ_iff.mp (map' α x).isLt)⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (castSucc_lt_map'_iff α x _).mp (Fin.lt_def.mpr (Finset.mem_range.mp hj))⟩, rfl⟩
  exact Finset.mem_range.mpr (Fin.lt_def.mp ((castSucc_lt_map'_iff α x i).mpr
    (Finset.mem_filter.mp hi).2))

end SimplexCategory.II

namespace SimplexCategory

/-- Underlying monotone-map evaluation of `(SimplexCategory.II.map α).unop`. -/
@[simp]
theorem II_map_unop_toOrderHom_apply {x y : SimplexCategory} (α : x ⟶ y) (t : Fin (y.len + 2)) :
    (II.map α).unop.toOrderHom t = II.map' α.toOrderHom t :=
  rfl

end SimplexCategory
