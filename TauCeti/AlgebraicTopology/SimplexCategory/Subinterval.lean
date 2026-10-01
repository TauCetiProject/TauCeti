/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Faces of subintervals in the simplex category

Mathlib's `SimplexCategory.subinterval j l h : ⦋l⦌ ⟶ ⦋n⦌` is the inert map onto the vertices
`j, …, j + l`.  This file records how it interacts with the coface maps `SimplexCategory.δ`:
a face of a subinterval is again a subinterval, possibly of a face.  With `j = 0` the
subinterval is the front face of a simplex and with `j + l = n` it is the back face, so these are
the identities behind the Alexander–Whitney formula and its compatibility with the simplicial
boundary.  It also records that a subinterval of a subinterval is a subinterval and that the
front face of full length is the identity, the identities behind associativity and the unit laws
of the cup product.
-/

public section

open CategoryTheory Simplicial

namespace SimplexCategory

@[simp]
lemma val_subinterval_toOrderHom_apply {n : ℕ} (j l : ℕ) (hjl : j + l ≤ n) (i : Fin (l + 1)) :
    ((subinterval j l hjl).toOrderHom i : ℕ) = i + j := (rfl)

/-- A face of a front face is the front face of the corresponding face. -/
lemma δ_comp_subinterval_zero {n p : ℕ} (i : Fin (p + 2)) (k : Fin (n + 2))
    (hik : (i : ℕ) = k) (h : 0 + (p + 1) ≤ n + 1) :
    δ i ≫ subinterval 0 (p + 1) h = subinterval 0 p (by omega) ≫ δ k := by
  ext j : 3
  rw [Fin.ext_iff]
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, δ, mkHom, Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    Fin.succAbove, Fin.lt_def, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ,
    val_subinterval_toOrderHom_apply]
  split_ifs <;> omega

/-- The last face of the front `(p + 1)`-face is the front `p`-face. -/
@[simp]
lemma δ_last_comp_subinterval_zero {n p : ℕ} (h : 0 + (p + 1) ≤ n) :
    δ (Fin.last (p + 1)) ≫ subinterval 0 (p + 1) h = subinterval 0 p (by omega) := by
  ext j : 3
  rw [Fin.ext_iff]
  simp [δ]

/-- The zeroth face of the subinterval starting at `j` is the subinterval starting at `j + 1`. -/
@[simp]
lemma δ_zero_comp_subinterval {n j q : ℕ} (h : j + (q + 1) ≤ n) :
    δ 0 ≫ subinterval j (q + 1) h = subinterval (j + 1) q (by omega) := by
  ext i : 3
  rw [Fin.ext_iff]
  simp [δ]
  omega

/-- A positive face of a subinterval is the subinterval of the corresponding face. -/
lemma δ_succ_comp_subinterval {n j q : ℕ} (i : Fin (q + 1)) (k : Fin (n + 2))
    (hik : j + 1 + (i : ℕ) = k) (h : j + (q + 1) ≤ n + 1) :
    δ i.succ ≫ subinterval j (q + 1) h = subinterval j q (by omega) ≫ δ k := by
  ext l : 3
  rw [Fin.ext_iff]
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, δ, mkHom, Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    Fin.succAbove, Fin.lt_def, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ,
    val_subinterval_toOrderHom_apply]
  split_ifs <;> omega

/-- Deleting a vertex before a subinterval shifts the subinterval. -/
@[simp]
lemma subinterval_comp_δ_of_le {n j q : ℕ} (k : Fin (n + 2)) (hk : (k : ℕ) ≤ j)
    (h : j + q ≤ n) :
    subinterval j q h ≫ δ k = subinterval (j + 1) q (by omega) := by
  ext l : 3
  rw [Fin.ext_iff]
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, δ, mkHom, Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    Fin.succAbove, Fin.lt_def, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ,
    val_subinterval_toOrderHom_apply]
  split_ifs <;> omega

/-- Deleting a vertex after a front face does not change it. -/
@[simp]
lemma subinterval_zero_comp_δ_of_lt {n p : ℕ} (k : Fin (n + 2)) (hk : p < (k : ℕ))
    (h : 0 + p ≤ n) :
    subinterval 0 p h ≫ δ k = subinterval 0 p (by omega) := by
  ext l : 3
  rw [Fin.ext_iff]
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, δ, mkHom, Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    Fin.succAbove, Fin.lt_def, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ,
    val_subinterval_toOrderHom_apply]
  split_ifs <;> omega

/-- A subinterval of a subinterval is a subinterval: the vertices `i, …, i + a` of the
subinterval `j, …, j + m` are the vertices `j + i, …, j + i + a`. -/
lemma subinterval_comp_subinterval {n m : ℕ} (i a j l : ℕ) (h : i + a ≤ m) (h' : j + m ≤ n)
    (hl : j + i = l) :
    subinterval i a h ≫ subinterval j m h' = subinterval l a (by omega) := by
  ext v : 3
  rw [Fin.ext_iff]
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    val_subinterval_toOrderHom_apply]
  omega

/-- The front face of full length is the identity. -/
@[simp]
lemma subinterval_zero_eq_id {n : ℕ} (h : 0 + n ≤ n) : subinterval 0 n h = 𝟙 ⦋n⦌ := by
  ext v : 3
  rw [Fin.ext_iff]
  simp

end SimplexCategory
