/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

import TauCeti.Data.Fin.Basic

/-!
# Faces of subintervals in the simplex category

Mathlib's `SimplexCategory.subinterval j l h : ⦋l⦌ ⟶ ⦋n⦌` is the inert map onto the vertices
`j, …, j + l`.  This file records how it interacts with the coface maps `SimplexCategory.δ`:
a face of a subinterval is again a subinterval, possibly of a face.  With `j = 0` the
subinterval is the front face of a simplex and with `j + l = n` it is the back face, so these are
the identities behind the Alexander–Whitney formula and its compatibility with the simplicial
boundary.  It also records that a subinterval of a subinterval is a subinterval and that the
front face of full length is the identity, the identities behind associativity and the unit laws
of the cup product.  Finally, a subinterval containing two consecutive vertices is not injective
after the codegeneracy collapsing them (`SimplexCategory.not_mono_subinterval_comp_σ`): a front or
back face of a degenerate simplex is degenerate as soon as it contains the collapsed edge, which
is why the Alexander–Whitney map preserves degenerate chains.
-/

public section

open CategoryTheory Simplicial

namespace SimplexCategory

@[simp]
lemma val_subinterval_toOrderHom_apply {n : ℕ} (j l : ℕ) (hjl : j + l ≤ n) (i : Fin (l + 1)) :
    ((subinterval j l hjl).toOrderHom i : ℕ) = i + j := (rfl)

/-- A subinterval containing two consecutive vertices `i` and `i + 1` is not injective after the
codegeneracy `σ i`, which identifies them. -/
lemma not_mono_subinterval_comp_σ {n j l : ℕ} (h : j + l ≤ n + 1) (i : Fin (n + 1))
    (hji : j ≤ i) (hil : (i : ℕ) < j + l) : ¬ Mono (subinterval j l h ≫ σ i) := by
  rw [mono_iff_injective]
  intro hinj
  have h₁ : (subinterval j l h).toOrderHom ⟨i - j, by dsimp; omega⟩ = i.castSucc := by
    ext; simp; omega
  have h₂ : (subinterval j l h).toOrderHom ⟨i - j + 1, by dsimp; omega⟩ = i.succ := by
    ext; simp; omega
  have := @hinj ⟨i - j, by dsimp; omega⟩ ⟨i - j + 1, by dsimp; omega⟩ (by simp [σ, h₁, h₂])
  simp [Fin.ext_iff] at this

end SimplexCategory

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-- The coface map `δ k` fixes the vertices before `k` and shifts the others up by one.

This is `SimplexCategory.δ_apply` read under `Fin.val` with `Fin.val_succAbove`.  It is stated for
the underlying monotone map `(δ k).toOrderHom`, the form the face proofs below reach after `ext`;
`δ_apply` is stated for the concrete-category application `δ k x`, which is by definition
`(δ k).toOrderHom x` (the concrete-category structure of `SimplexCategory` has
`hom := Hom.toOrderHom`). -/
private lemma val_δ_toOrderHom_apply {n : ℕ} (k : Fin (n + 2)) (x : Fin (n + 1)) :
    ((δ k).toOrderHom x : ℕ) = if (x : ℕ) < k then (x : ℕ) else x + 1 := by
  -- The concrete-category application `δ k x` of `δ_apply` unfolds to `(δ k).toOrderHom x`.
  rw [show (δ k).toOrderHom x = k.succAbove x from δ_apply k x, Fin.val_succAbove]

/-- A face of a subinterval is a subinterval of the corresponding face: the `i`-th face of the
subinterval `j, …, j + q + 1`, which omits its vertex `k = j + i`, is the subinterval `j, …, j + q`
followed by the coface map skipping `k`. -/
lemma δ_comp_subinterval {n j q : ℕ} (i : Fin (q + 2)) (k : Fin (n + 2))
    (hik : j + (i : ℕ) = k) (h : j + (q + 1) ≤ n + 1) :
    δ i ≫ subinterval j (q + 1) h = subinterval j q (by omega) ≫ δ k := by
  ext l : 3
  rw [Fin.ext_iff]
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, val_δ_toOrderHom_apply,
    val_subinterval_toOrderHom_apply, ← hik, add_comm j, Nat.add_lt_add_iff_right]
  split_ifs <;> omega

/-- Deleting a vertex before a subinterval shifts the subinterval. -/
@[simp]
lemma subinterval_comp_δ_of_le {n j q : ℕ} (k : Fin (n + 2)) (hk : (k : ℕ) ≤ j)
    (h : j + q ≤ n) :
    subinterval j q h ≫ δ k = subinterval (j + 1) q (by omega) := by
  ext l : 3
  rw [Fin.ext_iff]
  have hnot : ¬(l : ℕ) + j < k := by omega
  simp [val_δ_toOrderHom_apply, hnot]
  omega

/-- Deleting a vertex after a subinterval does not change it. -/
@[simp]
lemma subinterval_comp_δ_of_lt {n j q : ℕ} (k : Fin (n + 2)) (hk : j + q < k)
    (h : j + q ≤ n) :
    subinterval j q h ≫ δ k = subinterval j q (by omega) := by
  ext l : 3
  rw [Fin.ext_iff]
  simp [val_δ_toOrderHom_apply]
  omega

/-- The last face of the subinterval `j, …, j + q + 1` is the subinterval `j, …, j + q`. -/
@[simp]
lemma δ_last_comp_subinterval {n j q : ℕ} (h : j + (q + 1) ≤ n) :
    δ (Fin.last (q + 1)) ≫ subinterval j (q + 1) h = subinterval j q (by omega) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := n) (by omega)
  rw [δ_comp_subinterval _ ⟨j + q + 1, by omega⟩ (by simp; omega),
    subinterval_comp_δ_of_lt _ (by simp)]

/-- The zeroth face of the subinterval starting at `j` is the subinterval starting at `j + 1`. -/
@[simp]
lemma δ_zero_comp_subinterval {n j q : ℕ} (h : j + (q + 1) ≤ n) :
    δ 0 ≫ subinterval j (q + 1) h = subinterval (j + 1) q (by omega) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := n) (by omega)
  rw [δ_comp_subinterval _ ⟨j, by omega⟩ (by simp), subinterval_comp_δ_of_le (j := j) _ le_rfl]

/-- A subinterval of a subinterval is a subinterval: the vertices `i, …, i + l` of the
subinterval `j, …, j + m` are the vertices `j + i, …, j + i + l`. -/
lemma subinterval_comp_subinterval {n m : ℕ} (i l j j' : ℕ) (h : i + l ≤ m) (h' : j + m ≤ n)
    (hj' : j + i = j') :
    subinterval i l h ≫ subinterval j m h' = subinterval j' l (by omega) := by
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

end TauCeti.SimplexCategory
