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

/-- A face of a subinterval is a subinterval of the corresponding face: the `i`-th face of the
subinterval `j, …, j + q + 1`, which omits its vertex `k = j + i`, is the subinterval `j, …, j + q`
followed by the coface map skipping `k`. -/
lemma δ_comp_subinterval {n j q : ℕ} (i : Fin (q + 2)) (k : Fin (n + 2))
    (hik : j + (i : ℕ) = k) (h : j + (q + 1) ≤ n + 1) :
    δ i ≫ subinterval j (q + 1) h = subinterval j q (by omega) ≫ δ k := by
  ext l : 3
  rw [Fin.ext_iff]
  simp [δ, Fin.succAbove, Fin.lt_def, apply_ite Fin.val]
  split_ifs <;> omega

/-- The last face of the subinterval `j, …, j + q + 1` is the subinterval `j, …, j + q`. -/
@[simp]
lemma δ_last_comp_subinterval {n j q : ℕ} (h : j + (q + 1) ≤ n) :
    δ (Fin.last (q + 1)) ≫ subinterval j (q + 1) h = subinterval j q (by omega) := by
  ext l : 3
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

/-- Deleting a vertex before a subinterval shifts the subinterval. -/
@[simp]
lemma subinterval_comp_δ_of_le {n j q : ℕ} (k : Fin (n + 2)) (hk : (k : ℕ) ≤ j)
    (h : j + q ≤ n) :
    subinterval j q h ≫ δ k = subinterval (j + 1) q (by omega) := by
  ext l : 3
  rw [Fin.ext_iff]
  simp [δ, Fin.succAbove, Fin.lt_def, apply_ite Fin.val]
  split_ifs <;> omega

/-- Deleting a vertex after a subinterval does not change it. -/
@[simp]
lemma subinterval_comp_δ_of_lt {n j q : ℕ} (k : Fin (n + 2)) (hk : j + q < k)
    (h : j + q ≤ n) :
    subinterval j q h ≫ δ k = subinterval j q (by omega) := by
  ext l : 3
  rw [Fin.ext_iff]
  simp [δ, Fin.succAbove, Fin.lt_def, apply_ite Fin.val]
  omega

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
