/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Entries of Cartan matrices

An entry equal to `-1` in the generalized type-`E` Cartan matrix has distinct row and
column indices. This supplies the distinctness hypothesis for adjacent-root Serre relations.
The type-`B` entry characterizations identify the oriented double edge and consecutive nodes.
The exponents of the higher Serre relations of type `G₂` are `0`, `3`, `1` and `0`
(`CartanMatrix.toNat_neg_G₂`).
-/

public section

namespace CartanMatrix

/-- The unique double entry in the type-B Cartan matrix is the oriented last edge. -/
lemma B_apply_eq_neg_two_iff {n : ℕ} (i j : Fin n) :
    B n i j = -2 ↔ i.val + 2 = n ∧ j.val + 1 = n := by
  simp only [B, Matrix.of_apply]
  split_ifs <;> simp_all <;> omega

/-- Negative entries in the type-B Cartan matrix are exactly consecutive pairs of indices. -/
lemma B_apply_neg_iff {n : ℕ} (i j : Fin n) :
    B n i j < 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- Nodes joined by an entry `-1` in the type-`E` Cartan matrix are distinct, in every rank. -/
theorem E_ne_of_eq_neg_one {n : ℕ} {i j : Fin n} (hij : E n i j = -1) : i ≠ j := by
  rintro rfl
  exact (by decide : (2 : ℤ) ≠ -1) ((E_diag n i).symm.trans hij)

/-- The exponents `-CMᵢⱼ` of the higher Serre relations of type `G₂` are `0`, `3`, `1` and `0`. -/
theorem toNat_neg_G₂ : (-G₂ 0 0).toNat = 0 ∧ (-G₂ 0 1).toNat = 3 ∧
    (-G₂ 1 0).toNat = 1 ∧ (-G₂ 1 1).toNat = 0 := by
  decide

end CartanMatrix
