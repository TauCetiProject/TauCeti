/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Products of matrices with replaced columns

`Matrix.updateCol_mul_updateCol_apply_self` computes the replaced column of a product of matrices
with the same column replaced, when the new column of the right factor is `1` at that index and
supported on a set of rows together with it.
-/

public section

namespace Matrix

/-- The column `a` of a product of matrices with replaced columns `a`, when the new column `y` of
the right factor is `1` at `a` and supported on `S ∪ {a}`. -/
theorem updateCol_mul_updateCol_apply_self {l p T : Type*} [NonAssocSemiring T] [Fintype p]
    [DecidableEq p] {J : Matrix l p T} {H : Matrix p p T} (a : p) (x : l → T) (y : p → T)
    (S : Finset p) (haS : a ∉ S) (hya : y a = 1) (hy : ∀ k, k ∉ S → k ≠ a → y k = 0) (i : l) :
    (J.updateCol a x * H.updateCol a y) i a = x i + ∑ k ∈ S, J i k * y k := by
  simp only [Matrix.mul_apply, updateCol_self, updateCol_apply]
  have hterm (k : p) : (if k = a then x i else J i k) * y k =
      (if k = a then x i else 0) + if k ∈ S then J i k * y k else 0 := by
    by_cases hka : k = a
    · subst hka
      simp [hya, haS]
    · by_cases hk : k ∈ S
      · simp [hka, hk]
      · simp [hka, hk, hy k hk hka]
  rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp

end Matrix
