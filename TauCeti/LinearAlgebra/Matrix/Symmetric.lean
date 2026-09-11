/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal

/-!
# Parity of the diagonal of a symmetric integer matrix

For a symmetric integer matrix `A` and an integer vector `m`, the quadratic form
`mᵀ A m = ∑ᵢⱼ mᵢ mⱼ aᵢⱼ` agrees modulo two with `∑ᵢ mᵢ aᵢᵢ`: its off-diagonal part is even
because the summand is symmetric under swapping the indices, and `mᵢ² ≡ mᵢ` modulo two. In
particular `∑ᵢ mᵢ aᵢᵢ` is even whenever `mᵀ A m = 0`, for instance whenever `A m = 0`.

## Main results

* `Matrix.IsSymm.even_sum_mul_diag_of_dotProduct_mulVec_eq_zero`: if `A` is a symmetric integer
  matrix and `mᵀ A m = 0`, then `∑ᵢ mᵢ aᵢᵢ` is even.
-/

public section

namespace Matrix

open Finset

/-- If `A` is a symmetric integer matrix and `m` is an integer vector with `mᵀ A m = 0`, then
`∑ᵢ mᵢ aᵢᵢ` is even. The individual terms `mᵢ aᵢᵢ` need not be even. -/
theorem IsSymm.even_sum_mul_diag_of_dotProduct_mulVec_eq_zero {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℤ} (hA : A.IsSymm) {m : ι → ℤ} (hm : m ⬝ᵥ A *ᵥ m = 0) :
    Even (∑ i, m i * A i i) := by
  classical
  have hoff : Even (∑ i, ∑ j ∈ univ.erase i, m i * m j * A i j) :=
    TauCeti.even_sum_sum_erase univ fun i _ j _ ↦ by rw [hA.apply i j]; ring
  have htotal : ∑ i, ∑ j, m i * m j * A i j = 0 := by
    rw [← hm]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hdiag : (2 : ℤ) ∣ ∑ i, m i * m i * A i i := by
    have hsplit : ∑ i, m i * m i * A i i = -∑ i, ∑ j ∈ univ.erase i, m i * m j * A i j := by
      rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib, ← htotal]
      exact Finset.sum_congr rfl fun i _ ↦
        Finset.add_sum_erase univ (fun j ↦ m i * m j * A i j) (mem_univ i)
    rw [hsplit]
    exact dvd_neg.2 hoff.two_dvd
  have hcorr : (2 : ℤ) ∣ ∑ i, (m i * m i * A i i - m i * A i i) := by
    refine Finset.dvd_sum fun i _ ↦ ?_
    obtain ⟨c, hc⟩ := (Int.even_mul_pred_self (m i)).two_dvd
    exact ⟨c * A i i, by linear_combination A i i * hc⟩
  have key : ∑ i, m i * A i i =
      (∑ i, m i * m i * A i i) - ∑ i, (m i * m i * A i i - m i * A i i) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [even_iff_two_dvd, key]
  exact dvd_sub hdiag hcorr

end Matrix
