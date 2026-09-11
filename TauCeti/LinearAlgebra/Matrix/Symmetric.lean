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

* `Matrix.IsSymm.even_sum_mul_diag_iff_even_dotProduct_mulVec`: if `A` is a symmetric integer
  matrix then `∑ᵢ mᵢ aᵢᵢ` is even if and only if `mᵀ A m` is.
* `Matrix.IsSymm.even_sum_mul_diag_of_dotProduct_mulVec_eq_zero`: if `A` is a symmetric integer
  matrix and `mᵀ A m = 0`, then `∑ᵢ mᵢ aᵢᵢ` is even.
-/

public section

namespace Matrix

open Finset

/-- If `A` is a symmetric integer matrix and `m` is an integer vector, then `∑ᵢ mᵢ aᵢᵢ` has the
same parity as the quadratic form `mᵀ A m`. The individual terms `mᵢ aᵢᵢ` need not be even. -/
theorem IsSymm.even_sum_mul_diag_iff_even_dotProduct_mulVec {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℤ} (hA : A.IsSymm) (m : ι → ℤ) :
    Even (∑ i, m i * A i i) ↔ Even (m ⬝ᵥ A *ᵥ m) := by
  classical
  have hoff : Even (∑ i, ∑ j ∈ univ.erase i, m i * m j * A i j) :=
    TauCeti.even_sum_sum_erase univ fun i _ j _ ↦ by rw [hA.apply i j]; ring
  have hcorr : Even (∑ i, (m i * m i * A i i - m i * A i i)) := by
    rw [even_iff_two_dvd]
    refine Finset.dvd_sum fun i _ ↦ ?_
    obtain ⟨c, hc⟩ := (Int.even_mul_pred_self (m i)).two_dvd
    exact ⟨c * A i i, by linear_combination A i i * hc⟩
  have htotal : m ⬝ᵥ A *ᵥ m = ∑ i, ∑ j, m i * m j * A i j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- Splitting off the diagonal, `mᵀ A m` is `∑ᵢ mᵢ aᵢᵢ` plus the two even sums above.
  have hsum : m ⬝ᵥ A *ᵥ m = (∑ i, m i * A i i) +
      ((∑ i, (m i * m i * A i i - m i * A i i)) +
        ∑ i, ∑ j ∈ univ.erase i, m i * m j * A i j) := by
    have hrow (i : ι) : ∑ j, m i * m j * A i j = m i * A i i +
        ((m i * m i * A i i - m i * A i i) + ∑ j ∈ univ.erase i, m i * m j * A i j) := by
      rw [← Finset.add_sum_erase univ (fun j ↦ m i * m j * A i j) (mem_univ i)]
      ring
    rw [htotal, Finset.sum_congr rfl fun i _ ↦ hrow i, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
  rw [hsum, Int.even_add]
  exact ⟨fun h ↦ iff_of_true h (hcorr.add hoff), fun h ↦ h.mpr (hcorr.add hoff)⟩

/-- If `A` is a symmetric integer matrix and `m` is an integer vector with `mᵀ A m = 0`, then
`∑ᵢ mᵢ aᵢᵢ` is even. The individual terms `mᵢ aᵢᵢ` need not be even. -/
theorem IsSymm.even_sum_mul_diag_of_dotProduct_mulVec_eq_zero {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℤ} (hA : A.IsSymm) {m : ι → ℤ} (hm : m ⬝ᵥ A *ᵥ m = 0) :
    Even (∑ i, m i * A i i) :=
  (hA.even_sum_mul_diag_iff_even_dotProduct_mulVec m).2 (hm ▸ Even.zero)

end Matrix
