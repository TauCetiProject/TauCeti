/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.MeanInequalities

/-!
# Square sums over overlapping windows in `ℝ≥0∞`

For `L : ℕ`, the windows `[j + 1 - L, j + L)` each contain at most `2 L` indices, and each index
lies in at most `2 L` of them. Hence summing the squares of the window sums of a family
`c : ℕ → ℝ≥0∞` costs at most a factor `(2 L)²` over the sum of the squares
(`ENNReal.sum_sq_sum_Ico_le`). Such bounded-overlap estimates compare a square function built
from enlarged Littlewood–Paley pieces with the square function of the pieces themselves.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- **Bounded overlap of the windows.** Each window `[j + 1 - L, j + L)` has at most `2 L`
indices, and each index lies in at most `2 L` windows, so
`∑_{j ≤ n} (∑_{j + 1 - L ≤ k < j + L} cₖ)² ≤ (2 L)² ∑ₖ cₖ²`. -/
theorem sum_sq_sum_Ico_le (L n : ℕ) (c : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.range (n + 1), (∑ k ∈ Finset.Ico (j + 1 - L) (j + L), c k) ^ 2 ≤
      (2 * L) ^ 2 * ∑' k, c k ^ 2 := by
  have hcard : ∀ k, ((Finset.Ico (k + 1 - L) (k + L)).card : ℝ≥0∞) ≤ 2 * L := fun k ↦ by
    rw [Nat.card_Ico]
    exact_mod_cast (by omega : k + L - (k + 1 - L) ≤ 2 * L)
  calc ∑ j ∈ Finset.range (n + 1), (∑ k ∈ Finset.Ico (j + 1 - L) (j + L), c k) ^ 2
      ≤ ∑ j ∈ Finset.range (n + 1), 2 * L * ∑ k ∈ Finset.Ico (j + 1 - L) (j + L), c k ^ 2 := by
        gcongr with j
        have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.Ico (j + 1 - L) (j + L))
          (f := c) one_le_two
        norm_num only [ENNReal.rpow_two, ENNReal.rpow_one] at h
        exact h.trans (by gcongr; exact hcard j)
    _ = 2 * L * ∑ k ∈ Finset.range (n + L),
          ∑ j ∈ (Finset.range (n + 1)).filter (fun j ↦ k ∈ Finset.Ico (j + 1 - L) (j + L)),
            c k ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        refine Finset.sum_comm' fun j k ↦ ?_
        simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]
        omega
    _ ≤ 2 * L * ∑ k ∈ Finset.range (n + L), 2 * L * c k ^ 2 := by
        gcongr with k
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        refine le_trans ?_ (hcard k)
        gcongr
        intro j
        simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]
        omega
    _ ≤ (2 * L) ^ 2 * ∑' k, c k ^ 2 := by
        rw [← Finset.mul_sum, ← mul_assoc, ← sq]
        gcongr
        exact _root_.sum_le_tsum _

end ENNReal
