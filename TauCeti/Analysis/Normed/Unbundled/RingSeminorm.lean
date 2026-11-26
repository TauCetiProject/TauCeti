/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# Additional lemmas on ring seminorms

This file extends `Mathlib.Analysis.Normed.Unbundled.RingSeminorm` with general estimates for
`RingSeminorm`.

## Main results

* `RingSeminorm.pow_add_le_of_forall_pow_le`: geometric upper bounds on `μ (x ^ k)` and
  `μ (y ^ k)` yield a geometric upper bound on `μ ((x + y) ^ n)`.
-/

public section

namespace RingSeminorm

variable {R : Type*} [CommRing R]

/-- Binomial power bound: geometric upper bounds on `μ (x ^ k)` and `μ (y ^ k)` yield a
geometric upper bound on `μ ((x + y) ^ n)`. -/
theorem pow_add_le_of_forall_pow_le (μ : RingSeminorm R) {x y : R} {Cx Cy a b : ℝ}
    (hCx : ∀ k, μ (x ^ k) ≤ Cx * a ^ k) (hCy : ∀ k, μ (y ^ k) ≤ Cy * b ^ k) (n : ℕ) :
    μ ((x + y) ^ n) ≤ Cx * Cy * (a + b) ^ n := by
  calc μ ((x + y) ^ n)
      = μ (∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) * n.choose k) := by rw [add_pow]
    _ ≤ ∑ k ∈ Finset.range (n + 1), μ (x ^ k * y ^ (n - k) * n.choose k) :=
        Finset.map_sum_le_sum μ (Finset.range (n + 1)) _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (μ (x ^ k) * μ (y ^ (n - k))) := by
        gcongr with k
        have hchoose : μ (x ^ k * y ^ (n - k) * n.choose k) ≤
            (n.choose k : ℝ) * μ (x ^ k * y ^ (n - k)) := by
          simpa only [Finset.sum_const, Finset.card_range, ← nsmul_eq_mul', nsmul_eq_mul] using
            Finset.map_sum_le_sum μ (Finset.range (n.choose k)) (fun _ ↦ x ^ k * y ^ (n - k))
        exact hchoose.trans
          (mul_le_mul_of_nonneg_left (map_mul_le_mul μ _ _) (Nat.cast_nonneg _))
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((Cx * a ^ k) * (Cy * b ^ (n - k))) :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left
          (mul_le_mul (hCx k) (hCy (n - k)) (apply_nonneg μ _) ((apply_nonneg μ _).trans (hCx k)))
          (Nat.cast_nonneg _)
    _ = Cx * Cy * ∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k) * n.choose k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
    _ = Cx * Cy * (a + b) ^ n := by rw [← add_pow]

end RingSeminorm
