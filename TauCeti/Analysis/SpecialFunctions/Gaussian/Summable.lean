/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Summability of real Gaussian series over the integers

The centred Gaussian `n ↦ exp (a n²)` is summable over `n ∈ ℤ` if and only if `a < 0`: for `a < 0`
its tails on `ℕ` and `-ℕ` are dominated by the geometric series `exp (a n)` via
`Real.summable_exp_nat_mul_of_ge`, whereas for `a ≥ 0` every term is at least `1`.

## Main declarations

* `TauCeti.summable_exp_mul_sq_iff`: `∑_{n ∈ ℤ} exp (a n²)` converges if and only if `a < 0`.
* `TauCeti.summable_exp_neg_mul_sq_iff`, `TauCeti.summable_exp_neg_mul_sq`: `∑_{n ∈ ℤ} exp (-a n²)`
  converges if and only if `0 < a`.
-/

public section

open Filter

namespace TauCeti

/-- A real Gaussian `n ↦ exp (a n²)` is summable over `ℤ` if and only if `a < 0`. -/
@[simp]
theorem summable_exp_mul_sq_iff {a : ℝ} :
    (Summable fun n : ℤ ↦ Real.exp (a * (n : ℝ) ^ 2)) ↔ a < 0 := by
  refine ⟨fun h ↦ ?_, fun ha ↦ ?_⟩
  · by_contra! ha
    have ht := (h.comp_injective (Nat.cast_injective (R := ℤ))).tendsto_atTop_zero
    have h10 : (1 : ℝ) ≤ 0 :=
      ge_of_tendsto' ht fun _ ↦ Real.one_le_exp (mul_nonneg ha (sq_nonneg _))
    linarith
  · have hnat : Summable fun n : ℕ ↦ Real.exp (a * (n : ℝ) ^ 2) :=
      Real.summable_exp_nat_mul_of_ge ha fun n ↦ by exact_mod_cast Nat.le_self_pow two_ne_zero n
    exact Summable.of_nat_of_neg (by simpa using hnat) (by simpa using hnat)

/-- A real Gaussian `n ↦ exp (-a n²)` is summable over `ℤ` if and only if `0 < a`. -/
theorem summable_exp_neg_mul_sq_iff {a : ℝ} :
    (Summable fun n : ℤ ↦ Real.exp (-a * (n : ℝ) ^ 2)) ↔ 0 < a := by
  rw [summable_exp_mul_sq_iff, neg_lt_zero]

/-- For `0 < a`, the real Gaussian series `∑_{n ∈ ℤ} exp (-a n²)` converges. -/
theorem summable_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℤ ↦ Real.exp (-a * (n : ℝ) ^ 2) :=
  summable_exp_neg_mul_sq_iff.mpr ha

end TauCeti
