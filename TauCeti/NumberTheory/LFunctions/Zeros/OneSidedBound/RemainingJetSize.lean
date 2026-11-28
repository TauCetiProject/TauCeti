/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.JetSize
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Bounds

/-!
# Bounds for jet sizes after Legendre prime sums

The bound `TauCeti.sum_prime_weight_mul_max_mem_Icc` controls the cost subtracted from each
jet by its order times the logarithmic cutoff. The theorem
`TauCeti.OneSidedBound.directionAmount_mem_Icc_of_primeWeight` applies this estimate to
the direction amount. Its lower bound uses just the directions of large order, while its
upper bound uses the jet-size estimate in every direction.

The direction estimate follows `New.Data.directionAmount_mem_Icc` in
`grh/src/New/Reduction/PrimeSums.lean` of lsernau/grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC)
at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Finset Real

namespace TauCeti.OneSidedBound

/-- Bound the direction amount formed from the actual unrestricted Legendre prime sums.
The orders are at most `b`, with order at least `b` on the distinguished directions `t`.
The cutoff ratio limits contributing prime powers to `X`. The scale `c` pays for both the
prime-sum bound `4 log X` and the large-direction contribution `log b`, and `c ≤ 23 log b`.
Here `T` is any lower bound on `t.card * log b`. -/
theorem directionAmount_mem_Icc_of_primeWeight {ι : Type*} (d : ℕ) [Fact d.Prime]
    {s t : Finset ι} {κ : ι → ℕ} {N b : ℕ} {c T X : ℝ} (next : ι → ℕ → ι)
    (ht : t ⊆ s) (hX : 1 ≤ X)
    (hc₁ : log b + 4 * log X ≤ c) (hc₂ : c ≤ 23 * log b)
    (hκ : ∀ i ∈ s, (κ i : ℝ) ≤ b) (htκ : ∀ i ∈ t, (b : ℝ) ≤ κ i)
    (hT : T ≤ t.card * log b)
    (hcap : ∀ i ∈ s, ∀ n ∈ Ioc 0 N, (κ i : ℝ) ≤ X * κ (next i n)) :
    directionAmount s κ c (fun i ↦
      ∑ n ∈ Ioc 0 N, primeWeight d 1 n * max (κ i / (n : ℝ) - κ (next i n)) 0) ∈
      Set.Icc (b * T) (25 * s.card * b * log b) := by
  let P (i : ι) := ∑ n ∈ Ioc 0 N, primeWeight d 1 n * max (κ i / (n : ℝ) - κ (next i n)) 0
  have hP (i : ι) (hi : i ∈ s) : P i ∈ Set.Icc 0 (4 * (κ i : ℝ) * log X) :=
    sum_prime_weight_mul_max_mem_Icc (Nat.cast_nonneg _) hX
      (fun n _ ↦ ⟨primeWeight_nonneg d 1 n, primeWeight_le_two_mul_vonMangoldt d 1 n⟩)
      (hcap i hi)
  have hb : 0 ≤ log b := log_natCast_nonneg b
  have hscale : log b ≤ c - 4 * log X := by linarith
  have hprime (i : ι) (hi : i ∈ s) : P i ≤ (κ i : ℝ) * (4 * log X) := by
    simpa only [← mul_assoc, mul_comm (κ i : ℝ) 4] using (hP i hi).2
  exact ⟨mul_le_directionAmount ht (Nat.cast_nonneg b)
      (max_le (hb.trans hscale) hscale) htκ hT hprime,
    directionAmount_le hb hc₂ hκ (fun i hi ↦ (hP i hi).1)⟩

end TauCeti.OneSidedBound
