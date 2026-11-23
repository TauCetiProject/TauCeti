/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.Chebyshev.PrimeTail
import TauCeti.NumberTheory.Chebyshev.WeightedPrimeMellin

/-!
# Endpoints and normalization of weighted-prime Mellin smoothing

The examples retain the dyadic term in an inclusive tail, the primality filter and integer
part of a real cutoff, and the sign and real scalar action of real and complex prime weights.
The mass and logarithmic moment at smoothing parameter `2` check the outer normalization of
the Mellin integral.
-/

open TauCeti MeasureTheory Real Set

namespace TauCeti.WeightedPrimeMellinExamples

/-- The prime `2` occurs once when an inclusive tail is decomposed into its endpoint and a
strict tail. -/
example :
    (∑' n : ℕ, if n.Prime ∧ (2 : ℝ) ≤ n then log n / (n : ℝ) ^ 2 else 0) =
      log 2 / 4 + ∑' n : ℕ, if n.Prime ∧ (2 : ℝ) < n then log n / (n : ℝ) ^ 2 else 0 := by
  have htwo : (2 : ℝ) ^ 2 = 4 := by norm_num
  simpa only [Nat.cast_ofNat, htwo] using
    tsum_prime_log_div_sq_ge_eq Nat.prime_two

/-- There are no primes at cutoff one, even for complex weights. -/
example (a : ℕ → ℂ) : weightedPrimeSum a 1 = 0 := by
  exact weightedPrimeSum_eq_zero_of_lt_two a (by norm_num)

/-- The first prime contributes its logarithmic weight at the inclusive endpoint. -/
example : weightedPrimeSum (fun _ ↦ (1 : ℝ)) 2 = log 2 / 2 := by
  have hp : Nat.primesLE 2 = {2} := by decide
  norm_num [weightedPrimeSum_def, hp]

/-- The real cutoff uses its integer part, so `2.9` has exactly the same primes as `2`. -/
example (a : ℕ → ℂ) : weightedPrimeSum a (29 / 10) = weightedPrimeSum a 2 := by
  exact weightedPrimeSum_of_mem_Ico a (n := 2) (by norm_num)

/-- A composite cutoff adds no term: the weight at `4` is excluded by the prime filter. -/
example : weightedPrimeSum (fun _ ↦ (1 : ℝ)) 4 = log 2 / 2 + log 3 / 3 := by
  have hp : Nat.primesLE 4 = {2, 3} := by decide
  norm_num [weightedPrimeSum_def, hp]

/-- Complex weights use the same real scalar action and the same prime set. -/
example : weightedPrimeSum (fun _ ↦ Complex.I) 4 =
    (log 2 / 2 + log 3 / 3) • Complex.I := by
  have hp : Nat.primesLE 4 = {2, 3} := by decide
  norm_num [weightedPrimeSum_def, hp, add_smul]

/-- Arbitrary changes at `1`, `4` and `6` leave the entire prime-sum function unchanged. -/
example (a : ℕ → ℂ) (c₁ c₄ c₆ : ℂ) :
    weightedPrimeSum (Function.update (Function.update (Function.update a 1 c₁) 4 c₄) 6 c₆) =
      weightedPrimeSum a := by
  have hfour : ¬Nat.Prime 4 := by decide
  have hsix : ¬Nat.Prime 6 := by decide
  exact weightedPrimeSum_congr fun p hp ↦ by
    simp only [Function.update_of_ne hp.ne_one,
      Function.update_of_ne (fun (h : p = 4) ↦ hfour (h ▸ hp)),
      Function.update_of_ne (fun (h : p = 6) ↦ hsix (h ▸ hp))]

/-- Negating complex weights negates both the finite sum and its Mellin smoothing. -/
example (a : ℕ → ℂ) :
    weightedPrimeSum (-a) + weightedPrimeSum a = 0 ∧
    mellinWeightIntegral 2 (weightedPrimeSum (-a)) +
      mellinWeightIntegral 2 (weightedPrimeSum a) = 0 := by
  simp

/-- The smoothing is additive even though the sum of these two unit weights has norm `√2`. -/
example : mellinWeightIntegral 2 (weightedPrimeSum fun _ ↦ (1 : ℂ) + Complex.I) =
    mellinWeightIntegral 2 (weightedPrimeSum fun _ ↦ (1 : ℂ)) +
      mellinWeightIntegral 2 (weightedPrimeSum fun _ ↦ Complex.I) := by
  -- Function addition evaluates pointwise, so this specialization has weight `n ↦ 1 + I`.
  have hadd : weightedPrimeSum (fun _ ↦ (1 : ℂ) + Complex.I) =
      weightedPrimeSum (fun _ ↦ (1 : ℂ)) + weightedPrimeSum (fun _ ↦ Complex.I) :=
    weightedPrimeSum_add (fun _ ↦ (1 : ℂ)) (fun _ ↦ Complex.I)
  rw [hadd, mellinWeightIntegral_add
    (integrableOn_rpow_smul_weightedPrimeSum (a := fun _ ↦ (1 : ℂ))
      (fun _ _ ↦ by norm_num) (by norm_num : (0 : ℝ) < 2))
    (integrableOn_rpow_smul_weightedPrimeSum (a := fun _ ↦ Complex.I)
      (fun _ _ ↦ by norm_num) (by norm_num : (0 : ℝ) < 2))]

/-- At parameter two the normalized mass is one and the logarithmic moment is one half. -/
example : mellinWeightIntegral 2 (fun _ ↦ (1 : ℝ)) = 1 ∧
    mellinWeightIntegral 2 log = 1 / 2 := by
  exact ⟨mellinWeightIntegral_const (by norm_num) 1,
    by simpa using mellinWeightIntegral_log (η := 2) (by norm_num)⟩

/-- The cubic prime series with complex weights keeps the outer real factor two. -/
example : (∑' p : Nat.Primes, (log p / (p : ℝ) ^ (3 : ℝ)) • Complex.I) =
    (2 : ℝ) • ∫ t in Ioi (1 : ℝ),
      t ^ (-3 : ℝ) • weightedPrimeSum (fun _ ↦ Complex.I) t := by
  have hthree : 1 + (2 : ℝ) = 3 := by norm_num
  have hnegthree : -1 - (2 : ℝ) = -3 := by norm_num
  simpa only [mellinWeightIntegral_def, hthree, hnegthree] using
    tsum_weightedPrimeSeries (a := fun _ ↦ Complex.I) (η := 2)
      (fun _ _ ↦ by norm_num) (by norm_num)

/-- Dropping the outer factor two gives a false identity: the cubic prime series is positive.
-/
example : (∑' p : Nat.Primes, log p / (p : ℝ) ^ (3 : ℝ)) ≠
    ∫ t in Ioi (1 : ℝ), t ^ (-3 : ℝ) * weightedPrimeSum (fun _ ↦ (1 : ℝ)) t := by
  have hthree : 1 + (2 : ℝ) = 3 := by norm_num
  have hnegthree : -1 - (2 : ℝ) = -3 := by norm_num
  have hpos : 0 < ∑' p : Nat.Primes, log p / (p : ℝ) ^ (3 : ℝ) := by
    simpa only [hthree] using
      (summable_primes_log_div_rpow (η := 2) (by norm_num)).tsum_pos
        (fun p ↦ div_nonneg (log_nonneg (by exact_mod_cast p.prop.one_lt.le))
          (rpow_nonneg (by exact_mod_cast p.prop.pos.le) _)) ⟨2, Nat.prime_two⟩ (by positivity)
  have hM : (∑' p : Nat.Primes, log p / (p : ℝ) ^ (3 : ℝ)) =
      2 * ∫ t in Ioi (1 : ℝ), t ^ (-3 : ℝ) * weightedPrimeSum (fun _ ↦ (1 : ℝ)) t := by
    simpa only [mellinWeightIntegral_def, hthree, hnegthree, smul_eq_mul, mul_one] using
      tsum_weightedPrimeSeries (a := fun _ ↦ (1 : ℝ)) (η := 2)
        (fun _ _ ↦ by norm_num) (by norm_num)
  intro h
  linarith

/-- Changing the reciprocal-square weight to a reciprocal first power loses summability. -/
example : ¬Summable (fun n : ℕ ↦
    if n.Prime ∧ (2 : ℝ) ≤ n then log n / (n : ℝ) else 0) := by
  exact Chebyshev.not_summable_prime_log_div_ge 2

/-- The absolute tail constant specializes to `log 4` at the first prime. -/
example :
    (∑' n : ℕ, if n.Prime ∧ (2 : ℝ) ≤ n then log n / (n : ℝ) ^ 2 else 0) ≤ log 4 := by
  simpa using tsum_prime_log_div_sq_ge_le (y := 2) (by norm_num)

/-- At parameter one the same smoothing gives the reciprocal-square logarithmic prime series.
-/
example : (∑' p : Nat.Primes, log p / (p : ℝ) ^ 2) =
    ∫ t in Ioi (1 : ℝ), t ^ (-2 : ℝ) * weightedPrimeSum (fun _ ↦ (1 : ℝ)) t := by
  have htwo : 1 + (1 : ℝ) = 2 := by norm_num
  have hnegtwo : -1 - (1 : ℝ) = -2 := by norm_num
  simpa only [mellinWeightIntegral_def, htwo, hnegtwo, smul_eq_mul, mul_one, one_mul,
    rpow_two] using
    tsum_weightedPrimeSeries (a := fun _ ↦ (1 : ℝ)) (η := 1)
      (fun _ _ ↦ by norm_num) (by norm_num)

end TauCeti.WeightedPrimeMellinExamples
