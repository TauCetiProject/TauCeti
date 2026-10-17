/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.RCLike.Basic

/-!
# Regrouping a double series by the product of the indices

A sum over pairs of positive integers `(c, m)` can be regrouped according to the product
`n = c m`: the `n`-th group is the finite sum over `Nat.divisorsAntidiagonal n`. This is how a
double series `∑_{c, m ≥ 1} a(c) b(m) q^{c m}`, such as the `q`-expansion of an Eisenstein
series, becomes a power series `∑_n (∑_{c m = n} a(c) b(m)) q^n`.

Mathlib's `tsum_prod_pow_eq_tsum_sigma` proves one instance of this regrouping, for the terms
`m^k r^{c m}`; this file states the regrouping for an arbitrary summable family, through the
same equivalence `sigmaAntidiagonalEquivProd`.

## Main results

* `HasSum.sum_divisorsAntidiagonal`: regrouping a convergent double series by the product of
  the indices.
* `TauCeti.hasSum_bounded_sum_divisors_mul_pow`: convergence and regrouping for bounded weights.
* `TauCeti.tsum_bounded_mul_pow_mul_eq_tsum_sum_divisors`: a second parameter in the closed unit
  ball produces weighted divisor-sum coefficients.
-/

public section

variable {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α] [RegularSpace α]

/-- **Regrouping a double series by the product of the indices.** If the family
`(c, m) ↦ f c m` over pairs of positive integers sums to `a`, then so does the series over
`n ≥ 1` of the finite sums `∑_{c m = n} f c m`. -/
theorem HasSum.sum_divisorsAntidiagonal {f : ℕ → ℕ → α} {a : α}
    (hf : HasSum (fun p : ℕ+ × ℕ+ ↦ f p.1 p.2) a) :
    HasSum (fun n : ℕ+ ↦ ∑ x ∈ (n : ℕ).divisorsAntidiagonal, f x.1 x.2) a := by
  refine (sigmaAntidiagonalEquivProd.hasSum_iff.mpr hf).sigma fun n ↦ ?_
  have h := hasSum_fintype fun x : (n : ℕ).divisorsAntidiagonal ↦ f x.1.1 x.1.2
  rw [Finset.univ_eq_attach, Finset.sum_attach _ fun x : ℕ × ℕ ↦ f x.1 x.2] at h
  simpa [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors] using h

namespace TauCeti

variable {K : Type*} [NormedCommRing K] [NormOneClass K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- A Lambert-series family with bounded weights is absolutely summable inside the unit disc. -/
theorem summable_norm_bounded_mul_pow_prod (a : ℕ → K) (ha : ∀ d, ‖a d‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    Summable (fun p : ℕ+ × ℕ+ ↦ ‖a p.2 * q ^ (p.1 * p.2 : ℕ)‖) := by
  have hs : Summable (fun p : ℕ+ × ℕ+ ↦ ‖q‖ ^ (p.1 * p.2 : ℕ)) := by
    simpa using summable_prod_mul_pow 0 (r := ‖q‖) (by simpa using hq)
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) hs
  calc
    ‖a p.2 * q ^ (p.1 * p.2 : ℕ)‖ ≤ ‖a p.2‖ * ‖q ^ (p.1 * p.2 : ℕ)‖ := norm_mul_le _ _
    _ ≤ 1 * ‖q‖ ^ (p.1 * p.2 : ℕ) :=
      mul_le_mul (ha _) (norm_pow_le _ _) (norm_nonneg _) zero_le_one
    _ = ‖q‖ ^ (p.1 * p.2 : ℕ) := one_mul _

/-- Regrouping a Lambert series with bounded weights gives a convergent divisor-sum expansion.
The term at index zero vanishes because `Nat.divisors 0` is empty. -/
theorem hasSum_bounded_sum_divisors_mul_pow (a : ℕ → K) (ha : ∀ d, ‖a d‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors, a d) * q ^ n)
      (∑' n : ℕ+, ∑' d : ℕ+, a d * q ^ (n * d : ℕ)) := by
  have hs := (summable_norm_bounded_mul_pow_prod a ha hq).of_norm
  have h := HasSum.sum_divisorsAntidiagonal
    (f := fun n d : ℕ ↦ a d * q ^ (n * d)) hs.hasSum
  have he (n : ℕ+) :
      (∑ x ∈ (n : ℕ).divisorsAntidiagonal, a x.2 * q ^ (x.1 * x.2)) =
        (∑ d ∈ (n : ℕ).divisors, a d) * q ^ (n : ℕ) := by
    rw [Nat.sum_divisorsAntidiagonal' (fun c d ↦ a d * q ^ (c * d)), Finset.sum_mul]
    exact Finset.sum_congr rfl fun d hd ↦ by rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
  simp_rw [he] at h
  rw [hs.tsum_prod] at h
  simpa using (hasSum_pnat_iff (f := fun n : ℕ ↦
    (∑ d ∈ n.divisors, a d) * q ^ n)).mp h

/-- A bounded weighted Lambert series, with an additional parameter in the closed unit ball,
expands as a power series whose coefficients are finite divisor sums. -/
theorem tsum_bounded_mul_pow_mul_eq_tsum_sum_divisors (a : ℕ → K) (ha : ∀ d, ‖a d‖ ≤ 1)
    {q u : K} (hq : ‖q‖ < 1) (hu : ‖u‖ ≤ 1) :
    (∑' n : ℕ+, ∑' d : ℕ, a (d + 1) * (q ^ (n : ℕ) * u) ^ (d + 1)) =
      ∑' n : ℕ, (∑ d ∈ n.divisors, a d * u ^ d) * q ^ n := by
  have hau (d : ℕ) : ‖a d * u ^ d‖ ≤ 1 :=
    (norm_mul_le_of_le (ha d)
      ((norm_pow_le u d).trans (pow_le_one₀ (norm_nonneg u) hu))).trans_eq (one_mul _)
  rw [(hasSum_bounded_sum_divisors_mul_pow _ hau hq).tsum_eq]
  apply tsum_congr
  intro n
  rw [tsum_pnat_eq_tsum_succ (f := fun d : ℕ ↦ a d * u ^ d * q ^ ((n : ℕ) * d))]
  apply tsum_congr
  intro d
  rw [mul_pow, ← pow_mul]
  ring

end TauCeti
