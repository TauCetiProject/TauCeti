/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Regrouping a double series by the product of the indices

A sum over pairs of positive integers `(c, m)` can be regrouped according to the product
`n = c m`: the `n`-th group is the finite sum over `Nat.divisorsAntidiagonal n`. This is how a
double series `∑_{c, m ≥ 1} a(c) b(m) q^{c m}`, such as the `q`-expansion of an Eisenstein
series, becomes a power series `∑_n (∑_{c m = n} a(c) b(m)) q^n`.

Mathlib's `tsum_prod_pow_eq_tsum_sigma` proves one instance of this regrouping, for the terms
`m^k r^{c m}`; this file states the regrouping for an arbitrary summable family, through the
same equivalence `sigmaAntidiagonalEquivProd`. For weights of polynomial growth and `‖q‖ < 1`,
the Lambert double series converges absolutely and regroups into a divisor-sum power series.
An extra parameter `u` with `‖u‖ ≤ 1` gives coefficients `∑_{d ∣ n} a d u^d`.
For `‖u‖ = 1`, reciprocal summands give a bilateral-series expansion after removing its
constant term.

## Main results

* `HasSum.sum_divisorsAntidiagonal`: regrouping a convergent double series by the product of
  the indices.
* `TauCeti.hasSum_sum_divisors_mul_pow_of_norm_le_mul_pow`: convergence and regrouping
  for weights of polynomial growth.
* `TauCeti.hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow`: a second parameter
  in the closed unit ball produces weighted divisor-sum coefficients.
* `TauCeti.hasSum_sum_divisors_mul_pow_sub_of_norm_eq_one`: a reciprocal pair of
  expansions regroups the nonconstant part of a bilateral series on the unit circle.
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
/-- A Lambert-series family with weights of polynomial growth is absolutely summable
inside the unit disc. -/
theorem summable_norm_mul_pow_prod_of_norm_le_mul_pow (a : ℕ → K) {C : ℝ} {k : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun p : ℕ+ × ℕ+ ↦ ‖a p.2 * q ^ (p.1 * p.2 : ℕ)‖) := by
  have hs := (summable_prod_mul_pow k (r := ‖q‖) (by simpa using hq)).mul_left C
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) hs
  calc
    ‖a p.2 * q ^ (p.1 * p.2 : ℕ)‖ ≤ ‖a p.2‖ * ‖q ^ (p.1 * p.2 : ℕ)‖ := norm_mul_le _ _
    _ ≤ (C * (p.2 : ℝ) ^ k) * ‖q‖ ^ (p.1 * p.2 : ℕ) :=
      mul_le_mul (ha _) (norm_pow_le _ _) (norm_nonneg _)
        ((norm_nonneg _).trans (ha _))
    _ = C * ((p.2 : ℝ) ^ k * ‖q‖ ^ (p.1 * p.2 : ℕ)) := mul_assoc _ _ _

/-- Regrouping a Lambert series with weights of polynomial growth gives a convergent
divisor-sum expansion. The term at index zero vanishes because `Nat.divisors 0` is empty. -/
theorem hasSum_sum_divisors_mul_pow_of_norm_le_mul_pow (a : ℕ → K) {C : ℝ} {k : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k)
    {q : K} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors, a d) * q ^ n)
      (∑' n : ℕ+, ∑' d : ℕ+, a d * q ^ (n * d : ℕ)) := by
  have hs := (summable_norm_mul_pow_prod_of_norm_le_mul_pow a ha hq).of_norm
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

/-- A Lambert series with weights of polynomial growth and a parameter in the closed unit ball
expands as a power series whose coefficients are finite divisor sums. -/
theorem hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow (a : ℕ → K) {C : ℝ} {k : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k)
    {q u : K} (hq : ‖q‖ < 1) (hu : ‖u‖ ≤ 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors, a d * u ^ d) * q ^ n)
      (∑' n : ℕ+, ∑' d : ℕ, a (d + 1) * (q ^ (n : ℕ) * u) ^ (d + 1)) := by
  have hau (d : ℕ) : ‖a d * u ^ d‖ ≤ C * (d : ℝ) ^ k := by
    calc
      ‖a d * u ^ d‖ ≤ ‖a d‖ * ‖u ^ d‖ := norm_mul_le _ _
      _ ≤ (C * (d : ℝ) ^ k) * 1 :=
        mul_le_mul (ha d) ((norm_pow_le u d).trans (pow_le_one₀ (norm_nonneg u) hu))
          (norm_nonneg _) ((norm_nonneg _).trans (ha d))
      _ = C * (d : ℝ) ^ k := mul_one _
  convert hasSum_sum_divisors_mul_pow_of_norm_le_mul_pow _ hau hq using 1
  apply tsum_congr
  intro n
  rw [tsum_pnat_eq_tsum_succ (f := fun d : ℕ ↦ a d * u ^ d * q ^ ((n : ℕ) * d))]
  apply tsum_congr
  intro d
  rw [mul_pow, ← pow_mul]
  ring

section NormedField

variable {K : Type*} [NormedField K] [CompleteSpace K]

/-- If a summand and its reciprocal have geometric expansions with polynomially bounded
weights, their bilateral series on the unit circle, minus the index-zero term, has a
convergent divisor-sum expansion. -/
theorem hasSum_sum_divisors_mul_pow_sub_of_norm_eq_one (a b : ℕ → K) {C D : ℝ} {k l : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k) (hb : ∀ d, ‖b d‖ ≤ D * (d : ℝ) ^ l)
    (f g : K → K)
    (hf : ∀ r, ‖r‖ < 1 → (∑' d : ℕ, a (d + 1) * r ^ (d + 1)) = f r)
    (hg : ∀ r, ‖r‖ < 1 → (∑' d : ℕ, b (d + 1) * r ^ (d + 1)) = g r)
    (hinv : ∀ r, f r⁻¹ = g r) (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1)
    (hs : Summable (fun n : ℤ ↦ f ((q : K) ^ n * (u : K)))) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors,
        (a d * (u : K) ^ d + b d * (u : K)⁻¹ ^ d)) * (q : K) ^ n)
      ((∑' n : ℤ, f ((q : K) ^ n * (u : K))) - f (u : K)) := by
  have hsmall {v : K} (hv : ‖v‖ = 1) (n : ℕ+) : ‖(q : K) ^ (n : ℕ) * v‖ < 1 := by
    rw [norm_mul, norm_pow, hv, mul_one]
    exact pow_lt_one₀ (norm_nonneg _) hq n.ne_zero
  have hui : ‖(u : K)⁻¹‖ = 1 := by simp [hu]
  have hp := hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow a ha hq hu.le
  have hm := hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow b hb hq hui.le
  convert hp.add hm using 1
  · funext n
    simp only [Finset.sum_add_distrib, add_mul]
  · have hsplit := tsum_int_eq_zero_add_tsum_pnat hs
    simp only [zpow_natCast, zpow_neg, zpow_zero, one_mul] at hsplit
    have hneg (n : ℕ+) : f (((q : K) ^ (n : ℕ))⁻¹ * (u : K)) =
        g ((q : K) ^ (n : ℕ) * (u : K)⁻¹) := by
      simpa only [mul_inv, inv_inv] using hinv ((q : K) ^ (n : ℕ) * (u : K)⁻¹)
    simp_rw [hneg] at hsplit
    simp_rw [hf _ (hsmall hu _), hg _ (hsmall hui _)]
    rw [hsplit]
    ring

end NormedField

end TauCeti
