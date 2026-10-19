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
An extra parameter `u` with `‖q * u‖ < 1` gives coefficients `∑_{d ∣ n} a d u^d`.
When both `‖q * u‖ < 1` and `‖q * u⁻¹‖ < 1`, reciprocal summands give a bilateral-series
expansion after removing its constant term.

## Main results

* `HasSum.sum_divisorsAntidiagonal`: regrouping a convergent double series by the product of
  the indices.
* `TauCeti.hasSum_sum_divisors_mul_pow_of_norm_le_mul_pow`: convergence and regrouping
  for weights of polynomial growth.
* `TauCeti.hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow`: a second parameter
  with `‖q * u‖ < 1` produces weighted divisor-sum coefficients.
* `TauCeti.hasSum_sum_divisors_mul_pow_sub`: a reciprocal pair of
  expansions regroups the nonconstant part of a bilateral series on its annulus of convergence.
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
/-- Multiplying a parameter in the open unit ball by further powers of `q` keeps it there. -/
theorem norm_pow_pnat_mul_lt_one {q v : K} (hq : ‖q‖ < 1) (hqv : ‖q * v‖ < 1)
    (n : ℕ+) : ‖q ^ (n : ℕ) * v‖ < 1 := by
  have hn : (n : ℕ) = ((n : ℕ) - 1) + 1 := (Nat.sub_add_cancel n.pos).symm
  rw [hn, pow_succ, mul_assoc]
  exact (norm_mul_le _ _).trans_lt <| lt_of_le_of_lt
    (mul_le_of_le_one_left (norm_nonneg _)
      ((norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) hq.le))) hqv

omit [CompleteSpace K] in
/-- A Lambert-series family with weights of polynomial growth is absolutely summable when
both `‖q‖ < 1` and `‖q * u‖ < 1`. -/
theorem summable_norm_mul_pow_mul_pow_prod_of_norm_le_mul_pow (a : ℕ → K) {C : ℝ} {k : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k) {q u : K} (hq : ‖q‖ < 1) (hqu : ‖q * u‖ < 1) :
    Summable (fun p : ℕ+ × ℕ+ ↦ ‖a p.2 * u ^ (p.2 : ℕ) * q ^ (p.1 * p.2 : ℕ)‖) := by
  let r := max ‖q‖ ‖q * u‖
  have hr : r < 1 := max_lt hq hqu
  have hr0 : 0 ≤ r := (norm_nonneg q).trans (le_max_left _ _)
  have hbound := (summable_prod_mul_pow k (r := r)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) hbound
  have hn : (p.1 : ℕ) * p.2 = (p.2 : ℕ) + ((p.1 : ℕ) - 1) * p.2 := by
    have hn : (p.1 : ℕ) = ((p.1 : ℕ) - 1) + 1 := (Nat.sub_add_cancel p.1.pos).symm
    conv_lhs => rw [hn]
    ring
  have he : a p.2 * u ^ (p.2 : ℕ) * q ^ (p.1 * p.2 : ℕ) =
      a p.2 * (q * u) ^ (p.2 : ℕ) * q ^ (((p.1 : ℕ) - 1) * p.2) := by
    rw [mul_pow, hn, pow_add]
    ring
  rw [he]
  calc
    _ ≤ ‖a p.2‖ * ‖q * u‖ ^ (p.2 : ℕ) * ‖q‖ ^ (((p.1 : ℕ) - 1) * p.2) := by
      calc
        _ ≤ ‖a p.2 * (q * u) ^ (p.2 : ℕ)‖ *
            ‖q ^ (((p.1 : ℕ) - 1) * p.2)‖ := norm_mul_le _ _
        _ ≤ (‖a p.2‖ * ‖(q * u) ^ (p.2 : ℕ)‖) *
            ‖q ^ (((p.1 : ℕ) - 1) * p.2)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ _ := by gcongr <;> exact norm_pow_le _ _
    _ ≤ (C * (p.2 : ℝ) ^ k) * r ^ (p.2 : ℕ) * r ^ (((p.1 : ℕ) - 1) * p.2) := by
      have hC : 0 ≤ C * (p.2 : ℝ) ^ k := (norm_nonneg _).trans (ha _)
      gcongr
      · exact ha _
      · exact le_max_right _ _
      · exact le_max_left _ _
    _ = C * ((p.2 : ℝ) ^ k * r ^ (p.1 * p.2 : ℕ)) := by rw [hn, pow_add]; ring

/-- A Lambert series with weights of polynomial growth and `‖q * u‖ < 1` expands as a
power series whose coefficients are finite divisor sums. -/
theorem hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow (a : ℕ → K) {C : ℝ} {k : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k)
    {q u : K} (hq : ‖q‖ < 1) (hqu : ‖q * u‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors, a d * u ^ d) * q ^ n)
      (∑' n : ℕ+, ∑' d : ℕ, a (d + 1) * (q ^ (n : ℕ) * u) ^ (d + 1)) := by
  have hs := (summable_norm_mul_pow_mul_pow_prod_of_norm_le_mul_pow a ha hq hqu).of_norm
  have h := HasSum.sum_divisorsAntidiagonal
    (f := fun n d : ℕ ↦ a d * u ^ d * q ^ (n * d)) hs.hasSum
  simp_rw [Nat.sum_divisorsAntidiagonal' (fun n d ↦ a d * u ^ d * q ^ (n * d))] at h
  have he (n : ℕ+) : (∑ d ∈ (n : ℕ).divisors,
      a d * u ^ d * q ^ ((n : ℕ) / d * d)) =
        (∑ d ∈ (n : ℕ).divisors, a d * u ^ d) * q ^ (n : ℕ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun d hd ↦ by rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
  simp_rw [he] at h
  rw [hs.tsum_prod] at h
  have hnat := (hasSum_pnat_iff (f := fun n : ℕ ↦
    (∑ d ∈ n.divisors, a d * u ^ d) * q ^ n)).mp h
  simp only [Nat.divisors_zero, Finset.sum_empty, zero_mul, add_zero] at hnat
  convert hnat using 1
  apply tsum_congr
  intro n
  rw [tsum_pnat_eq_tsum_succ (f := fun d : ℕ ↦ a d * u ^ d * q ^ ((n : ℕ) * d))]
  apply tsum_congr
  intro d
  rw [mul_pow, ← pow_mul]
  ring

/-- Regrouping a Lambert series with weights of polynomial growth gives a convergent
divisor-sum expansion. The term at index zero vanishes because `Nat.divisors 0` is empty. -/
theorem hasSum_sum_divisors_mul_pow_of_norm_le_mul_pow (a : ℕ → K) {C : ℝ} {k : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k)
    {q : K} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors, a d) * q ^ n)
      (∑' n : ℕ+, ∑' d : ℕ+, a d * q ^ (n * d : ℕ)) := by
  have h := hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow a ha hq
    (u := 1) (by simpa using hq)
  simp only [one_pow, mul_one] at h
  convert h using 1
  apply tsum_congr
  intro n
  rw [tsum_pnat_eq_tsum_succ (f := fun d : ℕ ↦ a d * q ^ ((n : ℕ) * d))]
  simp only [pow_mul]

/-- A geometric expansion with polynomially bounded weights gives a summable sequence
when evaluated at `qⁿ * u` for positive `n` on the annulus of convergence. -/
theorem summable_apply_pow_pnat_mul_of_tsum_eq (a : ℕ → K) {C : ℝ} {k : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k) {q u : K}
    (hq : ‖q‖ < 1) (hqu : ‖q * u‖ < 1) (f : K → K)
    (hf : ∀ r, ‖r‖ < 1 → (∑' d : ℕ, a (d + 1) * r ^ (d + 1)) = f r) :
    Summable (fun n : ℕ+ ↦ f (q ^ (n : ℕ) * u)) := by
  have h := (summable_norm_mul_pow_mul_pow_prod_of_norm_le_mul_pow a ha hq hqu).of_norm.prod
  convert h using 1
  funext n
  rw [← hf _ (norm_pow_pnat_mul_lt_one hq hqu n),
    tsum_pnat_eq_tsum_succ (f := fun d : ℕ ↦ a d * u ^ d * q ^ ((n : ℕ) * d))]
  apply tsum_congr
  intro d
  rw [mul_pow, ← pow_mul]
  ring

section NormedField

variable {K : Type*} [NormedField K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- If multiplying by both a unit and its inverse has norm less than one, the original
element has norm less than one. -/
theorem norm_lt_one_of_norm_mul_lt_one_of_norm_mul_inv_lt_one {q : K} (u : Kˣ)
    (hqu : ‖q * (u : K)‖ < 1) (hqui : ‖q * (u : K)⁻¹‖ < 1) : ‖q‖ < 1 := by
  have h := (mul_le_of_le_one_right (norm_nonneg _) hqui.le).trans_lt hqu
  rw [← norm_mul, mul_mul_mul_comm, mul_inv_cancel₀ u.ne_zero, mul_one,
    ← pow_two, norm_pow] at h
  exact (sq_lt_one_iff₀ (norm_nonneg _)).mp h

/-- If a summand and its reciprocal have geometric expansions with polynomially bounded
weights, their bilateral series, minus the index-zero term, has a
convergent divisor-sum expansion. -/
theorem hasSum_sum_divisors_mul_pow_sub (a b : ℕ → K) {C D : ℝ} {k l : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k) (hb : ∀ d, ‖b d‖ ≤ D * (d : ℝ) ^ l)
    (f g : K → K)
    (hf : ∀ r, ‖r‖ < 1 → (∑' d : ℕ, a (d + 1) * r ^ (d + 1)) = f r)
    (hg : ∀ r, ‖r‖ < 1 → (∑' d : ℕ, b (d + 1) * r ^ (d + 1)) = g r)
    (hinv : ∀ r, f r⁻¹ = g r) (q u : Kˣ)
    (hqu : ‖(q : K) * (u : K)‖ < 1) (hqui : ‖(q : K) * (u : K)⁻¹‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors,
        (a d * (u : K) ^ d + b d * (u : K)⁻¹ ^ d)) * (q : K) ^ n)
      ((∑' n : ℤ, f ((q : K) ^ n * (u : K))) - f (u : K)) := by
  have hq := norm_lt_one_of_norm_mul_lt_one_of_norm_mul_inv_lt_one u hqu hqui
  have hneg (n : ℕ+) : f (((q : K) ^ (n : ℕ))⁻¹ * (u : K)) =
      g ((q : K) ^ (n : ℕ) * (u : K)⁻¹) := by
    simpa only [mul_inv, inv_inv] using hinv ((q : K) ^ (n : ℕ) * (u : K)⁻¹)
  have hs : Summable (fun n : ℤ ↦ f ((q : K) ^ n * (u : K))) := by
    apply Summable.of_nat_of_neg
    · simpa only [zpow_natCast] using
        (summable_pnat_iff_summable_nat (f := fun n : ℕ ↦ f ((q : K) ^ n * (u : K)))).mp
          (summable_apply_pow_pnat_mul_of_tsum_eq a ha hq hqu f hf)
    · apply (summable_pnat_iff_summable_nat
        (f := fun n : ℕ ↦ f ((q : K) ^ (-(n : ℤ)) * (u : K)))).mp
      simpa only [zpow_neg, zpow_natCast, hneg] using
        summable_apply_pow_pnat_mul_of_tsum_eq b hb hq hqui g hg
  have hp := hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow a ha hq hqu
  have hm := hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow b hb hq hqui
  convert hp.add hm using 1
  · funext n
    simp only [Finset.sum_add_distrib, add_mul]
  · have hsplit := tsum_int_eq_zero_add_tsum_pnat hs
    simp only [zpow_natCast, zpow_neg, zpow_zero, one_mul] at hsplit
    simp_rw [hneg] at hsplit
    simp_rw [hf _ (norm_pow_pnat_mul_lt_one hq hqu _),
      hg _ (norm_pow_pnat_mul_lt_one hq hqui _)]
    rw [hsplit]
    ring

end NormedField

end TauCeti
