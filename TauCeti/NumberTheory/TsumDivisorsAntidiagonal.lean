/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import TauCeti.Analysis.Normed.Ring.Basic
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

## Main results

* `HasSum.sum_divisorsAntidiagonal`: regrouping a convergent double series by the product of
  the indices.
* `TauCeti.hasSum_sum_divisors_mul_pow`: for polynomially bounded `g` and `‖r‖ < 1`, the series
  `∑_{c, m ≥ 1} g(m) r^{c m}` is the power series `∑_n (∑_{m ∣ n} g(m)) rⁿ`.
* `TauCeti.hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow`: a second parameter
  with `‖q * u‖ < 1` produces weighted divisor-sum coefficients.
* `TauCeti.hasSum_sum_divisors_mul_pow_mul_of_tsum_eq`: evaluates the inner geometric expansion
  to identify the Lambert series with a one-sided series of closed-form summands.
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

/-- **Lambert-type series as power series.** For polynomially bounded `g` and `‖r‖ < 1` in a
complete normed ring, the power series `∑_n (∑_{m ∣ n} g(m)) rⁿ` sums to the double series
`∑_{c ≥ 1} ∑_{m ≥ 1} g(m) r^{c m}`. For instance `g(m) = m sᵐ` gives
`∑_{c ≥ 1} r^c s / (1 - r^c s)²` when `‖s‖ ≤ 1` in a non-archimedean field. -/
theorem hasSum_sum_divisors_mul_pow {K : Type*} [NormedRing K] [CompleteSpace K] {g : ℕ → K}
    {C : ℝ} {k : ℕ} (hg : ∀ m, ‖g m‖ ≤ C * (m : ℝ) ^ k) {r : K} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ m ∈ n.divisors, g m) * r ^ n)
      (∑' c : ℕ, ∑' m : ℕ, g (m + 1) * r ^ ((c + 1) * (m + 1))) := by
  have hs : Summable (fun p : ℕ+ × ℕ+ ↦ g p.2 * r ^ ((p.1 : ℕ) * p.2)) := by
    refine Summable.of_norm_bounded
      (g := fun p : ℕ+ × ℕ+ ↦ C * ((p.2 : ℝ) ^ k * ‖r‖ ^ ((p.1 : ℕ) * p.2))) ?_ ?_
    · simpa using (summable_prod_mul_pow k (r := ‖r‖) (by simpa using hr)).mul_left C
    · intro p
      calc ‖g p.2 * r ^ ((p.1 : ℕ) * p.2)‖ ≤ ‖g p.2‖ * ‖r ^ ((p.1 : ℕ) * p.2)‖ := norm_mul_le _ _
        _ ≤ C * ((p.2 : ℝ) ^ k * ‖r‖ ^ ((p.1 : ℕ) * p.2)) := by
          rw [← mul_assoc]
          exact mul_le_mul (hg _) (norm_pow_le' _ (mul_pos p.1.2 p.2.2))
            (norm_nonneg _) ((norm_nonneg _).trans (hg _))
  have hv : ∑' p : ℕ+ × ℕ+, g p.2 * r ^ ((p.1 : ℕ) * p.2) =
      ∑' c : ℕ, ∑' m : ℕ, g (m + 1) * r ^ ((c + 1) * (m + 1)) := by
    rw [hs.tsum_prod, tsum_pnat_eq_tsum_succ (f := fun c ↦ ∑' m : ℕ+, g m * r ^ (c * m))]
    exact tsum_congr fun c ↦ tsum_pnat_eq_tsum_succ (f := fun m ↦ g m * r ^ ((c + 1) * m))
  have h := hs.hasSum.sum_divisorsAntidiagonal (f := fun c m ↦ g m * r ^ (c * m))
  rw [hv] at h
  -- the term `n = 0` vanishes, so the series over `ℕ` is the series over `ℕ+`
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.divisors_zero, Finset.sum_empty,
    zero_mul, sub_zero]
  rw [← hasSum_pnat_iff_hasSum_succ (f := fun n ↦ (∑ m ∈ n.divisors, g m) * r ^ n)]
  convert h using 2 with n
  rw [Nat.sum_divisorsAntidiagonal' (f := fun c m ↦ g m * r ^ (c * m)), Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)]

variable {K : Type*} [NormedCommRing K] [NormOneClass K] [CompleteSpace K]

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

/-- Evaluating the inner geometric expansion of a Lambert series gives a divisor-sum
expansion for the one-sided series of its closed-form summands. -/
theorem hasSum_sum_divisors_mul_pow_mul_of_tsum_eq (a : ℕ → K) {C : ℝ} {k : ℕ}
    (ha : ∀ d, ‖a d‖ ≤ C * (d : ℝ) ^ k) {q u : K}
    (hq : ‖q‖ < 1) (hqu : ‖q * u‖ < 1) (f : K → K)
    (hf : ∀ r, ‖r‖ < 1 → (∑' d : ℕ, a (d + 1) * r ^ (d + 1)) = f r) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors, a d * u ^ d) * q ^ n)
      (∑' n : ℕ, f (q ^ (n + 1) * u)) := by
  have h := hasSum_sum_divisors_mul_pow_mul_of_norm_le_mul_pow a ha hq hqu
  simp_rw [hf _ (norm_pow_pnat_mul_lt_one hq hqu _)] at h
  rwa [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f (q ^ n * u))] at h

end TauCeti
