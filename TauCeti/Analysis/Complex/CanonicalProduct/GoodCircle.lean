/-
Copyright (c) 2026 Matteo Cipollina and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import TauCeti.Analysis.Normed.Group.SummableNormInvRpow
import TauCeti.Analysis.SpecialFunctions.Integrals.PosLog
import TauCeti.Analysis.SpecialFunctions.Log.PosLog

/-!
# Cartan's good-circle estimate for Weierstrass primary products

Let `p` be a genus and `p ≤ τ ≤ p + 1`, and let `a : ι → ℂ` be a family with
`∑' i, ‖a i‖⁻¹ ^ τ < ∞`. Every dyadic interval `(R, 2 * R]`, `R > 0`, contains a radius `r` such
that on the whole circle `‖z‖ = r` the genus-`p` primary product is bounded below:
`exp (-(C * r ^ τ)) ≤ ‖∏' i, E_p(z / a i)‖`, with the explicit constant
`C = ((log 2 + 12 * sqrt 6 + p) * 4 ^ τ + p + 2) * ∑' i, ‖a i‖⁻¹ ^ τ`
(`Complex.exists_mem_Ioc_forall_norm_eq_exp_neg_le_norm_tprod_weierstrassFactor_div`).
This is the minimum-modulus step of finite-order Hadamard factorization: with a growth bound on
`f` of order below `τ`, it bounds the real part of the entire logarithm of `f / (z ^ m * P)` above
by `O(r ^ τ)` on these circles.

The proof splits the zeros at `4 * R`. A far zero has `‖z / a‖ ≤ 1 / 2`, where
`-log ‖E_p w‖ ≤ 2 * ‖w‖ ^ (p + 1) ≤ 2 * ‖w‖ ^ τ`. A near zero contributes at most
`log⁺ (1 / |1 - r / ‖a‖|) + p * (1 + (r / ‖a‖) ^ τ)`
(`Complex.neg_log_norm_one_sub_le_posLog_one_div_abs_one_sub_norm` and the whole-plane bound
`Complex.neg_log_norm_weierstrassFactor_le_mul_max`). There are only finitely many near zeros,
at most `(4 * R) ^ τ * ∑' i, ‖a i‖⁻¹ ^ τ` (`Summable.finite_setOf_ne_zero_norm_le` and
`Summable.card_le_rpow_mul_tsum`), and Cartan's averaging over `(R, 2 * R]`
(`Finset.exists_mem_Ioc_notMem_sum_mul_posLog_one_div_abs_one_sub_div_le`) chooses `r` away from
their moduli with the sum of their logarithmic singularities at most a universal constant times
their number. The bound holds for every finite partial product, hence for the unordered product.

Indices with `a i = 0` contribute the unit factor `E_p 0 = 1`. A product over grouped
multiplicities is the product over `Σ i, Fin (m i)`
(`Complex.tprod_weierstrassFactor_div_pow_eq_sigma`).

## Provenance

Adapted from Matteo Cipollina's `CartanBound.lean`, `CartanInverseFactorBound.lean` and
`CartanMajorantBound.lean` in
[PrimeNumberTheoremAnd, revision df0ccba](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/df0ccba486bb86e273ecab565b6ab222c37f8320/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex),
which state the near-zero factor bound and the majorant sum over a divisor-indexed zero
enumeration with the weight `(1 + r) ^ τ`. Here the estimate is stated for an arbitrary index
family and directly for the product, with the weight `r ^ τ`.

## References

* B. Ya. Levin, *Distribution of Zeros of Entire Functions*, Chapter I, §§7 and 10.
* A. Kupers, *Complex analysis* lecture notes, Lemmas 14.1.4 and 14.1.5.
-/

public section

open Filter Topology

namespace Complex

/-- The lower bound for one rescaled factor on the circle `‖z‖ = r`, split at `4 * R`. -/
private lemma neg_log_norm_weierstrassFactor_div_le (p : ℕ) {τ R r : ℝ} (hpτ : (p : ℝ) ≤ τ)
    (hτp : τ ≤ p + 1) (hr : r ≤ 2 * R) {a z : ℂ} (hz : ‖z‖ = r) (hra : r ≠ ‖a‖) :
    weierstrassFactor p (z / a) ≠ 0 ∧ -Real.log ‖weierstrassFactor p (z / a)‖ ≤
      (if a ≠ 0 ∧ ‖a‖ ≤ 4 * R then Real.posLog (1 / |1 - r / ‖a‖|) + p else 0) +
        (p + 2) * (r / ‖a‖) ^ τ := by
  have hw : ‖z / a‖ = r / ‖a‖ := by rw [norm_div, hz]
  have hw1 : ‖z / a‖ ≠ 1 := by
    rw [hw]
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · exact fun h ↦ hra ((div_eq_one_iff_eq (norm_ne_zero_iff.mpr ha)).mp h)
  refine ⟨fun h ↦ hw1 (by rw [(weierstrassFactor_eq_zero_iff p).mp h, norm_one]), ?_⟩
  have hx : 0 ≤ (r / ‖a‖) ^ τ := Real.rpow_nonneg (by rw [← hw]; positivity) τ
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  split_ifs with h
  · have hmax : max 1 ‖z / a‖ ^ p ≤ 1 + (r / ‖a‖) ^ τ := by
      rcases le_total ‖z / a‖ 1 with h1 | h1
      · rw [max_eq_left h1, one_pow]
        linarith
      · rw [max_eq_right h1, ← Real.rpow_natCast, ← hw]
        linarith [Real.rpow_le_rpow_of_exponent_le h1 hpτ]
    have h1 := neg_log_norm_one_sub_le_posLog_one_div_abs_one_sub_norm hw1
    rw [hw] at h1
    nlinarith [neg_log_norm_weierstrassFactor_le_mul_max p (z / a),
      mul_le_mul_of_nonneg_left hmax hp]
  · have hhalf : ‖z / a‖ ≤ 1 / 2 := by
      rw [hw]
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      · have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
        rw [div_le_iff₀ hpos]
        linarith [lt_of_not_ge (not_and.mp h ha)]
    have hpow := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (z / a)) (by linarith)
      (hp.trans hpτ) hτp
    have h2 := neg_log_norm_weierstrassFactor_le_two_mul p hhalf
    rw [← Nat.cast_add_one, Real.rpow_natCast, hw] at hpow
    rw [hw] at h2
    linarith [mul_nonneg hp hx]

/-- The good-circle bound for every finite partial product, once the radius `r` avoids the
moduli of the near zeros and controls the sum of their logarithmic singularities. -/
private lemma exp_neg_le_norm_prod_weierstrassFactor_div {ι : Type*} (p : ℕ) {τ R r : ℝ}
    (hpτ : (p : ℝ) ≤ τ) (hτp : τ ≤ p + 1) {a : ι → ℂ} (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ τ)
    (hr : r ≤ 2 * R) {near : Finset ι}
    (hnear : ∀ i, i ∈ near ↔ a i ≠ 0 ∧ ‖a i‖ ≤ 4 * R)
    (hsum : ∑ i ∈ near, Real.posLog (1 / |1 - r / ‖a i‖|) ≤
      (Real.log 2 + 12 * Real.sqrt 6) * near.card)
    (hcard : (near.card : ℝ) ≤ 4 ^ τ * r ^ τ * ∑' i, ‖a i‖⁻¹ ^ τ)
    (hra : ∀ i, r ≠ ‖a i‖) {z : ℂ} (hz : ‖z‖ = r) (s : Finset ι) :
    Real.exp (-(((Real.log 2 + 12 * Real.sqrt 6 + p) * 4 ^ τ + p + 2) *
      (∑' i, ‖a i‖⁻¹ ^ τ) * r ^ τ)) ≤ ‖∏ i ∈ s, weierstrassFactor p (z / a i)‖ := by
  classical
  have hr0 : 0 ≤ r := hz ▸ norm_nonneg z
  have hfac (i : ι) := neg_log_norm_weierstrassFactor_div_le p hpτ hτp hr hz (hra i)
  have hpow : ∑ i ∈ s, (r / ‖a i‖) ^ τ ≤ r ^ τ * ∑' i, ‖a i‖⁻¹ ^ τ := by
    simp only [div_eq_mul_inv, Real.mul_rpow hr0 (inv_nonneg.mpr (norm_nonneg _)),
      ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ha.sum_le_tsum s fun i _ ↦ by positivity)
      (Real.rpow_nonneg hr0 τ)
  have hite : ∑ i ∈ s, (if a i ≠ 0 ∧ ‖a i‖ ≤ 4 * R then
      Real.posLog (1 / |1 - r / ‖a i‖|) + p else 0) ≤
        ∑ i ∈ near, (Real.posLog (1 / |1 - r / ‖a i‖|) + p) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi ↦ (hnear i).mpr (Finset.mem_filter.mp hi).2)
      fun i _ _ ↦ add_nonneg Real.posLog_nonneg (Nat.cast_nonneg p)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hite
  rw [norm_prod]
  calc
    _ ≤ Real.exp (-∑ i ∈ s, ((if a i ≠ 0 ∧ ‖a i‖ ≤ 4 * R then
          Real.posLog (1 / |1 - r / ‖a i‖|) + p else 0) + (p + 2) * (r / ‖a i‖) ^ τ)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff, Finset.sum_add_distrib, ← Finset.mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left hcard (by positivity :
        (0 : ℝ) ≤ Real.log 2 + 12 * Real.sqrt 6 + p), mul_le_mul_of_nonneg_left hpow
        (by positivity : (0 : ℝ) ≤ p + 2)]
    _ = ∏ i ∈ s, Real.exp (-((if a i ≠ 0 ∧ ‖a i‖ ≤ 4 * R then
          Real.posLog (1 / |1 - r / ‖a i‖|) + p else 0) + (p + 2) * (r / ‖a i‖) ^ τ)) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]
    _ ≤ ∏ i ∈ s, ‖weierstrassFactor p (z / a i)‖ := by
      refine Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) fun i _ ↦ ?_
      rw [← Real.exp_log (norm_pos_iff.mpr (hfac i).1), Real.exp_le_exp]
      linarith [(hfac i).2]

/-- **Cartan's good-circle estimate.** Let `p ≤ τ ≤ p + 1` and `∑' i, ‖a i‖⁻¹ ^ τ < ∞`. Every
interval `(R, 2 * R]` with `R > 0` contains a radius `r` on whose circle the genus-`p` primary
product satisfies `exp (-(C * r ^ τ)) ≤ ‖∏' i, E_p(z / a i)‖`, where
`C = ((log 2 + 12 * sqrt 6 + p) * 4 ^ τ + p + 2) * ∑' i, ‖a i‖⁻¹ ^ τ`.

Both bounds on `τ` are needed; take the single zero `a = 1`. For genus `0` and `τ = 2`, at
`z = r` we have `-log (1 - r) ≥ r > C * r ^ 2` once `2 * R < 1 / C`. For genus `1` and `τ = 0`,
at `z = -r` we have `-log ‖E_1 (-r)‖ = r - log (1 + r)`, which exceeds the constant `C` once `R`
is large. -/
theorem exists_mem_Ioc_forall_norm_eq_exp_neg_le_norm_tprod_weierstrassFactor_div {ι : Type*}
    (p : ℕ) {τ : ℝ} (hpτ : (p : ℝ) ≤ τ) (hτp : τ ≤ p + 1) {a : ι → ℂ}
    (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ τ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Ioc R (2 * R), ∀ z : ℂ, ‖z‖ = r →
      Real.exp (-(((Real.log 2 + 12 * Real.sqrt 6 + p) * 4 ^ τ + p + 2) *
        (∑' i, ‖a i‖⁻¹ ^ τ) * r ^ τ)) ≤ ‖∏' i, weierstrassFactor p (z / a i)‖ := by
  classical
  have hτ : 0 ≤ τ := (Nat.cast_nonneg p).trans hpτ
  set near := (ha.finite_setOf_ne_zero_norm_le hτ (4 * R)).toFinset
  have hnear (i : ι) : i ∈ near ↔ a i ≠ 0 ∧ ‖a i‖ ≤ 4 * R := Set.Finite.mem_toFinset _
  obtain ⟨r, hr, hrbad, hsum⟩ :=
    near.exists_mem_Ioc_notMem_sum_mul_posLog_one_div_abs_one_sub_div_le (fun _ ↦ 1)
      (fun i ↦ ‖a i‖) (fun _ _ ↦ zero_le_one) ((near.image fun i ↦ ‖a i‖).measure_zero _) hR
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hr0 : 0 < r := hR.trans hr.1
  have hra (i : ι) : r ≠ ‖a i‖ := by
    by_cases hi : i ∈ near
    · exact fun h ↦ hrbad (by simpa [h] using Finset.mem_image_of_mem (fun i ↦ ‖a i‖) hi)
    · rcases eq_or_ne (a i) 0 with h | h
      · simpa [h] using hr0.ne'
      · linarith [hr.2, lt_of_not_ge (not_and.mp ((hnear i).not.mp hi) h)]
  have hcard : (near.card : ℝ) ≤ 4 ^ τ * r ^ τ * ∑' i, ‖a i‖⁻¹ ^ τ := by
    refine (ha.card_le_rpow_mul_tsum hτ (by linarith) fun i hi ↦ (hnear i).mp hi).trans ?_
    rw [← Real.mul_rpow (by norm_num) hr0.le]
    gcongr
    linarith [hr.1]
  refine ⟨r, hr, fun z hz ↦ ?_⟩
  have hpartial := exp_neg_le_norm_prod_weierstrassFactor_div p hpτ hτp ha hr.2 hnear hsum hcard
    hra hz
  by_cases hm : Multipliable fun i ↦ weierstrassFactor p (z / a i)
  · exact ge_of_tendsto' hm.hasProd.norm hpartial
  · rw [tprod_eq_one_of_not_multipliable hm, norm_one, Real.exp_le_one_iff, neg_nonpos]
    have : 0 ≤ ∑' i, ‖a i‖⁻¹ ^ τ := tsum_nonneg fun i ↦ by positivity
    positivity

end Complex
