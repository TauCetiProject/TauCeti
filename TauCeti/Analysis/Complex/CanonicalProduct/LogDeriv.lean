/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.Convergence
public import TauCeti.Analysis.Normed.Field.Rational
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Paired logarithmic derivatives of genus-one products

The logarithmic derivative of `E₁(a z)` is `-a² z / (1 - a z)`. This cancels the
linear contribution, so weighted square summability of the slopes gives absolute
convergence and uniform convergence on compact sets of the paired rational series.
Off the product's roots, the sum equals its logarithmic derivative.

The rational family uses total division, including at its poles. Its uniform convergence on
all compact sets concerns the tails of this family; the logarithmic-derivative identity is
asserted only where the product is nonzero. Finite singular terms do not affect tail convergence.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Complex Filter Metric Topology
open scoped BigOperators

namespace Complex

variable {ι : Type*} (a : ι → ℂ) (ha : Summable (fun i ↦ ‖a i‖ ^ 2))

include ha

private theorem exists_summable_logDerivWeierstrassFactorOneMul_majorant
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ u : ι → ℝ, Summable u ∧ ∀ᶠ i in cofinite, ∀ z ∈ K,
      ‖logDerivWeierstrassFactorOneMul (a i) z‖ ≤ u i := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let C : ℝ := max M 1
  have hC : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  refine ⟨fun i ↦ (2 * C) * ‖a i‖ ^ 2, ha.mul_left _, ?_⟩
  have he : ∀ᶠ i in cofinite, ‖a i‖ ^ 2 ≤ ((2 * C) ^ 2 + 1)⁻¹ :=
    ha.tendsto_cofinite_zero.eventually (ge_mem_nhds (by positivity))
  filter_upwards [he] with i hi z hz
  have hzC : ‖z‖ ≤ C := (hM z hz).trans (le_max_left _ _)
  have hsmall : ‖a i‖ * (2 * C) ≤ 1 := by
    have hp := mul_le_mul_of_nonneg_right hi (sq_nonneg (2 * C))
    have hp' : (‖a i‖ * (2 * C)) ^ 2 ≤ 1 := by
      calc
        _ = (‖a i‖ ^ 2) * (2 * C) ^ 2 := by ring
        _ ≤ ((2 * C) ^ 2 + 1)⁻¹ * (2 * C) ^ 2 := hp
        _ ≤ 1 := by
          rw [inv_mul_le_iff₀ (by positivity)]
          linarith
    nlinarith [mul_nonneg (norm_nonneg (a i)) (show 0 ≤ 2 * C by positivity)]
  have hzsmall : ‖a i * z‖ ≤ 1 / 2 := by
    rw [norm_mul]
    have ht := mul_le_mul_of_nonneg_left hzC (norm_nonneg (a i))
    nlinarith
  exact (TauCeti.norm_neg_sq_mul_div_one_sub_mul_le hzsmall).trans (by gcongr)

/-- The paired rational terms are absolutely summable at every point, using total division. -/
theorem summable_norm_logDerivWeierstrassFactorOneMul (z : ℂ) :
    Summable (fun i ↦ ‖logDerivWeierstrassFactorOneMul (a i) z‖) := by
  obtain ⟨u, hu, hb⟩ := exists_summable_logDerivWeierstrassFactorOneMul_majorant a ha
    (isCompact_singleton (x := z))
  apply hu.of_norm_bounded_eventually
  filter_upwards [hb] with i hi
  simpa only [Real.norm_eq_abs, abs_norm] using hi z (Set.mem_singleton z)

/-- The paired rational series converges uniformly on every compact set, using total division. -/
theorem hasSumUniformlyOn_logDerivWeierstrassFactorOneMul {K : Set ℂ} (hK : IsCompact K) :
    HasSumUniformlyOn (fun i z ↦ logDerivWeierstrassFactorOneMul (a i) z)
      (fun z ↦ ∑' i, logDerivWeierstrassFactorOneMul (a i) z) K := by
  obtain ⟨u, hu, hb⟩ := exists_summable_logDerivWeierstrassFactorOneMul_majorant a ha hK
  exact HasSumUniformlyOn.of_norm_le_summable_eventually hu hb

/-- The paired rational series converges locally uniformly on the plane, using total division. -/
theorem hasSumLocallyUniformlyOn_logDerivWeierstrassFactorOneMul :
    HasSumLocallyUniformlyOn (fun i z ↦ logDerivWeierstrassFactorOneMul (a i) z)
      (fun z ↦ ∑' i, logDerivWeierstrassFactorOneMul (a i) z) Set.univ := by
  apply hasSumLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact hasSumUniformlyOn_logDerivWeierstrassFactorOneMul a ha hK

end Complex

namespace Complex

private theorem logDeriv_weierstrassFactorOne_mul_pow (a z : ℂ) (m : ℕ) :
    logDeriv (fun w ↦ weierstrassFactorOne (a * w) ^ m) z =
      (m : ℂ) * (logDerivWeierstrassFactorOneMul a z) := by
  rw [logDeriv_fun_pow (by fun_prop), logDeriv_weierstrassFactorOne_mul]

variable {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
  (hm : Summable (fun i ↦ (m i : ℝ) * ‖a i‖ ^ 2))

include hm

/-- The paired rational terms with natural multiplicities are absolutely summable. -/
theorem summable_norm_natCast_mul_logDerivWeierstrassFactorOneMul (z : ℂ) :
    Summable (fun i ↦ ‖(m i : ℂ) * (logDerivWeierstrassFactorOneMul (a i) z)‖) := by
  have hs := (summable_norm_logDerivWeierstrassFactorOneMul (fun p : Σ i, Fin (m i) ↦ a p.1)
    ((TauCeti.summable_sigma_fin_iff (fun i ↦ sq_nonneg ‖a i‖) m).mpr hm) z).sigma
  simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, norm_mul, norm_natCast] using hs

private theorem tsum_natCast_mul_logDerivWeierstrassFactorOneMul_eq_sigma (z : ℂ) :
    (∑' i, (m i : ℂ) * (logDerivWeierstrassFactorOneMul (a i) z)) =
      ∑' p : Σ i, Fin (m i), logDerivWeierstrassFactorOneMul (a p.1) z := by
  have hs := (summable_norm_logDerivWeierstrassFactorOneMul (fun p : Σ i, Fin (m i) ↦ a p.1)
    ((TauCeti.summable_sigma_fin_iff (fun i ↦ sq_nonneg ‖a i‖) m).mpr hm) z).of_norm
  rw [hs.tsum_sigma]
  simp

/-- The paired rational series with natural multiplicities converges uniformly on compact sets. -/
theorem hasSumUniformlyOn_natCast_mul_logDerivWeierstrassFactorOneMul
    {K : Set ℂ} (hK : IsCompact K) :
    HasSumUniformlyOn (fun i z ↦ (m i : ℂ) * (logDerivWeierstrassFactorOneMul (a i) z))
      (fun z ↦ ∑' i, (m i : ℂ) * (logDerivWeierstrassFactorOneMul (a i) z)) K := by
  classical
  have ht : Tendsto (fun s : Finset ι ↦ s.sigma (fun i ↦ Finset.univ : ∀ i, Finset (Fin (m i))))
      atTop atTop := by
    refine tendsto_atTop.mpr fun t ↦ eventually_atTop.mpr ⟨t.image Sigma.fst, ?_⟩
    intro s hs p hp
    exact Finset.mem_sigma.mpr ⟨hs (Finset.mem_image.mpr ⟨p, hp, rfl⟩), Finset.mem_univ _⟩
  have h0 := HasSumUniformlyOn.tendstoUniformlyOn
    (hasSumUniformlyOn_logDerivWeierstrassFactorOneMul (fun p : Σ i, Fin (m i) ↦ a p.1)
      ((TauCeti.summable_sigma_fin_iff (fun i ↦ sq_nonneg ‖a i‖) m).mpr hm) hK)
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  intro u hu
  filter_upwards [ht.eventually (h0 u hu)] with s hs z hz
  have hsz := hs z hz
  simpa only [← tsum_natCast_mul_logDerivWeierstrassFactorOneMul_eq_sigma a m hm,
    Finset.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsz

/-- The weighted paired rational series converges locally uniformly on the plane. -/
theorem hasSumLocallyUniformlyOn_natCast_mul_logDerivWeierstrassFactorOneMul :
    HasSumLocallyUniformlyOn (fun i z ↦ (m i : ℂ) * (logDerivWeierstrassFactorOneMul (a i) z))
      (fun z ↦ ∑' i, (m i : ℂ) * (logDerivWeierstrassFactorOneMul (a i) z)) Set.univ := by
  apply hasSumLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact hasSumUniformlyOn_natCast_mul_logDerivWeierstrassFactorOneMul a m hm hK

/-- Off the roots, the logarithmic derivative is the absolutely convergent weighted paired
series. -/
theorem logDeriv_tprod_weierstrassFactorOne_pow {z : ℂ}
    (hz : ∀ i, m i ≠ 0 → a i * z ≠ 1) :
    logDeriv (fun w ↦ ∏' i, weierstrassFactorOne (a i * w) ^ m i) z =
      ∑' i, (m i : ℂ) * (logDerivWeierstrassFactorOneMul (a i) z) := by
  have hne : ∀ i, weierstrassFactorOne (a i * z) ^ m i ≠ 0 := by
    intro i
    by_cases hmi : m i = 0
    · simp [hmi]
    · apply pow_ne_zero
      intro hzero
      exact hz i hmi (weierstrassFactorOne_eq_zero_iff.mp hzero)
  have hp : (∏' i, weierstrassFactorOne (a i * z) ^ m i) ≠ 0 := by
    rw [ne_eq, tprod_weierstrassFactorOne_pow_eq_zero_iff a m hm]
    rintro ⟨i, hi, hzero⟩
    exact hz i hi hzero
  have hs : Summable (fun i ↦ logDeriv (fun w ↦ weierstrassFactorOne (a i * w) ^ m i) z) := by
    simpa only [logDeriv_weierstrassFactorOne_mul_pow] using
      (summable_norm_natCast_mul_logDerivWeierstrassFactorOneMul a m hm z).of_norm
  have hd : ∀ i, DifferentiableOn ℂ (fun w ↦ weierstrassFactorOne (a i * w) ^ m i) Set.univ := by
    intro i
    fun_prop
  have ht := logDeriv_tprod_eq_tsum (f := fun i w ↦ weierstrassFactorOne (a i * w) ^ m i)
    isOpen_univ (Set.mem_univ z) hne hd hs
    (hasProdLocallyUniformlyOn_weierstrassFactorOne_pow a m hm).multipliableLocallyUniformlyOn hp
  simpa only [logDeriv_weierstrassFactorOne_mul_pow] using ht

end Complex

