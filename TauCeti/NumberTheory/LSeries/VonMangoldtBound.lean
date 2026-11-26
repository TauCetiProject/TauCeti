/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# A reference bound for restricted von Mangoldt series

The sum of the norms of Dirichlet terms with coefficients dominated by the von Mangoldt
function is bounded by `-Re (ζ′/ζ)` at the real abscissa, even after restriction to any set
of indices. At `1 + 1/U` the unrestricted von Mangoldt sum differs from `U` by a quantity
that tends to Euler's constant, so the same `U` bounds all the restricted series for large `U`.
In particular this gives a common reference bound for the two outer ranges in Gaussian
estimates for primes in logarithmic windows.

The reference point and its use in the window argument are from `New.exists_prime_modEq_one_log_mem`
in [`Lib/Analytic/Primes.lean`][short-proof]. The estimate here uses the sign of the regular part
of `-ζ′/ζ` at `1`.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Primes.lean
-/

public section

open ArithmeticFunction Complex Filter
open scoped Topology

namespace TauCeti.LSeries

/-- On a real abscissa to the right of `1`, the von Mangoldt terms are nonnegative real
numbers. Their absolute sum is the negative real part of the logarithmic derivative of ζ. -/
theorem hasSum_norm_term_vonMangoldt {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n : ℕ ↦ ‖_root_.LSeries.term (fun k ↦ (Λ k : ℂ)) σ n‖)
      (-(logDeriv riemannZeta σ).re) := by
  have hs : 1 < (σ : ℂ).re := by simpa only [ofReal_re] using hσ
  have h := Complex.hasSum_re (LSeriesSummable_vonMangoldt hs).hasSum
  rw [← _root_.LSeries, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div,
    ← logDeriv_apply, neg_re] at h
  refine h.congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [_root_.LSeries.term_of_ne_zero hn, ← ofReal_natCast,
    ← ofReal_cpow (Nat.cast_nonneg n), ← ofReal_div, ofReal_re, norm_real,
    Real.norm_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))]

/-- At a complex abscissa `s` with `1 < Re s`, the restricted sum of absolute terms with
coefficients bounded by `Λ` is at most `-Re (ζ′/ζ)(Re s)`. The coefficient bound only needs to
hold on the retained positive indices. -/
theorem exists_hasSum_norm_term_le_neg_re_logDeriv_riemannZeta (a : ℕ → ℂ) (S : Set ℕ)
    {s : ℂ} (hs : 1 < s.re) (ha : ∀ n ∈ S, 0 < n → ‖a n‖ ≤ Λ n) :
    ∃ B, HasSum (fun n : S ↦ ‖_root_.LSeries.term a s n‖) B ∧
      B ≤ -(logDeriv riemannZeta s.re).re := by
  let g (n : ℕ) := ‖_root_.LSeries.term (fun k ↦ (Λ k : ℂ)) (s.re : ℂ) n‖
  have hg := hasSum_norm_term_vonMangoldt hs
  have hle (n : S) : ‖_root_.LSeries.term a s n‖ ≤ g n := by
    rcases Nat.eq_zero_or_pos n.val with hn | hn
    · simp [g, hn]
    calc
      _ ≤ ‖_root_.LSeries.term (fun k ↦ (Λ k : ℂ)) s n‖ :=
        _root_.LSeries.norm_term_le s (by
          simpa only [norm_real, Real.norm_of_nonneg vonMangoldt_nonneg] using ha n n.prop hn)
      _ ≤ g n := _root_.LSeries.norm_term_le_of_re_le_re _ (by simp) n
  have hgS := hg.summable.subtype (· ∈ S)
  have hf := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hgS
  refine ⟨_, hf.hasSum, (hf.tsum_le_tsum hle hgS).trans ?_⟩
  exact (hg.summable.tsum_subtype_le g S (fun _ ↦ norm_nonneg _)).trans_eq hg.tsum_eq

/-- At the real point `1 + 1/U`, the excess of `U` over the full von Mangoldt sum tends to
Euler's constant. In particular, the leading coefficient `1` in the reference bound is sharp. -/
theorem tendsto_sub_tsum_norm_term_vonMangoldt_one_add_inv :
    Tendsto (fun U : ℝ ↦ U - ∑' n : ℕ,
      ‖_root_.LSeries.term (fun k ↦ (Λ k : ℂ)) (1 + (U⁻¹ : ℝ)) n‖)
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  let F := DirichletCharacter.LFunctionTrivChar₁ 1
  have hF : AnalyticAt ℂ F 1 :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt 1
  have hcont : ContinuousAt (fun s : ℂ ↦ (logDeriv F s).re) 1 :=
    continuous_re.continuousAt.comp
      (hF.logDeriv (DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1)).continuousAt
  have hlim : Tendsto (fun U : ℝ ↦ (1 : ℂ) + (U⁻¹ : ℝ)) atTop (𝓝 1) := by
    simpa using (continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero).const_add
      (1 : ℂ)
  have h := hcont.tendsto.comp hlim
  rw [DirichletCharacter.logDeriv_LFunctionTrivChar₁_one_one, ofReal_re] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
  have hσ : 1 < (1 + U⁻¹ : ℝ) := lt_add_of_pos_right _ (inv_pos.mpr hU)
  have hs : 1 < ((1 : ℂ) + (U⁻¹ : ℝ)).re := by simpa using hσ
  have h1 : (1 : ℂ) + (U⁻¹ : ℝ) ≠ 1 := by
    intro he
    simp only [he, one_re, lt_irrefl] at hs
  have hres := TauCeti.logDeriv_riemannZeta_add_inv_sub_one h1
    (riemannZeta_ne_zero_of_one_le_re hs.le)
  have hreal := congrArg Complex.re hres
  simp only [add_sub_cancel_left, ← ofReal_inv, inv_inv, add_re, ofReal_re] at hreal
  rw [← ofReal_one, ← ofReal_add] at hreal
  simp only [Function.comp_apply, ← ofReal_one, ← ofReal_add]
  rw [(hasSum_norm_term_vonMangoldt hσ).tsum_eq]
  linarith only [hreal]

/-- For all sufficiently large `U`, the absolute Dirichlet sum at `1 + 1/U` is at most `U`
for all sets of indices and all coefficient sequences dominated on those indices by `Λ`.
The threshold is independent of the residue class, modulus, and truncation. -/
theorem eventually_exists_hasSum_norm_term_one_add_inv_le :
    ∀ᶠ U : ℝ in atTop, ∀ (a : ℕ → ℂ) (S : Set ℕ), (∀ n ∈ S, 0 < n → ‖a n‖ ≤ Λ n) →
      ∃ B, HasSum (fun n : S ↦ ‖_root_.LSeries.term a (1 + (U⁻¹ : ℝ)) n‖) B ∧ B ≤ U := by
  have hγ : 0 < Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  filter_upwards [tendsto_sub_tsum_norm_term_vonMangoldt_one_add_inv.eventually (Ioi_mem_nhds hγ),
    eventually_gt_atTop (0 : ℝ)] with U hlim hU a S ha
  have hσ : 1 < (1 + U⁻¹ : ℝ) := lt_add_of_pos_right _ (inv_pos.mpr hU)
  have hs : 1 < ((1 : ℂ) + (U⁻¹ : ℝ)).re := by simpa using hσ
  obtain ⟨B, hB, hle⟩ := exists_hasSum_norm_term_le_neg_re_logDeriv_riemannZeta a S hs ha
  rw [add_re, one_re, ofReal_re] at hle
  refine ⟨B, hB, hle.trans ?_⟩
  have h := (Set.mem_Ioi.mp hlim).le
  rwa [← ofReal_one, ← ofReal_add, (hasSum_norm_term_vonMangoldt hσ).tsum_eq, sub_nonneg] at h

end TauCeti.LSeries
