/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.FunctionalEquation
public import TauCeti.NumberTheory.LFunctions.GammaFactor.Vertical
import TauCeti.NumberTheory.LFunctions.GammaFactor.Order
import TauCeti.NumberTheory.LSeries.Continuity

/-!
# The two edges of the convexity strip

For an analytic L-function record `d` with conductor `N`, gamma factor `γ`, root number `ε` and
continued function `L = d.continuedL`, this file proves the two edge estimates behind the
convexity bound on the strip `-δ ≤ Re s ≤ 1 + δ`.

* **The right edge.** With Dirichlet agreement, `L` is the Dirichlet series `∑ a(k) k ^ (-s)` on
  `Re s > 1`, so for `σ > 1` it is bounded on the closed half-plane `σ ≤ Re s` by
  `∑ ‖a(k)‖ k ^ (-σ)` (`HasDirichletAgreement.norm_continuedL_le`); under
  `HasAverageCoefficientGrowth` this sum is finite for every `σ > 1`. When it diverges, `LSeries`
  takes the value `0` on the strip `1 < Re s < σ`, so `L` vanishes on an open set, hence
  identically, and the bound holds with both sides `0`.
* **The reflection.** Solving the functional equation of `L` against the dual record gives
  `L(s) = ε N ^ (1/2 - s) (γ^∨(1 - s) / γ(s)) L^∨(1 - s)` at every point `s` such that `γ^∨` is
  regular and `L^∨` is analytic at `1 - s` (`HasFunctionalEquation.continuedL_eq_of_analyticAt`).
  This includes the poles of `γ`, where the quotient takes the value `0`.
* **The left edge.** On the line `Re s = -δ`, `δ > 0`, the reflection evaluates the dual
  function on the right edge `Re (1 - s) = 1 + δ`, and the dual coefficients have the same
  norms. With the conductor-uniform estimate
  `exists_norm_conductor_cpow_mul_dual_gammaFactor_div_neg_line_le_analyticConductorAt_rpow` for
  the archimedean factor, this gives
  `‖L(s)‖ ≤ C (∑ ‖a(k)‖ k ^ (-(1 + δ))) 𝔮(s) ^ (1/2 + δ)` with `𝔮 = d.analyticConductorAt`
  (`exists_norm_continuedL_neg_line_le_analyticConductorAt_rpow`). The constant `C` depends only
  on `δ`, the degree, a bound for the gamma shifts and their margin in the right half-plane; it
  does not depend on the conductor or on the record.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.2.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (1986), §5.1.
-/

public section

open Complex Filter Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable {d : AnalyticLFunctionData}

/-- If the Dirichlet series of a record with Dirichlet agreement does not converge absolutely at
some real `σ > 1`, then `LSeries` takes the value `0` on the open strip `1 < Re s < σ`, so the
continued function vanishes on an open set and hence everywhere. -/
private theorem HasDirichletAgreement.continuedL_eq_zero_of_not_LSeriesSummable
    (hD : d.HasDirichletAgreement) {σ : ℝ} (hσ : 1 < σ) (hsum : ¬LSeriesSummable d.coeff σ)
    (s : ℂ) : d.continuedL s = 0 := by
  by_cases hm : Meromorphic d.completed
  swap
  · simp [continuedL_of_not_meromorphic hm]
  have hstrip : ∀ z : ℂ, 1 < z.re → z.re < σ → d.continuedL z = 0 := fun z h1 h2 ↦ by
    rw [hD.continuedL_eq_LSeries hm h1, LSeries]
    exact tsum_eq_zero_of_not_summable fun h ↦
      hsum (LSeriesSummable.of_re_le_re (by simpa using h2.le) h)
  have hU : {z : ℂ | 1 < z.re ∧ z.re < σ} ∈ 𝓝 (((1 + σ) / 2 : ℝ) : ℂ) :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).mem_nhds
      ⟨by simp only [Set.mem_ofPred_eq, ofReal_re]; linarith,
        by simp only [Set.mem_ofPred_eq, ofReal_re]; linarith⟩
  have htop : meromorphicOrderAt d.continuedL (((1 + σ) / 2 : ℝ) : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds hU] with z hz using hstrip z hz.1 hz.2
  have hs : meromorphicOrderAt d.continuedL s = ⊤ := by
    by_contra h
    exact d.meromorphic_continuedL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ s) (Set.mem_univ _) h htop
  exact continuedL_eq_of_eventuallyEq (g := fun _ ↦ 0) continuousAt_const
    (meromorphicOrderAt_eq_top_iff.mp hs)

/-- **The right edge of the convexity strip.** For a record with Dirichlet agreement and real
`σ > 1`, the continued function is bounded on the closed half-plane `σ ≤ Re s` by the sum
`∑ ‖a(k)‖ k ^ (-σ)` of the norms of the terms of its Dirichlet series at `σ`. If that series
diverges, both sides vanish. -/
theorem HasDirichletAgreement.norm_continuedL_le (hD : d.HasDirichletAgreement) {σ : ℝ}
    (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖d.continuedL s‖ ≤ ∑' k, ‖LSeries.term d.coeff σ k‖ := by
  by_cases hsum : LSeriesSummable d.coeff σ
  · by_cases hm : Meromorphic d.completed
    · rw [hD.continuedL_eq_LSeries hm (hσ.trans_le hs)]
      exact hsum.norm_LSeries_le (by simpa using hs)
    · rw [continuedL_of_not_meromorphic hm, Pi.zero_apply, norm_zero]
      exact tsum_nonneg fun _ ↦ norm_nonneg _
  · rw [hD.continuedL_eq_zero_of_not_LSeriesSummable hσ hsum s, norm_zero]
    exact tsum_nonneg fun _ ↦ norm_nonneg _

/-- **The functional equation solved for the continued function.** If the dual gamma factor is
regular at `1 - s` and the dual continued function is analytic there, then
`L(s) = ε N ^ (1/2 - s) (γ^∨(1 - s) / γ(s)) L^∨(1 - s)`.
No regularity of `γ` at `s` is assumed: at a pole of `γ` the quotient takes Mathlib's value `0`,
and so does `L(s)`. -/
theorem HasFunctionalEquation.continuedL_eq_of_analyticAt (hfe : d.HasFunctionalEquation)
    {s : ℂ} (hγ : d.dual.gammaFactor (1 - s) ≠ 0)
    (ha : AnalyticAt ℂ d.dual.continuedL (1 - s)) :
    d.continuedL s = d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ (1 / 2 - s) *
      (d.dual.gammaFactor (1 - s) / d.gammaFactor s) * d.dual.continuedL (1 - s) := by
  have hquot : (fun z ↦ d.dual.gammaFactor (1 - z) / d.gammaFactor z) =
      fun z ↦ d.dual.gammaFactor (1 - z) * d.invGammaFactor z := by
    funext z
    rw [invGammaFactor_def, div_eq_mul_inv]
  have h1 : AnalyticAt ℂ (fun z ↦ d.dual.gammaFactor (1 - z) / d.gammaFactor z) s := by
    rw [hquot]
    exact ((d.dual.analyticAt_gammaFactor hγ).comp (by fun_prop)).mul
      (d.analyticAt_invGammaFactor s)
  have h2 : AnalyticAt ℂ (fun z ↦ d.dual.continuedL (1 - z)) s := ha.comp (by fun_prop)
  have hg : ContinuousAt (fun z ↦ d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ (1 / 2 - z) *
      (d.dual.gammaFactor (1 - z) / d.gammaFactor z) * d.dual.continuedL (1 - z)) s :=
    (((analyticAt_const.mul (d.analyticAt_conductor_cpow (g := fun z ↦ 1 / 2 - z)
      (by fun_prop))).mul h1).mul h2).continuousAt
  refine continuedL_eq_of_eventuallyEq hg ?_
  filter_upwards [hfe.gammaFactor_mul_continuedL_eventuallyEq s,
    d.eventually_gammaFactor_ne_zero s] with z hz hγz
  rw [← mul_div_cancel_left₀ (d.continuedL z) hγz, hz]
  ring

/-- **The left edge of the convexity strip, uniformly in the conductor.** Fix `δ > 0`, a degree
`n`, a bound `M` for the gamma shifts and a margin `ε > 0` keeping the reflected shifts inside the
right half-plane (`ε ≤ 1 + δ + Re μ`). There is `C > 0` such that every record with these data,
Dirichlet agreement and a functional equation satisfies
`‖L(s)‖ ≤ C (∑ ‖a(k)‖ k ^ (-(1 + δ))) 𝔮(s) ^ (1/2 + δ)` on the line `Re s = -δ`, where
`𝔮 = d.analyticConductorAt` and `a = d.coeff`. -/
theorem exists_norm_continuedL_neg_line_le_analyticConductorAt_rpow {δ : ℝ} (hδ : 0 < δ)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (M : ℝ) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ ε ≤ 1 + δ + μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ ε ≤ 1 + δ + ν.re) →
      d.HasDirichletAgreement → d.HasFunctionalEquation →
      ∀ s : ℂ, s.re = -δ →
        ‖d.continuedL s‖ ≤ C * (∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖) *
          d.analyticConductorAt s ^ (1 / 2 + δ) := by
  obtain ⟨C, hC, hfactor⟩ :=
    exists_norm_conductor_cpow_mul_dual_gammaFactor_div_neg_line_le_analyticConductorAt_rpow
      δ hε n M
  refine ⟨C, hC, fun d hd hR hC' hD hfe s hs ↦ ?_⟩
  have hs' : ((-δ : ℝ) : ℂ) + (s.im : ℂ) * I = s := by
    apply Complex.ext <;> simp [hs]
  have hq := hfactor d hd hR hC' s.im
  rw [hs'] at hq
  have hγ : d.dual.gammaFactor (1 - s) ≠ 0 := by
    refine d.dual.gammaFactor_ne_zero_of_forall_re_add_pos (fun μ hμ ↦ ?_) (fun ν hν ↦ ?_)
    · rw [dual_gammaR] at hμ
      obtain ⟨μ₀, hμ₀, rfl⟩ := Multiset.mem_map.mp hμ
      have := (hR μ₀ hμ₀).2
      simp only [sub_re, one_re, hs, conj_re]
      linarith
    · rw [dual_gammaC] at hν
      obtain ⟨ν₀, hν₀, rfl⟩ := Multiset.mem_map.mp hν
      have := (hC' ν₀ hν₀).2
      simp only [sub_re, one_re, hs, conj_re]
      linarith
  have h1s : (1 - s).re = 1 + δ := by
    simp only [sub_re, one_re, hs]
    ring
  have ha : AnalyticAt ℂ d.dual.continuedL (1 - s) :=
    hD.dual.analyticAt_continuedL (by rw [h1s]; linarith)
  have hB : ‖d.dual.continuedL (1 - s)‖ ≤ ∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖ := by
    simpa only [LSeries.norm_term_eq, dual_coeff, Complex.norm_conj] using
      hD.dual.norm_continuedL_le (σ := 1 + δ) (by linarith) h1s.ge
  calc ‖d.continuedL s‖
      = ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
          (d.dual.gammaFactor (1 - s) / d.gammaFactor s)‖ * ‖d.dual.continuedL (1 - s)‖ := by
        rw [hfe.continuedL_eq_of_analyticAt hγ ha]
        simp only [norm_mul, hfe.norm_rootNumber, one_mul]
    _ ≤ C * d.analyticConductorAt s ^ (1 / 2 + δ) *
          ∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖ :=
        mul_le_mul hq hB (norm_nonneg _)
          (mul_nonneg hC.le (Real.rpow_nonneg (d.analyticConductorAt_pos s).le _))
    _ = C * (∑' k, ‖LSeries.term d.coeff (1 + δ : ℝ) k‖) *
          d.analyticConductorAt s ^ (1 / 2 + δ) := by
        ring

end TauCeti.LFunctions.AnalyticLFunctionData
