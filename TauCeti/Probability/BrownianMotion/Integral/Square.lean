/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Integration
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.LpLimit
import TauCeti.Probability.Process.TimeIntegral

/-!
# Square compensation for Brownian integrals

The square of an elementary Brownian integral, minus its elapsed pathwise square
energy, is a martingale. The heights are square integrable and known at the left
endpoints; they need not be bounded or independent of one another. This is the
elementary square decomposition used to identify the bracket of the completed integral,
and passing to the `L²` limit yields the square-compensation martingale property
`martingale_sq_sub_integral_of_ae_eq_l2Integral` for any strongly adapted modification of the
completed `L²` integral of a `BrownianIntegrable` integrand.

Only filtration-relative pre-Brownian laws are needed, not path continuity or usual
conditions on the filtration. Empty grids and repeated dates are allowed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Springer, 1991, §3.2, Proposition 3.2.10.
-/

public section

open Filter MeasureTheory ProbabilityTheory Finset Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ξ : Ω → ℝ} {s v : ℝ≥0}

/-- The square of a Brownian position held on `(s,v]`, compensated by its elapsed
square energy, is a true martingale. Only the second moment of the position is needed. -/
theorem martingale_sq_mul_sub_min_sub (hW : IsFilteredPreBrownianReal ℱ W P) (hsv : s ≤ v)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    Martingale (fun t ω ↦ (ξ ω * (W (min v t) ω - W (min s t) ω)) ^ 2 -
      ξ ω ^ 2 * (↑(min v t) - ↑(min s t))) ℱ P := by
  have := hW.isGaussianProcess.isProbabilityMeasure
  -- First center the Brownian square at s. Subtracting the cross term is essential:
  -- the difference of the two compensated marginal squares alone is not this square.
  have hcross := hW.martingale_mul_sub_min hsv (hW.adapted s).stronglyMeasurable
    (hW.integrable_eval s)
  have hcenter : Martingale (fun t ω ↦
      (W (min v t) ω - W (min s t) ω) ^ 2 -
        (↑(min v t) - ↑(min s t))) ℱ P := by
    convert ((hW.martingale_sq_sub.const_min v).sub
      (hW.martingale_sq_sub.const_min s)).sub (hcross.smul 2) using 1
    ext t ω
    by_cases hst : s ≤ t
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, min_eq_left hst]
      ring
    · have hts : t ≤ s := (not_le.mp hst).le
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, min_eq_right hts,
        min_eq_right (hts.trans hsv), sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0),
        Pi.zero_apply]
  have hproduct : ∀ t, Integrable (fun ω ↦ ξ ω ^ 2 *
      ((W (min v t) ω - W (min s t) ω) ^ 2 -
        (↑(min v t) - ↑(min s t)))) P := by
    intro t
    by_cases hst : s ≤ t
    · have hi := (hW.indepFun_sub (le_min hsv hst) hξ.measurable).comp
        (measurable_id.pow_const 2)
        ((measurable_id.pow_const 2).sub
          (measurable_const (a := (↑(min v t) - (s : ℝ)))))
      simpa only [Function.comp_apply, id_eq, min_eq_left hst, Pi.mul_def, Pi.sub_def] using
        hi.integrable_mul hξ₂.integrable_sq
          ((hW.integrable_pow_sub s (min v t) 2).sub (integrable_const _))
    · have hts : t ≤ s := (not_le.mp hst).le
      simp only [min_eq_right hts, min_eq_right (hts.trans hsv), sub_self,
        zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact integrable_zero _ _ _
  have h := hcenter.mul_left_of_eq_zero (r := s) (fun t ht ↦ by
    ext ω
    simp [min_eq_right ht, min_eq_right (ht.trans hsv)]) (hξ.pow 2) hproduct
  convert h using 1
  ext t ω
  simp only [Pi.mul_apply, Pi.pow_apply]
  ring

/-- **Elementary Brownian square decomposition.** Squared elementary gains minus the
sum of squared heights times elapsed interval lengths form a true martingale. The
compensator is random pathwise energy, not its expectation. The process is defined
at all observation times, including times inside trading intervals. -/
theorem martingale_sq_simpleGains_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    Martingale (fun t ω ↦ Finance.simpleGains τ n a W t ω ^ 2 -
      ∑ i ∈ range n, a i ω ^ 2 * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) ℱ P := by
  have := hW.isGaussianProcess.isProbabilityMeasure
  induction n with
  | zero =>
    simpa only [Finance.simpleGains_def, sum_range_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero, Pi.zero_def] using (martingale_zero ℝ ℱ P)
  | succ n ih =>
    have hτn : MonotoneOn τ (Set.Iic n) := hτ.mono (Iic_subset_Iic.mpr n.le_succ)
    have han i (hi : i < n) := ha i (hi.trans n.lt_succ_self)
    have han₂ i (hi : i < n) := ha₂ i (hi.trans n.lt_succ_self)
    have hsv : τ n ≤ τ (n + 1) := hτ (by simp) (by simp) n.le_succ
    have hprev := ih hτn han han₂
    -- The new cross term uses the gains already realized at the left endpoint.
    -- Its height is L¹ by Cauchy–Schwarz, and Brownian independence suffices thereafter.
    have hknown : StronglyMeasurable[ℱ (τ n)] (Finance.simpleGains τ n a W (τ n)) :=
      Finance.stronglyAdapted_simpleGains hτn han hW.adapted.stronglyAdapted (τ n)
    have hprev₂ := hW.memLp_simpleGains hτn han han₂ (τ n)
    have hcross := hW.martingale_mul_sub_min hsv (hknown.mul (ha n n.lt_succ_self))
      (hprev₂.integrable_mul (ha₂ n n.lt_succ_self))
    have hnext := hW.martingale_sq_mul_sub_min_sub hsv (ha n n.lt_succ_self)
      (ha₂ n n.lt_succ_self)
    convert (hprev.add hnext).add (hcross.smul 2) using 1
    ext t ω
    have hgain : Finance.simpleGains τ (n + 1) a W t ω =
        Finance.simpleGains τ n a W t ω +
          a n ω * (W (min (τ (n + 1)) t) ω - W (min (τ n) t) ω) := by
      simp only [Finance.simpleGains_def, sum_range_succ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    rw [hgain, sum_range_succ]
    by_cases hnt : τ n ≤ t
    · rw [Finance.simpleGains_of_ge hτn hnt]
      ring
    · have htn : t ≤ τ n := (not_le.mp hnt).le
      simp only [min_eq_right htn, min_eq_right (htn.trans hsv), sub_self, mul_zero]
      ring

/-- **Brownian square-compensation martingale.** For any `BrownianIntegrable` integrand `H` and
strongly adapted modification `I` of `l2Integral`, `I_t² - ∫_{(0, t]} H_s² ds` is a true
martingale on the original raw filtration. -/
theorem martingale_sq_sub_integral_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI_adapt : StronglyAdapted ℱ I)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, _, _, hτ, ha, _, ha₂, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  let M (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 -
      ∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t
  have hM (m : ℕ) : Martingale (M m) ℱ P := by
    convert hW.martingale_sq_simpleGains_sub (hτ m).monotoneOn (ha m) (ha₂ m) using 1
    ext t ω; dsimp only [M]
    rw [Finance.integral_sq_simpleHolding_timeMeasure (hτ m).monotoneOn t ω]
  have hcomp_adapt : StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) := by
    simpa only [sq] using (hH.isStronglyPredictable.mul
      hH.isStronglyPredictable).isStronglyProgressive.integral_timeMeasure.stronglyAdapted
  refine martingale_of_tendsto_eLpNorm_one hM (fun t ↦ ((hI_adapt t).pow 2).sub (hcomp_adapt t))
    fun t ↦ ?_
  have hG_lim : Tendsto (fun m ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) 1 P) atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_one_sq_sub_sq (hW.memLp_of_ae_eq_l2Integral hH (hI t)).eLpNorm_ne_top
      (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
        (fun _ ↦ hH) (fun _ ↦ hI t) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (herr t))
  have hA_lim : Tendsto (fun m ↦ eLpNorm
      (fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
        ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (TauCeti.tendsto_eLpNorm_one_sq_sub_sq (hH.memLp_timeMeasure t).eLpNorm_ne_top (herr t))
      (fun _ ↦ bot_le) fun m ↦ ?_
    have hS := TauCeti.brownianIntegrable_simpleHolding (ha m) (ha₂ m)
    have hdiff_sm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦
        Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 ^ 2 - Function.uncurry H p ^ 2) :=
      ((hS.isStronglyPredictable.pow 2).sub (hH.isStronglyPredictable.pow 2)).mono
        ℱ.predictable_le_prod
    have hS_adapt : StronglyAdapted ℱ
        (fun t ω ↦ ∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) := by
      simpa only [sq] using (hS.isStronglyPredictable.mul
        hS.isStronglyPredictable).isStronglyProgressive.integral_timeMeasure.stronglyAdapted
    have hlhs_m : AEStronglyMeasurable
        (fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t) P :=
      (((hS_adapt t).sub (hcomp_adapt t)).mono (ℱ.le t)).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_eNorm hlhs_m,
      eLpNorm_one_eq_lintegral_eNorm hdiff_sm.aestronglyMeasurable,
      lintegral_prod_symm _ hdiff_sm.eNorm.aemeasurable]
    refine lintegral_mono_ae ?_
    filter_upwards [hS.locallyBrownianIntegrable.ae_memLp,
      hH.locallyBrownianIntegrable.ae_memLp] with ω hSω hHω
    rw [← integral_sub
      (by simpa [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hSω t).integrable_sq)
      (by simpa [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hHω t).integrable_sq)]
    exact eNorm_integral_le_lintegral_eNorm _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hG_lim.add hA_lim) (fun _ ↦ bot_le) fun m ↦ ?_
  have htri : (M m t - fun ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) =
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) -
        fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t := by ext ω; simp [M]; ring
  rw [htri]; exact eLpNorm_sub_le le_rfl

end TauCeti.Probability.IsFilteredPreBrownianReal
