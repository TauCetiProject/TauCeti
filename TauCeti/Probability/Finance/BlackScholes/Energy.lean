/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Geometric.Integrable
public import TauCeti.Probability.Finance.BlackScholes.Predictable

/-!
# Expected square energy of the Black–Scholes delta hedges

For the stock `S_t = s exp ((μ - σ² / 2)t + σW_t)`, the Brownian gains coefficient of a
stock holding `a` is `σ S a`, not `a` alone. The call and put delta hedges, set to zero at and
after expiry, give predictable coefficients in `TauCeti.BrownianIntegrable`. Thus their
expected square energy is finite on the full horizon, including arbitrarily close to expiry,
where gamma can diverge. The result holds under any physical drift `μ`, not just `μ = r`.

The driving process must be predictable with the pre-Brownian laws; neither path continuity
nor increment independence from the filtration is needed. For filtered Brownian motion,
a continuous predictable version exists on the original raw filtration by
`IsFilteredPreBrownianReal.exists_isStronglyPredictable_isBrownianReal_indist`.
No usual-filtration assumption is required. The maturity slice is assigned zero explicitly;
no terminal derivative of the payoff is assumed.

These are expected-energy domain results, stronger than pathwise square integrability.
They do not construct a stochastic integral or assert self-financing or replication.
Together with the existing pathwise drift/bond integrability and value-process martingale
results, they supply the integrability inputs for verification of the delta hedge.

The proof uses the bounded-delta formulas and
`ProbabilityTheory.IsPreBrownianReal.brownianIntegrable_geometricBrownianMotion`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti TauCeti.Probability TauCeti.BlackScholes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {s σ K T : ℝ}

/-- The call hedge's Brownian gains coefficient `σ S C_s`, extended by zero at and after
maturity, is predictable and has finite expected square energy on every finite horizon.
The stock may have any physical drift. -/
theorem brownianIntegrable_call_hedge (hW : IsPreBrownianReal W P)
    (hp : IsStronglyPredictable ℱ W)
    (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (μ r : ℝ) :
    BrownianIntegrable ℱ P (fun t ω ↦ σ * geometricBrownianMotion s μ σ W t ω *
      (if (t : ℝ) < T then deriv (fun x ↦ callPrice x r σ K (T - t))
        (geometricBrownianMotion s μ σ W t ω) else 0)) := by
  have hS := hW.brownianIntegrable_geometricBrownianMotion hp s μ σ
  have hd := hS.isStronglyPredictable.deriv_callPrice_spot
    (r := r) (T := T) (fun t ω _ ↦ geometricBrownianMotion_pos hs μ σ W t ω) hK hσ
  refine ⟨(hS.isStronglyPredictable.const_mul σ).mul hd, fun U ↦ ?_⟩
  refine ((hS.memLp U).const_mul σ).mul
    (memLp_top_of_bound (hd.mono ℱ.predictable_le_prod).aestronglyMeasurable 1 ?_)
  exact Eventually.of_forall fun z ↦ by
    split_ifs with ht
    · have hdelta := deriv_callPrice_spot_mem_Ioo
        (r := r) (geometricBrownianMotion_pos hs μ σ W z.1 z.2) hK hσ (sub_pos.mpr ht)
      simpa only [Real.norm_eq_abs, abs_of_pos hdelta.1] using hdelta.2.le
    · simp

/-- The put hedge's Brownian gains coefficient `σ S P_s`, extended by zero at and after
maturity, is predictable and has finite expected square energy on every finite horizon.
No bound on gamma at expiry is needed. -/
theorem brownianIntegrable_put_hedge (hW : IsPreBrownianReal W P)
    (hp : IsStronglyPredictable ℱ W)
    (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (μ r : ℝ) :
    BrownianIntegrable ℱ P (fun t ω ↦ σ * geometricBrownianMotion s μ σ W t ω *
      (if (t : ℝ) < T then deriv (fun x ↦ putPrice x r σ K (T - t))
        (geometricBrownianMotion s μ σ W t ω) else 0)) := by
  have hS := hW.brownianIntegrable_geometricBrownianMotion hp s μ σ
  have hd := hS.isStronglyPredictable.deriv_putPrice_spot
    (r := r) (T := T) (fun t ω _ ↦ geometricBrownianMotion_pos hs μ σ W t ω) hK hσ
  refine ⟨(hS.isStronglyPredictable.const_mul σ).mul hd, fun U ↦ ?_⟩
  refine ((hS.memLp U).const_mul σ).mul
    (memLp_top_of_bound (hd.mono ℱ.predictable_le_prod).aestronglyMeasurable 1 ?_)
  exact Eventually.of_forall fun z ↦ by
    split_ifs with ht
    · have hdelta := deriv_putPrice_spot_mem_Ioo
        (r := r) (geometricBrownianMotion_pos hs μ σ W z.1 z.2) hK hσ (sub_pos.mpr ht)
      rw [Real.norm_eq_abs, abs_of_neg hdelta.2]
      linarith [hdelta.1]
    · simp

end ProbabilityTheory.IsPreBrownianReal
