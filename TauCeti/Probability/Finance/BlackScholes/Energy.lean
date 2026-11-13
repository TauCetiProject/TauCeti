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
an almost-surely continuous predictable indistinguishable version exists on the original raw
filtration by
`TauCeti.Probability.IsFilteredPreBrownianReal.exists_isStronglyPredictable_isBrownianReal_indist`.
No usual-filtration assumption is required. The maturity slice is assigned zero explicitly;
no terminal derivative of the payoff is assumed.

These are expected-energy domain results, stronger than pathwise square integrability.
They do not construct a stochastic integral or assert self-financing or replication.
Together with the existing pathwise drift/bond integrability and value-process martingale
results, they supply the integrability inputs for verification of the delta hedge.

The general results `TauCeti.BrownianIntegrable.mul_deriv_callPrice_spot` and
`TauCeti.BrownianIntegrable.mul_deriv_putPrice_spot` require only a positive spot process in
the expected-energy domain and allow any constant prefactor. They use the bounded-delta
formulas and `TauCeti.BrownianIntegrable.mul_of_bound`. The geometric Brownian specializations
then use `ProbabilityTheory.IsPreBrownianReal.brownianIntegrable_geometricBrownianMotion`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

open TauCeti TauCeti.Probability TauCeti.BlackScholes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {S W : ℝ≥0 → Ω → ℝ} {s σ K T : ℝ}

namespace TauCeti.BrownianIntegrable

/-- Multiplying an expected-square-integrable positive spot process by the zero-extended
call delta and any constant preserves finite expected square energy. -/
theorem mul_deriv_callPrice_spot (hS : BrownianIntegrable ℱ P S)
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω)
    (hK : 0 < K) (hσ : σ ≠ 0) (r c : ℝ) :
    BrownianIntegrable ℱ P (fun t ω ↦ c * S t ω *
      (if (t : ℝ) < T then deriv (fun x ↦ callPrice x r σ K (T - t))
        (S t ω) else 0)) := by
  have hd := hS.isStronglyPredictable.deriv_callPrice_spot (r := r) hpos hK hσ
  refine (hS.const_mul c).mul_of_bound hd 1 fun t ω ↦ ?_
  split_ifs with ht
  · have hdelta := deriv_callPrice_spot_mem_Ioo
      (r := r) (hpos t ω ht) hK hσ (sub_pos.mpr ht)
    simpa only [Real.norm_eq_abs, abs_of_pos hdelta.1] using hdelta.2.le
  · simp

/-- Multiplying an expected-square-integrable positive spot process by the zero-extended
put delta and any constant preserves finite expected square energy. -/
theorem mul_deriv_putPrice_spot (hS : BrownianIntegrable ℱ P S)
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω)
    (hK : 0 < K) (hσ : σ ≠ 0) (r c : ℝ) :
    BrownianIntegrable ℱ P (fun t ω ↦ c * S t ω *
      (if (t : ℝ) < T then deriv (fun x ↦ putPrice x r σ K (T - t))
        (S t ω) else 0)) := by
  have hd := hS.isStronglyPredictable.deriv_putPrice_spot (r := r) hpos hK hσ
  refine (hS.const_mul c).mul_of_bound hd 1 fun t ω ↦ ?_
  split_ifs with ht
  · have hdelta := deriv_putPrice_spot_mem_Ioo
      (r := r) (hpos t ω ht) hK hσ (sub_pos.mpr ht)
    rw [Real.norm_eq_abs, abs_of_neg hdelta.2]
    linarith [hdelta.1]
  · simp

end TauCeti.BrownianIntegrable

namespace ProbabilityTheory.IsPreBrownianReal

/-- The call hedge's Brownian gains coefficient `σ S C_s`, extended by zero at and after
maturity, is predictable and has finite expected square energy on every finite horizon.
The stock may have any physical drift. -/
theorem brownianIntegrable_mul_deriv_callPrice_spot_geometricBrownianMotion
    (hW : IsPreBrownianReal W P) (hp : IsStronglyPredictable ℱ W)
    (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (μ r : ℝ) :
    BrownianIntegrable ℱ P (fun t ω ↦ σ * geometricBrownianMotion s μ σ W t ω *
      (if (t : ℝ) < T then deriv (fun x ↦ callPrice x r σ K (T - t))
        (geometricBrownianMotion s μ σ W t ω) else 0)) :=
  (hW.brownianIntegrable_geometricBrownianMotion hp s μ σ).mul_deriv_callPrice_spot
    (fun t ω _ ↦ geometricBrownianMotion_pos hs μ σ W t ω) hK hσ r σ

/-- The put hedge's Brownian gains coefficient `σ S P_s`, extended by zero at and after
maturity, is predictable and has finite expected square energy on every finite horizon.
No bound on gamma at expiry is needed. -/
theorem brownianIntegrable_mul_deriv_putPrice_spot_geometricBrownianMotion
    (hW : IsPreBrownianReal W P) (hp : IsStronglyPredictable ℱ W)
    (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (μ r : ℝ) :
    BrownianIntegrable ℱ P (fun t ω ↦ σ * geometricBrownianMotion s μ σ W t ω *
      (if (t : ℝ) < T then deriv (fun x ↦ putPrice x r σ K (T - t))
        (geometricBrownianMotion s μ σ W t ω) else 0)) :=
  (hW.brownianIntegrable_geometricBrownianMotion hp s μ σ).mul_deriv_putPrice_spot
    (fun t ω _ ↦ geometricBrownianMotion_pos hs μ σ W t ω) hK hσ r σ

end ProbabilityTheory.IsPreBrownianReal
