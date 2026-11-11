/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Hedge
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Probability.Cdf

/-!
# Full-horizon integrability of the Black–Scholes hedge coefficients

Along a positive continuous stock path on `[0, T]`, the call and put deltas are bounded,
although their derivatives can diverge at expiry. Consequently the stock gains coefficients
`μ S a` and `σ S a` belong to every `Lᵖ` in time on `[0, T)`, including `L∞`. More generally,
multiplying the delta by a time-`Lᵖ` stock path preserves that class. The bond gains
coefficient `r β b` belongs to every `Lᵖ`: the factor `β` cancels from the hedge formula,
leaving a bounded Gaussian cdf times the discounted strike.

In particular the stock drift and bond gains are absolutely integrable, and the stock diffusion
coefficient is square integrable on the full horizon, not only on compact subintervals before
expiry. These pathwise results apply to every continuous geometric Brownian stock path. No
moment assumption on a random initial stock value is involved. The endpoint `T` is omitted
because the payoff need not be differentiable there; its value does not affect a time integral.

These are integrability conditions for the candidate hedge, not a construction of a stochastic
integral or a proof of self-financing. Predictable representatives and the stochastic Itô
identity must be supplied separately. In the bond results `β` need not be continuous: only its
nonvanishing before expiry is used, since the gains depend on `b β`, not on `b` separately.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal

namespace TauCeti.BlackScholes

variable {S β : ℝ → ℝ} {r σ K T : ℝ}

/-- The call delta along a measurable stock path that is positive almost everywhere in time
belongs to every time `Lᵖ`, including `L∞`, on the full interval before expiry. -/
theorem memLp_deriv_callPrice_spot_path
    (hS : AEStronglyMeasurable S (volume.restrict (Ico 0 T)))
    (hs : ∀ᵐ t ∂volume.restrict (Ico 0 T), 0 < S t) (hK : 0 < K) (hσ : σ ≠ 0) (p : ℝ≥0∞) :
    MemLp (fun t => deriv (fun x => callPrice x r σ K (T - t)) (S t)) p
      (volume.restrict (Ico 0 T)) := by
  have hd := (measurable_dPlus r σ K).comp_aemeasurable
    (hS.aemeasurable.prodMk
      (measurable_const.sub measurable_id : Measurable (fun t : ℝ => T - t)).aemeasurable)
  have heq : (fun t => cdf (gaussianReal 0 1) (dPlus (S t) r σ K (T - t))) =ᵐ[
      volume.restrict (Ico 0 T)]
      fun t => deriv (fun x => callPrice x r σ K (T - t)) (S t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico, hs] with t ht hst
    exact (deriv_callPrice_spot hst hK hσ (sub_pos.mpr ht.2)).symm
  exact ((gaussianReal 0 1).memLp_cdf_comp hd p).ae_eq heq

/-- The put delta along a measurable stock path that is positive almost everywhere in time
belongs to every time `Lᵖ`, including `L∞`, on the full interval before expiry. -/
theorem memLp_deriv_putPrice_spot_path
    (hS : AEStronglyMeasurable S (volume.restrict (Ico 0 T)))
    (hs : ∀ᵐ t ∂volume.restrict (Ico 0 T), 0 < S t) (hK : 0 < K) (hσ : σ ≠ 0) (p : ℝ≥0∞) :
    MemLp (fun t => deriv (fun x => putPrice x r σ K (T - t)) (S t)) p
      (volume.restrict (Ico 0 T)) := by
  refine ((memLp_deriv_callPrice_spot_path (r := r) hS hs hK hσ p).sub
    (memLp_const (1 : ℝ))).ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ico, hs] with t ht hst
  simp only [Pi.sub_apply]
  rw [deriv_callPrice_spot hst hK hσ (sub_pos.mpr ht.2),
    deriv_putPrice_spot hst hK hσ (sub_pos.mpr ht.2),
    TauCeti.Probability.cdf_gaussianReal_zero_one_neg]
  ring

/-- Multiplying a time-`Lᵖ` stock path by a constant and the call delta preserves its `Lᵖ`
class on the full horizon. Taking `c = μ`, `p = 1` gives absolute integrability of the stock
drift, and taking `c = σ`, `p = 2` gives square integrability of its diffusion. -/
theorem memLp_mul_deriv_callPrice_spot {p : ℝ≥0∞}
    (hS : MemLp S p (volume.restrict (Ico 0 T)))
    (hs : ∀ᵐ t ∂volume.restrict (Ico 0 T), 0 < S t) (hK : 0 < K) (hσ : σ ≠ 0) (c : ℝ) :
    MemLp (fun t => c * S t * deriv (fun x => callPrice x r σ K (T - t)) (S t)) p
      (volume.restrict (Ico 0 T)) := by
  exact (hS.const_mul c).mul
    (memLp_deriv_callPrice_spot_path (r := r) hS.aestronglyMeasurable hs hK hσ ∞)

/-- The put stock gains coefficients have the same full-horizon time integrability as the
call coefficients, both for the drift (`p = 1`) and diffusion (`p = 2`). -/
theorem memLp_mul_deriv_putPrice_spot {p : ℝ≥0∞}
    (hS : MemLp S p (volume.restrict (Ico 0 T)))
    (hs : ∀ᵐ t ∂volume.restrict (Ico 0 T), 0 < S t) (hK : 0 < K) (hσ : σ ≠ 0) (c : ℝ) :
    MemLp (fun t => c * S t * deriv (fun x => putPrice x r σ K (T - t)) (S t)) p
      (volume.restrict (Ico 0 T)) := by
  exact (hS.const_mul c).mul
    (memLp_deriv_putPrice_spot_path (r := r) hS.aestronglyMeasurable hs hK hσ ∞)

/-- The bond gains coefficient of the call hedge is in every time `Lᵖ` on the full horizon.
Only nonvanishing of the bond price is needed, since that price cancels from `r β b`. -/
theorem memLp_mul_hedgeBondHolding_callPrice
    (hS : AEStronglyMeasurable S (volume.restrict (Ico 0 T)))
    (hs : ∀ᵐ t ∂volume.restrict (Ico 0 T), 0 < S t) (hK : 0 < K) (hσ : σ ≠ 0)
    (hβ : ∀ᵐ t ∂volume.restrict (Ico 0 T), β t ≠ 0) (p : ℝ≥0∞) :
    MemLp (fun t => r * β t *
      hedgeBondHolding (fun x => callPrice x r σ K (T - t)) (S t) (β t)) p
      (volume.restrict (Ico 0 T)) := by
  have hd := (measurable_dMinus r σ K).comp_aemeasurable
    (hS.aemeasurable.prodMk
      (measurable_const.sub measurable_id : Measurable (fun t : ℝ => T - t)).aemeasurable)
  have hcdf := (gaussianReal 0 1).memLp_cdf_comp hd ∞
  have he : ContinuousOn (fun t : ℝ => -(r * K * exp (-r * (T - t)))) (Icc 0 T) := by fun_prop
  refine (hcdf.mul (he.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ico
    Ico_subset_Icc_self p)).ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ico, hs, hβ] with t ht hst hβt
  simp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply]
  rw [hedgeBondHolding_callPrice hst hK hσ (sub_pos.mpr ht.2)]
  field_simp [hβt]

/-- The bond gains coefficient of the put hedge is in every time `Lᵖ` on the full horizon,
without any regularity assumption on the nonvanishing bond price. -/
theorem memLp_mul_hedgeBondHolding_putPrice
    (hS : AEStronglyMeasurable S (volume.restrict (Ico 0 T)))
    (hs : ∀ᵐ t ∂volume.restrict (Ico 0 T), 0 < S t) (hK : 0 < K) (hσ : σ ≠ 0)
    (hβ : ∀ᵐ t ∂volume.restrict (Ico 0 T), β t ≠ 0) (p : ℝ≥0∞) :
    MemLp (fun t => r * β t *
      hedgeBondHolding (fun x => putPrice x r σ K (T - t)) (S t) (β t)) p
      (volume.restrict (Ico 0 T)) := by
  -- Put–call parity makes the difference of the bond gains a deterministic discounted strike.
  have he : ContinuousOn (fun t : ℝ => r * K * exp (-r * (T - t))) (Icc 0 T) := by fun_prop
  refine ((memLp_mul_hedgeBondHolding_callPrice (r := r) hS hs hK hσ hβ p).add
    (he.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ico
      Ico_subset_Icc_self p)).ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ico, hs, hβ] with t ht hst hβt
  simp only [Pi.add_apply]
  rw [hedgeBondHolding_callPrice hst hK hσ (sub_pos.mpr ht.2),
    hedgeBondHolding_putPrice hst hK hσ (sub_pos.mpr ht.2),
    TauCeti.Probability.cdf_gaussianReal_zero_one_neg]
  field_simp [hβt]
  ring

end TauCeti.BlackScholes
