/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Extension
public import TauCeti.Probability.Distributions.Gaussian.Smooth
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Classical regularity of Black–Scholes prices

For nonzero volatility and positive strike, the call and put prices are jointly smooth in
spot and remaining maturity on the open pricing domain. The continuously extended values
have the same regularity in the interior, including in calendar time on `s > 0, t < T`.
Consequently their spatial and time derivatives have the continuity required of classical
solutions of the Black–Scholes equation and for applications of Itô's formula.

Smoothness is only asserted before maturity and away from zero spot. In particular it does
not assert differentiability of the terminal payoff at the strike. This file concerns
analytic regularity, not stochastic integrability or admissibility of a trading strategy.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ContDiff NNReal Topology

namespace TauCeti.BlackScholes

variable {s r σ K τ : ℝ}

/-- The Black–Scholes normal argument is jointly smooth in spot and remaining maturity
where its logarithm and denominator are nonsingular. -/
@[fun_prop]
theorem contDiffAt_dPlus (hs : s ≠ 0) (hK : K ≠ 0) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => dPlus p.1 r σ K p.2) (s, τ) := by
  simp only [dPlus_def]
  exact (((contDiffAt_fst.div_const K).log (div_ne_zero hs hK)).add
    (contDiffAt_const.mul contDiffAt_snd)).div
      (contDiffAt_const.mul (contDiffAt_snd.sqrt hτ.ne'))
      (mul_ne_zero hσ (sqrt_pos.2 hτ).ne')

/-- The lower Black–Scholes normal argument is jointly smooth on the same domain. -/
@[fun_prop]
theorem contDiffAt_dMinus (hs : s ≠ 0) (hK : K ≠ 0) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => dMinus p.1 r σ K p.2) (s, τ) := by
  simp only [dMinus_def]
  exact (contDiffAt_dPlus hs hK hσ hτ).sub
    (contDiffAt_const.mul (contDiffAt_snd.sqrt hτ.ne'))

/-- The closed-form call price is jointly smooth in spot and remaining maturity wherever
the normal arguments are nonsingular. -/
@[fun_prop]
theorem contDiffAt_callPrice (hs : s ≠ 0) (hK : K ≠ 0) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => callPrice p.1 r σ K p.2) (s, τ) := by
  have hΦ := Probability.contDiff_cdf_gaussianReal 0 one_ne_zero
  simp only [callPrice_def]
  exact (contDiffAt_fst.mul (hΦ.contDiffAt.comp _ (contDiffAt_dPlus hs hK hσ hτ))).sub
    ((contDiffAt_const.mul ((contDiffAt_const.mul contDiffAt_snd).exp)).mul
      (hΦ.contDiffAt.comp _ (contDiffAt_dMinus hs hK hσ hτ)))

/-- The closed-form put price is jointly smooth in spot and remaining maturity wherever
the normal arguments are nonsingular. -/
@[fun_prop]
theorem contDiffAt_putPrice (hs : s ≠ 0) (hK : K ≠ 0) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => putPrice p.1 r σ K p.2) (s, τ) := by
  simp only [putPrice_eq_callPrice]
  exact ((contDiffAt_callPrice hs hK hσ hτ).sub contDiffAt_fst).add
    (contDiffAt_const.mul ((contDiffAt_const.mul contDiffAt_snd).exp))

/-- The continuous call value is smooth at every interior pricing point. -/
@[fun_prop]
theorem contDiffAt_callValue (hs : 0 < s) (hK : K ≠ 0) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => callValue p.1 r σ K p.2) (s, τ) := by
  apply (contDiffAt_callPrice (r := r) hs.ne' hK hσ hτ).congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioi.prod isOpen_Ioi).mem_nhds (mk_mem_prod hs hτ)] with p hp
  exact callValue_of_pos hp.1 hp.2

/-- The continuous put value is smooth at every interior pricing point. -/
@[fun_prop]
theorem contDiffAt_putValue (hs : 0 < s) (hK : K ≠ 0) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => putValue p.1 r σ K p.2) (s, τ) := by
  apply (contDiffAt_putPrice (r := r) hs.ne' hK hσ hτ).congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioi.prod isOpen_Ioi).mem_nhds (mk_mem_prod hs hτ)] with p hp
  exact putValue_of_pos hp.1 hp.2

/-- The extended call is jointly smooth on the open positive-spot, positive-maturity domain. -/
@[fun_prop]
theorem contDiffOn_callValue (r : ℝ) (hK : K ≠ 0) (hσ : σ ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => callValue p.1 r σ K p.2)
      (Ioi 0 ×ˢ Ioi 0) :=
  fun _ hp => (contDiffAt_callValue hp.1 hK hσ hp.2).contDiffWithinAt

/-- The extended put is jointly smooth on the open positive-spot, positive-maturity domain. -/
@[fun_prop]
theorem contDiffOn_putValue (r : ℝ) (hK : K ≠ 0) (hσ : σ ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => putValue p.1 r σ K p.2)
      (Ioi 0 ×ˢ Ioi 0) :=
  fun _ hp => (contDiffAt_putValue hp.1 hK hσ hp.2).contDiffWithinAt

/-- In calendar time, the extended call is smooth at every positive spot before expiry.
This includes time zero whenever the expiry is strictly positive. -/
@[fun_prop]
theorem contDiffAt_callValue_calendarTime {T t : ℝ} (hs : 0 < s) (hK : K ≠ 0)
    (hσ : σ ≠ 0) (ht : t < T) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => callValue p.1 r σ K (T - p.2)) (s, t) := by
  exact (contDiffAt_callValue hs hK hσ (sub_pos.2 ht)).comp (s, t)
    (contDiffAt_fst.prodMk (contDiffAt_const.sub contDiffAt_snd))

/-- In calendar time, the extended put is smooth at every positive spot before expiry. -/
@[fun_prop]
theorem contDiffAt_putValue_calendarTime {T t : ℝ} (hs : 0 < s) (hK : K ≠ 0)
    (hσ : σ ≠ 0) (ht : t < T) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => putValue p.1 r σ K (T - p.2)) (s, t) := by
  exact (contDiffAt_putValue hs hK hσ (sub_pos.2 ht)).comp (s, t)
    (contDiffAt_fst.prodMk (contDiffAt_const.sub contDiffAt_snd))

end TauCeti.BlackScholes
