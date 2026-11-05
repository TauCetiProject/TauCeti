/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Extension

/-!
# Classical regularity of Black–Scholes prices

For nonzero volatility and nonzero strike, the closed-form call and put prices are jointly
smooth wherever spot is nonzero and remaining maturity is positive (see `ContDiffAt.callPrice`
and `ContDiffAt.putPrice`). The continuously extended values have the same regularity where
spot and remaining maturity are positive, including in calendar time on `s > 0, t < T`.
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
open TauCeti.BlackScholes

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {x : E} {r σ K : ℝ} {n : ℕ∞}

/-- The continuous call value is smooth under composition at every interior pricing point. -/
@[fun_prop]
theorem callValue (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hs : 0 < f x) (hK : K ≠ 0) (hσ : σ ≠ 0) (hτ : 0 < g x) :
    ContDiffAt ℝ n (fun y => callValue (f y) r σ K (g y)) x := by
  apply (hf.callPrice hg hs.ne' hK hσ hτ (r := r)).congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds hs),
    hg.continuousAt.eventually (Ioi_mem_nhds hτ)] with y hy hy'
  exact callValue_of_pos hy hy'

/-- The continuous put value is smooth under composition at every interior pricing point. -/
@[fun_prop]
theorem putValue (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hs : 0 < f x) (hK : K ≠ 0) (hσ : σ ≠ 0) (hτ : 0 < g x) :
    ContDiffAt ℝ n (fun y => putValue (f y) r σ K (g y)) x := by
  apply (hf.putPrice hg hs.ne' hK hσ hτ (r := r)).congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds hs),
    hg.continuousAt.eventually (Ioi_mem_nhds hτ)] with y hy hy'
  exact putValue_of_pos hy hy'

end ContDiffAt

namespace TauCeti.BlackScholes

variable {s r σ K : ℝ} {n : ℕ∞}

/-- The extended call is jointly smooth on the open positive-spot, positive-maturity domain. -/
theorem contDiffOn_callValue (hK : K ≠ 0) (hσ : σ ≠ 0) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => callValue p.1 r σ K p.2)
      (Ioi 0 ×ˢ Ioi 0) :=
  fun _ hp => (contDiffAt_fst.callValue contDiffAt_snd hp.1 hK hσ hp.2).contDiffWithinAt

/-- The extended put is jointly smooth on the open positive-spot, positive-maturity domain. -/
theorem contDiffOn_putValue (hK : K ≠ 0) (hσ : σ ≠ 0) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => putValue p.1 r σ K p.2)
      (Ioi 0 ×ˢ Ioi 0) :=
  fun _ hp => (contDiffAt_fst.putValue contDiffAt_snd hp.1 hK hσ hp.2).contDiffWithinAt

/-- In calendar time, the extended call is smooth at every positive spot before expiry.
This includes time zero whenever the expiry is strictly positive. -/
theorem contDiffAt_callValue_calendarTime {T t : ℝ} (hs : 0 < s) (hK : K ≠ 0)
    (hσ : σ ≠ 0) (ht : t < T) :
    ContDiffAt ℝ n (fun p : ℝ × ℝ => callValue p.1 r σ K (T - p.2)) (s, t) :=
  contDiffAt_fst.callValue (contDiffAt_const.sub contDiffAt_snd) hs hK hσ (sub_pos.2 ht)

/-- In calendar time, the extended put is smooth at every positive spot before expiry. -/
theorem contDiffAt_putValue_calendarTime {T t : ℝ} (hs : 0 < s) (hK : K ≠ 0)
    (hσ : σ ≠ 0) (ht : t < T) :
    ContDiffAt ℝ n (fun p : ℝ × ℝ => putValue p.1 r σ K (T - p.2)) (s, t) :=
  contDiffAt_fst.putValue (contDiffAt_const.sub contDiffAt_snd) hs hK hσ (sub_pos.2 ht)

end TauCeti.BlackScholes
