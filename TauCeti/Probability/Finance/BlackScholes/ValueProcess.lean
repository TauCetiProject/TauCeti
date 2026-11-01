/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.ConditionalPrice

/-!
# The discounted Black–Scholes value process is a martingale

Let the stock `S_t = s exp ((r - σ² / 2) t + σ W_t)` have drift equal to the interest rate `r`,
for a Brownian motion `W` relative to a filtration `ℱ`, and fix a maturity `T`. The time-`u`
value of a claim paying `h (S_T)` at `T` is the risk-neutral price
`V_u = riskNeutralPrice h S_u r σ (T - u)`, and its discounted value is `e^{-r u} V_u`. Stopped at
`T`, that is evaluated at `min u T`, the discounted value process is a version of the closed
martingale `E[e^{-r T} h (S_T) | ℱ_u]`. Hence it is a martingale relative to `ℱ` on the whole
time axis, and it lies in `Lᵖ` whenever the discounted claim does (`1 ≤ p`).

For the call and put payoffs the value is the extended Black–Scholes price `C = callValue`,
respectively `P = putValue`. Their discounted value processes `e^{-r u} C(S_u, T - u)` and
`e^{-r u} P(S_u, T - u)`, stopped at `T`, are martingales, the call lies in every `Lᵖ` with
`p < ∞`, and the put is bounded. The same holds in the Black–Scholes market itself, where the
stock has an arbitrary drift `μ` under the physical measure `P`: the discounted value processes
are martingales under the risk-neutral measure `Q = P.tilted (-κ W_T ·)`, `κ = (μ - r) / σ`, and
lie in the corresponding `Lᵖ(Q)`.

Finally, along every path on which `W` is continuous at `T`, `C(S_t, T - t) → (S_T - K)⁺` and
`P(S_t, T - t) → (K - S_T)⁺` as `t → T`, by joint continuity of the extended prices. For a Brownian
motion with almost surely continuous paths the value processes therefore converge almost surely to
the payoffs at maturity.

With the bond `β_t = e^{r t}`, these are the true-martingale, square-integrability and
terminal-convergence conditions on the discounted price `C(S_t, t) / β_t` that an admissible
replicating strategy for the call or put must satisfy. The stochastic integrability of the delta
hedge against the stock is a separate condition and is not treated here.

## Main declarations

All declarations about martingales are in the namespace
`TauCeti.Probability.IsFilteredPreBrownianReal`.

* `discounted_riskNeutralPrice_ae_eq_condExp`: the stopped discounted value process is a version
  of `E[e^{-r T} h (S_T) | ℱ_u]`.
* `martingale_discounted_riskNeutralPrice`, `memLp_discounted_riskNeutralPrice`: it is a
  martingale, in `Lᵖ` with the claim.
* `martingale_discounted_callValue`, `memLp_discounted_callValue`,
  `martingale_discounted_putValue`, `memLp_discounted_putValue`: the call and put.
* `martingale_discounted_callValue_tilted`, `memLp_discounted_callValue_tilted`,
  `martingale_discounted_putValue_tilted`, `memLp_discounted_putValue_tilted`: the call and put in
  the Black–Scholes market, under the risk-neutral measure.
* `TauCeti.BlackScholes.tendsto_callValue_geometricBrownianMotion`,
  `TauCeti.BlackScholes.tendsto_putValue_geometricBrownianMotion`: convergence to the payoffs at
  maturity.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5 and §5.2.
* I. Karatzas, S. E. Shreve, *Methods of Mathematical Finance*, Springer, 1998, §1.4 and §2.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Topology TauCeti.BlackScholes
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s σ K : ℝ} {T : ℝ≥0} {h : ℝ → ℝ}

/-! ### The value process of a claim on the terminal stock -/

/-- **The value process as a closed martingale.** For a stock with drift `r` driven by a Brownian
motion relative to `ℱ` and a claim `h (S_T)` with `h` measurable and `h (S_T)` integrable, the
discounted value process `e^{-r u} riskNeutralPrice h S_u r σ (T - u)`, stopped at `T`, is at every
time `u` a version of the conditional expectation `E[e^{-r T} h (S_T) | ℱ_u]`. -/
theorem discounted_riskNeutralPrice_ae_eq_condExp (hW : IsFilteredPreBrownianReal ℱ W P)
    (s r σ : ℝ) (hh : Measurable h)
    (hint : Integrable (fun ω ↦ h (geometricBrownianMotion s r σ W T ω)) P) (u : ℝ≥0) :
    (fun ω ↦ exp (-r * (min u T : ℝ≥0)) * riskNeutralPrice h
        (geometricBrownianMotion s r σ W (min u T) ω) r σ (T - (min u T : ℝ≥0))) =ᵐ[P]
      P[fun ω ↦ exp (-r * T) * h (geometricBrownianMotion s r σ W T ω) | ℱ u] := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hX : (fun ω ↦ exp (-r * T) * h (geometricBrownianMotion s r σ W T ω)) =
      exp (-r * T) • fun ω ↦ h (geometricBrownianMotion s r σ W T ω) :=
    funext fun ω ↦ (smul_eq_mul _ _).symm
  rcases le_total u T with huT | hTu
  · -- Before maturity this is the conditional price, discounted to time `0`.
    rw [min_eq_left huT, hX]
    filter_upwards [hW.riskNeutralPrice_eq_condExp_geometricBrownianMotion s r σ hh huT hint,
      condExp_smul (exp (-r * T)) (fun ω ↦ h (geometricBrownianMotion s r σ W T ω)) (ℱ u)]
      with ω h₁ h₂
    rw [h₁, h₂, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← exp_add]
    ring_nf
  · -- After maturity both sides are the discounted payoff, which is known at time `T ≤ u`.
    have hm : StronglyMeasurable[ℱ u]
        fun ω ↦ exp (-r * T) * h (geometricBrownianMotion s r σ W T ω) :=
      ((hh.comp (hW.adapted.stronglyAdapted_geometricBrownianMotion s r σ T).measurable).const_mul
        _).stronglyMeasurable.mono (ℱ.mono hTu)
    rw [condExp_of_stronglyMeasurable (ℱ.le u) hm (hint.const_mul _), min_eq_right hTu]
    exact Eventually.of_forall fun ω ↦ by simp

/-- **The discounted value process is a martingale.** For a stock with drift `r` driven by a
Brownian motion relative to `ℱ` and a claim `h (S_T)` with `h` measurable and `h (S_T)` integrable,
the discounted value process `e^{-r u} riskNeutralPrice h S_u r σ (T - u)`, stopped at `T`, is a
martingale relative to `ℱ`. -/
theorem martingale_discounted_riskNeutralPrice (hW : IsFilteredPreBrownianReal ℱ W P)
    (s r σ : ℝ) (hh : Measurable h)
    (hint : Integrable (fun ω ↦ h (geometricBrownianMotion s r σ W T ω)) P) :
    Martingale (fun u ω ↦ exp (-r * (min u T : ℝ≥0)) * riskNeutralPrice h
      (geometricBrownianMotion s r σ W (min u T) ω) r σ (T - (min u T : ℝ≥0))) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine (martingale_condExp (fun ω ↦ exp (-r * T) * h (geometricBrownianMotion s r σ W T ω))
    ℱ P).congr (fun u ↦ ?_)
    fun u ↦ (hW.discounted_riskNeutralPrice_ae_eq_condExp s r σ hh hint u).symm
  have hS : Measurable[ℱ u] (geometricBrownianMotion s r σ W (min u T)) :=
    (hW.adapted.stronglyAdapted_geometricBrownianMotion s r σ (min u T)).measurable.mono
      (ℱ.mono (min_le_left u T)) le_rfl
  exact (((measurable_riskNeutralPrice hh r σ _).comp hS).const_mul _).stronglyMeasurable

/-- **Integrability of the value process.** If the claim `h (S_T)` lies in `Lᵖ`, `1 ≤ p`, then so
does the discounted value process `e^{-r u} riskNeutralPrice h S_u r σ (T - u)`, stopped at `T`, at
every time `u`. -/
theorem memLp_discounted_riskNeutralPrice (hW : IsFilteredPreBrownianReal ℱ W P)
    (s r σ : ℝ) (hh : Measurable h) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hmem : MemLp (fun ω ↦ h (geometricBrownianMotion s r σ W T ω)) p P) (u : ℝ≥0) :
    MemLp (fun ω ↦ exp (-r * (min u T : ℝ≥0)) * riskNeutralPrice h
      (geometricBrownianMotion s r σ W (min u T) ω) r σ (T - (min u T : ℝ≥0))) p P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact ((hmem.const_mul _).condExp hp).ae_eq
    (hW.discounted_riskNeutralPrice_ae_eq_condExp s r σ hh (hmem.integrable hp) u).symm

/-! ### The call and the put -/

/-- Before maturity, the stopped call value is the risk-neutral price of the call payoff. -/
private theorem callValue_min_eq_riskNeutralPrice (hs : 0 < s) (r : ℝ) (hσ : 0 < σ) (hK : 0 < K)
    (u : ℝ≥0) (ω : Ω) :
    callValue (geometricBrownianMotion s r σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0)) =
      riskNeutralPrice (fun x ↦ (x - K)⁺) (geometricBrownianMotion s r σ W (min u T) ω) r σ
        (T - (min u T : ℝ≥0)) :=
  (riskNeutralPrice_call_eq_callValue (geometricBrownianMotion_pos hs r σ W _ ω) hσ hK
    (sub_nonneg.2 (NNReal.coe_le_coe.2 (min_le_right u T)))).symm

/-- Before maturity, the stopped put value is the risk-neutral price of the put payoff. -/
private theorem putValue_min_eq_riskNeutralPrice (hs : 0 < s) (r : ℝ) (hσ : 0 < σ) (hK : 0 < K)
    (u : ℝ≥0) (ω : Ω) :
    putValue (geometricBrownianMotion s r σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0)) =
      riskNeutralPrice (fun x ↦ (K - x)⁺) (geometricBrownianMotion s r σ W (min u T) ω) r σ
        (T - (min u T : ℝ≥0)) :=
  (riskNeutralPrice_put_eq_putValue (geometricBrownianMotion_pos hs r σ W _ ω) hσ hK
    (sub_nonneg.2 (NNReal.coe_le_coe.2 (min_le_right u T)))).symm

/-- **The discounted call value is a martingale.** For a stock with drift `r` and volatility
`σ > 0` driven by a Brownian motion relative to `ℱ`, the discounted Black–Scholes call value
`e^{-r u} C(S_u, T - u)`, stopped at the maturity `T`, is a martingale relative to `ℱ`. -/
theorem martingale_discounted_callValue (hW : IsFilteredPreBrownianReal ℱ W P) (hs : 0 < s)
    (r : ℝ) (hσ : 0 < σ) (hK : 0 < K) :
    Martingale (fun u ω ↦ exp (-r * (min u T : ℝ≥0)) *
      callValue (geometricBrownianMotion s r σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0))) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  simp_rw [callValue_min_eq_riskNeutralPrice hs r hσ hK]
  exact hW.martingale_discounted_riskNeutralPrice s r σ
    (by fun_prop : Continuous fun x : ℝ ↦ (x - K)⁺).measurable
    ((hW.integrable_geometricBrownianMotion s r σ T).sub (integrable_const K)).pos_part

/-- **The discounted put value is a martingale.** For a stock with drift `r` and volatility
`σ > 0` driven by a Brownian motion relative to `ℱ`, the discounted Black–Scholes put value
`e^{-r u} P(S_u, T - u)`, stopped at the maturity `T`, is a martingale relative to `ℱ`. -/
theorem martingale_discounted_putValue (hW : IsFilteredPreBrownianReal ℱ W P) (hs : 0 < s)
    (r : ℝ) (hσ : 0 < σ) (hK : 0 < K) :
    Martingale (fun u ω ↦ exp (-r * (min u T : ℝ≥0)) *
      putValue (geometricBrownianMotion s r σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0))) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  simp_rw [putValue_min_eq_riskNeutralPrice hs r hσ hK]
  exact hW.martingale_discounted_riskNeutralPrice s r σ
    (by fun_prop : Continuous fun x : ℝ ↦ (K - x)⁺).measurable
    ((integrable_const K).sub (hW.integrable_geometricBrownianMotion s r σ T)).pos_part

/-- **The discounted call value has finite moments.** For a stock with drift `r` and volatility
`σ > 0` driven by a Brownian motion relative to `ℱ`, the discounted Black–Scholes call value
`e^{-r u} C(S_u, T - u)`, stopped at the maturity `T`, lies in `Lᵖ` for every `p < ∞`; in
particular it is square integrable. -/
theorem memLp_discounted_callValue (hW : IsFilteredPreBrownianReal ℱ W P) (hs : 0 < s)
    (r : ℝ) (hσ : 0 < σ) (hK : 0 < K) {p : ℝ≥0∞} (hp : p ≠ ∞) (u : ℝ≥0) :
    MemLp (fun ω ↦ exp (-r * (min u T : ℝ≥0)) *
      callValue (geometricBrownianMotion s r σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0))) p P := by
  -- `0 ≤ C(S, τ) ≤ S`, and `S` has finite moments of every finite order.
  refine ((hW.memLp_geometricBrownianMotion s r σ (min u T) hp).const_mul
    (exp (-r * (min u T : ℝ≥0)))).of_le
    (((hW.martingale_discounted_callValue hs r hσ hK).stronglyMeasurable u).mono
      (ℱ.le u)).aestronglyMeasurable (Eventually.of_forall fun ω ↦ ?_)
  have hS := geometricBrownianMotion_pos hs r σ W (min u T) ω
  rw [Real.norm_of_nonneg (mul_nonneg (exp_pos _).le (callValue_nonneg hσ hK _ _ _)),
    Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (callValue_le hS.le hK.le) (exp_pos _).le

/-- **The discounted put value is bounded.** For a stock with drift `r` and volatility `σ > 0`
driven by a Brownian motion relative to `ℱ`, the discounted Black–Scholes put value
`e^{-r u} P(S_u, T - u)`, stopped at the maturity `T`, is bounded by `K e^{-r T}`, so it lies in
`Lᵖ` for every `p`. -/
theorem memLp_discounted_putValue (hW : IsFilteredPreBrownianReal ℱ W P) (hs : 0 < s)
    (r : ℝ) (hσ : 0 < σ) (hK : 0 < K) (p : ℝ≥0∞) (u : ℝ≥0) :
    MemLp (fun ω ↦ exp (-r * (min u T : ℝ≥0)) *
      putValue (geometricBrownianMotion s r σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0))) p P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  -- `0 ≤ P(S, τ) ≤ K e^{-r τ}`, and the discount factors combine to `e^{-r T}`.
  refine MemLp.of_bound
    (((hW.martingale_discounted_putValue hs r hσ hK).stronglyMeasurable u).mono
      (ℱ.le u)).aestronglyMeasurable (K * exp (-r * T)) (Eventually.of_forall fun ω ↦ ?_)
  have hS := geometricBrownianMotion_pos hs r σ W (min u T) ω
  rw [Real.norm_of_nonneg (mul_nonneg (exp_pos _).le (putValue_nonneg hσ hK _ _ _))]
  calc exp (-r * (min u T : ℝ≥0)) * putValue (geometricBrownianMotion s r σ W (min u T) ω) r σ K
        (T - (min u T : ℝ≥0))
      ≤ exp (-r * (min u T : ℝ≥0)) * (K * exp (-r * (T - (min u T : ℝ≥0)))) :=
        mul_le_mul_of_nonneg_left (putValue_le hS.le hK.le) (exp_pos _).le
    _ = K * exp (-r * T) := by
        rw [mul_left_comm, ← exp_add]
        ring_nf

/-! ### The call and the put under the risk-neutral measure of the Black–Scholes market -/

/-- **The discounted call value is a risk-neutral martingale.** Let the stock have drift `μ` and
volatility `σ > 0` under `P`, driven by a Brownian motion relative to `ℱ`, and let
`Q = P.tilted (-κ W_T ·)`, `κ = (μ - r) / σ`, be the risk-neutral measure for the maturity `T`.
The discounted Black–Scholes call value `e^{-r u} C(S_u, T - u)`, stopped at `T`, is a martingale
relative to `ℱ` under `Q`. -/
theorem martingale_discounted_callValue_tilted (hW : IsFilteredPreBrownianReal ℱ W P)
    (hs : 0 < s) (μ r : ℝ) (hσ : 0 < σ) (hK : 0 < K) :
    Martingale (fun u ω ↦ exp (-r * (min u T : ℝ≥0)) *
      callValue (geometricBrownianMotion s μ σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0))) ℱ
      (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω) := by
  simp_rw [geometricBrownianMotion_eq_riskNeutral s μ r hσ.ne' (min_le_right _ T)]
  exact (hW.sub_mul_min_tilted_mul_eval _ T).martingale_discounted_callValue hs r hσ hK

/-- **The discounted put value is a risk-neutral martingale.** Let the stock have drift `μ` and
volatility `σ > 0` under `P`, driven by a Brownian motion relative to `ℱ`, and let
`Q = P.tilted (-κ W_T ·)`, `κ = (μ - r) / σ`, be the risk-neutral measure for the maturity `T`.
The discounted Black–Scholes put value `e^{-r u} P(S_u, T - u)`, stopped at `T`, is a martingale
relative to `ℱ` under `Q`. -/
theorem martingale_discounted_putValue_tilted (hW : IsFilteredPreBrownianReal ℱ W P)
    (hs : 0 < s) (μ r : ℝ) (hσ : 0 < σ) (hK : 0 < K) :
    Martingale (fun u ω ↦ exp (-r * (min u T : ℝ≥0)) *
      putValue (geometricBrownianMotion s μ σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0))) ℱ
      (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω) := by
  simp_rw [geometricBrownianMotion_eq_riskNeutral s μ r hσ.ne' (min_le_right _ T)]
  exact (hW.sub_mul_min_tilted_mul_eval _ T).martingale_discounted_putValue hs r hσ hK

/-- **The discounted call value has finite risk-neutral moments.** In the Black–Scholes market
with stock drift `μ`, volatility `σ > 0` and risk-neutral measure `Q = P.tilted (-κ W_T ·)`,
`κ = (μ - r) / σ`, the discounted call value `e^{-r u} C(S_u, T - u)`, stopped at `T`, lies in
`Lᵖ(Q)` for every `p < ∞`. -/
theorem memLp_discounted_callValue_tilted (hW : IsFilteredPreBrownianReal ℱ W P) (hs : 0 < s)
    (μ r : ℝ) (hσ : 0 < σ) (hK : 0 < K) {p : ℝ≥0∞} (hp : p ≠ ∞) (u : ℝ≥0) :
    MemLp (fun ω ↦ exp (-r * (min u T : ℝ≥0)) *
      callValue (geometricBrownianMotion s μ σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0))) p
      (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω) := by
  simp_rw [geometricBrownianMotion_eq_riskNeutral s μ r hσ.ne' (min_le_right _ T)]
  exact (hW.sub_mul_min_tilted_mul_eval _ T).memLp_discounted_callValue hs r hσ hK hp u

/-- **The discounted put value is bounded under the risk-neutral measure.** In the Black–Scholes
market with stock drift `μ`, volatility `σ > 0` and risk-neutral measure `Q = P.tilted (-κ W_T ·)`,
`κ = (μ - r) / σ`, the discounted put value `e^{-r u} P(S_u, T - u)`, stopped at `T`, lies in
`Lᵖ(Q)` for every `p`. -/
theorem memLp_discounted_putValue_tilted (hW : IsFilteredPreBrownianReal ℱ W P) (hs : 0 < s)
    (μ r : ℝ) (hσ : 0 < σ) (hK : 0 < K) (p : ℝ≥0∞) (u : ℝ≥0) :
    MemLp (fun ω ↦ exp (-r * (min u T : ℝ≥0)) *
      putValue (geometricBrownianMotion s μ σ W (min u T) ω) r σ K (T - (min u T : ℝ≥0))) p
      (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω) := by
  simp_rw [geometricBrownianMotion_eq_riskNeutral s μ r hσ.ne' (min_le_right _ T)]
  exact (hW.sub_mul_min_tilted_mul_eval _ T).memLp_discounted_putValue hs r hσ hK p u

end TauCeti.Probability.IsFilteredPreBrownianReal

/-! ### Convergence to the payoff at maturity -/

namespace TauCeti.BlackScholes

open TauCeti.Probability

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {σ K : ℝ} {T : ℝ≥0} {ω : Ω}

/-- **The call value converges to the payoff at maturity.** Along a path on which the driving
process `W` is continuous at the maturity `T`, the Black–Scholes call value `C(S_t, T - t)` of the
geometric Brownian motion `S` (of any drift `μ`) tends to the payoff `(S_T - K)⁺` as `t → T`. -/
theorem tendsto_callValue_geometricBrownianMotion (s μ r : ℝ) (hσ : 0 < σ) (hK : 0 < K)
    (hW : ContinuousAt (fun t ↦ W t ω) T) :
    Tendsto (fun t ↦ callValue (geometricBrownianMotion s μ σ W t ω) r σ K (T - t)) (𝓝 T)
      (𝓝 (geometricBrownianMotion s μ σ W T ω - K)⁺) := by
  have hS : ContinuousAt (fun t ↦ geometricBrownianMotion s μ σ W t ω) T := by
    simp_rw [geometricBrownianMotion_def]
    fun_prop
  have hτ : ContinuousAt (fun t : ℝ≥0 ↦ (T : ℝ) - t) T := by fun_prop
  have h := ((continuous_callValue (r := r) hσ hK).continuousAt.comp (hS.prodMk hτ)).tendsto
  rw [Function.comp_apply, sub_self, callValue_maturity_zero] at h
  exact h

/-- **The put value converges to the payoff at maturity.** Along a path on which the driving
process `W` is continuous at the maturity `T`, the Black–Scholes put value `P(S_t, T - t)` of the
geometric Brownian motion `S` (of any drift `μ`) tends to the payoff `(K - S_T)⁺` as `t → T`. -/
theorem tendsto_putValue_geometricBrownianMotion (s μ r : ℝ) (hσ : 0 < σ) (hK : 0 < K)
    (hW : ContinuousAt (fun t ↦ W t ω) T) :
    Tendsto (fun t ↦ putValue (geometricBrownianMotion s μ σ W t ω) r σ K (T - t)) (𝓝 T)
      (𝓝 (K - geometricBrownianMotion s μ σ W T ω)⁺) := by
  have hS : ContinuousAt (fun t ↦ geometricBrownianMotion s μ σ W t ω) T := by
    simp_rw [geometricBrownianMotion_def]
    fun_prop
  have hτ : ContinuousAt (fun t : ℝ≥0 ↦ (T : ℝ) - t) T := by fun_prop
  have h := ((continuous_putValue (r := r) hσ hK).continuousAt.comp (hS.prodMk hτ)).tendsto
  rw [Function.comp_apply, sub_self, putValue_maturity_zero] at h
  exact h

end TauCeti.BlackScholes
