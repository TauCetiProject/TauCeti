/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Greeks
import TauCeti.Probability.Distributions.Gaussian.Basic
import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# Boundary and terminal behaviour of the Black–Scholes prices

This file describes the closed-form Black–Scholes prices
`C = s Φ(d₊) - K e^{-rτ} Φ(d₋)` and `P = K e^{-rτ} Φ(-d₋) - s Φ(-d₊)` of
`TauCeti.Probability.Finance.BlackScholes.Basic` at the edges of their domain `s > 0`, `τ > 0`,
for a volatility `σ > 0` and strike `K > 0`. Here `Φ` is the standard Gaussian cdf and
`φ = gaussianPDFReal 0 1` its density.

* **Zero spot.** As `s → 0⁺`, `C → 0` and `P → K e^{-rτ}`.
* **Far field.** As `s → ∞`, `C - s + K e^{-rτ} → 0` and `P → 0`.
* **Maturity.** As `(s, τ) → (s₀, 0⁺)` with `s₀ > 0`, `C → (s₀ - K)⁺` and `P → (K - s₀)⁺`. So
  the prices extend continuously to the expiry `τ = 0` by the call and put payoffs.
* **Gamma at maturity.** For a fixed spot `s ≠ K` the gamma `φ(d₊) / (s σ √τ)` of the call
  (equivalently, of the put) tends to `0` as `τ → 0⁺`. At the money it blows up like `1 / √τ`:
  `√τ ∂²C/∂s²(K, τ) → 1 / (K σ √(2π))`, so the gamma tends to `+∞` and has no finite terminal
  value at `s = K`.

The zero-spot and far-field limits are squeezes between the no-arbitrage bounds `0 ≤ C ≤ s` and
`0 ≤ P ≤ K e^{-rτ} Φ(-d₋)`, where nonnegativity comes from the risk-neutral representation of the
prices. The terminal limits follow the sign of `log (s / K)`, which decides whether `d₊` and `d₋`
tend to `+∞`, to `-∞`, or to `0`; joint continuity in `(s, τ)` then follows because the call is
`1`-Lipschitz in the spot, its delta `Φ(d₊)` lying in `(0, 1)`.

## Main declarations

* `TauCeti.BlackScholes.callPrice_nonneg`, `TauCeti.BlackScholes.putPrice_nonneg`,
  `TauCeti.BlackScholes.callPrice_le` — the bounds `0 ≤ C ≤ s` and `0 ≤ P`.
* `TauCeti.BlackScholes.abs_callPrice_sub_callPrice_le` — the call is `1`-Lipschitz in the spot.
* `TauCeti.BlackScholes.tendsto_callPrice_spot_zero`,
  `TauCeti.BlackScholes.tendsto_putPrice_spot_zero` — the limits at zero spot.
* `TauCeti.BlackScholes.tendsto_callPrice_sub_spot_atTop`,
  `TauCeti.BlackScholes.tendsto_putPrice_spot_atTop` — the far-field limits.
* `TauCeti.BlackScholes.tendsto_callPrice_maturity_zero`,
  `TauCeti.BlackScholes.tendsto_putPrice_maturity_zero` — the limits at maturity for a fixed spot.
* `TauCeti.BlackScholes.tendsto_callPrice_terminal`,
  `TauCeti.BlackScholes.tendsto_putPrice_terminal` — the joint limits at maturity.
* `TauCeti.BlackScholes.tendsto_deriv_deriv_callPrice_spot_maturity_zero` — gamma away from the
  money vanishes at maturity.
* `TauCeti.BlackScholes.tendsto_sqrt_mul_deriv_deriv_callPrice_spot_strike`,
  `TauCeti.BlackScholes.tendsto_deriv_deriv_callPrice_spot_strike_atTop` — gamma at the money.
* The corresponding put gamma statements.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
* J. C. Hull, *Options, Futures, and Other Derivatives*, Pearson, 2018, Chapters 11 and 19.
-/

public section

noncomputable section

open Filter ProbabilityTheory Real Set TauCeti.Probability
open scoped Topology

namespace TauCeti.BlackScholes

variable {s r σ K τ : ℝ}

/-! ### No-arbitrage bounds -/

/-- The Black–Scholes call price is nonnegative. -/
theorem callPrice_nonneg (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    0 ≤ callPrice s r σ K τ := by
  rw [← riskNeutralPrice_call hs hσ hK hτ]
  exact riskNeutralPrice_nonneg (fun x => posPart_nonneg _) s r σ τ

/-- The Black–Scholes put price is nonnegative. -/
theorem putPrice_nonneg (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    0 ≤ putPrice s r σ K τ := by
  rw [← riskNeutralPrice_put hs hσ hK hτ]
  exact riskNeutralPrice_nonneg (fun x => posPart_nonneg _) s r σ τ

/-- The Black–Scholes call price is at most the spot. -/
theorem callPrice_le (hs : 0 ≤ s) (hK : 0 ≤ K) : callPrice s r σ K τ ≤ s := by
  rw [callPrice_def]
  have h₁ := mul_le_mul_of_nonneg_left (cdf_le_one (gaussianReal 0 1) (dPlus s r σ K τ)) hs
  have h₂ := mul_nonneg (mul_nonneg hK (exp_pos (-r * τ)).le)
    (cdf_nonneg (gaussianReal 0 1) (dMinus s r σ K τ))
  linarith

/-- The put price is at most its strike leg `K e^{-rτ} Φ(-d₋)`. -/
private theorem putPrice_le_mul_cdf (hs : 0 ≤ s) :
    putPrice s r σ K τ ≤ K * exp (-r * τ) * cdf (gaussianReal 0 1) (-dMinus s r σ K τ) := by
  rw [putPrice_def]
  linarith [mul_nonneg hs (cdf_nonneg (gaussianReal 0 1) (-dPlus s r σ K τ))]

/-- The Black–Scholes call price is `1`-Lipschitz in the spot. -/
theorem abs_callPrice_sub_callPrice_le {x : ℝ} (hx : 0 < x) (hs : 0 < s) (hK : 0 < K)
    (hσ : σ ≠ 0) (hτ : 0 < τ) :
    |callPrice x r σ K τ - callPrice s r σ K τ| ≤ |x - s| := by
  have h := (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y => callPrice y r σ K τ) (C := 1)
    (fun y hy => (hasDerivAt_callPrice_spot (r := r) hy hK hσ hτ).hasDerivWithinAt)
    (fun y _ => by
      rw [norm_of_nonneg (cdf_nonneg _ _)]
      exact cdf_le_one _ _) hs hx
  simpa only [norm_eq_abs, one_mul] using h

/-! ### Limits in the spot -/

/-- **Call boundary at zero spot.** As the spot tends to `0`, the call price tends to `0`. -/
theorem tendsto_callPrice_spot_zero (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    Tendsto (fun x => callPrice x r σ K τ) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_nhdsWithin_of_tendsto_nhds (f := fun x => x) tendsto_id) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact callPrice_nonneg hx hσ hK hτ
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact callPrice_le (le_of_lt hx) hK.le

/-- **Put boundary at zero spot.** As the spot tends to `0`, the put price tends to the
discounted strike `K e^{-rτ}`. -/
theorem tendsto_putPrice_spot_zero (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    Tendsto (fun x => putPrice x r σ K τ) (𝓝[>] 0) (𝓝 (K * exp (-r * τ))) := by
  have h := ((tendsto_callPrice_spot_zero (r := r) hσ hK hτ).sub
    (tendsto_nhdsWithin_of_tendsto_nhds (f := fun x => x) tendsto_id)).add_const
    (K * exp (-r * τ))
  simp only [sub_zero, zero_add] at h
  simpa only [putPrice_eq_callPrice] using h

/-- As the spot tends to `∞`, so does `d₋`. -/
private theorem tendsto_dMinus_spot_atTop (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    Tendsto (fun x => dMinus x r σ K τ) atTop atTop := by
  have h : Tendsto (fun x => log (x / K)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_id.atTop_div_const hK)
  simp_rw [dMinus_eq _ r σ K hτ.le]
  exact (h.atTop_add tendsto_const_nhds).atTop_div_const (mul_pos hσ (sqrt_pos.2 hτ))

/-- **Put far field.** As the spot tends to `∞`, the put price tends to `0`. -/
theorem tendsto_putPrice_spot_atTop (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    Tendsto (fun x => putPrice x r σ K τ) atTop (𝓝 0) := by
  have h : Tendsto (fun x => K * exp (-r * τ) * cdf (gaussianReal 0 1) (-dMinus x r σ K τ))
      atTop (𝓝 0) := by
    simpa using ((tendsto_cdf_atBot _).comp
      (tendsto_neg_atTop_atBot.comp (tendsto_dMinus_spot_atTop hσ hK hτ))).const_mul
      (K * exp (-r * τ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact putPrice_nonneg hx hσ hK hτ
  · filter_upwards [eventually_ge_atTop 0] with x hx
    exact putPrice_le_mul_cdf hx

/-- **Call far field.** As the spot tends to `∞`, the call price is asymptotic to the forward
value `s - K e^{-rτ}`: the difference tends to `0`. -/
theorem tendsto_callPrice_sub_spot_atTop (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    Tendsto (fun x => callPrice x r σ K τ - x + K * exp (-r * τ)) atTop (𝓝 0) := by
  simpa only [putPrice_eq_callPrice] using tendsto_putPrice_spot_atTop (r := r) hσ hK hτ

/-! ### Limits at maturity -/

/-- As the remaining maturity tends to `0`, `σ √τ` tends to `0` through positive values. -/
private theorem tendsto_mul_sqrt_nhdsGT_zero (hσ : 0 < σ) :
    Tendsto (fun u => σ * √u) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Continuous fun u => σ * √u := by fun_prop
    simpa using (h.continuousWithinAt (s := Ioi 0) (x := 0)).tendsto
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact mul_pos hσ (sqrt_pos.2 hu)

/-- For a positive maturity, `d₊ = log (s / K) / (σ √τ) + (r + σ² / 2) √τ / σ`. -/
private theorem dPlus_eq_add (hσ : σ ≠ 0) (hτ : 0 < τ) :
    dPlus s r σ K τ = log (s / K) * (σ * √τ)⁻¹ + (r + σ ^ 2 / 2) * √τ / σ := by
  have h := (sqrt_pos.2 hτ).ne'
  rw [dPlus_def, add_div, div_eq_mul_inv]
  congr 1
  field_simp
  rw [sq_sqrt hτ.le]

/-- As the maturity tends to `0⁺`, `d₊` behaves like `log (s / K) / (σ √τ)`: the remainder
tends to `0`. -/
private theorem tendsto_dPlus_sub (hσ : 0 < σ) :
    Tendsto (fun u => dPlus s r σ K u - log (s / K) * (σ * √u)⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have h : Continuous fun u => (r + σ ^ 2 / 2) * √u / σ := by fun_prop
  refine ((h.continuousWithinAt (s := Ioi 0) (x := 0)).tendsto.congr' ?_).trans (by simp)
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [dPlus_eq_add hσ.ne' hu, add_sub_cancel_left]

/-- As the maturity tends to `0⁺`, `d₊ → +∞` in the money. -/
private theorem tendsto_dPlus_maturity_atTop (hσ : 0 < σ) (hK : 0 < K) (hsK : K < s) :
    Tendsto (dPlus s r σ K) (𝓝[>] 0) atTop := by
  have hlog : 0 < log (s / K) := log_pos ((one_lt_div hK).2 hsK)
  have h := (tendsto_inv_nhdsGT_zero.comp (tendsto_mul_sqrt_nhdsGT_zero hσ)).const_mul_atTop hlog
  exact (h.atTop_add (tendsto_dPlus_sub (s := s) (r := r) (K := K) hσ)).congr fun u => by
    simp only [Function.comp_apply]
    ring

/-- As the maturity tends to `0⁺`, `d₊ → -∞` out of the money. -/
private theorem tendsto_dPlus_maturity_atBot (hσ : 0 < σ) (hs : 0 < s) (hsK : s < K) :
    Tendsto (dPlus s r σ K) (𝓝[>] 0) atBot := by
  have hlog : log (s / K) < 0 := log_neg (div_pos hs (hs.trans hsK)) ((div_lt_one
    (hs.trans hsK)).2 hsK)
  have h := (tendsto_inv_nhdsGT_zero.comp
    (tendsto_mul_sqrt_nhdsGT_zero hσ)).const_mul_atTop_of_neg hlog
  exact (h.atBot_add (tendsto_dPlus_sub (s := s) (r := r) (K := K) hσ)).congr fun u => by
    simp only [Function.comp_apply]
    ring

/-- As the maturity tends to `0⁺`, `d₊ → 0` at the money. -/
private theorem tendsto_dPlus_maturity_strike (hσ : 0 < σ) (hK : 0 < K) :
    Tendsto (dPlus K r σ K) (𝓝[>] 0) (𝓝 0) := by
  simpa [div_self hK.ne'] using tendsto_dPlus_sub (s := K) (r := r) (K := K) hσ

/-- `d₋ = d₊ - σ √τ` has the same limit as `d₊` at maturity. -/
private theorem tendsto_dMinus_maturity_of_tendsto_dPlus (hσ : 0 < σ) {l : Filter ℝ}
    (hl : ∀ {f g : ℝ → ℝ}, Tendsto f (𝓝[>] 0) l → Tendsto g (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun u => f u - g u) (𝓝[>] 0) l)
    (h : Tendsto (dPlus s r σ K) (𝓝[>] 0) l) :
    Tendsto (dMinus s r σ K) (𝓝[>] 0) l := by
  have hsq := (tendsto_mul_sqrt_nhdsGT_zero hσ).mono_right nhdsWithin_le_nhds
  exact (hl h hsq).congr fun u => (dMinus_def s r σ K u).symm

/-- If `Φ(d₊)` and `Φ(d₋)` both tend to `a` at maturity, the call price tends to `s a - K a`. -/
private theorem tendsto_callPrice_maturity_of_tendsto_cdf {a : ℝ}
    (hp : Tendsto (fun u => cdf (gaussianReal 0 1) (dPlus s r σ K u)) (𝓝[>] 0) (𝓝 a))
    (hm : Tendsto (fun u => cdf (gaussianReal 0 1) (dMinus s r σ K u)) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (callPrice s r σ K) (𝓝[>] 0) (𝓝 (s * a - K * a)) := by
  have hdisc : Tendsto (fun u => K * exp (-r * u)) (𝓝[>] 0) (𝓝 K) := by
    have h : Continuous fun u => K * exp (-r * u) := by fun_prop
    simpa using (h.continuousWithinAt (s := Ioi 0) (x := 0)).tendsto
  exact ((hp.const_mul s).sub (hdisc.mul hm)).congr fun u => (callPrice_def s r σ K u).symm

/-- **Call payoff at maturity.** For a fixed spot `s > 0`, as the remaining maturity tends to
`0⁺` the call price tends to the payoff `(s - K)⁺`. -/
theorem tendsto_callPrice_maturity_zero (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) :
    Tendsto (callPrice s r σ K) (𝓝[>] 0) (𝓝 (s - K)⁺) := by
  rcases lt_trichotomy s K with hsK | rfl | hsK
  · -- Out of the money, `d₊, d₋ → -∞` and both cdf values tend to `0`.
    have hp := tendsto_dPlus_maturity_atBot (r := r) hσ hs hsK
    have hm := tendsto_dMinus_maturity_of_tendsto_dPlus hσ
      (fun hf hg => by simpa only [sub_eq_add_neg] using hf.atBot_add hg.neg) hp
    have h := tendsto_callPrice_maturity_of_tendsto_cdf ((tendsto_cdf_atBot _).comp hp)
      ((tendsto_cdf_atBot _).comp hm)
    rw [posPart_eq_zero.2 (sub_nonpos.2 hsK.le)]
    simpa using h
  · -- At the money, `d₊, d₋ → 0` and both cdf values tend to `Φ(0)`.
    have hp := tendsto_dPlus_maturity_strike (r := r) hσ hK
    have hm := tendsto_dMinus_maturity_of_tendsto_dPlus hσ
      (fun hf hg => by simpa only [sub_zero] using hf.sub hg) hp
    have hΦ := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero 0).continuousAt.tendsto
    have h := tendsto_callPrice_maturity_of_tendsto_cdf (hΦ.comp hp) (hΦ.comp hm)
    simpa using h
  · -- In the money, `d₊, d₋ → +∞` and both cdf values tend to `1`.
    have hp := tendsto_dPlus_maturity_atTop (r := r) hσ hK hsK
    have hm := tendsto_dMinus_maturity_of_tendsto_dPlus hσ
      (fun hf hg => by simpa only [sub_eq_add_neg] using hf.atTop_add hg.neg) hp
    have h := tendsto_callPrice_maturity_of_tendsto_cdf ((tendsto_cdf_atTop _).comp hp)
      ((tendsto_cdf_atTop _).comp hm)
    rw [posPart_eq_self.2 (sub_nonneg.2 hsK.le)]
    simpa using h

/-- **Continuous extension of the call to maturity.** As `(s, τ) → (s₀, 0⁺)` with `s₀ > 0`, the
call price tends to the payoff `(s₀ - K)⁺`. -/
theorem tendsto_callPrice_terminal (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) :
    Tendsto (fun p : ℝ × ℝ => callPrice p.1 r σ K p.2) (𝓝 s ×ˢ 𝓝[>] 0) (𝓝 (s - K)⁺) := by
  -- Split `|C(x, u) - (s - K)⁺| ≤ |x - s| + |C(s, u) - (s - K)⁺|` by the Lipschitz bound.
  have h₁ : Tendsto (fun p : ℝ × ℝ => |p.1 - s|) (𝓝 s ×ˢ 𝓝[>] 0) (𝓝 |s - s|) :=
    (tendsto_fst.sub_const s).abs
  have h₂ : Tendsto (fun p : ℝ × ℝ => |callPrice s r σ K p.2 - (s - K)⁺|)
      (𝓝 s ×ˢ 𝓝[>] 0) (𝓝 |(s - K)⁺ - (s - K)⁺|) :=
    (((tendsto_callPrice_maturity_zero hs hσ hK).sub_const (s - K)⁺).abs).comp tendsto_snd
  rw [sub_self, abs_zero] at h₁ h₂
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [norm_eq_abs]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using h₁.add h₂) (Eventually.of_forall fun p => abs_nonneg _) ?_
  filter_upwards [prod_mem_prod (Ioi_mem_nhds hs) self_mem_nhdsWithin] with p hp
  calc |callPrice p.1 r σ K p.2 - (s - K)⁺|
      ≤ |callPrice p.1 r σ K p.2 - callPrice s r σ K p.2| +
        |callPrice s r σ K p.2 - (s - K)⁺| := abs_sub_le _ _ _
    _ ≤ |p.1 - s| + |callPrice s r σ K p.2 - (s - K)⁺| := by
      linarith [abs_callPrice_sub_callPrice_le (r := r) hp.1 hs hK hσ.ne' hp.2]

/-- **Continuous extension of the put to maturity.** As `(s, τ) → (s₀, 0⁺)` with `s₀ > 0`, the
put price tends to the payoff `(K - s₀)⁺`. -/
theorem tendsto_putPrice_terminal (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) :
    Tendsto (fun p : ℝ × ℝ => putPrice p.1 r σ K p.2) (𝓝 s ×ˢ 𝓝[>] 0) (𝓝 (K - s)⁺) := by
  have hdisc : Tendsto (fun p : ℝ × ℝ => K * exp (-r * p.2)) (𝓝 s ×ˢ 𝓝[>] 0)
      (𝓝 (K * exp (-r * 0))) := by
    have h : Continuous fun u => K * exp (-r * u) := by fun_prop
    exact (h.continuousWithinAt (s := Ioi 0) (x := 0)).tendsto.comp tendsto_snd
  rw [mul_zero, exp_zero, mul_one] at hdisc
  have h := ((tendsto_callPrice_terminal (r := r) hs hσ hK).sub tendsto_fst).add hdisc
  have hpay : (s - K)⁺ - s + K = (K - s)⁺ := by
    rw [show K - s = -(s - K) by ring, posPart_neg]
    linear_combination posPart_sub_negPart (s - K)
  rw [hpay] at h
  simpa only [putPrice_eq_callPrice] using h

/-- **Put payoff at maturity.** For a fixed spot `s > 0`, as the remaining maturity tends to
`0⁺` the put price tends to the payoff `(K - s)⁺`. -/
theorem tendsto_putPrice_maturity_zero (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) :
    Tendsto (putPrice s r σ K) (𝓝[>] 0) (𝓝 (K - s)⁺) :=
  (tendsto_putPrice_terminal hs hσ hK).comp (tendsto_const_nhds.prodMk tendsto_id)

/-! ### Gamma at maturity -/

/-- **Gamma away from the money at maturity.** For a fixed spot `s > 0` with `s ≠ K`, the call
gamma tends to `0` as the remaining maturity tends to `0⁺`. -/
theorem tendsto_deriv_deriv_callPrice_spot_maturity_zero (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K)
    (hsK : s ≠ K) :
    Tendsto (fun u => deriv (deriv fun x => callPrice x r σ K u) s) (𝓝[>] 0) (𝓝 0) := by
  -- Writing `A(τ) = log (s / K) + (r + σ² / 2) τ = σ √τ d₊`, the gamma `φ(d₊) / (s σ √τ)` is
  -- `d₊ φ(d₊) / (s A(τ))`, where `d₊ φ(d₊) → 0` since `|d₊| → ∞` and `A(τ) → log (s / K) ≠ 0`.
  have hlog : log (s / K) ≠ 0 := by
    rw [Ne, log_eq_zero, not_or, not_or]
    refine ⟨(div_pos hs hK).ne', fun h => hsK ((div_eq_one_iff_eq hK.ne').1 h), ?_⟩
    linarith [div_pos hs hK]
  have hA : Tendsto (fun u => s * (log (s / K) + (r + σ ^ 2 / 2) * u)) (𝓝[>] 0)
      (𝓝 (s * (log (s / K) + (r + σ ^ 2 / 2) * 0))) := by
    have h : Continuous fun u => s * (log (s / K) + (r + σ ^ 2 / 2) * u) := by fun_prop
    exact (h.continuousWithinAt (s := Ioi 0) (x := 0)).tendsto
  rw [mul_zero, add_zero] at hA
  have hd : Tendsto (dPlus s r σ K) (𝓝[>] 0) (cocompact ℝ) := by
    rcases hsK.lt_or_gt with hsK | hsK
    · exact (tendsto_dPlus_maturity_atBot (r := r) hσ hs hsK).mono_right atBot_le_cocompact
    · exact (tendsto_dPlus_maturity_atTop (r := r) hσ hK hsK).mono_right atTop_le_cocompact
  have h := (tendsto_mul_gaussianPDFReal_zero_one_cocompact.comp hd).div hA
    (mul_ne_zero hs.ne' hlog)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hA.eventually_ne (mul_ne_zero hs.ne' hlog)] with u hu hAu
  have hsq := (sqrt_pos.2 hu).ne'
  have hdu : dPlus s r σ K u = (log (s / K) + (r + σ ^ 2 / 2) * u) / (σ * √u) := dPlus_def ..
  rw [(hasDerivAt_deriv_callPrice_spot hs hK hσ.ne' hu).deriv, Pi.div_apply,
    Function.comp_apply, hdu]
  have hA0 : log (s / K) + (r + σ ^ 2 / 2) * u ≠ 0 := right_ne_zero_of_mul hAu
  have := hs.ne'
  have := hσ.ne'
  generalize gaussianPDFReal 0 1 _ = c
  generalize log (s / K) + (r + σ ^ 2 / 2) * u = A at hA0 ⊢
  field_simp

/-- **Gamma at the money near maturity.** At the spot `s = K`, `√τ` times the call gamma tends to
`1 / (K σ √(2π))` as the remaining maturity tends to `0⁺`. -/
theorem tendsto_sqrt_mul_deriv_deriv_callPrice_spot_strike (hσ : 0 < σ) (hK : 0 < K) :
    Tendsto (fun u => √u * deriv (deriv fun x => callPrice x r σ K u) K) (𝓝[>] 0)
      (𝓝 (1 / (K * σ * √(2 * π)))) := by
  have hφ : Continuous (gaussianPDFReal 0 1) := by
    simp_rw [funext gaussianPDFReal_zero_one]
    fun_prop
  have h := ((hφ.tendsto 0).comp (tendsto_dPlus_maturity_strike (r := r) hσ hK)).div_const
    (K * σ)
  rw [Function.comp_def, gaussianPDFReal_zero_one] at h
  refine (h.congr' ?_).trans (by simp [div_eq_inv_mul, mul_comm])
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hsq := (sqrt_pos.2 hu).ne'
  rw [(hasDerivAt_deriv_callPrice_spot hK hK hσ.ne' hu).deriv]
  field_simp

/-- **Gamma blows up at the money.** At the spot `s = K` the call gamma tends to `+∞` as the
remaining maturity tends to `0⁺`. -/
theorem tendsto_deriv_deriv_callPrice_spot_strike_atTop (hσ : 0 < σ) (hK : 0 < K) :
    Tendsto (fun u => deriv (deriv fun x => callPrice x r σ K u) K) (𝓝[>] 0) atTop := by
  have hsqrt : Tendsto (fun u : ℝ => √u) (𝓝[>] 0) (𝓝[>] 0) := by
    simpa using tendsto_mul_sqrt_nhdsGT_zero (σ := 1) one_pos
  have h := (tendsto_sqrt_mul_deriv_deriv_callPrice_spot_strike (r := r) hσ hK).pos_mul_atTop
    (by positivity) (tendsto_inv_nhdsGT_zero.comp hsqrt)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [Function.comp_apply, mul_comm, ← mul_assoc, inv_mul_cancel₀ (sqrt_pos.2 hu).ne', one_mul]

/-- For a positive maturity, put gamma and call gamma agree; as functions of the maturity they
are eventually equal as `τ → 0⁺`. -/
private theorem deriv_deriv_putPrice_spot_eventuallyEq (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) :
    (fun u => deriv (deriv fun x => putPrice x r σ K u) s) =ᶠ[𝓝[>] 0]
      fun u => deriv (deriv fun x => callPrice x r σ K u) s := by
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact deriv_deriv_putPrice_spot hs hK hσ.ne' hu

/-- For a fixed spot `s > 0` with `s ≠ K`, the put gamma tends to `0` as the remaining maturity
tends to `0⁺`. -/
theorem tendsto_deriv_deriv_putPrice_spot_maturity_zero (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K)
    (hsK : s ≠ K) :
    Tendsto (fun u => deriv (deriv fun x => putPrice x r σ K u) s) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_deriv_deriv_callPrice_spot_maturity_zero hs hσ hK hsK).congr'
    (deriv_deriv_putPrice_spot_eventuallyEq hs hσ hK).symm

/-- At the spot `s = K`, `√τ` times the put gamma tends to `1 / (K σ √(2π))` as the remaining
maturity tends to `0⁺`. -/
theorem tendsto_sqrt_mul_deriv_deriv_putPrice_spot_strike (hσ : 0 < σ) (hK : 0 < K) :
    Tendsto (fun u => √u * deriv (deriv fun x => putPrice x r σ K u) K) (𝓝[>] 0)
      (𝓝 (1 / (K * σ * √(2 * π)))) :=
  (tendsto_sqrt_mul_deriv_deriv_callPrice_spot_strike hσ hK).congr' <| by
    filter_upwards [deriv_deriv_putPrice_spot_eventuallyEq (r := r) hK hσ hK] with u hu
    rw [hu]

/-- At the spot `s = K` the put gamma tends to `+∞` as the remaining maturity tends to `0⁺`. -/
theorem tendsto_deriv_deriv_putPrice_spot_strike_atTop (hσ : 0 < σ) (hK : 0 < K) :
    Tendsto (fun u => deriv (deriv fun x => putPrice x r σ K u) K) (𝓝[>] 0) atTop :=
  (tendsto_deriv_deriv_callPrice_spot_strike_atTop hσ hK).congr'
    (deriv_deriv_putPrice_spot_eventuallyEq hK hσ hK).symm

end TauCeti.BlackScholes
