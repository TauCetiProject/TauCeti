/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Basic
import TauCeti.Probability.Finance.BlackScholes.Limits

/-!
# The Black–Scholes prices on the closed pricing domain

The closed-form Black–Scholes prices `callPrice` and `putPrice` of
`TauCeti.Probability.Finance.BlackScholes.Basic` are only meaningful for spot `s > 0` and remaining
maturity `τ > 0`: at `s = 0` or `τ = 0` the formulas for `d₊` and `d₋` divide by zero or take the
logarithm of zero. This file extends both prices to every `(s, τ)` by the discounted intrinsic
values

`C(s, τ) = (s - K e^{-rτ})⁺`,  `P(s, τ) = (K e^{-rτ} - s)⁺`  off `{s > 0, τ > 0}`.

On the boundary of the pricing domain these are the values the Black–Scholes problem prescribes:
the payoffs `(s - K)⁺` and `(K - s)⁺` at maturity `τ = 0`, and, for a strike `K ≥ 0`,
`C(0, τ) = 0` and `P(0, τ) = K e^{-rτ}` at zero spot.

For `σ > 0` and `K > 0` the extended prices are jointly continuous in `(s, τ)` on the whole plane,
in particular on the closed domain `s ≥ 0`, `τ ≥ 0`; they satisfy put–call parity everywhere and
the no-arbitrage bounds `0 ≤ C ≤ s` and `0 ≤ P ≤ K e^{-rτ}` for `s ≥ 0`; and in the interior they
agree with the closed forms, so they solve the Black–Scholes equation there. These are the
continuity, growth and terminal conditions under which a solution of the Black–Scholes equation
is compared with the closed-form price.

Continuity at an interior point is continuity of the closed forms
(`TauCeti.BlackScholes.continuousAt_callPrice`). At a maturity point
`(s₀, 0)` with `s₀ > 0` it combines the joint terminal limit
`TauCeti.BlackScholes.tendsto_callPrice_terminal` from the side `τ > 0` with continuity of the
intrinsic value from the side `τ ≤ 0`. At zero spot it is the squeeze `0 ≤ C ≤ s⁺`.

## Main declarations

* `TauCeti.BlackScholes.callValue`, `TauCeti.BlackScholes.putValue`: the extended prices.
* `TauCeti.BlackScholes.callValue_maturity_zero`,
  `TauCeti.BlackScholes.putValue_maturity_zero`: the payoffs at maturity.
* `TauCeti.BlackScholes.callValue_spot_zero`, `TauCeti.BlackScholes.putValue_spot_zero`: the
  values at zero spot.
* `TauCeti.BlackScholes.callValue_sub_putValue`: put–call parity.
* `TauCeti.BlackScholes.callValue_nonneg`, `TauCeti.BlackScholes.callValue_le`,
  `TauCeti.BlackScholes.putValue_nonneg`, `TauCeti.BlackScholes.putValue_le`: the no-arbitrage
  bounds `0 ≤ C ≤ s` and `0 ≤ P ≤ K e^{-rτ}`.
* `TauCeti.BlackScholes.continuous_callValue`, `TauCeti.BlackScholes.continuous_putValue`:
  joint continuity of the extended prices in the spot and the remaining maturity.
* `TauCeti.BlackScholes.callValue_pde`, `TauCeti.BlackScholes.putValue_pde`: the Black–Scholes
  equation in the interior.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
-/

public section

noncomputable section

open Filter ProbabilityTheory Real Set
open scoped Topology

namespace TauCeti.BlackScholes

variable {s r σ K τ : ℝ}

/-! ### The extended prices -/

/-- The Black–Scholes call price on the whole `(s, τ)`-plane: the closed form `callPrice` for spot
`s > 0` and remaining maturity `τ > 0`, and the discounted intrinsic value `(s - K e^{-rτ})⁺`
elsewhere. It is the payoff `(s - K)⁺` at maturity and, for a strike `K ≥ 0`, `0` at zero spot. -/
def callValue (s r σ K τ : ℝ) : ℝ :=
  if 0 < s ∧ 0 < τ then callPrice s r σ K τ else (s - K * exp (-r * τ))⁺

/-- The Black–Scholes put price on the whole `(s, τ)`-plane: the closed form `putPrice` for spot
`s > 0` and remaining maturity `τ > 0`, and the discounted intrinsic value `(K e^{-rτ} - s)⁺`
elsewhere. It is the payoff `(K - s)⁺` at maturity and, for a strike `K ≥ 0`, `K e^{-rτ}` at zero
spot. -/
def putValue (s r σ K τ : ℝ) : ℝ :=
  if 0 < s ∧ 0 < τ then putPrice s r σ K τ else (K * exp (-r * τ) - s)⁺

/-- Unfolding lemma for `callValue`. -/
theorem callValue_def (s r σ K τ : ℝ) :
    callValue s r σ K τ =
      if 0 < s ∧ 0 < τ then callPrice s r σ K τ else (s - K * exp (-r * τ))⁺ :=
  (rfl)

/-- Unfolding lemma for `putValue`. -/
theorem putValue_def (s r σ K τ : ℝ) :
    putValue s r σ K τ =
      if 0 < s ∧ 0 < τ then putPrice s r σ K τ else (K * exp (-r * τ) - s)⁺ :=
  (rfl)

/-- In the interior of the pricing domain the extended call is the closed-form price. -/
@[simp]
theorem callValue_of_pos (hs : 0 < s) (hτ : 0 < τ) : callValue s r σ K τ = callPrice s r σ K τ :=
  ite_eq_left ⟨hs, hτ⟩

/-- Off the interior of the pricing domain the extended call is the discounted intrinsic value. -/
theorem callValue_of_nonpos (h : s ≤ 0 ∨ τ ≤ 0) :
    callValue s r σ K τ = (s - K * exp (-r * τ))⁺ :=
  ite_eq_right fun h' => h.elim h'.1.not_ge h'.2.not_ge

/-- In the interior of the pricing domain the extended put is the closed-form price. -/
@[simp]
theorem putValue_of_pos (hs : 0 < s) (hτ : 0 < τ) : putValue s r σ K τ = putPrice s r σ K τ :=
  ite_eq_left ⟨hs, hτ⟩

/-- Off the interior of the pricing domain the extended put is the discounted intrinsic value. -/
theorem putValue_of_nonpos (h : s ≤ 0 ∨ τ ≤ 0) :
    putValue s r σ K τ = (K * exp (-r * τ) - s)⁺ :=
  ite_eq_right fun h' => h.elim h'.1.not_ge h'.2.not_ge

/-- **Call payoff at maturity.** At `τ = 0` the extended call is the payoff `(s - K)⁺`. -/
@[simp]
theorem callValue_maturity_zero (s r σ K : ℝ) : callValue s r σ K 0 = (s - K)⁺ := by
  simp [callValue_of_nonpos (Or.inr le_rfl)]

/-- **Put payoff at maturity.** At `τ = 0` the extended put is the payoff `(K - s)⁺`. -/
@[simp]
theorem putValue_maturity_zero (s r σ K : ℝ) : putValue s r σ K 0 = (K - s)⁺ := by
  simp [putValue_of_nonpos (Or.inr le_rfl)]

/-- **Call boundary at zero spot.** For a nonnegative strike the extended call vanishes at zero
spot. -/
@[simp]
theorem callValue_spot_zero (hK : 0 ≤ K) (r σ τ : ℝ) : callValue 0 r σ K τ = 0 := by
  rw [callValue_of_nonpos (Or.inl le_rfl), posPart_eq_zero, zero_sub, neg_nonpos]
  positivity

/-- **Put boundary at zero spot.** For a nonnegative strike the extended put at zero spot is the
discounted strike `K e^{-rτ}`. -/
@[simp]
theorem putValue_spot_zero (hK : 0 ≤ K) (r σ τ : ℝ) : putValue 0 r σ K τ = K * exp (-r * τ) := by
  rw [putValue_of_nonpos (Or.inl le_rfl), sub_zero, posPart_eq_self]
  positivity

/-- **Put–call parity** for the extended prices: `C - P = s - K e^{-rτ}` at every `(s, τ)`. -/
theorem callValue_sub_putValue (s r σ K τ : ℝ) :
    callValue s r σ K τ - putValue s r σ K τ = s - K * exp (-r * τ) := by
  by_cases h : 0 < s ∧ 0 < τ
  · rw [callValue_of_pos h.1 h.2, putValue_of_pos h.1 h.2, callPrice_sub_putPrice]
  · have h' : s ≤ 0 ∨ τ ≤ 0 := by contrapose! h; exact h
    rw [callValue_of_nonpos h', putValue_of_nonpos h',
      ← neg_sub s (K * exp (-r * τ)), posPart_neg, posPart_sub_negPart]

/-- Put–call parity, solved for the extended put. -/
theorem putValue_eq_callValue (s r σ K τ : ℝ) :
    putValue s r σ K τ = callValue s r σ K τ - s + K * exp (-r * τ) := by
  linear_combination -callValue_sub_putValue s r σ K τ

/-! ### No-arbitrage bounds -/

/-- The extended call is nonnegative. -/
theorem callValue_nonneg (hσ : 0 < σ) (hK : 0 < K) (s r τ : ℝ) : 0 ≤ callValue s r σ K τ := by
  by_cases h : 0 < s ∧ 0 < τ
  · rw [callValue_of_pos h.1 h.2]
    exact callPrice_nonneg h.1 hσ hK h.2
  · rw [callValue_of_nonpos (by contrapose! h; exact h)]
    exact posPart_nonneg _

/-- The extended put is nonnegative. -/
theorem putValue_nonneg (hσ : 0 < σ) (hK : 0 < K) (s r τ : ℝ) : 0 ≤ putValue s r σ K τ := by
  by_cases h : 0 < s ∧ 0 < τ
  · rw [putValue_of_pos h.1 h.2]
    exact putPrice_nonneg h.1 hσ hK h.2
  · rw [putValue_of_nonpos (by contrapose! h; exact h)]
    exact posPart_nonneg _

/-- For a nonnegative spot and strike the extended call is at most the spot. -/
theorem callValue_le (hs : 0 ≤ s) (hK : 0 ≤ K) : callValue s r σ K τ ≤ s := by
  by_cases h : 0 < s ∧ 0 < τ
  · rw [callValue_of_pos h.1 h.2]
    exact callPrice_le hs hK
  · rw [callValue_of_nonpos (by contrapose! h; exact h), posPart_def]
    have : 0 ≤ K * exp (-r * τ) := by positivity
    exact sup_le (by linarith) hs

/-- For a nonnegative spot and strike the extended put is at most the discounted strike. -/
theorem putValue_le (hs : 0 ≤ s) (hK : 0 ≤ K) : putValue s r σ K τ ≤ K * exp (-r * τ) := by
  by_cases h : 0 < s ∧ 0 < τ
  · rw [putValue_of_pos h.1 h.2]
    exact putPrice_le hs hK
  · rw [putValue_of_nonpos (by contrapose! h; exact h), posPart_def]
    exact sup_le (by linarith) (by positivity)

/-! ### Continuity -/

/-- For a nonnegative strike the extended call is at most `s⁺` at every spot. -/
private theorem callValue_le_posPart (hK : 0 ≤ K) : callValue s r σ K τ ≤ s⁺ := by
  by_cases h : 0 < s ∧ 0 < τ
  · rw [posPart_eq_self.2 h.1.le]
    exact callValue_le h.1.le hK
  · rw [callValue_of_nonpos (by contrapose! h; exact h)]
    exact posPart_mono (sub_le_self _ (by positivity))

/-- The discounted intrinsic value `(s - K e^{-rτ})⁺` is jointly continuous. -/
private theorem continuous_callIntrinsic (r K : ℝ) :
    Continuous fun p : ℝ × ℝ => (p.1 - K * exp (-r * p.2))⁺ := by
  simp only [posPart_def]
  fun_prop

/-- **Joint continuity of the extended call.** For `σ > 0` and `K > 0` the extended Black–Scholes
call is jointly continuous in the spot and the remaining maturity. In particular it is continuous
on the closed pricing domain `s ≥ 0`, `τ ≥ 0`, up to zero spot and up to maturity. -/
theorem continuous_callValue (hσ : 0 < σ) (hK : 0 < K) :
    Continuous fun p : ℝ × ℝ => callValue p.1 r σ K p.2 := by
  refine continuous_iff_continuousAt.2 fun ⟨s, τ⟩ => ?_
  rcases le_or_gt s 0 with hs | hs
  · -- At nonpositive spot, squeeze between `0` and `s⁺`, which tends to `0`.
    have hval : callValue s r σ K τ = 0 := le_antisymm
      (callValue_le_posPart hK.le |>.trans (posPart_eq_zero.2 hs).le) (callValue_nonneg hσ hK s r τ)
    have hpos : Tendsto (fun p : ℝ × ℝ => p.1⁺) (𝓝 (s, τ)) (𝓝 0) := by
      have : Continuous fun p : ℝ × ℝ => p.1⁺ := by simp only [posPart_def]; fun_prop
      simpa [posPart_eq_zero.2 hs] using this.tendsto (s, τ)
    rw [ContinuousAt, hval]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpos
      (fun p => callValue_nonneg hσ hK p.1 r p.2) fun p => callValue_le_posPart hK.le
  rcases lt_trichotomy τ 0 with hτ | rfl | hτ
  · -- Before the domain in time, the extended call is locally the intrinsic value.
    refine ((continuous_callIntrinsic r K).continuousAt).congr ?_
    filter_upwards [continuousAt_snd.preimage_mem_nhds (Iio_mem_nhds hτ)] with p hp
    exact (callValue_of_nonpos (Or.inr hp.le)).symm
  · -- At maturity, combine the terminal limit for `τ > 0` with the intrinsic value for `τ ≤ 0`.
    have hnhds : 𝓝 ((s, 0) : ℝ × ℝ) = 𝓝 s ×ˢ 𝓝[≤] 0 ⊔ 𝓝 s ×ˢ 𝓝[>] 0 := by
      rw [nhds_prod_eq, ← Filter.prod_sup, nhdsLE_sup_nhdsGT]
    rw [ContinuousAt, callValue_maturity_zero, hnhds, tendsto_sup]
    constructor
    · have h := (continuous_callIntrinsic r K).tendsto (s, 0)
      rw [nhds_prod_eq] at h
      refine ((h.mono_left (prod_mono le_rfl nhdsWithin_le_nhds)).congr' ?_).trans_eq (by simp)
      filter_upwards [prod_mem_prod univ_mem self_mem_nhdsWithin] with p hp
      exact (callValue_of_nonpos (Or.inr hp.2)).symm
    · refine (tendsto_callPrice_terminal (r := r) hs hσ hK).congr' ?_
      filter_upwards [prod_mem_prod (Ioi_mem_nhds hs) self_mem_nhdsWithin] with p hp
      exact (callValue_of_pos hp.1 hp.2).symm
  · -- In the interior, the extended call is locally the closed form.
    refine (continuousAt_callPrice (r := r) hs hσ.ne' hK hτ).congr ?_
    filter_upwards [(isOpen_Ioi.prod isOpen_Ioi).mem_nhds (mk_mem_prod hs hτ)] with p hp
    exact (callValue_of_pos hp.1 hp.2).symm

/-- **Joint continuity of the extended put.** For `σ > 0` and `K > 0` the extended Black–Scholes
put is jointly continuous in the spot and the remaining maturity. In particular it is continuous
on the closed pricing domain `s ≥ 0`, `τ ≥ 0`, up to zero spot and up to maturity. -/
theorem continuous_putValue (hσ : 0 < σ) (hK : 0 < K) :
    Continuous fun p : ℝ × ℝ => putValue p.1 r σ K p.2 := by
  simp only [putValue_eq_callValue]
  exact ((continuous_callValue hσ hK).sub continuous_fst).add (by fun_prop)

/-! ### The Black–Scholes equation -/

/-- **The Black–Scholes equation for the extended call.** In calendar time `t < T` and at spot
`s > 0`, the extended call `C(s, t) = callValue s r σ K (T - t)` satisfies
`∂C/∂t + σ² s² / 2 ∂²C/∂s² + r (s ∂C/∂s - C) = 0`. -/
theorem callValue_pde (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) {T t : ℝ} (ht : t < T) :
    deriv (fun u => callValue s r σ K (T - u)) t +
      σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => callValue x r σ K (T - t)) s +
      r * (s * deriv (fun x => callValue x r σ K (T - t)) s - callValue s r σ K (T - t)) = 0 := by
  have hτ : 0 < T - t := sub_pos.2 ht
  have hspot : (fun x => callValue x r σ K (T - t)) =ᶠ[𝓝 s]
      fun x => callPrice x r σ K (T - t) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact callValue_of_pos hx hτ
  have htime : (fun u => callValue s r σ K (T - u)) =ᶠ[𝓝 t]
      fun u => callPrice s r σ K (T - u) := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact callValue_of_pos hs (sub_pos.2 hu)
  rw [htime.deriv_eq, hspot.deriv.deriv_eq, hspot.deriv_eq, callValue_of_pos hs hτ]
  exact callPrice_pde hs hK hσ ht

/-- **The Black–Scholes equation for the extended put.** In calendar time `t < T` and at spot
`s > 0`, the extended put `P(s, t) = putValue s r σ K (T - t)` satisfies
`∂P/∂t + σ² s² / 2 ∂²P/∂s² + r (s ∂P/∂s - P) = 0`. -/
theorem putValue_pde (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) {T t : ℝ} (ht : t < T) :
    deriv (fun u => putValue s r σ K (T - u)) t +
      σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => putValue x r σ K (T - t)) s +
      r * (s * deriv (fun x => putValue x r σ K (T - t)) s - putValue s r σ K (T - t)) = 0 := by
  have hτ : 0 < T - t := sub_pos.2 ht
  have hspot : (fun x => putValue x r σ K (T - t)) =ᶠ[𝓝 s]
      fun x => putPrice x r σ K (T - t) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact putValue_of_pos hx hτ
  have htime : (fun u => putValue s r σ K (T - u)) =ᶠ[𝓝 t]
      fun u => putPrice s r σ K (T - u) := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact putValue_of_pos hs (sub_pos.2 hu)
  rw [htime.deriv_eq, hspot.deriv.deriv_eq, hspot.deriv_eq, putValue_of_pos hs hτ]
  exact putPrice_pde hs hK hσ ht

end TauCeti.BlackScholes
