/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Probability.Finance.BlackScholes.Basic
public import TauCeti.Probability.Finance.MarketImpact.Clearing
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Probability.Finance.BlackScholes.Greeks

/-!
# Feedback volatility of market clearing with program trading

In the feedback model of Sircar and Papanicolaou, reference traders with income `y > 0` demand
`d₀ y ^ γ / x` units of an asset at price `x > 0`, and program traders demand `H(x)`. With total
supply one, the market clears at the positive price `x = ψ(y)` solving

`x (1 - H(x)) = d₀ y ^ γ`,

the *equilibrium price* `TauCeti.Finance.linearEquilibriumPrice H d₀ γ y`. If the income follows
`dY = μ Y dt + η Y dW`, Itô's formula makes `X = ψ(Y)` a diffusion with Brownian loading
`η Y ψ'(Y)`. This file computes that loading. With `h = H(x)` and `k = H'(x)` it is the
*feedback volatility* (`TauCeti.Finance.linearFeedbackVolatility`)

`σ_fb = σ x (1 - h) / (1 - h - x k)`,  `σ = γ η`,

of `TauCeti.Finance.mul_mul_deriv_linearEquilibriumPrice`. Without program trading it is the
Black–Scholes coefficient `σ x`. The second derivative `ψ''`, which enters the drift of `X`, is
`(v' v - v) / y²` for `v(x) = σ_fb(x) / η`
(`TauCeti.Finance.hasDerivAt_deriv_linearEquilibriumPrice`).

Replicating a claim of price `C(x, t)` in this market leads to the Black–Scholes equation with
`σ_fb` in place of `σ x`. Its residual is `TauCeti.Finance.linearFeedbackResidual`; with no
program trading it is the Black–Scholes residual (`TauCeti.Finance.linearFeedbackResidual_zero`),
solved for example by the call price. For a single hedged claim, `H = ρ C_x`, so `k = ρ C_xx`
and the diffusion term `σ_fb² C_xx / 2` is a nonlinear function of the gamma `Γ = C_xx`. Its
derivative in `Γ` is

`σ² x² (1 - h)² (1 - h + ρ x Γ) / (2 (1 - h - ρ x Γ) ³)`

(`TauCeti.Finance.hasDerivAt_linearFeedbackVolatility_sq_div_two_mul`). Where both `1 - h - ρ x Γ`
and `1 - h + ρ x Γ` are positive the equation is therefore parabolic: the diffusion term is
strictly increasing in `Γ` there
(`TauCeti.Finance.strictMonoOn_linearFeedbackVolatility_sq_div_two_mul`). For `σ x > 0`, the
feedback volatility then also exceeds half the no-feedback volatility
(`TauCeti.Finance.mul_div_two_lt_linearFeedbackVolatility`).

The derivatives of `ψ` are spatial: for program-trader demand depending on time, `ψ` also has a
time derivative, which this file does not compute.

## References

* R. Sircar, G. Papanicolaou, *General Black–Scholes models accounting for increased market
  volatility from hedging strategies*, Applied Mathematical Finance 5 (1998), 45–82, §2,
  equations (2.23)–(2.24).
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti.Finance

variable {H : ℝ → ℝ} {σ x h k d₀ γ y : ℝ}

/-! ### The feedback volatility -/

/-- The feedback volatility `σ x (1 - h) / (1 - h - x k)` at asset price `x`, for program-trader
demand level `h` and demand slope `k` at `x`. It is the diffusion coefficient of the asset price
when market clearing transmits an income volatility producing the Black–Scholes coefficient
`σ x` in the absence of program trading. -/
def linearFeedbackVolatility (σ x h k : ℝ) : ℝ :=
  σ * x * (1 - h) / (1 - h - x * k)

/-- Unfold the feedback volatility. -/
theorem linearFeedbackVolatility_def (σ x h k : ℝ) :
    linearFeedbackVolatility σ x h k = σ * x * (1 - h) / (1 - h - x * k) :=
  (rfl)

/-- Without program trading the feedback volatility is the Black–Scholes coefficient `σ x`. -/
@[simp]
theorem linearFeedbackVolatility_zero_zero (σ x : ℝ) :
    linearFeedbackVolatility σ x 0 0 = σ * x := by
  simp [linearFeedbackVolatility_def]

/-- The feedback volatility is linear in the no-feedback volatility `σ`. -/
theorem linearFeedbackVolatility_mul (a σ x h k : ℝ) :
    linearFeedbackVolatility (a * σ) x h k = a * linearFeedbackVolatility σ x h k := by
  simp only [linearFeedbackVolatility_def]
  ring

/-- With positive clearing factor `1 - h` and clearing derivative `1 - h - x k`, the feedback
volatility of a positive price is positive. -/
theorem linearFeedbackVolatility_pos (hσ : 0 < σ) (hx : 0 < x) (h₁ : 0 < 1 - h)
    (h₂ : 0 < 1 - h - x * k) : 0 < linearFeedbackVolatility σ x h k := by
  rw [linearFeedbackVolatility_def]
  positivity

/-- If `1 - h - x k` and `1 - h + x k` are both positive, the feedback volatility exceeds half the
no-feedback volatility `σ x`, for `σ x > 0`. -/
theorem mul_div_two_lt_linearFeedbackVolatility (hσx : 0 < σ * x) (h₂ : 0 < 1 - h - x * k)
    (h₃ : 0 < 1 - h + x * k) : σ * x / 2 < linearFeedbackVolatility σ x h k := by
  rw [linearFeedbackVolatility_def, lt_div_iff₀ h₂]
  nlinarith

/-! ### The equilibrium price and its diffusion coefficient -/

/-- The equilibrium price at income `y` for linear reference demand `d₀ y ^ γ / x` and
program-trader demand `H`: the positive solution `x` of `x (1 - H(x)) = d₀ y ^ γ`, when it is
unique (`TauCeti.Finance.linearEquilibriumPrice_eq`,
`TauCeti.Finance.existsUnique_clearingMap_eq`). -/
def linearEquilibriumPrice (H : ℝ → ℝ) (d₀ γ y : ℝ) : ℝ :=
  invFunOn (clearingMap H) (Ioi 0) (d₀ * y ^ γ)

/-- Unfold the equilibrium price. -/
theorem linearEquilibriumPrice_def (H : ℝ → ℝ) (d₀ γ y : ℝ) :
    linearEquilibriumPrice H d₀ γ y = invFunOn (clearingMap H) (Ioi 0) (d₀ * y ^ γ) :=
  (rfl)

section Pos

variable (hH : DifferentiableOn ℝ H (Ioi 0)) (hpos : ∀ x, 0 < x → 0 < 1 - H x - x * deriv H x)
include hH hpos

/-- Under a positive clearing derivative, a positive price clearing the market at income `y` is
the equilibrium price. -/
theorem linearEquilibriumPrice_eq (hx : 0 < x) (hxy : clearingMap H x = d₀ * y ^ γ) :
    linearEquilibriumPrice H d₀ γ y = x := by
  rw [linearEquilibriumPrice_def, ← hxy, invFunOn_clearingMap hH hpos hx]

/-- Under a positive clearing derivative, the equilibrium price is differentiable in the income
`y > 0` wherever it clears the market at a positive price `x`, with derivative
`σ_fb / y` for the feedback volatility `σ_fb` with `σ = γ`. -/
theorem hasDerivAt_linearEquilibriumPrice (hy : 0 < y) (hx : 0 < x)
    (hxy : clearingMap H x = d₀ * y ^ γ) :
    HasDerivAt (linearEquilibriumPrice H d₀ γ)
      (linearFeedbackVolatility γ x (H x) (deriv H x) / y) y := by
  have hinv := hasDerivAt_invFunOn_clearingMap hH hpos hx
  rw [hxy] at hinv
  rw [show linearEquilibriumPrice H d₀ γ = invFunOn (clearingMap H) (Ioi 0) ∘ fun y ↦ d₀ * y ^ γ
    from funext fun y ↦ linearEquilibriumPrice_def H d₀ γ y]
  have hc := hinv.comp y (((Real.hasDerivAt_rpow_const (p := γ) (Or.inl hy.ne')).const_mul d₀))
  convert hc using 1
  have hD := (hpos x hx).ne'
  rw [clearingMap_def] at hxy
  rw [linearFeedbackVolatility_def, Real.rpow_sub_one hy.ne', mul_assoc γ, hxy]
  ring

/-- **Feedback volatility.** If the income has percentage volatility `η`, the Brownian loading
`η y ψ'(y)` of the equilibrium price `ψ` at a positive income `y` clearing at the positive price
`x` is the feedback volatility `γ η x (1 - H(x)) / (1 - H(x) - x H'(x))`. -/
theorem mul_mul_deriv_linearEquilibriumPrice (η : ℝ) (hy : 0 < y) (hx : 0 < x)
    (hxy : clearingMap H x = d₀ * y ^ γ) :
    η * y * deriv (linearEquilibriumPrice H d₀ γ) y =
      linearFeedbackVolatility (γ * η) x (H x) (deriv H x) := by
  rw [(hasDerivAt_linearEquilibriumPrice hH hpos hy hx hxy).deriv, mul_comm γ,
    linearFeedbackVolatility_mul]
  field_simp

end Pos

section Margin

variable (hH : DifferentiableOn ℝ H (Ioi 0)) {δ : ℝ}
  (hmargin : ∀ x, 0 < x → δ ≤ 1 - H x - x * deriv H x)
  (hzero : Tendsto (clearingMap H) (𝓝[>] 0) (𝓝 0)) (hδ : 0 < δ)
include hH hmargin hzero hδ

/-- Under a strictly positive clearing-derivative margin and the zero limit at zero price, the
equilibrium price at a positive income is positive, for `d₀ > 0`. -/
theorem linearEquilibriumPrice_pos (hd₀ : 0 < d₀) (hy : 0 < y) :
    0 < linearEquilibriumPrice H d₀ γ y :=
  (bijOn_invFunOn_clearingMap hH hmargin hzero hδ).mapsTo
    (mul_pos hd₀ (Real.rpow_pos_of_pos hy γ))

/-- Under a strictly positive clearing-derivative margin and the zero limit at zero price, the
equilibrium price at a positive income clears the market, for `d₀ > 0`. -/
theorem clearingMap_linearEquilibriumPrice (hd₀ : 0 < d₀) (hy : 0 < y) :
    clearingMap H (linearEquilibriumPrice H d₀ γ y) = d₀ * y ^ γ :=
  clearingMap_invFunOn hH hmargin hzero hδ (mul_pos hd₀ (Real.rpow_pos_of_pos hy γ))

/-- Under a strictly positive clearing-derivative margin and the zero limit at zero price, the
derivative of the equilibrium price `ψ` is `ψ'(y) = v(ψ(y)) / y` at every positive income `y`,
where `v(x) = γ x (1 - H(x)) / (1 - H(x) - x H'(x))`, for `d₀ > 0`. -/
theorem deriv_linearEquilibriumPrice (hd₀ : 0 < d₀) (hy : 0 < y) :
    deriv (linearEquilibriumPrice H d₀ γ) y =
      linearFeedbackVolatility γ (linearEquilibriumPrice H d₀ γ y)
        (H (linearEquilibriumPrice H d₀ γ y))
        (deriv H (linearEquilibriumPrice H d₀ γ y)) / y :=
  (hasDerivAt_linearEquilibriumPrice hH (fun x hx ↦ hδ.trans_le (hmargin x hx)) hy
    (linearEquilibriumPrice_pos hH hmargin hzero hδ hd₀ hy)
    (clearingMap_linearEquilibriumPrice hH hmargin hzero hδ hd₀ hy)).deriv

/-- **Second derivative of the equilibrium price.** Under a strictly positive clearing-derivative
margin and the zero limit at zero price, let `v(x) = γ x (1 - H(x)) / (1 - H(x) - x H'(x))`
have derivative `v'` at the equilibrium price `x = ψ(y)` of a positive income `y`. Then
`ψ'' (y) = (v' v(x) - v(x)) / y²`, for `d₀ > 0`. -/
theorem hasDerivAt_deriv_linearEquilibriumPrice {v' : ℝ} (hd₀ : 0 < d₀) (hy : 0 < y)
    (hv : HasDerivAt (fun x ↦ linearFeedbackVolatility γ x (H x) (deriv H x)) v'
      (linearEquilibriumPrice H d₀ γ y)) :
    HasDerivAt (deriv (linearEquilibriumPrice H d₀ γ))
      ((v' * linearFeedbackVolatility γ (linearEquilibriumPrice H d₀ γ y)
          (H (linearEquilibriumPrice H d₀ γ y)) (deriv H (linearEquilibriumPrice H d₀ γ y)) -
        linearFeedbackVolatility γ (linearEquilibriumPrice H d₀ γ y)
          (H (linearEquilibriumPrice H d₀ γ y)) (deriv H (linearEquilibriumPrice H d₀ γ y))) /
        y ^ 2) y := by
  have hpos : ∀ x, 0 < x → 0 < 1 - H x - x * deriv H x := fun x hx ↦ hδ.trans_le (hmargin x hx)
  have hψ := hasDerivAt_linearEquilibriumPrice hH hpos hy
    (linearEquilibriumPrice_pos (γ := γ) hH hmargin hzero hδ hd₀ hy)
    (clearingMap_linearEquilibriumPrice hH hmargin hzero hδ hd₀ hy)
  have hq := (hv.comp y hψ).div (hasDerivAt_id y) hy.ne'
  refine (hq.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds hy] with y' hy'
    exact deriv_linearEquilibriumPrice hH hmargin hzero hδ hd₀ hy'
  · simp only [id_eq, comp_apply]
    field_simp

end Margin

/-! ### The feedback pricing equation -/

/-- The residual of the feedback pricing equation

`C_t + σ_fb² C_xx / 2 + r (x C_x - C)`

for a spot-first price `C(x, t)`, short rate `r`, no-feedback volatility `σ` and spot-first
program-trader demand `H(x, t)`, where `σ_fb` is the feedback volatility of the demand level
`H(x, t)` and slope `H_x(x, t)`. For a single hedged claim, `H = ρ C_x`. -/
def linearFeedbackResidual (r σ : ℝ) (H C : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun u ↦ C x u) t +
    linearFeedbackVolatility σ x (H x t) (deriv (fun z ↦ H z t) x) ^ 2 / 2 *
      deriv (deriv fun z ↦ C z t) x +
    r * (x * deriv (fun z ↦ C z t) x - C x t)

/-- Unfold the feedback pricing residual. -/
theorem linearFeedbackResidual_def (r σ : ℝ) (H C : ℝ → ℝ → ℝ) (x t : ℝ) :
    linearFeedbackResidual r σ H C x t =
      deriv (fun u ↦ C x u) t +
        linearFeedbackVolatility σ x (H x t) (deriv (fun z ↦ H z t) x) ^ 2 / 2 *
          deriv (deriv fun z ↦ C z t) x +
        r * (x * deriv (fun z ↦ C z t) x - C x t) :=
  (rfl)

/-- Without program trading the feedback pricing residual is the Black–Scholes residual
`C_t + σ² x² C_xx / 2 + r (x C_x - C)`. -/
theorem linearFeedbackResidual_zero (r σ : ℝ) (C : ℝ → ℝ → ℝ) (x t : ℝ) :
    linearFeedbackResidual r σ (fun _ _ ↦ 0) C x t =
      deriv (fun u ↦ C x u) t + σ ^ 2 * x ^ 2 / 2 * deriv (deriv fun z ↦ C z t) x +
        r * (x * deriv (fun z ↦ C z t) x - C x t) := by
  simp [linearFeedbackResidual_def, mul_pow]

/-- For a single claim hedged with `H = ρ C_x`, the feedback pricing residual is

`C_t + (σ x (1 - ρ C_x) / (1 - ρ C_x - ρ x C_xx))² C_xx / 2 + r (x C_x - C)`. -/
theorem linearFeedbackResidual_const_mul_deriv (r σ ρ : ℝ) (C : ℝ → ℝ → ℝ) (x t : ℝ) :
    linearFeedbackResidual r σ (fun z u ↦ ρ * deriv (fun w ↦ C w u) z) C x t =
      deriv (fun u ↦ C x u) t +
        (σ * x * (1 - ρ * deriv (fun z ↦ C z t) x) /
          (1 - ρ * deriv (fun z ↦ C z t) x - ρ * x * deriv (deriv fun z ↦ C z t) x)) ^ 2 / 2 *
          deriv (deriv fun z ↦ C z t) x +
        r * (x * deriv (fun z ↦ C z t) x - C x t) := by
  simp only [linearFeedbackResidual_def, linearFeedbackVolatility_def, deriv_const_mul_field]
  ring_nf

/-- Without program trading the Black–Scholes call price `C(s, t)` of strike `K > 0` and
maturity `T` solves the feedback pricing equation at every positive spot before maturity. -/
theorem linearFeedbackResidual_zero_callPrice (r σ : ℝ) {K T s t : ℝ} (hs : 0 < s) (hK : 0 < K)
    (ht : t < T) :
    linearFeedbackResidual r σ (fun _ _ ↦ 0)
      (fun x u ↦ BlackScholes.callPrice x r σ K (T - u)) s t = 0 := by
  rw [linearFeedbackResidual_zero]
  exact BlackScholes.callPrice_pde hs hK ht

/-! ### Parabolicity of the single-claim equation -/

/-- For a single claim with demand `ρ C_x` of level `h`, the diffusion term
`σ_fb² Γ / 2 = (σ x (1 - h) / (1 - h - ρ x Γ))² Γ / 2` of the feedback pricing equation, as a
function of the gamma `Γ`, has derivative
`σ² x² (1 - h)² (1 - h + ρ x Γ) / (2 (1 - h - ρ x Γ) ³)` wherever `1 - h - ρ x Γ ≠ 0`. -/
theorem hasDerivAt_linearFeedbackVolatility_sq_div_two_mul {ρ Γ : ℝ}
    (hΓ : 1 - h - x * (ρ * Γ) ≠ 0) :
    HasDerivAt (fun Γ ↦ linearFeedbackVolatility σ x h (ρ * Γ) ^ 2 / 2 * Γ)
      (σ ^ 2 * x ^ 2 * (1 - h) ^ 2 * (1 - h + x * (ρ * Γ)) / (2 * (1 - h - x * (ρ * Γ)) ^ 3))
      Γ := by
  simp only [linearFeedbackVolatility_def]
  have hden : HasDerivAt (fun Γ ↦ 1 - h - x * (ρ * Γ)) (-(x * ρ)) Γ := by
    simpa [mul_comm, mul_left_comm] using ((hasDerivAt_id Γ).const_mul (x * ρ)).const_sub (1 - h)
  have hq := (((hasDerivAt_const Γ (σ * x * (1 - h))).div hden hΓ).pow 2).div_const 2
  convert hq.mul (hasDerivAt_id Γ) using 1
  · ext Γ
    simp
  · simp only [id_eq, Pi.div_apply]
    norm_num
    field_simp
    ring

/-- For a single claim with demand `ρ C_x` of level `h`, the diffusion term
`(σ x (1 - h) / (1 - h - ρ x Γ))² Γ / 2` of the feedback pricing equation is strictly
increasing in the gamma `Γ` on the set where both `1 - h - ρ x Γ` and `1 - h + ρ x Γ` are
positive, provided `σ x (1 - h) ≠ 0`. -/
theorem strictMonoOn_linearFeedbackVolatility_sq_div_two_mul {ρ : ℝ} (hσx : σ * x * (1 - h) ≠ 0) :
    StrictMonoOn (fun Γ ↦ linearFeedbackVolatility σ x h (ρ * Γ) ^ 2 / 2 * Γ)
      {Γ | 0 < 1 - h - x * (ρ * Γ) ∧ 0 < 1 - h + x * (ρ * Γ)} := by
  set D := {Γ : ℝ | 0 < 1 - h - x * (ρ * Γ) ∧ 0 < 1 - h + x * (ρ * Γ)}
  have hD : IsOpen D := by
    simp only [D, ofPred_and]
    exact (isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt continuous_const (by fun_prop))
  have hconv : Convex ℝ D := by
    refine Set.OrdConnected.convex ⟨fun a ha b hb Γ hΓ ↦ ⟨?_, ?_⟩⟩ <;>
      rcases le_total 0 (x * ρ) with h0 | h0
    · nlinarith [hb.1, mul_le_mul_of_nonneg_left hΓ.2 h0]
    · nlinarith [ha.1, mul_le_mul_of_nonpos_left hΓ.1 h0]
    · nlinarith [ha.2, mul_le_mul_of_nonneg_left hΓ.1 h0]
    · nlinarith [hb.2, mul_le_mul_of_nonpos_left hΓ.2 h0]
  have hderiv : ∀ Γ ∈ D, HasDerivAt (fun Γ ↦ linearFeedbackVolatility σ x h (ρ * Γ) ^ 2 / 2 * Γ)
      (σ ^ 2 * x ^ 2 * (1 - h) ^ 2 * (1 - h + x * (ρ * Γ)) / (2 * (1 - h - x * (ρ * Γ)) ^ 3))
      Γ := fun Γ hΓ ↦ hasDerivAt_linearFeedbackVolatility_sq_div_two_mul hΓ.1.ne'
  refine strictMonoOn_of_deriv_pos hconv
    (fun Γ hΓ ↦ (hderiv Γ hΓ).continuousAt.continuousWithinAt) fun Γ hΓ ↦ ?_
  rw [hD.interior_eq] at hΓ
  rw [(hderiv Γ hΓ).deriv]
  have : 0 < σ ^ 2 * x ^ 2 * (1 - h) ^ 2 := by
    rw [← mul_pow, ← mul_pow]
    positivity
  have := hΓ.1
  have := hΓ.2
  positivity

end TauCeti.Finance
