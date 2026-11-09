/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.Second
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The pricing equation in log-spot coordinates

For a stock with local volatility `σ` and a bond with short rate `r`, the price `C(s, t)` of a
claim on the stock, as a function of the spot `s > 0` and calendar time `t`, solves the pricing
equation

`C_t + σ² s² / 2 C_ss + r (s C_s - C) = 0`.

Its spatial operator degenerates at `s = 0` and has coefficients growing with `s`. In the
log-spot variable `y = log s`, with `C(s, t) = u(log s, t)`, it becomes

`u_t + σ² / 2 u_yy + (r - σ² / 2) u_y - r u = 0`,

an equation on the whole line with diffusion `σ² / 2`, drift `r - σ² / 2` (the risk-neutral
drift of the log-spot) and potential `-r`. These coefficients are bounded whenever `σ` and `r`
are. The equation is backward parabolic, and whole-space parabolic existence and uniqueness
theory applies to it, only under further hypotheses that this file does not impose: uniform
ellipticity (`σ²` bounded below by a positive constant) and the regularity of the coefficients
(for instance Hölder continuity) required by the existence theorem used. The identities proved
here need neither: they are pointwise, assume only local differentiability of the price, and hold
for arbitrary real `σ` and `r` (including `σ = 0`), which may be the values `σ(s, t)` and `r(t)`
of a local volatility and a time-dependent rate at the point under consideration.

Both directions of the change of variables are stated: `TauCeti.Finance.pde_comp_log` transports a
function of the log-spot to a function of the spot, and `TauCeti.Finance.pde_comp_exp` a function
of the spot to a function of the log-spot. They rest on the chain rules `s ∂ₛ = ∂_y` and
`s² ∂ₛ² = ∂_y² - ∂_y` (`TauCeti.mul_deriv_comp_log`, `TauCeti.sq_mul_deriv_deriv_comp_log`,
`TauCeti.deriv_deriv_comp_exp`).

A price of linear growth in the spot, `|C(s, t)| ≤ A (1 + s)`, becomes in log-spot coordinates a
function `u` with `u / (1 + exp y)` bounded. The logarithm of the weight `1 + exp y` has bounded,
Hölder continuous derivatives of every positive order: they are the derivatives of the sigmoid
(`Real.iteratedDeriv_succ_log_one_add_exp`, `Real.memHolder_iteratedDeriv_sigmoid`).
Dividing by this weight conjugates the log-spot operator to one with bounded coefficients: with
`a = σ² / 2` and the sigmoid `p = e^y / (1 + e^y)`, the function `w = u / (1 + e^y)` satisfies
`w_t + a w_yy + (r + a (2 p - 1)) w_y - r (1 - p) w = 0` exactly when `u` solves the log-spot
equation (`TauCeti.Finance.pde_comp_exp_div_one_add_exp`).

## Main declarations

* `TauCeti.Finance.pde_comp_log`, `TauCeti.Finance.pde_comp_exp`: the pricing operator in
  log-spot coordinates.
* `TauCeti.Finance.pde_comp_exp_div_one_add_exp`: the pricing operator in log-spot coordinates
  divided by the weight `1 + e^y`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5 and §6.4.
* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*, Cambridge
  University Press, 1995, §5.4.
-/

public section

open Real Filter Topology

namespace TauCeti.Finance

variable {s y : ℝ}

/-- **The pricing equation in log-spot coordinates.** For `C(s, t) = u(log s, t)` at a spot
`s ≠ 0`, the pricing operator `C_t + σ² s² / 2 C_ss + r (s C_s - C)` equals the log-spot operator
`u_t + σ² / 2 u_yy + (r - σ² / 2) u_y - r u` at `y = log s`. The volatility `σ` and the rate `r`
are arbitrary reals, so they may be the values of a local volatility and a time-dependent rate at
`(s, t)`. -/
theorem pde_comp_log {u : ℝ → ℝ → ℝ} {t : ℝ} (σ r : ℝ)
    (hu' : DifferentiableAt ℝ (deriv fun y => u y t) (log s)) (hs : s ≠ 0) :
    deriv (fun t' => u (log s) t') t +
        σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => u (log x) t) s +
        r * (s * deriv (fun x => u (log x) t) s - u (log s) t) =
      deriv (fun t' => u (log s) t') t + σ ^ 2 / 2 * deriv (deriv fun y => u y t) (log s) +
        (r - σ ^ 2 / 2) * deriv (fun y => u y t) (log s) - r * u (log s) t := by
  have h₁ := mul_deriv_comp_log (v := fun y => u y t) hs
  have h₂ := sq_mul_deriv_deriv_comp_log (v := fun y => u y t) hu' hs
  linear_combination σ ^ 2 / 2 * h₂ + r * h₁

/-- **The pricing equation in log-spot coordinates.** For a function `C(s, t)` of the spot and
`u(y, t) = C(e^y, t)`, the log-spot operator `u_t + σ² / 2 u_yy + (r - σ² / 2) u_y - r u` at `y`
equals the pricing operator `C_t + σ² s² / 2 C_ss + r (s C_s - C)` at the spot `s = e^y`. The
volatility `σ` and the rate `r` are arbitrary reals, so they may be the values of a local
volatility and a time-dependent rate at `(e^y, t)`. -/
theorem pde_comp_exp {C : ℝ → ℝ → ℝ} {t : ℝ} (σ r : ℝ)
    (hC : ∀ᶠ x in 𝓝 (exp y), DifferentiableAt ℝ (fun x => C x t) x)
    (hC' : DifferentiableAt ℝ (deriv fun x => C x t) (exp y)) :
    deriv (fun t' => C (exp y) t') t + σ ^ 2 / 2 * deriv (deriv fun y => C (exp y) t) y +
        (r - σ ^ 2 / 2) * deriv (fun y => C (exp y) t) y - r * C (exp y) t =
      deriv (fun t' => C (exp y) t') t +
        σ ^ 2 * exp y ^ 2 / 2 * deriv (deriv fun x => C x t) (exp y) +
        r * (exp y * deriv (fun x => C x t) (exp y) - C (exp y) t) := by
  have h₁ : HasDerivAt (fun y => C (exp y) t) (deriv (fun x => C x t) (exp y) * exp y) y :=
    hC.self_of_nhds.hasDerivAt.comp y (hasDerivAt_exp y)
  rw [deriv_deriv_comp_exp (f := fun x => C x t) hC', h₁.deriv]
  ring

/-- **The pricing equation in weighted log-spot coordinates.** For a function `C(s, t)` of the
spot, differentiable in the spot near `e^y` with spot derivative differentiable at `e^y`, and
`w(y, t) = C(e^y, t) / (1 + e^y)`, the operator
`w_t + a w_yy + (r + a (e^y - 1) / (e^y + 1)) w_y - r / (1 + e^y) w` with `a = σ² / 2` at `y`
equals the pricing operator `C_t + σ² s² / 2 C_ss + r (s C_s - C)` at the spot `s = e^y`, divided
by the weight `1 + e^y`. The coefficients of the weighted operator are bounded whenever `σ` and
`r` are. -/
theorem pde_comp_exp_div_one_add_exp {C : ℝ → ℝ → ℝ} {t : ℝ} (σ r : ℝ)
    (hC : ∀ᶠ x in 𝓝 (exp y), DifferentiableAt ℝ (fun x => C x t) x)
    (hC' : DifferentiableAt ℝ (deriv fun x => C x t) (exp y)) :
    deriv (fun t' => C (exp y) t' / (1 + exp y)) t +
        σ ^ 2 / 2 * deriv (deriv fun y => C (exp y) t / (1 + exp y)) y +
        (r + σ ^ 2 / 2 * ((exp y - 1) / (exp y + 1))) *
          deriv (fun y => C (exp y) t / (1 + exp y)) y -
        r / (1 + exp y) * (C (exp y) t / (1 + exp y)) =
      (deriv (fun t' => C (exp y) t') t +
          σ ^ 2 * exp y ^ 2 / 2 * deriv (deriv fun x => C x t) (exp y) +
          r * (exp y * deriv (fun x => C x t) (exp y) - C (exp y) t)) /
        (1 + exp y) := by
  set w : ℝ → ℝ := fun y => C (exp y) t / (1 + exp y)
  have hψ (z : ℝ) : 1 + exp z ≠ 0 := (add_pos one_pos (exp_pos z)).ne'
  have hψd (z : ℝ) : HasDerivAt (fun z => 1 + exp z) (exp z) z := (hasDerivAt_exp z).const_add 1
  have hCe : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (fun x => C x t) (exp z) :=
    continuous_exp.continuousAt.eventually hC
  have hgd {z : ℝ} (hz : DifferentiableAt ℝ (fun x => C x t) (exp z)) :
      HasDerivAt (fun z => C (exp z) t) (deriv (fun x => C x t) (exp z) * exp z) z :=
    hz.hasDerivAt.comp z (hasDerivAt_exp z)
  have hwd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ w z := by
    filter_upwards [hCe] with z hz
    exact (hgd hz).differentiableAt.div (hψd z).differentiableAt (hψ z)
  -- Near `y`, the derivative of `w` is given by the quotient rule, differentiable at `y`.
  have hw' : deriv w =ᶠ[𝓝 y] fun z => (deriv (fun x => C x t) (exp z) * exp z * (1 + exp z) -
      C (exp z) t * exp z) / (1 + exp z) ^ 2 := by
    filter_upwards [hCe] with z hz
    exact ((hgd hz).div (hψd z) (hψ z)).deriv
  have hwd' : DifferentiableAt ℝ (deriv w) y := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hw'
    have h₁ : DifferentiableAt ℝ (fun z => deriv (fun x => C x t) (exp z) * exp z) y :=
      (hC'.comp y differentiableAt_exp).mul differentiableAt_exp
    have h₂ : DifferentiableAt ℝ (fun z => C (exp z) t * exp z) y :=
      (hgd hC.self_of_nhds).differentiableAt.mul differentiableAt_exp
    exact ((h₁.mul (hψd y).differentiableAt).sub h₂).div ((hψd y).differentiableAt.pow 2)
      (pow_ne_zero 2 (hψ y))
  -- The log-spot price `g(y) = C(e^y, t)` is the weight times `w`; differentiate the product.
  have hgw : (fun y => C (exp y) t) = fun z => (1 + exp z) * w z := by
    ext z
    simp only [w]
    field_simp [hψ z]
  have hg' : deriv (fun y => C (exp y) t) =ᶠ[𝓝 y]
      fun z => exp z * w z + (1 + exp z) * deriv w z := by
    filter_upwards [hwd] with z hz
    rw [hgw]
    exact ((hψd z).mul hz.hasDerivAt).deriv
  have hg'' : deriv (deriv fun y => C (exp y) t) y =
      exp y * w y + exp y * deriv w y + (exp y * deriv w y + (1 + exp y) * deriv (deriv w) y) := by
    rw [hg'.deriv_eq]
    exact (((hasDerivAt_exp y).mul hwd.self_of_nhds.hasDerivAt).add
      ((hψd y).mul hwd'.hasDerivAt)).deriv
  rw [← pde_comp_exp σ r hC hC', hg'', hg'.self_of_nhds, deriv_div_const]
  have hwy : C (exp y) t = (1 + exp y) * w y := congrFun hgw y
  rw [hwy]
  have h1 : exp y + 1 ≠ 0 := by rw [add_comm]; exact hψ y
  field_simp [hψ y, h1]
  ring

end TauCeti.Finance
