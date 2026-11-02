/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.Second
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

## Main declarations

* `TauCeti.Finance.pde_comp_log`, `TauCeti.Finance.pde_comp_exp`: the pricing operator in
  log-spot coordinates.

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
    (hu : ∀ᶠ y in 𝓝 (log s), DifferentiableAt ℝ (fun y => u y t) y)
    (hu' : DifferentiableAt ℝ (deriv fun y => u y t) (log s)) (hs : s ≠ 0) :
    deriv (fun t' => u (log s) t') t +
        σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => u (log x) t) s +
        r * (s * deriv (fun x => u (log x) t) s - u (log s) t) =
      deriv (fun t' => u (log s) t') t + σ ^ 2 / 2 * deriv (deriv fun y => u y t) (log s) +
        (r - σ ^ 2 / 2) * deriv (fun y => u y t) (log s) - r * u (log s) t := by
  have h₁ := mul_deriv_comp_log hu.self_of_nhds hs
  have h₂ := sq_mul_deriv_deriv_comp_log hu hu' hs
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
  rw [deriv_deriv_comp_exp (f := fun x => C x t) hC hC', h₁.deriv]
  ring

end TauCeti.Finance
