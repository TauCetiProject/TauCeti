/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Extension
import TauCeti.Probability.Finance.BlackScholes.Smooth
import TauCeti.Probability.Finance.Comparison

/-!
# Uniqueness of the Black–Scholes call and put prices

Fix an interest rate `r`, a volatility `σ > 0`, a strike `K > 0` and an expiry `T`. This file
shows that the Black–Scholes prices are the only classical solutions of linear growth of the
Black–Scholes equation

`C_t + σ² s² / 2 C_ss + r (s C_s - C) = 0`,  `s > 0`, `0 < t < T`,

with the call payoff `(s - K)⁺`, respectively the put payoff `(K - s)⁺`, as terminal value at
`t = T`. Precisely, let `C(s, t)` be continuous on `s > 0`, `0 ≤ t ≤ T`, twice continuously
differentiable in the spot and differentiable in time for `s > 0`, `0 < t < T`, and satisfy
`|C(s, t)| ≤ A (1 + s)`. If `C` solves the equation with terminal value `(s - K)⁺`, then
`C(s, t) = callValue s r σ K (T - t)` for `s > 0` and `0 ≤ t ≤ T`
(`TauCeti.BlackScholes.eq_callValue_of_pde`); with terminal value `(K - s)⁺` it is the put price
`putValue s r σ K (T - t)` (`TauCeti.BlackScholes.eq_putValue_of_pde`).

Nothing is assumed at zero spot, and the time derivative is only required before expiry. By
`TauCeti.BlackScholes.riskNeutralPrice_call_eq_callValue` and
`TauCeti.BlackScholes.riskNeutralPrice_put_eq_putValue`, such a solution is therefore also the
discounted risk-neutral expectation of the payoff.

The extended prices themselves lie in this class: they are continuous up to maturity
(`TauCeti.BlackScholes.continuous_callValue`), smooth before expiry
(`ContDiffAt.callValue`), solve the equation (`TauCeti.BlackScholes.callValue_pde`), and satisfy
`0 ≤ C ≤ s` and `0 ≤ P ≤ K e^{-r (T - t)}`. Uniqueness is then the comparison principle for the
pricing equation in the linear-growth class, `TauCeti.Finance.eq_of_pde_eq_of_terminal_eq`,
applied with constant coefficients.

## Main declarations

* `TauCeti.BlackScholes.eq_callValue_of_pde`: uniqueness of the call price.
* `TauCeti.BlackScholes.eq_putValue_of_pde`: uniqueness of the put price.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964, Chapter 2,
  Section 4.
* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*, Cambridge
  University Press, 1995, §5.4.
-/

public section

open Real Set

namespace TauCeti.BlackScholes

variable {C : ℝ → ℝ → ℝ} {r σ K T A : ℝ}

/-- **Uniqueness of the Black–Scholes call price.** Let `σ > 0` and `K > 0`. Let `C(s, t)` be
continuous on `s > 0`, `0 ≤ t ≤ T`, twice continuously differentiable in the spot and
differentiable in time for `s > 0`, `0 < t < T`, with `|C(s, t)| ≤ A (1 + s)`. If `C` solves the
Black–Scholes equation `C_t + σ² s² / 2 C_ss + r (s C_s - C) = 0` for `s > 0`, `0 < t < T`, and
`C(s, T) = (s - K)⁺`, then `C` is the Black–Scholes call price:
`C(s, t) = callValue s r σ K (T - t)` for `s > 0` and `0 ≤ t ≤ T`. -/
theorem eq_callValue_of_pde (hσ : 0 < σ) (hK : 0 < K)
    (hC : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc 0 T))
    (hcd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
    (hdiff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ (fun u ↦ C s u) t)
    (hpde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T →
      deriv (fun u ↦ C s u) t + σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
        r * (s * deriv (fun x ↦ C x t) s - C s t) = 0)
    (hgrowth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc 0 T → |C s t| ≤ A * (1 + s))
    (hterminal : ∀ ⦃s⦄, 0 < s → C s T = (s - K)⁺) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc 0 T → C s t = callValue s r σ K (T - t) :=
  Finance.eq_of_pde_eq_of_terminal_eq (σ := fun _ _ ↦ σ) (r := fun _ ↦ r) (Λ := σ ^ 2)
    (R := |r|) (A := A + 1) (fun _ _ _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) hC
    ((continuous_callValue hσ hK).comp (by fun_prop : Continuous fun p : ℝ × ℝ ↦ (p.1, T - p.2))
      |>.continuousOn)
    (fun s hs t ht ↦ by
      -- `|C - callValue| ≤ |C| + callValue ≤ A (1 + s) + s`, since `0 ≤ callValue ≤ s`.
      linarith [abs_sub (C s t) (callValue s r σ K (T - t)), hgrowth hs ht,
        abs_of_nonneg (callValue_nonneg (K := K) hσ s r (T - t)),
        callValue_le (r := r) (σ := σ) (τ := T - t) hs.le hK.le])
    hcd (fun s hs t ht ↦
      contDiffAt_id.callValue contDiffAt_const hs (sub_pos.2 ht.2) (r := r) (σ := σ) (K := K))
    hdiff
    (fun s hs t ht ↦ (contDiffAt_const.callValue (contDiffAt_const.sub contDiffAt_id) hs
      (sub_pos.2 ht.2) (n := 1) (r := r) (σ := σ) (K := K)).differentiableAt one_ne_zero)
    (fun s hs t ht ↦ (hpde hs ht).trans (callValue_pde hs hK hσ.ne' ht.2).symm)
    (fun s hs ↦ by rw [hterminal hs, sub_self, callValue_maturity_zero])

/-- **Uniqueness of the Black–Scholes put price.** Let `σ > 0` and `K > 0`. Let `C(s, t)` be
continuous on `s > 0`, `0 ≤ t ≤ T`, twice continuously differentiable in the spot and
differentiable in time for `s > 0`, `0 < t < T`, with `|C(s, t)| ≤ A (1 + s)`. If `C` solves the
Black–Scholes equation `C_t + σ² s² / 2 C_ss + r (s C_s - C) = 0` for `s > 0`, `0 < t < T`, and
`C(s, T) = (K - s)⁺`, then `C` is the Black–Scholes put price:
`C(s, t) = putValue s r σ K (T - t)` for `s > 0` and `0 ≤ t ≤ T`. -/
theorem eq_putValue_of_pde (hσ : 0 < σ) (hK : 0 < K)
    (hC : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc 0 T))
    (hcd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
    (hdiff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ (fun u ↦ C s u) t)
    (hpde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T →
      deriv (fun u ↦ C s u) t + σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
        r * (s * deriv (fun x ↦ C x t) s - C s t) = 0)
    (hgrowth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc 0 T → |C s t| ≤ A * (1 + s))
    (hterminal : ∀ ⦃s⦄, 0 < s → C s T = (K - s)⁺) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc 0 T → C s t = putValue s r σ K (T - t) :=
  Finance.eq_of_pde_eq_of_terminal_eq (σ := fun _ _ ↦ σ) (r := fun _ ↦ r) (Λ := σ ^ 2)
    (R := |r|) (A := A + K * exp (|r| * T)) (fun _ _ _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) hC
    ((continuous_putValue hσ hK).comp (by fun_prop : Continuous fun p : ℝ × ℝ ↦ (p.1, T - p.2))
      |>.continuousOn)
    (fun s hs t ht ↦ by
      -- `0 ≤ putValue ≤ K e^{-r (T - t)} ≤ K e^{|r| T}`, since `0 ≤ T - t ≤ T`.
      have hP := putValue_nonneg hσ hK s r (T - t)
      have hexp : exp (-r * (T - t)) ≤ exp (|r| * T) := exp_le_exp.2 <| by
        nlinarith [neg_abs_le r, abs_nonneg r, ht.1, ht.2]
      have hle : putValue s r σ K (T - t) ≤ K * exp (|r| * T) :=
        (putValue_le hs.le hK.le).trans (mul_le_mul_of_nonneg_left hexp hK.le)
      have hKs : 0 ≤ K * exp (|r| * T) * s := by positivity
      linarith [abs_sub (C s t) (putValue s r σ K (T - t)), hgrowth hs ht, abs_of_nonneg hP])
    hcd (fun s hs t ht ↦
      contDiffAt_id.putValue contDiffAt_const hs (sub_pos.2 ht.2) (r := r) (σ := σ) (K := K))
    hdiff
    (fun s hs t ht ↦ (contDiffAt_const.putValue (contDiffAt_const.sub contDiffAt_id) hs
      (sub_pos.2 ht.2) (n := 1) (r := r) (σ := σ) (K := K)).differentiableAt one_ne_zero)
    (fun s hs t ht ↦ (hpde hs ht).trans (putValue_pde hs hK ht.2).symm)
    (fun s hs ↦ by rw [hterminal hs, sub_self, putValue_maturity_zero])

end TauCeti.BlackScholes
