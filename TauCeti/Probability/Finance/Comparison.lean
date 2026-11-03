/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeLine
import TauCeti.Probability.Finance.LogSpot

/-!
# Comparison and uniqueness for the pricing equation

For a stock with local volatility `σ(s, t)` and a bond with short rate `r(t)`, the price `C(s, t)`
of a claim on the stock, as a function of the spot `s > 0` and calendar time `t ∈ [0, T]`, solves
the pricing equation

`C_t + σ² s² / 2 C_ss + r (s C_s - C) = 0`,

with the payoff as terminal value at `t = T`. This file proves the comparison principle for this
equation in the class of prices of **linear growth** in the spot: if `C₁` and `C₂` are classical
solutions, `C₁ - C₂ ≤ A (1 + s)`, the pricing operator of `C₁` dominates that of `C₂` and
`C₁(·, T) ≤ C₂(·, T)`, then `C₁ ≤ C₂` (`TauCeti.Finance.le_of_pde_le_of_terminal_le`). In
particular a classical solution of the pricing equation with `|C(s, t)| ≤ A (1 + s)` is determined
by its terminal value (`TauCeti.Finance.eq_of_pde_eq_of_terminal_eq`). Calls, puts and the stock
itself have linear growth, so this is the uniqueness class in which prices of such claims are
characterised by their payoffs.

The volatility and the rate need only be bounded on `(0, T)`: no regularity, no positive lower
bound on `σ` (the equation may degenerate) and no sign of `r` is assumed. The solutions are
required to be continuous on `s > 0`, `0 ≤ t ≤ T`, twice continuously differentiable in `s` and
differentiable in `t` for `0 < t < T`; nothing is required at `s = 0`.

## The argument

The equation degenerates at `s = 0` and its coefficients grow with `s`. In the log-spot variable
`y = log s` it becomes `u_t + a u_yy + (r - a) u_y - r u = 0` with `a = σ² / 2`
(`TauCeti.Finance.pde_comp_exp`), and the linear-growth class becomes the class of `u` with
`u / (1 + e^y)` bounded. Dividing by the weight `1 + e^y`, whose logarithmic derivative is the
sigmoid `p = e^y / (1 + e^y)`, the function `w = u / (1 + e^y)` solves

`w_t + a w_yy + (r + a (2 p - 1)) w_y - r (1 - p) w = 0`
(`TauCeti.Finance.pde_comp_exp_div_one_add_exp`),

an equation on the whole line with bounded coefficients. Reversing time turns this terminal-value
problem into an initial-value problem, to which the comparison principle for bounded solutions on
the whole line applies
(`TauCeti.PDE.le_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_le_of_le_initial`).

## Main declarations

* `TauCeti.Finance.le_of_pde_le_of_terminal_le`: the comparison principle for the pricing equation
  in the linear-growth class.
* `TauCeti.Finance.eq_of_pde_eq_of_terminal_eq`: uniqueness of classical solutions of linear growth
  with given terminal value.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964, Chapter 2,
  Section 4.
* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*, Cambridge
  University Press, 1995, §5.4.
-/

public section

open Real Filter Topology Set

namespace TauCeti.Finance

variable {σ : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {C₁ C₂ : ℝ → ℝ → ℝ} {T Λ R A : ℝ}

/-- **The comparison principle for the pricing equation.** Let the volatility `σ(s, t)` and the
rate `r(t)` be bounded for `0 < t < T`, by `σ² ≤ Λ` and `|r| ≤ R`. Let `C₁` and `C₂` be continuous
on `s > 0`, `0 ≤ t ≤ T`, twice continuously differentiable in the spot and differentiable in time
for `s > 0`, `0 < t < T`, with `C₁ - C₂ ≤ A (1 + s)`. If the pricing operator
`C_t + σ² s² / 2 C_ss + r (s C_s - C)` of `C₂` is at most that of `C₁` for `0 < t < T`, and
`C₁(s, T) ≤ C₂(s, T)` for every spot `s > 0`, then `C₁ ≤ C₂` for `s > 0` and `0 ≤ t ≤ T`. -/
theorem le_of_pde_le_of_terminal_le
    (hσ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → σ s t ^ 2 ≤ Λ)
    (hr : ∀ ⦃t⦄, t ∈ Ioo 0 T → |r t| ≤ R)
    (hC₁ : ContinuousOn (Function.uncurry C₁) (Ioi 0 ×ˢ Icc 0 T))
    (hC₂ : ContinuousOn (Function.uncurry C₂) (Ioi 0 ×ˢ Icc 0 T))
    (hgrowth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc 0 T → C₁ s t - C₂ s t ≤ A * (1 + s))
    (hcd₁ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun x ↦ C₁ x t) s)
    (hcd₂ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun x ↦ C₂ x t) s)
    (hdiff₁ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ (fun u ↦ C₁ s u) t)
    (hdiff₂ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ (fun u ↦ C₂ s u) t)
    (hpde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T →
      deriv (fun u ↦ C₂ s u) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C₂ x t) s +
          r t * (s * deriv (fun x ↦ C₂ x t) s - C₂ s t) ≤
        deriv (fun u ↦ C₁ s u) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C₁ x t) s +
          r t * (s * deriv (fun x ↦ C₁ x t) s - C₁ s t))
    (hterminal : ∀ ⦃s⦄, 0 < s → C₁ s T ≤ C₂ s T) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc 0 T → C₁ s t ≤ C₂ s t := by
  have hψ (y : ℝ) : 0 < 1 + exp y := add_pos one_pos (exp_pos y)
  have hrev {τ : ℝ} (hτ : τ ∈ Ioo 0 T) : T - τ ∈ Ioo 0 T := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  -- In weighted log-spot coordinates and reversed time, `vᵢ(τ, y) = Cᵢ(e^y, T - τ) / (1 + e^y)`.
  have hcont {C : ℝ → ℝ → ℝ} (hC : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc 0 T)) :
      ContinuousOn (Function.uncurry fun τ y ↦ C (exp y) (T - τ) / (1 + exp y))
        (Icc 0 T ×ˢ univ) := by
    refine ContinuousOn.div ?_ (by fun_prop) fun p _ ↦ (hψ p.2).ne'
    refine hC.comp (f := fun p : ℝ × ℝ ↦ (exp p.2, T - p.1)) (by fun_prop) fun p hp ↦ ?_
    exact ⟨exp_pos p.2, by linarith [hp.1.2], by linarith [hp.1.1]⟩
  have hcd {C : ℝ → ℝ → ℝ}
      (hcd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
      {τ : ℝ} (hτ : τ ∈ Ioo 0 T) (y : ℝ) :
      ContDiffAt ℝ 2 (fun y ↦ C (exp y) (T - τ) / (1 + exp y)) y :=
    ((hcd (exp_pos y) (hrev hτ)).comp y contDiff_exp.contDiffAt).div
      (contDiffAt_const.add contDiff_exp.contDiffAt) (hψ y).ne'
  have hdiff {C : ℝ → ℝ → ℝ}
      (hdiff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ (fun u ↦ C s u) t)
      {τ : ℝ} (hτ : τ ∈ Ioo 0 T) (y : ℝ) :
      DifferentiableAt ℝ (fun τ' ↦ C (exp y) (T - τ') / (1 + exp y)) τ :=
    ((hdiff (exp_pos y) (hrev hτ)).comp τ
      ((differentiableAt_const T).sub differentiableAt_id)).div_const _
  have hCd {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
      ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z :=
    (hf.eventually (by simp)).mono fun z hz ↦ hz.differentiableAt (by norm_num)
  have hCd' {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (deriv f) x :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- Apply the comparison principle on the whole line to `v₁` and `v₂`. The coefficients
  -- `a = σ² / 2`, `b = r + a (e^y - 1) / (e^y + 1)` and `c = -r / (1 + e^y)` are bounded by
  -- `|Λ| / 2`, `|R| + |Λ| / 2` and `|R|`; `v₁ - v₂ ≤ A` by the growth bound; and the operators
  -- compare by `pde_comp_exp_div_one_add_exp`.
  have h := PDE.le_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_le_of_le_initial
    (a := fun τ y ↦ σ (exp y) (T - τ) ^ 2 / 2)
    (b := fun τ y ↦ r (T - τ) + σ (exp y) (T - τ) ^ 2 / 2 * ((exp y - 1) / (exp y + 1)))
    (c := fun τ y ↦ -r (T - τ) / (1 + exp y))
    (u := fun τ y ↦ C₁ (exp y) (T - τ) / (1 + exp y))
    (v := fun τ y ↦ C₂ (exp y) (T - τ) / (1 + exp y))
    (Lam := |Λ| / 2) (β := |R| + |Λ| / 2) (γ := |R|)
    (fun τ _ y ↦ by positivity)
    (fun τ hτ y ↦ by
      have h1 := (hσ (exp_pos y) (hrev hτ)).trans (le_abs_self Λ)
      nlinarith [abs_nonneg Λ, sq_nonneg y])
    (fun τ hτ y ↦ by
      have hq : |(exp y - 1) / (exp y + 1)| ≤ 1 := by
        rw [abs_div, abs_of_pos (by positivity : 0 < exp y + 1), div_le_one (by positivity),
          abs_le]
        constructor <;> linarith [exp_pos y]
      have h1 := (hσ (exp_pos y) (hrev hτ)).trans (le_abs_self Λ)
      have h2 := (hr (hrev hτ)).trans (le_abs_self R)
      have h3 : 0 ≤ σ (exp y) (T - τ) ^ 2 / 2 := by positivity
      calc |r (T - τ) + σ (exp y) (T - τ) ^ 2 / 2 * ((exp y - 1) / (exp y + 1))|
          ≤ |r (T - τ)| + σ (exp y) (T - τ) ^ 2 / 2 * 1 := by
            refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [abs_mul, abs_of_nonneg h3]
            exact mul_le_mul_of_nonneg_left hq h3
        _ ≤ (|R| + |Λ| / 2) * 1 := by linarith
        _ ≤ (|R| + |Λ| / 2) * (1 + |y|) := by
            nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ |R| + |Λ| / 2) (abs_nonneg y)])
    (fun τ hτ y ↦ by
      have h1 := (neg_le_abs (r (T - τ))).trans ((hr (hrev hτ)).trans (le_abs_self R))
      rw [div_le_iff₀ (hψ y)]
      nlinarith [mul_nonneg (abs_nonneg R) (exp_pos y).le])
    (hcont hC₁) (hcont hC₂)
    ⟨A, by
      rintro _ ⟨⟨τ, y⟩, ⟨hτ, -⟩, rfl⟩
      simp only [Function.uncurry_apply_pair, Pi.sub_apply, ← sub_div]
      rw [div_le_iff₀ (hψ y)]
      have := hgrowth (exp_pos y) (t := T - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
      linarith⟩
    (fun τ hτ y ↦ hcd hcd₁ hτ y) (fun τ hτ y ↦ hcd hcd₂ hτ y)
    (fun τ hτ y ↦ hdiff hdiff₁ hτ y) (fun τ hτ y ↦ hdiff hdiff₂ hτ y)
    (fun τ hτ y ↦ by
      rw [deriv_comp_const_sub (f := fun t ↦ C₁ (exp y) t / (1 + exp y)),
        deriv_comp_const_sub (f := fun t ↦ C₂ (exp y) t / (1 + exp y))]
      have hc₁ := hcd₁ (exp_pos y) (hrev hτ)
      have h₁ := pde_comp_exp_div_one_add_exp (σ (exp y) (T - τ)) (r (T - τ))
        (hCd hc₁) (hCd' hc₁)
      have hc₂ := hcd₂ (exp_pos y) (hrev hτ)
      have h₂ := pde_comp_exp_div_one_add_exp (σ (exp y) (T - τ)) (r (T - τ))
        (hCd hc₂) (hCd' hc₂)
      have h := div_le_div_of_nonneg_right (hpde (exp_pos y) (hrev hτ)) (hψ y).le
      linear_combination h + h₂ - h₁)
    (fun y ↦ by
      simp only [sub_zero]
      exact div_le_div_of_nonneg_right (hterminal (exp_pos y)) (hψ y).le)
  -- Undo the change of variables at `τ = T - t`, `y = log s`.
  intro s hs t ht
  have hle := h (t := T - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (log s)
  simp only [exp_log hs, sub_sub_cancel] at hle
  exact (div_le_div_iff_of_pos_right (by linarith)).mp hle

/-- **Uniqueness for the pricing equation in the linear-growth class.** Let the volatility
`σ(s, t)` and the rate `r(t)` be bounded for `0 < t < T`, by `σ² ≤ Λ` and `|r| ≤ R`. Two functions
`C₁` and `C₂` that are continuous on `s > 0`, `0 ≤ t ≤ T`, twice continuously differentiable in the
spot and differentiable in time for `s > 0`, `0 < t < T`, with `|C₁ - C₂| ≤ A (1 + s)`, the same
pricing operator `C_t + σ² s² / 2 C_ss + r (s C_s - C)` for `0 < t < T` and the same terminal
value at `t = T`, agree for `s > 0` and `0 ≤ t ≤ T`. In particular a classical solution of the
pricing equation `C_t + σ² s² / 2 C_ss + r (s C_s - C) = 0` with `|C(s, t)| ≤ A (1 + s)` is
determined by its terminal value. -/
theorem eq_of_pde_eq_of_terminal_eq
    (hσ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → σ s t ^ 2 ≤ Λ)
    (hr : ∀ ⦃t⦄, t ∈ Ioo 0 T → |r t| ≤ R)
    (hC₁ : ContinuousOn (Function.uncurry C₁) (Ioi 0 ×ˢ Icc 0 T))
    (hC₂ : ContinuousOn (Function.uncurry C₂) (Ioi 0 ×ˢ Icc 0 T))
    (hgrowth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc 0 T → |C₁ s t - C₂ s t| ≤ A * (1 + s))
    (hcd₁ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun x ↦ C₁ x t) s)
    (hcd₂ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → ContDiffAt ℝ 2 (fun x ↦ C₂ x t) s)
    (hdiff₁ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ (fun u ↦ C₁ s u) t)
    (hdiff₂ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ (fun u ↦ C₂ s u) t)
    (hpde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo 0 T →
      deriv (fun u ↦ C₁ s u) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C₁ x t) s +
          r t * (s * deriv (fun x ↦ C₁ x t) s - C₁ s t) =
        deriv (fun u ↦ C₂ s u) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C₂ x t) s +
          r t * (s * deriv (fun x ↦ C₂ x t) s - C₂ s t))
    (hterminal : ∀ ⦃s⦄, 0 < s → C₁ s T = C₂ s T) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc 0 T → C₁ s t = C₂ s t := by
  intro s hs t ht
  exact le_antisymm
    (le_of_pde_le_of_terminal_le hσ hr hC₁ hC₂
      (fun s hs t ht ↦ (le_abs_self _).trans (hgrowth hs ht)) hcd₁ hcd₂ hdiff₁ hdiff₂
      (fun s hs t ht ↦ (hpde hs ht).ge) (fun s hs ↦ (hterminal hs).le) hs ht)
    (le_of_pde_le_of_terminal_le hσ hr hC₂ hC₁
      (fun s hs t ht ↦ (le_abs_self _).trans (abs_sub_comm (C₁ s t) _ ▸ hgrowth hs ht))
      hcd₂ hcd₁ hdiff₂ hdiff₁
      (fun s hs t ht ↦ (hpde hs ht).le) (fun s hs ↦ (hterminal hs).ge) hs ht)

end TauCeti.Finance
