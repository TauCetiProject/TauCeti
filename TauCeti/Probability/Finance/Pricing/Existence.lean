/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Operator
public import TauCeti.Probability.Finance.WeightedLogSpot
import TauCeti.Analysis.PDE.Parabolic.Holder.Line

/-!
# Existence of prices of linear growth with Hölder local volatility

Write `a = σ² / 2` for the local variance rate in log-spot coordinates `y = log s`, and let `r` be
the short rate. If `a` and `r` are bounded parabolic Hölder fields on `ℝ × [t₀, t₁]`, of exponent
`0 < α < 1`, and `a` is bounded below by a positive constant, then the terminal-value problem for
the weighted log-spot pricing operator `P` is well posed in `C_b^{2+α,1+α/2}`: the terminal-data map
`v ↦ (P v, v(·, t₁))` is an isomorphism of Banach spaces onto `C_b^{α,α/2} × C_b^{2,α}`
(`TauCeti.Finance.isInvertible_weightedLogSpotPricingOperatorL_prod_spatialTraceL`). Uniqueness
holds even without ellipticity
(`TauCeti.Finance.injective_weightedLogSpotPricingOperatorL_prod_spatialTraceL`); the point here is
existence, together with the boundedness of the solution operator.

In spot coordinates, this constructs the classical price of a payoff `h` with
`y ↦ h (exp y) / (1 + exp y)` in `C_b^{2,α}`. There is exactly one `v ∈ C_b^{2+α,1+α/2}` whose
price `C(s, t) = (1 + s) v(log s, t)` (`TauCeti.Finance.weightedLogSpotPrice`) solves the pricing
equation

`C_t + a(log s, t) s² C_ss + r(log s, t) (s C_s - C) = 0`

for every spot `s > 0` and every `t ∈ [t₀, t₁]`, with one-sided time derivatives at the endpoints,
and has terminal value `C(s, t₁) = h(s)`
(`TauCeti.Finance.existsUnique_pde_weightedLogSpotPrice_eq_zero`). For a local volatility
`σ(s, t)` the second-order term is `σ² s² / 2 C_ss`. The rate may depend on the spot as well; the
financial short rate is the special case of a field constant in space. The price has linear
growth together with its dollar delta, `|C| + |s C_s| ≤ A (1 + s)`
(`TauCeti.Finance.abs_weightedLogSpotPrice_le`,
`TauCeti.Finance.abs_mul_deriv_weightedLogSpotPrice_le`), the growth class of the comparison
principle in spot coordinates.

The proof transports the variable-coefficient Cauchy problem
(`TauCeti.ParabolicC2HolderSpace.isInvertible_backwardParabolicOperatorL_prod_spatialTraceL_real`)
to the conjugated coefficients of the weighted operator. Only the lower bound on `a` is a
hypothesis: the conjugated first- and zeroth-order coefficients are bounded Hölder fields by
construction, whatever the sign of `r`.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964,
  Chapter 2, Section 4.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*,
  Cambridge University Press, 1995, §5.4.
-/

public section
noncomputable section

namespace TauCeti.Finance

open Set Real ParabolicSpaceTime ParabolicC2HolderSpace
open scoped NNReal

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- **The weighted terminal-value problem is well posed.** For `0 < α < 1`, a local variance rate
`a ≥ lam > 0` and a rate `r` in `C_b^{α,α/2}(ℝ × [t₀, t₁])`, the terminal-data map
`v ↦ (P v, v(·, t₁))` of the weighted log-spot pricing operator `P` is an isomorphism of Banach
spaces from `C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}`. -/
theorem isInvertible_weightedLogSpotPricingOperatorL_prod_spatialTraceL (hα₀ : 0 < α)
    (hα₁ : α < 1) {a : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p, lam ≤ a p) :
    ((weightedLogSpotPricingOperatorL (ht := ht) hα₁.le a r).prod
      (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩)).IsInvertible := by
  rw [weightedLogSpotPricingOperatorL_def]
  exact isInvertible_backwardParabolicOperatorL_prod_spatialTraceL_real hα₀ hα₁ ht _ _ hlam
    fun p ↦ by simpa using ha p

section Residual

variable {hα : α ≤ 1} {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}

/-- The spot pricing residual of the price represented by `v` is `1 + s` times the weighted
log-spot operator applied to `v`. -/
private theorem pde_weightedLogSpotPrice_eq_mul (v : ParabolicC2HolderSpace α ℝ ℝ ht) {s : ℝ}
    (hs : 0 < s) (t : Icc t₀ t₁) :
    derivWithin (weightedLogSpotPrice v s) (Icc t₀ t₁) t +
        a (slabMk (log s) t) * s ^ 2 * deriv (deriv fun x ↦ weightedLogSpotPrice v x t) s +
        r (slabMk (log s) t) * (s * deriv (fun x ↦ weightedLogSpotPrice v x t) s -
          weightedLogSpotPrice v s t) =
      (1 + s) * weightedLogSpotPricingOperatorL hα a r v (slabMk (log s) t) := by
  have hsig : sigmoid (log s) = s / (1 + s) := by
    rw [sigmoid_def, exp_neg, exp_log hs]
    field_simp
    ring
  have h₁ : 2 * sigmoid (log s) - 1 = (s - 1) / (s + 1) := by
    rw [hsig]
    field_simp
    ring
  have h₂ : 1 - sigmoid (log s) = 1 / (1 + s) := by
    rw [hsig]
    field_simp
    ring
  rw [weightedLogSpotPricingOperatorL_apply, space_slabMk, h₁, h₂]
  -- The change of variables holds for every volatility; both sides are affine in `σ² / 2`, so
  -- its instances with `σ = 0` and `σ = 1` combine to the local variance rate `a`.
  have e₀ := pde_weightedLogSpotPrice v hs t 0 (r (slabMk (log s) t))
  have e₁ := pde_weightedLogSpotPrice v hs t 1 (r (slabMk (log s) t))
  linear_combination (1 - 2 * a (slabMk (log s) t)) * e₀ + 2 * a (slabMk (log s) t) * e₁

end Residual

/-- **Existence and uniqueness of the classical price in the weighted Hölder class.** Let
`0 < α < 1`, let the local variance rate `a = σ² / 2 ≥ lam > 0` and the rate `r` be fields in
`C_b^{α,α/2}(ℝ × [t₀, t₁])` in log-spot coordinates, and let the payoff `h` satisfy
`h (exp y) / (1 + exp y) = g y` for some `g ∈ C_b^{2,α}`. Then exactly one
`v ∈ C_b^{2+α,1+α/2}` has a price `C(s, t) = (1 + s) v(log s, t)` that solves
`C_t + a(log s, t) s² C_ss + r(log s, t) (s C_s - C) = 0` for all `s > 0` and `t ∈ [t₀, t₁]` and
satisfies `C(s, t₁) = h(s)` for all `s > 0`. -/
theorem existsUnique_pde_weightedLogSpotPrice_eq_zero (hα₀ : 0 < α) (hα₁ : α < 1)
    {a : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
    {lam : ℝ} (hlam : 0 < lam) (ha : ∀ p, lam ≤ a p) {h : ℝ → ℝ} (g : CkHolderSpace 2 α ℝ ℝ)
    (hg : ∀ y, g y = h (exp y) / (1 + exp y)) :
    ∃! v : ParabolicC2HolderSpace α ℝ ℝ ht,
      (∀ s, 0 < s → ∀ t : Icc t₀ t₁,
        derivWithin (weightedLogSpotPrice v s) (Icc t₀ t₁) t +
            a (slabMk (log s) t) * s ^ 2 * deriv (deriv fun x ↦ weightedLogSpotPrice v x t) s +
          r (slabMk (log s) t) * (s * deriv (fun x ↦ weightedLogSpotPrice v x t) s -
            weightedLogSpotPrice v s t) = 0) ∧
      ∀ s, 0 < s → weightedLogSpotPrice v s t₁ = h s := by
  -- The two conditions say exactly that the terminal-data map sends `v` to `(0, g)`.
  refine (existsUnique_congr fun v ↦ ?_).2
    ((isInvertible_weightedLogSpotPricingOperatorL_prod_spatialTraceL (ht := ht) hα₀ hα₁ r hlam
      ha).bijective.existsUnique (0, g))
  rw [ContinuousLinearMap.prod_apply, Prod.mk.injEq, spatialTraceL_apply]
  refine and_congr ⟨fun hv ↦ ?_, fun hv s hs t ↦ ?_⟩ ⟨fun hv ↦ ?_, fun hv s hs ↦ ?_⟩
  · -- Every slab point is `(log s, t)` for the spot `s = exp y`, and `1 + s ≠ 0`.
    refine HolderSpace.ext fun p ↦ ?_
    obtain ⟨y, t, rfl⟩ : ∃ y t, slabMk y t = p := ⟨_, _, slabMk_space_slabTime p⟩
    have hp := hv (exp y) (exp_pos y) t
    rw [pde_weightedLogSpotPrice_eq_mul (hα := hα₁.le) v (exp_pos y) t, log_exp] at hp
    exact (mul_eq_zero.1 hp).resolve_left (by positivity)
  · rw [pde_weightedLogSpotPrice_eq_mul (hα := hα₁.le) v hs t, hv, HolderSpace.zero_apply,
      mul_zero]
  · ext y
    have hy := (weightedLogSpotPrice_of_mem v (exp y) ⟨t₁, right_mem_Icc.2 ht.le⟩).symm.trans
      (hv (exp y) (exp_pos y))
    rw [log_exp] at hy
    rw [spatialTrace_apply, hg, ← hy, mul_div_cancel_left₀ _ (by positivity)]
  · exact weightedLogSpotPrice_terminal v (fun y ↦ by rw [← spatialTrace_apply, hv, hg]) hs

end TauCeti.Finance
