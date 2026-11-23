/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Solvability
public import TauCeti.Probability.Finance.Pricing.Coefficients
import TauCeti.Probability.Finance.Pricing.Comparison

/-!
# Existence of prices of linear growth with Hölder local volatility

Write `a = σ² / 2` for the local variance rate in log-spot coordinates `y = log s`, and let `r` be
the short rate. For general bounded parabolic Hölder fields `a` and `r` on `ℝ × [t₀, t₁]` with
`t₀ < t₁` of exponent `0 < α < 1` with `a` bounded below by a positive constant, and for a terminal
payoff `h` whose weighted log-spot profile `y ↦ h(e^y) / (1 + e^y)` lies in `C_b^{2,α}(ℝ)`,
well-posedness of the weighted terminal-data map `v ↦ (P v, v(·, t₁))`
(`TauCeti.Finance.isInvertible_weightedLogSpotPricingOperatorL_prod_spatialTraceL`,
`TauCeti.Finance.weightedLogSpotTerminalDataCLE`) constructs the unique `v ∈ C_b^{2+α,1+α/2}`
whose reconstructed spot price `C(s, t) = (1 + s) v(log s, t)`
(`TauCeti.Finance.weightedLogSpotPrice`) solves the closed-slab pricing equation

`derivWithin (C s ·) [t₀, t₁] t + a(log s, t) s² C_ss + r(log s, t) (s C_s - C) = 0`

for `s > 0`, `t ∈ [t₀, t₁]` (where `derivWithin` denotes the within-slab time derivative, one-sided
at the endpoints `t₀` and `t₁`) with terminal value `C(s, t₁) = h(s)`
(`TauCeti.Finance.existsUnique_pde_weightedLogSpotPrice_eq_zero`).

Specialized to market volatility `σ(s, t)` and a time-only `(α / 2)`-Hölder short rate `r(t)`:

* `TauCeti.Finance.logSpotHalfVarianceHolder` and `TauCeti.Finance.shortRateHolder` (in
  `TauCeti.Probability.Finance.Pricing.Coefficients`) build the parabolic Hölder coefficient fields
  on `slab t₀ t₁`, with quantitative norm bounds exported by
  `TauCeti.Finance.norm_logSpotHalfVarianceHolder_le` and
  `TauCeti.Finance.norm_shortRateHolder_le`.
* `TauCeti.Finance.eq_weightedLogSpotPrice_of_pde_eq_zero_of_terminal_eq` (in
  `TauCeti.Probability.Finance.Pricing.Comparison`) proves that every continuous linear-growth
  competitor that is twice continuously differentiable in spot and differentiable in time at
  interior times `t ∈ (t₀, t₁)` with matching interior coefficients and payoff and that solves the
  interior pricing PDE agrees with `weightedLogSpotPrice u` on the closed slab `(0, ∞) × [t₀, t₁]`.
* `TauCeti.Finance.exists_weightedLogSpotPrice_pde_and_unique` assumes `t₀ < t₁`, a uniform
  volatility bound `|σ(e^y, t)| ≤ M`, uniform positive ellipticity `δ ≤ σ(s, t)²`, parabolic
  `α`-Hölder regularity of `(y, t) ↦ σ(e^y, t)`, `(α / 2)`-Hölder regularity of `r` on `[t₀, t₁]`,
  and weighted payoff regularity `g ∈ C_b^{2,α}(ℝ)`. It proves existence of a weighted log-spot
  profile witnessing classical interior PDE solvability, uniqueness in the linear-growth class
  (for competitors twice continuously differentiable in spot and differentiable in time at interior
  times), joint continuity of `C`, `∂ₛC`, `∂ₛ²C`, and within-slab `∂ₜC` on `(0, ∞) × [t₀, t₁]`,
  and linear-growth bounds on both price and dollar delta `s ∂ₛC`. The parabolic Hölder input for
  `σ` is supplied with quantitative constant `L + 2 * M + H` (and membership) by
  `ParabolicSpaceTime.holderWith_slab_of_norm_le_of_lipschitzWith_of_holderOnWith` and
  `ParabolicSpaceTime.memHolder_slab_of_norm_le_of_lipschitzWith_of_holderOnWith` from a uniform
  bound, a common spatial Lipschitz constant across time slices, and a common temporal `(α / 2)`-
  Hölder constant across space.

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

/-- **Existence and uniqueness of the classical price in the weighted Hölder class.** Let
`0 < α < 1`, `t₀ < t₁`, let the local variance rate `a = σ² / 2 ≥ lam > 0` and the rate `r` be
fields in `C_b^{α,α/2}(ℝ × [t₀, t₁])` in log-spot coordinates, and let the payoff `h` satisfy
`h (exp y) / (1 + exp y) = g y` for some `g ∈ C_b^{2,α}`. Then exactly one
`v ∈ C_b^{2+α,1+α/2}` has a price `C(s, t) = (1 + s) v(log s, t)` that solves
`derivWithin (C s ·) [t₀, t₁] t + a(log s, t) s² C_ss + r(log s, t) (s C_s - C) = 0` for all
`s > 0` and `t ∈ [t₀, t₁]` (with within-slab, one-sided-at-endpoints time derivative) and satisfies
`C(s, t₁) = h(s)` for all `s > 0`. -/
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
    rw [pde_weightedLogSpotPrice_eq_mul hα₁.le a r v (exp_pos y) t, log_exp] at hp
    exact (mul_eq_zero.1 hp).resolve_left (by positivity)
  · rw [pde_weightedLogSpotPrice_eq_mul hα₁.le a r v hs t, hv, HolderSpace.zero_apply,
      mul_zero]
  · ext y
    have hy := (weightedLogSpotPrice_of_mem v (exp y) ⟨t₁, right_mem_Icc.2 ht.le⟩).symm.trans
      (hv (exp y) (exp_pos y))
    rw [log_exp] at hy
    rw [spatialTrace_apply, hg, ← hy, mul_div_cancel_left₀ _ (by positivity)]
  · exact weightedLogSpotPrice_terminal v (fun y ↦ by rw [← spatialTrace_apply, hv, hg]) hs

/-- **Existence, linear-growth bounds, and uniqueness for the self-financing pricing PDE.**
Let `0 < α < 1`, `t₀ < t₁`, `0 < δ`, let `σ(s, t)` satisfy `δ ≤ σ(s, t)²` and `|σ(e^y, t)| ≤ M`
with `(y, t) ↦ σ(e^y, t)` parabolically `α`-Hölder on `slab t₀ t₁`, let `r` be `(α / 2)`-Hölder on
`[t₀, t₁]`, and let `h` be a terminal payoff whose weighted log-spot profile
`y ↦ h(e^y) / (1 + e^y)` is represented by `g ∈ C_b^{2,α}(ℝ)`. Then there exists a witness
`u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solving the weighted log-spot terminal-value problem (uniquely
by `weightedLogSpotTerminalDataCLE`), and its reconstructed spot price `C = weightedLogSpotPrice u`
is the unique classical solution of the pricing PDE in the linear-growth class (among competitors
twice continuously differentiable in spot and differentiable in time at interior times), with joint
continuity of `C`, `∂ₛC`, `∂ₛ²C`, and within-slab `∂ₜC` on `(0, ∞) × [t₀, t₁]` and linear-growth
bounds on both the price and the dollar-delta exposure. -/
theorem exists_weightedLogSpotPrice_pde_and_unique
    (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    {σ : ℝ → ℝ → ℝ} {r h : ℝ → ℝ} {δ : ℝ} {M H_r : ℝ≥0}
    (hδ : 0 < δ)
    (hσ_low : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → δ ≤ σ s t ^ 2)
    (hσ_bdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ_hol : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (hr_hol : HolderOnWith H_r (α / 2) r (Icc t₀ t₁))
    (g : CkHolderSpace 2 α ℝ ℝ) (hg : ∀ y, g y = h (exp y) / (1 + exp y)) :
    ∃ u : ParabolicC2HolderSpace α ℝ ℝ ht,
      weightedLogSpotPricingOperatorL hα₁.le
          (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol)
          (shortRateHolder hα₀ r hr_hol) u = 0 ∧
      u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩ = g ∧
      (∀ s > 0, weightedLogSpotPrice u s t₁ = h s) ∧
      ContinuousOn (Function.uncurry (weightedLogSpotPrice u)) (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun s ↦ weightedLogSpotPrice u s p.2) p.1)
        (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (deriv fun s ↦ weightedLogSpotPrice u s p.2) p.1)
        (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ derivWithin (weightedLogSpotPrice u p.1) (Icc t₀ t₁) p.2)
        (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      (∀ s > 0, ∀ t ∈ Icc t₀ t₁,
        ContDiffAt ℝ 2 (fun x ↦ weightedLogSpotPrice u x t) s ∧
          |weightedLogSpotPrice u s t| + |s * deriv (fun x ↦ weightedLogSpotPrice u x t) s| ≤
            2 * ‖u‖ * (1 + s)) ∧
      (∀ s > 0, ∀ t ∈ Ioo t₀ t₁,
        DifferentiableAt ℝ (weightedLogSpotPrice u s) t ∧
          deriv (weightedLogSpotPrice u s) t +
              σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
              r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
                weightedLogSpotPrice u s t) = 0) ∧
      ∀ (C : ℝ → ℝ → ℝ) (A : ℝ),
        ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s)) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
          deriv (fun τ ↦ C s τ) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
            r t * (s * deriv (fun x ↦ C x t) s - C s t) = 0) →
        (∀ ⦃s⦄, 0 < s → C s t₁ = h s) →
        ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → C s t = weightedLogSpotPrice u s t := by
  let a := logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol
  let rH := shortRateHolder hα₀ r hr_hol
  have ha : ∀ p, δ / 2 ≤ a p := fun p ↦ by
    rw [logSpotHalfVarianceHolder_apply]
    exact div_le_div_of_nonneg_right (hσ_low (exp_pos _) (slabTime p).property) zero_le_two
  let u := (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a rH ⟨δ / 2, half_pos hδ, ha⟩).symm (0, g)
  have hPu : weightedLogSpotPricingOperatorL hα₁.le a rH u = 0 :=
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply (0, g)
  have htr : u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩ = g :=
    spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply (0, g)
  have huterm : ∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = h (exp y) / (1 + exp y) :=
    fun y ↦ by rw [← spatialTrace_apply, htr, hg]
  refine ⟨u, hPu, htr, fun s hs ↦ weightedLogSpotPrice_terminal u huterm hs,
    (continuousOn_weightedLogSpotPrice u).mono (prod_mono_right (subset_univ _)),
    continuousOn_deriv_weightedLogSpotPrice_spot u,
    continuousOn_deriv_deriv_weightedLogSpotPrice_spot u,
    continuousOn_derivWithin_weightedLogSpotPrice_time u,
    fun s hs t ht' ↦ ⟨(contDiffOn_weightedLogSpotPrice u ⟨t, ht'⟩).contDiffAt (Ioi_mem_nhds hs),
      abs_weightedLogSpotPrice_add_abs_mul_deriv_le u hs ht'⟩,
    fun s hs t ht' ↦ ⟨differentiableAt_weightedLogSpotPrice_time u s ht',
      pde_weightedLogSpotPrice_eq_zero_of_mem_Ioo hα₁.le u hPu hs ht' (by simp [a, exp_log hs])
        (by simp [rH])⟩,
    fun C A hCc hCg hCcd hCd hCpde hCt ↦ ?_⟩
  exact eq_weightedLogSpotPrice_of_pde_eq_zero_of_terminal_eq hα₁.le
    (fun s hs t ht' ↦ by simp [a, exp_log hs]) (fun s _ t ht' ↦ by simp [rH])
    u hPu huterm hCc hCg hCcd hCd hCpde hCt

end TauCeti.Finance
