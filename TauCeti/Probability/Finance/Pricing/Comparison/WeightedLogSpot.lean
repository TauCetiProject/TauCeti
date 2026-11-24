/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Operator
import TauCeti.Probability.Finance.Pricing.Comparison.Basic

/-!
# Comparison of classical prices against weighted log-spot solutions

Given a weighted log-spot solution `u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` of
`weightedLogSpotPricingOperatorL hα a rH u = 0` whose coefficients `a` and `rH` match `a₀ ≥ 0`
and `r₀` at interior times `t ∈ (t₀, t₁)`,
`TauCeti.Finance.eq_weightedLogSpotPrice_of_pde_eq_zero_of_terminal_eq` proves that every
linear-growth competitor `C` (`|C(s, t)| ≤ A (1 + s)`) that is jointly continuous on the closed
positive-spot slab `(0, ∞) × [t₀, t₁]` (including both time endpoints `t₀` and `t₁`), twice
continuously differentiable in spot and differentiable in time at interior times `t ∈ (t₀, t₁)`,
solves the interior pricing PDE at `t ∈ (t₀, t₁)`, and attains the same terminal payoff `h` at
`t₁` agrees with `weightedLogSpotPrice u` on `(0, ∞) × [t₀, t₁]`.

This comparison step requires neither uniform ellipticity of `a` nor parabolic Schauder existence
theory.
-/

public section
noncomputable section

namespace TauCeti.Finance

open Set Real ParabolicSpaceTime ParabolicC2HolderSpace
open scoped NNReal

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- **Uniqueness of classical linear-growth prices on `[t₀, t₁]`.** If
`u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solves `weightedLogSpotPricingOperatorL u = 0` with terminal
profile `y ↦ h(e^y) / (1 + e^y)`, and `a` and `rH` match `a₀` (`0 ≤ a₀`) and `r₀` on the
interior times `t ∈ (t₀, t₁)`, then every linear-growth competitor `C` (with
`|C(s, t)| ≤ A (1 + s)`) that is jointly continuous on `(0, ∞) × [t₀, t₁]` (in contrast to its
interior-only `t ∈ (t₀, t₁)` differentiability and PDE hypotheses), twice continuously
differentiable in spot and differentiable in time at interior times `t ∈ (t₀, t₁)`, solves the
interior pricing PDE, and attains the same terminal payoff `h` at `t₁` agrees with the
reconstructed price `weightedLogSpotPrice u` on the closed slab `(0, ∞) × [t₀, t₁]`. -/
theorem eq_weightedLogSpotPrice_of_pde_eq_zero_of_terminal_eq (hα : α ≤ 1)
    {a₀ r₀ : ℝ → ℝ → ℝ} {h : ℝ → ℝ} {A : ℝ}
    {a rH : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    (ha₀ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → 0 ≤ a₀ s t)
    (ha_eq : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄ (ht' : t ∈ Ioo t₀ t₁),
      a (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = a₀ s t)
    (hr_eq : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄ (ht' : t ∈ Ioo t₀ t₁),
      rH (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = r₀ s t)
    (u : ParabolicC2HolderSpace α ℝ ℝ ht)
    (hPu : weightedLogSpotPricingOperatorL hα a rH u = 0)
    (huterm : ∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = h (exp y) / (1 + exp y))
    {C : ℝ → ℝ → ℝ}
    (hC_cont : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁))
    (hC_growth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s))
    (hC_cd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
    (hC_diff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t)
    (hC_pde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
      deriv (fun τ ↦ C s τ) t + a₀ s t * s ^ 2 * deriv (deriv fun x ↦ C x t) s +
        r₀ s t * (s * deriv (fun x ↦ C x t) s - C s t) = 0)
    (hC_term : ∀ ⦃s⦄, 0 < s → C s t₁ = h s) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → C s t = weightedLogSpotPrice u s t := by
  let W := weightedLogSpotPrice u
  refine eq_of_pde_eq_of_terminal_eq (a := a₀) (r := r₀) (C₁ := C) (C₂ := W)
    (Λ := ‖a‖) (R := ‖rH‖) (A := max A 0 + ‖u‖)
    ha₀
    (fun s hs t ht' ↦ by
      have ha1 : a₀ s t = a (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) := (ha_eq hs ht').symm
      simpa only [ha1, Real.norm_eq_abs] using (le_abs_self _).trans (a.norm_apply_le _))
    (fun s hs t ht' ↦ by
      have hr1 : r₀ s t = rH (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) := (hr_eq hs ht').symm
      simpa only [hr1, Real.norm_eq_abs] using rH.norm_apply_le _)
    hC_cont ((continuousOn_weightedLogSpotPrice u).mono (prod_mono_right (subset_univ _)))
    (fun s hs t ht' ↦ by
      have h1 := hC_growth hs ht'
      have h2 := abs_weightedLogSpotPrice_le u hs.le t
      calc |C s t - W s t| ≤ |C s t| + |W s t| := abs_sub _ _
        _ ≤ A * (1 + s) + ‖u‖ * (1 + s) := add_le_add h1 h2
        _ ≤ (max A 0 + ‖u‖) * (1 + s) := by nlinarith [le_max_left A 0, hs.le])
    hC_cd
    (fun s hs t ht' ↦ (contDiffOn_weightedLogSpotPrice u
      ⟨t, Ioo_subset_Icc_self ht'⟩).contDiffAt (Ioi_mem_nhds hs))
    hC_diff
    (fun s _ t ht' ↦ differentiableAt_weightedLogSpotPrice_time u s ht')
    (fun s hs t ht' ↦ by
      have hW := pde_weightedLogSpotPrice_eq_mul_of_mem_Ioo hα a rH u hs ht'
      rw [ha_eq hs ht', hr_eq hs ht', hPu, HolderSpace.zero_apply, mul_zero] at hW
      rw [hC_pde hs ht', hW])
    (fun s hs ↦ by
      dsimp only [W]
      rw [hC_term hs, weightedLogSpotPrice_slice u ⟨t₁, right_mem_Icc.2 ht.le⟩ huterm hs])

end TauCeti.Finance
