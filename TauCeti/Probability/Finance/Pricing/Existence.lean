/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Solvability
import TauCeti.Probability.Finance.Comparison

/-!
# Existence of prices of linear growth with Hölder local volatility

Write `a = σ² / 2` for the local variance rate in log-spot coordinates `y = log s`, and let `r` be
the short rate. For general bounded parabolic Hölder fields `a` and `r` on `ℝ × [t₀, t₁]` of
exponent `0 < α < 1` with `a` bounded below by a positive constant, and for a terminal payoff `h`
whose weighted log-spot profile `y ↦ h(e^y) / (1 + e^y)` lies in `C_b^{2,α}(ℝ)`, well-posedness of
the weighted terminal-data map `v ↦ (P v, v(·, t₁))`
(`TauCeti.Finance.isInvertible_weightedLogSpotPricingOperatorL_prod_spatialTraceL`,
`TauCeti.Finance.weightedLogSpotTerminalDataCLE`) constructs the unique `v ∈ C_b^{2+α,1+α/2}`
whose reconstructed spot price `C(s, t) = (1 + s) v(log s, t)`
(`TauCeti.Finance.weightedLogSpotPrice`) solves the closed-slab pricing equation

`derivWithin (C s ·) [t₀, t₁] t + a(log s, t) s² C_ss + r(log s, t) (s C_s - C) = 0`

for `s > 0`, `t ∈ [t₀, t₁]` (where `derivWithin` denotes the within-slab time derivative, one-sided
at the endpoints `t₀` and `t₁`) with terminal value `C(s, t₁) = h(s)`
(`TauCeti.Finance.existsUnique_pde_weightedLogSpotPrice_eq_zero`).

Specialized to market volatility `σ(s, t)` and a time-only `(α / 2)`-Hölder short rate `r(t)`:

* `TauCeti.Finance.logSpotHalfVarianceHolder` and `TauCeti.Finance.shortRateHolder` build the
  parabolic Hölder coefficient fields on `slab t₀ t₁`, with quantitative norm bounds exported by
  `TauCeti.Finance.norm_logSpotHalfVarianceHolder_le` and
  `TauCeti.Finance.norm_shortRateHolder_le`.
* `TauCeti.Finance.eq_weightedLogSpotPrice_of_pde_eq_zero_of_terminal_eq` proves that every
  continuous linear-growth competitor with matching interior coefficients and payoff that solves the
  interior pricing PDE agrees with `weightedLogSpotPrice u` on the closed slab `(0, ∞) × [t₀, t₁]`.
* `TauCeti.Finance.exists_weightedLogSpotPrice_pde_and_unique` assumes a uniform volatility bound
  `|σ(e^y, t)| ≤ M`, uniform positive ellipticity `δ ≤ σ(s, t)²`, parabolic `α`-Hölder regularity
  of `(y, t) ↦ σ(e^y, t)`, `(α / 2)`-Hölder regularity of `r` on `[t₀, t₁]`, and weighted payoff
  regularity `g ∈ C_b^{2,α}(ℝ)`. It proves existence of a weighted log-spot profile witnessing
  classical interior PDE solvability, uniqueness in the linear-growth class, joint continuity of
  `C`, `∂ₛC`, `∂ₛ²C`, and within-slab `∂ₜC` on `(0, ∞) × [t₀, t₁]`, and linear-growth bounds on
  both price and dollar delta `s ∂ₛC`. The parabolic Hölder input for `σ` is supplied with
  quantitative constant `L + 2 * M + H` (and membership) by
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
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- **Existence and uniqueness of the classical price in the weighted Hölder class.** Let
`0 < α < 1`, let the local variance rate `a = σ² / 2 ≥ lam > 0` and the rate `r` be fields in
`C_b^{α,α/2}(ℝ × [t₀, t₁])` in log-spot coordinates, and let the payoff `h` satisfy
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

/-! ### Market coefficient fields -/

section MarketCoefficients

/-- The log-spot half-variance field `a(y, t) = σ(e^y, t)² / 2` as an element of
`HolderSpace α (slab t₀ t₁) ℝ`, built from a bounded parabolically `α`-Hölder volatility
(`0 < α`). -/
def logSpotHalfVarianceHolder (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  let f : slab (E := ℝ) t₀ t₁ → ℝ := fun p ↦
    σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)
  let σB : slab (E := ℝ) t₀ t₁ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f
    (hσ.holderWith.continuous hα₀) M fun p ↦ by
      simpa only [f, Real.norm_eq_abs] using hbdd _ _ (slabTime p).property
  have hcoe : (σB : slab (E := ℝ) t₀ t₁ → ℝ) = f :=
    BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _
  (2⁻¹ : ℝ) • (HolderSpace.ofBoundedContinuousFunction σB (hcoe.symm ▸ hσ)) ^ 2

/-- Evaluation of `logSpotHalfVarianceHolder` at a slab point gives `σ(e^y, t)² / 2`. -/
@[simp]
theorem logSpotHalfVarianceHolder_apply (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (p : slab (E := ℝ) t₀ t₁) :
    logSpotHalfVarianceHolder hα₀ σ hbdd hσ p =
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p) ^ 2 / 2 := by
  rw [logSpotHalfVarianceHolder, HolderSpace.smul_apply, HolderSpace.pow_apply,
    HolderSpace.ofBoundedContinuousFunction_apply]
  have hcoe : ∀ q : slab (E := ℝ) t₀ t₁,
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun p : slab (E := ℝ) t₀ t₁ ↦ σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))
        (hσ.holderWith.continuous hα₀) M
        (fun p ↦ by simpa only [Real.norm_eq_abs] using hbdd _ _ (slabTime p).property) q =
      σ (exp (q : ParabolicSpaceTime ℝ).space) (slabTime q) :=
    congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _)
  rw [hcoe, smul_eq_mul]
  ring

/-- Norm bound for `logSpotHalfVarianceHolder`: if `|σ(e^y, t)| ≤ M` (`0 ≤ M`) and
`(y, t) ↦ σ(e^y, t)` is parabolically `α`-Hölder with constant `H`, then the log-spot half-variance
field `a = σ² / 2` has Hölder-space norm at most `M ^ 2 / 2 + M * H`. -/
theorem norm_logSpotHalfVarianceHolder_le (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hM0 : 0 ≤ M) (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    {H : ℝ≥0} (hσH : HolderWith H α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))) :
    ‖logSpotHalfVarianceHolder hα₀ σ hbdd hσ‖ ≤ M ^ 2 / 2 + M * H := by
  let f : slab (E := ℝ) t₀ t₁ → ℝ := fun p ↦
    σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)
  have hpoint : ∀ p : slab (E := ℝ) t₀ t₁,
      ‖logSpotHalfVarianceHolder hα₀ σ hbdd hσ p‖ ≤ M ^ 2 / 2 := fun p ↦ by
    rw [logSpotHalfVarianceHolder_apply, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (two_pos : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (hbdd _ _ (slabTime p).property) 2) zero_le_two
  have hhold : HolderWith (M.toNNReal * H) α (logSpotHalfVarianceHolder hα₀ σ hbdd hσ) := by
    intro p q
    simp only [logSpotHalfVarianceHolder_apply]
    have hdiff : f p ^ 2 / 2 - f q ^ 2 / 2 = ((f p + f q) / 2) * (f p - f q) := by ring
    have havg : ‖(f p + f q) / 2‖₊ ≤ M.toNNReal := by
      rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs, Real.coe_toNNReal _ hM0, abs_div,
        abs_of_pos (two_pos : (0 : ℝ) < 2)]
      have hp := hbdd (p : ParabolicSpaceTime ℝ).space _ (slabTime p).property
      have hq := hbdd (q : ParabolicSpaceTime ℝ).space _ (slabTime q).property
      linarith [abs_add_le (f p) (f q)]
    rw [eDist_eq_eNorm_sub, hdiff, eNorm_mul, ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' (ENNReal.coe_le_coe.2 havg)
      (by simpa only [eDist_eq_eNorm_sub] using hσH p q)
  simpa only [NNReal.coe_mul, Real.coe_toNNReal _ hM0] using
    HolderSpace.norm_le_of_norm_le_of_holderWith (by positivity) hpoint hhold

/-- A time-only short rate `r : ℝ → ℝ` that is `(α / 2)`-Hölder on `[t₀, t₁]` (`0 < α`), promoted
via `HolderSpace.compSlabTimeL` to a space-independent parabolic `α`-Hölder field on
`slab (E := ℝ) t₀ t₁`. -/
def shortRateHolder (hα₀ : 0 < α) (r : ℝ → ℝ) {H : ℝ≥0}
    (hr : HolderOnWith H (α / 2) r (Icc t₀ t₁)) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  HolderSpace.compSlabTimeL
    (HolderSpace.ofHolderWithOfCompact (div_pos hα₀ two_pos) (fun t : Icc t₀ t₁ ↦ r t)
      fun t s ↦ by simpa only [Subtype.edist_eq] using hr t t.property s s.property)

/-- Evaluation of `shortRateHolder` at a slab point gives `r` at its time coordinate. -/
@[simp]
theorem shortRateHolder_apply (hα₀ : 0 < α) (r : ℝ → ℝ) {H : ℝ≥0}
    (hr : HolderOnWith H (α / 2) r (Icc t₀ t₁)) (p : slab (E := ℝ) t₀ t₁) :
    shortRateHolder hα₀ r hr p = r (slabTime p) := by
  rw [shortRateHolder, HolderSpace.compSlabTimeL_apply]
  exact HolderSpace.ofHolderWithOfCompact_apply (div_pos hα₀ two_pos) (fun t : Icc t₀ t₁ ↦ r t) _
    (slabTime p)

/-- Norm bound for `shortRateHolder`: if `|r(t)| ≤ M` (`0 ≤ M`) and `r` is `H`-Hölder of exponent
`α / 2` on `[t₀, t₁]`, then `shortRateHolder` has Hölder-space norm at most `M + H`. -/
theorem norm_shortRateHolder_le (hα₀ : 0 < α) (r : ℝ → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hbdd : ∀ t ∈ Icc t₀ t₁, |r t| ≤ M) {H : ℝ≥0} (hr : HolderOnWith H (α / 2) r (Icc t₀ t₁)) :
    ‖shortRateHolder hα₀ r hr‖ ≤ M + H :=
  (HolderSpace.norm_compSlabTimeL_apply_le _).trans
    (HolderSpace.norm_ofHolderWithOfCompact_le (div_pos hα₀ two_pos) (fun t : Icc t₀ t₁ ↦ r t) _
      hM0 fun t ↦ by simpa only [Real.norm_eq_abs] using hbdd t.val t.property)

end MarketCoefficients

/-! ### Classical spot-coordinate pricing PDE existence and uniqueness -/

section SpotPricingPDE

/-- **Uniqueness of classical linear-growth prices on `[t₀, t₁]`.** If
`u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solves `weightedLogSpotPricingOperatorL u = 0` with terminal
profile `y ↦ h(e^y) / (1 + e^y)`, and `a` and `rH` match `σ² / 2` and `r` on the interior times
`t ∈ (t₀, t₁)`, then every continuous linear-growth competitor `C` (with `|C(s, t)| ≤ A (1 + s)`)
and matching coefficients and terminal payoff `h` that solves the interior pricing PDE agrees with
the reconstructed price `weightedLogSpotPrice u` on the closed slab `(0, ∞) × [t₀, t₁]`. -/
theorem eq_weightedLogSpotPrice_of_pde_eq_zero_of_terminal_eq (hα : α ≤ 1)
    {σ : ℝ → ℝ → ℝ} {r h : ℝ → ℝ} {A : ℝ}
    {a rH : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    (ha_eq : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄ (ht' : t ∈ Ioo t₀ t₁),
      a (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = σ s t ^ 2 / 2)
    (hr_eq : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄ (ht' : t ∈ Ioo t₀ t₁),
      rH (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) = r t)
    (u : ParabolicC2HolderSpace α ℝ ℝ ht)
    (hPu : weightedLogSpotPricingOperatorL hα a rH u = 0)
    (huterm : ∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = h (exp y) / (1 + exp y))
    {C : ℝ → ℝ → ℝ}
    (hC_cont : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁))
    (hC_growth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s))
    (hC_cd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
    (hC_diff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t)
    (hC_pde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
      deriv (fun τ ↦ C s τ) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
        r t * (s * deriv (fun x ↦ C x t) s - C s t) = 0)
    (hC_term : ∀ ⦃s⦄, 0 < s → C s t₁ = h s) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → C s t = weightedLogSpotPrice u s t := by
  let W := weightedLogSpotPrice u
  refine eq_of_pde_eq_of_terminal_eq (σ := σ) (r := r) (C₁ := C) (C₂ := W)
    (Λ := 2 * ‖a‖) (R := ‖rH‖) (A := max A 0 + ‖u‖)
    (fun s hs t ht' ↦ by
      have ha1 : σ s t ^ 2 / 2 = a (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) :=
        (ha_eq hs ht').symm
      have ha2 : |a (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩)| ≤ ‖a‖ :=
        a.norm_apply_le _
      linarith [(le_abs_self _).trans ha2])
    (fun t ht' ↦ by
      have hr1 : r t = rH (slabMk (log 1) ⟨t, Ioo_subset_Icc_self ht'⟩) :=
        (hr_eq one_pos ht').symm
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
      rw [hC_pde hs ht']
      linear_combination -hW)
    (fun s hs ↦ by
      dsimp only [W]
      rw [hC_term hs, weightedLogSpotPrice_terminal u huterm hs])

/-- **Existence, linear-growth bounds, and uniqueness for the self-financing pricing PDE.**
Let `0 < α < 1`, `t₀ < t₁`, `0 < δ`, let `σ(s, t)` satisfy `δ ≤ σ(s, t)²` and `|σ(e^y, t)| ≤ M`
with `(y, t) ↦ σ(e^y, t)` parabolically `α`-Hölder on `slab t₀ t₁`, let `r` be `(α / 2)`-Hölder on
`[t₀, t₁]`, and let `h` be a terminal payoff whose weighted log-spot profile
`y ↦ h(e^y) / (1 + e^y)` is represented by `g ∈ C_b^{2,α}(ℝ)`. Then there exists a witness
`u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solving the weighted log-spot terminal-value problem (uniquely
by `weightedLogSpotTerminalDataCLE`), and its reconstructed spot price `C = weightedLogSpotPrice u`
is the unique classical solution of the pricing PDE in the linear-growth class, with joint
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
    congrArg Prod.snd <| by
      simpa only [weightedLogSpotTerminalDataCLE_apply] using
        (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a rH ⟨δ / 2, half_pos hδ, ha⟩).apply_symm_apply
          (0, g)
  have huterm : ∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = h (exp y) / (1 + exp y) :=
    fun y ↦ by rw [← spatialTrace_apply, htr, hg]
  refine ⟨u, hPu, htr, fun s hs ↦ weightedLogSpotPrice_terminal u huterm hs,
    (continuousOn_weightedLogSpotPrice u).mono (prod_mono_right (subset_univ _)),
    continuousOn_deriv_weightedLogSpotPrice_spot u,
    continuousOn_deriv_deriv_weightedLogSpotPrice_spot u,
    continuousOn_derivWithin_weightedLogSpotPrice_time u,
    fun s hs t ht' ↦ ⟨(contDiffOn_weightedLogSpotPrice u ⟨t, ht'⟩).contDiffAt (Ioi_mem_nhds hs),
      abs_weightedLogSpotPrice_add_abs_mul_deriv_le u hs ht'⟩,
    fun s hs t ht' ↦ ⟨differentiableAt_weightedLogSpotPrice_time u s ht', ?_⟩,
    fun C A hCc hCg hCcd hCd hCpde hCt ↦ ?_⟩
  · have hW := pde_weightedLogSpotPrice_eq_mul_of_mem_Ioo hα₁.le a rH u hs ht'
    rw [hPu, HolderSpace.zero_apply, mul_zero] at hW
    simp only [a, rH, logSpotHalfVarianceHolder_apply, shortRateHolder_apply, space_slabMk,
      slabTime_slabMk, exp_log hs] at hW
    linear_combination hW
  · exact eq_weightedLogSpotPrice_of_pde_eq_zero_of_terminal_eq hα₁.le
      (fun s hs t ht' ↦ by simp [a, exp_log hs]) (fun s _ t ht' ↦ by simp [rH])
      u hPu huterm hCc hCg hCcd hCd hCpde hCt

end SpotPricingPDE

end TauCeti.Finance
