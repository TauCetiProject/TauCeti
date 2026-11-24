/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Solvability
public import TauCeti.Probability.Finance.Pricing.Coefficients
import TauCeti.Probability.Finance.Pricing.Comparison.WeightedLogSpot

/-!
# Existence of prices of linear growth with Hölder local volatility

Write `a` for the diffusion coefficient (the half-variance `a = σ² / 2` in the market
specialization below) in log-spot coordinates `y = log s`, and let `r` be
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

Specialized to market volatility `σ(s, t)` (with half-variance `a = σ² / 2`) and a time-only
`(α / 2)`-Hölder short rate `r(t)`:

* `TauCeti.Finance.logSpotHalfVarianceHolder` and `TauCeti.Finance.shortRateHolder` (in
  `TauCeti.Probability.Finance.Pricing.Coefficients`) build the parabolic Hölder coefficient fields
  on `slab t₀ t₁`, with quantitative norm bounds exported by
  `TauCeti.Finance.norm_logSpotHalfVarianceHolder_le` and
  `TauCeti.Finance.norm_shortRateHolder_le`.
* `TauCeti.Finance.eq_weightedLogSpotPrice_of_pde_eq_zero_of_terminal_eq` (in
  `TauCeti.Probability.Finance.Pricing.Comparison.WeightedLogSpot`) proves that every competitor
  jointly continuous on the closed positive-spot slab `(0, ∞) × [t₀, t₁]` with linear growth
  (`|C(s, t)| ≤ A (1 + s)`) that is twice continuously differentiable in spot and differentiable in
  time at interior times `t ∈ (t₀, t₁)`, solves the interior pricing PDE, and attains the same
  terminal payoff `h` at `t₁` agrees with `weightedLogSpotPrice u` on `(0, ∞) × [t₀, t₁]`.
* `TauCeti.Finance.marketPriceProfile` constructs the solution
  `u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` of the weighted log-spot terminal-value problem from a
  uniformly elliptic (`δ ≤ σ(s, t)²`), bounded (`|σ(e^y, t)| ≤ M`), parabolically `α`-Hölder
  volatility `(y, t) ↦ σ(e^y, t)`, an `(α / 2)`-Hölder short rate `r` on `[t₀, t₁]`, and a
  weighted terminal payoff `g ∈ C_b^{2,α}(ℝ)`, packaged as a continuous linear map in `g` by
  `TauCeti.Finance.marketPriceProfileL` (with `TauCeti.Finance.marketPriceProfile_zero`,
  `TauCeti.Finance.marketPriceProfile_add`, `TauCeti.Finance.marketPriceProfile_smul`). Separate
  lemmas expose its vanishing weighted residual
  (`TauCeti.Finance.weightedLogSpotPricingOperatorL_marketPriceProfile`), terminal trace
  (`TauCeti.Finance.spatialTrace_marketPriceProfile`), uniqueness from its weighted residual and
  terminal trace (`TauCeti.Finance.eq_marketPriceProfile`), terminal payoff
  (`TauCeti.Finance.weightedLogSpotPrice_marketPriceProfile_terminal`), closed-slab `derivWithin`
  and interior classical PDEs (`TauCeti.Finance.pde_weightedLogSpotPrice_marketPriceProfile`,
  `TauCeti.Finance.pde_weightedLogSpotPrice_marketPriceProfile_of_mem_Ioo`), and uniqueness in the
  linear-growth classical class
  (`TauCeti.Finance.eq_weightedLogSpotPrice_marketPriceProfile_of_pde_eq_zero_of_terminal_eq`),
  while `TauCeti.Finance.weightedLogSpotPrice_marketPriceProfile_spec` collects the classical
  regularity, PDE, terminal payoff, price-and-dollar-delta linear-growth bound, and uniqueness
  guarantees for `weightedLogSpotPrice (marketPriceProfile ...)` in one market-facing theorem.

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
`0 < α < 1`, `t₀ < t₁`, let the diffusion coefficient `a ≥ lam > 0` (specializing to the
half-variance `σ² / 2` for a market volatility `σ`) and the rate `r` be
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
  exact and_congr (pde_weightedLogSpotPrice_eq_zero_iff hα₁.le a r v)
    (weightedLogSpotPrice_slice_iff v ⟨t₁, right_mem_Icc.2 ht.le⟩ hg)

/-- **Weighted log-spot solution profile for the market pricing PDE.** Given `0 < α < 1`,
`t₀ < t₁`, a uniformly elliptic (`0 < δ ≤ σ(s, t)²`), bounded (`|σ(e^y, t)| ≤ M`), parabolically
`α`-Hölder volatility `(y, t) ↦ σ(e^y, t)`, an `(α / 2)`-Hölder short rate `r` on `[t₀, t₁]`,
and a weighted terminal datum `g ∈ C_b^{2,α}(ℝ)`, `marketPriceProfile` is the unique
`u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solving the weighted log-spot terminal-value problem with zero
forcing and terminal trace `g`. -/
def marketPriceProfile (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    {σ : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {δ : ℝ} {M H_r : ℝ≥0}
    (hδ : 0 < δ)
    (hσ_low : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → δ ≤ σ s t ^ 2)
    (hσ_bdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ_hol : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (hr_hol : HolderOnWith H_r (α / 2) r (Icc t₀ t₁))
    (g : CkHolderSpace 2 α ℝ ℝ) :
    ParabolicC2HolderSpace α ℝ ℝ ht :=
  (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht
    (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (shortRateHolder hα₀ r hr_hol)
    ⟨δ / 2, half_pos hδ, half_le_logSpotHalfVarianceHolder hα₀ hσ_low hσ_bdd hσ_hol⟩).symm
    (0, g)

/-- **Solution operator for the weighted market pricing PDE.** As a continuous linear map in the
weighted terminal datum `g ∈ C_b^{2,α}(ℝ)`, `marketPriceProfileL` maps `g` to
`marketPriceProfile ... g`. -/
def marketPriceProfileL (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    {σ : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {δ : ℝ} {M H_r : ℝ≥0}
    (hδ : 0 < δ)
    (hσ_low : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → δ ≤ σ s t ^ 2)
    (hσ_bdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ_hol : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (hr_hol : HolderOnWith H_r (α / 2) r (Icc t₀ t₁)) :
    CkHolderSpace 2 α ℝ ℝ →L[ℝ] ParabolicC2HolderSpace α ℝ ℝ ht :=
  (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht
    (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (shortRateHolder hα₀ r hr_hol)
    ⟨δ / 2, half_pos hδ,
      half_le_logSpotHalfVarianceHolder hα₀ hσ_low hσ_bdd hσ_hol⟩).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (CkHolderSpace 2 α ℝ ℝ))

/-- Pointwise evaluation of `marketPriceProfileL` agrees with `marketPriceProfile`. -/
@[simp]
theorem marketPriceProfileL_apply (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    {σ : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {δ : ℝ} {M H_r : ℝ≥0}
    (hδ : 0 < δ)
    (hσ_low : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → δ ≤ σ s t ^ 2)
    (hσ_bdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ_hol : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (hr_hol : HolderOnWith H_r (α / 2) r (Icc t₀ t₁))
    (g : CkHolderSpace 2 α ℝ ℝ) :
    marketPriceProfileL hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g =
      marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g :=
  (rfl)

section MarketPriceProfile

variable (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
  {σ : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {δ : ℝ} {M H_r : ℝ≥0}
  (hδ : 0 < δ)
  (hσ_low : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → δ ≤ σ s t ^ 2)
  (hσ_bdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
  (hσ_hol : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
    σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
  (hr_hol : HolderOnWith H_r (α / 2) r (Icc t₀ t₁))
  (g : CkHolderSpace 2 α ℝ ℝ)

/-- Equation lemma expressing `marketPriceProfile` as the inverse terminal-data isomorphism
applied to `(0, g)`. -/
theorem marketPriceProfile_def :
    marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g =
      (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht
        (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (shortRateHolder hα₀ r hr_hol)
        ⟨δ / 2, half_pos hδ,
          half_le_logSpotHalfVarianceHolder hα₀ hσ_low hσ_bdd hσ_hol⟩).symm (0, g) :=
  (rfl)

/-- The weighted market price profile vanishes for zero terminal payoff. -/
@[simp]
theorem marketPriceProfile_zero :
    marketPriceProfile (α := α) (t₀ := t₀) (t₁ := t₁) hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol
      hr_hol 0 = 0 :=
  (marketPriceProfileL hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol).map_zero

/-- The weighted market price profile is additive in the terminal datum. -/
theorem marketPriceProfile_add (g₁ g₂ : CkHolderSpace 2 α ℝ ℝ) :
    marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol (g₁ + g₂) =
      marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g₁ +
        marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g₂ := by
  simp only [← marketPriceProfileL_apply, map_add]

/-- The weighted market price profile commutes with scalar multiplication in the terminal datum. -/
theorem marketPriceProfile_smul (c : ℝ) :
    marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol (c • g) =
      c • marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g := by
  simp only [← marketPriceProfileL_apply, map_smul]

/-- The weighted log-spot residual of `marketPriceProfile` vanishes everywhere on the slab. -/
@[simp]
theorem weightedLogSpotPricingOperatorL_marketPriceProfile :
    weightedLogSpotPricingOperatorL hα₁.le
        (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (shortRateHolder hα₀ r hr_hol)
        (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) = 0 := by
  rw [marketPriceProfile_def]
  exact weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply (0, g)

/-- The terminal spatial trace of `marketPriceProfile` at `t₁` is `g`. -/
@[simp]
theorem spatialTrace_marketPriceProfile :
    (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = g := by
  rw [marketPriceProfile_def]
  exact spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply (0, g)

/-- At time `t₁`, `marketPriceProfile` evaluates to `g y` at `(y, t₁)`. -/
@[simp]
theorem marketPriceProfile_apply_slabMk_right (y : ℝ) :
    marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g
      (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = g y := by
  rw [marketPriceProfile_def]
  exact weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right (0, g) y

/-- **Uniqueness for `marketPriceProfile`.** Any weighted profile `u ∈ C_b^{2+α,1+α/2}` with
zero weighted pricing residual and terminal trace `g` at `t₁` equals `marketPriceProfile ... g`. -/
theorem eq_marketPriceProfile {u : ParabolicC2HolderSpace α ℝ ℝ ht}
    (hu_pde : weightedLogSpotPricingOperatorL hα₁.le
      (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (shortRateHolder hα₀ r hr_hol) u = 0)
    (hu_trace : u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩ = g) :
    u = marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g := by
  rw [marketPriceProfile_def, ContinuousLinearEquiv.eq_symm_apply,
    weightedLogSpotTerminalDataCLE_apply, hu_pde, hu_trace]

/-- **Terminal payoff of the reconstructed market price.** If `g y = h (exp y) / (1 + exp y)`,
then the reconstructed price `weightedLogSpotPrice (marketPriceProfile ...)` attains `h s` at
`t₁` for all `s > 0`. -/
theorem weightedLogSpotPrice_marketPriceProfile_terminal {h : ℝ → ℝ}
    (hg : ∀ y, g y = h (exp y) / (1 + exp y)) {s : ℝ} (hs : 0 < s) :
    weightedLogSpotPrice
      (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) s t₁ = h s :=
  weightedLogSpotPrice_slice _ ⟨t₁, right_mem_Icc.2 ht.le⟩
    (fun y ↦ by rw [marketPriceProfile_apply_slabMk_right, hg]) hs

/-- **Closed-slab spot pricing equation for `marketPriceProfile`.** On `(0, ∞) × [t₀, t₁]`, the
reconstructed price `C = weightedLogSpotPrice (marketPriceProfile ...)` solves the spot pricing
equation with within-slab time derivative `derivWithin` (one-sided at `t₀` and `t₁`). -/
theorem pde_weightedLogSpotPrice_marketPriceProfile {s : ℝ} (hs : 0 < s)
    {t : ℝ} (ht' : t ∈ Icc t₀ t₁) :
    derivWithin
          (weightedLogSpotPrice
            (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) s)
          (Icc t₀ t₁) t +
        σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦
          weightedLogSpotPrice
            (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) x t) s +
        r t * (s * deriv (fun x ↦
          weightedLogSpotPrice
            (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) x t) s -
          weightedLogSpotPrice
            (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) s t) = 0 := by
  have hW := pde_weightedLogSpotPrice_eq_mul hα₁.le
    (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (shortRateHolder hα₀ r hr_hol)
    (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) hs ⟨t, ht'⟩
  rw [logSpotHalfVarianceHolder_apply, shortRateHolder_apply, space_slabMk, exp_log hs,
    slabTime_slabMk, weightedLogSpotPricingOperatorL_marketPriceProfile, HolderSpace.zero_apply,
    mul_zero, div_mul_eq_mul_div] at hW
  exact hW

/-- **Interior classical spot pricing PDE for `marketPriceProfile`.** At every interior time
`t ∈ (t₀, t₁)` and `s > 0`, `weightedLogSpotPrice (marketPriceProfile ...)` solves the classical
pricing PDE with ordinary time derivative `deriv`. -/
theorem pde_weightedLogSpotPrice_marketPriceProfile_of_mem_Ioo {s : ℝ} (hs : 0 < s)
    {t : ℝ} (ht' : t ∈ Ioo t₀ t₁) :
    deriv
          (weightedLogSpotPrice
            (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) s) t +
        σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦
          weightedLogSpotPrice
            (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) x t) s +
        r t * (s * deriv (fun x ↦
          weightedLogSpotPrice
            (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) x t) s -
          weightedLogSpotPrice
            (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) s t) = 0 := by
  simpa only [derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)] using
    pde_weightedLogSpotPrice_marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g hs
      (Ioo_subset_Icc_self ht')

/-- **Uniqueness for the spot pricing PDE in the linear-growth class.** Any competitor `C` that is
jointly continuous on `(0, ∞) × [t₀, t₁]`, satisfies `|C(s, t)| ≤ A (1 + s)`, is twice
continuously differentiable in spot and differentiable in time at interior times `t ∈ (t₀, t₁)`,
solves the interior pricing PDE, and matches `h` at `t₁` (where `g y = h (exp y) / (1 + exp y)`)
agrees with `weightedLogSpotPrice (marketPriceProfile ...)` on `(0, ∞) × [t₀, t₁]`. -/
theorem eq_weightedLogSpotPrice_marketPriceProfile_of_pde_eq_zero_of_terminal_eq {h : ℝ → ℝ}
    (hg : ∀ y, g y = h (exp y) / (1 + exp y)) {C : ℝ → ℝ → ℝ} (A : ℝ)
    (hC_cont : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁))
    (hC_growth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s))
    (hC_cd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
    (hC_diff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t)
    (hC_pde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
      deriv (fun τ ↦ C s τ) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
        r t * (s * deriv (fun x ↦ C x t) s - C s t) = 0)
    (hC_term : ∀ ⦃s⦄, 0 < s → C s t₁ = h s) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ →
      C s t = weightedLogSpotPrice
        (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) s t :=
  eq_weightedLogSpotPrice_of_pde_eq_zero_of_terminal_eq hα₁.le
    (a₀ := fun s t ↦ σ s t ^ 2 / 2) (r₀ := fun _ t ↦ r t)
    (fun _ _ _ _ ↦ by positivity)
    (fun s hs t ht' ↦ by simp [exp_log hs]) (fun s _ t ht' ↦ by simp)
    _ (weightedLogSpotPricingOperatorL_marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol
      g)
    (fun y ↦ by rw [marketPriceProfile_apply_slabMk_right, hg])
    hC_cont hC_growth hC_cd hC_diff
    (fun s hs t ht' ↦ by simpa only [div_mul_eq_mul_div] using hC_pde hs ht') hC_term

/-- **Market specification for the reconstructed spot price.** For `C := weightedLogSpotPrice u`
with `u := marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g` and terminal payoff
`h` satisfying `g y = h (exp y) / (1 + exp y)`, `C` enjoys joint continuity of `C`, `∂ₛC`, `∂ₛ²C`,
and within-slab `∂ₜC` on `(0, ∞) × [t₀, t₁]`, twice continuous spot differentiability on
`(0, ∞) × [t₀, t₁]` and interior time differentiability on `(0, ∞) × (t₀, t₁)`, solves both the
closed-slab `derivWithin` and interior classical pricing PDEs, attains `h` at `t₁`, satisfies the
price-and-dollar-delta linear-growth bound `|C(s, t)| + |s ∂ₛC(s, t)| ≤ 2 ‖u‖ (1 + s)`, and
is the unique solution in the linear-growth classical class. -/
theorem weightedLogSpotPrice_marketPriceProfile_spec {h : ℝ → ℝ}
    (hg : ∀ y, g y = h (exp y) / (1 + exp y)) :
    let u := marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g
    ContinuousOn (Function.uncurry (weightedLogSpotPrice u)) (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun s ↦ weightedLogSpotPrice u s p.2) p.1)
        (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ deriv (deriv fun s ↦ weightedLogSpotPrice u s p.2) p.1)
        (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ derivWithin (weightedLogSpotPrice u p.1) (Icc t₀ t₁) p.2)
        (Ioi 0 ×ˢ Icc t₀ t₁) ∧
      (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ →
        ContDiffAt ℝ 2 (fun x ↦ weightedLogSpotPrice u x t) s) ∧
      (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (weightedLogSpotPrice u s) t) ∧
      (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ →
        derivWithin (weightedLogSpotPrice u s) (Icc t₀ t₁) t +
            σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
            r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
              weightedLogSpotPrice u s t) = 0) ∧
      (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
        deriv (weightedLogSpotPrice u s) t +
            σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
            r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
              weightedLogSpotPrice u s t) = 0) ∧
      (∀ ⦃s⦄, 0 < s → weightedLogSpotPrice u s t₁ = h s) ∧
      (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ →
        |weightedLogSpotPrice u s t| + |s * deriv (fun x ↦ weightedLogSpotPrice u x t) s| ≤
          2 * ‖u‖ * (1 + s)) ∧
      ∀ (C : ℝ → ℝ → ℝ) (A : ℝ),
        ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s)) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t) →
        (∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
          deriv (fun τ ↦ C s τ) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
            r t * (s * deriv (fun x ↦ C x t) s - C s t) = 0) →
        (∀ ⦃s⦄, 0 < s → C s t₁ = h s) →
        ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → C s t = weightedLogSpotPrice u s t :=
  ⟨(continuousOn_weightedLogSpotPrice _).mono (prod_mono_right (subset_univ _)),
    continuousOn_deriv_weightedLogSpotPrice_spot _,
    continuousOn_deriv_deriv_weightedLogSpotPrice_spot _,
    continuousOn_derivWithin_weightedLogSpotPrice_time _,
    fun _ hs t ht' ↦ (contDiffOn_weightedLogSpotPrice _ ⟨t, ht'⟩).contDiffAt (Ioi_mem_nhds hs),
    fun s _ _ ht' ↦ differentiableAt_weightedLogSpotPrice_time _ s ht',
    fun _ hs _ ht' ↦
      pde_weightedLogSpotPrice_marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g hs
        ht',
    fun _ hs _ ht' ↦
      pde_weightedLogSpotPrice_marketPriceProfile_of_mem_Ioo hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol
        hr_hol g hs ht',
    fun _ hs ↦
      weightedLogSpotPrice_marketPriceProfile_terminal hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g
        hg hs,
    fun _ hs _ ht' ↦ abs_weightedLogSpotPrice_add_abs_mul_deriv_le _ hs ht',
    fun _ _ hCc hCg hCcd hCd hCpde hCt ↦
      eq_weightedLogSpotPrice_marketPriceProfile_of_pde_eq_zero_of_terminal_eq hα₀ hα₁ ht hδ hσ_low
        hσ_bdd hσ_hol hr_hol g hg _ hCc hCg hCcd hCd hCpde hCt⟩

end MarketPriceProfile

end TauCeti.Finance
