/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Pricing.Operator
public import TauCeti.Probability.Finance.WeightedLogSpot
import TauCeti.Analysis.PDE.Parabolic.Holder.Line
import TauCeti.Probability.Finance.Comparison

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

## Terminal-data isomorphism, solution operator, and classical solvability

This file packages `v ↦ (P v, v(·, t₁))` as a Banach-space isomorphism
(`weightedLogSpotTerminalDataCLE`) via `realTerminalDataCLE`. At zero forcing this yields the
homogeneous terminal solution operator `weightedLogSpotTerminalSolutionL`, its discounted supremum
bound (`abs_weightedLogSpotTerminalSolutionL_le_exp_mul`), its spot-PDE identities in all three
time-derivative conventions, and its discounted linear-growth bound. Finally, `halfSqVolatility`,
`HolderSpace.ofHolderSpaceTime`, and `HolderSpace.ofHolderTime` lift log-spot `α`-Hölder / time
`(α / 2)`-Hölder coefficients to `C_b^{α,α/2}`, giving
`exists_weightedLogSpotPrice_terminal_and_pde` and `eq_weightedLogSpotPrice_of_pde_of_terminal`.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964,
  Chapter 2, Section 4.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Hölder Spaces*, AMS, 1996,
  Chapter 8.
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

/-! ### Terminal-data Banach isomorphism -/

section TerminalDataCLE

open ContinuousLinearMap

/-- **The terminal-data isomorphism of the weighted log-spot pricing operator.** For `0 < α < 1`,
`t₀ < t₁`, and `a, r ∈ C_b^{α,α/2}(ℝ × [t₀, t₁])` with `a` uniformly positive, `u ↦ (P u, u(·, t₁))`
as a Banach-space isomorphism onto `C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`. -/
def weightedLogSpotTerminalDataCLE (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ :=
  realTerminalDataCLE hα₀ hα₁ ht (weightedLogSpotSecondOrderCoeff a)
    (weightedLogSpotFirstOrderCoeff hα₁.le a r) (weightedLogSpotZerothOrderCoeff hα₁.le r)
    (ha.elim fun lam h ↦
      ⟨lam, h.1, fun p ↦ (weightedLogSpotSecondOrderCoeff_apply_mul a p).symm ▸ h.2 p⟩)

section TerminalDataEval

variable {hα₀ : 0 < α} {hα₁ : α < 1} {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}

@[simp] theorem weightedLogSpotTerminalDataCLE_apply (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha u =
      (weightedLogSpotPricingOperatorL hα₁.le a r u,
        u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  rw [weightedLogSpotTerminalDataCLE, realTerminalDataCLE_apply,
    ← weightedLogSpotPricingOperatorL_def]

@[simp] theorem weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotPricingOperatorL hα₁.le a r
      ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d) = d.1 := by
  rw [weightedLogSpotTerminalDataCLE, weightedLogSpotPricingOperatorL_def,
    backwardParabolicOperatorL_realTerminalDataCLE_symm_apply]

@[simp] theorem spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = d.2 :=
  spatialTrace_realTerminalDataCLE_symm_apply d

@[simp] theorem weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) (x : ℝ) :
    (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d
      (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) = d.2 x := by
  rw [← spatialTrace_apply, spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply]

/-- The underlying continuous linear map of `weightedLogSpotTerminalDataCLE` is the product of
`weightedLogSpotPricingOperatorL` and the terminal spatial trace. -/
theorem weightedLogSpotTerminalDataCLE_toContinuousLinearMap :
    (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).toContinuousLinearMap =
      (weightedLogSpotPricingOperatorL (ht := ht) hα₁.le a r).prod
        (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩) :=
  ContinuousLinearMap.ext fun u ↦ by simp [spatialTraceL_apply]

/-- **Pointwise exponential bound for the weighted log-spot solution operator.** If `r ≥ -γ` with
`0 ≤ γ`, `|f| ≤ K` and `|g| ≤ M`, then the solution `u` of `P u = f`, `u(·, t₁) = g` satisfies
`|u(y, t)| ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`. For a nonnegative short rate, `γ = 0`. -/
theorem abs_weightedLogSpotTerminalDataCLE_symm_apply_le {γ M K : ℝ}
    (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ)
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ)
    (hd₁ : ∀ p, |d.1 p| ≤ K) (hd₂ : ∀ y, |d.2 y| ≤ M) (p : slab (E := ℝ) t₀ t₁) :
    |(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d p| ≤
      Real.exp (γ * (t₁ - slabTime p)) * (M + (t₁ - slabTime p) * K) := by
  obtain ⟨δ, hδ, ha'⟩ := ha
  refine abs_le_exp_mul_mul_add_mul_of_abs_weightedLogSpotPricingOperatorL_le hα₁.le
    (fun q ↦ hδ.le.trans (ha' q)) hr hγ _ ?_ ?_ p
  · intro q
    rw [weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply]
    exact hd₁ q
  · intro y
    rw [weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right]
    exact hd₂ y

end TerminalDataEval

private theorem norm_weightedCoeffs_le {α : ℝ≥0} {t₀ t₁ : ℝ} (hα : α ≤ 1) {K : ℝ≥0}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} (hak : ‖a‖ ≤ K) (hrk : ‖r‖ ≤ K) :
    ‖weightedLogSpotSecondOrderCoeff a‖ ≤ (6 * K : ℝ≥0) ∧
      ‖weightedLogSpotFirstOrderCoeff hα a r‖ ≤ (6 * K : ℝ≥0) ∧
      ‖weightedLogSpotZerothOrderCoeff hα r‖ ≤ (6 * K : ℝ≥0) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (norm_weightedLogSpotSecondOrderCoeff_le a).trans ?_
    push_cast
    linarith [K.coe_nonneg]
  · refine (norm_weightedLogSpotFirstOrderCoeff_le hα a r).trans ?_
    push_cast
    linarith [K.coe_nonneg]
  · refine (norm_weightedLogSpotZerothOrderCoeff_le hα r).trans ?_
    push_cast
    linarith [K.coe_nonneg]

/-- **Uniform Schauder estimate for the weighted log-spot terminal-value problem.** For `0 < α < 1`,
`0 < δ`, a coefficient bound `K` and a horizon bound `T₀`, the solution operators of the weighted
log-spot terminal-value problems on `ℝ × [t₀, t₁]` with `t₁ - t₀ ≤ T₀`, `δ ≤ a`, `‖a‖ ≤ K` and
`‖r‖ ≤ K` are uniformly bounded in operator norm. -/
theorem exists_norm_weightedLogSpotTerminalDataCLE_symm_le {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {δ : ℝ} (hδ : 0 < δ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∀ p, δ ≤ a p),
        ‖a‖ ≤ K → ‖r‖ ≤ K →
        ‖(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r
            ⟨δ, hδ, ha⟩).symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨C, hC, hest⟩ := exists_norm_realTerminalDataCLE_symm_le (α := α) hα₀ hα₁ hδ (6 * K) T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hTT₀ a r ha hak hrk ↦ ?_⟩
  obtain ⟨h2, h1, h0⟩ := norm_weightedCoeffs_le hα₁.le hak hrk
  exact hest ht hTT₀ (weightedLogSpotSecondOrderCoeff a)
    (weightedLogSpotFirstOrderCoeff hα₁.le a r) (weightedLogSpotZerothOrderCoeff hα₁.le r)
    (fun p ↦ by simp [ha p]) h2 h1 h0

/-- **Lipschitz dependence of the weighted log-spot solution operator on `(a, r)`.** Under the
bounds of `exists_norm_weightedLogSpotTerminalDataCLE_symm_le`, the solution operators for `(a, r)`
and `(a', r')` differ in operator norm by at most `C (‖a - a'‖ + ‖r - r'‖)`. -/
theorem exists_norm_weightedLogSpotTerminalDataCLE_symm_sub_le {α : ℝ≥0} (hα₀ : 0 < α)
    (hα₁ : α < 1) {δ : ℝ} (hδ : 0 < δ) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (a a' r r' : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)
        (ha : ∀ p, δ ≤ a p) (ha' : ∀ p, δ ≤ a' p),
        ‖a‖ ≤ K → ‖r‖ ≤ K → ‖a'‖ ≤ K → ‖r'‖ ≤ K →
        ‖(weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r
            ⟨δ, hδ, ha⟩).symm.toContinuousLinearMap -
          (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a' r'
            ⟨δ, hδ, ha'⟩).symm.toContinuousLinearMap‖ ≤ C * (‖a - a'‖ + ‖r - r'‖) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_realTerminalDataCLE_symm_sub_le (α := α) hα₀ hα₁ hδ (6 * K) T₀
  refine ⟨C * 6, by positivity, fun {t₀ t₁} ht hTT₀ a a' r r' ha ha' hak hrk hak' hrk' ↦ ?_⟩
  obtain ⟨h2, h1, h0⟩ := norm_weightedCoeffs_le hα₁.le hak hrk
  obtain ⟨h2', h1', h0'⟩ := norm_weightedCoeffs_le hα₁.le hak' hrk'
  have hmid := hest ht hTT₀
    (weightedLogSpotSecondOrderCoeff a) (weightedLogSpotSecondOrderCoeff a')
    (weightedLogSpotFirstOrderCoeff hα₁.le a r) (weightedLogSpotFirstOrderCoeff hα₁.le a' r')
    (weightedLogSpotZerothOrderCoeff hα₁.le r) (weightedLogSpotZerothOrderCoeff hα₁.le r')
    (fun p ↦ by simp [ha p]) (fun p ↦ by simp [ha' p]) h2 h1 h0 h2' h1' h0'
  have hd2 : ‖weightedLogSpotSecondOrderCoeff a - weightedLogSpotSecondOrderCoeff a'‖ ≤
      ‖a - a'‖ := by
    rw [← weightedLogSpotSecondOrderCoeff_sub]
    exact norm_weightedLogSpotSecondOrderCoeff_le (a - a')
  have hd1 : ‖weightedLogSpotFirstOrderCoeff hα₁.le a r -
        weightedLogSpotFirstOrderCoeff hα₁.le a' r'‖ ≤ 5 * ‖a - a'‖ + ‖r - r'‖ := by
    rw [← weightedLogSpotFirstOrderCoeff_sub]
    exact norm_weightedLogSpotFirstOrderCoeff_le hα₁.le (a - a') (r - r')
  have hd0 : ‖weightedLogSpotZerothOrderCoeff hα₁.le r -
        weightedLogSpotZerothOrderCoeff hα₁.le r'‖ ≤ 3 * ‖r - r'‖ := by
    rw [← weightedLogSpotZerothOrderCoeff_sub]
    exact norm_weightedLogSpotZerothOrderCoeff_le hα₁.le (r - r')
  have hsum :
      ‖weightedLogSpotSecondOrderCoeff a - weightedLogSpotSecondOrderCoeff a'‖ +
          ‖weightedLogSpotFirstOrderCoeff hα₁.le a r -
            weightedLogSpotFirstOrderCoeff hα₁.le a' r'‖ +
          ‖weightedLogSpotZerothOrderCoeff hα₁.le r -
            weightedLogSpotZerothOrderCoeff hα₁.le r'‖ ≤
        6 * (‖a - a'‖ + ‖r - r'‖) := by
    linarith [norm_nonneg (a - a'), norm_nonneg (r - r')]
  dsimp only [weightedLogSpotTerminalDataCLE]
  convert (hmid.trans (mul_le_mul_of_nonneg_left hsum hC)).trans_eq (mul_assoc _ _ _).symm using 1

end TerminalDataCLE

/-- **The weighted terminal-value problem is well posed.** For `0 < α < 1`, a local variance rate
`a ≥ lam > 0` and a rate `r` in `C_b^{α,α/2}(ℝ × [t₀, t₁])`, the terminal-data map
`v ↦ (P v, v(·, t₁))` of the weighted log-spot pricing operator `P` is an isomorphism of Banach
spaces from `C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}`. -/
theorem isInvertible_weightedLogSpotPricingOperatorL_prod_spatialTraceL (hα₀ : 0 < α)
    (hα₁ : α < 1) {a : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p, lam ≤ a p) :
    ((weightedLogSpotPricingOperatorL (ht := ht) hα₁.le a r).prod
      (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩)).IsInvertible :=
  ⟨weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ⟨lam, hlam, ha⟩,
    ContinuousLinearMap.ext fun u ↦ by simp [spatialTraceL_apply]⟩

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
    rw [pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL hα₁.le v (exp_pos y) t,
      log_exp] at hp
    exact (mul_eq_zero.1 hp).resolve_left (by positivity)
  · rw [pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL hα₁.le v hs t, hv,
      HolderSpace.zero_apply, mul_zero]
  · ext y
    have hy := (weightedLogSpotPrice_of_mem v (exp y) ⟨t₁, right_mem_Icc.2 ht.le⟩).symm.trans
      (hv (exp y) (exp_pos y))
    rw [log_exp] at hy
    rw [spatialTrace_apply, hg, ← hy, mul_div_cancel_left₀ _ (by positivity)]
  · exact weightedLogSpotPrice_terminal v (fun y ↦ by rw [← spatialTrace_apply, hv, hg]) hs

/-! ### The homogeneous terminal-value solution operator -/

section TerminalSolution

open ContinuousLinearMap

/-- **The homogeneous terminal solution operator.** Sends `g ∈ C_b^{2,α}(ℝ)` to the unique
`u ∈ C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` solving `P u = 0` with `u(·, t₁) = g`. -/
def weightedLogSpotTerminalSolutionL (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p) :
    CkHolderSpace 2 α ℝ ℝ →L[ℝ] ParabolicC2HolderSpace α ℝ ℝ ht :=
  (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℝ (HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) (CkHolderSpace 2 α ℝ ℝ)

section TerminalSolutionEval
variable {hα₀ : 0 < α} {hα₁ : α < 1} {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}

theorem weightedLogSpotTerminalSolutionL_apply (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g =
      (weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm (0, g) := by
  simp [weightedLogSpotTerminalSolutionL]

@[simp] theorem weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL
    (g : CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotPricingOperatorL hα₁.le a r
      (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) = 0 := by
  rw [weightedLogSpotTerminalSolutionL_apply,
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply]

@[simp] theorem spatialTrace_weightedLogSpotTerminalSolutionL (g : CkHolderSpace 2 α ℝ ℝ) :
    (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = g := by
  rw [weightedLogSpotTerminalSolutionL_apply,
    spatialTrace_weightedLogSpotTerminalDataCLE_symm_apply]

@[simp] theorem weightedLogSpotTerminalSolutionL_slabMk_right (g : CkHolderSpace 2 α ℝ ℝ) (x : ℝ) :
    weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g
      (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) = g x := by
  rw [weightedLogSpotTerminalSolutionL_apply,
    weightedLogSpotTerminalDataCLE_symm_apply_slabMk_right]

end TerminalSolutionEval

/-- **Discounted supremum bound for the terminal solution.** When `r ≥ -γ` with `0 ≤ γ` and
`|g y| ≤ M` on `ℝ`, the solution satisfies `|u p| ≤ exp (γ (t₁ - t)) M` on the whole slab. -/
theorem abs_weightedLogSpotTerminalSolutionL_le_exp_mul {hα₀ : 0 < α} {hα₁ : α < 1}
    {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ} {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}
    {γ M : ℝ} (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ) {g : CkHolderSpace 2 α ℝ ℝ} (hg : ∀ y, |g y| ≤ M)
    (p : slab (E := ℝ) t₀ t₁) :
    |weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g p| ≤ exp (γ * (t₁ - slabTime p)) * M := by
  obtain ⟨lam, hlam, hle⟩ := ha
  simpa using abs_le_exp_mul_mul_add_mul_of_abs_weightedLogSpotPricingOperatorL_le hα₁.le
    (fun q ↦ hlam.le.trans (hle q)) hr hγ (M := M) (K := 0)
    (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ⟨lam, hlam, hle⟩ g)
    (fun q ↦ by simp) (fun y ↦ by simpa using hg y) p

end TerminalSolution

/-! ### Financial coefficient adapters -/

section HalfSq
variable {X : Type*} [MetricSpace X]

/-- Half the squared volatility `(1 / 2) σ²`, built in the Banach algebra `HolderSpace α X ℝ`. -/
def halfSqVolatility (σ : HolderSpace α X ℝ) : HolderSpace α X ℝ := (1 / 2 : ℝ) • (σ * σ)

theorem halfSqVolatility_def (σ : HolderSpace α X ℝ) :
    halfSqVolatility σ = (1 / 2 : ℝ) • (σ * σ) := (rfl)

@[simp] theorem halfSqVolatility_apply (σ : HolderSpace α X ℝ) (x : X) :
    halfSqVolatility σ x = σ x ^ 2 / 2 := by simp [halfSqVolatility_def, sq]; ring

@[simp] theorem halfSqVolatility_zero : halfSqVolatility (0 : HolderSpace α X ℝ) = 0 := by
  simp [halfSqVolatility_def]

@[simp] theorem halfSqVolatility_neg (σ : HolderSpace α X ℝ) :
    halfSqVolatility (-σ) = halfSqVolatility σ := by ext x; simp

theorem norm_halfSqVolatility_le (σ : HolderSpace α X ℝ) : ‖halfSqVolatility σ‖ ≤ ‖σ‖ ^ 2 / 2 := by
  rw [halfSqVolatility_def, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2), sq]
  linarith [norm_mul_le σ σ]

theorem div_le_halfSqVolatility_of_le_sq {σ : HolderSpace α X ℝ} {δ : ℝ} (hδ : ∀ x, δ ≤ σ x ^ 2)
    (x : X) : δ / 2 ≤ halfSqVolatility σ x := by rw [halfSqVolatility_apply]; linarith [hδ x]
end HalfSq

private def logSpotVolBCF (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))) :
    BoundedContinuousFunction (slab (E := ℝ) t₀ t₁) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : slab (E := ℝ) t₀ t₁ ↦ σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))
    (hσ.holderWith.continuous hα₀) M (fun p ↦ by
      rw [Real.norm_eq_abs]
      exact hbdd _ _ (slabTime p).property)

@[simp]
private theorem logSpotVolBCF_apply (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (p : slab (E := ℝ) t₀ t₁) :
    logSpotVolBCF hα₀ σ hbdd hσ p =
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p) :=
  congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _) p

/-- The log-spot half-variance field `a(y, t) = σ(e^y, t)² / 2` as an element of
`HolderSpace α (slab t₀ t₁) ℝ`, built from a bounded parabolically `α`-Hölder volatility
(`0 < α`). -/
def logSpotHalfVarianceHolder (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  have hcoe : (logSpotVolBCF hα₀ σ hbdd hσ : slab (E := ℝ) t₀ t₁ → ℝ) =
      fun p : slab (E := ℝ) t₀ t₁ ↦
        σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p) :=
    funext (logSpotVolBCF_apply hα₀ σ hbdd hσ)
  halfSqVolatility (HolderSpace.ofBoundedContinuousFunction (logSpotVolBCF hα₀ σ hbdd hσ)
    (hcoe.symm ▸ hσ))

/-- Evaluation of `logSpotHalfVarianceHolder` at a slab point gives `σ(e^y, t)² / 2`. -/
@[simp]
theorem logSpotHalfVarianceHolder_apply (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (p : slab (E := ℝ) t₀ t₁) :
    logSpotHalfVarianceHolder hα₀ σ hbdd hσ p =
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p) ^ 2 / 2 := by
  simp only [logSpotHalfVarianceHolder, halfSqVolatility_apply,
    HolderSpace.ofBoundedContinuousFunction_apply, logSpotVolBCF_apply]

/-- A uniform lower bound `δ ≤ σ(s, t)²` gives the lower bound `δ / 2 ≤ logSpotHalfVarianceHolder`
for the log-spot half-variance field. -/
theorem half_le_logSpotHalfVarianceHolder (hα₀ : 0 < α) {σ : ℝ → ℝ → ℝ} {δ : ℝ} {M : ℝ≥0}
    (hσ_low : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → δ ≤ σ s t ^ 2)
    (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    (hσ : MemHolder α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)))
    (p : slab (E := ℝ) t₀ t₁) :
    δ / 2 ≤ logSpotHalfVarianceHolder hα₀ σ hbdd hσ p := by
  rw [logSpotHalfVarianceHolder_apply]
  exact div_le_div_of_nonneg_right (hσ_low (exp_pos _) (slabTime p).property) zero_le_two

/-- Norm bound for `logSpotHalfVarianceHolder`: if `|σ(e^y, t)| ≤ M` (`0 ≤ M`) and
`(y, t) ↦ σ(e^y, t)` is parabolically `α`-Hölder with constant `H`, then the log-spot half-variance
field `a = σ² / 2` has Hölder-space norm at most `M ^ 2 / 2 + M * H`. -/
theorem norm_logSpotHalfVarianceHolder_le (hα₀ : 0 < α) (σ : ℝ → ℝ → ℝ) {M : ℝ}
    (hM0 : 0 ≤ M) (hbdd : ∀ y, ∀ t ∈ Icc t₀ t₁, |σ (exp y) t| ≤ M)
    {H : ℝ≥0} (hσH : HolderWith H α (fun p : slab (E := ℝ) t₀ t₁ ↦
      σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p))) :
    ‖logSpotHalfVarianceHolder hα₀ σ hbdd hσH.memHolder‖ ≤ M ^ 2 / 2 + M * H := by
  let f : slab (E := ℝ) t₀ t₁ → ℝ := fun p ↦
    σ (exp (p : ParabolicSpaceTime ℝ).space) (slabTime p)
  have hpoint : ∀ p : slab (E := ℝ) t₀ t₁,
      ‖logSpotHalfVarianceHolder hα₀ σ hbdd hσH.memHolder p‖ ≤ M ^ 2 / 2 := fun p ↦ by
    rw [logSpotHalfVarianceHolder_apply, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (two_pos : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (hbdd _ _ (slabTime p).property) 2) zero_le_two
  have hmul : HolderWith (‖ContinuousLinearMap.mul ℝ ℝ‖₊ * (M.toNNReal * H + M.toNNReal * H)) α
      (fun p ↦ f p * f p) :=
    (ContinuousLinearMap.mul ℝ ℝ).holderWith_comp₂ hσH hσH
      (fun p ↦ by
        simpa only [f, Real.norm_eq_abs, Real.coe_toNNReal _ hM0] using
          hbdd _ _ (slabTime p).property)
      (fun p ↦ by
        simpa only [f, Real.norm_eq_abs, Real.coe_toNNReal _ hM0] using
          hbdd _ _ (slabTime p).property)
  have hsmul : HolderWith (M.toNNReal * H) α (fun p ↦ (2⁻¹ : ℝ) • (f p * f p)) := by
    refine (hmul.smul (2⁻¹ : ℝ)).mono ?_
    have hB : ‖ContinuousLinearMap.mul ℝ ℝ‖₊ ≤ 1 := by
      exact_mod_cast ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    have hhalf : ‖(2⁻¹ : ℝ)‖₊ = 2⁻¹ := by
      rw [← NNReal.coe_inj, coe_nnNorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      norm_num
    rw [hhalf]
    calc ‖ContinuousLinearMap.mul ℝ ℝ‖₊ * (M.toNNReal * H + M.toNNReal * H) * 2⁻¹
        ≤ 1 * (M.toNNReal * H + M.toNNReal * H) * 2⁻¹ := by gcongr
      _ = M.toNNReal * H := by ring
  have hhold : HolderWith (M.toNNReal * H) α
      (logSpotHalfVarianceHolder hα₀ σ hbdd hσH.memHolder) := by
    have hfun : (⇑(logSpotHalfVarianceHolder hα₀ σ hbdd hσH.memHolder)) =
        fun p ↦ (2⁻¹ : ℝ) • (f p * f p) :=
      funext fun p ↦ by rw [logSpotHalfVarianceHolder_apply, smul_eq_mul]; ring
    simpa only [hfun] using hsmul
  simpa only [NNReal.coe_mul, Real.coe_toNNReal _ hM0] using
    HolderSpace.norm_le_of_norm_le_of_holderWith (by positivity) hpoint hhold

/-! ### Classical spot-coordinate solutions and uniqueness -/

section SolutionSpotPDE
variable {hα₀ : 0 < α} {hα₁ : α < 1} {a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p}

/-- The reconstructed price of `weightedLogSpotTerminalSolutionL` solves the spot pricing PDE on
`(0, ∞) × [t₀, t₁]` with time derivative within `[t₀, t₁]`. -/
theorem pde_weightedLogSpotPrice_weightedLogSpotTerminalSolutionL (g : CkHolderSpace 2 α ℝ ℝ)
    {s : ℝ} (hs : 0 < s) (t : Icc t₀ t₁) :
    derivWithin (weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) s)
          (Icc t₀ t₁) t +
        a (slabMk (log s) t) * s ^ 2 * deriv (deriv fun x ↦ weightedLogSpotPrice
          (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) x t) s +
        r (slabMk (log s) t) * (s * deriv (fun x ↦ weightedLogSpotPrice
          (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) x t) s -
          weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) s t) = 0 := by
  rw [pde_weightedLogSpotPrice_eq_mul_weightedLogSpotPricingOperatorL hα₁.le _ hs t,
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL, HolderSpace.zero_apply,
    mul_zero]

/-- Pre-maturity (`t ∈ [t₀, t₁)`) version of
`pde_weightedLogSpotPrice_weightedLogSpotTerminalSolutionL`, with time derivative within
`[t₀, ∞)`. -/
theorem pde_weightedLogSpotPrice_Ici_weightedLogSpotTerminalSolutionL (g : CkHolderSpace 2 α ℝ ℝ)
    {s t : ℝ} (hs : 0 < s) (ht' : t ∈ Ico t₀ t₁) :
    derivWithin (weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) s)
          (Ici t₀) t +
        a (slabMk (log s) ⟨t, Ico_subset_Icc_self ht'⟩) * s ^ 2 *
          deriv (deriv fun x ↦ weightedLogSpotPrice
            (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) x t) s +
        r (slabMk (log s) ⟨t, Ico_subset_Icc_self ht'⟩) *
          (s * deriv (fun x ↦ weightedLogSpotPrice
            (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) x t) s -
            weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) s t) =
      0 := by
  rw [pde_weightedLogSpotPrice_Ici_eq_mul_weightedLogSpotPricingOperatorL hα₁.le _ hs ht',
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL, HolderSpace.zero_apply,
    mul_zero]

/-- Open-horizon (`t ∈ (t₀, t₁)`) version of
`pde_weightedLogSpotPrice_weightedLogSpotTerminalSolutionL`, with ordinary time derivative. -/
theorem pde_weightedLogSpotPrice_Ioo_weightedLogSpotTerminalSolutionL (g : CkHolderSpace 2 α ℝ ℝ)
    {s t : ℝ} (hs : 0 < s) (ht' : t ∈ Ioo t₀ t₁) :
    deriv (weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) s) t +
        a (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) * s ^ 2 *
          deriv (deriv fun x ↦ weightedLogSpotPrice
            (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) x t) s +
        r (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht'⟩) *
          (s * deriv (fun x ↦ weightedLogSpotPrice
            (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) x t) s -
            weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) s t) =
      0 := by
  rw [pde_weightedLogSpotPrice_Ioo_eq_mul_weightedLogSpotPricingOperatorL hα₁.le _ hs ht',
    weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL, HolderSpace.zero_apply,
    mul_zero]

/-- Discounted linear-growth bound on `weightedLogSpotPrice (weightedLogSpotTerminalSolutionL ...)`
when `r ≥ -γ` with `0 ≤ γ` and `|g y| ≤ M`. -/
theorem abs_weightedLogSpotPrice_weightedLogSpotTerminalSolutionL_le_exp_mul_mul
    {γ M : ℝ} (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ) {g : CkHolderSpace 2 α ℝ ℝ}
    (hg : ∀ y, |g y| ≤ M) {s : ℝ} (hs : 0 ≤ s) (t : Icc t₀ t₁) :
    |weightedLogSpotPrice (weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a r ha g) s t| ≤
      exp (γ * (t₁ - t)) * M * (1 + s) := by
  rw [weightedLogSpotPrice_of_mem, abs_mul, abs_of_pos (by positivity : 0 < 1 + s), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (by simpa using abs_weightedLogSpotTerminalSolutionL_le_exp_mul hr hγ hg (slabMk (log s) t))
    (by positivity)
end SolutionSpotPDE

/-- **Existence of classical linear-growth prices under log-spot coefficient regularity.** For
`0 < α < 1`, `t₀ < t₁`, `0 < δ ≤ σ(s, t)² ≤ Λ`, log-spot `α`-Hölder / time `(α / 2)`-Hölder `σ`,
time `(α / 2)`-Hölder `r`, and payoff `h` with `y ↦ h(e^y) / (1 + e^y)` equal to `g ∈ C_b^{2,α}`,
there exists `u ∈ C_b^{2+α,1+α/2}` with terminal trace `g` whose price `weightedLogSpotPrice u`
equals `h` at `t₁` and solves the spot PDE in all three time-derivative conventions. -/
theorem exists_weightedLogSpotPrice_terminal_and_pde (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    {δ Λ : ℝ} (hδ : 0 < δ) {K Hσ Hr : ℝ≥0} {σ : ℝ → ℝ → ℝ} {r h : ℝ → ℝ}
    {g : CkHolderSpace 2 α ℝ ℝ}
    (hσ_bounds : ∀ s > 0, ∀ t ∈ Icc t₀ t₁, δ ≤ σ s t ^ 2 ∧ σ s t ^ 2 ≤ Λ)
    (hσ_space : ∀ t ∈ Icc t₀ t₁, HolderWith K α (fun y ↦ σ (exp y) t))
    (hσ_hold : ∀ y, HolderOnWith Hσ (α / 2) (fun t ↦ σ (exp y) t) (Icc t₀ t₁))
    (hr_hold : HolderOnWith Hr (α / 2) r (Icc t₀ t₁))
    (hg : ∀ y, g y = h (exp y) / (1 + exp y)) :
    ∃ u : ParabolicC2HolderSpace α ℝ ℝ ht,
      (∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = g y) ∧
      (∀ s > 0, weightedLogSpotPrice u s t₁ = h s) ∧
      (∀ s > 0, ∀ t ∈ Icc t₀ t₁, derivWithin (weightedLogSpotPrice u s) (Icc t₀ t₁) t +
          σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
          r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
            weightedLogSpotPrice u s t) = 0) ∧
      (∀ s > 0, ∀ t ∈ Ico t₀ t₁, derivWithin (weightedLogSpotPrice u s) (Ici t₀) t +
          σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
          r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
            weightedLogSpotPrice u s t) = 0) ∧
      (∀ s > 0, ∀ t ∈ Ioo t₀ t₁, deriv (weightedLogSpotPrice u s) t +
          σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
          r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s -
            weightedLogSpotPrice u s t) = 0) := by
  let M : ℝ≥0 := ⟨√Λ, sqrt_nonneg Λ⟩
  have hM (y t : ℝ) (ht' : t ∈ Icc t₀ t₁) : ‖σ (exp y) t‖ ≤ M := by
    rw [Real.norm_eq_abs]
    exact abs_le_sqrt (hσ_bounds (exp y) (exp_pos y) t ht').2
  let σH := HolderSpace.ofHolderSpaceTime hα₀ (f := fun y t ↦ σ (exp y) t) hM hσ_space hσ_hold
  let a := halfSqVolatility σH
  let rH := HolderSpace.ofHolderTime (E := ℝ) hα₀ hr_hold
  have ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ a p :=
    ⟨δ / 2, half_pos hδ, div_le_halfSqVolatility_of_le_sq fun p ↦ by
      simpa [σH] using (hσ_bounds _ (exp_pos _) _ (slabTime p).property).1⟩
  have ha_eval {s t : ℝ} (hs : 0 < s) (ht' : t ∈ Icc t₀ t₁) :
      a (slabMk (log s) ⟨t, ht'⟩) * s ^ 2 = σ s t ^ 2 * s ^ 2 / 2 := by
    simp only [a, σH, halfSqVolatility_apply, HolderSpace.ofHolderSpaceTime_apply,
      space_slabMk, slabTime_slabMk, exp_log hs, div_mul_eq_mul_div]
  have hr_eval {s t : ℝ} (ht' : t ∈ Icc t₀ t₁) : rH (slabMk (log s) ⟨t, ht'⟩) = r t := by
    simp only [rH, HolderSpace.ofHolderTime_apply, slabTime_slabMk]
  refine ⟨weightedLogSpotTerminalSolutionL hα₀ hα₁ ht a rH ha g,
    weightedLogSpotTerminalSolutionL_slabMk_right g,
    fun s hs ↦ weightedLogSpotPrice_terminal _
      (fun y ↦ by rw [weightedLogSpotTerminalSolutionL_slabMk_right, hg]) hs,
    fun s hs t ht' ↦ ?_, fun s hs t ht' ↦ ?_, fun s hs t ht' ↦ ?_⟩
  · have h := pde_weightedLogSpotPrice_weightedLogSpotTerminalSolutionL
      (ht := ht) (hα₀ := hα₀) (hα₁ := hα₁) (a := a) (r := rH) (ha := ha) g hs ⟨t, ht'⟩
    rwa [ha_eval hs ht', hr_eval ht'] at h
  · have h := pde_weightedLogSpotPrice_Ici_weightedLogSpotTerminalSolutionL
      (ht := ht) (hα₀ := hα₀) (hα₁ := hα₁) (a := a) (r := rH) (ha := ha) g hs ht'
    rwa [ha_eval hs (Ico_subset_Icc_self ht'), hr_eval (Ico_subset_Icc_self ht')] at h
  · have h := pde_weightedLogSpotPrice_Ioo_weightedLogSpotTerminalSolutionL
      (ht := ht) (hα₀ := hα₀) (hα₁ := hα₁) (a := a) (r := rH) (ha := ha) g hs ht'
    rwa [ha_eval hs (Ioo_subset_Icc_self ht'), hr_eval (Ioo_subset_Icc_self ht')] at h

/-- **Uniqueness of the reconstructed spot price in the classical linear-growth class.** On
`[t₀, t₁]` (`t₀ < t₁`), for bounded `σ² ≤ Λ` and `|r| ≤ R` on `(t₀, t₁)`, any classical function
`C` with `|C(s, t)| ≤ A (1 + s)` having the same pricing operator on `(0, ∞) × (t₀, t₁)` and the
same terminal value at `t₁` on `(0, ∞)` as `weightedLogSpotPrice u` equals it on
`(0, ∞) × [t₀, t₁]`. -/
theorem eq_weightedLogSpotPrice_of_pde_of_terminal {Λ R A : ℝ} {σ : ℝ → ℝ → ℝ} {r : ℝ → ℝ}
    (u : ParabolicC2HolderSpace α ℝ ℝ ht) {C : ℝ → ℝ → ℝ}
    (hσ : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → σ s t ^ 2 ≤ Λ)
    (hr : ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → |r t| ≤ R)
    (hC_cont : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Icc t₀ t₁))
    (hC_growth : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → |C s t| ≤ A * (1 + s))
    (hC_cd : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → ContDiffAt ℝ 2 (fun x ↦ C x t) s)
    (hC_diff : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ → DifferentiableAt ℝ (fun τ ↦ C s τ) t)
    (hpde : ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Ioo t₀ t₁ →
      deriv (fun τ ↦ C s τ) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
          r t * (s * deriv (fun x ↦ C x t) s - C s t) =
        deriv (weightedLogSpotPrice u s) t +
          σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ weightedLogSpotPrice u x t) s +
          r t * (s * deriv (fun x ↦ weightedLogSpotPrice u x t) s - weightedLogSpotPrice u s t))
    (hterm : ∀ ⦃s⦄, 0 < s → C s t₁ = weightedLogSpotPrice u s t₁) :
    ∀ ⦃s⦄, 0 < s → ∀ ⦃t⦄, t ∈ Icc t₀ t₁ → C s t = weightedLogSpotPrice u s t :=
  eq_of_pde_eq_of_terminal_eq (A := |A| + ‖u‖) hσ hr hC_cont
    ((continuousOn_weightedLogSpotPrice u).mono (prod_mono_right (subset_univ _)))
    (fun x hx τ hτ ↦ by
      have := (hC_growth hx hτ).trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
      linarith [abs_weightedLogSpotPrice_le u hx.le τ,
        abs_sub (C x τ) (weightedLogSpotPrice u x τ)])
    hC_cd (fun _ hx _ hτ ↦ (contDiffOn_weightedLogSpotPrice u
      ⟨_, Ioo_subset_Icc_self hτ⟩).contDiffAt (Ioi_mem_nhds hx))
    hC_diff (fun x _ _ hτ ↦ differentiableAt_weightedLogSpotPrice_time u x hτ) hpde hterm

/-! ### Market price profile under joint parabolic Hölder volatility -/

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
  weightedLogSpotTerminalSolutionL hα₀ hα₁ ht
    (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (HolderSpace.ofHolderTime hα₀ hr_hol)
    ⟨δ / 2, half_pos hδ, half_le_logSpotHalfVarianceHolder hα₀ hσ_low hσ_bdd hσ_hol⟩ g

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
  weightedLogSpotTerminalSolutionL hα₀ hα₁ ht
    (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (HolderSpace.ofHolderTime hα₀ hr_hol)
    ⟨δ / 2, half_pos hδ, half_le_logSpotHalfVarianceHolder hα₀ hσ_low hσ_bdd hσ_hol⟩

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
        (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (HolderSpace.ofHolderTime hα₀ hr_hol)
        ⟨δ / 2, half_pos hδ,
          half_le_logSpotHalfVarianceHolder hα₀ hσ_low hσ_bdd hσ_hol⟩).symm (0, g) :=
  weightedLogSpotTerminalSolutionL_apply g

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
        (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (HolderSpace.ofHolderTime hα₀ hr_hol)
        (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) = 0 :=
  weightedLogSpotPricingOperatorL_weightedLogSpotTerminalSolutionL g

/-- The terminal spatial trace of `marketPriceProfile` at `t₁` is `g`. -/
@[simp]
theorem spatialTrace_marketPriceProfile :
    (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = g :=
  spatialTrace_weightedLogSpotTerminalSolutionL g

/-- At time `t₁`, `marketPriceProfile` evaluates to `g y` at `(y, t₁)`. -/
@[simp]
theorem marketPriceProfile_apply_slabMk_right (y : ℝ) :
    marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g
      (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) = g y :=
  weightedLogSpotTerminalSolutionL_slabMk_right g y

/-- **Uniqueness for `marketPriceProfile`.** Any weighted profile `u ∈ C_b^{2+α,1+α/2}` with
zero weighted pricing residual and terminal trace `g` at `t₁` equals `marketPriceProfile ... g`. -/
theorem eq_marketPriceProfile {u : ParabolicC2HolderSpace α ℝ ℝ ht}
    (hu_pde : weightedLogSpotPricingOperatorL hα₁.le
      (logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol) (HolderSpace.ofHolderTime hα₀ hr_hol) u = 0)
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
  weightedLogSpotPrice_terminal _
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
  have h := pde_weightedLogSpotPrice_weightedLogSpotTerminalSolutionL
    (ht := ht) (hα₀ := hα₀) (hα₁ := hα₁)
    (a := logSpotHalfVarianceHolder hα₀ σ hσ_bdd hσ_hol)
    (r := HolderSpace.ofHolderTime hα₀ hr_hol)
    (ha := ⟨δ / 2, half_pos hδ, half_le_logSpotHalfVarianceHolder hα₀ hσ_low hσ_bdd hσ_hol⟩)
    g hs ⟨t, ht'⟩
  dsimp only [marketPriceProfile]
  simpa only [logSpotHalfVarianceHolder_apply, HolderSpace.ofHolderTime_apply,
    space_slabMk, exp_log hs, slabTime_slabMk, div_mul_eq_mul_div] using h

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
        (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g) s t := by
  let rH := HolderSpace.ofHolderTime (E := ℝ) hα₀ hr_hol
  refine eq_weightedLogSpotPrice_of_pde_of_terminal (Λ := (M : ℝ) ^ 2) (R := ‖rH‖)
    (σ := σ) (r := r) (marketPriceProfile hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol hr_hol g)
    (fun s hs t ht' ↦ by
      rw [← exp_log hs]
      exact sq_le_sq' (abs_le.1 (hσ_bdd (log s) t (Ioo_subset_Icc_self ht'))).1
        (abs_le.1 (hσ_bdd (log s) t (Ioo_subset_Icc_self ht'))).2)
    (fun t ht' ↦ by
      have hrt : r t = rH (slabMk 0 ⟨t, Ioo_subset_Icc_self ht'⟩) := by simp [rH]
      rw [hrt, ← Real.norm_eq_abs]
      exact rH.norm_apply_le _)
    hC_cont hC_growth hC_cd hC_diff
    (fun s hs t ht' ↦ by
      rw [hC_pde hs ht',
        pde_weightedLogSpotPrice_marketPriceProfile_of_mem_Ioo hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol
          hr_hol g hs ht'])
    (fun s hs ↦ by
      rw [hC_term hs,
        weightedLogSpotPrice_marketPriceProfile_terminal hα₀ hα₁ ht hδ hσ_low hσ_bdd hσ_hol
          hr_hol g hg hs])

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
    (continuousOn_deriv_weightedLogSpotPrice_spot _).mono (prod_mono_right (subset_univ _)),
    (continuousOn_deriv_deriv_weightedLogSpotPrice_spot _).mono (prod_mono_right (subset_univ _)),
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
    fun _ hs t _ ↦ abs_weightedLogSpotPrice_add_abs_mul_deriv_le _ hs.le t,
    fun _ _ hCc hCg hCcd hCd hCpde hCt ↦
      eq_weightedLogSpotPrice_marketPriceProfile_of_pde_eq_zero_of_terminal_eq hα₀ hα₁ ht hδ hσ_low
        hσ_bdd hσ_hol hr_hol g hg _ hCc hCg hCcd hCd hCpde hCt⟩

end MarketPriceProfile

end TauCeti.Finance
