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
    weightedLogSpotSecondOrderCoeff_def, ← weightedLogSpotPricingOperatorL_def]

@[simp] theorem weightedLogSpotPricingOperatorL_weightedLogSpotTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    weightedLogSpotPricingOperatorL hα₁.le a r
      ((weightedLogSpotTerminalDataCLE hα₀ hα₁ ht a r ha).symm d) = d.1 := by
  rw [weightedLogSpotTerminalDataCLE, weightedLogSpotPricingOperatorL_def,
    ← weightedLogSpotSecondOrderCoeff_def,
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

end TerminalDataEval

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

end TauCeti.Finance
