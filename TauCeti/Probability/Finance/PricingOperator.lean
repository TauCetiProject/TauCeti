/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Weight
public import TauCeti.Analysis.PDE.Parabolic.Holder.Backward
import TauCeti.Probability.Finance.LogSpot
import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeLine

/-!
# The weighted log-spot pricing operator on parabolic Hölder spaces

Write `a = σ² / 2`, and let `r` be the short rate. In log-spot coordinates the pricing
operator is `∂ₜ + a ∂ᵧ² + (r - a) ∂ᵧ - r`. Conjugating by the weight `1 + exp y`
turns prices of linear growth in the spot into bounded functions. This file constructs
its coefficients as bounded parabolic Hölder fields and the resulting operator as a
continuous linear map on `ParabolicC2HolderSpace`:

`∂ₜ + a ∂ᵧ² + (r + a (2 sigmoid y - 1)) ∂ᵧ - r (1 - sigmoid y)`.

The second-order coefficient is unchanged, so a positive lower bound for `a` is preserved.
The construction needs no ellipticity or sign assumption. Both `a` and `r` may be parabolic
Hölder fields, although the financial short rate is normally independent of space. The
coefficient formulas and operator identity hold on the closed time slab, using within
derivatives at its endpoints.

The construction and conjugation identity use
`ParabolicC2HolderSpace.weightFirstOrderCoeff` and
`ParabolicC2HolderSpace.weightZerothOrderCoeff`, with the gradient and Hessian of
`log (1 + exp y)`. The zeroth-order coefficient simplifies to an expression independent
of `a`. Identification with the spot pricing equation uses `TauCeti.Finance.pde_comp_exp`.

## The terminal-value problem

For `a ≥ 0` the operator is degenerate parabolic, and the terminal-value problem
`P u = g`, `u(·, t₁) = h` has at most one solution in `C_b^{2+α,1+α/2}`
(`TauCeti.Finance.eq_of_weightedLogSpotPricingOperatorL_eq`): the terminal-data map
`u ↦ (P u, u(·, t₁))` is injective
(`TauCeti.Finance.injective_weightedLogSpotPricingOperatorL_prod_spatialTraceL`). Quantitatively,
if the rate is bounded below, `r ≥ -γ` with `0 ≤ γ`, then

`|u(y, t)| ≤ exp (γ (t₁ - t)) (sup |u(·, t₁)| + (t₁ - t) sup |P u|)`

(`TauCeti.Finance.abs_le_exp_mul_mul_add_mul_of_abs_weightedLogSpotPricingOperatorL_le`). This is
the supremum bound that turns a Schauder estimate with a lower-order term `‖u‖_∞` on its right
side into an a priori estimate in terms of `P u` and the terminal trace alone. Only the lower
bound on `r` enters: the zeroth-order coefficient `-r (1 - sigmoid y)` is then at most `γ`,
since `0 < 1 - sigmoid y < 1`. For a nonnegative short rate the bound holds with `γ = 0`.

The proof reads `u` backward from `t₁` and compares it on the whole line with the barrier
`exp (γ τ) (M + τ K)` in the remaining time `τ`, by the comparison principle
`TauCeti.PDE.le_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_le_of_le_initial`. Its growth
conditions hold because the weighted coefficients are bounded. For a price
`C(s, t) = (1 + s) u(log s, t)` the statements transfer through
`TauCeti.Finance.weightedLogSpotPricingOperatorL_eq_spot`; in spot coordinates, uniqueness among
all prices of linear growth is `TauCeti.Finance.eq_of_pde_eq_of_terminal_eq`.

## References

* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*,
  Cambridge University Press, 1995, §5.4.
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964,
  Chapter 2, Section 4.
-/

public section
noncomputable section

namespace TauCeti.Finance

open Set Real Filter Topology ParabolicSpaceTime ContinuousLinearMap
open ParabolicC2HolderSpace
open scoped NNReal

variable {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁}

-- These shortcuts keep instance search shallow for the nested coefficient spaces.
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance

/-- The first-order coefficient of the weighted log-spot pricing operator, acting on a
spatial gradient by multiplication by `r + a (2 sigmoid y - 1)`. -/
def weightedLogSpotFirstOrderCoeff (hα : α ≤ 1)
    (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  weightFirstOrderCoeff
    ((lsmul ℝ ℝ).compHolder₂ a (HolderSpace.const ((apply ℝ ℝ 1).comp (apply ℝ _ 1))))
    ((lsmul ℝ ℝ).compHolder₂ (r - a) (HolderSpace.const (apply ℝ ℝ 1)))
    (logOneAddExpGrad hα)

/-- The zeroth-order coefficient of the weighted log-spot pricing operator, acting by
multiplication by `-r (1 - sigmoid y)`. -/
def weightedLogSpotZerothOrderCoeff (hα : α ≤ 1)
    (r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ) :=
  (lsmul ℝ ℝ).compHolder₂ (-r)
    (HolderSpace.const (ContinuousLinearMap.id ℝ ℝ) -
      HolderSpace.compSlabSpaceL (logOneAddExpGrad hα))

variable (hα : α ≤ 1) (a r : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ)

@[simp]
theorem weightedLogSpotFirstOrderCoeff_apply (p : slab (E := ℝ) t₀ t₁)
    (D : ℝ →L[ℝ] ℝ) :
    weightedLogSpotFirstOrderCoeff hα a r p D =
      (r p + a p * (2 * sigmoid (p : ParabolicSpaceTime ℝ).space - 1)) * D 1 := by
  simp [weightedLogSpotFirstOrderCoeff, weightFirstOrderCoeff_apply]
  ring

@[simp]
theorem weightedLogSpotZerothOrderCoeff_apply (p : slab (E := ℝ) t₀ t₁) (v : ℝ) :
    weightedLogSpotZerothOrderCoeff hα r p v =
      -(r p * (1 - sigmoid (p : ParabolicSpaceTime ℝ).space)) * v := by
  simp [weightedLogSpotZerothOrderCoeff]
  ring

/-- The backward pricing operator after division by `1 + exp y`, as a bounded linear
map from bounded order-two parabolic Hölder functions to parabolic Hölder functions. -/
def weightedLogSpotPricingOperatorL :
    ParabolicC2HolderSpace α ℝ ℝ ht →L[ℝ] HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ :=
  backwardParabolicOperatorL (F := ℝ) hα
    ((lsmul ℝ ℝ).compHolder₂ a (HolderSpace.const ((apply ℝ ℝ 1).comp (apply ℝ _ 1))))
    (weightedLogSpotFirstOrderCoeff hα a r) (weightedLogSpotZerothOrderCoeff hα r)

/-- Evaluation of the bounded operator in terms of its derivative fields. -/
@[simp]
theorem weightedLogSpotPricingOperatorL_apply (v : ParabolicC2HolderSpace α ℝ ℝ ht)
    (p : slab (E := ℝ) t₀ t₁) :
    weightedLogSpotPricingOperatorL hα a r v p = timeDerivL v p +
      (a p * spatialSecondFDerivL v p 1 1 +
        (r p + a p * (2 * sigmoid (p : ParabolicSpaceTime ℝ).space - 1)) *
          spatialFDerivL v p 1 -
        r p * (1 - sigmoid (p : ParabolicSpaceTime ℝ).space) * v p) := by
  simp [weightedLogSpotPricingOperatorL, sub_eq_add_neg]

/-- The bounded weighted operator is the classical backward log-spot pricing operator
on `(1 + exp y) v`, divided by the weight. Within time derivatives include the endpoints. -/
theorem one_add_exp_mul_weightedLogSpotPricingOperatorL
    (v : ParabolicC2HolderSpace α ℝ ℝ ht) (x : ℝ) (t : Icc t₀ t₁) :
    (1 + exp x) * weightedLogSpotPricingOperatorL hα a r v (slabMk x t) =
      derivWithin (fun s ↦ (1 + exp x) * timeExtension ht.le v x s) (Icc t₀ t₁) t +
        (a (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦
            (1 + exp y) * v (slabMk y t)) x 1 1 +
          (r (slabMk x t) - a (slabMk x t)) *
            fderiv ℝ (fun y ↦ (1 + exp y) * v (slabMk y t)) x 1 -
          r (slabMk x t) * ((1 + exp x) * v (slabMk x t))) := by
  have h := one_add_exp_smul_parabolicOperatorL_weightCoeff hα
    (A := (lsmul ℝ ℝ).compHolder₂ a
      (HolderSpace.const ((apply ℝ ℝ 1).comp (apply ℝ _ 1))))
    (B := (lsmul ℝ ℝ).compHolder₂ (r - a) (HolderSpace.const (apply ℝ ℝ 1)))
    (C := (lsmul ℝ ℝ).compHolder₂ (-r)
      (HolderSpace.const (ContinuousLinearMap.id ℝ ℝ))) v
    (u := fun p ↦ (1 + exp (p : ParabolicSpaceTime ℝ).space) * v p)
    (fun _ ↦ rfl) x t
  have htime : timeExtension ht.le
      (fun p ↦ (1 + exp (p : ParabolicSpaceTime ℝ).space) * v p) x =
      fun s ↦ (1 + exp x) * timeExtension ht.le v x s := by
    ext s
    simp [timeExtension_def]
  simp only [smul_eq_mul, htime] at h
  have hw := weightedLogSpotPricingOperatorL_apply hα a r v (slabMk x t)
  simp only [space_slabMk] at hw
  have hd := ((v.hasTimeDerivWithinAt x t).const_mul (1 + exp x)).derivWithin
    (uniqueDiffOn_Icc ht t t.2)
  simp [parabolicOperatorL_apply, weightFirstOrderCoeff_apply,
    weightZerothOrderCoeff_apply, space_slabMk] at h
  rw [hw]
  simp only [fderiv_apply_one_eq_deriv]
  -- The supplier uses the forward sign. Negate its identity and add twice the time identity.
  linear_combination -h - 2 * hd

/-- For a price `C` represented by the bounded weighted function `v`, the constructed
operator is the spot pricing equation divided by `1 + exp x`. The local volatility is
specified only through `a = σ² / 2` at the point in question. -/
theorem weightedLogSpotPricingOperatorL_eq_spot
    (v : ParabolicC2HolderSpace α ℝ ℝ ht) {C : ℝ → ℝ → ℝ}
    (hC : ∀ y (s : Icc t₀ t₁), C (exp y) s = (1 + exp y) * v (slabMk y s))
    (x : ℝ) (t : Icc t₀ t₁) (σ : ℝ) (ha : a (slabMk x t) = σ ^ 2 / 2)
    (hCs : ∀ᶠ s in 𝓝 (exp x), DifferentiableAt ℝ (fun s ↦ C s t) s)
    (hCss : DifferentiableAt ℝ (deriv fun s ↦ C s t) (exp x))
    (hCt : DifferentiableAt ℝ (C (exp x)) t) :
    weightedLogSpotPricingOperatorL hα a r v (slabMk x t) =
      (deriv (C (exp x)) t +
        σ ^ 2 * exp x ^ 2 / 2 * deriv (deriv fun s ↦ C s t) (exp x) +
        r (slabMk x t) * (exp x * deriv (fun s ↦ C s t) (exp x) - C (exp x) t)) /
      (1 + exp x) := by
  have hw := one_add_exp_mul_weightedLogSpotPricingOperatorL hα a r v x t
  have hs : (fun y ↦ (1 + exp y) * v (slabMk y t)) = fun y ↦ C (exp y) t :=
    funext fun y ↦ (hC y t).symm
  have htime : derivWithin (fun s ↦ (1 + exp x) * timeExtension ht.le v x s)
      (Icc t₀ t₁) t = deriv (C (exp x)) t := by
    rw [derivWithin_congr (f := C (exp x))
      (fun s hs ↦ by
        rw [timeExtension_of_mem ht.le v x ⟨s, hs⟩]
        exact (hC x ⟨s, hs⟩).symm)
      (by rw [timeExtension_of_mem ht.le v x t]; exact (hC x t).symm)]
    exact hCt.derivWithin (uniqueDiffOn_Icc ht t t.2)
  have hsecond : fderiv ℝ (fderiv ℝ fun y ↦ C (exp y) t) x 1 1 =
      deriv (deriv fun y ↦ C (exp y) t) x := by
    simpa [_root_.iteratedFDeriv_two_apply, iteratedDeriv_succ, iteratedDeriv_one] using
      (iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod (𝕜 := ℝ) (n := 2)
        (f := fun y ↦ C (exp y) t) (x := x) (m := fun _ ↦ 1))
  rw [hs, htime, ha, hsecond, fderiv_apply_one_eq_deriv, ← hC x t] at hw
  have hpde := pde_comp_exp σ (r (slabMk x t)) hCs hCss
  apply (eq_div_iff (by positivity : 1 + exp x ≠ 0)).2
  linear_combination hw + hpde

/-! ### The a priori bound and uniqueness for the terminal-value problem -/

section TerminalValue

variable {a r}

/-- At an interior remaining time `τ`, the slice through `y` read backward from `t₁` has the
negated recorded time derivative as its ordinary derivative. -/
private theorem hasDerivAt_reverse (u : ParabolicC2HolderSpace α ℝ ℝ ht) (y : ℝ) {τ : ℝ}
    (h : τ ∈ Ioo 0 (t₁ - t₀)) :
    HasDerivAt (fun σ ↦ u (slabMk y (projIcc t₀ t₁ ht.le (t₁ - σ))))
      (-timeDerivL u (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ)))) τ := by
  have hτ : ((projIcc t₀ t₁ ht.le (t₁ - τ) : Icc t₀ t₁) : ℝ) = t₁ - τ :=
    congrArg Subtype.val (projIcc_of_mem ht.le ⟨by linarith [h.2], by linarith [h.1]⟩)
  have hd := (u.hasTimeDerivWithinAt y (projIcc t₀ t₁ ht.le (t₁ - τ))).hasDerivAt
    (Icc_mem_nhds (by rw [hτ]; linarith [h.2]) (by rw [hτ]; linarith [h.1]))
  rw [hτ, timeExtension_def] at hd
  exact (hd.comp τ ((hasDerivAt_id τ).const_sub t₁)).congr_deriv (by simp)

/-- Read backward from `t₁`, the classical forward operator with the weighted coefficients is
the negated weighted pricing operator at the corresponding slab point. -/
private theorem reverse_operator_eq (u : ParabolicC2HolderSpace α ℝ ℝ ht) {τ : ℝ}
    (h : τ ∈ Ioo 0 (t₁ - t₀)) (y : ℝ) :
    deriv (fun σ ↦ u (slabMk y (projIcc t₀ t₁ ht.le (t₁ - σ)))) τ -
      (a (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) *
          deriv (deriv fun z ↦ u (slabMk z (projIcc t₀ t₁ ht.le (t₁ - τ)))) y +
        (r (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) +
            a (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) * (2 * sigmoid y - 1)) *
          deriv (fun z ↦ u (slabMk z (projIcc t₀ t₁ ht.le (t₁ - τ)))) y +
        -(r (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) * (1 - sigmoid y)) *
          u (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ)))) =
      -weightedLogSpotPricingOperatorL hα a r u (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) := by
  have hx : deriv (fun z ↦ u (slabMk z (projIcc t₀ t₁ ht.le (t₁ - τ)))) =
      fun z ↦ spatialFDerivL u (slabMk z (projIcc t₀ t₁ ht.le (t₁ - τ))) 1 :=
    funext (u.deriv_spatialSlice _)
  rw [(hasDerivAt_reverse u y h).deriv, hx, u.deriv_spatialFDerivL_apply,
    weightedLogSpotPricingOperatorL_apply]
  simp only [space_slabMk]
  ring

/-- **The one-sided a priori bound for the weighted terminal-value problem.** Let `a ≥ 0` and
`r ≥ -γ` with `0 ≤ γ`. If `u ∈ C_b^{2+α,1+α/2}` on `ℝ × [t₀, t₁]` satisfies `P u ≥ -K` for the
weighted log-spot pricing operator `P` and `u(·, t₁) ≤ M`, with `0 ≤ M` and `0 ≤ K`, then
`u(y, t) ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`. -/
theorem le_exp_mul_mul_add_mul_of_le_weightedLogSpotPricingOperatorL (ha : ∀ p, 0 ≤ a p)
    {γ : ℝ} (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (u : ParabolicC2HolderSpace α ℝ ℝ ht)
    (hP : ∀ p, -K ≤ weightedLogSpotPricingOperatorL hα a r u p)
    (hterm : ∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) ≤ M)
    (p : slab (E := ℝ) t₀ t₁) :
    u p ≤ Real.exp (γ * (t₁ - slabTime p)) * (M + (t₁ - slabTime p) * K) := by
  -- Read `u` backward from `t₁` and compare it on the whole line with the barrier
  -- `exp (γ τ) (M + τ K)` in the remaining time `τ`.
  have hcont : Continuous fun z : ℝ × ℝ ↦ u (slabMk z.2 (projIcc t₀ t₁ ht.le (t₁ - z.1))) :=
    (valueL u).continuous.comp (continuous_slabMk.comp (continuous_snd.prodMk
      ((continuous_projIcc (h := ht.le)).comp (continuous_const.sub continuous_fst))))
  have hbar (τ : ℝ) : HasDerivAt (fun σ ↦ Real.exp (γ * σ) * (M + σ * K))
      (γ * Real.exp (γ * τ) * (M + τ * K) + Real.exp (γ * τ) * K) τ := by
    have h := (((hasDerivAt_id τ).const_mul γ).exp).mul
      (((hasDerivAt_id τ).mul_const K).const_add M)
    simp only [id, mul_one, one_mul] at h
    convert h using 1
    ring
  have key := PDE.le_of_deriv_sub_mul_deriv_deriv_add_mul_deriv_add_mul_le_of_le_initial
    (u := fun τ y ↦ u (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))))
    (v := fun τ _ ↦ Real.exp (γ * τ) * (M + τ * K))
    (a := fun τ y ↦ a (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))))
    (b := fun τ y ↦ r (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) +
      a (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) * (2 * sigmoid y - 1))
    (c := fun τ y ↦ -(r (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) * (1 - sigmoid y)))
    (T := t₁ - t₀) (Lam := ‖a‖) (β := ‖r‖ + ‖a‖) (γ := γ)
    -- The weighted coefficients are bounded, and `c = -r (1 - sigmoid y) ≤ γ`.
    (fun τ _ y ↦ ha _)
    (fun τ _ y ↦ (le_abs_self _).trans ((HolderSpace.norm_apply_le a _).trans
      (le_mul_of_one_le_right (norm_nonneg a) (by nlinarith [sq_nonneg y]))))
    (fun τ _ y ↦ by
      have hσ : |2 * sigmoid y - 1| ≤ 1 :=
        abs_le.2 ⟨by linarith [Real.sigmoid_pos y], by linarith [Real.sigmoid_lt_one y]⟩
      calc _ ≤ |r (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ)))| +
              |a (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ)))| * |2 * sigmoid y - 1| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ ‖r‖ + ‖a‖ * 1 := by
            gcongr
            exacts [HolderSpace.norm_apply_le r _, HolderSpace.norm_apply_le a _]
        _ ≤ _ := by nlinarith [abs_nonneg y, norm_nonneg r, norm_nonneg a])
    (fun τ _ y ↦ by
      have h := hr (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ)))
      nlinarith [mul_nonneg (by linarith : 0 ≤ r (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) + γ)
        (by linarith [Real.sigmoid_lt_one y] : 0 ≤ 1 - sigmoid y),
        mul_nonneg hγ (Real.sigmoid_pos y).le])
    -- `u` is bounded and the barrier is nonnegative, so their difference is bounded above.
    hcont.continuousOn (by fun_prop)
    ⟨‖valueL u‖, by
      rintro _ ⟨⟨τ, y⟩, ⟨hτ, -⟩, rfl⟩
      have hu : u (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) ≤ ‖valueL u‖ :=
        (le_abs_self _).trans ((valueL u).norm_coe_le_norm _)
      have hv : 0 ≤ Real.exp (γ * τ) * (M + τ * K) := by
        have := hτ.1
        positivity
      simp only [Function.uncurry_apply_pair, Pi.sub_apply]
      linarith⟩
    (fun τ _ y ↦ (u.contDiff_spatialSlice _).contDiffAt)
    (fun τ _ y ↦ contDiffAt_const)
    (fun τ h y ↦ (hasDerivAt_reverse u y h).differentiableAt)
    (fun τ _ y ↦ (hbar τ).differentiableAt)
    -- The reversed operator of `u` is `-P u ≤ K`, which the barrier's operator dominates.
    (fun τ h y ↦ by
      rw [reverse_operator_eq hα u h y, (hbar τ).deriv]
      simp only [deriv_const', mul_zero, zero_add]
      have hc := hr (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ)))
      have hE : 1 ≤ Real.exp (γ * τ) := Real.one_le_exp (mul_nonneg hγ h.1.le)
      have hMK : 0 ≤ M + τ * K := by nlinarith [h.1]
      have hs := Real.sigmoid_pos y
      have hs' := Real.sigmoid_lt_one y
      have h₁ : 0 ≤ (γ + r (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ))) * (1 - sigmoid y)) *
          (Real.exp (γ * τ) * (M + τ * K)) := by
        refine mul_nonneg ?_ (by positivity)
        nlinarith
      nlinarith [hP (slabMk y (projIcc t₀ t₁ ht.le (t₁ - τ)))])
    -- At `τ = 0` the barrier is `M`, which bounds the terminal trace.
    (fun y ↦ by
      simpa only [sub_zero, projIcc_right, mul_zero, Real.exp_zero, zero_mul, add_zero,
        one_mul] using hterm y)
  have hp : t₁ - slabTime p ∈ Icc 0 (t₁ - t₀) :=
    ⟨by linarith [(slabTime p).2.2], by linarith [(slabTime p).2.1]⟩
  have hτ : projIcc t₀ t₁ ht.le (t₁ - (t₁ - slabTime p)) = slabTime p := by
    rw [sub_sub_cancel, projIcc_val]
  simpa only [hτ, slabMk_space_slabTime] using key hp (p : ParabolicSpaceTime ℝ).space

/-- **The a priori bound for the weighted terminal-value problem.** Let `a ≥ 0` and `r ≥ -γ`
with `0 ≤ γ`. If `u ∈ C_b^{2+α,1+α/2}` on `ℝ × [t₀, t₁]` satisfies `|P u| ≤ K` for the weighted
log-spot pricing operator `P` and `|u(·, t₁)| ≤ M`, then
`|u(y, t)| ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`. -/
theorem abs_le_exp_mul_mul_add_mul_of_abs_weightedLogSpotPricingOperatorL_le
    (ha : ∀ p, 0 ≤ a p) {γ : ℝ} (hr : ∀ p, -γ ≤ r p) (hγ : 0 ≤ γ) {M K : ℝ}
    (u : ParabolicC2HolderSpace α ℝ ℝ ht)
    (hP : ∀ p, |weightedLogSpotPricingOperatorL hα a r u p| ≤ K)
    (hterm : ∀ y, |u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩)| ≤ M)
    (p : slab (E := ℝ) t₀ t₁) :
    |u p| ≤ Real.exp (γ * (t₁ - slabTime p)) * (M + (t₁ - slabTime p) * K) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hterm 0)
  have hK : 0 ≤ K := (abs_nonneg _).trans (hP p)
  -- The lower bound is the upper bound for `-u`.
  have hge := le_exp_mul_mul_add_mul_of_le_weightedLogSpotPricingOperatorL hα ha hr hγ hM hK (-u)
    (fun q ↦ by rw [map_neg, HolderSpace.neg_apply]; exact neg_le_neg (abs_le.1 (hP q)).2)
    (fun y ↦ by rw [ParabolicC2HolderSpace.neg_apply]; exact neg_le.1 (abs_le.1 (hterm y)).1) p
  rw [ParabolicC2HolderSpace.neg_apply] at hge
  exact abs_le.2 ⟨neg_le.1 hge, le_exp_mul_mul_add_mul_of_le_weightedLogSpotPricingOperatorL hα
    ha hr hγ hM hK u (fun q ↦ (abs_le.1 (hP q)).1) (fun y ↦ (abs_le.1 (hterm y)).2) p⟩

/-- **Uniqueness for the weighted terminal-value problem.** For `a ≥ 0`, an element of
`C_b^{2+α,1+α/2}` on `ℝ × [t₀, t₁]` is determined by its image under the weighted log-spot pricing
operator and its terminal trace `u(·, t₁)`. No lower bound on `r` is needed. -/
theorem eq_of_weightedLogSpotPricingOperatorL_eq (ha : ∀ p, 0 ≤ a p)
    {u v : ParabolicC2HolderSpace α ℝ ℝ ht}
    (hP : weightedLogSpotPricingOperatorL hα a r u = weightedLogSpotPricingOperatorL hα a r v)
    (hterm : ∀ y, u (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩) =
      v (slabMk y ⟨t₁, right_mem_Icc.2 ht.le⟩)) :
    u = v := by
  ext p
  have h := abs_le_exp_mul_mul_add_mul_of_abs_weightedLogSpotPricingOperatorL_le hα (r := r) ha
    (fun q ↦ (abs_le.1 ((Real.norm_eq_abs _).symm.trans_le (HolderSpace.norm_apply_le r q))).1)
    (norm_nonneg r) (M := 0) (K := 0) (u - v)
    (fun q ↦ by simp only [map_sub, hP, sub_self, HolderSpace.zero_apply, abs_zero, le_refl])
    (fun y ↦ by simp [hterm]) p
  simpa [ParabolicC2HolderSpace.sub_apply, sub_eq_zero] using h

/-- The terminal-data map `u ↦ (P u, u(·, t₁))` of the weighted log-spot pricing operator `P`
is injective when `a ≥ 0`. -/
theorem injective_weightedLogSpotPricingOperatorL_prod_spatialTraceL (ha : ∀ p, 0 ≤ a p) :
    Function.Injective ((weightedLogSpotPricingOperatorL (ht := ht) hα a r).prod
      (spatialTraceL ⟨t₁, right_mem_Icc.2 ht.le⟩)) := by
  intro u v h
  simp only [ContinuousLinearMap.prod_apply, Prod.mk.injEq] at h
  exact eq_of_weightedLogSpotPricingOperatorL_eq hα ha h.1 fun y ↦ by
    simpa [spatialTraceL_apply, spatialTrace_apply] using
      congrArg (fun f : CkHolderSpace 2 α ℝ ℝ ↦ f y) h.2

end TerminalValue

end TauCeti.Finance
