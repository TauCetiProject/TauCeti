/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Calculus.IteratedGradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.InnerProductSpace.NormPow.Regularized
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Regularization
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Weak derivatives of norm powers

Let `E` be a finite-dimensional real inner product space of dimension `d`. For every real
exponent `s > 1 - d`, the power `x ↦ ‖x‖ ^ s` is weakly differentiable on every open set, with
weak derivative its classical derivative `s ‖x‖ ^ (s - 2) ⟪x, ·⟫` away from the origin.
The condition `s > 1 - d` makes that derivative, whose norm is `|s| ‖x‖ ^ (s - 1)` away from the
origin, locally integrable.

For `s > 0` the power is continuous and the origin is a removable point
(`TauCeti.hasWeakFDerivOn_of_hasFDerivAt_off_countable`). For `s ≤ 0`, where the power is
unbounded near the origin unless `s = 0`, the power is replaced by the smooth regularizations
`(‖x‖ ^ 2 + t) ^ (s / 2)`, whose values and derivatives are dominated by those at `t = 0`, and
dominated convergence passes the integration by parts identity to the limit `t → 0⁺`.

The same regularization gives the second derivatives. For `s > 2 - d` the classical Hessian of
`‖x‖ ^ s` is the weak derivative of its gradient across the origin. For `s ≤ 2` the regularized
gradients `TauCeti.regularizedNormRpowGradient` and their derivatives
`TauCeti.regularizedNormRpowHessian` are dominated, uniformly in `t ≥ 0`, by multiples of
`‖x‖ ^ (s - 1)` and `‖x‖ ^ (s - 2)`, which are locally integrable. So they converge in `L¹` on
balls, and the weak derivative identity passes to the limit
(`TauCeti.hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub`). For `s > 2` the power is `C²`.

This adapts the regularization proof first given for the Newtonian kernel in Tau Ceti's
`TauCeti.integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul`
(`TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/DistributionalLaplacian.lean`), replacing the
exponent `2 - n` by an arbitrary exponent; that theorem is derived from the general one here.

The case `s = 1` shows that if `d ≥ 2`, the coordinates `‖x‖⁻¹ ⟪x, v⟫` of the unit radial field
`x / ‖x‖`, which is the weak gradient of the norm, are weakly differentiable on every open set:
they are the components of the gradient of `‖x‖`, whose Hessian is dominated by `2 ‖x‖⁻¹`.

## Main declarations

* `TauCeti.locallyIntegrable_norm_rpow_smul_innerSL`: the classical derivative is locally
  integrable for `s > 1 - d`.
* `TauCeti.integral_norm_rpow_mul_fderiv_eq_neg`: integration by parts against `‖x‖ ^ s` for
  `1 - d < s ≤ 0`.
* `TauCeti.hasWeakFDerivOn_norm_rpow`, `TauCeti.hasWeakFDerivOn_norm_rpow_innerSL_gradient`: the
  classical derivative is a weak derivative on every open set for `s > 1 - d`.
* `TauCeti.hasWeakFDerivOn_gradient_norm_rpow`: the classical Hessian is the weak derivative of
  the gradient on every open set for `s > 2 - d`.
* `TauCeti.hasWeakFDerivOn_norm_rpow_neg_one_mul_inner`: for `d ≥ 2`, the coordinates of the unit
  radial field are weakly differentiable on every open set, with their classical derivatives.
* `TauCeti.abs_norm_rpow_neg_one_mul_inner_le`,
  `TauCeti.norm_norm_rpow_neg_one_smul_innerSL_sub_le`: the coordinates are bounded by `‖v‖` and
  their derivatives by `2 ‖v‖ ‖x‖⁻¹`.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set Topology TopologicalSpace

open scoped RealInnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : ℝ}

/-- The norm power regularized at scale `t`. -/
private def regPow (s t : ℝ) (x : E) : ℝ :=
  (‖x‖ ^ 2 + t) ^ (s / 2)

/-- The derivative of the regularized norm power in the direction `v`. -/
private def regPowDeriv (s : ℝ) (v : E) (t : ℝ) (x : E) : ℝ :=
  ⟪regularizedNormRpowGradient s t x, v⟫

omit [InnerProductSpace ℝ E] in
private lemma regPow_zero (s : ℝ) (x : E) : regPow s 0 x = ‖x‖ ^ s := by
  rw [regPow, add_zero, Real.sq_rpow_div_two (norm_nonneg x)]

private lemma regPowDeriv_zero (s : ℝ) (v : E) (x : E) :
    regPowDeriv s v 0 x = ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) v := by
  have hs : s / 2 - 1 = (s - 2) / 2 := by ring
  rw [regPowDeriv, regularizedNormRpowGradient_apply, real_inner_smul_left, add_zero, hs,
    Real.sq_rpow_div_two (norm_nonneg x)]
  simp [mul_assoc]

private lemma hasLineDerivAt_regPow [CompleteSpace E] (s : ℝ) (v : E) {t : ℝ} (ht : 0 < t)
    (x : E) : HasLineDerivAt ℝ (regPow s t) (regPowDeriv s v t x) x v := by
  have hpos : 0 < ‖x‖ ^ 2 + t := add_pos_of_nonneg_of_pos (sq_nonneg _) ht
  have h := (hasGradientAt_norm_sq_add_rpow s t hpos.ne').hasFDerivAt.hasLineDerivAt v
  rw [InnerProductSpace.toDual_apply_apply] at h
  exact h

omit [InnerProductSpace ℝ E] in
private lemma continuous_regPow (s : ℝ) {t : ℝ} (ht : 0 < t) : Continuous (regPow (E := E) s t) :=
  continuous_norm_sq_add_rpow ht _

private lemma continuous_regPowDeriv (s : ℝ) (v : E) {t : ℝ} (ht : 0 < t) :
    Continuous (regPowDeriv s v t) :=
  (continuous_regularizedNormRpowGradient s ht).inner continuous_const

private lemma tendsto_regPowDeriv (s : ℝ) (v x : E) :
    Tendsto (fun t ↦ regPowDeriv s v t x) (𝓝[>] 0) (𝓝 (regPowDeriv s v 0 x)) :=
  ((continuousAt_regularizedNormRpowGradient_apply_zero x).tendsto.mono_left
    nhdsWithin_le_nhds).inner tendsto_const_nhds

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- For `s > 1 - dim E`, the classical derivative `s ‖x‖ ^ (s - 2) ⟪x, ·⟫` of `x ↦ ‖x‖ ^ s` away
from the origin is locally integrable. -/
theorem locallyIntegrable_norm_rpow_smul_innerSL
    (hs : 1 - (Module.finrank ℝ E : ℝ) < s) :
    LocallyIntegrable (fun x : E => (s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) μ := by
  have hpow : LocallyIntegrable (fun x : E => ‖x‖ ^ (s - 1)) μ := by
    simpa only [zero_sub, norm_neg] using
      locallyIntegrable_norm_sub_rpow (mu := μ) (s := s - 1) (by linarith) (0 : E)
  have hbound : LocallyIntegrable (fun x : E => |s| * ‖x‖ ^ (s - 1)) μ := hpow.smul |s|
  have hmeas : Measurable fun x : E => (s * ‖x‖ ^ (s - 2)) • innerSL ℝ x :=
    (measurable_const.mul (measurable_norm.pow_const _)).smul (innerSL ℝ).continuous.measurable
  refine hbound.mono hmeas.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  refine (norm_rpow_smul_innerSL_le s x).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `s ≤ 0`, the regularized powers are dominated by the power away from the origin. -/
private lemma abs_regPow_le (hs : s ≤ 0) {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : x ≠ 0) :
    |regPow s t x| ≤ |regPow s 0 x| := by
  rw [regPow_zero, regPow, abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) ht) _),
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  exact norm_sq_add_rpow_div_two_le ht hx hs

/-- **Integration by parts against a singular norm power.** For `1 - dim E < s ≤ 0` and a `C¹`
function `g` with compact support, `∫ ‖x‖ ^ s ∂ᵥg = -∫ s ‖x‖ ^ (s - 2) ⟪x, v⟫ g`, although for
`s < 0` the power is unbounded near the origin. -/
theorem integral_norm_rpow_mul_fderiv_eq_neg (hs0 : s ≤ 0)
    (hs : 1 - (Module.finrank ℝ E : ℝ) < s) {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (v : E) :
    ∫ x, ‖x‖ ^ s * fderiv ℝ g x v ∂μ =
      -∫ x, ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) v * g x ∂μ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    by_contra h
    have : (Module.finrank ℝ E : ℝ) = 0 := by exact_mod_cast Nat.eq_zero_of_not_pos h
    linarith)
  have hg' : Continuous fun x ↦ fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcg' : HasCompactSupport fun x ↦ fderiv ℝ g x v :=
    (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ ↦ L v) rfl
  have hloc : LocallyIntegrable (fun x : E => ‖x‖ ^ s) μ := by
    simpa only [zero_sub, norm_neg] using
      locallyIntegrable_norm_sub_rpow (mu := μ) (s := s) (by linarith) (0 : E)
  -- Integration by parts for the smooth regularizations.
  have hibp : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ x, regPow s t x * fderiv ℝ g x v ∂μ =
      -∫ x, regPowDeriv s v t x * g x ∂μ :=
    eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) ↦ by
      simpa using integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
        (μ := μ) (B := ContinuousLinearMap.mul ℝ ℝ) (f := regPow s t)
        (f' := regPowDeriv s v t) (g := g) (g' := fun x ↦ fderiv ℝ g x v)
        (((continuous_regPowDeriv s v ht).mul hg.continuous).integrable_of_hasCompactSupport
          hc.mul_left)
        (((continuous_regPow s ht).mul hg').integrable_of_hasCompactSupport hcg'.mul_left)
        (((continuous_regPow s ht).mul hg.continuous).integrable_of_hasCompactSupport
          hc.mul_left)
        (fun x _ ↦ hasLineDerivAt_regPow s v ht x)
        (fun x _ ↦ ((hg.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v)
  -- At `t = 0` the regularizations are the power and, its derivative.
  have hderiv : (fun x ↦ ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) v * g x) =ᵐ[μ]
      fun x ↦ regPowDeriv s v 0 x * g x := by
    filter_upwards with x
    rw [regPowDeriv_zero s v x]
  have hintD : Integrable (fun x ↦ ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) v * g x) μ := by
    simpa [mul_comm] using
      ((locallyIntegrable_norm_rpow_smul_innerSL (μ := μ)
        hs).integrable_smul_left_of_hasCompactSupport hg.continuous hc).apply_continuousLinearMap v
  -- Both sides converge as `t → 0⁺`.
  have hL := tendsto_integral_mul_of_dominated_away ((measure_singleton (0 : E)))
    (μ := μ) (l := 𝓝[>] (0 : ℝ)) (K := regPow s) (K₀ := regPow s 0)
    (eventually_mem_nhdsWithin.mono fun t ht ↦ (continuous_regPow s ht).aestronglyMeasurable)
    (by simpa [regPow_zero] using hloc.integrable_smul_right_of_hasCompactSupport hg' hcg')
    (eventually_mem_nhdsWithin.mono fun t ht x hx ↦ abs_regPow_le hs0 (le_of_lt ht) hx)
    (fun x hx ↦ tendsto_sq_add_rpow (norm_ne_zero_iff.mpr hx) _)
  have hR := tendsto_integral_mul_of_dominated_away ((measure_singleton (0 : E)))
    (μ := μ) (l := 𝓝[>] (0 : ℝ)) (K := regPowDeriv s v) (K₀ := regPowDeriv s v 0)
    (eventually_mem_nhdsWithin.mono fun t ht ↦
      (continuous_regPowDeriv s v ht).aestronglyMeasurable)
    (hintD.congr hderiv)
    (eventually_mem_nhdsWithin.mono fun t ht x _ ↦
      abs_inner_regularizedNormRpowGradient_le (by linarith) (le_of_lt ht) x v)
    (fun x _ ↦ tendsto_regPowDeriv s v x)
  simp only [regPow_zero] at hL
  rw [integral_congr_ae hderiv]
  exact tendsto_nhds_unique (hL.congr' hibp) hR.neg

/-- **Norm powers are weakly differentiable.** For `s > 1 - dim E`, on every open set the
classical derivative `s ‖x‖ ^ (s - 2) ⟪x, ·⟫` of `x ↦ ‖x‖ ^ s`, which exists away from the
origin, is a weak derivative of the power, although for `s < 0` the power is unbounded near the
origin. -/
theorem hasWeakFDerivOn_norm_rpow (hs : 1 - (Module.finrank ℝ E : ℝ) < s) (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (fun x : E => ‖x‖ ^ s)
      (fun x => (s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) := by
  rcases le_or_gt s 0 with hs0 | hs0
  · exact hasWeakFDerivOn_of_forall_integral_fderiv_smul
      (by simpa only [zero_sub, norm_neg] using
        locallyIntegrable_norm_sub_rpow (mu := μ) (s := s) (by linarith) (0 : E))
      (locallyIntegrable_norm_rpow_smul_innerSL hs) (fun _ hg hc v ↦ by
        simpa only [smul_eq_mul, mul_comm] using
          integral_norm_rpow_mul_fderiv_eq_neg hs0 hs hg hc v) Ω
  · exact hasWeakFDerivOn_of_hasFDerivAt_off_countable (countable_singleton 0)
      (continuous_norm.rpow_const fun _ ↦ Or.inr hs0.le).continuousOn
      ((locallyIntegrable_norm_rpow_smul_innerSL hs).locallyIntegrableOn _)
      fun x hx ↦ hasFDerivAt_norm_rpow_of_ne s hx.2

/-! ### The weak Hessian -/

/-- On a ball centred at the origin, the derivative of the gradient field `s ‖x‖ ^ (s - 2) x`
across the origin is its classical derivative. -/
private theorem hasWeakFDerivOn_ball_regularizedNormRpowGradient [Nontrivial E] (hs : s ≤ 2)
    (hn : 2 < Module.finrank ℝ E + s) (R : ℝ) :
    HasWeakFDerivOn μ ⟨Metric.ball 0 R, Metric.isOpen_ball⟩ (regularizedNormRpowGradient s 0)
      (regularizedNormRpowHessian s 0) := by
  have hs1 : -(Module.finrank ℝ E : ℝ) < s - 1 := by linarith
  have hs2 : -(Module.finrank ℝ E : ℝ) < s - 2 := by linarith
  have hae : ∀ᵐ x ∂μ.restrict (Metric.ball 0 R), x ≠ 0 := ae_restrict_of_ae (μ.ae_ne 0)
  have htpos : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
  -- The limit fields are integrable on the ball.
  have hG : IntegrableOn (regularizedNormRpowGradient s 0) (Metric.ball 0 R) μ :=
    ((integrableOn_norm_rpow_ball (mu := μ) hs1).const_mul |s|).mono'
      (measurable_regularizedNormRpowGradient s 0).aestronglyMeasurable
      (ae_of_all _ fun x => norm_regularizedNormRpowGradient_le_mul_rpow hs le_rfl x)
  have hH : ∀ v : E, IntegrableOn (fun x => regularizedNormRpowHessian s 0 x v) (Metric.ball 0 R)
      μ := fun v => by
    refine ((integrableOn_norm_rpow_ball (mu := μ) hs2).const_mul (|s| * (3 - s) * ‖v‖)).mono'
      ?_ (hae.mono fun x hx => ?_)
    · simp only [regularizedNormRpowHessian_apply]
      exact Measurable.aestronglyMeasurable (by fun_prop)
    · calc ‖regularizedNormRpowHessian s 0 x v‖ ≤ ‖regularizedNormRpowHessian s 0 x‖ * ‖v‖ :=
            (regularizedNormRpowHessian s 0 x).le_opNorm v
        _ ≤ |s| * (3 - s) * ‖x‖ ^ (s - 2) * ‖v‖ := by
          gcongr
          exact norm_regularizedNormRpowHessian_le hs le_rfl hx
        _ = |s| * (3 - s) * ‖v‖ * ‖x‖ ^ (s - 2) := by ring
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    (u := fun k : ℕ => regularizedNormRpowGradient s (1 / (k + 1)))
    (U := fun k : ℕ => regularizedNormRpowHessian s (1 / (k + 1)))
    hG.locallyIntegrableOn (fun v => (hH v).locallyIntegrableOn) (fun k => ?_) ?_ ?_
  · exact hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (continuous_regularizedNormRpowGradient s (htpos k)).continuousOn
      ((continuous_regularizedNormRpowHessian (htpos k)).locallyIntegrable.locallyIntegrableOn _)
      fun x _ => hasFDerivAt_regularizedNormRpowGradient s _ (by positivity)
  · exact tendsto_setLIntegral_enorm_sub_of_norm_le_mul_norm_rpow Metric.isBounded_ball hs1
      (Eventually.of_forall fun k =>
        (continuous_regularizedNormRpowGradient s (htpos k)).aestronglyMeasurable)
      (Eventually.of_forall fun k => ae_of_all _ fun x =>
        norm_regularizedNormRpowGradient_le_mul_rpow hs (htpos k).le x)
      (ae_of_all _ fun x =>
        (continuousAt_regularizedNormRpowGradient_apply_zero x).tendsto.comp
          tendsto_one_div_add_atTop_nhds_zero_nat)
  · exact tendsto_setLIntegral_enorm_sub_of_norm_le_mul_norm_rpow Metric.isBounded_ball hs2
      (Eventually.of_forall fun k =>
        (continuous_regularizedNormRpowHessian (htpos k)).aestronglyMeasurable)
      (Eventually.of_forall fun k => hae.mono fun x hx =>
        norm_regularizedNormRpowHessian_le hs (htpos k).le hx)
      (hae.mono fun x hx => (continuousAt_regularizedNormRpowHessian_apply_zero hx).tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem nontrivial_of_two_lt (hs : s ≤ 2) (hn : 2 < Module.finrank ℝ E + s) :
    Nontrivial E :=
  Module.nontrivial_of_finrank_pos (R := ℝ)
    (by exact_mod_cast (by linarith : (0 : ℝ) < Module.finrank ℝ E))

private theorem hasWeakFDerivOn_regularizedNormRpowGradient (hs : s ≤ 2)
    (hn : 2 < Module.finrank ℝ E + s) (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (regularizedNormRpowGradient s 0) (regularizedNormRpowHessian s 0) :=
  have := nontrivial_of_two_lt hs hn
  hasWeakFDerivOn_iff_locally.2 fun x _ => ⟨⟨Metric.ball 0 (‖x‖ + 1), Metric.isOpen_ball⟩,
    mem_ball_zero_iff.2 (lt_add_one _), hasWeakFDerivOn_ball_regularizedNormRpowGradient hs hn _⟩

/-- For `s > 1 - dim E`, the classical gradient of `‖x‖ ^ s` is its weak gradient on every open
set: `TauCeti.hasWeakFDerivOn_norm_rpow` with the derivative written through the gradient. -/
theorem hasWeakFDerivOn_norm_rpow_innerSL_gradient (hs : 1 - (Module.finrank ℝ E : ℝ) < s)
    (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (fun y : E => ‖y‖ ^ s)
      (fun x => innerSL ℝ (∇ (fun y : E => ‖y‖ ^ s) x)) := by
  refine (hasWeakFDerivOn_norm_rpow hs Ω).congr_ae_deriv ?_
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- On the zero space both derivatives are the zero functional.
    exact ae_of_all _ fun x => by
      beta_reduce
      rw [Subsingleton.elim x 0, Subsingleton.elim (∇ (fun y : E => ‖y‖ ^ s) 0) 0]
      simp
  filter_upwards [ae_restrict_of_ae (μ.ae_ne 0)] with x hx
  rw [gradient_norm_rpow_of_ne hx, map_smul]

/-- **The weak Hessian of a norm power.** Let `n + s > 2`, where `n` is the dimension. On every
open set, the classical Hessian of `‖x‖ ^ s`, which exists away from the origin, is the weak
derivative of its gradient across the origin. For `s > 2` the function is `C²`. For smaller `s`
the Hessian, of size at most a multiple of `‖x‖ ^ (s - 2)`, may be unbounded near the origin, but
it is locally integrable. -/
theorem hasWeakFDerivOn_gradient_norm_rpow (hn : 2 < Module.finrank ℝ E + s) (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (∇ fun y : E => ‖y‖ ^ s)
      (iteratedGradientChain (fun y : E => ‖y‖ ^ s) 1) := by
  rcases le_or_gt s 2 with hs | hs
  · have := nontrivial_of_two_lt hs hn
    have hae : ∀ᵐ x ∂μ.restrict Ω, x ≠ 0 := ae_restrict_of_ae (μ.ae_ne 0)
    exact ((hasWeakFDerivOn_regularizedNormRpowGradient hs hn Ω).congr_ae
      (hae.mono fun x hx =>
        (gradient_norm_rpow_eq_regularizedNormRpowGradient hx).symm)).congr_ae_deriv
      (hae.mono fun x hx =>
        (iteratedGradientChain_one_norm_rpow_eq_regularizedNormRpowHessian hx).symm)
  · -- For `s > 2` the function is `C²`, so its gradient is `C¹` with continuous derivative.
    have hC : ContDiff ℝ 2 (fun y : E => ‖y‖ ^ s) :=
      contDiff_norm_rpow_of_lt (k := 2) (by exact_mod_cast hs)
    have h1 : ∀ x, ContDiffAt ℝ 1 (iteratedGradientChain (fun y : E => ‖y‖ ^ s) 0) x :=
      fun x => contDiffAt_iteratedGradientChain hC.contDiffAt 0 (by norm_num)
    have h0 : Continuous (iteratedGradientChain (fun y : E => ‖y‖ ^ s) 1) :=
      continuous_iff_continuousAt.2 fun x =>
        (contDiffAt_iteratedGradientChain hC.contDiffAt 1 (m := 0) (by norm_num)).continuousAt
    rw [← iteratedGradientChain_zero, iteratedGradientChain_succ]
    exact hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt).continuousOn
      (by simpa only [iteratedGradientChain_succ] using h0.locallyIntegrable.locallyIntegrableOn _)
      fun x _ => ((h1 x).differentiableAt (by norm_num)).hasFDerivAt

/-! ### The unit radial field -/

section UnitRadial

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The coordinate `‖x‖⁻¹ ⟪x, v⟫` of the unit radial field is bounded by `‖v‖`. -/
theorem abs_norm_rpow_neg_one_mul_inner_le (v x : E) : |‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫| ≤ ‖v‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [abs_mul, abs_of_nonneg (by positivity), Real.rpow_neg_one]
  calc _ ≤ ‖x‖⁻¹ * (‖x‖ * ‖v‖) := by gcongr; exact abs_real_inner_le_norm x v
    _ = ‖v‖ := by field_simp

/-- The coordinate `‖x‖⁻¹ ⟪x, v⟫` of the unit radial field is the `v`-component of the
unregularized gradient field at `s = 1`. -/
private lemma inner_regularizedNormRpowGradient_one_zero (v x : E) :
    innerSL ℝ v (regularizedNormRpowGradient 1 0 x) = ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫ := by
  rw [innerSL_apply_apply, regularizedNormRpowGradient_zero_right, real_inner_smul_right,
    real_inner_comm, one_mul]
  norm_num

/-- The derivative of the coordinate `‖x‖⁻¹ ⟪x, v⟫` is the `v`-component of the unregularized
Hessian field at `s = 1`. -/
private lemma innerSL_comp_regularizedNormRpowHessian_one_zero (v x : E) :
    (innerSL ℝ v).comp (regularizedNormRpowHessian 1 0 x) =
      ‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x := by
  ext w
  simp only [ContinuousLinearMap.comp_apply, regularizedNormRpowHessian_zero_apply,
    innerSL_apply_apply, sub_apply, smul_apply, inner_add_right, real_inner_smul_right,
    smul_eq_mul]
  rw [real_inner_comm v x]
  norm_num
  ring

/-- Away from the origin, the derivative `‖x‖⁻¹ ⟪v, ·⟫ - ‖x‖⁻³ ⟪x, v⟫ ⟪x, ·⟫` of the coordinate
`‖x‖⁻¹ ⟪x, v⟫` of the unit radial field has norm at most `2 ‖v‖ ‖x‖⁻¹`. -/
theorem norm_norm_rpow_neg_one_smul_innerSL_sub_le (v x : E) :
    ‖‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x‖ ≤
      2 * ‖v‖ * ‖x‖ ^ (-1 : ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [← innerSL_comp_regularizedNormRpowHessian_one_zero]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [innerSL_apply_norm]
  have h := norm_regularizedNormRpowHessian_le (s := 1) one_le_two le_rfl hx
  norm_num at h
  calc ‖v‖ * ‖regularizedNormRpowHessian 1 0 x‖ ≤ ‖v‖ * (2 * ‖x‖ ^ (-1 : ℝ)) := by gcongr
    _ = 2 * ‖v‖ * ‖x‖ ^ (-1 : ℝ) := by ring

end UnitRadial

/-- **The unit radial field is weakly differentiable.** If `dim E ≥ 2`, then on every open set the
classical derivative `‖x‖⁻¹ ⟪v, ·⟫ - ‖x‖⁻³ ⟪x, v⟫ ⟪x, ·⟫` of the coordinate `‖x‖⁻¹ ⟪x, v⟫` of the
unit radial field `x / ‖x‖`, which exists away from the origin, is a weak derivative of the
coordinate, although the coordinate is discontinuous at the origin. The derivative has size
`‖x‖⁻¹`, which is locally integrable exactly when `dim E ≥ 2`. -/
theorem hasWeakFDerivOn_norm_rpow_neg_one_mul_inner (hd : 1 < Module.finrank ℝ E) (v : E)
    (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (fun x : E ↦ ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫)
      (fun x ↦ ‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x) := by
  have hn : 2 < (Module.finrank ℝ E : ℝ) + 1 := by
    have := (Nat.one_lt_cast (α := ℝ)).2 hd
    linarith
  simpa only [inner_regularizedNormRpowGradient_one_zero,
    innerSL_comp_regularizedNormRpowHessian_one_zero] using
    (hasWeakFDerivOn_regularizedNormRpowGradient (μ := μ) one_le_two hn Ω).clm_comp (innerSL ℝ v)

end TauCeti
