/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Regularization
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

This adapts the regularization proof first given for the Newtonian kernel in Tau Ceti's
`TauCeti.integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul`
(`TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/DistributionalLaplacian.lean`), replacing the
exponent `2 - n` by an arbitrary exponent; that theorem is derived from the general one here.

## Main declarations

* `TauCeti.locallyIntegrable_norm_rpow_smul_innerSL`: the classical derivative is locally
  integrable for `s > 1 - d`.
* `TauCeti.integral_norm_rpow_mul_fderiv_eq_neg`: integration by parts against `‖x‖ ^ s` for
  `1 - d < s ≤ 0`.
* `TauCeti.hasWeakFDerivOn_norm_rpow`: the classical derivative is a weak derivative on every
  open set for `s > 1 - d`.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set Topology TopologicalSpace

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : ℝ}

/-- The norm power regularized at scale `t`. -/
private def regPow (s t : ℝ) (x : E) : ℝ :=
  (‖x‖ ^ 2 + t) ^ (s / 2)

/-- The derivative of the regularized norm power in the direction `v`. -/
private def regPowDeriv (s : ℝ) (v : E) (t : ℝ) (x : E) : ℝ :=
  s * (‖x‖ ^ 2 + t) ^ (s / 2 - 1) * ⟪x, v⟫

omit [InnerProductSpace ℝ E] in
private lemma regPow_zero (s : ℝ) (x : E) : regPow s 0 x = ‖x‖ ^ s := by
  rw [regPow, add_zero, Real.sq_rpow_div_two (norm_nonneg x)]

private lemma regPowDeriv_zero (s : ℝ) (v : E) (x : E) :
    regPowDeriv s v 0 x = ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) v := by
  have hs : s / 2 - 1 = (s - 2) / 2 := by ring
  rw [regPowDeriv, add_zero, hs, Real.sq_rpow_div_two (norm_nonneg x)]
  simp [mul_assoc]

private lemma hasLineDerivAt_regPow (s : ℝ) (v : E) {t : ℝ} (ht : 0 < t) (x : E) :
    HasLineDerivAt ℝ (regPow s t) (regPowDeriv s v t x) x v := by
  have hpos : 0 < ‖x‖ ^ 2 + t := add_pos_of_nonneg_of_pos (sq_nonneg _) ht
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const t).rpow_const
    (p := s / 2) (Or.inl hpos.ne')
  refine (h.hasLineDerivAt v).congr_deriv ?_
  rw [regPowDeriv, smul_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] in
private lemma continuous_regPow (s : ℝ) {t : ℝ} (ht : 0 < t) : Continuous (regPow (E := E) s t) :=
  ((continuous_norm.pow 2).add continuous_const).rpow_const
    fun _ ↦ Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg _) ht).ne'

private lemma continuous_regPowDeriv (s : ℝ) (v : E) {t : ℝ} (ht : 0 < t) :
    Continuous (regPowDeriv s v t) :=
  (continuous_const.mul (((continuous_norm.pow 2).add continuous_const).rpow_const
    fun _ ↦ Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg _) ht).ne')).mul
      (continuous_id.inner continuous_const)

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
  simp only [regPow, abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) ht) _),
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) le_rfl) _)]
  exact sq_add_rpow_le (norm_ne_zero_iff.mpr hx) ht (by linarith)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `s ≤ 2`, the derivatives of the regularized powers are dominated by the regularization at
`t = 0` away from the origin. -/
private lemma abs_regPowDeriv_le (hs : s ≤ 2) (v : E) {t : ℝ} (ht : 0 ≤ t) {x : E}
    (hx : x ≠ 0) : |regPowDeriv s v t x| ≤ |regPowDeriv s v 0 x| := by
  simp only [regPowDeriv, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) ht) _),
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) le_rfl) _)]
  gcongr ?_ * _
  exact mul_le_mul_of_nonneg_left (sq_add_rpow_le (norm_ne_zero_iff.mpr hx) ht (by linarith))
    (abs_nonneg s)

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
    (eventually_mem_nhdsWithin.mono fun t ht x hx ↦
      abs_regPowDeriv_le (by linarith) v (le_of_lt ht) hx)
    (fun x hx ↦ ((tendsto_sq_add_rpow (norm_ne_zero_iff.mpr hx) _).const_mul _).mul_const _)
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

end TauCeti
