/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Calculus.FDeriv.Integral
import TauCeti.Analysis.InnerProductSpace.NormPow
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

For `s > 0` the power is continuous and the origin is a removable point: the integral of the
derivative of `‖x‖ ^ s g(x)`, which exists off the origin, vanishes for every `C¹` function `g`
with compact support (`TauCeti.integral_apply_eq_zero_of_hasFDerivAt_off_countable`). For
`s ≤ 0`, where the power is unbounded near the origin unless `s = 0`, the power is replaced by the
smooth regularizations `(‖x‖ ^ 2 + t) ^ (s / 2)`, whose values and derivatives are dominated by
those at `t = 0`, and dominated convergence passes the integration by parts identity to the limit
`t → 0⁺`.

This adapts the regularization proof first given for the Newtonian kernel in Tau Ceti's
`TauCeti.integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul`
(`TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/DistributionalLaplacian.lean`), replacing the
exponent `2 - n` by an arbitrary exponent; that theorem is derived from the general one here.

The same regularization shows that for `s > -d` the products `‖x‖ ^ s ⟪x, v⟫` are weakly
differentiable on every open set, with their classical derivatives
`‖x‖ ^ s ⟪v, ·⟫ + s ‖x‖ ^ (s - 2) ⟪x, v⟫ ⟪x, ·⟫`: for `s ≤ 0` their regularizations
`(‖x‖ ^ 2 + t) ^ (s / 2) ⟪x, v⟫` and the derivatives of those converge in `L¹` on the unit ball,
dominated by `‖v‖ ‖x‖ ^ (s + 1)` and by `(1 + |s|) ‖v‖ ‖x‖ ^ s`. At `s = -1` these are the
coordinates of the unit radial field `x / ‖x‖`, the weak gradient of the norm, and at `s = p - 2`
they are multiples of the coordinates of the gradient `p ‖x‖ ^ (p - 2) x` of `‖x‖ ^ p`, so the
second weak derivatives of norm powers are their classical ones.

## Main declarations

* `TauCeti.locallyIntegrable_norm_rpow_smul_innerSL`: the classical derivative is locally
  integrable for `s > 1 - d`.
* `TauCeti.integral_norm_rpow_mul_fderiv_eq_neg`: integration by parts against `‖x‖ ^ s` for
  `s > 1 - d`.
* `TauCeti.hasWeakFDerivOn_norm_rpow`: the classical derivative is a weak derivative on every
  open set for `s > 1 - d`.
* `TauCeti.hasWeakFDerivOn_norm_rpow_mul_inner`: for `s > -d`, the products `‖x‖ ^ s ⟪x, v⟫` are
  weakly differentiable on every open set, with their classical derivatives.
* `TauCeti.abs_norm_rpow_mul_inner_le`, `TauCeti.norm_norm_rpow_smul_innerSL_add_le`: the products
  are bounded by `‖v‖ ‖x‖ ^ (s + 1)` and their derivatives by `(1 + |s|) ‖v‖ ‖x‖ ^ s`.
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

/-- The regularization `(‖x‖ ^ 2 + t) ^ (s / 2) ⟪x, v⟫` of `‖x‖ ^ s ⟪x, v⟫`. -/
private def regMulInner (s : ℝ) (v : E) (t : ℝ) (x : E) : ℝ :=
  regPow s t x * ⟪x, v⟫

/-- The derivative of the regularized norm power in the direction `v`. -/
private def regPowDeriv (s : ℝ) (v : E) (t : ℝ) (x : E) : ℝ :=
  s * regMulInner (s - 2) v t x

omit [InnerProductSpace ℝ E] in
private lemma regPow_zero (s : ℝ) (x : E) : regPow s 0 x = ‖x‖ ^ s := by
  rw [regPow, add_zero, Real.sq_rpow_div_two (norm_nonneg x)]

private lemma regMulInner_zero (s : ℝ) (v : E) :
    regMulInner s v 0 = fun x ↦ ‖x‖ ^ s * ⟪x, v⟫ := by
  funext x
  rw [regMulInner, regPow_zero]

private lemma regPowDeriv_zero (s : ℝ) (v : E) (x : E) :
    regPowDeriv s v 0 x = ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) v := by
  rw [regPowDeriv, regMulInner_zero]
  simp [mul_assoc]

private lemma hasLineDerivAt_regPow (s : ℝ) (v : E) {t : ℝ} (ht : 0 < t) (x : E) :
    HasLineDerivAt ℝ (regPow s t) (regPowDeriv s v t x) x v := by
  have hpos : 0 < ‖x‖ ^ 2 + t := add_pos_of_nonneg_of_pos (sq_nonneg _) ht
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const t).rpow_const
    (p := s / 2) (Or.inl hpos.ne')
  refine (h.hasLineDerivAt v).congr_deriv ?_
  rw [regPowDeriv, regMulInner, regPow, show (s - 2) / 2 = s / 2 - 1 by ring, smul_apply,
    smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] in
private lemma continuous_regPow (s : ℝ) {t : ℝ} (ht : 0 < t) : Continuous (regPow (E := E) s t) :=
  continuous_norm_sq_add_rpow ht _

private lemma continuous_regMulInner (s : ℝ) (v : E) {t : ℝ} (ht : 0 < t) :
    Continuous (regMulInner s v t) :=
  (continuous_regPow s ht).mul (continuous_id.inner continuous_const)

private lemma continuous_regPowDeriv (s : ℝ) (v : E) {t : ℝ} (ht : 0 < t) :
    Continuous (regPowDeriv s v t) :=
  continuous_const.mul (continuous_regMulInner (s - 2) v ht)

private lemma tendsto_regMulInner (s : ℝ) (v : E) {x : E} (hx : x ≠ 0) :
    Tendsto (fun t ↦ regMulInner s v t x) (𝓝[>] 0) (𝓝 (regMulInner s v 0 x)) :=
  (tendsto_sq_add_rpow (norm_ne_zero_iff.mpr hx) _).mul_const _

private lemma tendsto_regPowDeriv (s : ℝ) (v : E) {x : E} (hx : x ≠ 0) :
    Tendsto (fun t ↦ regPowDeriv s v t x) (𝓝[>] 0) (𝓝 (regPowDeriv s v 0 x)) :=
  (tendsto_regMulInner (s - 2) v hx).const_mul s

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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `s ≤ 0`, the regularizations of `‖x‖ ^ s ⟪x, v⟫` are dominated by the regularization at
`t = 0` away from the origin. -/
private lemma abs_regMulInner_le (hs : s ≤ 0) (v : E) {t : ℝ} (ht : 0 ≤ t) {x : E}
    (hx : x ≠ 0) : |regMulInner s v t x| ≤ |regMulInner s v 0 x| := by
  rw [regMulInner, regMulInner, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_regPow_le hs ht hx) (abs_nonneg _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `s ≤ 2`, the derivatives of the regularized powers are dominated by the regularization at
`t = 0` away from the origin. -/
private lemma abs_regPowDeriv_le (hs : s ≤ 2) (v : E) {t : ℝ} (ht : 0 ≤ t) {x : E}
    (hx : x ≠ 0) : |regPowDeriv s v t x| ≤ |regPowDeriv s v 0 x| := by
  rw [regPowDeriv, regPowDeriv, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_regMulInner_le (by linarith) v ht hx) (abs_nonneg s)

/-- Integration by parts against a norm power `‖x‖ ^ s` with `1 - dim E < s ≤ 0`, through the
smooth regularizations `(‖x‖ ^ 2 + t) ^ (s / 2)`. -/
private theorem integral_norm_rpow_mul_fderiv_eq_neg_of_nonpos (hs0 : s ≤ 0)
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
    (fun x hx ↦ tendsto_regPowDeriv s v hx)
  simp only [regPow_zero] at hL
  rw [integral_congr_ae hderiv]
  exact tendsto_nhds_unique (hL.congr' hibp) hR.neg

/-- Integration by parts against a norm power `‖x‖ ^ s` with `s > 0`, which is continuous and
differentiable off the origin. -/
private theorem integral_norm_rpow_mul_fderiv_eq_neg_of_pos (hs0 : 0 < s)
    (hs : 1 - (Module.finrank ℝ E : ℝ) < s) {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (v : E) :
    ∫ x, ‖x‖ ^ s * fderiv ℝ g x v ∂μ =
      -∫ x, ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) v * g x ∂μ := by
  have hpow : Continuous fun x : E ↦ ‖x‖ ^ s := continuous_norm.rpow_const fun _ ↦ Or.inr hs0.le
  have hg' : Continuous fun x ↦ fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcg' : HasCompactSupport fun x ↦ fderiv ℝ g x v :=
    (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ ↦ L v) rfl
  have hi₁ : Integrable (fun x ↦ ‖x‖ ^ s * fderiv ℝ g x v) μ :=
    (hpow.mul hg').integrable_of_hasCompactSupport hcg'.mul_left
  have hi₂ : Integrable (fun x ↦ ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) v * g x) μ := by
    simpa [mul_comm] using
      ((locallyIntegrable_norm_rpow_smul_innerSL (μ := μ)
        hs).integrable_smul_left_of_hasCompactSupport hg.continuous hc).apply_continuousLinearMap v
  -- The product `‖x‖ ^ s g(x)` is differentiable off the origin, so its derivative integrates
  -- to zero.
  have hzero := integral_apply_eq_zero_of_hasFDerivAt_off_countable (μ := μ)
    (countable_singleton (0 : E)) (hpow.mul hg.continuous) hc.mul_left
    (fun x hx ↦ (hasFDerivAt_norm_rpow_of_ne s hx).mul
      ((hg.differentiable one_ne_zero) x).hasFDerivAt) v
  rw [eq_neg_iff_add_eq_zero, ← integral_add hi₁ hi₂, ← hzero]
  congr 1 with x
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- **Integration by parts against a norm power.** For `s > 1 - dim E` and a `C¹` function `g`
with compact support, `∫ ‖x‖ ^ s ∂ᵥg = -∫ s ‖x‖ ^ (s - 2) ⟪x, v⟫ g`, although for `s < 0` the
power is unbounded near the origin. -/
theorem integral_norm_rpow_mul_fderiv_eq_neg (hs : 1 - (Module.finrank ℝ E : ℝ) < s)
    {g : E → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (v : E) :
    ∫ x, ‖x‖ ^ s * fderiv ℝ g x v ∂μ =
      -∫ x, ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) v * g x ∂μ := by
  rcases le_or_gt s 0 with hs0 | hs0
  · exact integral_norm_rpow_mul_fderiv_eq_neg_of_nonpos hs0 hs hg hc v
  · exact integral_norm_rpow_mul_fderiv_eq_neg_of_pos hs0 hs hg hc v

/-- **Norm powers are weakly differentiable.** For `s > 1 - dim E`, on every open set the
classical derivative `s ‖x‖ ^ (s - 2) ⟪x, ·⟫` of `x ↦ ‖x‖ ^ s`, which exists away from the
origin, is a weak derivative of the power, although for `s < 0` the power is unbounded near the
origin. -/
theorem hasWeakFDerivOn_norm_rpow (hs : 1 - (Module.finrank ℝ E : ℝ) < s) (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (fun x : E => ‖x‖ ^ s)
      (fun x => (s * ‖x‖ ^ (s - 2)) • innerSL ℝ x) :=
  hasWeakFDerivOn_of_forall_integral_fderiv_smul
    (by simpa only [zero_sub, norm_neg] using
      locallyIntegrable_norm_sub_rpow (mu := μ) (s := s) (by linarith) (0 : E))
    (locallyIntegrable_norm_rpow_smul_innerSL hs) (fun _ hg hc v ↦ by
      simpa only [smul_eq_mul, mul_comm] using integral_norm_rpow_mul_fderiv_eq_neg hs hg hc v) Ω

/-! ### Norm powers times a coordinate -/

section RpowMulInner

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The derivative of `regMulInner s v t`. -/
private def regMulInnerDeriv (s : ℝ) (v : E) (t : ℝ) (x : E) : E →L[ℝ] ℝ :=
  (‖x‖ ^ 2 + t) ^ (s / 2) • innerSL ℝ v +
    (s * (‖x‖ ^ 2 + t) ^ (s / 2 - 1) * ⟪x, v⟫) • innerSL ℝ x

private lemma regMulInnerDeriv_zero (s : ℝ) (v x : E) :
    regMulInnerDeriv s v 0 x =
      ‖x‖ ^ s • innerSL ℝ v + (s * ‖x‖ ^ (s - 2) * ⟪x, v⟫) • innerSL ℝ x := by
  have hs : s / 2 - 1 = (s - 2) / 2 := by ring
  rw [regMulInnerDeriv, add_zero, hs, Real.sq_rpow_div_two (norm_nonneg x),
    Real.sq_rpow_div_two (norm_nonneg x)]

private lemma hasFDerivAt_regMulInner (s : ℝ) (v : E) {t : ℝ} {x : E}
    (hx : 0 < ‖x‖ ^ 2 + t) :
    HasFDerivAt (regMulInner s v t) (regMulInnerDeriv s v t x) x := by
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const t).rpow_const
    (p := s / 2) (Or.inl hx.ne')).mul (innerSL ℝ v).hasFDerivAt
  convert h using 1
  · funext y
    rw [regMulInner, regPow, Pi.mul_apply, innerSL_apply_apply, real_inner_comm]
  · ext w
    simp only [regMulInnerDeriv, add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
      nsmul_eq_mul]
    rw [real_inner_comm v x]
    ring

private lemma continuous_regMulInnerDeriv (s : ℝ) (v : E) {t : ℝ} (ht : 0 < t) :
    Continuous (regMulInnerDeriv s v t) :=
  ((continuous_norm_sq_add_rpow ht _).smul continuous_const).add
    (((continuous_const.mul (continuous_norm_sq_add_rpow ht _)).mul
      (continuous_id.inner continuous_const)).smul (innerSL ℝ (E := E)).continuous)

private lemma tendsto_regMulInnerDeriv (s : ℝ) (v : E) {x : E} (hx : x ≠ 0) :
    Tendsto (fun t ↦ regMulInnerDeriv s v t x) (𝓝[>] 0) (𝓝 (regMulInnerDeriv s v 0 x)) :=
  ((((continuousAt_sq_add_rpow (norm_ne_zero_iff.2 hx) _).smul continuousAt_const).add
    (((continuousAt_const.mul (continuousAt_sq_add_rpow (norm_ne_zero_iff.2 hx) _)).mul
      continuousAt_const).smul continuousAt_const)).tendsto).mono_left nhdsWithin_le_nhds

/-- The product `‖x‖ ^ s ⟪x, v⟫` is bounded by `‖v‖ ‖x‖ ^ (s + 1)`. -/
theorem abs_norm_rpow_mul_inner_le (s : ℝ) (v x : E) :
    |‖x‖ ^ s * ⟪x, v⟫| ≤ ‖v‖ * ‖x‖ ^ (s + 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [inner_zero_left, mul_zero, abs_zero]
    positivity
  rw [abs_mul, abs_of_nonneg (by positivity), Real.rpow_add_one (norm_ne_zero_iff.2 hx)]
  calc _ ≤ ‖x‖ ^ s * (‖x‖ * ‖v‖) := by gcongr; exact abs_real_inner_le_norm x v
    _ = _ := by ring

/-- Away from the origin, the derivative `‖x‖ ^ s ⟪v, ·⟫ + s ‖x‖ ^ (s - 2) ⟪x, v⟫ ⟪x, ·⟫` of
`x ↦ ‖x‖ ^ s ⟪x, v⟫` has norm at most `(1 + |s|) ‖v‖ ‖x‖ ^ s`. -/
theorem norm_norm_rpow_smul_innerSL_add_le (s : ℝ) (v x : E) :
    ‖‖x‖ ^ s • innerSL ℝ v + (s * ‖x‖ ^ (s - 2) * ⟪x, v⟫) • innerSL ℝ x‖ ≤
      (1 + |s|) * ‖v‖ * ‖x‖ ^ s := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [inner_zero_left, mul_zero, zero_smul, add_zero, norm_smul, innerSL_apply_norm,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg (0 : E)) s)]
    have : 0 ≤ ‖(0 : E)‖ ^ s * ‖v‖ := by positivity
    nlinarith [abs_nonneg s]
  have h2 : ‖x‖ ^ (s - 2) * ‖x‖ ^ 2 = ‖x‖ ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.2 hx)]
    norm_num
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, innerSL_apply_norm, innerSL_apply_norm,
    Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ (s - 2))]
  calc _ ≤ ‖x‖ ^ s * ‖v‖ + |s| * ‖x‖ ^ (s - 2) * (‖x‖ * ‖v‖) * ‖x‖ := by
        gcongr; exact abs_real_inner_le_norm x v
    _ = (1 + |s|) * ‖v‖ * ‖x‖ ^ s := by rw [← h2]; ring

/-- For `s ≤ 0`, the derivatives of the regularizations are dominated by
`(1 + |s|) ‖v‖ ‖x‖ ^ s` away from the origin. -/
private lemma norm_regMulInnerDeriv_le {s : ℝ} (hs : s ≤ 0) (v : E) {t : ℝ} (ht : 0 ≤ t)
    {x : E} (hx : x ≠ 0) : ‖regMulInnerDeriv s v t x‖ ≤ (1 + |s|) * ‖v‖ * ‖x‖ ^ s := by
  have hpos : 0 < ‖x‖ ^ 2 + t := by have := norm_pos_iff.2 hx; positivity
  have h1 : (‖x‖ ^ 2 + t) ^ (s / 2) ≤ ‖x‖ ^ s := norm_sq_add_rpow_div_two_le ht hx hs
  have h3 : (‖x‖ ^ 2 + t) ^ (s / 2 - 1) * ‖x‖ ^ 2 ≤ (‖x‖ ^ 2 + t) ^ (s / 2) := by
    calc _ ≤ (‖x‖ ^ 2 + t) ^ (s / 2 - 1) * (‖x‖ ^ 2 + t) := by gcongr; linarith
      _ = _ := by rw [← Real.rpow_add_one hpos.ne']; norm_num
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, innerSL_apply_norm, innerSL_apply_norm,
    Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖x‖ ^ 2 + t) ^ (s / 2 - 1))]
  calc _ ≤ (‖x‖ ^ 2 + t) ^ (s / 2) * ‖v‖ +
        |s| * (‖x‖ ^ 2 + t) ^ (s / 2 - 1) * (‖x‖ * ‖v‖) * ‖x‖ := by
        gcongr; exact abs_real_inner_le_norm x v
    _ = ‖v‖ * ((‖x‖ ^ 2 + t) ^ (s / 2) + |s| * ((‖x‖ ^ 2 + t) ^ (s / 2 - 1) * ‖x‖ ^ 2)) := by
        ring
    _ ≤ ‖v‖ * (‖x‖ ^ s + |s| * ‖x‖ ^ s) := by gcongr; exact h3.trans h1
    _ = _ := by ring

end RpowMulInner

private lemma locallyIntegrable_norm_rpow_smul_innerSL_add {s : ℝ}
    (hs : -(Module.finrank ℝ E : ℝ) < s) (v : E) :
    LocallyIntegrable
      (fun x : E ↦ ‖x‖ ^ s • innerSL ℝ v + (s * ‖x‖ ^ (s - 2) * ⟪x, v⟫) • innerSL ℝ x) μ := by
  have h := (locallyIntegrable_norm_sub_rpow (mu := μ) hs 0).smul ((1 + |s|) * ‖v‖)
  refine h.mono (by fun_prop : Measurable _).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  rw [Pi.smul_apply, zero_sub, norm_neg, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact norm_norm_rpow_smul_innerSL_add_le s v x

private lemma hasWeakFDerivOn_regMulInner_ball {s : ℝ} (hs0 : s ≤ 0)
    (hs : -(Module.finrank ℝ E : ℝ) < s) (v : E) :
    HasWeakFDerivOn μ ⟨Metric.ball 0 1, Metric.isOpen_ball⟩ (fun x : E ↦ ‖x‖ ^ s * ⟪x, v⟫)
      (fun x ↦ ‖x‖ ^ s • innerSL ℝ v + (s * ‖x‖ ^ (s - 2) * ⟪x, v⟫) • innerSL ℝ x) := by
  have hs1 : -(Module.finrank ℝ E : ℝ) < s + 1 := by linarith
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by exact_mod_cast
    (neg_neg_iff_pos.1 (hs.trans_le hs0) : (0 : ℝ) < Module.finrank ℝ E))
  set c : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hc0 : ∀ n, 0 < c n := fun n ↦ Nat.one_div_pos_of_nat
  have hc : Tendsto c atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hc0⟩
  have hloc : LocallyIntegrable (fun x : E ↦ ‖x‖ ^ s * ⟪x, v⟫) μ := by
    refine ((locallyIntegrable_norm_sub_rpow (mu := μ) hs1 0).smul ‖v‖).mono
      (by fun_prop : Measurable _).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
    rw [Pi.smul_apply, zero_sub, norm_neg, smul_eq_mul,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖v‖ * ‖x‖ ^ (s + 1))]
    exact abs_norm_rpow_mul_inner_le s v x
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    (u := fun n ↦ regMulInner s v (c n)) (U := fun n ↦ regMulInnerDeriv s v (c n))
    (hloc.locallyIntegrableOn _)
    (fun w ↦ by
      simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
        (ContinuousLinearMap.apply ℝ ℝ w).locallyIntegrableOn_comp
          ((locallyIntegrable_norm_rpow_smul_innerSL_add hs v).locallyIntegrableOn _))
    (fun n ↦ ?_) ?_ ?_
  · exact hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (continuous_regMulInner s v (hc0 n)).continuousOn
      ((continuous_regMulInnerDeriv s v (hc0 n)).locallyIntegrable.locallyIntegrableOn _)
      fun x _ ↦ hasFDerivAt_regMulInner s v (by have := hc0 n; positivity)
  · simpa only [ofReal_norm, Opens.coe_mk] using
      tendsto_lintegral_norm_of_dominated_convergence
        (μ := μ.restrict (Metric.ball 0 1)) (bound := fun x ↦ ‖v‖ * ‖x‖ ^ (s + 1))
        (fun n ↦ (continuous_regMulInner s v (hc0 n)).aestronglyMeasurable)
        ((integrableOn_norm_rpow_ball (mu := μ) hs1).const_mul ‖v‖).hasFiniteIntegral
        (fun n ↦ ae_restrict_of_ae <| by
          filter_upwards [μ.ae_ne 0] with x hx
          exact (abs_regMulInner_le hs0 v (hc0 n).le hx).trans
            (by simpa only [regMulInner_zero] using abs_norm_rpow_mul_inner_le s v x))
        (ae_restrict_of_ae <| by
          filter_upwards [μ.ae_ne 0] with x hx
          simpa only [regMulInner_zero, Function.comp_def] using
            (tendsto_regMulInner s v hx).comp hc)
  · simpa only [ofReal_norm, Opens.coe_mk] using
      tendsto_lintegral_norm_of_dominated_convergence
        (μ := μ.restrict (Metric.ball 0 1)) (bound := fun x ↦ (1 + |s|) * ‖v‖ * ‖x‖ ^ s)
        (fun n ↦ (continuous_regMulInnerDeriv s v (hc0 n)).aestronglyMeasurable)
        ((integrableOn_norm_rpow_ball (mu := μ) hs).const_mul ((1 + |s|) * ‖v‖)).hasFiniteIntegral
        (fun n ↦ ae_restrict_of_ae <| by
          filter_upwards [μ.ae_ne 0] with x hx
          exact norm_regMulInnerDeriv_le hs0 v (hc0 n).le hx)
        (ae_restrict_of_ae <| by
          filter_upwards [μ.ae_ne 0] with x hx
          simpa only [regMulInnerDeriv_zero, Function.comp_def] using
            (tendsto_regMulInnerDeriv s v hx).comp hc)

/-- **Norm powers times a coordinate are weakly differentiable.** For `s > -dim E`, on every open
set the classical derivative `‖x‖ ^ s ⟪v, ·⟫ + s ‖x‖ ^ (s - 2) ⟪x, v⟫ ⟪x, ·⟫` of
`x ↦ ‖x‖ ^ s ⟪x, v⟫`, which exists away from the origin, is a weak derivative of the product,
although for `s ≤ -1` the product is discontinuous at the origin. The derivative has size
`‖x‖ ^ s`, which is locally integrable exactly when `s > -dim E`. For `s = -1` the product is a
coordinate of the unit radial field `x / ‖x‖`, the weak gradient of the norm; for `s = p - 2` it is
`p⁻¹` times a coordinate of the gradient of `‖x‖ ^ p`. -/
theorem hasWeakFDerivOn_norm_rpow_mul_inner {s : ℝ} (hs : -(Module.finrank ℝ E : ℝ) < s)
    (v : E) (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (fun x : E ↦ ‖x‖ ^ s * ⟪x, v⟫)
      (fun x ↦ ‖x‖ ^ s • innerSL ℝ v + (s * ‖x‖ ^ (s - 2) * ⟪x, v⟫) • innerSL ℝ x) := by
  have hderiv : ∀ x : E, x ≠ 0 → HasFDerivAt (fun x : E ↦ ‖x‖ ^ s * ⟪x, v⟫)
      (‖x‖ ^ s • innerSL ℝ v + (s * ‖x‖ ^ (s - 2) * ⟪x, v⟫) • innerSL ℝ x) x :=
    fun x hx ↦ by
      simpa only [regMulInner_zero, regMulInnerDeriv_zero] using
        hasFDerivAt_regMulInner (t := 0) s v (by have := norm_pos_iff.2 hx; positivity)
  have hD := (locallyIntegrable_norm_rpow_smul_innerSL_add (μ := μ) hs v).locallyIntegrableOn
  rcases lt_or_ge 0 s with hs0 | hs0
  · exact hasWeakFDerivOn_of_hasFDerivAt_off_countable (countable_singleton 0)
      (((continuous_norm.rpow_const fun _ ↦ Or.inr hs0.le).mul
        (continuous_id.inner continuous_const)).continuousOn) (hD _) fun x hx ↦ hderiv x hx.2
  have hcompl : HasWeakFDerivOn μ ⟨{0}ᶜ, isOpen_compl_singleton⟩
      (fun x : E ↦ ‖x‖ ^ s * ⟪x, v⟫)
      (fun x ↦ ‖x‖ ^ s • innerSL ℝ v + (s * ‖x‖ ^ (s - 2) * ⟪x, v⟫) • innerSL ℝ x) :=
    hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (fun x hx ↦ (hderiv x hx).continuousAt.continuousWithinAt) (hD _) fun x hx ↦ hderiv x hx.1
  refine ((hasWeakFDerivOn_regMulInner_ball hs0 hs v).sup hcompl).mono fun x _ ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inl (Metric.mem_ball_self one_pos)
  · exact Or.inr hx

end TauCeti
