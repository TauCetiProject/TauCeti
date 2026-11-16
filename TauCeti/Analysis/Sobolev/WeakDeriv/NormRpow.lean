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

This adapts the regularization proof first given for the Newtonian kernel in Tau Ceti's
`TauCeti.integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul`
(`TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/DistributionalLaplacian.lean`), replacing the
exponent `2 - n` by an arbitrary exponent; that theorem is derived from the general one here.

The same regularization at `s = 1` shows that if `d ≥ 2`, the coordinates `‖x‖⁻¹ ⟪x, v⟫` of the
unit radial field `x / ‖x‖`, which is the weak gradient of the norm, are weakly differentiable on
every open set: their regularizations `(‖x‖ ^ 2 + t) ^ (-1 / 2) ⟪x, v⟫` and the derivatives of
those converge in `L¹` on the unit ball, dominated by `‖v‖` and by `2 ‖v‖ ‖x‖⁻¹`.

## Main declarations

* `TauCeti.locallyIntegrable_norm_rpow_smul_innerSL`: the classical derivative is locally
  integrable for `s > 1 - d`.
* `TauCeti.integral_norm_rpow_mul_fderiv_eq_neg`: integration by parts against `‖x‖ ^ s` for
  `1 - d < s ≤ 0`.
* `TauCeti.hasWeakFDerivOn_norm_rpow`: the classical derivative is a weak derivative on every
  open set for `s > 1 - d`.
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
  continuous_norm_sq_add_rpow ht _

private lemma continuous_regPowDeriv (s : ℝ) (v : E) {t : ℝ} (ht : 0 < t) :
    Continuous (regPowDeriv s v t) :=
  (continuous_const.mul (continuous_norm_sq_add_rpow ht _)).mul
    (continuous_id.inner continuous_const)

private lemma tendsto_regPowDeriv (s : ℝ) (v : E) {x : E} (hx : x ≠ 0) :
    Tendsto (fun t ↦ regPowDeriv s v t x) (𝓝[>] 0) (𝓝 (regPowDeriv s v 0 x)) :=
  ((tendsto_sq_add_rpow (norm_ne_zero_iff.mpr hx) _).const_mul _).mul_const _

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
    (fun x hx ↦ tendsto_regPowDeriv s v hx)
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

/-! ### The unit radial field -/

section UnitRadial

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The derivative of `regPowDeriv 1 v t`, which regularizes the coordinate `‖x‖⁻¹ ⟪x, v⟫` of
the unit radial field. -/
private def regPowDerivOneDeriv (v : E) (t : ℝ) (x : E) : E →L[ℝ] ℝ :=
  (‖x‖ ^ 2 + t) ^ (-1 / 2 : ℝ) • innerSL ℝ v -
    ((‖x‖ ^ 2 + t) ^ (-3 / 2 : ℝ) * ⟪x, v⟫) • innerSL ℝ x

private lemma regPowDeriv_one (v : E) (t : ℝ) (x : E) :
    regPowDeriv 1 v t x = (‖x‖ ^ 2 + t) ^ (-1 / 2 : ℝ) * ⟪x, v⟫ := by
  rw [regPowDeriv, one_mul]
  norm_num

private lemma regPowDeriv_one_zero (v : E) :
    regPowDeriv 1 v 0 = fun x ↦ ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫ := by
  funext x
  rw [regPowDeriv_one, add_zero, Real.sq_rpow_div_two (norm_nonneg x)]

private lemma regPowDerivOneDeriv_zero (v x : E) :
    regPowDerivOneDeriv v 0 x =
      ‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x := by
  rw [regPowDerivOneDeriv, add_zero, Real.sq_rpow_div_two (norm_nonneg x),
    Real.sq_rpow_div_two (norm_nonneg x)]

private lemma hasFDerivAt_regPowDeriv_one (v : E) {t : ℝ} {x : E} (hx : 0 < ‖x‖ ^ 2 + t) :
    HasFDerivAt (regPowDeriv 1 v t) (regPowDerivOneDeriv v t x) x := by
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const t).rpow_const
    (p := -1 / 2) (Or.inl hx.ne')).mul (innerSL ℝ v).hasFDerivAt
  have h32 : (-1 / 2 - 1 : ℝ) = -3 / 2 := by norm_num
  convert h using 1
  · funext y
    rw [regPowDeriv_one, Pi.mul_apply, innerSL_apply_apply, real_inner_comm]
  · ext w
    simp only [regPowDerivOneDeriv, sub_apply, add_apply, smul_apply, smul_eq_mul,
      innerSL_apply_apply, nsmul_eq_mul, h32]
    rw [real_inner_comm v x]
    ring

private lemma continuous_regPowDerivOneDeriv (v : E) {t : ℝ} (ht : 0 < t) :
    Continuous (regPowDerivOneDeriv v t) :=
  ((continuous_norm_sq_add_rpow ht _).smul continuous_const).sub
    (((continuous_norm_sq_add_rpow ht _).mul (continuous_id.inner continuous_const)).smul
      (innerSL ℝ (E := E)).continuous)

private lemma tendsto_regPowDerivOneDeriv (v : E) {x : E} (hx : x ≠ 0) :
    Tendsto (fun t ↦ regPowDerivOneDeriv v t x) (𝓝[>] 0) (𝓝 (regPowDerivOneDeriv v 0 x)) :=
  ((((continuousAt_sq_add_rpow (norm_ne_zero_iff.2 hx) _).smul continuousAt_const).sub
    (((continuousAt_sq_add_rpow (norm_ne_zero_iff.2 hx) _).mul continuousAt_const).smul
      continuousAt_const)).tendsto).mono_left nhdsWithin_le_nhds

/-- The coordinate `‖x‖⁻¹ ⟪x, v⟫` of the unit radial field is bounded by `‖v‖`. -/
theorem abs_norm_rpow_neg_one_mul_inner_le (v x : E) : |‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫| ≤ ‖v‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [abs_mul, abs_of_nonneg (by positivity), Real.rpow_neg_one]
  calc _ ≤ ‖x‖⁻¹ * (‖x‖ * ‖v‖) := by gcongr; exact abs_real_inner_le_norm x v
    _ = ‖v‖ := by field_simp

private lemma abs_regPowDeriv_one_le (v : E) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    |regPowDeriv 1 v t x| ≤ ‖v‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [regPowDeriv]
  refine (abs_regPowDeriv_le one_le_two v ht hx).trans ?_
  rw [regPowDeriv_one_zero]
  exact abs_norm_rpow_neg_one_mul_inner_le v x

private lemma norm_regPowDerivOneDeriv_le (v : E) {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : x ≠ 0) :
    ‖regPowDerivOneDeriv v t x‖ ≤ 2 * ‖v‖ * ‖x‖ ^ (-1 : ℝ) := by
  have hs : 0 < ‖x‖ ^ 2 + t := by have := norm_pos_iff.2 hx; positivity
  have h1 : (‖x‖ ^ 2 + t) ^ (-1 / 2 : ℝ) ≤ ‖x‖ ^ (-1 : ℝ) :=
    norm_sq_add_rpow_div_two_le ht hx (by norm_num)
  have h3 : (‖x‖ ^ 2 + t) ^ (-3 / 2 : ℝ) * ‖x‖ ^ 2 ≤ (‖x‖ ^ 2 + t) ^ (-1 / 2 : ℝ) := by
    calc _ ≤ (‖x‖ ^ 2 + t) ^ (-3 / 2 : ℝ) * (‖x‖ ^ 2 + t) := by gcongr; linarith
      _ = _ := by rw [← Real.rpow_add_one hs.ne']; norm_num
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_mul, innerSL_apply_norm, innerSL_apply_norm,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  calc _ ≤ (‖x‖ ^ 2 + t) ^ (-1 / 2 : ℝ) * ‖v‖ +
        (‖x‖ ^ 2 + t) ^ (-3 / 2 : ℝ) * (‖x‖ * ‖v‖) * ‖x‖ := by
        gcongr; exact abs_real_inner_le_norm x v
    _ = ‖v‖ * ((‖x‖ ^ 2 + t) ^ (-1 / 2 : ℝ) + (‖x‖ ^ 2 + t) ^ (-3 / 2 : ℝ) * ‖x‖ ^ 2) := by
        ring
    _ ≤ ‖v‖ * (2 * ‖x‖ ^ (-1 : ℝ)) := by gcongr; linarith
    _ = _ := by ring

/-- Away from the origin, the derivative `‖x‖⁻¹ ⟪v, ·⟫ - ‖x‖⁻³ ⟪x, v⟫ ⟪x, ·⟫` of the coordinate
`‖x‖⁻¹ ⟪x, v⟫` of the unit radial field has norm at most `2 ‖v‖ ‖x‖⁻¹`. -/
theorem norm_norm_rpow_neg_one_smul_innerSL_sub_le (v x : E) :
    ‖‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x‖ ≤
      2 * ‖v‖ * ‖x‖ ^ (-1 : ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [← regPowDerivOneDeriv_zero]
  exact norm_regPowDerivOneDeriv_le v le_rfl hx

end UnitRadial

private lemma locallyIntegrable_norm_rpow_neg_one_mul_inner (v : E) :
    LocallyIntegrable (fun x : E ↦ ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫) μ :=
  (locallyIntegrable_const ‖v‖).mono (by fun_prop : Measurable _).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by simpa using abs_norm_rpow_neg_one_mul_inner_le v x)

private lemma locallyIntegrable_norm_rpow_neg_one_smul_innerSL_sub
    (hd : 1 < Module.finrank ℝ E) (v : E) :
    LocallyIntegrable
      (fun x : E ↦ ‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x) μ := by
  have h := (locallyIntegrable_norm_sub_rpow (mu := μ) (s := -1)
    (by simpa using (Nat.one_lt_cast (α := ℝ)).2 hd) 0).smul (2 * ‖v‖)
  refine h.mono (by fun_prop : Measurable _).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  rw [Pi.smul_apply, zero_sub, norm_neg, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact norm_norm_rpow_neg_one_smul_innerSL_sub_le v x

private lemma hasWeakFDerivOn_regPowDeriv_one_ball (hd : 1 < Module.finrank ℝ E) (v : E) :
    HasWeakFDerivOn μ ⟨Metric.ball 0 1, Metric.isOpen_ball⟩ (fun x : E ↦ ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫)
      (fun x ↦ ‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (zero_lt_one.trans hd)
  have hd' : -(Module.finrank ℝ E : ℝ) < -1 := by
    simpa using (Nat.one_lt_cast (α := ℝ)).2 hd
  set c : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hc0 : ∀ n, 0 < c n := fun n ↦ Nat.one_div_pos_of_nat
  have hc : Tendsto c atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hc0⟩
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    (u := fun n ↦ regPowDeriv 1 v (c n)) (U := fun n ↦ regPowDerivOneDeriv v (c n))
    ((locallyIntegrable_norm_rpow_neg_one_mul_inner v).locallyIntegrableOn _)
    (fun w ↦ by
      simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
        (ContinuousLinearMap.apply ℝ ℝ w).locallyIntegrableOn_comp
          ((locallyIntegrable_norm_rpow_neg_one_smul_innerSL_sub hd v).locallyIntegrableOn _))
    (fun n ↦ ?_) ?_ ?_
  · exact hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (continuous_regPowDeriv 1 v (hc0 n)).continuousOn
      ((continuous_regPowDerivOneDeriv v (hc0 n)).locallyIntegrable.locallyIntegrableOn _)
      fun x _ ↦ hasFDerivAt_regPowDeriv_one v (by have := hc0 n; positivity)
  · simpa only [ofReal_norm, Opens.coe_mk] using
      tendsto_lintegral_norm_of_dominated_convergence
        (μ := μ.restrict (Metric.ball 0 1)) (bound := fun _ ↦ ‖v‖)
        (fun n ↦ (continuous_regPowDeriv 1 v (hc0 n)).aestronglyMeasurable)
        (integrableOn_const measure_ball_lt_top.ne).hasFiniteIntegral
        (fun n ↦ Eventually.of_forall fun x ↦ abs_regPowDeriv_one_le v (hc0 n).le x)
        (ae_restrict_of_ae <| by
          filter_upwards [μ.ae_ne 0] with x hx
          simpa only [regPowDeriv_one_zero, Function.comp_def] using
            (tendsto_regPowDeriv 1 v hx).comp hc)
  · simpa only [ofReal_norm, Opens.coe_mk] using
      tendsto_lintegral_norm_of_dominated_convergence
        (μ := μ.restrict (Metric.ball 0 1)) (bound := fun x ↦ 2 * ‖v‖ * ‖x‖ ^ (-1 : ℝ))
        (fun n ↦ (continuous_regPowDerivOneDeriv v (hc0 n)).aestronglyMeasurable)
        ((integrableOn_norm_rpow_ball (mu := μ) hd').const_mul (2 * ‖v‖)).hasFiniteIntegral
        (fun n ↦ ae_restrict_of_ae <| by
          filter_upwards [μ.ae_ne 0] with x hx
          exact norm_regPowDerivOneDeriv_le v (hc0 n).le hx)
        (ae_restrict_of_ae <| by
          filter_upwards [μ.ae_ne 0] with x hx
          simpa only [regPowDerivOneDeriv_zero, Function.comp_def] using
            (tendsto_regPowDerivOneDeriv v hx).comp hc)

/-- **The unit radial field is weakly differentiable.** If `dim E ≥ 2`, then on every open set the
classical derivative `‖x‖⁻¹ ⟪v, ·⟫ - ‖x‖⁻³ ⟪x, v⟫ ⟪x, ·⟫` of the coordinate `‖x‖⁻¹ ⟪x, v⟫` of the
unit radial field `x / ‖x‖`, which exists away from the origin, is a weak derivative of the
coordinate, although the coordinate is discontinuous at the origin. The derivative has size
`‖x‖⁻¹`, which is locally integrable exactly when `dim E ≥ 2`. -/
theorem hasWeakFDerivOn_norm_rpow_neg_one_mul_inner (hd : 1 < Module.finrank ℝ E) (v : E)
    (Ω : Opens E) :
    HasWeakFDerivOn μ Ω (fun x : E ↦ ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫)
      (fun x ↦ ‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x) := by
  have hderiv : ∀ x : E, x ≠ 0 → HasFDerivAt (fun x : E ↦ ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫)
      (‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x) x :=
    fun x hx ↦ by
      simpa only [regPowDeriv_one_zero, regPowDerivOneDeriv_zero] using
        hasFDerivAt_regPowDeriv_one (t := 0) v (by have := norm_pos_iff.2 hx; positivity)
  have hcompl : HasWeakFDerivOn μ ⟨{0}ᶜ, isOpen_compl_singleton⟩
      (fun x : E ↦ ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫)
      (fun x ↦ ‖x‖ ^ (-1 : ℝ) • innerSL ℝ v - (‖x‖ ^ (-3 : ℝ) * ⟪x, v⟫) • innerSL ℝ x) :=
    hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (fun x hx ↦ (hderiv x hx).continuousAt.continuousWithinAt)
      ((locallyIntegrable_norm_rpow_neg_one_smul_innerSL_sub hd v).locallyIntegrableOn _)
      fun x hx ↦ hderiv x hx.1
  refine ((hasWeakFDerivOn_regPowDeriv_one_ball hd v).sup hcompl).mono fun x _ ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inl (Metric.mem_ball_self one_pos)
  · exact Or.inr hx

end TauCeti
