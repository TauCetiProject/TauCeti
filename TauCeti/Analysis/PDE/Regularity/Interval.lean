/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import TauCeti.Analysis.Calculus.ContDiff.ClosedInterval
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import TauCeti.Order.Filter.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# Global Hölder estimate for divergence-form equations on an interval

On a bounded interval `(x₀, x₁)` consider the one-dimensional divergence-form equation

`-(a u')' = f + F'`

with a measurable coefficient `λ ≤ a ≤ M`, `λ > 0`, and data `f ∈ L¹` and `F ∈ Lˢ`, `1 ≤ s ≤ ∞`.
A solution is `u ∈ W^{1,p}(x₀, x₁)` with

`∫ a u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

A weak solution in `H¹(x₀, x₁)`, tested against all of `H¹₀(x₀, x₁)`, is in particular such a
solution, via the test functions `TauCeti.W1p.ofTestFunctionₗ`.

In one dimension the equation can be integrated once: the flux `a u' + F` has weak derivative `-f`,
so it equals `k - ∫_{x₀}^t f` for a constant `k`. Integrating `u' = (k - ∫ f - F) / a` over the
interval determines `k` from the endpoint values of the continuous representative `ū` of `u`. This
gives a pointwise bound for `u'` and then a Hölder bound for `ū` up to the boundary with exponent
`1 - 1 / s`, both controlled by `|ū x₀| + |ū x₁| + ‖f‖₁ + ‖F‖ₛ`. No regularity of `a` beyond
measurability is used, and the exponent is the best possible: for `a = 1`, `f = 0` the solution
is a primitive of `-F` plus an affine function, which is in general no better than
`(1 - 1 / s)`-Hölder.

## Main declarations

* `TauCeti.PDE.exists_ae_mul_gradient_add_eq_sub_intervalIntegral`: the first integral
  `a u' + F = k - ∫_{x₀}^t f`, and its converse
  `TauCeti.PDE.setIntegral_mul_deriv_eq_sub_of_ae_add_eq_sub_intervalIntegral`.
* `TauCeti.PDE.exists_contDiff_eq_intervalRepresentativeL_and_deriv_eq`: for a continuous
  nonvanishing coefficient and continuous `F`, the first integral holds pointwise and `ū` is `C¹`
  up to the boundary, with `ū' = (k - ∫_{x₀}^t f - F) / a`.
* `TauCeti.PDE.abs_add_setIntegral_inv_mul_div_le`: for `λ ≤ a ≤ M`, the bound for the constant
  `k = (δ + ∫ a⁻¹ G) / ∫ a⁻¹` of a first integral, independent of `a` beyond `λ` and `M`.
* `TauCeti.PDE.ae_abs_gradient_le_of_forall_integral_eq`: the explicit pointwise bound for `u'`.
* `TauCeti.PDE.abs_intervalRepresentativeL_sub_le_of_forall_integral_eq`: the explicit bound for
  the increments of `ū`.
* `TauCeti.PDE.abs_intervalRepresentativeL_sub_le_min_mul_div`: for equal endpoint values `g`,
  the decay `|ū y - g| ≤ min (y - x₀) (x₁ - y) * N / λ`, where `N` bounds the oscillation of
  `∫_{x₀}^t f + F`.
* `TauCeti.PDE.exists_norm_intervalRepresentativeL_le_and_holderWith`: the global estimate
  `‖ū‖_∞ + [ū]_{1 - 1 / s} ≲ |ū x₀| + |ū x₁| + ‖f‖₁ + ‖F‖ₛ`, with a constant depending only on
  the interval, `λ`, `M` and `s`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Lemma 8.1
  and Section 8.4 (one-dimensional boundary value problems).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.29 (the global Hölder estimate in every dimension).
-/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Distributions

namespace TauCeti.PDE

variable {x₀ x₁ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {a f F : ℝ → ℝ}
  {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}

/-- **The first integral of a one-dimensional divergence-form equation.** Let `a` be bounded and
measurable and `f`, `F` integrable on `(x₀, x₁)`, and let `u ∈ W^{1,p}(x₀, x₁)` solve
`-(a u')' = f + F'` in the sense of distributions on `(x₀, x₁)`. Then the flux `a u' + F` is
almost everywhere equal to `k - ∫_{x₀}^t f` for a constant `k`. -/
theorem exists_ae_mul_gradient_add_eq_sub_intervalIntegral
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁))) {M : ℝ}
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), |a t| ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∃ k, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      a t * W1p.gradient u t + F t = k - ∫ s in x₀..t, f s := by
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo x₀ x₁, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hgrad : IntegrableOn (W1p.gradient u) (Ioo x₀ x₁) :=
    (Lp.memLp (W1p.gradient u)).integrable Fact.out
  have hau : IntegrableOn (fun t => a t * W1p.gradient u t) (Ioo x₀ x₁) :=
    hgrad.bdd_mul ha (haM.mono fun t ht => by simpa using ht)
  -- The flux has weak derivative `-f`.
  have hw : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩
      (fun t => a t * W1p.gradient u t + F t) (-f) 1 := by
    refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance,
      (hau.add hF).locallyIntegrableOn, hf.neg.locallyIntegrableOn, fun φ => ?_⟩
    have hline : ∀ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 = deriv (φ : ℝ → ℝ) t := fun t =>
      (φ.contDiff.differentiable (by simp) t).lineDeriv_eq_fderiv
    have h1 := integrable_lineDeriv_smul_of_locallyIntegrableOn
      (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩) (μ := volume) hau.locallyIntegrableOn φ 1
    have h2 := integrable_lineDeriv_smul_of_locallyIntegrableOn
      (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩) (μ := volume) hF.locallyIntegrableOn φ 1
    -- Each pairing with a test function only sees `(x₀, x₁)`.
    have e1 : ∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • (a t * W1p.gradient u t) =
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t := by
      rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul]
      simp only [Opens.coe_mk, hline, smul_eq_mul, mul_comm]
    have e2 : ∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • F t = ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
      rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul]
      simp only [Opens.coe_mk, hline, smul_eq_mul, mul_comm]
    have e3 : ∫ t, (φ : ℝ → ℝ) t • f t = ∫ t in Ioo x₀ x₁, f t * φ t := by
      rw [← setIntegral_smul_eq_integral_smul]
      simp only [Opens.coe_mk, smul_eq_mul, mul_comm]
    simp only [smul_add, Pi.neg_apply, smul_neg, MeasureTheory.integral_neg, neg_neg]
    rw [integral_add h1 h2, e1, e2, e3, hu φ]
    exact sub_add_cancel _ _
  obtain ⟨k, hk⟩ := hw.exists_ae_eq_add_intervalIntegral_left hf.neg
  refine ⟨k, ?_⟩
  filter_upwards [hk] with t ht
  rw [ht, Pi.neg_def, intervalIntegral.integral_neg, sub_eq_add_neg]

/-- **The weak equation from a first integral.** Conversely to
`exists_ae_mul_gradient_add_eq_sub_intervalIntegral`, let `f` be integrable and `F` locally
integrable on `(x₀, x₁)`, and let the flux `q + F` be almost everywhere equal to `k - ∫_{x₀}^t f`
there for a constant `k`. Then `-q' = f + F'` in the sense of distributions on `(x₀, x₁)`. -/
theorem setIntegral_mul_deriv_eq_sub_of_ae_add_eq_sub_intervalIntegral
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : LocallyIntegrableOn F (Ioo x₀ x₁)) {q : ℝ → ℝ} {k : ℝ}
    (hq : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), q t + F t = k - ∫ s in x₀..t, f s)
    (φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ)) :
    ∫ t in Ioo x₀ x₁, q t * deriv φ t =
      (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  -- `k - ∫_{x₀}^t f` has weak derivative `-f`.
  have hw : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩
      (fun t => k - ∫ s in x₀..t, f s) (-f) 1 :=
    ((hasWeakLineDerivOn_const k).sub (hasWeakLineDerivOn_intervalIntegral_left hf)).congr_ae_deriv
      (EventuallyEq.of_eq (zero_sub f))
  have hkΦ : ∫ t in Ioo x₀ x₁, (k - ∫ s in x₀..t, f s) * deriv φ t =
      ∫ t in Ioo x₀ x₁, f t * φ t := by
    have e := hw.integral_lineDeriv_smul_eq_neg_integral_smul φ
    rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
      ← setIntegral_smul_eq_integral_smul] at e
    simp only [Opens.coe_mk, lineDeriv_one, smul_eq_mul, Pi.neg_apply, mul_neg,
      MeasureTheory.integral_neg, neg_neg] at e
    simpa only [mul_comm] using e
  have h1 := integrable_lineDeriv_smul_of_locallyIntegrableOn
    (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩) (μ := volume) hw.locallyIntegrableOn φ 1
  have h2 := integrable_lineDeriv_smul_of_locallyIntegrableOn
    (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩) (μ := volume) hF φ 1
  simp only [lineDeriv_one, smul_eq_mul] at h1 h2
  have hcongr : (fun t => q t * deriv φ t) =ᵐ[volume.restrict (Ioo x₀ x₁)]
      fun t => (k - ∫ s in x₀..t, f s) * deriv φ t - F t * deriv φ t := by
    filter_upwards [hq] with t ht
    rw [← ht]
    ring
  rw [integral_congr_ae hcongr, integral_sub (h1.integrableOn.congr_fun (fun t _ => mul_comm _ _)
    measurableSet_Ioo) (h2.integrableOn.congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioo),
    hkΦ]

/-- **Continuous coefficients give `C¹` solutions.** Let `a` be continuous and nonvanishing on
`[x₀, x₁]`, let `f` be integrable on `(x₀, x₁)` and `F` continuous on `[x₀, x₁]`, and let
`u ∈ W^{1,p}(x₀, x₁)` solve `-(a u')' = f + F'` in the sense of distributions. Then the continuous
representative `ū` of `u` is `C¹` up to the boundary: it agrees on `[x₀, x₁]` with a `C¹` function
`w` on `ℝ`, and for a constant `k` the first integral holds pointwise on `[x₀, x₁]`,
`w' t = (k - ∫_{x₀}^t f - F t) / a t`. -/
theorem exists_contDiff_eq_intervalRepresentativeL_and_deriv_eq (hx : x₀ < x₁)
    (ha : ContinuousOn a (Icc x₀ x₁)) (ha0 : ∀ t ∈ Icc x₀ x₁, a t ≠ 0)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : ContinuousOn F (Icc x₀ x₁))
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∃ k : ℝ, ∃ w : ℝ → ℝ, ContDiff ℝ 1 w ∧
      (∀ t : Icc x₀ x₁, W1p.intervalRepresentativeL hx u t = w t) ∧
      ∀ t ∈ Icc x₀ x₁, deriv w t = (k - (∫ s in x₀..t, f s) - F t) / a t := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  obtain ⟨k, hk⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral
    ((ha.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht =>
      (Real.norm_eq_abs _).symm.trans_le (hM t (Ioo_subset_Icc_self ht))))
    hf (hF.integrableOn_Icc.mono_set Ioo_subset_Icc_self) hu
  -- The derivative `g = (k - ∫ f - F) / a` is continuous on `[x₀, x₁]`; extend it by projection.
  set g : ℝ → ℝ := fun t => (k - (∫ s in x₀..t, f s) - F t) / a t
  have hg : ContinuousOn g (Icc x₀ x₁) :=
    ((continuousOn_const.sub
      (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
        (left_mem_Icc.2 hx.le))).sub hF).div ha ha0
  set ĝ : ℝ → ℝ := fun t => g (projIcc x₀ x₁ hx.le t)
  set x₀' : Icc x₀ x₁ := ⟨x₀, left_mem_Icc.2 hx.le⟩
  obtain ⟨hw, hdw⟩ := hg.contDiff_and_deriv_const_add_integral_comp_projIcc hx.le
    (W1p.intervalRepresentativeL hx u x₀')
  refine ⟨k, fun t => W1p.intervalRepresentativeL hx u x₀' + ∫ s in x₀..t, ĝ s, hw, fun t => ?_,
    fun t ht => ?_⟩
  · -- On `(x₀, x₁)` the weak gradient is `g` almost everywhere, by the first integral.
    have hgrad : ∀ᵐ s ∂volume.restrict (Ioo x₀ t), W1p.gradient u s = ĝ s := by
      have hk' := (ae_restrict_iff' measurableSet_Ioo).1 hk
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hk'] with s hs hst
      have hs' : s ∈ Ioo x₀ x₁ := ⟨hst.1, hst.2.trans_le t.property.2⟩
      have has := ha0 s (Ioo_subset_Icc_self hs')
      simp only [ĝ, g, projIcc_of_mem hx.le (Ioo_subset_Icc_self hs')]
      rw [eq_div_iff has, ← hs hs']
      ring
    have hĝint : ∫ s in x₀..t, W1p.gradient u s = ∫ s in x₀..t, ĝ s := by
      simp only [intervalIntegral.integral_of_le t.property.1, integral_Ioc_eq_integral_Ioo]
      exact integral_congr_ae hgrad
    have hint := W1p.integral_gradient_eq_intervalRepresentativeL_sub hx u x₀' t
    rw [hĝint] at hint
    simp only [hint, add_sub_cancel]
  · rw [hdw]
    simp only [g, projIcc_of_mem hx.le ht]

/-- **The constant of a first integral is bounded independently of the coefficient.** If
`λ ≤ a ≤ M` almost everywhere on `(x₀, x₁)`, with `λ > 0`, and `G` is integrable there, then
`|(δ + ∫ a⁻¹ G) / ∫ a⁻¹| ≤ M / (x₁ - x₀) * (|δ| + λ⁻¹ ∫ |G|)` for every `δ`, all integrals being
over `(x₀, x₁)`. -/
theorem abs_add_setIntegral_inv_mul_div_le (hx : x₀ < x₁) {lam M : ℝ} (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M) {G : ℝ → ℝ}
    (hG : IntegrableOn G (Ioo x₀ x₁)) (δ : ℝ) :
    |(δ + ∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t) / ∫ t in Ioo x₀ x₁, (a t)⁻¹| ≤
      M / (x₁ - x₀) * (|δ| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t|) := by
  have hI0 : volume (Ioo x₀ x₁) ≠ 0 := by simp [hx]
  have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 hI0
  have hM : 0 < M := hlam.trans_le (le_of_eventually_le_and_le haM)
  have hD0 := setIntegral_inv_pos hI0 measure_Ioo_lt_top.ne hlam ha (haM.mono fun _ ht => ht.1)
  have hD := div_le_setIntegral_inv measure_Ioo_lt_top.ne hlam ha haM
  rw [Real.volume_real_Ioo_of_le hx.le] at hD
  -- `|∫ a⁻¹ G| ≤ λ⁻¹ ∫ |G|`.
  have hN : |∫ t in Ioo x₀ x₁, (a t)⁻¹ * G t| ≤ lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t| := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hG.abs.const_mul _) ?_
    filter_upwards [(haM.mono fun _ ht => ht.1).norm_inv_le_inv hlam] with t ht
    rw [norm_mul, Real.norm_eq_abs (G t)]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  rw [abs_div, abs_of_pos hD0, div_le_iff₀ hD0]
  calc _ ≤ |δ| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t| := (abs_add_le _ _).trans (by gcongr)
    _ = M / (x₁ - x₀) * (|δ| + lam⁻¹ * ∫ t in Ioo x₀ x₁, |G t|) * ((x₁ - x₀) / M) := by
        field_simp [(sub_pos.2 hx).ne']
    _ ≤ _ := by gcongr

/-- Integrating the first integral `a u' + F = k - Φ` over `(x₀, x₁)`, after dividing by `a`:
`k ∫ a⁻¹ = ū x₁ - ū x₀ + ∫ a⁻¹ (Φ + F)`. So the constant `k` is determined by the endpoint values
of `u`. -/
theorem mul_setIntegral_inv_eq (hx : x₀ < x₁) {lam : ℝ} (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hlama : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) (hF : IntegrableOn F (Ioo x₀ x₁))
    {Φ : ℝ → ℝ} (hΦ : IntegrableOn Φ (Ioo x₀ x₁)) {k : ℝ}
    (hk : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), a t * W1p.gradient u t + F t = k - Φ t) :
    k * ∫ t in Ioo x₀ x₁, (a t)⁻¹ = (W1p.intervalTraceL hx u).2 - (W1p.intervalTraceL hx u).1 +
      ∫ t in Ioo x₀ x₁, (a t)⁻¹ * (Φ t + F t) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hinv := hlama.norm_inv_le_inv hlam
  have hgrad : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      W1p.gradient u t = k * (a t)⁻¹ - (a t)⁻¹ * (Φ t + F t) := by
    filter_upwards [hk, hlama] with t ht hat
    have ha0 : a t ≠ 0 := (hlam.trans_le hat).ne'
    field_simp
    linarith
  have h1 : Integrable (fun t => k * (a t)⁻¹) (volume.restrict (Ioo x₀ x₁)) :=
    (Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _ hinv).const_mul k
  have h2 : Integrable (fun t => (a t)⁻¹ * (Φ t + F t)) (volume.restrict (Ioo x₀ x₁)) :=
    (hΦ.add hF).bdd_mul ha.aemeasurable.inv.aestronglyMeasurable hinv
  rw [W1p.intervalTraceL_apply,
    ← W1p.setIntegral_Ioo_gradient_eq_intervalRepresentativeL_sub hx u (s := ⟨x₀, _⟩) (t := ⟨x₁, _⟩)
      hx.le, integral_congr_ae hgrad, integral_sub h1 h2, integral_const_mul]
  ring

/-- The constant `k` of the first integral `a u' + F = k - Φ`, where `|Φ| ≤ N` on `(x₀, x₁)`, is
bounded by `M / (x₁ - x₀) * (|ū x₁ - ū x₀| + ((x₁ - x₀) N + ‖F‖₁) / λ)`, since `∫ a⁻¹` is at least
`(x₁ - x₀) / M`. -/
private theorem abs_le_of_ae_mul_gradient_add_eq (hx : x₀ < x₁) {lam M : ℝ} (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hF : IntegrableOn F (Ioo x₀ x₁)) {Φ : ℝ → ℝ} {N : ℝ} (hΦi : IntegrableOn Φ (Ioo x₀ x₁))
    (hΦ : ∀ t ∈ Ioo x₀ x₁, |Φ t| ≤ N) {k : ℝ}
    (hk : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), a t * W1p.gradient u t + F t = k - Φ t) :
    |k| ≤ M / (x₁ - x₀) * (|(W1p.intervalTraceL hx u).2 - (W1p.intervalTraceL hx u).1| +
      ((x₁ - x₀) * N + ∫ t in Ioo x₀ x₁, |F t|) / lam) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hI0 : volume (Ioo x₀ x₁) ≠ 0 := by simp [hx]
  have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 hI0
  have hM : 0 < M := hlam.trans_le (le_of_eventually_le_and_le haM)
  have hkA := mul_setIntegral_inv_eq hx hlam ha (haM.mono fun _ ht => ht.1) hF hΦi hk
  rw [← eq_div_iff (setIntegral_inv_pos hI0 measure_Ioo_lt_top.ne hlam ha
    (haM.mono fun _ ht => ht.1)).ne'] at hkA
  -- `∫ |Φ + F| ≤ (x₁ - x₀) N + ‖F‖₁`.
  have hR : ∫ t in Ioo x₀ x₁, |Φ t + F t| ≤ (x₁ - x₀) * N + ∫ t in Ioo x₀ x₁, |F t| := by
    calc ∫ t in Ioo x₀ x₁, |Φ t + F t| ≤ ∫ t in Ioo x₀ x₁, (N + |F t|) :=
          setIntegral_mono_on (hΦi.add hF).abs ((integrable_const N).add hF.abs) measurableSet_Ioo
            fun t ht => (abs_add_le _ _).trans (add_le_add_left (hΦ t ht) _)
      _ = _ := by
          rw [integral_add (integrable_const _) hF.abs, setIntegral_const,
            Real.volume_real_Ioo_of_le hx.le, smul_eq_mul]
  rw [hkA]
  refine (abs_add_setIntegral_inv_mul_div_le hx hlam ha haM (G := fun t => Φ t + F t)
    (hΦi.add hF) _).trans ?_
  rw [inv_mul_eq_div]
  have : 0 ≤ M / (x₁ - x₀) := (div_pos hM (sub_pos.2 hx)).le
  gcongr

/-- **The derivative of a solution is bounded by the data.** Let `λ ≤ a ≤ M` almost everywhere on
`(x₀, x₁)`, with `λ > 0`, let `f` and `F` be integrable there, and let `u ∈ W^{1,p}(x₀, x₁)` solve
`-(a u')' = f + F'` in the sense of distributions. Then, almost everywhere,
`|u'(t)| ≤ K + |F t| / λ` with

`K = (M / (x₁ - x₀) * (|u(x₁) - u(x₀)| + ((x₁ - x₀) ‖f‖₁ + ‖F‖₁) / λ) + ‖f‖₁) / λ`,

where `u(x₀)` and `u(x₁)` are the endpoint values of the continuous representative and the `L¹`
norms are over `(x₀, x₁)`. -/
theorem ae_abs_gradient_le_of_forall_integral_eq (hx : x₀ < x₁) {lam M : ℝ} (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), |W1p.gradient u t| ≤
      (M / (x₁ - x₀) * (|(W1p.intervalTraceL hx u).2 - (W1p.intervalTraceL hx u).1| +
          ((x₁ - x₀) * (∫ s in Ioo x₀ x₁, |f s|) + ∫ s in Ioo x₀ x₁, |F s|) / lam) +
        ∫ s in Ioo x₀ x₁, |f s|) / lam + |F t| / lam := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  obtain ⟨k, hk⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral ha
    (haM.mono fun t ht => abs_le.2 ⟨by linarith [ht.1], ht.2⟩) hf hF hu
  -- The primitive `Φ` of `f` from `x₀` is bounded by `‖f‖₁` on `(x₀, x₁)`, hence integrable there.
  have hΦ : ∀ t ∈ Ioo x₀ x₁, |∫ s in x₀..t, f s| ≤ ∫ s in Ioo x₀ x₁, |f s| := fun t ht => by
    refine (intervalIntegral.abs_integral_le_integral_abs ht.1.le).trans ?_
    rw [intervalIntegral.integral_of_le ht.1.le]
    exact setIntegral_mono_set hf.abs (ae_of_all _ fun _ => abs_nonneg _)
      (Ioc_subset_Ioo_right ht.2).eventuallySubset
  have hΦi : IntegrableOn (fun t => ∫ s in x₀..t, f s) (Ioo x₀ x₁) :=
    TauCeti.intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hf (left_mem_Icc.2 hx.le)
  have hkle := abs_le_of_ae_mul_gradient_add_eq hx hlam ha haM hF hΦi hΦ hk
  -- Solving the first integral for `u'` gives the bound.
  filter_upwards [hk, haM, ae_restrict_mem measurableSet_Ioo] with t ht hat htI
  have hat0 : 0 < a t := hlam.trans_le hat.1
  have hgt : W1p.gradient u t = (k - (∫ s in x₀..t, f s) - F t) / a t := by
    rw [eq_div_iff hat0.ne']
    linarith
  have hnum : |k - (∫ s in x₀..t, f s) - F t| ≤
      M / (x₁ - x₀) * (|(W1p.intervalTraceL hx u).2 - (W1p.intervalTraceL hx u).1| +
        ((x₁ - x₀) * (∫ s in Ioo x₀ x₁, |f s|) + ∫ s in Ioo x₀ x₁, |F s|) / lam) +
          (∫ s in Ioo x₀ x₁, |f s|) + |F t| :=
    calc |k - (∫ s in x₀..t, f s) - F t| ≤ |k| + |∫ s in x₀..t, f s| + |F t| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ _ := by gcongr; exact hΦ t htI
  rw [hgt, abs_div, abs_of_pos hat0, ← add_div]
  exact div_le_div₀ ((abs_nonneg _).trans hnum) hnum hlam hat.1

/-- **Hölder increments of a solution.** Under the hypotheses of
`TauCeti.PDE.ae_abs_gradient_le_of_forall_integral_eq`, with now `F ∈ Lˢ(x₀, x₁)` for some
`1 ≤ s ≤ ∞`, the continuous representative `ū` of `u` satisfies, for all `y, z ∈ [x₀, x₁]`,

`|ū z - ū y| ≤ K |z - y| + ‖F‖ₛ / λ * |z - y| ^ (1 - 1 / s)`,

with `K = (M / (x₁ - x₀) * (|ū x₁ - ū x₀| + ((x₁ - x₀) ‖f‖₁ + ‖F‖₁) / λ) + ‖f‖₁) / λ`. At `s = ∞`
the exponent is `1` (`1 / s.toReal` is then `0`). -/
theorem abs_intervalRepresentativeL_sub_le_of_forall_integral_eq (hx : x₀ < x₁) {lam M : ℝ}
    (hlam : 0 < lam) (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) {s : ℝ≥0∞} (hs : 1 ≤ s)
    (hF : MemLp F s (volume.restrict (Ioo x₀ x₁)))
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    (y z : Icc x₀ x₁) :
    |W1p.intervalRepresentativeL hx u z - W1p.intervalRepresentativeL hx u y| ≤
      (M / (x₁ - x₀) * (|(W1p.intervalTraceL hx u).2 - (W1p.intervalTraceL hx u).1| +
          ((x₁ - x₀) * (∫ t in Ioo x₀ x₁, |f t|) + ∫ t in Ioo x₀ x₁, |F t|) / lam) +
        ∫ t in Ioo x₀ x₁, |f t|) / lam * |(z : ℝ) - y| +
      (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal / lam *
        |(z : ℝ) - y| ^ (1 - 1 / s.toReal) := by
  wlog hyz : (y : ℝ) ≤ z generalizing y z
  · rw [abs_sub_comm, abs_sub_comm (z : ℝ)]
    exact this z y (le_of_not_ge hyz)
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo x₀ x₁, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have : IsFiniteMeasure (volume.restrict (Ioo (y : ℝ) z)) := Real.isFiniteMeasure_restrict_Ioo _ _
  have : Fact (1 ≤ s) := ⟨hs⟩
  have hsub : Ioo (y : ℝ) z ⊆ Ioo x₀ x₁ := Ioo_subset_Ioo y.property.1 z.property.2
  have hFi : IntegrableOn F (Ioo x₀ x₁) := hF.integrable hs
  set K := (M / (x₁ - x₀) * (|(W1p.intervalTraceL hx u).2 - (W1p.intervalTraceL hx u).1| +
      ((x₁ - x₀) * (∫ t in Ioo x₀ x₁, |f t|) + ∫ t in Ioo x₀ x₁, |F t|) / lam) +
    ∫ t in Ioo x₀ x₁, |f t|) / lam
  have hbound := ae_restrict_of_ae_restrict_of_subset hsub
    (ae_abs_gradient_le_of_forall_integral_eq hx hlam ha haM hf hFi hu)
  have hgrad : IntegrableOn (W1p.gradient u) (Ioo x₀ x₁) :=
    (Lp.memLp (W1p.gradient u)).integrable Fact.out
  -- The `L¹` norm of `F` on `(y, z)` is controlled by Hölder's inequality.
  have hFyz : MemLp F s (volume.restrict (Ioo (y : ℝ) z)) :=
    hF.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hF1 : ∫ t in Ioo (y : ℝ) z, |F t| ≤ ((z : ℝ) - y) ^ (1 - 1 / s.toReal) *
      (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal := by
    have h := hFyz.integral_norm_le_mul_eLpNorm hs
    simp only [Real.norm_eq_abs] at h
    rw [Measure.restrict_apply_univ, Real.volume_Ioo, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (sub_nonneg.2 hyz)] at h
    refine h.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hF.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)))
      (Real.rpow_nonneg (sub_nonneg.2 hyz) _))
  rw [← W1p.setIntegral_Ioo_gradient_eq_intervalRepresentativeL_sub hx u hyz,
    abs_of_nonneg (sub_nonneg.2 hyz)]
  calc |∫ t in Ioo (y : ℝ) z, W1p.gradient u t|
      ≤ ∫ t in Ioo (y : ℝ) z, |W1p.gradient u t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioo (y : ℝ) z, (K + |F t| / lam) :=
        integral_mono_ae (hgrad.mono_set hsub).abs
          ((integrable_const K).add ((hFyz.integrable hs).abs.div_const lam))
          hbound
    _ = K * ((z : ℝ) - y) + (∫ t in Ioo (y : ℝ) z, |F t|) / lam := by
        rw [integral_add (integrable_const K) ((hFyz.integrable hs).abs.div_const lam),
          setIntegral_const, Real.volume_real_Ioo_of_le hyz, smul_eq_mul, integral_div, mul_comm]
    _ ≤ K * ((z : ℝ) - y) + (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal / lam *
          ((z : ℝ) - y) ^ (1 - 1 / s.toReal) := by
        refine add_le_add le_rfl ?_
        rw [div_mul_eq_mul_div, mul_comm (eLpNorm F s _).toReal]
        exact div_le_div_of_nonneg_right hF1 hlam.le

/-- The constant of `TauCeti.PDE.abs_intervalRepresentativeL_sub_le_of_forall_integral_eq` is at
most `c (|T₀| + |T₁| + N_f + N)`, with `c` depending only on `L`, `λ`, `M` and `β`, when the `L¹`
norm `N_F` is at most `L ^ β N`. -/
private theorem div_le_mul_add_add_add {L lam M β T₀ T₁ Nf NF N : ℝ} (hL : 0 < L) (hlam : 0 < lam)
    (hNf : 0 ≤ Nf) (hNF0 : 0 ≤ NF) (hN : 0 ≤ N) (hNF : NF ≤ L ^ β * N) :
    (M / L * (|T₁ - T₀| + (L * Nf + NF) / lam) + Nf) / lam ≤
      (|M| / L * (1 + (L + L ^ β) / lam) + 1) / lam * (|T₀| + |T₁| + Nf + N) := by
  set B := |T₀| + |T₁| + Nf + N
  have hD : |T₁ - T₀| ≤ B := (abs_sub _ _).trans (by linarith [abs_nonneg T₀, abs_nonneg T₁])
  have hNfB : Nf ≤ B := by linarith [abs_nonneg T₀, abs_nonneg T₁]
  have hNFB : NF ≤ L ^ β * B :=
    hNF.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg T₀, abs_nonneg T₁])
      (by positivity))
  have hX : |T₁ - T₀| + (L * Nf + NF) / lam ≤ B + (L * B + L ^ β * B) / lam := by gcongr
  have hMX : M / L * (|T₁ - T₀| + (L * Nf + NF) / lam) ≤
      |M| / L * (B + (L * B + L ^ β * B) / lam) :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self M) hL.le)
      (by positivity)).trans (mul_le_mul_of_nonneg_left hX (by positivity))
  calc _ ≤ (|M| / L * (B + (L * B + L ^ β * B) / lam) + B) / lam :=
        div_le_div_of_nonneg_right (add_le_add hMX hNfB) hlam.le
    _ = _ := by field_simp

/-- The increments of `ū` in terms of `B = |ū x₀| + |ū x₁| + ‖f‖₁ + ‖F‖ₛ`, with an explicit
constant depending only on `x₀`, `x₁`, `λ`, `M` and `s`. -/
private theorem abs_intervalRepresentativeL_sub_le_mul_rpow (hx : x₀ < x₁) {lam M : ℝ}
    (hlam : 0 < lam) (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) {s : ℝ≥0∞} (hs : 1 ≤ s)
    (hF : MemLp F s (volume.restrict (Ioo x₀ x₁)))
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    (y z : Icc x₀ x₁) :
    |W1p.intervalRepresentativeL hx u z - W1p.intervalRepresentativeL hx u y| ≤
      ((|M| / (x₁ - x₀) * (1 + ((x₁ - x₀) + (x₁ - x₀) ^ (1 - 1 / s.toReal)) / lam) + 1) / lam *
          (x₁ - x₀) ^ (1 / s.toReal) + 1 / lam) *
        (|(W1p.intervalTraceL hx u).1| + |(W1p.intervalTraceL hx u).2| +
          (∫ t in Ioo x₀ x₁, |f t|) + (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal) *
        |(z : ℝ) - y| ^ (1 - 1 / s.toReal) := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have hL : 0 < x₁ - x₀ := sub_pos.2 hx
  -- Hölder's inequality: `‖F‖₁ ≤ (x₁ - x₀) ^ (1 - 1 / s) ‖F‖ₛ`.
  have hNF : ∫ t in Ioo x₀ x₁, |F t| ≤
      (x₁ - x₀) ^ (1 - 1 / s.toReal) * (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal := by
    have h := hF.integral_norm_le_mul_eLpNorm hs
    simp only [Real.norm_eq_abs] at h
    rwa [Measure.restrict_apply_univ, Real.volume_Ioo, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hL.le] at h
  have hK := div_le_mul_add_add_add (M := M) (T₀ := (W1p.intervalTraceL hx u).1)
    (T₁ := (W1p.intervalTraceL hx u).2) (Nf := ∫ t in Ioo x₀ x₁, |f t|) hL hlam
    (integral_nonneg fun t => abs_nonneg (f t)) (integral_nonneg fun t => abs_nonneg (F t))
    ENNReal.toReal_nonneg hNF
  -- `|z - y| ≤ (x₁ - x₀) ^ (1 / s) |z - y| ^ (1 - 1 / s)`, since `|z - y| ≤ x₁ - x₀`.
  have hsplit :
      |(z : ℝ) - y| ≤ (x₁ - x₀) ^ (1 / s.toReal) * |(z : ℝ) - y| ^ (1 - 1 / s.toReal) := by
    calc |(z : ℝ) - y| = |(z : ℝ) - y| ^ (1 / s.toReal) * |(z : ℝ) - y| ^ (1 - 1 / s.toReal) := by
          rw [← Real.rpow_add' (abs_nonneg _) (by norm_num), add_sub_cancel, Real.rpow_one]
      _ ≤ _ := by
          gcongr; exact abs_sub_le_of_le_of_le z.property.1 z.property.2 y.property.1 y.property.2
  refine (abs_intervalRepresentativeL_sub_le_of_forall_integral_eq hx hlam ha haM hf hs hF hu
    y z).trans ?_
  have hFB : (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal ≤
      |(W1p.intervalTraceL hx u).1| + |(W1p.intervalTraceL hx u).2| +
        (∫ t in Ioo x₀ x₁, |f t|) + (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal :=
    le_add_of_nonneg_left (by
      have : 0 ≤ ∫ t in Ioo x₀ x₁, |f t| := integral_nonneg fun t => abs_nonneg (f t)
      positivity)
  set B := |(W1p.intervalTraceL hx u).1| + |(W1p.intervalTraceL hx u).2| +
    (∫ t in Ioo x₀ x₁, |f t|) + (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal
  set c := (|M| / (x₁ - x₀) * (1 + ((x₁ - x₀) + (x₁ - x₀) ^ (1 - 1 / s.toReal)) / lam) + 1) / lam
  calc _ ≤ c * B * ((x₁ - x₀) ^ (1 / s.toReal) * |(z : ℝ) - y| ^ (1 - 1 / s.toReal)) +
        B / lam * |(z : ℝ) - y| ^ (1 - 1 / s.toReal) := by gcongr
    _ = _ := by ring

/-- Let `v a = k - G` almost everywhere on `(x₀, x₁)`, with `λ ≤ a ≤ M` and `G` in `[m, m + N]`,
and let `v` have integral zero over `(x₀, x₁)`, as the derivative `v = u'` of a solution with equal
endpoint values does. Then `|v| ≤ N / λ`: the flux constant `k` lies in `[m, m + N]`, since
otherwise `v` would have a fixed sign and a nonzero integral. -/
private theorem ae_abs_le_div_of_integral_eq_zero (hx : x₀ < x₁) {lam M : ℝ} (hlam : 0 < lam)
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M) {v G : ℝ → ℝ} {k m N : ℝ}
    (hv : IntegrableOn v (Ioo x₀ x₁)) (hint : ∫ t in Ioo x₀ x₁, v t = 0)
    (hva : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), v t * a t = k - G t)
    (hG : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), m ≤ G t ∧ G t ≤ m + N) :
    ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), |v t| ≤ N / lam := by
  have : IsFiniteMeasure (volume.restrict (Ioo x₀ x₁)) := Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 (by simp [hx])
  have hM : 0 < M := hlam.trans_le (le_of_eventually_le_and_le haM)
  -- A function bounded away from zero with a fixed sign has nonzero integral over `(x₀, x₁)`.
  have hvol : (volume.restrict (Ioo x₀ x₁)).real univ = x₁ - x₀ := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le hx.le]
  have hpos : ∀ c, 0 < c → ¬∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), c ≤ v t := fun c hc h => by
    have hle := integral_mono_ae (integrable_const c) hv h
    rw [hint, integral_const, smul_eq_mul, hvol] at hle
    nlinarith [sub_pos.2 hx]
  have hneg : ∀ c, 0 < c → ¬∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), v t ≤ -c := fun c hc h => by
    have hle := integral_mono_ae hv (integrable_const (-c)) h
    rw [hint, integral_const, smul_eq_mul, hvol] at hle
    nlinarith [sub_pos.2 hx]
  -- The flux constant lies in `[m, m + N]`.
  have hk₁ : k ≤ m + N := by
    by_contra! hlt
    refine hpos ((k - (m + N)) / M) (div_pos (sub_pos.2 hlt) hM) ?_
    filter_upwards [hva, hG, haM] with t ht htG hat
    have hv0 : 0 < v t := by nlinarith [hlam.trans_le hat.1]
    rw [div_le_iff₀ hM]
    nlinarith [mul_le_mul_of_nonneg_left hat.2 hv0.le]
  have hk₀ : m ≤ k := by
    by_contra! hlt
    refine hneg ((m - k) / M) (div_pos (sub_pos.2 hlt) hM) ?_
    filter_upwards [hva, hG, haM] with t ht htG hat
    have hv0 : v t < 0 := by nlinarith [hlam.trans_le hat.1]
    rw [← neg_div, le_div_iff₀ hM]
    nlinarith [mul_le_mul_of_nonpos_left hat.2 hv0.le]
  filter_upwards [hva, hG, haM] with t ht htG hat
  have hat0 : 0 < a t := hlam.trans_le hat.1
  have h1 : |v t| * a t ≤ N := by
    rw [← abs_of_pos hat0, ← abs_mul, ht, abs_le]
    constructor <;> linarith
  rw [le_div_iff₀ hlam]
  exact (mul_le_mul_of_nonneg_left hat.1 (abs_nonneg _)).trans h1

/-- **Decay towards equal boundary values.** Let `λ ≤ a ≤ M` almost everywhere on `(x₀, x₁)`, with
`λ > 0`, let `f` and `F` be integrable there, and let `u ∈ W^{1,p}(x₀, x₁)` solve
`-(a u')' = f + F'` in the sense of distributions, with the same value `g` at both endpoints. If
`G t = ∫_{x₀}^t f + F t` lies in an interval `[m, m + N]` for almost every `t ∈ (x₀, x₁)`, then
the continuous representative `ū` satisfies

`|ū y - g| ≤ min (y - x₀) (x₁ - y) * N / λ` for every `y ∈ [x₀, x₁]`,

so `|ū - g| ≤ (x₁ - x₀) N / (2 λ)`. For instance, for `f ≥ 0` and `F = 0` one may take `m = 0`
and `N = ‖f‖₁`. The upper bound `M` on `a` does not enter the estimate. -/
theorem abs_intervalRepresentativeL_sub_le_min_mul_div (hx : x₀ < x₁) {lam M : ℝ}
    (hlam : 0 < lam) (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    {g : ℝ} (htr : W1p.intervalTraceL hx u = (g, g)) {m N : ℝ}
    (hG : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      m ≤ (∫ s in x₀..t, f s) + F t ∧ (∫ s in x₀..t, f s) + F t ≤ m + N)
    (y : Icc x₀ x₁) :
    |W1p.intervalRepresentativeL hx u y - g| ≤ min ((y : ℝ) - x₀) (x₁ - y) * N / lam := by
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo x₀ x₁, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo x₀ x₁
  have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 (by simp [hx])
  obtain ⟨k, hk⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral ha
    (haM.mono fun t ht => abs_le.2 ⟨by linarith [ht.1], ht.2⟩) hf hF hu
  rw [W1p.intervalTraceL_apply, Prod.mk.injEq] at htr
  have hgi : IntegrableOn (W1p.gradient u) (Ioo x₀ x₁) :=
    (Lp.memLp (W1p.gradient u)).integrable Fact.out
  have hint : ∫ t in Ioo x₀ x₁, W1p.gradient u t = 0 := by
    rw [W1p.setIntegral_Ioo_gradient_eq_intervalRepresentativeL_sub hx u
      (s := ⟨x₀, left_mem_Icc.2 hx.le⟩) (t := ⟨x₁, right_mem_Icc.2 hx.le⟩) hx.le, htr.1, htr.2,
      sub_self]
  have hbound := ae_abs_le_div_of_integral_eq_zero hx hlam haM hgi hint
    (hk.mono fun t ht => by linarith) hG
  have hN : 0 ≤ N / lam := by
    obtain ⟨t, ht⟩ := hbound.exists
    exact (abs_nonneg _).trans ht
  -- Integrating `|u'| ≤ N / λ` from either endpoint.
  have hI : ∀ c d : Icc x₀ x₁, (c : ℝ) ≤ d → |W1p.intervalRepresentativeL hx u d -
      W1p.intervalRepresentativeL hx u c| ≤ ((d : ℝ) - c) * (N / lam) := fun c d hcd => by
    rw [← W1p.setIntegral_Ioo_gradient_eq_intervalRepresentativeL_sub hx u hcd, ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const_ae measure_Ioo_lt_top
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo c.property.1 d.property.2)
        (hbound.mono fun t ht => (Real.norm_eq_abs _).trans_le ht))).trans_eq ?_
    rw [Real.volume_real_Ioo_of_le hcd, mul_comm]
  have hl := hI ⟨x₀, left_mem_Icc.2 hx.le⟩ y y.property.1
  have hr := hI y ⟨x₁, right_mem_Icc.2 hx.le⟩ y.property.2
  rw [htr.1] at hl
  rw [htr.2, abs_sub_comm] at hr
  rw [mul_div_assoc, min_mul_of_nonneg _ _ hN]
  exact le_min hl hr

/-- **Global Hölder estimate on an interval.** Let `x₀ < x₁`, `0 < λ` and `1 ≤ s ≤ ∞`. There is a
constant `C > 0`, depending only on `x₀`, `x₁`, `λ`, `M` and `s`, with the following property. Let
`a` be measurable with `λ ≤ a ≤ M`, let `f ∈ L¹(x₀, x₁)` and `F ∈ Lˢ(x₀, x₁)`, and let
`u ∈ W^{1,p}(x₀, x₁)` solve `-(a u')' = f + F'` in the sense of distributions. Then the continuous
representative `ū ∈ C([x₀, x₁])` of `u` satisfies

`‖ū‖_∞ ≤ C B` and `|ū y - ū z| ≤ C B |y - z| ^ (1 - 1 / s)`,

where `B = |ū x₀| + |ū x₁| + ‖f‖₁ + ‖F‖ₛ`. So the solution is `(1 - 1 / s)`-Hölder up to the
boundary, with norm controlled by its boundary values and the data; at `s = ∞` it is Lipschitz. -/
theorem exists_norm_intervalRepresentativeL_le_and_holderWith (hx : x₀ < x₁) {lam M : ℝ}
    (hlam : 0 < lam) {s : ℝ≥0∞} (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a f F : ℝ → ℝ} {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p},
      AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)) →
      (∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M) →
      IntegrableOn f (Ioo x₀ x₁) → MemLp F s (volume.restrict (Ioo x₀ x₁)) →
      (∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) →
      ‖W1p.intervalRepresentativeL hx u‖ ≤
          C * (|(W1p.intervalTraceL hx u).1| + |(W1p.intervalTraceL hx u).2| +
            (∫ t in Ioo x₀ x₁, |f t|) + (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal) ∧
        HolderWith (C * (|(W1p.intervalTraceL hx u).1| + |(W1p.intervalTraceL hx u).2| +
            (∫ t in Ioo x₀ x₁, |f t|) +
              (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal)).toNNReal
          (1 - s.toNNReal⁻¹) (W1p.intervalRepresentativeL hx u) := by
  -- The Hölder exponent `β = 1 - 1 / s` lies in `[0, 1]`.
  have hinv : s.toNNReal⁻¹ ≤ 1 := by
    rcases eq_or_ne s ⊤ with rfl | hs'
    · simp
    · exact inv_le_one_of_one_le₀ (by simpa using ENNReal.toNNReal_mono hs' hs)
  have hβ : ((1 - s.toNNReal⁻¹ : ℝ≥0) : ℝ) = 1 - 1 / s.toReal := by
    rw [NNReal.coe_sub hinv, NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal, NNReal.coe_one,
      one_div]
  have hβ0 : 0 ≤ 1 - 1 / s.toReal := by rw [← hβ]; exact NNReal.coe_nonneg _
  set c := (|M| / (x₁ - x₀) * (1 + ((x₁ - x₀) + (x₁ - x₀) ^ (1 - 1 / s.toReal)) / lam) + 1) /
    lam * (x₁ - x₀) ^ (1 / s.toReal) + 1 / lam
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c + 1 + c * (x₁ - x₀) ^ (1 - 1 / s.toReal), by positivity, ?_⟩
  intro a f F u ha haM hf hF hu
  set ū := W1p.intervalRepresentativeL hx u
  set B := |(W1p.intervalTraceL hx u).1| + |(W1p.intervalTraceL hx u).2| +
    (∫ t in Ioo x₀ x₁, |f t|) + (eLpNorm F s (volume.restrict (Ioo x₀ x₁))).toReal with hB
  have hinc := abs_intervalRepresentativeL_sub_le_mul_rpow hx hlam ha haM hf hs hF hu
  have hcC : c ≤ c + 1 + c * (x₁ - x₀) ^ (1 - 1 / s.toReal) :=
    le_add_of_nonneg_right (by positivity) |>.trans' (le_add_of_nonneg_right zero_le_one)
  refine ⟨(ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_,
    holderOnWith_univ.1 (HolderOnWith.of_dist_le fun y _ z _ => ?_)⟩
  · -- The supremum bound, from the value at `x₀` and the Hölder bound.
    have h0 := hinc ⟨x₀, left_mem_Icc.2 hx.le⟩ t
    have hpow : |(t : ℝ) - x₀| ^ (1 - 1 / s.toReal) ≤ (x₁ - x₀) ^ (1 - 1 / s.toReal) :=
      Real.rpow_le_rpow (abs_nonneg _) (abs_sub_le_of_le_of_le t.property.1 t.property.2 le_rfl
          hx.le) hβ0
    have h1 : |ū ⟨x₀, left_mem_Icc.2 hx.le⟩| ≤ B := by
      simp only [hB, W1p.intervalTraceL_apply]
      have : 0 ≤ ∫ t in Ioo x₀ x₁, |f t| := integral_nonneg fun t => abs_nonneg (f t)
      linarith [abs_nonneg (ū ⟨x₁, right_mem_Icc.2 hx.le⟩),
        ENNReal.toReal_nonneg (a := eLpNorm F s (volume.restrict (Ioo x₀ x₁)))]
    calc ‖ū t‖ = |ū ⟨x₀, left_mem_Icc.2 hx.le⟩ + (ū t - ū ⟨x₀, left_mem_Icc.2 hx.le⟩)| := by
          rw [Real.norm_eq_abs, add_sub_cancel]
      _ ≤ B + c * B * (x₁ - x₀) ^ (1 - 1 / s.toReal) :=
          (abs_add_le _ _).trans (add_le_add h1 (h0.trans (by gcongr)))
      _ = (1 + c * (x₁ - x₀) ^ (1 - 1 / s.toReal)) * B := by ring
      _ ≤ _ := by gcongr; linarith
  · rw [Real.coe_toNNReal _ (by positivity), hβ, Real.dist_eq, Subtype.dist_eq, Real.dist_eq,
      abs_sub_comm (y : ℝ), abs_sub_comm (ū y)]
    exact (hinc y z).trans (by gcongr)

end TauCeti.PDE
