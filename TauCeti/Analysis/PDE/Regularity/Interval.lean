/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
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
* `TauCeti.PDE.abs_add_setIntegral_inv_mul_div_le`: for `λ ≤ a ≤ M`, the bound for the constant
  `k = (δ + ∫ a⁻¹ G) / ∫ a⁻¹` of a first integral, independent of `a` beyond `λ` and `M`.
* `TauCeti.PDE.ae_abs_gradient_le_of_forall_integral_eq`: the explicit pointwise bound for `u'`.
* `TauCeti.PDE.abs_intervalRepresentativeL_sub_le_of_forall_integral_eq`: the explicit bound for
  the increments of `ū`.
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
`k ∫ a⁻¹ = ū x₁ - ū x₀ + ∫ a⁻¹ (Φ + F)`. -/
private theorem mul_setIntegral_inv_eq (hx : x₀ < x₁) {lam : ℝ} (hlam : 0 < lam)
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
  rw [W1p.intervalTraceL_apply, ← W1p.integral_gradient_eq_intervalRepresentativeL_sub,
    intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo, integral_congr_ae hgrad,
    integral_sub h1 h2, integral_const_mul]
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
    Integrable.of_bound
      (((TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hf
        (left_mem_Icc.2 hx.le)).mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
      _ ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (Real.norm_eq_abs _).le.trans
        (hΦ t ht))
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
  have hsub : Ioo (y : ℝ) z ⊆ Ioo x₀ x₁ := Ioo_subset_Ioo y.2.1 z.2.2
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
  rw [← W1p.integral_gradient_eq_intervalRepresentativeL_sub, intervalIntegral.integral_of_le hyz,
    integral_Ioc_eq_integral_Ioo, abs_of_nonneg (sub_nonneg.2 hyz)]
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
      _ ≤ _ := by gcongr; exact abs_sub_le_of_le_of_le z.2.1 z.2.2 y.2.1 y.2.2
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
      Real.rpow_le_rpow (abs_nonneg _) (abs_sub_le_of_le_of_le t.2.1 t.2.2 le_rfl hx.le) hβ0
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
