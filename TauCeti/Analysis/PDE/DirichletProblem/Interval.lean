/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The Dirichlet problem for divergence-form equations on an interval

On a bounded interval `(x₀, x₁)` consider the one-dimensional divergence-form equation

`-(a u')' = f + F'`

with a measurable coefficient `a ≥ λ > 0` and data `f ∈ L¹(x₀, x₁)` and `F ∈ Lᵖ(x₀, x₁)`. As in
`TauCeti.Analysis.PDE.Regularity.Interval`, a solution is `u ∈ W^{1,p}(x₀, x₁)` with

`∫ a u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

This file proves that for every pair `g` of endpoint values the Dirichlet problem, the equation
together with the boundary condition that the continuous representative `ū` of `u` takes the
values `g.1` at `x₀` and `g.2` at `x₁`, has exactly one solution in `W^{1,p}(x₀, x₁)`, for every
`1 ≤ p ≤ ∞`, and that the solution depends continuously on the coefficient: if `aᵢ → a` almost
everywhere with uniform bounds `λ ≤ aᵢ ≤ M`, the continuous representatives of the solutions
converge uniformly on `[x₀, x₁]`. Only measurability and the bounds are used, no continuity of
the coefficients.

In one dimension the equation can be solved explicitly. With `Φ t = ∫_{x₀}^t f`, the flux
`a u' + F` has weak derivative `-f`, so `a u' + F = k - Φ` for a constant `k`, and

`u' = (k - Φ - F) / a`, `k ∫ a⁻¹ = g.2 - g.1 + ∫ a⁻¹ (Φ + F)`.

Conversely this formula, integrated from `x₀` with initial value `g.1`, defines a solution. The
global Hölder bound for these solutions is
`TauCeti.PDE.exists_norm_intervalRepresentativeL_le_and_holderWith`; the continuity in the
coefficient is the input needed to solve quasilinear equations `-(A(x, u) u')' = f + F'` by a
fixed-point argument.

## Main declarations

* `TauCeti.PDE.exists_intervalTraceL_eq_and_forall_integral_eq`: existence for every lower bound
  `λ ≤ a`, without an upper bound on the coefficient.
* `TauCeti.PDE.existsUnique_intervalTraceL_eq_and_forall_integral_eq`: existence and uniqueness
  for `λ ≤ a ≤ M`.
* `TauCeti.PDE.tendsto_intervalRepresentativeL_of_ae_tendsto`: continuous dependence of the
  solution on the coefficient.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Section 8.4
  (one-dimensional boundary value problems).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.3 (the weak Dirichlet problem in every dimension).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Distributions

namespace TauCeti.PDE

variable {x₀ x₁ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {a f F : ℝ → ℝ}

/-- A coefficient bounded below by `λ > 0` has `a⁻¹` integrable on `(x₀, x₁)`, bounded by `λ⁻¹`. -/
private theorem integrable_inv {lam : ℝ} (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hlama : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) :
    (∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ‖(a t)⁻¹‖ ≤ lam⁻¹) ∧
      Integrable (fun t => (a t)⁻¹) (volume.restrict (Ioo x₀ x₁)) := by
  have hinv : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), ‖(a t)⁻¹‖ ≤ lam⁻¹ := hlama.mono fun t ht => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hlam.trans_le ht)]
    exact inv_anti₀ hlam ht
  exact ⟨hinv, Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _ hinv⟩

/-- A coefficient bounded below by `λ > 0` has `∫_{x₀}^{x₁} a⁻¹ > 0`. -/
private theorem setIntegral_inv_pos (hx : x₀ < x₁) {lam : ℝ} (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hlama : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t) :
    0 < ∫ t in Ioo x₀ x₁, (a t)⁻¹ := by
  refine (integral_pos_iff_support_of_nonneg_ae
    (hlama.mono fun t ht => (inv_pos.2 (hlam.trans_le ht)).le)
    (integrable_inv hlam ha hlama).2).2 ?_
  -- The support of `a⁻¹` has full measure in `(x₀, x₁)`.
  have h0 : volume.restrict (Ioo x₀ x₁) (Function.support fun t => (a t)⁻¹)ᶜ = 0 := by
    rw [Function.compl_support]
    simpa using ae_iff.1 (hlama.mono fun t ht => (inv_pos.2 (hlam.trans_le ht)).ne')
  have hpos : 0 < volume.restrict (Ioo x₀ x₁) univ := by simp [hx]
  exact (hpos.trans_le (measure_univ_le_add_compl (Function.support fun t => (a t)⁻¹))).trans_eq
    (by rw [h0, add_zero])

/-- **The explicit form of a solution.** A solution of `-(a u')' = f + F'` on `(x₀, x₁)` with
`λ ≤ a ≤ M` has `u' = k a⁻¹ - a⁻¹ (Φ + F)` almost everywhere, where `Φ t = ∫_{x₀}^t f` and the
constant `k` is determined by `k ∫ a⁻¹ = ū x₁ - ū x₀ + ∫ a⁻¹ (Φ + F)`. -/
private theorem exists_mul_setIntegral_inv_eq_and_gradient_ae_eq (hx : x₀ < x₁) {lam M : ℝ}
    (hlam : 0 < lam) (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∃ k, k * ∫ t in Ioo x₀ x₁, (a t)⁻¹ =
        (W1p.intervalTraceL hx u).2 - (W1p.intervalTraceL hx u).1 +
          ∫ t in Ioo x₀ x₁, (a t)⁻¹ * ((∫ s in x₀..t, f s) + F t) ∧
      W1p.gradient u =ᵐ[volume.restrict (Ioo x₀ x₁)]
        fun t => k * (a t)⁻¹ - (a t)⁻¹ * ((∫ s in x₀..t, f s) + F t) := by
  obtain ⟨k, hk⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral ha
    (haM.mono fun t ht => abs_le.2 ⟨by linarith [ht.1], ht.2⟩) hf hF hu
  refine ⟨k, mul_setIntegral_inv_eq_of_ae_mul_gradient_add_eq hx hlam ha
    (haM.mono fun _ ht => ht.1) hF
    (TauCeti.intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hf (left_mem_Icc.2 hx.le))
    hk, ?_⟩
  filter_upwards [hk, haM] with t ht hat
  have ha0 : a t ≠ 0 := (hlam.trans_le hat.1).ne'
  field_simp
  linarith

/-- **The converse of the first integral.** If the flux of `u ∈ W^{1,p}(x₀, x₁)` is
`a u' = k - Φ - F` almost everywhere, where `Φ t = ∫_{x₀}^t f`, then `u` solves
`-(a u')' = f + F'` in the sense of distributions: `k - Φ` has weak derivative `-f`. -/
private theorem forall_integral_eq_of_ae_mul_gradient_eq (hf : IntegrableOn f (Ioo x₀ x₁))
    (hF : IntegrableOn F (Ioo x₀ x₁)) {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p} {k : ℝ}
    (hflux : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁),
      a t * W1p.gradient u t = k - (∫ s in x₀..t, f s) - F t)
    (φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ)) :
    ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
      (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  set Φ : ℝ → ℝ := fun t => ∫ s in x₀..t, f s with hΦ_def
  have hline : ∀ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 = deriv (φ : ℝ → ℝ) t := fun t =>
    (φ.contDiff.differentiable (by simp) t).lineDeriv_eq_fderiv
  have hwk : HasWeakLineDerivOn volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ (fun t => k - Φ t) (-f) 1 :=
    ((hasWeakLineDerivOn_const k).sub (hasWeakLineDerivOn_intervalIntegral_left hf)).congr_ae_deriv
      (EventuallyEq.of_eq (zero_sub f))
  obtain ⟨-, hkΦ, -, hwkφ⟩ := hasWeakLineDerivOn_iff_testFunction.1 hwk
  have h1 := integrable_lineDeriv_smul_of_locallyIntegrableOn (μ := volume) hkΦ φ 1
  have h2 := integrable_lineDeriv_smul_of_locallyIntegrableOn (μ := volume)
    (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩) hF.locallyIntegrableOn φ 1
  have hflux' : (fun t => a t * W1p.gradient u t * deriv (φ : ℝ → ℝ) t) =ᵐ[volume.restrict
      (Ioo x₀ x₁)] fun t => lineDeriv ℝ (φ : ℝ → ℝ) t 1 • ((k - Φ t) - F t) := by
    filter_upwards [hflux] with t ht
    rw [ht, hline, smul_eq_mul, mul_comm]
  -- Pass between integrals over `(x₀, x₁)` and over the line, where the test functions live.
  have e0 := setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul (μ := volume)
    (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩) (w := fun t => (k - Φ t) - F t) φ 1
  simp only [TopologicalSpace.Opens.coe_mk] at e0
  have e1 : ∫ t in Ioo x₀ x₁, f t * φ t = ∫ t, (φ : ℝ → ℝ) t • f t := by
    rw [← setIntegral_smul_eq_integral_smul (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩)]
    simp only [TopologicalSpace.Opens.coe_mk, smul_eq_mul, mul_comm]
  have e2 : ∫ t in Ioo x₀ x₁, F t * deriv φ t = ∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • F t := by
    rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul (Ω := ⟨Ioo x₀ x₁, isOpen_Ioo⟩)]
    simp only [TopologicalSpace.Opens.coe_mk, hline, smul_eq_mul, mul_comm]
  have hsplit : ∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • ((k - Φ t) - F t) =
      (∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • (k - Φ t)) - ∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • F t := by
    rw [← integral_sub h1 h2]
    simp only [smul_sub]
  rw [integral_congr_ae hflux', e0, hsplit, e1, e2, hwkφ]
  simp only [Pi.neg_apply, smul_neg, MeasureTheory.integral_neg, neg_neg]

/-- **Existence for the Dirichlet problem on an interval.** Let `a` be measurable on `(x₀, x₁)`
with `a ≥ λ > 0` almost everywhere, and let `f ∈ L¹(x₀, x₁)` and `F ∈ Lᵖ(x₀, x₁)`,
`1 ≤ p ≤ ∞`. Then for every pair `g` of endpoint values there is `u ∈ W^{1,p}(x₀, x₁)` with
endpoint trace `g` solving `-(a u')' = f + F'` in the sense of distributions. -/
theorem exists_intervalTraceL_eq_and_forall_integral_eq (hx : x₀ < x₁) {lam : ℝ} (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hlama : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g : ℝ × ℝ) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p, W1p.intervalTraceL hx u = g ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  set Φ : ℝ → ℝ := fun t => ∫ s in x₀..t, f s with hΦ_def
  have hF1 : IntegrableOn F (Ioo x₀ x₁) := hF.integrable Fact.out
  have hΦi : IntegrableOn Φ (Ioo x₀ x₁) :=
    TauCeti.intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hf (left_mem_Icc.2 hx.le)
  obtain ⟨hinv, hainv⟩ := integrable_inv hlam ha hlama
  have hpos := setIntegral_inv_pos hx hlam ha hlama
  have hR : Integrable (fun t => (a t)⁻¹ * (Φ t + F t)) (volume.restrict (Ioo x₀ x₁)) :=
    (hΦi.add hF1).bdd_mul ha.aemeasurable.inv.aestronglyMeasurable hinv
  -- The flux constant `k` and the derivative `G = (k - Φ - F) / a` of the solution.
  set k : ℝ := (g.2 - g.1 + ∫ t in Ioo x₀ x₁, (a t)⁻¹ * (Φ t + F t)) /
    ∫ t in Ioo x₀ x₁, (a t)⁻¹ with hk_def
  set G : ℝ → ℝ := fun t => k * (a t)⁻¹ - (a t)⁻¹ * (Φ t + F t) with hG_def
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioo x₀ x₁)) :=
    (hainv.const_mul k).aestronglyMeasurable.sub hR.aestronglyMeasurable
  -- `G ∈ Lᵖ`, since `|G| ≤ λ⁻¹ (|k| + ‖f‖₁ + |F|)`.
  have hG : MemLp G p (volume.restrict (Ioo x₀ x₁)) := by
    have hb : MemLp (fun t => (|k| + ∫ s in Ioo x₀ x₁, |f s|) + |F t|) p
        (volume.restrict (Ioo x₀ x₁)) := (memLp_const _).add hF.abs
    refine hb.of_le_mul (c := lam⁻¹) hGm ?_
    filter_upwards [hlama, ae_restrict_mem measurableSet_Ioo] with t ht htI
    have hat : 0 < a t := hlam.trans_le ht
    have hb0 : 0 ≤ (|k| + ∫ s in Ioo x₀ x₁, |f s|) + |F t| := by
      have := setIntegral_nonneg (μ := volume) measurableSet_Ioo fun s (_ : s ∈ Ioo x₀ x₁) =>
        abs_nonneg (f s)
      positivity
    have hGt : |G t| = |k - (Φ t + F t)| * (a t)⁻¹ := by
      rw [show G t = (k - (Φ t + F t)) * (a t)⁻¹ by simp only [hG_def]; ring, abs_mul,
        abs_of_pos (inv_pos.2 hat)]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb0, hGt]
    have hΦt : |Φ t| ≤ ∫ s in Ioo x₀ x₁, |f s| := by
      simpa only [Real.norm_eq_abs] using
        TauCeti.intervalIntegral.norm_primitive_le_setIntegral_norm hf (left_mem_Icc.2 hx.le)
          (Ioo_subset_Icc_self htI)
    calc |k - (Φ t + F t)| * (a t)⁻¹ ≤ ((|k| + ∫ s in Ioo x₀ x₁, |f s|) + |F t|) * lam⁻¹ := by
          gcongr
          · calc |k - (Φ t + F t)| ≤ |k| + |Φ t| + |F t| :=
                  (abs_sub _ _).trans (by rw [add_assoc]; gcongr; exact abs_add_le _ _)
              _ ≤ _ := by gcongr
      _ = _ := mul_comm _ _
  have hGi : IntegrableOn G (Ioo x₀ x₁) := hG.integrable Fact.out
  have hGii : IntervalIntegrable G volume x₀ x₁ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2 hGi
  -- The total increment of the solution is `∫ G = g.2 - g.1`.
  have hGint : ∫ t in x₀..x₁, G t = g.2 - g.1 := by
    rw [intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo, hG_def,
      integral_sub (hainv.const_mul k) hR, integral_const_mul, hk_def,
      div_mul_cancel₀ _ hpos.ne']
    ring
  -- The solution `w t = g.1 + ∫_{x₀}^t G`.
  set w : ℝ → ℝ := fun t => g.1 + ∫ s in x₀..t, G s with hw_def
  have hwac : AbsolutelyContinuousOnInterval w x₀ x₁ :=
    (LipschitzWith.const g.1).lipschitzOnWith.absolutelyContinuousOnInterval.add
      (hGii.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  have hdw : deriv w =ᵐ[volume.restrict (Ioo x₀ x₁)] G := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hGii] with t ht htI
    have hmem : t ∈ uIcc x₀ x₁ := uIcc_of_le hx.le ▸ Ioo_subset_Icc_self htI
    exact ((ht hmem x₀ left_mem_uIcc).const_add g.1).deriv
  obtain ⟨u, huv, hug⟩ := hwac.exists_w1p_value_gradient_ae_eq (hG.ae_eq hdw.symm)
  have hwc : ContinuousOn w (Icc x₀ x₁) := uIcc_of_le hx.le ▸ hwac.continuousOn
  have hrep : W1p.intervalRepresentativeL hx u = ⟨(Icc x₀ x₁).domRestrict w, hwc.domRestrict⟩ := by
    refine (W1p.intervalRepresentativeL_eq_iff hx u _).2 ?_
    filter_upwards [huv, ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [ht]
    simp [projIcc_of_mem hx.le (Ioo_subset_Icc_self htI)]
  refine ⟨u, ?_, forall_integral_eq_of_ae_mul_gradient_eq (k := k) hf hF1 ?_⟩
  · rw [W1p.intervalTraceL_apply, hrep]
    ext <;> simp [w, hGint]
  · -- `a u' = a G = k - Φ - F`.
    filter_upwards [hug, hdw, hlama] with t hut hdt hat
    have ha0 : a t ≠ 0 := (hlam.trans_le hat).ne'
    rw [hut, hdt, hG_def]
    field_simp
    ring

/-- **Existence and uniqueness for the Dirichlet problem on an interval.** Let `a` be measurable
on `(x₀, x₁)` with `λ ≤ a ≤ M` almost everywhere, `λ > 0`, and let `f ∈ L¹(x₀, x₁)` and
`F ∈ Lᵖ(x₀, x₁)`, `1 ≤ p ≤ ∞`. Then for every pair `g` of endpoint values there is exactly one
`u ∈ W^{1,p}(x₀, x₁)` with endpoint trace `g` solving `-(a u')' = f + F'` in the sense of
distributions. -/
theorem existsUnique_intervalTraceL_eq_and_forall_integral_eq (hx : x₀ < x₁) {lam M : ℝ}
    (hlam : 0 < lam) (ha : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a t ∧ a t ≤ M)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : MemLp F p (volume.restrict (Ioo x₀ x₁)))
    (g : ℝ × ℝ) :
    ∃! u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p, W1p.intervalTraceL hx u = g ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, a t * W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  obtain ⟨u, hu⟩ := exists_intervalTraceL_eq_and_forall_integral_eq hx hlam ha
    (haM.mono fun _ ht => ht.1) hf hF g
  refine ⟨u, hu, fun v hv => ?_⟩
  have hF1 : IntegrableOn F (Ioo x₀ x₁) := hF.integrable Fact.out
  have hpos := setIntegral_inv_pos hx hlam ha (haM.mono fun _ ht => ht.1)
  -- Both derivatives are given by the explicit formula, with the same constant.
  obtain ⟨k, hk, hku⟩ := exists_mul_setIntegral_inv_eq_and_gradient_ae_eq hx hlam ha haM hf hF1 hu.2
  obtain ⟨k', hk', hkv⟩ :=
    exists_mul_setIntegral_inv_eq_and_gradient_ae_eq hx hlam ha haM hf hF1 hv.2
  rw [hu.1] at hk
  rw [hv.1, ← hk] at hk'
  obtain rfl : k' = k := mul_right_cancel₀ hpos.ne' hk'
  apply W1p.intervalRepresentativeL_injective hx
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine (W1p.norm_intervalRepresentativeL_sub_le hx v u).trans_eq ?_
  rw [hu.1, hv.1, sub_self, abs_zero, zero_add]
  have h0 : (fun t => |W1p.gradient v t - W1p.gradient u t|) =ᵐ[volume.restrict (Ioo x₀ x₁)]
      fun _ => (0 : ℝ) := by
    filter_upwards [hkv, hku] with t hvt hut
    rw [hvt, hut, sub_self, abs_zero]
  rw [integral_congr_ae h0, integral_zero]

/-- Dominated convergence for `∫ aᵢ⁻¹ w` when `aᵢ → a` almost everywhere with `aᵢ, a ≥ λ > 0`. -/
private theorem tendsto_setIntegral_inv_mul {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {lam : ℝ} (hlam : 0 < lam) {a : ι → ℝ → ℝ} {a₀ : ℝ → ℝ}
    (ha : ∀ i, AEStronglyMeasurable (a i) (volume.restrict (Ioo x₀ x₁)))
    (hlama : ∀ i, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a i t)
    (hlama₀ : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a₀ t)
    (hlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun i => a i t) l (𝓝 (a₀ t)))
    {w : ℝ → ℝ} (hw : IntegrableOn w (Ioo x₀ x₁)) :
    Tendsto (fun i => ∫ t in Ioo x₀ x₁, (a i t)⁻¹ * w t) l
      (𝓝 (∫ t in Ioo x₀ x₁, (a₀ t)⁻¹ * w t)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun t => lam⁻¹ * |w t|)
    (Eventually.of_forall fun i => (ha i).aemeasurable.inv.aestronglyMeasurable.mul
      hw.aestronglyMeasurable)
    (Eventually.of_forall fun i => (hlama i).mono fun t ht => ?_) (hw.abs.const_mul _) ?_
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos (hlam.trans_le ht)]
    gcongr
  · filter_upwards [hlim, hlama₀] with t ht ht₀
    exact (ht.inv₀ (hlam.trans_le ht₀).ne').mul_const _

/-- **Continuous dependence on the coefficient.** Let `aᵢ` be a family of measurable coefficients
on `(x₀, x₁)` with uniform bounds `λ ≤ aᵢ ≤ M`, `λ > 0`, converging almost everywhere along a
countably generated filter to a coefficient `a₀` with the same bounds, let `f, F` be integrable,
and let `uᵢ, u₀ ∈ W^{1,p}(x₀, x₁)` solve `-(aᵢ uᵢ')' = f + F'` and `-(a₀ u₀')' = f + F'` with the
same endpoint traces. Then the continuous representatives of `uᵢ` converge to that of `u₀`
uniformly on `[x₀, x₁]`. -/
theorem tendsto_intervalRepresentativeL_of_ae_tendsto {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (hx : x₀ < x₁) {lam M : ℝ} (hlam : 0 < lam) {a : ι → ℝ → ℝ}
    {a₀ : ℝ → ℝ} (ha : ∀ i, AEStronglyMeasurable (a i) (volume.restrict (Ioo x₀ x₁)))
    (haM : ∀ i, ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a i t ∧ a i t ≤ M)
    (haM₀ : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), lam ≤ a₀ t ∧ a₀ t ≤ M)
    (hlim : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), Tendsto (fun i => a i t) l (𝓝 (a₀ t)))
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    {u : ι → W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p} {u₀ : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hu : ∀ i, ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a i t * W1p.gradient (u i) t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    (hu₀ : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, a₀ t * W1p.gradient u₀ t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    (htr : ∀ i, W1p.intervalTraceL hx (u i) = W1p.intervalTraceL hx u₀) :
    Tendsto (fun i => W1p.intervalRepresentativeL hx (u i)) l
      (𝓝 (W1p.intervalRepresentativeL hx u₀)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have ha₀ : AEStronglyMeasurable a₀ (volume.restrict (Ioo x₀ x₁)) :=
    aestronglyMeasurable_of_tendsto_ae l ha hlim
  set Φ : ℝ → ℝ := fun t => ∫ s in x₀..t, f s with hΦ_def
  set Δ := (W1p.intervalTraceL hx u₀).2 - (W1p.intervalTraceL hx u₀).1
  have hR : IntegrableOn (fun t => Φ t + F t) (Ioo x₀ x₁) :=
    (TauCeti.intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hf
      (left_mem_Icc.2 hx.le)).add hF
  have hlama := fun i => (haM i).mono fun _ (ht : _ ∧ _) => ht.1
  have hlama₀ := haM₀.mono fun _ (ht : _ ∧ _) => ht.1
  -- The explicit formulas `uᵢ' = kᵢ aᵢ⁻¹ - aᵢ⁻¹ (Φ + F)` and `u₀' = k₀ a₀⁻¹ - a₀⁻¹ (Φ + F)`.
  choose k hk hku using fun i =>
    exists_mul_setIntegral_inv_eq_and_gradient_ae_eq hx hlam (ha i) (haM i) hf hF (hu i)
  obtain ⟨k₀, hk₀, hku₀⟩ :=
    exists_mul_setIntegral_inv_eq_and_gradient_ae_eq hx hlam ha₀ haM₀ hf hF hu₀
  simp only [htr] at hk
  -- `∫ aᵢ⁻¹ → ∫ a₀⁻¹` and `∫ aᵢ⁻¹ (Φ + F) → ∫ a₀⁻¹ (Φ + F)`, hence `kᵢ → k₀`.
  have hI := tendsto_setIntegral_inv_mul hlam ha hlama hlama₀ hlim
    (integrableOn_const (C := (1 : ℝ)) (by simp))
  simp only [mul_one] at hI
  have hJ := tendsto_setIntegral_inv_mul hlam ha hlama hlama₀ hlim hR
  have hpos := setIntegral_inv_pos hx hlam ha₀ hlama₀
  have hk_lim : Tendsto k l (𝓝 k₀) := by
    have hkdiv : ∀ i, k i = (Δ + ∫ t in Ioo x₀ x₁, (a i t)⁻¹ * (Φ t + F t)) /
        ∫ t in Ioo x₀ x₁, (a i t)⁻¹ := fun i =>
      eq_div_of_mul_eq (setIntegral_inv_pos hx hlam (ha i) (hlama i)).ne' (hk i)
    rw [funext hkdiv, eq_div_of_mul_eq hpos.ne' hk₀]
    exact (hJ.const_add Δ).div hI hpos.ne'
  -- Dominated convergence for `∫ |uᵢ' - u₀'|`.
  have hD : Tendsto (fun i => ∫ t in Ioo x₀ x₁, |W1p.gradient (u i) t - W1p.gradient u₀ t|) l
      (𝓝 0) := by
    have hcongr : ∀ i, ∫ t in Ioo x₀ x₁, |W1p.gradient (u i) t - W1p.gradient u₀ t| =
        ∫ t in Ioo x₀ x₁, |(k i * (a i t)⁻¹ - (a i t)⁻¹ * (Φ t + F t)) -
          (k₀ * (a₀ t)⁻¹ - (a₀ t)⁻¹ * (Φ t + F t))| := fun i =>
      integral_congr_ae ((hku i).mp (hku₀.mono fun t ht₀ ht => by simp only [ht, ht₀, hΦ_def]))
    simp only [hcongr]
    rw [show (0 : ℝ) = ∫ t in Ioo x₀ x₁, (0 : ℝ) by simp]
    have hkb : ∀ᶠ i in l, |k i| ≤ |k₀| + 1 := (Metric.tendsto_nhds.1 hk_lim 1 one_pos).mono
      fun i hi => by
        rw [Real.dist_eq] at hi
        linarith [abs_sub_abs_le_abs_sub (k i) k₀]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => lam⁻¹ * ((|k₀| + 1) + |k₀|) + 2 * (lam⁻¹ * |Φ t + F t|))
      (Eventually.of_forall fun i => ?_) (hkb.mono fun i hi => ?_)
      ((integrable_const _).add (hR.abs.const_mul _ |>.const_mul _)) ?_
    · have hmi := (ha i).aemeasurable.inv.aestronglyMeasurable
      have hm₀ := ha₀.aemeasurable.inv.aestronglyMeasurable
      exact continuous_abs.comp_aestronglyMeasurable (((hmi.const_mul _).sub
        (hmi.mul hR.aestronglyMeasurable)).sub ((hm₀.const_mul _).sub
          (hm₀.mul hR.aestronglyMeasurable)))
    · filter_upwards [hlama i, hlama₀] with t ht ht₀
      have hi₀ : 0 < (a i t)⁻¹ := inv_pos.2 (hlam.trans_le ht)
      have h₀ : 0 < (a₀ t)⁻¹ := inv_pos.2 (hlam.trans_le ht₀)
      have hle : (a i t)⁻¹ ≤ lam⁻¹ := inv_anti₀ hlam ht
      have hle₀ : (a₀ t)⁻¹ ≤ lam⁻¹ := inv_anti₀ hlam ht₀
      rw [Real.norm_eq_abs, abs_abs]
      calc |(k i * (a i t)⁻¹ - (a i t)⁻¹ * (Φ t + F t)) -
            (k₀ * (a₀ t)⁻¹ - (a₀ t)⁻¹ * (Φ t + F t))| ≤
            |k i| * (a i t)⁻¹ + |k₀| * (a₀ t)⁻¹ + ((a i t)⁻¹ * |Φ t + F t| +
              (a₀ t)⁻¹ * |Φ t + F t|) := by
            have := abs_sub (k i * (a i t)⁻¹ - (a i t)⁻¹ * (Φ t + F t))
              (k₀ * (a₀ t)⁻¹ - (a₀ t)⁻¹ * (Φ t + F t))
            have h1 := abs_sub (k i * (a i t)⁻¹) ((a i t)⁻¹ * (Φ t + F t))
            have h2 := abs_sub (k₀ * (a₀ t)⁻¹) ((a₀ t)⁻¹ * (Φ t + F t))
            rw [abs_mul, abs_mul, abs_of_pos hi₀] at h1
            rw [abs_mul, abs_mul, abs_of_pos h₀] at h2
            linarith
        _ ≤ (|k₀| + 1) * lam⁻¹ + |k₀| * lam⁻¹ + (lam⁻¹ * |Φ t + F t| + lam⁻¹ * |Φ t + F t|) := by
            gcongr
        _ = _ := by ring
    · filter_upwards [hlim, hlama₀] with t ht ht₀
      have hinv := ht.inv₀ (hlam.trans_le ht₀).ne'
      have := (((hk_lim.mul hinv).sub (hinv.mul_const (Φ t + F t))).sub
        (tendsto_const_nhds (x := k₀ * (a₀ t)⁻¹ - (a₀ t)⁻¹ * (Φ t + F t)))).abs
      simpa only [sub_self, abs_zero] using this
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun i => (W1p.norm_intervalRepresentativeL_sub_le hx (u i) u₀).trans_eq
      (by rw [htr i, sub_self, abs_zero, zero_add])) hD)

end TauCeti.PDE
