/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Hazard
public import TauCeti.Probability.Distributions.Relations
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Hazards of independent minima

The survival function of the minimum of a nonempty finite independent family is the product of
the marginal survival functions. Consequently its cumulative hazard is the sum of the marginal
cumulative hazards wherever all survival probabilities are positive. This identity allows
atomic laws as well as laws with densities.

At points where the marginal cdfs are differentiable, the hazard of the minimum is the sum of
the marginal hazards. Absolute continuity on a compact interval gives this equality almost
everywhere on that interval, together with integrability of the minimum's hazard. For continuous
densities the equality holds pointwise. The product-measure version describes the minimum of
the coordinate projections directly, without a separate random-variable model.

Hazards are expressed as the derivative of the cdf divided by survival, without choosing a
new density or imposing a value where survival vanishes.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace TauCeti.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
  {P : Measure Ω} {μ : ι → Measure ℝ} {X : ι → Ω → ℝ}
  [∀ i, IsProbabilityMeasure (μ i)]

/-- **Cumulative hazards add under independent minima.** At a point where every component has
positive survival, the negative logarithm of the minimum's survival is the sum of the component
negative logarithms. No atomlessness assumption is needed. -/
theorem neg_log_one_sub_cdf_min_indep (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μ i) P) {x : ℝ} (hS : ∀ i, cdf (μ i) x < 1) :
    -Real.log (1 - cdf (P.map fun ω =>
      Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) x) =
      ∑ i, -Real.log (1 - cdf (μ i) x) := by
  rw [cdf_min_indep hindep hlaw]
  simp only [sub_sub_cancel]
  rw [Real.log_prod (fun i _ => (sub_pos.2 (hS i)).ne'), Finset.sum_neg_distrib]

/-- **Hazards add at differentiability points.** The derivative of the minimum's cdf divided by
survival equals the sum of the corresponding marginal ratios. -/
theorem deriv_cdf_min_div_one_sub_cdf (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μ i) P) {x : ℝ}
    (hS : ∀ i, cdf (μ i) x < 1) (hd : ∀ i, DifferentiableAt ℝ (cdf (μ i)) x) :
    deriv (cdf (P.map fun ω =>
      Finset.univ.inf' Finset.univ_nonempty fun i => X i ω)) x /
        (1 - cdf (P.map fun ω =>
          Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) x) =
      ∑ i, deriv (cdf (μ i)) x / (1 - cdf (μ i) x) := by
  have hprod := logDeriv_fun_prod
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (sub_pos.2 (hS i)).ne')
    (fun i _ => (hd i).const_sub 1)
  have heq : (fun t => 1 - cdf (P.map fun ω =>
      Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) t) =
      fun t => ∏ i, (1 - cdf (μ i) t) := by
    funext t
    simp [cdf_min_indep hindep hlaw]
  rw [← heq, logDeriv_apply, deriv_const_sub] at hprod
  simp only [logDeriv_apply, deriv_const_sub, neg_div, Finset.sum_neg_distrib] at hprod
  linarith

/-- The cumulative hazard of an independent minimum has derivative equal to the sum of the
component hazards wherever the marginal cdfs are differentiable and survival is positive. -/
theorem hasDerivAt_neg_log_one_sub_cdf_min_indep (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μ i) P) {f : ι → ℝ} {x : ℝ}
    (hS : ∀ i, cdf (μ i) x < 1) (hf : ∀ i, HasDerivAt (cdf (μ i)) (f i) x) :
    HasDerivAt (fun t => -Real.log (1 - cdf (P.map fun ω =>
      Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) t))
      (∑ i, f i / (1 - cdf (μ i) x)) x := by
  have hnear : ∀ᶠ t in 𝓝 x, ∀ i, cdf (μ i) t < 1 := by
    rw [eventually_all]
    exact fun i => (hf i).continuousAt.eventually_lt_const (hS i)
  exact (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    hasDerivAt_neg_log_one_sub_cdf (hf i) (hS i)).congr_of_eventuallyEq
      (hnear.mono fun t ht => neg_log_one_sub_cdf_min_indep hindep hlaw ht)

/-- **Almost-everywhere addition of hazards.** On an interval where the marginal cdfs are
absolutely continuous and survival is positive, the minimum's hazard is their sum almost
everywhere with respect to Lebesgue measure. -/
theorem ae_deriv_cdf_min_div_one_sub_cdf (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μ i) P) {a b : ℝ}
    (hac : ∀ i, AbsolutelyContinuousOnInterval (cdf (μ i)) a b)
    (hS : ∀ t ∈ uIcc a b, ∀ i, cdf (μ i) t < 1) :
    ∀ᵐ t, t ∈ uIcc a b →
      deriv (cdf (P.map fun ω =>
        Finset.univ.inf' Finset.univ_nonempty fun i => X i ω)) t /
          (1 - cdf (P.map fun ω =>
            Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) t) =
        ∑ i, deriv (cdf (μ i)) t / (1 - cdf (μ i) t) := by
  have hd : ∀ᵐ t, ∀ i, t ∈ uIcc a b → DifferentiableAt ℝ (cdf (μ i)) t :=
    (ae_all_iff).2 fun i => (hac i).ae_differentiableAt
  filter_upwards [hd] with t ht hmem
  exact deriv_cdf_min_div_one_sub_cdf hindep hlaw (hS t hmem) fun i => ht i hmem

/-- **Integrability of the minimum's hazard.** Absolute continuity of the component cdfs and
positive component survival on the whole compact interval make the minimum's hazard integrable.
-/
theorem intervalIntegrable_deriv_cdf_min_div_one_sub_cdf (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μ i) P) {a b : ℝ}
    (hac : ∀ i, AbsolutelyContinuousOnInterval (cdf (μ i)) a b)
    (hS : ∀ t ∈ uIcc a b, ∀ i, cdf (μ i) t < 1) :
    IntervalIntegrable (fun t =>
      deriv (cdf (P.map fun ω =>
        Finset.univ.inf' Finset.univ_nonempty fun i => X i ω)) t /
          (1 - cdf (P.map fun ω =>
            Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) t)) volume a b := by
  have hi : ∀ i, IntervalIntegrable
      (fun t => deriv (cdf (μ i)) t / (1 - cdf (μ i) t)) volume a b := by
    intro i
    apply intervalIntegrable_div_one_sub_cdf (hac i) (fun t ht => hS t ht i)
    filter_upwards [(hac i).ae_differentiableAt] with t ht hmem
    exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt
  have hsum := IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
  apply hsum.congr_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [ae_deriv_cdf_min_div_one_sub_cdf hindep hlaw hac hS] with t ht hmem
  simpa only [Finset.sum_apply] using (ht (uIoc_subset_uIcc hmem)).symm

/-- **Pointwise addition for continuous densities.** If each marginal has a nonnegative density
continuous at `x`, then the minimum's hazard at `x` is the sum of those density values divided
by their respective survival probabilities. -/
theorem deriv_cdf_min_div_one_sub_cdf_of_eq_withDensity (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (μ i) P) {f : ι → ℝ → ℝ}
    (hμ : ∀ i, μ i = volume.withDensity fun t => ENNReal.ofReal (f i t))
    (hfm : ∀ i, AEMeasurable (f i)) (hnn : ∀ i, 0 ≤ᵐ[volume] f i) {x : ℝ}
    (hS : ∀ i, cdf (μ i) x < 1) (hc : ∀ i, ContinuousAt (f i) x) :
    deriv (cdf (P.map fun ω =>
      Finset.univ.inf' Finset.univ_nonempty fun i => X i ω)) x /
        (1 - cdf (P.map fun ω =>
          Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) x) =
      ∑ i, f i x / (1 - cdf (μ i) x) := by
  have hd i := hasDerivAt_cdf_of_eq_withDensity (hμ i) (hfm i) (hnn i) (hc i)
  rw [deriv_cdf_min_div_one_sub_cdf hindep hlaw hS (fun i => (hd i).differentiableAt)]
  simp_rw [(hd _).deriv]

/-- **Cumulative hazard of the product-measure minimum.** This measure identity applies to any
finite nonempty family of real probability laws, including laws with atoms. -/
theorem neg_log_one_sub_cdf_map_min_pi {x : ℝ} (hS : ∀ i, cdf (μ i) x < 1) :
    -Real.log (1 - cdf ((Measure.pi μ).map fun z =>
      Finset.univ.inf' Finset.univ_nonempty fun i => z i) x) =
      ∑ i, -Real.log (1 - cdf (μ i) x) := by
  apply neg_log_one_sub_cdf_min_indep (iIndepFun_pi (μ := μ) fun _ => measurable_id.aemeasurable)
    (fun i => ⟨(measurable_pi_apply i).aemeasurable, ?_⟩) hS
  exact (measurePreserving_eval μ i).map_eq

/-- **Hazard of the product-measure minimum.** Where survival is positive and each marginal cdf
is differentiable, the hazard of the minimum of the coordinate projections is their hazard sum.
-/
theorem deriv_cdf_map_min_pi_div_one_sub_cdf {x : ℝ}
    (hS : ∀ i, cdf (μ i) x < 1) (hd : ∀ i, DifferentiableAt ℝ (cdf (μ i)) x) :
    deriv (cdf ((Measure.pi μ).map fun z =>
      Finset.univ.inf' Finset.univ_nonempty fun i => z i)) x /
        (1 - cdf ((Measure.pi μ).map fun z =>
          Finset.univ.inf' Finset.univ_nonempty fun i => z i) x) =
      ∑ i, deriv (cdf (μ i)) x / (1 - cdf (μ i) x) := by
  apply deriv_cdf_min_div_one_sub_cdf (iIndepFun_pi (μ := μ) fun _ => measurable_id.aemeasurable)
    (fun i => ⟨(measurable_pi_apply i).aemeasurable, ?_⟩) hS hd
  exact (measurePreserving_eval μ i).map_eq

end TauCeti.Probability
