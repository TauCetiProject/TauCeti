/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CurveAction.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# Absolutely continuous curves of laws of random curves

Let `η` be a law on the path space `C([a, b], X)` of a separable metric space, concentrated on
absolutely continuous paths, and let `η_t` be its law at time `t`, the pushforward of `η` along
the evaluation `γ ↦ γ t`. For an exponent `1 ≤ p < ∞`, this file shows that the curve `t ↦ η_t`
moves in the `p`-Wasserstein distance no faster than the `Lᵖ(η)` average of the speeds of the
paths:

`W_p(η_s, η_u) ≤ ∫_s^u ‖|γ'|(r)‖_{Lᵖ(η)} dr`.

Indeed `γ ↦ (γ s, γ u)` pushes `η` to a coupling of `η_s` and `η_u`, each path covers the distance
`d(γ s, γ u) ≤ ∫_s^u |γ'|(r) dr`, and Minkowski's integral inequality
(`TauCeti.lintegral_Lp_lintegral_le`) moves the `Lᵖ(η)` seminorm inside the time integral.

When moreover the expected `p`-action `∫ A_p(γ) dη` is finite, the averaged speed
`r ↦ ‖|γ'|(r)‖_{Lᵖ(η)}` is integrable, so a curve `μ` in the finite-moment Wasserstein space
`P_p(X)` with `μ t = η_t` is absolutely continuous, and since its metric derivative is the smallest
integrable density bounding its distances,

`|μ'|(t) ^ p ≤ ∫ |γ'|(t) ^ p dη(γ)` for almost every `t`, hence `A_p(μ) ≤ ∫ A_p(γ) dη(γ)`.

Every representation of an absolutely continuous curve of laws as the time marginals of a law on
paths therefore averages the speeds of the paths to at least the metric speed of the curve. For
`1 < p < ∞`, the superposition principle of Lisini constructs a representation attaining
equality, which the inequality proved here shows to be minimal among all representations. The
finite moments needed to place the laws `η_t` in `P_p(X)` propagate from a single time
(`TauCeti.hasFiniteMoment_map_IccExtend`).

## Main results

* `TauCeti.wassersteinEDist_map_IccExtend_le_lintegral_eLpNorm`: the Wasserstein distance
  between two time marginals of a law on absolutely continuous paths is at most the time integral
  of the `Lᵖ` norms of the metric derivatives of the paths.
* `TauCeti.hasFiniteMoment_map_IccExtend`: with finite expected action, the time marginals all
  have finite `p`-moment once one of them does.
* `TauCeti.absolutelyContinuousOnInterval_of_coe_eq_map_IccExtend`: a curve in `P_p(X)` traced by
  the time marginals of a law on absolutely continuous paths of finite expected action is
  absolutely continuous.
* `TauCeti.ae_metricDerivative_rpow_le_lintegral_of_coe_eq_map_IccExtend`: its metric derivative
  satisfies `|μ'|(t) ^ p ≤ ∫ |γ'|(t) ^ p dη` at almost every time.
* `TauCeti.curveAction_le_lintegral_of_coe_eq_map_IccExtend`: its `p`-action is at most the
  expected `p`-action of the paths.

## References

* S. Lisini, *Characterization of absolutely continuous curves in Wasserstein spaces*, Calc. Var.
  Partial Differential Equations 28 (2007), 85--120.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §8.2, for the Euclidean case.
-/

public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {a b : ℝ} {p : ℝ≥0∞}

/-- The averaged speed `r ↦ ‖|γ'|(r)‖_{Lᵖ(η)}` of a law on paths is measurable. -/
private lemma measurable_eLpNorm_metricDerivative (hab : a ≤ b) (η : Measure C(Icc a b, X))
    [SFinite η] (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    Measurable fun r ↦
      eLpNorm (fun γ : C(Icc a b, X) ↦ metricDerivative (IccExtend hab γ) r) p η := by
  have hM := measurable_metricDerivative_IccExtend (X := X) hab
  have h : (fun r ↦
      eLpNorm (fun γ : C(Icc a b, X) ↦ metricDerivative (IccExtend hab γ) r) p η) =
      fun r ↦ (∫⁻ γ, metricDerivative (IccExtend hab γ) r ^ p.toReal ∂η) ^ (1 / p.toReal) := by
    funext r
    exact eLpNorm_eq_lintegral_rpow hp0 hp
      (measurable_metricDerivative_IccExtend_apply hab r).aemeasurable
  rw [h]
  exact ((hM.pow_const p.toReal).lintegral_prod_left' (μ := η)).pow_const _

/-- The `p`-th power of the averaged speed integrates over `[a, b]` to the expected `p`-action. -/
private lemma lintegral_eLpNorm_metricDerivative_rpow (hab : a ≤ b) (η : Measure C(Icc a b, X))
    [SFinite η] (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    ∫⁻ r in Ι a b,
        eLpNorm (fun γ : C(Icc a b, X) ↦ metricDerivative (IccExtend hab γ) r) p η ^ p.toReal =
      ∫⁻ γ, curveAction p.toReal (IccExtend hab γ) a b ∂η := by
  have hM := measurable_metricDerivative_IccExtend (X := X) hab
  simp_rw [curveAction_def]
  rw [lintegral_lintegral_swap (hM.pow_const p.toReal).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_uIoc fun r _ ↦ ?_
  exact eLpNorm_rpow_eq_lintegral hp0 hp
    (measurable_metricDerivative_IccExtend_apply hab r).aemeasurable

/-- With finite expected `p`-action, the averaged speed of a law on paths is integrable over
`[a, b]`. -/
private lemma lintegral_eLpNorm_metricDerivative_ne_top (hab : a ≤ b)
    (η : Measure C(Icc a b, X)) [SFinite η] (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (hA : ∫⁻ γ, curveAction p.toReal (IccExtend hab γ) a b ∂η ≠ ∞) :
    ∫⁻ r in Ι a b, eLpNorm (fun γ : C(Icc a b, X) ↦ metricDerivative (IccExtend hab γ) r) p η ≠
      ∞ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp hp1
  -- Hölder's inequality on `[a, b]` bounds the integral by the expected action.
  have h := rpow_lintegral_le_measure_univ_rpow_mul (μ := volume.restrict (Ι a b))
    (measurable_eLpNorm_metricDerivative hab η hp0 hp).aemeasurable hr
  rw [lintegral_eLpNorm_metricDerivative_rpow hab η hp0 hp, Measure.restrict_apply_univ,
    Real.volume_uIoc] at h
  refine ((ENNReal.rpow_lt_top_iff_of_pos (by linarith)).1 (h.trans_lt ?_)).ne
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
    hA.lt_top

variable [MeasurableSpace X] [BorelSpace X]

/-- A curve of probability measures whose values on `[a, b]` are the time marginals of `η` forces
`η` to be a probability measure. -/
private lemma isProbabilityMeasure_of_coe_eq_map_IccExtend (hab : a ≤ b)
    {η : Measure C(Icc a b, X)} {μ : ℝ → WassersteinSpace p X}
    (hμ : ∀ t ∈ uIcc a b, ((μ t : ProbabilityMeasure X) : Measure X) =
      η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ t) :
    IsProbabilityMeasure η := by
  constructor
  have h := measure_univ (μ := ((μ a : ProbabilityMeasure X) : Measure X))
  rwa [hμ a left_mem_uIcc, Measure.map_apply (measurable_IccExtend_apply hab a)
    MeasurableSet.univ, preimage_univ] at h

variable [SecondCountableTopology X]

/-- **Time marginals of a law on paths move no faster than the averaged speed.** Let `η` be a
σ-finite measure on `C([a, b], X)` concentrated on paths that are absolutely continuous on
`[a, b]`, and let `1 ≤ p < ∞`. For times `s, u ∈ [a, b]`, the `p`-Wasserstein distance between the
laws of `γ s` and `γ u` is at most the integral over the times between `s` and `u` of the `Lᵖ(η)`
norm of the metric derivative of the paths. -/
theorem wassersteinEDist_map_IccExtend_le_lintegral_eLpNorm (hab : a ≤ b)
    {η : Measure C(Icc a b, X)} [SigmaFinite η]
    (hAC : ∀ᵐ γ : C(Icc a b, X) ∂η, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) {s u : ℝ} (hs : s ∈ uIcc a b) (hu : u ∈ uIcc a b) :
    wassersteinEDist p (η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ s)
        (η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ u) ≤
      ∫⁻ r in Ι s u, eLpNorm (fun γ : C(Icc a b, X) ↦ metricDerivative (IccExtend hab γ) r) p η
    := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp hp1
  have hM := measurable_metricDerivative_IccExtend (X := X) hab
  have hs' := measurable_IccExtend_apply (X := X) hab s
  have hu' := measurable_IccExtend_apply (X := X) hab u
  -- The joint law of the path at times `s` and `u` couples the two time marginals.
  calc wassersteinEDist p (η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ s)
        (η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ u)
      ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p
          (η.map fun γ : C(Icc a b, X) ↦ (IccExtend hab γ s, IccExtend hab γ u)) :=
        wassersteinEDist_le (isCoupling_map_prodMk_of_measurePreserving ⟨hs', rfl⟩ ⟨hu', rfl⟩) p
    _ = eLpNorm (fun γ : C(Icc a b, X) ↦ edist (IccExtend hab γ s) (IccExtend hab γ u)) p η :=
        eLpNorm_map_measure measurable_edist.aestronglyMeasurable (hs'.prodMk hu').aemeasurable
    _ ≤ eLpNorm (fun γ : C(Icc a b, X) ↦ ∫⁻ r in Ι s u, metricDerivative (IccExtend hab γ) r)
          p η := by
        refine eLpNorm_mono_enorm_ae (hs'.edist hu').aestronglyMeasurable ?_
        filter_upwards [hAC] with γ hγ
        simpa only [enorm_eq_self] using hγ.edist_le_lintegral_metricDerivative hs hu
    _ ≤ ∫⁻ r in Ι s u,
          eLpNorm (fun γ : C(Icc a b, X) ↦ metricDerivative (IccExtend hab γ) r) p η := by
        -- Minkowski's integral inequality moves the `Lᵖ(η)` seminorm inside the time integral.
        rw [eLpNorm_eq_lintegral_rpow hp0 hp
          (hM.lintegral_prod_right' (ν := volume.restrict (Ι s u))).aemeasurable]
        refine (lintegral_Lp_lintegral_le (μ := η) (ν := volume.restrict (Ι s u))
          (f := fun γ r ↦ metricDerivative (IccExtend hab γ) r) hM.aemeasurable hr).trans_eq
          (setLIntegral_congr_fun measurableSet_uIoc fun r _ ↦ ?_)
        exact (eLpNorm_eq_lintegral_rpow hp0 hp
          (measurable_metricDerivative_IccExtend_apply hab r).aemeasurable).symm

/-- **Finite moments propagate along a law on paths of finite expected action.** Let `η` be a
probability measure on `C([a, b], X)` concentrated on paths absolutely continuous on `[a, b]`
with finite expected `p`-action, for `1 ≤ p < ∞`. If the law of `γ t₀` has finite `p`-moment for
one time `t₀ ∈ [a, b]`, then so does the law of `γ t` for every time `t`. -/
theorem hasFiniteMoment_map_IccExtend (hab : a ≤ b) {η : Measure C(Icc a b, X)}
    [IsProbabilityMeasure η]
    (hAC : ∀ᵐ γ : C(Icc a b, X) ∂η, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hA : ∫⁻ γ, curveAction p.toReal (IccExtend hab γ) a b ∂η ≠ ∞)
    {t₀ : ℝ} (ht₀ : t₀ ∈ uIcc a b)
    (h₀ : HasFiniteMoment p (η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ t₀)) (t : ℝ) :
    HasFiniteMoment p (η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ t) := by
  -- Outside `[a, b]` the extended paths are constant, so it suffices to treat `t ∈ [a, b]`.
  have hproj : (fun γ : C(Icc a b, X) ↦ IccExtend hab γ t) =
      fun γ : C(Icc a b, X) ↦ IccExtend hab γ (projIcc a b hab t) := by
    funext γ
    rw [IccExtend_val]
    -- `IccExtend hab γ` is defined as `γ ∘ projIcc a b hab`.
    rfl
  have ht : (projIcc a b hab t : ℝ) ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact (projIcc a b hab t).2
  rw [hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment measurable_edist h₀, hproj]
  refine ne_top_of_le_ne_top ?_
    (wassersteinEDist_map_IccExtend_le_lintegral_eLpNorm hab hAC hp1 hp ht₀ ht)
  exact ne_top_of_le_ne_top (lintegral_eLpNorm_metricDerivative_ne_top hab η hp1 hp hA)
    (lintegral_mono_set (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc ht₀ ht)))

variable [StandardBorelSpace X] [Fact (1 ≤ p)]

/-- Along a curve in `P_p(X)` traced by the time marginals of `η`, the distances are bounded by
the integrals of the averaged speed of the paths. -/
private lemma edist_le_lintegral_of_coe_eq_map_IccExtend (hab : a ≤ b)
    {η : Measure C(Icc a b, X)}
    (hAC : ∀ᵐ γ : C(Icc a b, X) ∂η, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    (hp : p ≠ ∞) {μ : ℝ → WassersteinSpace p X}
    (hμ : ∀ t ∈ uIcc a b, ((μ t : ProbabilityMeasure X) : Measure X) =
      η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ t) :
    ∀ s ∈ uIcc a b, ∀ u ∈ uIcc a b, edist (μ s) (μ u) ≤
      ∫⁻ r in Ι s u, eLpNorm (fun γ : C(Icc a b, X) ↦ metricDerivative (IccExtend hab γ) r) p η
    := by
  have := isProbabilityMeasure_of_coe_eq_map_IccExtend hab hμ
  intro s hs u hu
  rw [WassersteinSpace.edist_def, hμ s hs, hμ u hu]
  exact wassersteinEDist_map_IccExtend_le_lintegral_eLpNorm hab hAC Fact.out hp hs hu

/-- **Time marginals of a law on paths form an absolutely continuous curve.** Let `1 ≤ p < ∞` and
let `η` be a measure on `C([a, b], X)` concentrated on paths absolutely continuous on `[a, b]`,
with finite expected `p`-action. A curve `μ` in the finite-moment Wasserstein space `P_p(X)` whose
value at each time `t ∈ [a, b]` is the law of `γ t` under `η` is absolutely continuous on
`[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_coe_eq_map_IccExtend (hab : a ≤ b)
    {η : Measure C(Icc a b, X)}
    (hAC : ∀ᵐ γ : C(Icc a b, X) ∂η, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    (hp : p ≠ ∞) (hA : ∫⁻ γ, curveAction p.toReal (IccExtend hab γ) a b ∂η ≠ ∞)
    {μ : ℝ → WassersteinSpace p X}
    (hμ : ∀ t ∈ uIcc a b, ((μ t : ProbabilityMeasure X) : Measure X) =
      η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ t) :
    AbsolutelyContinuousOnInterval μ a b := by
  have := isProbabilityMeasure_of_coe_eq_map_IccExtend hab hμ
  exact absolutelyContinuousOnInterval_of_edist_le_lintegral
    (lintegral_eLpNorm_metricDerivative_ne_top hab η Fact.out hp hA)
    (edist_le_lintegral_of_coe_eq_map_IccExtend hab hAC hp hμ)

/-- **The metric speed of the time marginals is at most the averaged speed of the paths.** Let
`1 ≤ p < ∞` and let `η` be a measure on `C([a, b], X)` concentrated on paths absolutely continuous
on `[a, b]`, with finite expected `p`-action. If a curve `μ` in `P_p(X)` takes at each time
`t ∈ [a, b]` the law of `γ t` under `η` as its value, then at almost every `t ∈ [a, b]` its metric
derivative satisfies `|μ'|(t) ^ p ≤ ∫ |γ'|(t) ^ p dη(γ)`. -/
theorem ae_metricDerivative_rpow_le_lintegral_of_coe_eq_map_IccExtend (hab : a ≤ b)
    {η : Measure C(Icc a b, X)}
    (hAC : ∀ᵐ γ : C(Icc a b, X) ∂η, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    (hp : p ≠ ∞) (hA : ∫⁻ γ, curveAction p.toReal (IccExtend hab γ) a b ∂η ≠ ∞)
    {μ : ℝ → WassersteinSpace p X}
    (hμ : ∀ t ∈ uIcc a b, ((μ t : ProbabilityMeasure X) : Measure X) =
      η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ t) :
    ∀ᵐ t, t ∈ uIcc a b →
      metricDerivative μ t ^ p.toReal ≤ ∫⁻ γ, metricDerivative (IccExtend hab γ) t ^ p.toReal ∂η
    := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have := isProbabilityMeasure_of_coe_eq_map_IccExtend hab hμ
  -- The metric derivative is the smallest integrable density bounding the distances along `μ`.
  filter_upwards [ae_metricDerivative_le
    (measurable_eLpNorm_metricDerivative hab η hp0 hp).aemeasurable
    (lintegral_eLpNorm_metricDerivative_ne_top hab η hp1 hp hA)
    (edist_le_lintegral_of_coe_eq_map_IccExtend hab hAC hp hμ)] with t ht htab
  rw [← eLpNorm_rpow_eq_lintegral hp0 hp
    (measurable_metricDerivative_IccExtend_apply hab t).aemeasurable]
  exact ENNReal.rpow_le_rpow (ht htab) ENNReal.toReal_nonneg

/-- **The action of the time marginals is at most the expected action of the paths.** Let
`1 ≤ p < ∞` and let `η` be a measure on `C([a, b], X)` concentrated on paths absolutely continuous
on `[a, b]`. If a curve `μ` in `P_p(X)` takes at each time `t ∈ [a, b]` the law of `γ t` under `η`
as its value, then the `p`-action of `μ` over `[a, b]` is at most the expected `p`-action
`∫ A_p(γ) dη(γ)` of the paths. -/
theorem curveAction_le_lintegral_of_coe_eq_map_IccExtend (hab : a ≤ b)
    {η : Measure C(Icc a b, X)}
    (hAC : ∀ᵐ γ : C(Icc a b, X) ∂η, AbsolutelyContinuousOnInterval (IccExtend hab γ) a b)
    (hp : p ≠ ∞) {μ : ℝ → WassersteinSpace p X}
    (hμ : ∀ t ∈ uIcc a b, ((μ t : ProbabilityMeasure X) : Measure X) =
      η.map fun γ : C(Icc a b, X) ↦ IccExtend hab γ t) :
    curveAction p.toReal μ a b ≤ ∫⁻ γ, curveAction p.toReal (IccExtend hab γ) a b ∂η := by
  rcases eq_or_ne (∫⁻ γ, curveAction p.toReal (IccExtend hab γ) a b ∂η) ∞ with hA | hA
  · rw [hA]
    exact le_top
  have := isProbabilityMeasure_of_coe_eq_map_IccExtend hab hμ
  have hM := measurable_metricDerivative_IccExtend (X := X) hab
  have hle := ae_metricDerivative_rpow_le_lintegral_of_coe_eq_map_IccExtend hab hAC hp hA hμ
  rw [curveAction_def]
  calc ∫⁻ t in Ι a b, metricDerivative μ t ^ p.toReal
      ≤ ∫⁻ t in Ι a b, ∫⁻ γ, metricDerivative (IccExtend hab γ) t ^ p.toReal ∂η := by
        refine setLIntegral_mono_ae' measurableSet_uIoc ?_
        filter_upwards [hle] with t ht htab using ht (uIoc_subset_uIcc htab)
    _ = ∫⁻ γ, curveAction p.toReal (IccExtend hab γ) a b ∂η := by
        simp_rw [curveAction_def]
        exact (lintegral_lintegral_swap (hM.pow_const p.toReal).aemeasurable).symm

end TauCeti
