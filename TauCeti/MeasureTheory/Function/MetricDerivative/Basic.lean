/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import TauCeti.Topology.Order.Interval

/-!
# The metric derivative of a curve

For a curve `γ : ℝ → X` in an extended pseudometric space, the *metric derivative* at `t` is
`|γ'|(t) = limsup_{s → t, s ≠ t} edist (γ s) (γ t) / |s - t|`, the metric replacement for the norm
of the velocity of a curve in a normed space (`HasDerivAt.metricDerivative_eq`). It is the speed
that the action `∫ |γ'|(t)ᵖ dt` of a curve integrates, and so the basic object behind absolutely
continuous curves in metric spaces, dynamic transport plans and metric gradient flows.

The main result is the *fundamental theorem for absolutely continuous metric-valued curves*
(Ambrosio–Gigli–Savaré, Theorem 1.1.2). For a curve `γ` that is absolutely continuous on `[a, b]`
in Mathlib's sense, `AbsolutelyContinuousOnInterval γ a b`:

* the difference quotients `edist (γ s) (γ t) / edist s t` converge, so the `limsup` defining the
  metric derivative is a genuine limit, at almost every `t ∈ [a, b]`;
* the metric derivative has finite integral over `[a, b]`, and
  `edist (γ s) (γ u) ≤ ∫⁻ r in Ι s u, |γ'|(r)` for all `s, u ∈ [a, b]`;
* it is the smallest such density: any almost everywhere measurable `m` with finite integral over
  `[a, b]` satisfying the same bound dominates the metric derivative almost everywhere on `[a, b]`.

Conversely a curve admitting such an integrable density is absolutely continuous, so absolute
continuity of a metric-valued curve is exactly the existence of an integrable density bounding its
distances, which is the definition used by Ambrosio–Gigli–Savaré
(`absolutelyContinuousOnInterval_iff_exists_edist_le_lintegral`).

The proof of the fundamental theorem follows Ambrosio–Gigli–Savaré. The image of `[a, b]` is
compact, hence separable, so it has a countable dense subset `c`. Each distance profile
`r ↦ dist (γ r) x` with `x ∈ c` is a real absolutely continuous function, hence the integral of its
derivative, and the supremum `m` of the absolute values of these derivatives bounds
`edist (γ s) (γ u)` by `∫⁻ r in Ι s u, m r`. Every difference quotient of `γ` dominates those of
the profiles, so `m` is a lower bound for the `liminf`, while the Lebesgue differentiation theorem
makes `m` an upper bound for the `limsup`. Finiteness of `∫⁻ m` comes from the variation function
of `γ`, a monotone real function whose increments dominate the distances along `γ`, so that its
integrable derivative bounds the metric derivative almost everywhere.

For continuous curves the `limsup` defining the metric derivative can be taken along rational
increments, which makes the metric derivative jointly measurable in the time and in the parameter
of a measurable family of continuous curves, and absolute continuity can be tested on rational
times. On the space `C([a, b], X)` of continuous paths with its Borel structure, the space on which
dynamic transport plans live, this gives the measurability of the metric derivative and of the
set of absolutely continuous paths, which the action functional of a dynamic plan integrates.

## Main definitions

* `TauCeti.metricDerivative γ t`: the metric derivative of `γ` at `t`, as an extended nonnegative
  real.

## Main results

* `HasDerivAt.tendsto_edist_div` and `HasDerivAt.metricDerivative_eq`: on a normed space the
  difference quotients converge to the norm of the derivative, which is the metric derivative.
* `TauCeti.continuousAt_of_metricDerivative_ne_top`: a curve is continuous wherever its metric
  derivative is finite.
* `LipschitzWith.metricDerivative_le` and `LipschitzWith.metricDerivative_comp_le`: Lipschitz
  bounds on a curve and under Lipschitz post-composition.
* `BoundedVariationOn.ae_metricDerivative_le_enorm_deriv_variationOnFromTo`: for a curve of bounded
  variation, the metric derivative is almost everywhere at most the derivative of the variation.
* `TauCeti.ae_metricDerivative_le`: minimality of the metric derivative among the integrable
  densities bounding the distances along a curve.
* `AbsolutelyContinuousOnInterval.ae_tendsto_metricDerivative`,
  `AbsolutelyContinuousOnInterval.lintegral_metricDerivative_lt_top` and
  `AbsolutelyContinuousOnInterval.edist_le_lintegral_metricDerivative`: the fundamental theorem
  for absolutely continuous curves.
* `TauCeti.absolutelyContinuousOnInterval_iff_exists_edist_le_lintegral`: absolute continuity as
  the existence of an integrable density bounding the distances along a curve.
* `TauCeti.measurable_metricDerivative` and `Continuous.measurable_metricDerivative`: joint
  measurability of the metric derivative in a measurable family of continuous curves, and
  measurability for a single continuous curve.
* `TauCeti.absolutelyContinuousOnInterval_iff_forall_rat_edist_le_lintegral` and
  `TauCeti.measurableSet_absolutelyContinuousOnInterval`: absolute continuity of a continuous curve
  tested on rational times, and the measurability of the absolutely continuous members of a
  measurable family of continuous curves.
* `TauCeti.measurable_metricDerivative_IccExtend` and
  `TauCeti.measurableSet_absolutelyContinuousOnInterval_IccExtend`: the same statements on the
  path space `C([a, b], X)`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Definition 1.1.1 and Theorem 1.1.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Interval

namespace TauCeti

section PseudoEMetricSpace

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {γ : ℝ → X} {t : ℝ}

/-- The *metric derivative* of a curve `γ : ℝ → X` at `t`, the upper limit of the difference
quotients `edist (γ s) (γ t) / edist s t` as `s → t` with `s ≠ t`. For an absolutely continuous
curve these quotients converge at almost every time
(`AbsolutelyContinuousOnInterval.ae_tendsto_metricDerivative`); taking the upper limit makes the
metric derivative defined at every time. -/
def metricDerivative (γ : ℝ → X) (t : ℝ) : ℝ≥0∞ :=
  limsup (fun s ↦ edist (γ s) (γ t) / edist s t) (𝓝[≠] t)

/-- The defining formula of the metric derivative, as an upper limit of difference quotients. -/
theorem metricDerivative_def (γ : ℝ → X) (t : ℝ) :
    metricDerivative γ t = limsup (fun s ↦ edist (γ s) (γ t) / edist s t) (𝓝[≠] t) :=
  (rfl)

/-- If the difference quotients of `γ` at `t` converge, their limit is the metric derivative. -/
theorem metricDerivative_eq_of_tendsto {l : ℝ≥0∞}
    (h : Tendsto (fun s ↦ edist (γ s) (γ t) / edist s t) (𝓝[≠] t) (𝓝 l)) :
    metricDerivative γ t = l :=
  (metricDerivative_def γ t).trans h.limsup_eq

/-- A curve with finite metric derivative at `t` is continuous at `t`. -/
theorem continuousAt_of_metricDerivative_ne_top (h : metricDerivative γ t ≠ ∞) :
    ContinuousAt γ t := by
  obtain ⟨C, hC, hCtop⟩ := exists_between (lt_top_iff_ne_top.2 h)
  have hbound : ∀ᶠ s in 𝓝[≠] t, edist (γ s) (γ t) ≤ C * edist s t := by
    filter_upwards [eventually_lt_of_limsup_lt hC, self_mem_nhdsWithin] with s hs hst
    exact (ENNReal.div_le_iff (edist_pos.2 hst).ne' (edist_ne_top s t)).1 hs.le
  have hlim : Tendsto (fun s ↦ C * edist s t) (𝓝[≠] t) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (tendsto_id.edist (tendsto_const_nhds (x := t)))
      (Or.inr hCtop.ne) (f := 𝓝 t)
    simpa using this.mono_left nhdsWithin_le_nhds
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ bot_le) hbound

/-- The metric derivative of a `K`-Lipschitz curve is at most `K` everywhere. -/
theorem _root_.LipschitzWith.metricDerivative_le {K : ℝ≥0} (hγ : LipschitzWith K γ) (t : ℝ) :
    metricDerivative γ t ≤ K := by
  rw [metricDerivative_def]
  exact limsup_le_of_le (h := Eventually.of_forall fun s ↦ ENNReal.div_le_of_le_mul (hγ s t))

/-- Post-composing a curve with a `K`-Lipschitz map multiplies its metric derivative by at most
`K`. -/
theorem _root_.LipschitzWith.metricDerivative_comp_le {f : X → Y} {K : ℝ≥0}
    (hf : LipschitzWith K f) (γ : ℝ → X) (t : ℝ) :
    metricDerivative (f ∘ γ) t ≤ K * metricDerivative γ t := by
  rw [metricDerivative_def, metricDerivative_def,
    ← ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top]
  refine limsup_le_limsup (Eventually.of_forall fun s ↦ ?_)
  rw [← mul_div_assoc]
  exact ENNReal.div_le_div_right (hf _ _) _

/-- **Minimality of the metric derivative.** If `m` has finite integral over `[a, b]` and bounds
the distances along `γ` by `edist (γ s) (γ u) ≤ ∫⁻ r in Ι s u, m r` for all `s, u ∈ [a, b]`, then
the metric derivative of `γ` is at most `m` almost everywhere on `[a, b]`. -/
theorem ae_metricDerivative_le {m : ℝ → ℝ≥0∞} {a b : ℝ}
    (hm : AEMeasurable m (volume.restrict (Ι a b))) (hfin : ∫⁻ r in Ι a b, m r ≠ ∞)
    (h : ∀ s ∈ uIcc a b, ∀ u ∈ uIcc a b, edist (γ s) (γ u) ≤ ∫⁻ r in Ι s u, m r) :
    ∀ᵐ t, t ∈ uIcc a b → metricDerivative γ t ≤ m t := by
  filter_upwards [ae_tendsto_setLIntegral_uIoc_div hm hfin, volume.ae_ne a, volume.ae_ne b]
    with t ht hta htb htab
  rw [metricDerivative_def, ← (ht htab).limsup_eq]
  refine limsup_le_limsup ?_
  filter_upwards [nhdsWithin_le_nhds (uIcc_mem_nhds_of_ne htab hta htb)] with s hs
  rw [uIoc_comm]
  exact ENNReal.div_le_div_right (h s hs t htab) _

end PseudoEMetricSpace

/-- The difference quotients `edist (γ s) (γ t) / edist s t` of a curve in a normed space converge
to the norm of its derivative. -/
theorem _root_.HasDerivAt.tendsto_edist_div {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {γ : ℝ → E} {v : E} {t : ℝ} (h : HasDerivAt γ v t) :
    Tendsto (fun s ↦ edist (γ s) (γ t) / edist s t) (𝓝[≠] t) (𝓝 ‖v‖ₑ) := by
  refine ((continuous_enorm.tendsto v).comp (hasDerivAt_iff_tendsto_slope.1 h)).congr' <|
    eventually_nhdsWithin_of_forall fun s hs ↦ ?_
  simp only [Function.comp_apply, slope_def_module, enorm_smul, enorm_inv (sub_ne_zero.2 hs),
    edist_eq_enorm_sub, ENNReal.div_eq_inv_mul]

/-- On a normed space the metric derivative of a curve is the norm of its derivative. -/
theorem _root_.HasDerivAt.metricDerivative_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {γ : ℝ → E} {v : E} {t : ℝ} (h : HasDerivAt γ v t) :
    metricDerivative γ t = ‖v‖ₑ :=
  metricDerivative_eq_of_tendsto h.tendsto_edist_div

section BoundedVariation

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- At almost every time of `[a, b]`, the metric derivative of a curve of bounded variation on
`[a, b]` is at most the derivative of its variation function `variationOnFromTo γ (uIcc a b) a`. -/
theorem _root_.BoundedVariationOn.ae_metricDerivative_le_enorm_deriv_variationOnFromTo
    (hγ : BoundedVariationOn γ (uIcc a b)) :
    ∀ᵐ t, t ∈ uIcc a b →
      metricDerivative γ t ≤ ‖deriv (variationOnFromTo γ (uIcc a b) a) t‖ₑ := by
  set V := variationOnFromTo γ (uIcc a b) a
  -- The variation function dominates the distances along `γ`.
  have hV {s u : ℝ} (hs : s ∈ uIcc a b) (hu : u ∈ uIcc a b) (hsu : s ≤ u) :
      edist (γ s) (γ u) ≤ edist (V s) (V u) := by
    simp only [V]
    rw [edist_comm (variationOnFromTo _ _ _ s), edist_eq_enorm_sub,
      ← variationOnFromTo.add hγ.locallyBoundedVariationOn left_mem_uIcc hs hu, add_sub_cancel_left,
      variationOnFromTo.eq_of_le _ _ hsu, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ((eVariationOn.mono _ inter_subset_left).trans_lt hγ.lt_top).ne]
    exact eVariationOn.edist_le _ ⟨hs, le_rfl, hsu⟩ ⟨hu, hsu, le_rfl⟩
  have hVmono : MonotoneOn V (uIcc a b) :=
    variationOnFromTo.monotoneOn hγ.locallyBoundedVariationOn left_mem_uIcc
  filter_upwards [hVmono.ae_differentiableWithinAt_of_mem, volume.ae_ne a, volume.ae_ne b]
    with t ht hta htb htab
  have hnhds := uIcc_mem_nhds_of_ne htab hta htb
  rw [metricDerivative_def,
    ← ((ht htab).differentiableAt hnhds).hasDerivAt.tendsto_edist_div.limsup_eq]
  refine limsup_le_limsup ?_
  filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
  refine ENNReal.div_le_div_right ?_ _
  rcases le_total s t with hst | hts
  · exact hV hs htab hst
  · rw [edist_comm, edist_comm (V s)]
    exact hV htab hs hts

end BoundedVariation

section AbsolutelyContinuous

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- The supremum, over the points `x` of a set `c`, of the absolute derivatives of the distance
profiles `r ↦ dist (γ r) x`. For a countable set `c` dense in the image of an absolutely continuous
curve, this is a measurable representative of the metric derivative. -/
private noncomputable def profileSpeed (γ : ℝ → X) (c : Set X) (r : ℝ) : ℝ≥0∞ :=
  ⨆ x : c, ‖deriv (fun r ↦ dist (γ r) x) r‖ₑ

private lemma measurable_profileSpeed (c : Set X) [Countable c] :
    Measurable (profileSpeed γ c) :=
  Measurable.iSup fun _ ↦ (measurable_deriv _).enorm

/-- If `c` is dense in the image of `[a, b]`, the distances along `γ` are bounded by the integrals
of `profileSpeed γ c`. Each distance profile is the integral of its derivative, and the profile of
a point of `c` close to `γ s` recovers `edist (γ s) (γ u)` up to a small error. -/
private lemma edist_le_lintegral_profileSpeed (hγ : AbsolutelyContinuousOnInterval γ a b)
    {c : Set X} (hγc : γ '' uIcc a b ⊆ closure c) {s u : ℝ} (hs : s ∈ uIcc a b)
    (hu : u ∈ uIcc a b) :
    edist (γ s) (γ u) ≤ ∫⁻ r in Ι s u, profileSpeed γ c r := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨x, hxc, hx⟩ := EMetric.mem_closure_iff.1 (hγc (mem_image_of_mem γ hs)) (ε / 2)
    (ENNReal.half_pos (ENNReal.coe_ne_zero.2 hε.ne'))
  have hprofile : ‖dist (γ u) x - dist (γ s) x‖ₑ ≤ ∫⁻ r in Ι s u, profileSpeed γ c r := by
    have hφ : AbsolutelyContinuousOnInterval (fun r ↦ dist (γ r) x) s u :=
      ((LipschitzWith.dist_left x).comp_absolutelyContinuousOnInterval hγ).mono
        (uIcc_subset_uIcc hs hu)
    rw [← hφ.integral_deriv_eq_sub, ← ofReal_norm,
      intervalIntegral.norm_integral_eq_norm_integral_uIoc, ofReal_norm]
    exact (enorm_integral_le_lintegral_enorm _).trans <| lintegral_mono fun r ↦
      le_iSup (fun y : c ↦ ‖deriv (fun r ↦ dist (γ r) y) r‖ₑ) ⟨x, hxc⟩
  have hux : edist x (γ u) ≤ edist (γ s) x + ‖dist (γ u) x - dist (γ s) x‖ₑ := by
    rw [edist_comm, edist_dist, edist_dist, Real.enorm_eq_ofReal_abs]
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    linarith [le_abs_self (dist (γ u) x - dist (γ s) x)]
  calc edist (γ s) (γ u) ≤ edist (γ s) x + edist x (γ u) := edist_triangle _ _ _
    _ ≤ edist (γ s) x + (edist (γ s) x + ‖dist (γ u) x - dist (γ s) x‖ₑ) := by gcongr
    _ = ‖dist (γ u) x - dist (γ s) x‖ₑ + (edist (γ s) x + edist (γ s) x) := by ring
    _ ≤ (∫⁻ r in Ι s u, profileSpeed γ c r) + (ε / 2 + ε / 2) := by gcongr
    _ = (∫⁻ r in Ι s u, profileSpeed γ c r) + ε := by rw [ENNReal.add_halves]

/-- For countable `c`, at almost every time of `[a, b]` every distance profile is differentiable, so
`profileSpeed γ c` is at most the lower limit of the difference quotients of `γ`. -/
private lemma ae_profileSpeed_le_liminf (hγ : AbsolutelyContinuousOnInterval γ a b) (c : Set X)
    [Countable c] :
    ∀ᵐ t, t ∈ uIcc a b →
      profileSpeed γ c t ≤ liminf (fun s ↦ edist (γ s) (γ t) / edist s t) (𝓝[≠] t) := by
  have hdiff : ∀ᵐ t, ∀ x : c, t ∈ uIcc a b → DifferentiableAt ℝ (fun r ↦ dist (γ r) x) t :=
    ae_all_iff.2 fun x ↦
      ((LipschitzWith.dist_left (x : X)).comp_absolutelyContinuousOnInterval hγ).ae_differentiableAt
  filter_upwards [hdiff] with t ht htab
  refine iSup_le fun x ↦ ?_
  rw [← (ht x htab).hasDerivAt.tendsto_edist_div.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun s ↦ ENNReal.div_le_div_right ?_ _)
  simpa using (LipschitzWith.dist_left (x : X)).edist_le_mul (γ s) (γ t)

/-- The fundamental theorem for an absolutely continuous curve, with the metric derivative replaced
by the measurable density `profileSpeed γ c` for a countable set `c` dense in the image of `[a, b]`.
-/
private lemma exists_density (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ ∫⁻ r in Ι a b, m r ≠ ∞ ∧
      (∀ s ∈ uIcc a b, ∀ u ∈ uIcc a b, edist (γ s) (γ u) ≤ ∫⁻ r in Ι s u, m r) ∧
      ∀ᵐ t, t ∈ uIcc a b →
        Tendsto (fun s ↦ edist (γ s) (γ t) / edist s t) (𝓝[≠] t) (𝓝 (m t)) := by
  -- A countable dense subset `c` of the compact image of `[a, b]`.
  obtain ⟨c, hc, hγc⟩ := (isCompact_uIcc.image_of_continuousOn hγ.continuousOn').isSeparable
  have : Countable c := hc.to_subtype
  have hdist (s : ℝ) (hs : s ∈ uIcc a b) (u : ℝ) (hu : u ∈ uIcc a b) :=
    edist_le_lintegral_profileSpeed hγ hγc hs hu
  -- Integrability: `profileSpeed γ c` is below the lower, hence the upper, limit of the difference
  -- quotients, and so below the integrable derivative of the variation function.
  have hfin : ∫⁻ r in Ι a b, profileSpeed γ c r ≠ ∞ := by
    have hV := variationOnFromTo.monotoneOn hγ.boundedVariationOn'.locallyBoundedVariationOn
      left_mem_uIcc
    refine ne_top_of_le_ne_top (intervalIntegrable_iff.1 hV.intervalIntegrable_deriv).2.ne
      (lintegral_mono_ae ((ae_restrict_iff' measurableSet_uIoc).2 ?_))
    filter_upwards [ae_profileSpeed_le_liminf hγ c,
      hγ.boundedVariationOn'.ae_metricDerivative_le_enorm_deriv_variationOnFromTo]
      with t hlow hup htab
    have htab' := uIoc_subset_uIcc htab
    rw [metricDerivative_def] at hup
    exact (hlow htab').trans <| (liminf_le_limsup (by isBoundedDefault)
      (by isBoundedDefault)).trans (hup htab')
  refine ⟨profileSpeed γ c, measurable_profileSpeed c, hfin, hdist, ?_⟩
  -- Convergence: `profileSpeed γ c` is below the lower limit, and above the upper limit by the
  -- minimality of the metric derivative.
  filter_upwards [ae_profileSpeed_le_liminf hγ c,
    ae_metricDerivative_le (measurable_profileSpeed c).aemeasurable hfin hdist] with t hlow hup htab
  rw [metricDerivative_def] at hup
  exact tendsto_of_le_liminf_of_limsup_le (hlow htab) (hup htab)

/-- The fundamental theorem for an absolutely continuous curve, stated for a measurable density `m`
which agrees with the metric derivative almost everywhere on `[a, b]`. -/
private lemma exists_ae_eq_metricDerivative (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∃ m : ℝ → ℝ≥0∞, Measurable m ∧ ∫⁻ r in Ι a b, m r ≠ ∞ ∧
      (∀ s ∈ uIcc a b, ∀ u ∈ uIcc a b, edist (γ s) (γ u) ≤ ∫⁻ r in Ι s u, m r) ∧
      ∀ᵐ t, t ∈ uIcc a b → metricDerivative γ t = m t := by
  obtain ⟨m, hm, hfin, hdist, htendsto⟩ := exists_density hγ
  refine ⟨m, hm, hfin, hdist, ?_⟩
  filter_upwards [htendsto] with t ht htab using metricDerivative_eq_of_tendsto (ht htab)

/-- **Fundamental theorem for absolutely continuous curves**, existence of the metric derivative:
for an absolutely continuous curve `γ` on `[a, b]`, at almost every `t ∈ [a, b]` the difference
quotients `edist (γ s) (γ t) / edist s t` converge to the metric derivative as `s → t`. -/
theorem _root_.AbsolutelyContinuousOnInterval.ae_tendsto_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∀ᵐ t, t ∈ uIcc a b → Tendsto (fun s ↦ edist (γ s) (γ t) / edist s t) (𝓝[≠] t)
      (𝓝 (metricDerivative γ t)) := by
  obtain ⟨m, -, -, -, htendsto⟩ := exists_density hγ
  filter_upwards [htendsto] with t ht htab
  rw [metricDerivative_eq_of_tendsto (ht htab)]
  exact ht htab

/-- The metric derivative of an absolutely continuous curve on `[a, b]` is almost everywhere
measurable on `[a, b]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.aemeasurable_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AEMeasurable (metricDerivative γ) (volume.restrict (Ι a b)) := by
  obtain ⟨m, hm, -, -, heq⟩ := exists_ae_eq_metricDerivative hγ
  refine hm.aemeasurable.congr ((ae_restrict_iff' measurableSet_uIoc).2 ?_)
  filter_upwards [heq] with t ht htab using (ht (uIoc_subset_uIcc htab)).symm

/-- **Fundamental theorem for absolutely continuous curves**, integrability: the metric derivative
of an absolutely continuous curve on `[a, b]` has finite integral over `[a, b]`. -/
theorem _root_.AbsolutelyContinuousOnInterval.lintegral_metricDerivative_lt_top
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∫⁻ r in Ι a b, metricDerivative γ r < ∞ := by
  obtain ⟨m, -, hfin, -, heq⟩ := exists_ae_eq_metricDerivative hγ
  rw [lt_top_iff_ne_top, setLIntegral_congr_fun_ae measurableSet_uIoc]
  · exact hfin
  · filter_upwards [heq] with t ht htab using ht (uIoc_subset_uIcc htab)

/-- **Fundamental theorem for absolutely continuous curves**, the distance bound: along an
absolutely continuous curve on `[a, b]`, the distance between two times of `[a, b]` is at most the
integral of the metric derivative between them. -/
theorem _root_.AbsolutelyContinuousOnInterval.edist_le_lintegral_metricDerivative
    (hγ : AbsolutelyContinuousOnInterval γ a b) {s u : ℝ} (hs : s ∈ uIcc a b)
    (hu : u ∈ uIcc a b) :
    edist (γ s) (γ u) ≤ ∫⁻ r in Ι s u, metricDerivative γ r := by
  obtain ⟨m, -, -, hdist, heq⟩ := exists_ae_eq_metricDerivative hγ
  refine (hdist s hs u hu).trans_eq (setLIntegral_congr_fun_ae measurableSet_uIoc ?_)
  filter_upwards [heq] with t ht htsu
  exact (ht (uIcc_subset_uIcc hs hu (uIoc_subset_uIcc htsu))).symm

end AbsolutelyContinuous

section Converse

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- A curve whose distances on `[a, b]` are bounded by the integrals of a density `m` with finite
integral over `[a, b]` is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_edist_le_lintegral {m : ℝ → ℝ≥0∞}
    (hfin : ∫⁻ r in Ι a b, m r ≠ ∞)
    (h : ∀ s ∈ uIcc a b, ∀ u ∈ uIcc a b, edist (γ s) (γ u) ≤ ∫⁻ r in Ι s u, m r) :
    AbsolutelyContinuousOnInterval γ a b := by
  -- The integral of `m` over a union of intervals tends to `0` with the total length.
  have hT := tendsto_setLIntegral_zero (μ := volume.restrict (Ι a b)) (f := m) hfin
    (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
      a b)
  have hT' :=
    ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hT
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg) ?_
    hT'
  filter_upwards [eventually_inf_principal.2 (Eventually.of_forall fun _ hE ↦ hE)]
    with ⟨n, I⟩ ⟨hmem, hdisj⟩
  have hsub (i : ℕ) (hi : i ∈ Finset.range n) : Ι (I i).1 (I i).2 ⊆ Ι a b :=
    AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin ⟨hmem, hdisj⟩
      (Finset.mem_range.1 hi)
  have hne : ∫⁻ r in ⋃ i ∈ Finset.range n, Ι (I i).1 (I i).2, m r ∂volume.restrict (Ι a b) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)
  rw [Function.comp_apply, ← ENNReal.ofReal_le_iff_le_toReal hne,
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ dist_nonneg,
    lintegral_biUnion_finset hdisj (fun _ _ ↦ measurableSet_uIoc)]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  rw [Measure.restrict_restrict_of_subset (hsub i hi), ← edist_dist]
  exact h _ (hmem i hi).1 _ (hmem i hi).2

/-- **Absolute continuity of a metric-valued curve** is the existence of an integrable density
bounding its distances: `γ` is absolutely continuous on `[a, b]` exactly when some `m` with finite
integral over `[a, b]` bounds `edist (γ s) (γ u)` by `∫⁻ r in Ι s u, m r` for all `s, u ∈ [a, b]`.
The metric derivative is such an `m`, and by `TauCeti.ae_metricDerivative_le` it is almost
everywhere below every almost everywhere measurable one. -/
theorem absolutelyContinuousOnInterval_iff_exists_edist_le_lintegral :
    AbsolutelyContinuousOnInterval γ a b ↔ ∃ m : ℝ → ℝ≥0∞, ∫⁻ r in Ι a b, m r ≠ ∞ ∧
      ∀ s ∈ uIcc a b, ∀ u ∈ uIcc a b, edist (γ s) (γ u) ≤ ∫⁻ r in Ι s u, m r :=
  ⟨fun hγ ↦ ⟨metricDerivative γ, hγ.lintegral_metricDerivative_lt_top.ne,
      fun _ hs _ hu ↦ hγ.edist_le_lintegral_metricDerivative hs hu⟩,
    fun ⟨_, hfin, h⟩ ↦ absolutelyContinuousOnInterval_of_edist_le_lintegral hfin h⟩

end Converse

section Measurable

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {α : Type*} [MeasurableSpace α]
  {F : α → ℝ → X}

/-- For a continuous curve, the upper limit defining the metric derivative can be taken along
rational increments: `|γ'|(t)` is the infimum over `n` of the supremum of the difference quotients
`edist (γ (t + r)) (γ t) / |r|` over the rationals `0 < |r| < 1 / (n + 1)`. -/
theorem metricDerivative_eq_iInf_iSup_rat (hγ : Continuous γ) (t : ℝ) :
    metricDerivative γ t = ⨅ n : ℕ, ⨆ r ∈ {r : ℚ | r ≠ 0 ∧ |(r : ℝ)| < 1 / (n + 1)},
      edist (γ (t + r)) (γ t) / ‖(r : ℝ)‖ₑ := by
  have hden (r : ℝ) : edist (t + r) t = ‖r‖ₑ := by
    rw [edist_dist, Real.dist_eq, add_sub_cancel_left, Real.enorm_eq_ofReal_abs]
  rw [metricDerivative_def,
    (nhdsWithin_hasBasis Metric.nhds_basis_ball_inv_nat_succ {t}ᶜ).limsup_eq_iInf_iSup]
  simp only [iInf_true]
  refine iInf_congr fun n ↦ le_antisymm (iSup₂_le fun s hs ↦ ?_) (iSup₂_le fun r hr ↦ ?_)
  · -- The difference quotient is continuous at `s ≠ t`, and the times `t + r` with `r` rational
    -- are dense in the open set over which the supremum is taken.
    have hU : IsOpen (Metric.ball t (1 / (n + 1)) ∩ {t}ᶜ) :=
      Metric.isOpen_ball.inter isOpen_compl_singleton
    have hD : DenseRange fun r : ℚ ↦ t + r :=
      (Homeomorph.addLeft t).surjective.denseRange.comp Rat.denseRange_cast
        (continuous_const_add t)
    have hcl := hD.open_subset_closure_inter hU hs
    rw [mem_closure_iff_nhdsWithin_neBot] at hcl
    set V := Metric.ball t (1 / (n + 1)) ∩ {t}ᶜ ∩ range fun r : ℚ ↦ t + r
    have hq : ContinuousAt (fun x ↦ edist (γ x) (γ t) / edist x t) s :=
      ENNReal.Tendsto.div ((hγ.tendsto s).edist tendsto_const_nhds)
        (Or.inr (edist_pos.2 hs.2).ne') (tendsto_id.edist tendsto_const_nhds)
        (Or.inl (edist_ne_top s t))
    refine le_of_tendsto (hq.tendsto.mono_left (nhdsWithin_le_nhds (s := V))) ?_
    filter_upwards [self_mem_nhdsWithin] with x ⟨⟨hxb, hxt⟩, r, hr⟩
    subst hr
    refine le_iSup₂_of_le r ⟨?_, ?_⟩ (by rw [hden])
    · rintro rfl
      simp at hxt
    · rwa [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left] at hxb
  · refine le_iSup₂_of_le (t + r) ⟨?_, ?_⟩ (by rw [hden])
    · rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
      exact hr.2
    · simpa using hr.1

/-- **Joint measurability of the metric derivative** of a measurable family of continuous curves:
if each curve `F x` is continuous and the distances `edist (F x s) (F x u)` depend measurably on
`x`, then `(x, t) ↦ |(F x)'|(t)` is measurable. -/
theorem measurable_metricDerivative (hF : ∀ x, Continuous (F x))
    (hm : ∀ s u, Measurable fun x ↦ edist (F x s) (F x u)) :
    Measurable fun q : α × ℝ ↦ metricDerivative (F q.1) q.2 := by
  have h : (fun q : α × ℝ ↦ metricDerivative (F q.1) q.2) = fun q ↦ ⨅ n : ℕ,
      ⨆ r ∈ {r : ℚ | r ≠ 0 ∧ |(r : ℝ)| < 1 / (n + 1)},
        edist (F q.1 (q.2 + r)) (F q.1 q.2) / ‖(r : ℝ)‖ₑ :=
    funext fun q ↦ metricDerivative_eq_iInf_iSup_rat (hF q.1) q.2
  rw [h]
  refine Measurable.iInf fun n ↦ Measurable.biSup _ (Set.to_countable _) fun r _ ↦ ?_
  -- Each difference quotient is continuous in time and measurable in the parameter.
  have hc (x : α) : Continuous fun t : ℝ ↦ edist (F x (t + r)) (F x t) :=
    ((hF x).comp (continuous_id.add continuous_const)).edist (hF x)
  have : Measurable (Function.uncurry fun (t : ℝ) (x : α) ↦ edist (F x (t + r)) (F x t)) :=
    measurable_uncurry_of_continuous_of_measurable hc fun t ↦ hm _ _
  exact (this.comp (f := Prod.swap) measurable_swap).div_const _

/-- The metric derivative of a continuous curve is measurable. -/
theorem _root_.Continuous.measurable_metricDerivative (hγ : Continuous γ) :
    Measurable (metricDerivative γ) := by
  have h := TauCeti.measurable_metricDerivative (α := Unit) (F := fun _ ↦ γ) (fun _ ↦ hγ)
    fun _ _ ↦ measurable_const
  exact h.comp (f := fun t : ℝ ↦ ((), t)) measurable_prodMk_left

/-- On the space `C([a, b], X)` of continuous paths with its Borel structure, the metric
derivative `(γ, t) ↦ |γ'|(t)` of the path extended by constants outside `[a, b]` is jointly
measurable. -/
theorem measurable_metricDerivative_IccExtend {a b : ℝ} (hab : a ≤ b) :
    Measurable fun q : C(Icc a b, X) × ℝ ↦ metricDerivative (IccExtend hab q.1) q.2 :=
  measurable_metricDerivative (F := fun γ : C(Icc a b, X) ↦ IccExtend hab γ)
    (fun γ ↦ γ.continuous.Icc_extend') fun s u ↦ by
      simp only [IccExtend_apply]
      exact ((continuous_eval_const _).edist (continuous_eval_const _)).measurable

end Measurable

section MeasurableSet

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b : ℝ} {α : Type*}
  [MeasurableSpace α] {F : α → ℝ → X}

/-- **Absolute continuity on rational times.** A curve continuous on `[a, b]` is absolutely
continuous there exactly when its metric derivative has finite integral over `[a, b]` and bounds
the distances between the rational times of `[a, b]`:
`edist (γ q) (γ r) ≤ ∫⁻ x in Ι q r, |γ'|(x)`. -/
theorem absolutelyContinuousOnInterval_iff_forall_rat_edist_le_lintegral
    (hγ : ContinuousOn γ (uIcc a b)) :
    AbsolutelyContinuousOnInterval γ a b ↔ ∫⁻ r in Ι a b, metricDerivative γ r ≠ ∞ ∧
      ∀ q r : ℚ, (q : ℝ) ∈ uIcc a b → (r : ℝ) ∈ uIcc a b →
        edist (γ q) (γ r) ≤ ∫⁻ x in Ι (q : ℝ) r, metricDerivative γ x := by
  refine ⟨fun h ↦ ⟨h.lintegral_metricDerivative_lt_top.ne,
    fun q r hq hr ↦ h.edist_le_lintegral_metricDerivative hq hr⟩, fun ⟨hfin, h⟩ ↦
    absolutelyContinuousOnInterval_of_edist_le_lintegral hfin ?_⟩
  -- It suffices to bound the distance between times `s < u`. It is the limit of the distances
  -- between rational times of `(s, u)`, each bounded by the integral over `(s, u]`.
  have key : ∀ s ∈ uIcc a b, ∀ u ∈ uIcc a b, s < u →
      edist (γ s) (γ u) ≤ ∫⁻ x in Ι s u, metricDerivative γ x := by
    intro s hs u hu hsu
    have hsub : Icc s u ⊆ uIcc a b := Icc_subset_uIcc.trans (uIcc_subset_uIcc hs hu)
    set S := Ioo s u ×ˢ Ioo s u
    set D := range fun q : ℚ × ℚ ↦ ((q.1 : ℝ), (q.2 : ℝ))
    have hD : Dense D := Rat.denseRange_cast.prodMap Rat.denseRange_cast
    have hcl : (s, u) ∈ closure (S ∩ D) := by
      refine closure_mono (hD.open_subset_closure_inter (isOpen_Ioo.prod isOpen_Ioo))
        ?_ |> closure_closure.subset
      rw [closure_prod_eq, closure_Ioo hsu.ne]
      exact ⟨⟨le_rfl, hsu.le⟩, hsu.le, le_rfl⟩
    rw [mem_closure_iff_nhdsWithin_neBot] at hcl
    have hγ' : ContinuousOn γ (Icc s u) := hγ.mono hsub
    have h1 : ContinuousWithinAt (fun z : ℝ × ℝ ↦ γ z.1) (S ∩ D) (s, u) :=
      (hγ' s ⟨le_rfl, hsu.le⟩).comp continuousWithinAt_fst
        fun z (hz : z ∈ S ∩ D) ↦ Ioo_subset_Icc_self hz.1.1
    have h2 : ContinuousWithinAt (fun z : ℝ × ℝ ↦ γ z.2) (S ∩ D) (s, u) :=
      (hγ' u ⟨hsu.le, le_rfl⟩).comp continuousWithinAt_snd
        fun z (hz : z ∈ S ∩ D) ↦ Ioo_subset_Icc_self hz.1.2
    refine le_of_tendsto (h1.edist h2) ?_
    filter_upwards [self_mem_nhdsWithin] with z ⟨⟨hz1, hz2⟩, q, hq⟩
    subst hq
    refine (h q.1 q.2 (hsub (Ioo_subset_Icc_self hz1)) (hsub (Ioo_subset_Icc_self hz2))).trans
      (lintegral_mono_set (uIoc_subset_uIoc_of_uIcc_subset_uIcc
        (uIcc_subset_uIcc (Icc_subset_uIcc (Ioo_subset_Icc_self hz1))
          (Icc_subset_uIcc (Ioo_subset_Icc_self hz2)))))
  intro s hs u hu
  rcases lt_trichotomy s u with hsu | rfl | hus
  · exact key s hs u hu hsu
  · simp
  · rw [edist_comm, uIoc_comm]
    exact key u hu s hs hus

/-- **Measurability of absolute continuity** in a measurable family of continuous curves: if each
curve `F x` is continuous and the distances `edist (F x s) (F x u)` depend measurably on `x`, then
the parameters `x` for which `F x` is absolutely continuous on `[a, b]` form a measurable set. -/
theorem measurableSet_absolutelyContinuousOnInterval (hF : ∀ x, Continuous (F x))
    (hm : ∀ s u, Measurable fun x ↦ edist (F x s) (F x u)) (a b : ℝ) :
    MeasurableSet {x | AbsolutelyContinuousOnInterval (F x) a b} := by
  have hint (s u : ℝ) : Measurable fun x ↦ ∫⁻ r in Ι s u, metricDerivative (F x) r :=
    (measurable_metricDerivative hF hm).lintegral_prod_right'
      (f := fun q : α × ℝ ↦ metricDerivative (F q.1) q.2)
  simp_rw [absolutelyContinuousOnInterval_iff_forall_rat_edist_le_lintegral (hF _).continuousOn,
    ofPred_and, ofPred_forall]
  refine ((hint a b) (measurableSet_singleton ∞).compl).inter
    (.iInter fun q ↦ .iInter fun r ↦ ?_)
  by_cases hq : (q : ℝ) ∈ uIcc a b
  · by_cases hr : (r : ℝ) ∈ uIcc a b
    · simpa [hq, hr] using measurableSet_le (hm q r) (hint q r)
    · simp [hr]
  · simp [hq]

/-- On the space `C([a, b], X)` of continuous paths with its Borel structure, the paths whose
extension by constants outside `[a, b]` is absolutely continuous on `[s, u]` form a measurable
set. -/
theorem measurableSet_absolutelyContinuousOnInterval_IccExtend (hab : a ≤ b) (s u : ℝ) :
    MeasurableSet {γ : C(Icc a b, X) | AbsolutelyContinuousOnInterval (IccExtend hab γ) s u} :=
  measurableSet_absolutelyContinuousOnInterval (F := fun γ : C(Icc a b, X) ↦ IccExtend hab γ)
    (fun γ ↦ γ.continuous.Icc_extend') (fun s u ↦ by
      simp only [IccExtend_apply]
      exact ((continuous_eval_const _).edist (continuous_eval_const _)).measurable) s u

end MeasurableSet

end TauCeti
