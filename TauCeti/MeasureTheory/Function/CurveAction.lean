/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MetricDerivative
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.IntervalIntegral.SlidingWindow

/-!
# The `p`-action of a curve and its lower semicontinuity

For a curve `γ : ℝ → X` in an extended pseudometric space and an exponent `p`, the *`p`-action*
of `γ` over the interval between `a` and `b` is `A_p(γ) = ∫ |γ'|(t) ^ p dt`, the integral of the
`p`-th power of the metric derivative `|γ'|`, with no factor `1 / p`. The curves of finite
`p`-action among the absolutely continuous ones are the curves `ACᵖ` of Ambrosio–Gigli–Savaré, and
the action measures the cost of a path in the dynamic formulation of optimal transport and in
metric gradient flows.

The main results concern an absolutely continuous curve `γ` on `[a, b]` and `1 ≤ p`.

* The **Hölder estimate** `d(γ s, γ u) ^ p ≤ |u - s| ^ (p - 1) * A_p(γ; s, u)`: for `1 < p`, a
  curve of finite `p`-action is `(1 - 1 / p)`-Hölder continuous.
* The **difference-quotient formula**: the action is the limit, as `h → 0⁺`, of the integrated
  difference quotients `∫_a^(b - h) (d(γ t, γ (t + h)) / h) ^ p dt`. Each of these is at most the
  action, by the Hölder estimate on the windows `[t, t + h]` and Tonelli's theorem, and the action
  is at most their lower limit by Fatou's lemma, since the quotients tend to `|γ'|(t)` at almost
  every `t`.
* **Lower semicontinuity**: if curves `γᵢ`, eventually absolutely continuous on `[a, b]`, converge
  pointwise on `[a, b]`, along a countably generated filter, to an absolutely continuous curve `γ`,
  then `A_p(γ) ≤ liminf A_p(γᵢ)`. For each step `h`, Fatou's lemma passes the integrated difference
  quotients to the limit, and the difference-quotient formula recovers the action.
* For `1 < p`, a pointwise limit of eventually absolutely continuous curves whose actions have
  finite lower limit is itself absolutely continuous, by the Hölder estimate on finite unions of
  intervals. Lower semicontinuity therefore holds with no hypothesis on the limit curve.

The action is moreover a measurable function of the curve in a measurable family of continuous
curves, in particular on the path space `C([a, b], X)` with its Borel structure, so that it can be
integrated against a dynamic plan.

The difference-quotient formula is the metric counterpart of the characterisation of the Sobolev
space `W^{1,p}` on an interval by difference quotients.

## Main definitions

* `TauCeti.curveAction p γ a b`: the `p`-action `∫ t in Ι a b, |γ'|(t) ^ p` of `γ`.

## Main results

* `AbsolutelyContinuousOnInterval.edist_rpow_le_mul_curveAction`: the Hölder estimate.
* `AbsolutelyContinuousOnInterval.lintegral_edist_div_rpow_le_curveAction` and
  `AbsolutelyContinuousOnInterval.tendsto_lintegral_edist_div_rpow`: the integrated difference
  quotients are bounded by the action and converge to it.
* `TauCeti.absolutelyContinuousOnInterval_of_tendsto_of_liminf_ne_top`: for `1 < p`, pointwise
  limits of curves with bounded actions are absolutely continuous.
* `TauCeti.curveAction_le_liminf` and `TauCeti.curveAction_le_liminf_of_one_lt`: lower
  semicontinuity of the action under pointwise convergence.
* `TauCeti.measurable_curveAction` and `TauCeti.measurable_curveAction_IccExtend`: measurability
  of the action in a measurable family of continuous curves and on the path space `C([a, b], X)`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Definition 1.1.1 and Theorem 1.1.2.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer
  2011, Section 8.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Interval

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {p : ℝ} {γ : ℝ → X}

/-- The *`p`-action* `∫ |γ'|(t) ^ p dt` of a curve `γ : ℝ → X` over the interval between `a` and
`b`: the integral of the `p`-th power of its metric derivative, with no factor `1 / p`. When `X`
is a pseudometric space and `1 ≤ p`: for a curve absolutely continuous on `[a, b]` with `a ≤ b`,
the integrated difference quotients converge to it as the step tends to `0⁺`
(`AbsolutelyContinuousOnInterval.tendsto_lintegral_edist_div_rpow`); and it is lower
semicontinuous under pointwise convergence on `[a, b]`, along a countably generated filter, of
eventually absolutely continuous curves to an absolutely continuous one
(`TauCeti.curveAction_le_liminf`). -/
def curveAction (p : ℝ) (γ : ℝ → X) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ι a b, metricDerivative γ t ^ p

/-- The defining formula of the `p`-action, as an integral of a power of the metric derivative. -/
theorem curveAction_def (p : ℝ) (γ : ℝ → X) (a b : ℝ) :
    curveAction p γ a b = ∫⁻ t in Ι a b, metricDerivative γ t ^ p :=
  (rfl)

/-- The `p`-action does not depend on the orientation of the interval. -/
theorem curveAction_comm (p : ℝ) (γ : ℝ → X) (a b : ℝ) :
    curveAction p γ a b = curveAction p γ b a := by
  rw [curveAction_def, curveAction_def, uIoc_comm]

/-- The `p`-action over a degenerate interval vanishes. -/
@[simp]
theorem curveAction_self (p : ℝ) (γ : ℝ → X) (a : ℝ) : curveAction p γ a a = 0 := by
  simp [curveAction_def]

/-- The `p`-action is monotone in the interval. -/
theorem curveAction_mono (p : ℝ) (γ : ℝ → X) {a b s u : ℝ} (h : Ι s u ⊆ Ι a b) :
    curveAction p γ s u ≤ curveAction p γ a b :=
  lintegral_mono_set h

/-- The `p`-action is additive over adjacent intervals. -/
theorem curveAction_add (p : ℝ) (γ : ℝ → X) {a b c : ℝ} (hb : b ∈ uIcc a c) :
    curveAction p γ a b + curveAction p γ b c = curveAction p γ a c := by
  rw [curveAction_def, curveAction_def, curveAction_def, ← uIoc_union_uIoc hb,
    lintegral_union measurableSet_uIoc]
  rcases mem_uIcc.1 hb with ⟨hab, hbc⟩ | ⟨hcb, hba⟩
  · rw [uIoc_of_le hab, uIoc_of_le hbc]
    exact Ioc_disjoint_Ioc_of_le le_rfl
  · rw [uIoc_of_ge hba, uIoc_of_ge hcb]
    exact (Ioc_disjoint_Ioc_of_le le_rfl).symm

/-- The `p`-action of a `K`-Lipschitz curve over the interval between `a` and `b` is at most
`K ^ p` times the length of the interval. -/
theorem _root_.LipschitzWith.curveAction_le {K : ℝ≥0} (hγ : LipschitzWith K γ) (hp : 0 ≤ p)
    (a b : ℝ) : curveAction p γ a b ≤ (K : ℝ≥0∞) ^ p * edist a b := by
  calc curveAction p γ a b ≤ ∫⁻ _ in Ι a b, (K : ℝ≥0∞) ^ p :=
        lintegral_mono fun t ↦ ENNReal.rpow_le_rpow (hγ.metricDerivative_le t) hp
    _ = (K : ℝ≥0∞) ^ p * edist a b := by
        rw [setLIntegral_const, Real.volume_uIoc, edist_dist a b, Real.dist_eq, abs_sub_comm]

section Measurable

variable {α : Type*} [MeasurableSpace α] {F : α → ℝ → X}

/-- **Measurability of the action** in a measurable family of continuous curves: if each curve
`F x` is continuous and the distances `edist (F x s) (F x u)` depend measurably on `x`, then
`x ↦ A_p(F x)` is measurable. -/
theorem measurable_curveAction (hF : ∀ x, Continuous (F x))
    (hm : ∀ s u, Measurable fun x ↦ edist (F x s) (F x u)) (p a b : ℝ) :
    Measurable fun x ↦ curveAction p (F x) a b := by
  have h : Measurable fun q : α × ℝ ↦ metricDerivative (F q.1) q.2 ^ p :=
    (measurable_metricDerivative hF hm).pow_const p
  simp only [curveAction_def]
  exact h.lintegral_prod_right' (ν := volume.restrict (Ι a b))

/-- On the space `C([a, b], X)` of continuous paths with its Borel structure, the `p`-action over
`[s, u]` of the path extended by constants outside `[a, b]` is a measurable function of the
path. -/
theorem measurable_curveAction_IccExtend {a b : ℝ} (hab : a ≤ b) (p s u : ℝ) :
    Measurable fun γ : C(Icc a b, X) ↦ curveAction p (IccExtend hab γ) s u := by
  have h : Measurable fun q : C(Icc a b, X) × ℝ ↦ metricDerivative (IccExtend hab q.1) q.2 ^ p :=
    (measurable_metricDerivative_IccExtend hab).pow_const p
  simp only [curveAction_def]
  exact h.lintegral_prod_right' (ν := volume.restrict (Ι s u))

end Measurable

end PseudoEMetricSpace

section AbsolutelyContinuous

variable {X : Type*} [PseudoMetricSpace X] {p : ℝ} {γ : ℝ → X} {a b : ℝ}

/-- **Hölder estimate** along a curve: if `γ` is absolutely continuous on `[a, b]` and `1 ≤ p`,
then `edist (γ s) (γ u) ^ p ≤ edist s u ^ (p - 1) * curveAction p γ s u` for all `s, u ∈ [a, b]`.
In particular a curve of finite `p`-action with `1 < p` is `(1 - 1 / p)`-Hölder continuous. -/
theorem _root_.AbsolutelyContinuousOnInterval.edist_rpow_le_mul_curveAction
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hp : 1 ≤ p) {s u : ℝ} (hs : s ∈ uIcc a b)
    (hu : u ∈ uIcc a b) :
    edist (γ s) (γ u) ^ p ≤ edist s u ^ (p - 1) * curveAction p γ s u := by
  calc edist (γ s) (γ u) ^ p ≤ (∫⁻ r in Ι s u, metricDerivative γ r) ^ p :=
        ENNReal.rpow_le_rpow (hγ.edist_le_lintegral_metricDerivative hs hu) (by linarith)
    _ ≤ (volume.restrict (Ι s u)) univ ^ (p - 1) * ∫⁻ r in Ι s u, metricDerivative γ r ^ p :=
        rpow_lintegral_le_measure_univ_rpow_mul
          (hγ.mono (uIcc_subset_uIcc hs hu)).aemeasurable_metricDerivative hp
    _ = edist s u ^ (p - 1) * curveAction p γ s u := by
        rw [Measure.restrict_apply_univ, Real.volume_uIoc, curveAction_def, edist_dist s u,
          Real.dist_eq, abs_sub_comm]

/-- The two endpoints of a window `[t, t + h]` starting at `t ∈ Ioc a (b - h)` lie in `[a, b]`. -/
private lemma mem_uIcc_of_mem_Ioc_sub {h t : ℝ} (hh : 0 ≤ h) (ht : t ∈ Ioc a (b - h)) :
    t ∈ uIcc a b ∧ t + h ∈ uIcc a b :=
  ⟨mem_uIcc.2 (Or.inl ⟨ht.1.le, by linarith [ht.2]⟩),
    mem_uIcc.2 (Or.inl ⟨by linarith [ht.1], by linarith [ht.2]⟩)⟩

/-- The difference quotients `(edist (γ t) (γ (t + h)) / h) ^ p` over the starting points of the
windows `[t, t + h]` in `[a, b]` are almost everywhere measurable, as `γ` is continuous on
`[a, b]`. -/
private lemma aemeasurable_edist_div_rpow (hγ : AbsolutelyContinuousOnInterval γ a b) {h : ℝ}
    (hh : 0 ≤ h) :
    AEMeasurable (fun t ↦ (edist (γ t) (γ (t + h)) / ENNReal.ofReal h) ^ p)
      (volume.restrict (Ioc a (b - h))) := by
  have hc : ContinuousOn (fun t ↦ edist (γ t) (γ (t + h))) (Ioc a (b - h)) :=
    continuous_edist.comp_continuousOn
      ((hγ.continuousOn'.mono fun t ht ↦ (mem_uIcc_of_mem_Ioc_sub hh ht).1).prodMk
        (hγ.continuousOn'.comp (continuous_id.add continuous_const).continuousOn fun t ht ↦
          (mem_uIcc_of_mem_Ioc_sub hh ht).2))
  exact (by fun_prop : Measurable fun e : ℝ≥0∞ ↦ (e / ENNReal.ofReal h) ^ p).comp_aemeasurable
    (hc.aemeasurable measurableSet_Ioc)

/-- The integrated `p`-th power of the difference quotients of an absolutely continuous curve over
a step `h > 0` is at most its `p`-action, for `1 ≤ p`. -/
theorem _root_.AbsolutelyContinuousOnInterval.lintegral_edist_div_rpow_le_curveAction
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hp : 1 ≤ p) {h : ℝ} (hh : 0 < h) :
    ∫⁻ t in Ioc a (b - h), (edist (γ t) (γ (t + h)) / ENNReal.ofReal h) ^ p ≤
      curveAction p γ a b := by
  rcases lt_or_ge b a with hba | hab
  · simp [Ioc_eq_empty_of_le (show b - h ≤ a by linarith)]
  set H := ENNReal.ofReal h
  have hH : H ≠ 0 := ENNReal.ofReal_pos.2 hh |>.ne'
  -- On each window, the Hölder estimate bounds the difference quotient by the window average.
  have hwindow : ∀ t ∈ Ioc a (b - h), (edist (γ t) (γ (t + h)) / H) ^ p ≤
      H⁻¹ * ∫⁻ r in Ioc t (t + h), metricDerivative γ r ^ p := by
    intro t ht
    obtain ⟨hta, htb⟩ := mem_uIcc_of_mem_Ioc_sub hh.le ht
    have hHölder := hγ.edist_rpow_le_mul_curveAction hp hta htb
    rw [curveAction_def, uIoc_of_le (by linarith), edist_dist t, Real.dist_eq, abs_sub_comm,
      add_sub_cancel_left, abs_of_pos hh] at hHölder
    rw [ENNReal.div_rpow_of_nonneg _ _ (by linarith)]
    refine ENNReal.div_le_of_le_mul (hHölder.trans_eq ?_)
    rw [ENNReal.rpow_sub _ _ hH ENNReal.ofReal_ne_top, ENNReal.rpow_one, div_eq_mul_inv]
    ring
  have hF : AEMeasurable (fun r ↦ metricDerivative γ r ^ p) (volume.restrict (Ioc a b)) := by
    simpa [uIoc_of_le hab] using hγ.aemeasurable_metricDerivative.pow_const p
  calc ∫⁻ t in Ioc a (b - h), (edist (γ t) (γ (t + h)) / H) ^ p
      ≤ ∫⁻ t in Ioc a (b - h), H⁻¹ * ∫⁻ r in Ioc t (t + h), metricDerivative γ r ^ p :=
        setLIntegral_mono' measurableSet_Ioc hwindow
    _ = H⁻¹ * ∫⁻ t in Ioc a (b - h), ∫⁻ r in Ioc t (t + h), metricDerivative γ r ^ p :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hH)
    _ ≤ H⁻¹ * (H * curveAction p γ a b) := by
        gcongr
        rw [curveAction_def, uIoc_of_le hab]
        exact setLIntegral_setLIntegral_Ioc_add_le hF h
    _ = curveAction p γ a b := ENNReal.inv_mul_cancel_left hH ENNReal.ofReal_ne_top

/-- The `p`-action of a curve absolutely continuous on `[a, b]` is at most the lower limit of its
integrated difference quotients as `h → 0⁺`, by Fatou's lemma: at almost every time the difference
quotients tend to the metric derivative. -/
private lemma curveAction_le_liminf_lintegral_edist_div_rpow
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    curveAction p γ a b ≤ liminf (fun h ↦
      ∫⁻ t in Ioc a (b - h), (edist (γ t) (γ (t + h)) / ENNReal.ofReal h) ^ p) (𝓝[>] 0) := by
  -- The quotients, extended by zero to all of `Ioc a b` and to the steps `h ≤ 0`.
  let f (h t : ℝ) : ℝ≥0∞ := if 0 < h then
    (Ioc a (b - h)).indicator (fun t ↦ (edist (γ t) (γ (t + h)) / ENNReal.ofReal h) ^ p) t
    else 0
  have hf_int : ∀ᶠ h in 𝓝[>] 0, ∫⁻ t in Ioc a b, f h t =
      ∫⁻ t in Ioc a (b - h), (edist (γ t) (γ (t + h)) / ENNReal.ofReal h) ^ p := by
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    simp only [f, hh, ↓reduceIte]
    rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Ioc_inter_Ioc, max_self, min_eq_left (by linarith)]
  have hf_meas (h : ℝ) : AEMeasurable (f h) (volume.restrict (Ioc a b)) := by
    by_cases hh : 0 < h
    · simp only [f, hh, ↓reduceIte]
      exact ((aemeasurable_indicator_iff measurableSet_Ioc).2
        (aemeasurable_edist_div_rpow hγ hh.le)).restrict
    · simp only [f, hh, ↓reduceIte]
      exact aemeasurable_const
  -- At almost every `t`, the quotients converge to the metric derivative.
  have hf_lim : ∀ᵐ t ∂volume.restrict (Ioc a b),
      Tendsto (fun h ↦ f h t) (𝓝[>] 0) (𝓝 (metricDerivative γ t ^ p)) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hγ.ae_tendsto_metricDerivative, volume.ae_ne b] with t ht htb hti
    have hshift : Tendsto (fun h ↦ t + h) (𝓝[>] 0) (𝓝[≠] t) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_const.add continuous_id).tendsto' 0 t (add_zero t)).mono_left
          nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      simp [hh.ne']
    refine ((ENNReal.continuous_rpow_const.tendsto _).comp
      ((ht (mem_uIcc.2 (Or.inl ⟨hti.1.le, hti.2⟩))).comp hshift)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (lt_of_le_of_ne hti.2 htb))] with h hh
    simp only [Function.comp_apply, f, hh.1, ↓reduceIte,
      indicator_of_mem (show t ∈ Ioc a (b - h) from ⟨hti.1, by linarith [hh.2]⟩)]
    rw [edist_comm (γ t), edist_dist (t + h) t, Real.dist_eq, add_sub_cancel_left,
      abs_of_pos hh.1]
  calc curveAction p γ a b = ∫⁻ t in Ioc a b, liminf (fun h ↦ f h t) (𝓝[>] 0) := by
        rw [curveAction_def, uIoc_of_le hab]
        exact lintegral_congr_ae (hf_lim.mono fun t ht ↦ ht.liminf_eq.symm)
    _ ≤ liminf (fun h ↦ ∫⁻ t in Ioc a b, f h t) (𝓝[>] 0) := lintegral_liminf_le' hf_meas
    _ = _ := liminf_congr hf_int

/-- **Difference-quotient formula for the action.** For a curve `γ` absolutely continuous on
`[a, b]` and `1 ≤ p`, the integrated `p`-th powers of the difference quotients
`∫⁻ t in Ioc a (b - h), (edist (γ t) (γ (t + h)) / h) ^ p` converge to the `p`-action of `γ` as
`h → 0⁺`. -/
theorem _root_.AbsolutelyContinuousOnInterval.tendsto_lintegral_edist_div_rpow
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hp : 1 ≤ p) (hab : a ≤ b) :
    Tendsto (fun h ↦ ∫⁻ t in Ioc a (b - h), (edist (γ t) (γ (t + h)) / ENNReal.ofReal h) ^ p)
      (𝓝[>] 0) (𝓝 (curveAction p γ a b)) := by
  refine tendsto_of_le_liminf_of_limsup_le (curveAction_le_liminf_lintegral_edist_div_rpow hγ hab)
    (limsup_le_of_le (by isBoundedDefault) ?_)
  filter_upwards [self_mem_nhdsWithin] with h hh using
    hγ.lintegral_edist_div_rpow_le_curveAction hp hh

/-- The Hölder estimate on a finite disjoint family of intervals in `[a, b]`: the `p`-th power of
the sum of the distances along `γ` across the intervals is at most the measure of their union to
the power `p - 1`, times the `p`-action of `γ` over `[a, b]`. -/
private lemma _root_.AbsolutelyContinuousOnInterval.sum_edist_rpow_le_mul_curveAction
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hp : 1 ≤ p) {k : ℕ} {I : ℕ → ℝ × ℝ}
    (hE : (k, I) ∈ AbsolutelyContinuousOnInterval.disjWithin a b) :
    (∑ j ∈ Finset.range k, edist (γ (I j).1) (γ (I j).2)) ^ p ≤
      volume (⋃ j ∈ Finset.range k, Ι (I j).1 (I j).2) ^ (p - 1) * curveAction p γ a b := by
  set U := ⋃ j ∈ Finset.range k, Ι (I j).1 (I j).2
  have hU : U ⊆ Ι a b := AbsolutelyContinuousOnInterval.biUnion_uIoc_subset_of_mem_disjWithin hE
  calc (∑ j ∈ Finset.range k, edist (γ (I j).1) (γ (I j).2)) ^ p
      ≤ (∑ j ∈ Finset.range k, ∫⁻ r in Ι (I j).1 (I j).2, metricDerivative γ r) ^ p :=
        ENNReal.rpow_le_rpow (Finset.sum_le_sum fun j hj ↦
          hγ.edist_le_lintegral_metricDerivative (hE.1 j hj).1 (hE.1 j hj).2) (by linarith)
    _ = (∫⁻ r in U, metricDerivative γ r) ^ p := by
        rw [lintegral_biUnion_finset hE.2 fun _ _ ↦ measurableSet_uIoc]
    _ ≤ (volume.restrict U) univ ^ (p - 1) * ∫⁻ r in U, metricDerivative γ r ^ p :=
        rpow_lintegral_le_measure_univ_rpow_mul
          (hγ.aemeasurable_metricDerivative.mono_measure (Measure.restrict_mono hU le_rfl)) hp
    _ ≤ volume U ^ (p - 1) * curveAction p γ a b := by
        rw [Measure.restrict_apply_univ, curveAction_def]
        gcongr

end AbsolutelyContinuous

section LowerSemicontinuous

variable {X : Type*} [PseudoMetricSpace X] {p : ℝ} {γ : ℝ → X} {a b : ℝ} {ι : Type*}
  {l : Filter ι} {γs : ι → ℝ → X}

/-- For `1 < p`, a pointwise limit on `[a, b]` of curves `γs i`, eventually absolutely continuous
on `[a, b]`, whose `p`-actions have finite lower limit is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_tendsto_of_liminf_ne_top (hp : 1 < p)
    (hγs : ∀ᶠ i in l, AbsolutelyContinuousOnInterval (γs i) a b)
    (hlim : ∀ t ∈ uIcc a b, Tendsto (fun i ↦ γs i t) l (𝓝 (γ t)))
    (hA : liminf (fun i ↦ curveAction p (γs i) a b) l ≠ ∞) :
    AbsolutelyContinuousOnInterval γ a b := by
  obtain ⟨C, hAC, hC⟩ := exists_between (lt_top_iff_ne_top.2 hA)
  have hfreq : ∃ᶠ i in l, curveAction p (γs i) a b < C := frequently_lt_of_liminf_lt
    (by isBoundedDefault) hAC
  -- The measure of the union of the intervals of a disjoint family in `[a, b]`.
  let V (E : ℕ × (ℕ → ℝ × ℝ)) : ℝ≥0∞ :=
    volume.restrict (Ι a b) (⋃ i ∈ Finset.range E.1, Ι (E.2 i).1 (E.2 i).2)
  -- The Hölder estimate on the union of the intervals bounds the distances along `γ`.
  have key : ∀ E ∈ AbsolutelyContinuousOnInterval.disjWithin a b,
      ∑ i ∈ Finset.range E.1, edist (γ (E.2 i).1) (γ (E.2 i).2) ≤ (V E ^ (p - 1) * C) ^ p⁻¹ := by
    rintro ⟨k, I⟩ hE
    set U := ⋃ i ∈ Finset.range k, Ι (I i).1 (I i).2
    have hVU : V (k, I) = volume U := Measure.restrict_eq_self _
      (AbsolutelyContinuousOnInterval.biUnion_uIoc_subset_of_mem_disjWithin hE)
    have hsum : Tendsto (fun i ↦ (∑ j ∈ Finset.range k, edist (γs i (I j).1) (γs i (I j).2)) ^ p)
        l (𝓝 ((∑ j ∈ Finset.range k, edist (γ (I j).1) (γ (I j).2)) ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp (tendsto_finsetSum _ fun j hj ↦
        (hlim _ (hE.1 j hj).1).edist (hlim _ (hE.1 j hj).2))
    have hle : _ ≤ volume U ^ (p - 1) * C := le_of_tendsto_of_frequently hsum
      ((hfreq.and_eventually hγs).mono fun i hi ↦
        (hi.2.sum_edist_rpow_le_mul_curveAction hp.le hE).trans (by gcongr; exact hi.1.le))
    rw [hVU]
    exact (ENNReal.le_rpow_inv_iff (by positivity)).2 hle
  -- The bound tends to zero with the total length of the family.
  have hΦ : Tendsto (fun x : ℝ≥0∞ ↦ (x ^ (p - 1) * C) ^ p⁻¹) (𝓝 0) (𝓝 0) := by
    have h₁ : Tendsto (fun x : ℝ≥0∞ ↦ x ^ (p - 1) * C) (𝓝 0) (𝓝 0) := by
      simpa [ENNReal.zero_rpow_of_pos (sub_pos.2 hp)] using
        ENNReal.Tendsto.mul_const ((ENNReal.continuous_rpow_const (y := p - 1)).tendsto 0)
          (Or.inr hC.ne)
    simpa [ENNReal.zero_rpow_of_pos (inv_pos.2 (zero_lt_one.trans hp)), Function.comp_def] using
      ((ENNReal.continuous_rpow_const (y := p⁻¹)).tendsto 0).comp h₁
  have hT : Tendsto (fun E ↦ ((V E ^ (p - 1) * C) ^ p⁻¹).toReal)
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) := by
    have := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp (hΦ.comp
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        a b))
    rwa [ENNReal.toReal_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg) ?_ hT
  filter_upwards [eventually_inf_principal.2 (Eventually.of_forall fun _ hE ↦ hE)] with E hE
  have hne : (V E ^ (p - 1) * C) ^ p⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (ne_top_of_le_ne_top
        (by simp [Real.volume_uIoc]) (measure_mono (subset_univ _)))) hC.ne)
  rw [← ENNReal.ofReal_le_iff_le_toReal hne,
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ dist_nonneg]
  simpa only [← edist_dist] using key E hE

/-- **Lower semicontinuity of the action.** If curves `γs i`, eventually absolutely continuous on
`[a, b]`, converge pointwise on `[a, b]` along a countably generated filter to a curve `γ`
absolutely continuous on `[a, b]`, then the `p`-action of `γ` is at most the lower limit of their
`p`-actions, for `1 ≤ p`. -/
theorem curveAction_le_liminf [l.IsCountablyGenerated] (hp : 1 ≤ p)
    (hγs : ∀ᶠ i in l, AbsolutelyContinuousOnInterval (γs i) a b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hlim : ∀ t ∈ uIcc a b, Tendsto (fun i ↦ γs i t) l (𝓝 (γ t))) :
    curveAction p γ a b ≤ liminf (fun i ↦ curveAction p (γs i) a b) l := by
  wlog hab : a ≤ b generalizing a b
  · simp_rw [curveAction_comm p _ a b]
    exact this (hγs.mono fun _ hi ↦ hi.symm) hγ.symm (by rwa [uIcc_comm]) (le_of_not_ge hab)
  rcases l.eq_or_neBot with rfl | hl
  · simp
  -- Replacing the curves that are not absolutely continuous by `γ` changes neither the pointwise
  -- limit nor the lower limit of the actions, and makes every curve absolutely continuous.
  classical
  set γs' : ι → ℝ → X := fun i ↦ if AbsolutelyContinuousOnInterval (γs i) a b then γs i else γ
  have heq : ∀ᶠ i in l, γs' i = γs i := hγs.mono fun i hi ↦ by simp [γs', hi]
  have hγs' (i : ι) : AbsolutelyContinuousOnInterval (γs' i) a b := by
    by_cases hi : AbsolutelyContinuousOnInterval (γs i) a b
    · simp [γs', hi]
    · simpa [γs', hi] using hγ
  have hlim' (t : ℝ) (ht : t ∈ uIcc a b) : Tendsto (fun i ↦ γs' i t) l (𝓝 (γ t)) :=
    (hlim t ht).congr' (heq.mono fun i hi ↦ by simp only [hi])
  rw [← liminf_congr (f := l) (u := fun i ↦ curveAction p (γs' i) a b)
    (heq.mono fun i hi ↦ by rw [hi])]
  refine le_of_tendsto (hγ.tendsto_lintegral_edist_div_rpow hp hab) ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  -- For a fixed step `h`, Fatou's lemma passes the integrated difference quotients to the limit.
  calc ∫⁻ t in Ioc a (b - h), (edist (γ t) (γ (t + h)) / ENNReal.ofReal h) ^ p
      = ∫⁻ t in Ioc a (b - h),
          liminf (fun i ↦ (edist (γs' i t) (γs' i (t + h)) / ENNReal.ofReal h) ^ p) l := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
        obtain ⟨hta, htb⟩ := mem_uIcc_of_mem_Ioc_sub hh.le ht
        exact ((ENNReal.continuous_rpow_const.tendsto _).comp (ENNReal.Tendsto.div_const
          ((hlim' t hta).edist (hlim' _ htb))
          (Or.inr (ENNReal.ofReal_pos.2 hh).ne'))).liminf_eq.symm
    _ ≤ liminf (fun i ↦ ∫⁻ t in Ioc a (b - h),
          (edist (γs' i t) (γs' i (t + h)) / ENNReal.ofReal h) ^ p) l :=
        lintegral_liminf_le' fun i ↦ aemeasurable_edist_div_rpow (hγs' i) hh.le
    _ ≤ liminf (fun i ↦ curveAction p (γs' i) a b) l :=
        liminf_le_liminf (Eventually.of_forall fun i ↦
          (hγs' i).lintegral_edist_div_rpow_le_curveAction hp hh)

/-- **Lower semicontinuity of the action** for `1 < p`: if curves `γs i`, eventually absolutely
continuous on `[a, b]`, converge pointwise on `[a, b]` along a countably generated filter to `γ`,
then the `p`-action of `γ` is at most the lower limit of their `p`-actions. When that lower limit
is finite, `γ` is absolutely continuous by
`TauCeti.absolutelyContinuousOnInterval_of_tendsto_of_liminf_ne_top`. -/
theorem curveAction_le_liminf_of_one_lt [l.IsCountablyGenerated] (hp : 1 < p)
    (hγs : ∀ᶠ i in l, AbsolutelyContinuousOnInterval (γs i) a b)
    (hlim : ∀ t ∈ uIcc a b, Tendsto (fun i ↦ γs i t) l (𝓝 (γ t))) :
    curveAction p γ a b ≤ liminf (fun i ↦ curveAction p (γs i) a b) l := by
  by_cases hA : liminf (fun i ↦ curveAction p (γs i) a b) l = ∞
  · rw [hA]
    exact le_top
  · exact curveAction_le_liminf hp.le hγs
      (absolutelyContinuousOnInterval_of_tendsto_of_liminf_ne_top hp hγs hlim hA) hlim

end LowerSemicontinuous

end TauCeti
