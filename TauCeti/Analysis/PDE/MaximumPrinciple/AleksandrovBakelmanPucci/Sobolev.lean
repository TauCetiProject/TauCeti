/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation
import TauCeti.Analysis.InnerProductSpace.Positive.Basic
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.Topology.MetricSpace.Thickening

/-!
# The Aleksandrov–Bakelman–Pucci estimate for strong solutions

The Aleksandrov–Bakelman–Pucci estimate of
`TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Basic` is proved there for `C²`
functions. This file extends it to strong solutions: functions `u ∈ W^{2,n}(Ω)`, `n` the
dimension, with a representative `ū` continuous on `closure Ω`, satisfying the differential
inequality only almost everywhere, with the weak Hessian `D²u`. This is the form consumed by the
Krylov–Safonov theory of non-divergence equations with measurable coefficients, whose solutions
are only `W^{2,n}`.

For bounded open `Ω`, `x ∈ Ω` and `m` bounding `ū` on `frontier Ω`, the measure form reads

`μ (ball 0 ((ū x - m) / diam Ω)) ≤ ∫_{Γ⁺} 1_{D²u ≤ 0} |det D²u|`

(`TauCeti.PDE.addHaar_ball_le_lintegral_abs_det_iteratedGradient`), where `Γ⁺` is the upper
contact set of `ū` and `D²u ≤ 0` means that `-D²u` is a positive operator. If
`f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu` almost everywhere on `Γ⁺` with `a` positive definite there, this gives

`ū ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / D*‖_{Lⁿ(Γ⁺)}`, with `D* = (det a)^{1/n}`

(`TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp`). Nothing is assumed of the
coefficients beyond positive definiteness on the contact set; in particular no bound on
`a / D*` is needed.

Gilbarg–Trudinger, Theorem 9.1, states the estimate under the weaker hypothesis
`u ∈ W^{2,n}_loc(Ω) ∩ C⁰(closure Ω)`. That local form remains open here. It does not follow by
applying the results of this file on interior subsets of `Ω`, because the contact set of `ū`
relative to a subset need not lie in its contact set relative to `Ω`. The proof below uses
`u ∈ W^{2,n}(Ω)` in one place only: the common integrable majorant of `|det D²vₖ|` on all of `Ω`.
A proof of the local form could keep supporting slopes of norm below `(1 - ε) (ū x - m) / diam Ω`;
their contact points lie in `{y ∈ closure Ω | m + ε (ū x - m) ≤ ū y}`, a compact subset of `Ω`
on which `W^{2,n}_loc` gives the majorant.

## The approximation

Mollify `u` at radius `δₖ / 2` and restrict to the interior sets `Uₖ = {δₖ < dist(·, Ωᶜ)}`, with
`δₖ → 0`. The mollifications `vₖ` are smooth, converge to `ū` uniformly on `Uₖ` because `ū` is
uniformly continuous on the compact set `closure Ω`, are at most `m + o(1)` on the frontier of
`Uₖ`, and their Hessians are the mollified weak Hessians, which converge to `D²u` in `Lⁿ(Ω)`
(`TauCeti.Wkp.tendsto_eLpNorm_smoothField_sub`). The `C²` estimate applies to each `vₖ` on `Uₖ`.
To pass to the limit:

* along a subsequence the Hessians converge almost everywhere and `|det D²vₖ|` has a common
  integrable majorant, built from a summable sequence of `Lⁿ` errors
  (`TauCeti.exists_strictMono_lintegral_tsum_ne_top_of_tendsto_lintegral`), so the reverse
  Fatou lemma bounds the upper limit of the integrals over the contact sets of `vₖ`;
* a point that lies in the contact sets of infinitely many `vₖ` lies in the contact set of `ū`
  (`TauCeti.PDE.mem_upperContactSet_of_frequently`);
* at such a point the negated Hessians of the `vₖ` are positive
  (`TauCeti.PDE.isPositive_neg_hessianOperator_of_mem_upperContactSet`), hence so is their limit
  `-D²u`, since the positive operators form a closed set.

On the contact set the pointwise bound `TauCeti.PDE.abs_det_le_negPart_div_card_pow_div_det`,
shared with the `C²` case, then bounds `|det D²u|` by `(f⁻ / n)ⁿ / det a`.

## Main declarations

* `TauCeti.PDE.addHaar_ball_le_lintegral_abs_det_iteratedGradient`: the Aleksandrov measure
  estimate for `W^{2,n}` functions, for any additive Haar measure.
* `TauCeti.PDE.volume_ball_le_setLIntegral_upperContactSet_of_wkp`: the measure form for strong
  subsolutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f`, `|B(0, (ū x - m) / diam Ω)| ≤ ∫_{Γ⁺} (f⁻ / n)ⁿ / det a`.
* `TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp`: **the Aleksandrov–Bakelman–Pucci
  estimate for strong subsolutions**.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.1 (Lemma 9.2, Lemma 9.3 and Theorem 9.1, for `u` continuous on `closure Ω` and in
  `W^{2,n}_loc(Ω)`).
* L. C. Evans, *Partial Differential Equations*, §5.3.1 (interior mollification).
-/

public section

noncomputable section

open Filter InnerProductSpace Matrix Metric MeasureTheory Module Set Topology TopologicalSpace
open scoped Convolution ENNReal Gradient RealInnerProductSpace

namespace TauCeti

namespace PDE

section Approximation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {u : E → ℝ} {Ω : Set E} {x y : E} {m : ℝ}

/-- **The pointwise limit of the contact integrands.** In the setting of
`mem_upperContactSet_of_frequently`, let `y ∈ Ω` be a point at which the Hessians of the `C²`
functions `v k` converge to `H`. Then the upper limit of `|det D²(v k)(y)|` restricted to the
contact sets of `v k` is at most `|det H|`, restricted to the contact set of `u` and to the
points where `H` is symmetric and nonpositive. -/
private theorem limsup_indicator_upperContactSet_le {U : ℕ → Set E} {v : ℕ → E → ℝ}
    {H : E → E →L[ℝ] E} (hu : ContinuousOn u Ω) (hUo : ∀ k, IsOpen (U k))
    (hUΩ : ∀ k, U k ⊆ Ω) (hUball : ∀ z ∈ Ω, ∃ r > 0, ∀ᶠ k in atTop, closedBall z r ⊆ U k)
    (hv : ∀ k, ContDiff ℝ 2 (v k))
    (hvu : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ U k, |v k z - u z| ≤ ε)
    (hT : y ∈ Ω → Tendsto (fun k => hessianOperator (v k) y) atTop (𝓝 (H y))) :
    limsup (fun k => (upperContactSet (v k) (U k)).indicator
      (fun y => ENNReal.ofReal |(hessianOperator (v k) y).det|) y) atTop ≤
    (upperContactSet u Ω ∩ {y | (-H y).IsPositive}).indicator
      (fun y => ENNReal.ofReal |(H y).det|) y := by
  by_cases hfreq : ∃ᶠ k in atTop, y ∈ upperContactSet (v k) (U k)
  · have hyΓ := mem_upperContactSet_of_frequently hu hUΩ hUball hvu hfreq
    have hT := hT (upperContactSet_subset hyΓ)
    have hHN : H y ∈ {T : E →L[ℝ] E | (-T).IsPositive} :=
      (ContinuousLinearMap.isClosed_setOf_isPositive.preimage
        continuous_neg).mem_of_frequently_of_tendsto
        (hfreq.mono fun k hk => isPositive_neg_hessianOperator_of_mem_upperContactSet (hUo k)
          (hv k).contDiffOn hk) hT
    rw [indicator_of_mem (mem_inter hyΓ hHN)]
    refine (limsup_le_limsup (Eventually.of_forall fun k => indicator_le_self _ _ y)).trans
      (le_of_eq ?_)
    exact (((ENNReal.continuous_ofReal.comp
      (continuous_abs.comp ContinuousLinearMap.continuous_det)).tendsto _).comp hT).limsup_eq
  · rw [not_frequently] at hfreq
    refine (limsup_le_limsup (hfreq.mono fun k hk => ?_)).trans (limsup_const_bot.trans_le
      bot_le)
    rw [indicator_of_notMem hk]
    exact le_rfl

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [μ.IsAddHaarMeasure] in
/-- **A common majorant along a subsequence.** Let `F k` be measurable operator fields converging
to `H` in `Lⁿ` on open sets `U k ⊆ Ω`, `n` the dimension, with `‖H‖ ∈ Lⁿ(Ω)`, and let the `U k`
eventually contain a ball around each point of `Ω`. Then along a subsequence the determinants
`|det F (φ j)|` on `U (φ j)` have a common integrable majorant, and `F (φ j) → H` almost
everywhere on `Ω`. -/
private theorem exists_subseq_majorant [Nontrivial E] (hΩ : IsOpen Ω) {U : ℕ → Set E}
    (hUo : ∀ k, IsOpen (U k)) (hUΩ : ∀ k, U k ⊆ Ω)
    (hUball : ∀ z ∈ Ω, ∃ r > 0, ∀ᶠ k in atTop, closedBall z r ⊆ U k)
    {F : ℕ → E → E →L[ℝ] E} (hF : ∀ k, Measurable (F k)) {H : E → E →L[ℝ] E}
    (hHm : AEStronglyMeasurable H (μ.restrict Ω)) (hH : ∫⁻ y in Ω, ‖H y‖ₑ ^ finrank ℝ E ∂μ ≠ ∞)
    (hFH : Tendsto (fun k => ∫⁻ y in U k, ‖F k y - H y‖ₑ ^ finrank ℝ E ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∃ G : E → ℝ≥0∞, ∫⁻ y, G y ∂μ ≠ ∞ ∧
      ∀ j, ∀ y ∈ U (φ j), ENNReal.ofReal |(F (φ j) y).det| ≤ G y) ∧
      ∀ᵐ y ∂μ, y ∈ Ω → Tendsto (fun j => F (φ j) y) atTop (𝓝 (H y)) := by
  set n := finrank ℝ E
  have hn : n ≠ 0 := finrank_pos.ne'
  -- A subsequence along which the `Lⁿ` errors have a summable integral.
  set D : ℕ → E → ℝ≥0∞ := fun k => (U k).indicator fun y => ‖F k y - H y‖ₑ ^ n
  have hD (k : ℕ) : AEMeasurable (D k) μ :=
    (aemeasurable_indicator_iff (hUo k).measurableSet).2 ((((hF k).aestronglyMeasurable.sub
      (hHm.mono_measure (Measure.restrict_mono (hUΩ k) le_rfl))).enorm).pow_const n)
  obtain ⟨φ, hφ, hS⟩ := exists_strictMono_lintegral_tsum_ne_top_of_tendsto_lintegral hD
    (by simpa only [D, lintegral_indicator (hUo _).measurableSet] using hFH)
  refine ⟨φ, hφ, ?_, ?_⟩
  -- The majorant `2ⁿ (‖H‖ⁿ + ∑ⱼ ‖F (φ j) - H‖ⁿ)`.
  · have hC : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    refine ⟨fun y => 2 ^ n * (Ω.indicator (fun y => ‖H y‖ₑ ^ n) y + ∑' j, D (φ j) y), ?_,
      fun j y hy => ((F (φ j) y).ofReal_abs_det_le (H y)).trans
        (mul_le_mul_right (add_le_add ?_ ?_) _)⟩
    · rw [lintegral_const_mul' _ _ hC, lintegral_add_left'
        ((aemeasurable_indicator_iff hΩ.measurableSet).2 (hHm.enorm.pow_const n)),
        lintegral_indicator hΩ.measurableSet]
      exact ENNReal.mul_ne_top hC (ENNReal.add_ne_top.2 ⟨hH, hS⟩)
    · rw [indicator_of_mem (hUΩ _ hy)]
    · exact le_trans (le_of_eq (by simp only [D, n, indicator_of_mem hy]))
        (le_tsum (fun j => D (φ j) y) j)
  -- The errors tend to `0` where the sum is finite, and `y` lies in `U (φ j)` eventually.
  · filter_upwards [ae_lt_top' (AEMeasurable.tsum fun j => hD (φ j)) hS] with y hy hyΩ
    obtain ⟨r, hr, hball⟩ := hUball y hyΩ
    have h1 : Tendsto (fun j => ‖F (φ j) y - H y‖ₑ ^ n) atTop (𝓝 0) :=
      (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hy.ne).congr'
        ((hφ.tendsto_atTop.eventually hball).mono fun j hj => by
          simp only [D, indicator_of_mem (hj (mem_closedBall_self hr.le))])
    have h2 := ((ENNReal.continuous_rpow_const (y := (n : ℝ)⁻¹)).tendsto 0).comp h1
    simp only [Function.comp_def, ENNReal.pow_rpow_inv_natCast hn,
      ENNReal.zero_rpow_of_pos (inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)))] at h2
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [edist_eq_enorm_sub] using h2

/-- **The `C²` estimate for one approximant.** Let `v` be `C²`, with `|v x - u x| ≤ ε` and
`v ≤ m + ε` on the frontier of an open set `U ⊆ Ω` containing a ball around `x`, with `Ω`
bounded. Then `μ (ball 0 ((u x - m - 2 ε) / diam Ω))` is at most the integral of `|det D²v|`
over the upper contact set of `v` on `U`. -/
private theorem addHaar_ball_sub_le_lintegral [Nontrivial E] (hΩb : Bornology.IsBounded Ω)
    {U : Set E} (hUo : IsOpen U) (hUΩ : U ⊆ Ω) {r : ℝ} (hr : 0 < r) (hxU : closedBall x r ⊆ U)
    {v : E → ℝ} (hv : ContDiff ℝ 2 v) {ε : ℝ} (hvx : |v x - u x| ≤ ε)
    (hvm : ∀ z ∈ frontier U, v z ≤ m + ε) :
    μ (ball 0 ((u x - m - 2 * ε) / diam Ω)) ≤
      ∫⁻ y in upperContactSet v U, ENNReal.ofReal |(hessianOperator v y).det| ∂μ := by
  refine le_trans ?_ (addHaar_ball_le_lintegral_abs_det_hessianOperator μ (hΩb.subset hUΩ) hUo
    hv.continuous.continuousOn hv.contDiffOn hvm (hxU (mem_closedBall_self hr.le)))
  rcases le_or_gt (u x - m - 2 * ε) 0 with ha | ha
  · rw [ball_eq_empty.2 (div_nonpos_of_nonpos_of_nonneg ha diam_nonneg), measure_empty]
    exact zero_le
  have hdU : 0 < diam U := diam_pos (infinite_of_mem_nhds x
    (hUo.mem_nhds (hxU (mem_closedBall_self hr.le)))).nontrivial (hΩb.subset hUΩ)
  refine measure_mono (ball_subset_ball ?_)
  calc (u x - m - 2 * ε) / diam Ω ≤ (u x - m - 2 * ε) / diam U :=
        div_le_div_of_nonneg_left ha.le hdU (diam_mono hUΩ hΩb)
    _ ≤ (v x - (m + ε)) / diam U :=
        div_le_div_of_nonneg_right (by linarith [(abs_le.1 hvx).1]) hdU.le

/-- **The Aleksandrov measure estimate under `C²` approximation.** Let `Ω` be bounded and open,
`u` continuous on `Ω`, and `x ∈ Ω`. Let `U k ⊆ Ω` be open sets which eventually contain a ball
around each point of `Ω`, and let `v k` be `C²` functions with `v k → u` uniformly on `U k`,
`v k ≤ m + o(1)` on the frontier of `U k`, and Hessians converging to `H` in `Lⁿ`, where
`‖H‖ ∈ Lⁿ(Ω)` and `n` is the dimension. Then `μ (ball 0 ((u x - m) / diam Ω)) ≤ ∫ |det H|`
over the points of the upper contact set of `u` on `Ω` at which `H` is symmetric and
nonpositive. -/
private theorem addHaar_ball_le_of_tendsto [Nontrivial E] (hΩb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω) (hx : x ∈ Ω)
    {U : ℕ → Set E} (hUo : ∀ k, IsOpen (U k)) (hUΩ : ∀ k, U k ⊆ Ω)
    (hUball : ∀ z ∈ Ω, ∃ r > 0, ∀ᶠ k in atTop, closedBall z r ⊆ U k)
    {v : ℕ → E → ℝ} (hv : ∀ k, ContDiff ℝ 2 (v k))
    (hvu : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ U k, |v k z - u z| ≤ ε)
    (hvm : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ frontier (U k), v k z ≤ m + ε)
    {H : E → E →L[ℝ] E} (hHm : AEStronglyMeasurable H (μ.restrict Ω))
    (hH : ∫⁻ y in Ω, ‖H y‖ₑ ^ finrank ℝ E ∂μ ≠ ∞)
    (hvH : Tendsto (fun k => ∫⁻ y in U k, ‖hessianOperator (v k) y - H y‖ₑ ^ finrank ℝ E ∂μ)
      atTop (𝓝 0)) :
    μ (ball 0 ((u x - m) / diam Ω)) ≤
      ∫⁻ y in upperContactSet u Ω,
        {y | (-H y).IsPositive}.indicator
          (fun y => ENNReal.ofReal |(H y).det|) y ∂μ := by
  have hmeas (k : ℕ) : Measurable (hessianOperator (v k)) := by
    simpa only [funext (fderiv_gradient (v k))] using measurable_fderiv ℝ (∇ (v k))
  obtain ⟨φ, hφ, ⟨G, hGfin, hG⟩, hconv⟩ :=
    exists_subseq_majorant μ hΩ hUo hUΩ hUball hmeas hHm hH hvH
  have hφt := hφ.tendsto_atTop
  -- The contact integrands along the subsequence are measurable and dominated by `G`.
  set Γ : ℕ → Set E := fun j => upperContactSet (v (φ j)) (U (φ j))
  set g : ℕ → E → ℝ≥0∞ := fun j => (Γ j).indicator
    fun y => ENNReal.ofReal |(hessianOperator (v (φ j)) y).det|
  have hΓ (j : ℕ) : MeasurableSet (Γ j) :=
    measurableSet_upperContactSet (hUo _) ((hv _).contDiffOn.of_le one_le_two)
  have hg (j : ℕ) : Measurable (g j) := (ENNReal.measurable_ofReal.comp
    (continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp
      (hmeas _)))).indicator (hΓ j)
  have hgG (j : ℕ) (y : E) : g j y ≤ G y := by
    by_cases hy : y ∈ Γ j
    · exact (indicator_of_mem hy _).trans_le (hG j y (upperContactSet_subset hy))
    · simp only [g, indicator_of_notMem hy]
      exact zero_le
  -- Their upper limit is the contact integrand of `u`.
  have hlim : ∀ᵐ y ∂μ, limsup (fun j => g j y) atTop ≤
      (upperContactSet u Ω ∩ {y | (-H y).IsPositive}).indicator
        (fun y => ENNReal.ofReal |(H y).det|) y := by
    filter_upwards [hconv] with y hy
    exact limsup_indicator_upperContactSet_le (U := fun j => U (φ j)) (v := fun j => v (φ j))
      hu (fun _ => hUo _) (fun _ => hUΩ _)
      (fun z hz => (hUball z hz).imp fun r ⟨hr, h⟩ => ⟨hr, hφt.eventually h⟩)
      (fun _ => hv _) (fun ε hε => hφt.eventually (hvu ε hε)) hy
  -- Each approximant satisfies the `C²` estimate with boundary value `m + ε`; let `ε → 0`.
  refine Measure.measure_ball_le_of_forall_lt μ fun s hs => ?_
  have hd : 0 < diam Ω := diam_pos (infinite_of_mem_nhds x (hΩ.mem_nhds hx)).nontrivial hΩb
  set ε := ((u x - m) / diam Ω - s) * diam Ω / 2
  have hε : 0 < ε := by
    have : 0 < (u x - m) / diam Ω - s := sub_pos.2 hs
    positivity
  have hsε : s = (u x - m - 2 * ε) / diam Ω := by
    simp only [ε]
    field_simp
    ring
  obtain ⟨r, hr, hball⟩ := hUball x hx
  have hev : ∀ᶠ j in atTop, μ (ball 0 s) ≤ ∫⁻ y, g j y ∂μ := by
    filter_upwards [hφt.eventually hball, hφt.eventually (hvu ε hε),
      hφt.eventually (hvm ε hε)] with j hj hju hjm
    rw [hsε, lintegral_indicator (hΓ j)]
    exact addHaar_ball_sub_le_lintegral μ hΩb (hUo _) (hUΩ _) hr hj (hv _)
      (hju x (hj (mem_closedBall_self hr.le))) hjm
  calc μ (ball 0 s) ≤ limsup (fun j => ∫⁻ y, g j y ∂μ) atTop :=
        le_limsup_of_frequently_le hev.frequently
    _ ≤ ∫⁻ y, limsup (fun j => g j y) atTop ∂μ :=
        limsup_lintegral_le G hg (fun j => ae_of_all _ (hgG j)) hGfin
    _ ≤ _ := (lintegral_mono_ae hlim).trans (by
        rw [← indicator_indicator]
        exact lintegral_indicator_le _ _)

end Approximation

section Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {ū : E → ℝ} {x : E} {m : ℝ}

/-- On open sets `U k ⊆ Ω` whose points have their bump ball in `Ω`, the Hessians of the
mollifications of `u ∈ W^{2,n}(Ω)` converge to the weak Hessian in `Lⁿ` as the bump radii tend
to zero. -/
private theorem tendsto_setLIntegral_hessianOperator_smoothField_sub
    [Fact (1 ≤ (finrank ℝ E : ℝ≥0∞))] (hn : 1 ≤ finrank ℝ E) (u : Wkp μ Ω (finrank ℝ E) 2)
    {U : ℕ → Set E} (hUo : ∀ k, IsOpen (U k)) (hUΩ : ∀ k, U k ⊆ Ω)
    {φ : ℕ → ContDiffBump (0 : E)} (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0))
    (hball : ∀ k, ∀ y ∈ U k, closedBall y (φ k).rOut ⊆ Ω) :
    Tendsto (fun k => ∫⁻ y in U k, ‖hessianOperator (Wkp.smoothField (φ k) (Wkp.value 2 u)) y -
      Wkp.iteratedGradient 1 u y‖ₑ ^ finrank ℝ E ∂μ) atTop (𝓝 0) := by
  have h := (ENNReal.continuous_pow (finrank ℝ E)).tendsto 0 |>.comp
    (Wkp.tendsto_eLpNorm_smoothField_sub (ENNReal.natCast_ne_top _) hφ
      (Wkp.iteratedGradient 1 u))
  rw [zero_pow (Nat.one_le_iff_ne_zero.1 hn)] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun k => ?_
  rw [Function.comp_apply, ← lintegral_enorm_pow_eq_eLpNorm_pow (Nat.one_le_iff_ne_zero.1 hn)
    ((Wkp.contDiff_smoothField _ _).continuous.aestronglyMeasurable.sub
      (Lp.aestronglyMeasurable _))]
  refine (setLIntegral_congr_fun (hUo k).measurableSet fun y hy => ?_).trans_le
    (lintegral_mono_set (hUΩ k))
  rw [← fderiv_gradient,
    Wkp.fderiv_gradient_smoothField u (φ k) (((hUo k).eventually_mem hy).mono (hball k)),
    Pi.sub_apply]

/-- **The Aleksandrov measure estimate for `W^{2,n}` functions** (Gilbarg–Trudinger, Lemma 9.2
for strong solutions). Let `Ω` be a bounded open subset of a real inner product space of
dimension `n ≥ 1`, let `u ∈ W^{2,n}(Ω)` have a representative `ū` continuous on `closure Ω`,
and let `m` bound `ū` on `frontier Ω`. Then for `x ∈ Ω` and every additive Haar measure `μ`,
`μ (ball 0 ((ū x - m) / diam Ω)) ≤ ∫ |det D²u|`, the integral taken over the points of the upper
contact set of `ū` at which the weak Hessian `D²u` is symmetric and nonpositive. -/
theorem addHaar_ball_le_lintegral_abs_det_iteratedGradient {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hΩb : Bornology.IsBounded (Ω : Set E)) (hp : p = finrank ℝ E) (u : Wkp μ Ω p 2)
    (hcont : ContinuousOn ū (closure Ω))
    (hū : (Wkp.value 2 u : E → ℝ) =ᵐ[μ.restrict Ω] ū) (hm : ∀ z ∈ frontier (Ω : Set E), ū z ≤ m)
    (hx : x ∈ Ω) :
    μ (ball 0 ((ū x - m) / diam (Ω : Set E))) ≤
      ∫⁻ y in upperContactSet ū Ω,
        {y | (-(Wkp.iteratedGradient 1 u y : E →L[ℝ] E)).IsPositive}.indicator
        (fun y => ENNReal.ofReal |(Wkp.iteratedGradient 1 u y : E →L[ℝ] E).det|) y ∂μ := by
  subst hp
  have hn1 : 1 ≤ finrank ℝ E := by exact_mod_cast (Fact.out : 1 ≤ (finrank ℝ E : ℝ≥0∞))
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hn1
  -- The interior sets `U k = {δ k < dist(·, Ωᶜ)}` and mollifiers of radius `δ k / 2`.
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ (k : ℕ) : 0 < δ k := Nat.one_div_pos_of_nat
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set U : ℕ → Set E := fun k => {y | δ k < infDist y (Ω : Set E)ᶜ}
  set φ : ℕ → ContDiffBump (0 : E) := fun k =>
    ⟨δ k / 4, δ k / 2, by have := hδ k; positivity, by have := hδ k; linarith⟩
  have hφ0 : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    simpa using hδ0.div_const 2
  set v : ℕ → E → ℝ := fun k => Wkp.smoothField (φ k) (Wkp.value 2 u)
  have hball (k : ℕ) {y : E} (hy : δ k ≤ infDist y (Ω : Set E)ᶜ) :
      closedBall y (φ k).rOut ⊆ Ω :=
    (closedBall_subset_ball ((half_lt_self (hδ k)).trans_le hy)).trans ball_infDist_compl_subset
  have hUo (k : ℕ) : IsOpen (U k) := isOpen_lt continuous_const (continuous_infDist_pt _)
  have hUΩ (k : ℕ) : U k ⊆ Ω := fun y hy =>
    ball_infDist_compl_subset (mem_ball_self ((hδ k).trans hy))
  -- Uniform convergence of the mollifications, and their values on the frontier of `U k`,
  -- where `dist(·, Ωᶜ) = δ k`.
  have hclose : ∀ ε > 0, ∀ᶠ k in atTop, ∀ y, closedBall y (φ k).rOut ⊆ Ω → |v k y - ū y| ≤ ε := by
    intro ε hε
    obtain ⟨ρ, hρ, h⟩ := Wkp.exists_pos_forall_dist_smoothField_le
      ((hΩb.isCompact_closure.uniformContinuousOn_of_continuous hcont).mono subset_closure) hū hε
    filter_upwards [hφ0.eventually (gt_mem_nhds hρ)] with k hk y hy
    exact Real.dist_eq _ _ ▸ h _ hk y hy
  have hvm : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ frontier (U k), v k z ≤ m + ε := by
    intro ε hε
    obtain ⟨d, hd, hdm⟩ := Ω.isOpen.exists_pos_forall_lt_add_of_infDist_lt hΩb
      (hΩb.nonempty_compl ℝ) hcont hm (half_pos hε)
    filter_upwards [hδ0.eventually (gt_mem_nhds hd), hclose (ε / 2) (half_pos hε)] with k hk hk'
      z hz
    have hz' : δ k = infDist z (Ω : Set E)ᶜ :=
      frontier_lt_subset_eq continuous_const (continuous_infDist_pt _) hz
    have := hdm z (hball k hz'.le (mem_closedBall_self (φ k).rOut_pos.le)) (hz' ▸ hk)
    linarith [(abs_le.1 (hk' z (hball k hz'.le))).2]
  have hH : ∫⁻ y in Ω, ‖Wkp.iteratedGradient 1 u y‖ₑ ^ finrank ℝ E ∂μ ≠ ∞ := by
    rw [lintegral_enorm_pow_eq_eLpNorm_pow (Nat.one_le_iff_ne_zero.1 hn1)
      (Lp.aestronglyMeasurable _)]
    exact ENNReal.pow_ne_top (Lp.eLpNorm_lt_top _).ne
  exact addHaar_ball_le_of_tendsto μ hΩb Ω.isOpen (hcont.mono subset_closure) hx hUo hUΩ
    (fun z hz => Ω.isOpen.exists_eventually_closedBall_subset_setOf_lt_infDist
      (hΩb.nonempty_compl ℝ) hδ0 hz)
    (fun k => contDiff_infty.1 (Wkp.contDiff_smoothField _ _) 2)
    (fun ε hε => (hclose ε hε).mono fun k hk y hy => hk y (hball k (le_of_lt hy)))
    hvm (Lp.aestronglyMeasurable _) hH
    (tendsto_setLIntegral_hessianOperator_smoothField_sub hn1 u hUo hUΩ hφ0
      fun k y hy => hball k hy.le)

end Sobolev

section Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Opens (EuclideanSpace ℝ ι)}
  {ū f : EuclideanSpace ℝ ι → ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {m : ℝ}
  {x : EuclideanSpace ℝ ι} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Aleksandrov–Bakelman–Pucci estimate for strong subsolutions, measure form**
(Gilbarg–Trudinger, Lemma 9.3 without drift, for `W^{2,n}` functions). Let `Ω ⊆ ℝⁿ` be bounded
and open, let `u ∈ W^{2,n}(Ω)` have a representative `ū` continuous on `closure Ω`, and let `m`
bound `ū` on `frontier Ω`. If, almost everywhere on the upper contact set `Γ⁺` of `ū`, the
matrices `a y` are positive definite and `f y ≤ ∑ᵢⱼ aⁱʲ(y) ∂ᵢ∂ⱼu(y)` with the weak Hessian, then
for `x ∈ Ω`, `|B(0, (ū x - m) / diam Ω)| ≤ ∫_{Γ⁺} (f⁻ / n)ⁿ / det a`. -/
theorem volume_ball_le_setLIntegral_upperContactSet_of_wkp
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (hp : p = Fintype.card ι)
    (u : Wkp volume Ω p 2) (hcont : ContinuousOn ū (closure Ω))
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū)
    (ha : ∀ᵐ y ∂volume.restrict (upperContactSet ū Ω), (a y).PosDef)
    (hf : ∀ᵐ y ∂volume.restrict (upperContactSet ū Ω),
      f y ≤ ∑ i, ∑ j, a y i j * Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)
    (hm : ∀ z ∈ frontier (Ω : Set (EuclideanSpace ℝ ι)), ū z ≤ m) (hx : x ∈ Ω) :
    volume (ball (0 : EuclideanSpace ℝ ι) ((ū x - m) / diam (Ω : Set (EuclideanSpace ℝ ι)))) ≤
      ∫⁻ y in upperContactSet ū Ω,
        ENNReal.ofReal (((f y)⁻ / Fintype.card ι) ^ Fintype.card ι / (a y).det) := by
  refine (addHaar_ball_le_lintegral_abs_det_iteratedGradient hΩb
    (by rw [hp, finrank_euclideanSpace]) u hcont hū hm hx).trans (lintegral_mono_ae ?_)
  filter_upwards [ha, hf] with y hay hfy
  set T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι := Wkp.iteratedGradient 1 u y
  by_cases hy : (-T).IsPositive
  · rw [indicator_of_mem hy]
    exact ENNReal.ofReal_le_ofReal (abs_det_le_negPart_div_card_pow_div_det
      (by simpa only [ContinuousLinearMap.toLinearMap_neg] using hy.toLinearMap) hay hfy)
  · rw [indicator_of_notMem hy]
    exact zero_le

/-- **The Aleksandrov–Bakelman–Pucci estimate for strong subsolutions** (Gilbarg–Trudinger,
Lemma 9.3 and Theorem 9.1 without drift, for `W^{2,n}` functions). Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be
bounded and open, let `u ∈ W^{2,n}(Ω)` have a representative `ū` continuous on `closure Ω`, and let
`m` bound `ū` on `frontier Ω`. Suppose that almost everywhere on the upper contact set `Γ⁺` of `ū`
the matrices `a y` are positive definite and `f y ≤ ∑ᵢⱼ aⁱʲ(y) ∂ᵢ∂ⱼu(y)` with the weak Hessian,
and that `f⁻ / D*`, with `D* = (det a)^{1/n}`, lies in `Lⁿ(Γ⁺)`. Then on `Ω`,
`ū ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / D*‖_{Lⁿ(Γ⁺)}`, where `ωₙ` is the volume of the unit ball. -/
theorem le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) (hp : p = Fintype.card ι)
    (u : Wkp volume Ω p 2) (hcont : ContinuousOn ū (closure Ω))
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū)
    (ha : ∀ᵐ y ∂volume.restrict (upperContactSet ū Ω), (a y).PosDef)
    (hf : ∀ᵐ y ∂volume.restrict (upperContactSet ū Ω),
      f y ≤ ∑ i, ∑ j, a y i j * Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)
    (hg : MemLp (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
      (volume.restrict (upperContactSet ū Ω)))
    (hm : ∀ z ∈ frontier (Ω : Set (EuclideanSpace ℝ ι)), ū z ≤ m) (hx : x ∈ Ω) :
    ū x ≤ m + diam (Ω : Set (EuclideanSpace ℝ ι)) / (Fintype.card ι *
        (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹) *
      (eLpNorm (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
        (volume.restrict (upperContactSet ū Ω))).toReal := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by
    have h := (Fact.out : 1 ≤ p)
    rw [hp] at h
    exact_mod_cast h)
  refine le_add_div_mul_toReal_of_volume_ball_le
    (diam_pos (infinite_of_mem_nhds x (Ω.isOpen.mem_nhds hx)).nontrivial hΩb)
    hg.eLpNorm_lt_top.ne ?_
  rw [← setLIntegral_negPart_div_det_eq_mul_eLpNorm_pow ha hg.aestronglyMeasurable]
  exact volume_ball_le_setLIntegral_upperContactSet_of_wkp hΩb hp u hcont hū ha hf hm hx

end Operator

end PDE

end TauCeti
