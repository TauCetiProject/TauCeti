/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation
import Mathlib.Topology.MetricSpace.Sequences
import TauCeti.Analysis.InnerProductSpace.Spectrum
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence

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
* a point that lies in the contact sets of infinitely many `vₖ` lies in the contact set of `ū`,
  since the supporting slopes stay bounded and the supporting inequalities pass to the limit;
* at such a point the negated Hessians of the `vₖ` are positive, hence so is their limit `-D²u`.

On the contact set the determinant–trace inequality for the positive operator `-D²u`
(`LinearMap.IsPositive.det_mul_det_le_sum_mul_apply_div_card_pow`) then bounds `|det D²u|` by
`(f⁻ / n)ⁿ / det a`, as in the `C²` case.

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

omit [FiniteDimensional ℝ E] in
/-- **Supporting slopes are bounded.** If the affine function through `(y, v y)` with slope `p`
lies above `v` on `closedBall y r`, `r > 0`, and `|v| ≤ M` there, then `‖p‖ ≤ 2 M / r`: test the
inequality at `y - r p / ‖p‖`. -/
private theorem norm_le_of_forall_le_add_inner {v : E → ℝ} {p : E} {r M : ℝ} (hr : 0 < r)
    (hp : ∀ z ∈ closedBall y r, v z ≤ v y + ⟪p, z - y⟫)
    (hM : ∀ z ∈ closedBall y r, |v z| ≤ M) : ‖p‖ ≤ 2 * M / r := by
  rw [le_div_iff₀ hr]
  have hy := abs_le.1 (hM y (mem_closedBall_self hr.le))
  rcases eq_or_ne p 0 with rfl | h0
  · rw [norm_zero, zero_mul]
    linarith
  have hz : y - (r / ‖p‖) • p ∈ closedBall y r := by
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_div, abs_of_pos hr, abs_norm, div_mul_cancel₀ _ (norm_ne_zero_iff.2 h0)]
  have h := hp _ hz
  rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have hrp : r / ‖p‖ * ‖p‖ ^ 2 = ‖p‖ * r := by
    field_simp
  rw [hrp] at h
  linarith [abs_le.1 (hM _ hz)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Uniform convergence on sets `U k` which eventually contain a ball around each point of `Ω`
gives pointwise convergence on `Ω`. -/
private theorem tendsto_of_eventually_abs_sub_le {U : ℕ → Set E} {v : ℕ → E → ℝ}
    (hUball : ∀ z ∈ Ω, ∃ r > 0, ∀ᶠ k in atTop, closedBall z r ⊆ U k)
    (hvu : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ U k, |v k z - u z| ≤ ε) {z : E} (hz : z ∈ Ω) :
    Tendsto (fun k => v k z) atTop (𝓝 (u z)) := by
  obtain ⟨s, hs, hsb⟩ := hUball z hz
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [hsb, hvu (ε / 2) (half_pos hε)] with k hk hk'
  rw [Real.dist_eq]
  exact (hk' z (hk (mem_closedBall_self hs.le))).trans_lt (half_lt_self hε)

/-- **Contact points pass to the limit.** Let `v k` converge to `u` uniformly on open sets
`U k ⊆ Ω` which eventually contain a ball around each point of `Ω`. If `y` lies in the upper
contact set of `v k` on `U k` for infinitely many `k`, then `y` lies in the upper contact set of
`u` on `Ω`. -/
private theorem mem_upperContactSet_of_frequently {U : ℕ → Set E} {v : ℕ → E → ℝ}
    (hu : ContinuousOn u Ω) (hUΩ : ∀ k, U k ⊆ Ω)
    (hUball : ∀ z ∈ Ω, ∃ r > 0, ∀ᶠ k in atTop, closedBall z r ⊆ U k)
    (hvu : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ U k, |v k z - u z| ≤ ε)
    (hfreq : ∃ᶠ k in atTop, y ∈ upperContactSet (v k) (U k)) :
    y ∈ upperContactSet u Ω := by
  obtain ⟨k₀, hk₀⟩ := hfreq.exists
  have hyΩ : y ∈ Ω := hUΩ k₀ (upperContactSet_subset hk₀)
  obtain ⟨r, hr, hball⟩ := hUball y hyΩ
  obtain ⟨k₁, hk₁⟩ := hball.exists
  -- `u` is bounded on the ball around `y`.
  obtain ⟨M, hM⟩ := (isCompact_closedBall y r).exists_bound_of_continuousOn
    (hu.mono (hk₁.trans (hUΩ k₁)))
  -- Along a subsequence, `y` is a contact point and `v k` is uniformly close to `u`, so the
  -- supporting slopes are bounded and a further subsequence of them converges.
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop
    ((hfreq.and_eventually hball).and_eventually (hvu 1 one_pos))
  choose p hp using fun j => (mem_upperContactSet.1 (hP j).1.1).2
  have hpb (j : ℕ) : p j ∈ closedBall (0 : E) (2 * (M + 1) / r) := by
    refine mem_closedBall_zero_iff.2 (norm_le_of_forall_le_add_inner hr
      (fun z hz => hp j z ((hP j).1.2 hz)) fun z hz => ?_)
    have h := abs_le.1 ((hP j).2 z ((hP j).1.2 hz))
    have h' := abs_le.1 (Real.norm_eq_abs _ ▸ hM z hz)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  obtain ⟨q, -, ψ, hψ, hq⟩ := tendsto_subseq_of_bounded isBounded_closedBall hpb
  -- Pass to the limit in the supporting inequalities.
  have hφψ : Tendsto (fun j => φ (ψ j)) atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have hlim {z : E} (hz : z ∈ Ω) : Tendsto (fun j => v (φ (ψ j)) z) atTop (𝓝 (u z)) :=
    (tendsto_of_eventually_abs_sub_le hUball hvu hz).comp hφψ
  refine mem_upperContactSet.2 ⟨hyΩ, q, fun z hz => le_of_tendsto_of_tendsto (hlim hz)
    ((hlim hyΩ).add (hq.inner tendsto_const_nhds)) ?_⟩
  obtain ⟨s, hs, hsb⟩ := hUball z hz
  filter_upwards [hφψ.eventually hsb] with j hj
  exact hp (ψ j) z (hj (mem_closedBall_self hs.le))

omit [FiniteDimensional ℝ E] in
/-- At a contact point of a `C²` function, the negated Hessian operator is positive. -/
private theorem isPositive_neg_hessianOperator_of_mem_upperContactSet {v : E → ℝ} {U : Set E}
    [CompleteSpace E] (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U) (hy : y ∈ upperContactSet v U) :
    (-hessianOperator v y).IsPositive := by
  have hv' := hv.contDiffAt (hU.mem_nhds (upperContactSet_subset hy))
  refine (ContinuousLinearMap.isPositive_iff _).2 ⟨fun w w' => ?_, fun w => ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, neg_apply, inner_neg_left,
      inner_neg_right, inner_hessianOperator_left]
    rw [real_inner_comm, inner_hessianOperator_left]
    exact congrArg Neg.neg (hv'.isSymmSndFDerivAt (by simp) w w')
  · rw [neg_apply, inner_neg_left, inner_hessianOperator_left, neg_nonneg]
    exact fderiv_fderiv_self_nonpos_of_mem_upperContactSet hU hv hy w

/-- The determinant of `T` is controlled by the `n`-th powers of the norms of any `S` and of
`T - S`, `n` the dimension: `|det T| ≤ ‖T‖ⁿ ≤ 2ⁿ (‖S‖ⁿ + ‖T - S‖ⁿ)`. -/
private theorem ofReal_abs_det_le (T S : E →L[ℝ] E) :
    ENNReal.ofReal |T.det| ≤ 2 ^ finrank ℝ E * (‖S‖ₑ ^ finrank ℝ E + ‖T - S‖ₑ ^ finrank ℝ E) := by
  -- `‖T‖ ≤ 2 max (‖S‖, ‖T - S‖)`.
  have h1 : ‖T‖ₑ ≤ 2 * max ‖S‖ₑ ‖T - S‖ₑ := by
    calc ‖T‖ₑ = ENNReal.ofReal ‖S + (T - S)‖ := by rw [add_sub_cancel, ofReal_norm]
      _ ≤ ENNReal.ofReal (‖S‖ + ‖T - S‖) := ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ ≤ 2 * max ‖S‖ₑ ‖T - S‖ₑ := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm,
            two_mul]
          exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have h2 : max ‖S‖ₑ ‖T - S‖ₑ ^ finrank ℝ E ≤ ‖S‖ₑ ^ finrank ℝ E + ‖T - S‖ₑ ^ finrank ℝ E := by
    rcases le_total ‖S‖ₑ ‖T - S‖ₑ with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_self_add
  calc ENNReal.ofReal |T.det| ≤ ‖T‖ₑ ^ finrank ℝ E := by
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal T.abs_det_le_opNorm_pow
    _ ≤ _ := by
        refine (pow_le_pow_left' h1 _).trans ?_
        rw [mul_pow]
        exact mul_le_mul_right h2 _

omit [FiniteDimensional ℝ E] in
/-- The operators whose negative is positive form a closed set. -/
private theorem isClosed_setOf_isPositive_neg : IsClosed {T : E →L[ℝ] E | (-T).IsPositive} := by
  have h : {T : E →L[ℝ] E | (-T).IsPositive} =
      (⋂ w, ⋂ w', {T : E →L[ℝ] E | ⟪T w, w'⟫ = ⟪w, T w'⟫}) ∩ ⋂ w, {T | ⟪T w, w⟫ ≤ 0} := by
    ext T
    simp [ContinuousLinearMap.isPositive_iff, LinearMap.IsSymmetric]
  rw [h]
  refine (isClosed_iInter fun w => isClosed_iInter fun w' => isClosed_eq ?_ ?_).inter
    (isClosed_iInter fun w => isClosed_le ?_ continuous_const)
  · exact (continuous_id.clm_apply continuous_const).inner continuous_const
  · exact continuous_const.inner (continuous_id.clm_apply continuous_const)
  · exact (continuous_id.clm_apply continuous_const).inner continuous_const

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
      isClosed_setOf_isPositive_neg.mem_of_frequently_of_tendsto
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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- A ball is exhausted by the concentric balls of smaller radius, so a bound on the measures of
the smaller balls bounds the measure of the ball. -/
private theorem measure_ball_le_of_forall_lt {R : ℝ} {B : ℝ≥0∞}
    (h : ∀ s < R, μ (ball (0 : E) s) ≤ B) : μ (ball (0 : E) R) ≤ B := by
  have hU : ⋃ i : ℕ, ball (0 : E) (R - 1 / ((i : ℝ) + 1)) = ball 0 R := by
    ext z
    simp only [mem_iUnion, mem_ball, dist_zero_right]
    refine ⟨fun ⟨i, hi⟩ => hi.trans (sub_lt_self _ Nat.one_div_pos_of_nat), fun hz => ?_⟩
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
    exact ⟨i, by linarith⟩
  have hmono : Monotone fun i : ℕ => ball (0 : E) (R - 1 / ((i : ℝ) + 1)) := fun i j hij =>
    ball_subset_ball (sub_le_sub_left (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)) _)
  rw [← hU]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) fun i =>
    h _ (sub_lt_self _ Nat.one_div_pos_of_nat)


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
      fun j y hy => (ofReal_abs_det_le _ (H y)).trans (mul_le_mul_right (add_le_add ?_ ?_) _)⟩
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
  have hdU : 0 < diam U := (by positivity : (0 : ℝ) < 2 * r).trans_le
    ((diam_ball_eq x hr.le).symm.trans_le
      (diam_mono (ball_subset_closedBall.trans hxU) (hΩb.subset hUΩ)))
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
  refine measure_ball_le_of_forall_lt μ fun s hs => ?_
  have hd : 0 < diam Ω := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
    exact (by positivity : (0 : ℝ) < 2 * r).trans_le
      ((diam_ball_eq x hr.le).symm.trans_le (diam_mono hball hΩb))
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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A bounded subset of a nontrivial real normed space has nonempty complement. -/
private theorem nonempty_compl_of_isBounded [Nontrivial E] {s : Set E}
    (hs : Bornology.IsBounded s) : sᶜ.Nonempty :=
  nonempty_compl.2 fun h => NormedSpace.unbounded_univ ℝ E (h ▸ hs)

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `ū` is continuous on the closure of a bounded open set `Ω` and at most `m` on its frontier,
then `ū < m + η` at the points of `Ω` close enough to the complement of `Ω`. -/
private theorem exists_pos_forall_infDist_lt [Nontrivial E] (hΩb : Bornology.IsBounded (Ω : Set E))
    (hcont : ContinuousOn ū (closure Ω)) (hm : ∀ z ∈ frontier (Ω : Set E), ū z ≤ m) {η : ℝ}
    (hη : 0 < η) : ∃ δ > 0, ∀ z ∈ Ω, infDist z (Ω : Set E)ᶜ < δ → ū z < m + η := by
  -- The points of `closure Ω` where `ū ≥ m + η` form a compact subset of `Ω`.
  set K := closure (Ω : Set E) ∩ ū ⁻¹' Ici (m + η)
  have hK : IsCompact K := hΩb.isCompact_closure.of_isClosed_subset
    (hcont.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici) inter_subset_left
  have hKΩ : K ⊆ Ω := fun z ⟨hz, hzη⟩ => by
    by_contra hzΩ
    have := hm z ⟨hz, by rwa [Ω.isOpen.interior_eq]⟩
    simp only [mem_preimage, mem_Ici] at hzη
    linarith
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  refine ⟨δ, hδ, fun z hz hzδ => lt_of_not_ge fun hzη => hzδ.not_ge ?_⟩
  refine (le_infDist (nonempty_compl_of_isBounded hΩb)).2 fun w hw =>
    le_of_not_gt fun hwz => hw (hδK ?_)
  exact mem_cthickening_of_dist_le w z δ K ⟨subset_closure hz, hzη⟩ (dist_comm w z ▸ hwz.le)

omit [FiniteDimensional ℝ E] in
/-- Mollifications of a function continuous on the compact closure of `Ω` converge to it
uniformly on the points whose bump ball lies in `Ω`. -/
private theorem exists_pos_forall_abs_smoothField_sub_le {p : ℝ≥0∞}
    [FiniteDimensional ℝ E] (hΩb : Bornology.IsBounded (Ω : Set E))
    (hcont : ContinuousOn ū (closure Ω)) {f : Lp ℝ p (μ.restrict Ω)}
    (hf : (f : E → ℝ) =ᵐ[μ.restrict Ω] ū) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ φ : ContDiffBump (0 : E), φ.rOut < ρ → ∀ y, closedBall y φ.rOut ⊆ Ω →
      |Wkp.smoothField φ f y - ū y| ≤ ε := by
  obtain ⟨ρ, hρ, hū⟩ := Metric.uniformContinuousOn_iff.1
    (hΩb.isCompact_closure.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨ρ, hρ, fun φ hφ y hy => ?_⟩
  have hyΩ : y ∈ Ω := hy (mem_closedBall_self φ.rOut_pos.le)
  -- Replace the Sobolev value by `ū` inside the convolution.
  have hae : (Ω : Set E).indicator (f : E → ℝ) =ᵐ[μ] (Ω : Set E).indicator ū := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hf] with z hz
    by_cases hzΩ : z ∈ (Ω : Set E)
    · simp only [indicator_of_mem hzΩ, hz hzΩ]
    · simp only [indicator_of_notMem hzΩ]
  have hmeas : AEStronglyMeasurable ((Ω : Set E).indicator ū) μ :=
    (aestronglyMeasurable_indicator_iff Ω.isOpen.measurableSet).2
      ((hcont.mono subset_closure).aestronglyMeasurable Ω.isOpen.measurableSet)
  have h := φ.dist_normed_convolution_le (μ := μ) (x₀ := y) (ε := ε) hmeas fun z hz => by
    have hzΩ : z ∈ (Ω : Set E) := hy (ball_subset_closedBall hz)
    rw [indicator_of_mem hzΩ, indicator_of_mem hyΩ]
    exact (hū z (subset_closure hzΩ) y (subset_closure hyΩ) (hz.trans hφ)).le
  have hconv : Wkp.smoothField φ f =
      φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (Ω : Set E).indicator ū :=
    (Wkp.smoothField_def φ f).trans (convolution_congr _ EventuallyEq.rfl hae)
  rwa [indicator_of_mem hyΩ, ← hconv, Real.dist_eq] at h

/-- Where the bump ball around `y` lies in `Ω`, the Hessian of the mollified value of
`u ∈ W^{2,p}(Ω)` is the mollified weak Hessian. -/
private theorem hessianOperator_smoothField {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Wkp μ Ω p 2) (φ : ContDiffBump (0 : E)) {U : Set E} (hU : IsOpen U)
    (hUΩ : ∀ y ∈ U, closedBall y φ.rOut ⊆ Ω) {y : E} (hy : y ∈ U) :
    hessianOperator (Wkp.smoothField φ (Wkp.value 2 u)) y =
      Wkp.smoothField φ (Wkp.iteratedGradient 1 u) y := by
  have hgrad : ∇ (Wkp.smoothField φ (Wkp.value 2 u)) =ᶠ[𝓝 y]
      Wkp.smoothField φ (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [Wkp.value_succ]
    exact Wkp.gradient_smoothField _ φ z (hUΩ z hz)
  rw [← fderiv_gradient, hgrad.fderiv_eq]
  exact Wkp.fderiv_smoothField 0 u φ y (hUΩ y hy)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every point of an open set `s` with nonempty complement has a ball inside
`{y | δ k < dist(y, sᶜ)}` for all large `k`, if `δ k → 0`. -/
private theorem exists_eventually_closedBall_subset {s : Set E} (hs : IsOpen s) (hc : sᶜ.Nonempty)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) {z : E} (hz : z ∈ s) :
    ∃ r > 0, ∀ᶠ k in atTop, closedBall z r ⊆ {y | δ k < infDist y sᶜ} := by
  have hd := (hs.isClosed_compl.notMem_iff_infDist_pos hc).1 (not_not_intro hz)
  refine ⟨infDist z sᶜ / 2, half_pos hd, ?_⟩
  filter_upwards [hδ.eventually (gt_mem_nhds (half_pos hd))] with k hk w hw
  have := infDist_le_infDist_add_dist (x := z) (y := w) (s := sᶜ)
  rw [dist_comm] at this
  simp only [mem_ofPred_eq]
  linarith [mem_closedBall.1 hw]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The `n`-th power of the `Lⁿ` norm on `Ω` as a Lebesgue integral. -/
private theorem setLIntegral_enorm_pow_eq_eLpNorm_pow {F : Type*} [NormedAddCommGroup F]
    {n : ℕ} (hn : 1 ≤ n) {f : E → F} (hf : AEStronglyMeasurable f (μ.restrict Ω)) :
    ∫⁻ y in Ω, ‖f y‖ₑ ^ n ∂μ = eLpNorm f n (μ.restrict Ω) ^ n := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (n : NNReal))
    (Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hn)) hf
  simpa only [ENNReal.coe_natCast, NNReal.coe_natCast, ENNReal.rpow_natCast] using h.symm

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
  rw [Function.comp_apply, ← setLIntegral_enorm_pow_eq_eLpNorm_pow hn
    ((Wkp.contDiff_smoothField _ _).continuous.aestronglyMeasurable.sub
      (Lp.aestronglyMeasurable _))]
  refine (setLIntegral_congr_fun (hUo k).measurableSet fun y hy => ?_).trans_le
    (lintegral_mono_set (hUΩ k))
  rw [hessianOperator_smoothField u (φ k) (hUo k) (hball k) hy, Pi.sub_apply]

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
    obtain ⟨ρ, hρ, h⟩ := exists_pos_forall_abs_smoothField_sub_le hΩb hcont hū hε
    filter_upwards [hφ0.eventually (gt_mem_nhds hρ)] with k hk y hy using h _ hk y hy
  have hvm : ∀ ε > 0, ∀ᶠ k in atTop, ∀ z ∈ frontier (U k), v k z ≤ m + ε := by
    intro ε hε
    obtain ⟨d, hd, hdm⟩ := exists_pos_forall_infDist_lt hΩb hcont hm (half_pos hε)
    filter_upwards [hδ0.eventually (gt_mem_nhds hd), hclose (ε / 2) (half_pos hε)] with k hk hk'
      z hz
    have hz' : δ k = infDist z (Ω : Set E)ᶜ :=
      frontier_lt_subset_eq continuous_const (continuous_infDist_pt _) hz
    have := hdm z (hball k hz'.le (mem_closedBall_self (φ k).rOut_pos.le)) (hz' ▸ hk)
    linarith [(abs_le.1 (hk' z (hball k hz'.le))).2]
  have hH : ∫⁻ y in Ω, ‖Wkp.iteratedGradient 1 u y‖ₑ ^ finrank ℝ E ∂μ ≠ ∞ := by
    rw [setLIntegral_enorm_pow_eq_eLpNorm_pow hn1 (Lp.aestronglyMeasurable _)]
    exact ENNReal.pow_ne_top (Lp.eLpNorm_lt_top _).ne
  exact addHaar_ball_le_of_tendsto μ hΩb Ω.isOpen (hcont.mono subset_closure) hx hUo hUΩ
    (fun z hz => exists_eventually_closedBall_subset Ω.isOpen
      (nonempty_compl_of_isBounded hΩb) hδ0 hz)
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
    -- On the contact set `-D²u` is positive, so the determinant–trace inequality bounds the
    -- determinant of `D²u` by the elliptic operator.
    have hentry : ∑ i, ∑ j, a y i j * (↑(-T) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
        (EuclideanSpace.single j 1) i = -∑ i, ∑ j, a y i j * T (EuclideanSpace.single j 1) i := by
      simp [Finset.sum_neg_distrib]
    have hS := hy.toLinearMap.sum_mul_apply_nonneg hay.posSemidef
    have hD := hy.toLinearMap.det_mul_det_le_sum_mul_apply_div_card_pow hay.posSemidef
    rw [hentry] at hS hD
    rw [← hy.toLinearMap.abs_det_neg, ContinuousLinearMap.toLinearMap_neg, neg_neg] at hD
    refine ENNReal.ofReal_le_ofReal ((le_div_iff₀ hay.det_pos).2 (hD.trans (pow_le_pow_left₀
      (div_nonneg hS (Nat.cast_nonneg _)) (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) _)))
    exact (neg_le_neg hfy).trans (neg_le_negPart _)
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
  -- `Ω` is a nonempty open set, so it has positive diameter.
  have hd : 0 < diam (Ω : Set (EuclideanSpace ℝ ι)) := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
    calc 0 < 2 * ε := by positivity
      _ = diam (ball x ε) := (diam_ball_eq x hε.le).symm
      _ ≤ diam (Ω : Set (EuclideanSpace ℝ ι)) := diam_mono hball hΩb
  refine le_add_div_mul_toReal_of_volume_ball_le hd hg.eLpNorm_lt_top.ne ?_
  rw [← setLIntegral_negPart_div_det_eq_mul_eLpNorm_pow ha hg.aestronglyMeasurable]
  exact volume_ball_le_setLIntegral_upperContactSet_of_wkp hΩb hp u hcont hū ha hf hm hx

end Operator

end PDE

end TauCeti
