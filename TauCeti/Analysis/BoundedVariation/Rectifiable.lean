/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.BoundedVariation.Poincare
import TauCeti.Geometry.MeasureTheory.Rectifiable.ConeCriterion
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Countable rectifiability of the reduced boundary

For a set `s` in an open subset `Ω` of a finite-dimensional real inner product space `E` equipped
with an additive Haar measure `μ`, the reduced boundary `∂*s` (`TauCeti.reducedBoundary`) is
countably `(dim E - 1)`-rectifiable (`TauCeti.countablyRectifiable_reducedBoundary`). This is the
geometric half of De Giorgi's structure theorem for sets of locally finite perimeter.

The proof treats `dim E ≤ 1` and `dim E ≥ 2` by distinct mechanisms:

* **Low dimensions (`dim E ≤ 1`, `TauCeti.countable_reducedBoundary_of_finrank_le_one`).** When
  `dim E = 0`, `E` is a subsingleton. When `dim E = 1`, the localized BV Poincaré inequality on
  `ball x r ⊆ Ω` has exponent `(dim E)⁻¹ = 1`, so the volume factor `μ A` (`A = s ∩ ball x r` or
  `ball x r \ s`, depending on whether the ball mean of `χ_s` is at most or at least `1 / 2`)
  cancels from both sides and `diam (ball x r) / μ.real (ball x r)` is bounded independently of
  `r`. Letting `r → 0⁺` shows that every point of `∂*s` is an atom of the σ-finite perimeter
  measure `|Dχ_s|`, hence `∂*s` is countable.
* **Dimensions `dim E ≥ 2` (`TauCeti.exists_pos_forall_abs_inner_sub_outerNormal_le`).** By the
  lower volume density estimates (`TauCeti.eventually_ofReal_pow_le_mul_measure_inter_ball` and
  `TauCeti.eventually_ofReal_pow_le_mul_measure_ball_sdiff`), `∂*s` is a countable union of strata
  `T_m` on which both `s` and `sᶜ` satisfy uniform lower volume density bounds up to radius
  `1 / (m + 1)`. At any `x ∈ ∂*s`, the blow-ups `s_{x, r}` converge in `L¹_loc` to the half-space
  `{y | ⟪y, ν_s x⟫ < 0}`
  (`TauCeti.tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter`).
  A point `z ∈ T_m` near `x` violating the normal cone bound `|⟪z - x, ν_s x⟫| ≤ η ‖z - x‖` puts a
  rescaled ball of radius `η / 2` completely on the wrong side of `{y | ⟪y, ν_s x⟫ < 0}` while
  carrying uniformly positive blow-up mass on both `s` and `sᶜ`, a contradiction for small
  `r = ‖z - x‖`. Applying the codimension-one cone criterion
  (`TauCeti.CountablyRectifiable.of_forall_exists_abs_inner_sub_le`) to each `T_m` concludes.

## Main statements

* `TauCeti.countable_reducedBoundary_of_finrank_le_one`: when `dim E ≤ 1` and `μ` is an additive
  Haar measure, `reducedBoundary μ Ω s` is countable.
* `TauCeti.exists_pos_forall_abs_inner_sub_outerNormal_le`: for `dim E ≥ 2`, points of a uniform
  lower-density stratum near `x ∈ reducedBoundary μ Ω s` lie in an arbitrarily narrow normal cone
  around `(ℝ ∙ outerNormal μ Ω s x)ᗮ`.
* `TauCeti.countablyRectifiable_reducedBoundary`: for any additive Haar measure `μ` in any
  finite-dimensional real inner product space `E`, `reducedBoundary μ Ω s` is countably
  `(dim E - 1)`-rectifiable.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 15.9.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.3, Theorem 5.15.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.5, Theorem 3.59.
* H. Federer, *Geometric Measure Theory*, 4.5.6.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace symmDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E} {x : E}

/-! ### Dimension at most one -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- On a ball `B` of positive finite measure where `u = χ_s` has positive measure on a null
measurable subset `A ⊆ B` and `|u - m| ≥ 1 / 2` on `A`, the `L¹` deviation over `A` is at least
`2⁻¹ * μ A`. -/
private theorem half_mul_measure_le_setLIntegral_enorm_sub {A : Set E} {m : ℝ}
    (hAm : NullMeasurableSet A μ) (hval : ∀ z ∈ A, (1 / 2 : ℝ) ≤ |s.indicator (1 : E → ℝ) z - m|) :
    (2⁻¹ : ℝ≥0∞) * μ A ≤ ∫⁻ z in A, ‖s.indicator (1 : E → ℝ) z - m‖ₑ ∂μ := by
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = 2⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
  rw [← hhalf, ← setLIntegral_const]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem₀ hAm] with z hz
  rw [Real.eNorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (hval z hz)

/-- Around any `x ∈ reducedBoundary μ Ω s`, every ball `ball x r ⊆ Ω` (`r > 0`) contains a
null-measurable subset `A` of positive `μ`-measure on which `|χ_s - ⨍_{ball x r} χ_s| ≥ 1 / 2`. -/
private theorem exists_subset_ball_measure_ne_zero_half_le_abs_indicator_sub [μ.IsAddHaarMeasure]
    (hx : x ∈ reducedBoundary μ Ω s) {r : ℝ} (hr : 0 < r) (hrΩ : ball x r ⊆ Ω) :
    ∃ A ⊆ ball x r, μ A ≠ 0 ∧ NullMeasurableSet A μ ∧
      ∀ z ∈ A, (1 / 2 : ℝ) ≤
        |s.indicator (1 : E → ℝ) z - ⨍ y in ball x r, s.indicator (1 : E → ℝ) y ∂μ| := by
  set B : Set E := ball x r
  set m : ℝ := ⨍ y in B, s.indicator (1 : E → ℝ) y ∂μ
  have hsΩ : NullMeasurableSet (s ∩ Ω) μ := nullMeasurableSet_inter_of_mem_reducedBoundary hx
  rcases le_total m (1 / 2) with hm | hm
  · refine ⟨s ∩ B, inter_subset_right, (measure_inter_ball_pos hx hr).ne', ?_, fun z hz => ?_⟩
    · have heq : s ∩ B = (s ∩ Ω) ∩ B := by
        ext z; simp only [mem_inter_iff]
        exact ⟨fun h => ⟨⟨h.1, hrΩ h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
      rw [heq]
      exact hsΩ.inter measurableSet_ball.nullMeasurableSet
    · rw [indicator_of_mem hz.1, Pi.one_apply, abs_of_nonneg (by linarith)]
      linarith
  · have hxc : x ∈ reducedBoundary μ Ω sᶜ := by rwa [reducedBoundary_compl]
    refine ⟨sᶜ ∩ B, inter_subset_right, (measure_inter_ball_pos hxc hr).ne', ?_, fun z hz => ?_⟩
    · have heq : sᶜ ∩ B = B \ (s ∩ Ω) := by
        ext z; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
        exact ⟨fun h => ⟨h.2, fun hs => h.1 hs.1⟩, fun h => ⟨fun hs => h.2 ⟨hs, hrΩ h.1⟩, h.1⟩⟩
      rw [heq]
      exact measurableSet_ball.nullMeasurableSet.diff hsΩ
    · rw [indicator_of_notMem hz.1, zero_sub, abs_neg, abs_of_nonneg (by linarith)]
      exact hm

/-- In dimension `1`, at any `x ∈ reducedBoundary μ Ω s` and for any `ball x r ⊆ Ω` (`r > 0`), the
perimeter measure of `closedBall x r` is bounded below by a positive constant independent of `r`. -/
private theorem inv_two_le_mul_variationMeasure_closedBall_of_finrank_eq_one [μ.IsAddHaarMeasure]
    (hn : finrank ℝ E = 1) (hx : x ∈ reducedBoundary μ Ω s) {r : ℝ} (hr : 0 < r)
    (hrΩ : ball x r ⊆ Ω) :
    (2⁻¹ : ℝ≥0∞) ≤ ENNReal.ofReal (2 / μ.real (ball 0 1)) *
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  obtain ⟨hu₀, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set B : Set E := ball x r
  let U : Opens E := ⟨B, isOpen_ball⟩
  obtain ⟨A, hAB, hA0, hAm, hval⟩ :=
    exists_subset_ball_measure_ne_zero_half_le_abs_indicator_sub hx hr hrΩ
  have hAfin : μ A ≠ ∞ := ((measure_mono hAB).trans_lt measure_ball_lt_top).ne
  have hpoinc :=
    setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex
      (Ω := U) (convex_ball x r) isBounded_ball (hu₀.mono_set hrΩ) Subset.rfl
      (measure_ball_pos μ x hr).ne' hAB
  have hcoef : ENNReal.ofReal (μ.real (ball (0 : E) 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
      diam B ^ finrank ℝ E / μ.real B) ≤ ENNReal.ofReal (2 / μ.real (ball (0 : E) 1)) := by
    have hμB : μ.real B = r * μ.real (ball (0 : E) 1) := by
      simp [B, measureReal_def, Measure.addHaar_ball_of_pos μ x hr, hn, ENNReal.toReal_ofReal hr.le]
    rw [hn, Nat.cast_one, inv_one, sub_self, Real.rpow_zero, one_mul, pow_one, hμB]
    refine ENNReal.ofReal_le_ofReal ?_
    calc diam B / (r * μ.real (ball (0 : E) 1))
        ≤ (2 * r) / (r * μ.real (ball (0 : E) 1)) :=
          div_le_div_of_nonneg_right (diam_ball hr.le) (mul_nonneg hr.le measureReal_nonneg)
      _ = 2 / μ.real (ball (0 : E) 1) := by rw [mul_comm 2 r, mul_div_mul_left 2 _ hr.ne']
  have hcomb : (2⁻¹ : ℝ≥0∞) * μ A ≤
      (ENNReal.ofReal (2 / μ.real (ball (0 : E) 1)) *
        variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r)) * μ A := by
    refine (half_mul_measure_le_setLIntegral_enorm_sub hAm hval).trans (hpoinc.trans ?_)
    rw [Opens.coe_mk, hn, Nat.cast_one, inv_one, ENNReal.rpow_one, mul_right_comm]
    refine mul_le_mul_left (mul_le_mul ?_ ?_ zero_le zero_le) (μ A)
    · simpa only [hn, Nat.cast_one, inv_one] using hcoef
    · rw [← perimeter_def]
      exact perimeter_ball_le_variationMeasure_closedBall hu₀ hfin hrΩ
  have hcancel := mul_le_mul_left hcomb (μ A)⁻¹
  rwa [mul_assoc, ENNReal.mul_inv_cancel hA0 hAfin, mul_one,
    mul_assoc, ENNReal.mul_inv_cancel hA0 hAfin, mul_one] at hcancel

/-- **In dimension at most `1`, the reduced boundary is countable.** When `dim E = 0` the ambient
space is a subsingleton; when `dim E = 1`, every point of `∂*s` is an atom of the σ-finite perimeter
measure `|Dχ_s|`. -/
theorem countable_reducedBoundary_of_finrank_le_one [μ.IsAddHaarMeasure]
    (hn : finrank ℝ E ≤ 1) : (reducedBoundary μ Ω s).Countable := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with h0 | h1
  · have := finrank_zero_iff.1 h0
    exact Set.to_countable _
  · have := Ω.isOpen.locallyCompactSpace
    refine (Measure.countable_meas_level_set_pos (μ := variationMeasure μ Ω (s.indicator 1))
      measurable_subtype_coe).mono fun x hx => mem_ofPred.2 (pos_iff_ne_zero.2 fun h0 => ?_)
    obtain ⟨r₀, hr₀, hr₀Ω⟩ :=
      nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
    let S (t : ℝ) : Set Ω := ((↑) : Ω → E) ⁻¹' closedBall x t
    have hS0 : ⋂ t > (0 : ℝ), S t = {y : Ω | (y : E) = x} := by
      ext y
      simp only [S, mem_iInter, mem_preimage, mem_closedBall, forall_gt_imp_ge_iff_le_of_dense,
        dist_le_zero, mem_ofPred_eq]
    have hK : IsCompact (S r₀) := Topology.IsInducing.subtypeVal.isCompact_preimage'
      (isCompact_closedBall x r₀) (by rwa [Subtype.range_coe])
    have hfin : variationMeasure μ Ω (s.indicator 1) (S r₀) ≠ ∞ :=
      (hK.measure_lt_top (μ := variationMeasure μ Ω (s.indicator 1))).ne
    have hlim := tendsto_measure_biInter_gt (μ := variationMeasure μ Ω (s.indicator 1))
      (fun t _ =>
        (isClosed_closedBall.preimage continuous_subtype_val).measurableSet.nullMeasurableSet)
      (fun _ _ _ hij => preimage_mono (closedBall_subset_closedBall hij)) ⟨r₀, hr₀, hfin⟩
    rw [hS0, h0] at hlim
    have hmul : Tendsto (fun t => ENNReal.ofReal (2 / μ.real (ball (0 : E) 1)) *
        variationMeasure μ Ω (s.indicator 1) (S t)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using
        ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
    have hle : (2⁻¹ : ℝ≥0∞) ≤ 0 := ge_of_tendsto hmul <| by
      filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
      exact inv_two_le_mul_variationMeasure_closedBall_of_finrank_eq_one h1 hx hr.1
        ((ball_subset_closedBall.trans (closedBall_subset_closedBall hr.2.le)).trans hr₀Ω)
    exact absurd (nonpos_iff_eq_zero.1 hle) (by norm_num)

/-! ### Normal cone estimate in dimension at least two -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `‖w‖ = 1`, `‖ν‖ = 1`, `0 < η' ≤ 1`, and `η' < |⟪w, ν⟫|`, the ball `ball w (η' / 2)` lies in
`closedBall 0 2` and strictly on one side of the hyperplane `{y | ⟪y, ν⟫ = 0}`. -/
private theorem inter_or_sdiff_subset_symmDiff_inter_closedBall {S : Set E} {w ν : E} {η' : ℝ}
    (hw : ‖w‖ = 1) (hν : ‖ν‖ = 1) (hη'0 : 0 < η') (hη'1 : η' ≤ 1) (hgt : η' < |⟪w, ν⟫|) :
    S ∩ ball w (η' / 2) ⊆ (S ∆ {y | ⟪y, ν⟫ < 0}) ∩ closedBall 0 2 ∨
      ball w (η' / 2) \ S ⊆ (S ∆ {y | ⟪y, ν⟫ < 0}) ∩ closedBall 0 2 := by
  have hsubK : ball w (η' / 2) ⊆ closedBall 0 2 := fun y hy => by
    rw [mem_closedBall_zero_iff]
    have hyw : ‖y - w‖ < η' / 2 := by rwa [mem_ball, dist_eq_norm] at hy
    calc ‖y‖ = ‖(y - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ η' / 2 + 1 := by linarith [hw]
      _ ≤ 2 := by linarith
  rcases lt_abs.1 hgt with hpos | hneg
  · left
    refine fun y ⟨hyS, hyB⟩ => ⟨Or.inl ⟨hyS, fun hyH : ⟪y, ν⟫ < 0 => ?_⟩, hsubK hyB⟩
    have hyw : ‖y - w‖ < η' / 2 := by rwa [mem_ball, dist_eq_norm] at hyB
    have hcs : |⟪y - w, ν⟫| ≤ ‖y - w‖ := by
      simpa only [hν, mul_one] using abs_real_inner_le_norm (y - w) ν
    have hsplit : ⟪y, ν⟫ = ⟪w, ν⟫ + ⟪y - w, ν⟫ := by rw [← inner_add_left, add_sub_cancel]
    linarith [neg_abs_le ⟪y - w, ν⟫]
  · right
    refine fun y ⟨hyB, hyS⟩ => ⟨Or.inr ⟨mem_ofPred.2 ?_, hyS⟩, hsubK hyB⟩
    have hyw : ‖y - w‖ < η' / 2 := by rwa [mem_ball, dist_eq_norm] at hyB
    have hcs : |⟪y - w, ν⟫| ≤ ‖y - w‖ := by
      simpa only [hν, mul_one] using abs_real_inner_le_norm (y - w) ν
    have hsplit : ⟪y, ν⟫ = ⟪w, ν⟫ + ⟪y - w, ν⟫ := by rw [← inner_add_left, add_sub_cancel]
    linarith [le_abs_self ⟪y - w, ν⟫]

/-- Rescaling lower volume density bounds at `z` (`z ≠ x`, `r = ‖z - x‖`, `w = r⁻¹ • (z - x)`) to
the blow-up `(fun y => x + r • y) ⁻¹' s` on `ball w τ`. -/
private theorem ofReal_pow_le_mul_measure_preimage_inter_and_sdiff [μ.IsAddHaarMeasure]
    {z : E} {C : ℝ≥0} {τ : ℝ} (hzx : z ≠ x)
    (h1 : ENNReal.ofReal ((‖z - x‖ * τ) ^ finrank ℝ E) ≤
      (C : ℝ≥0∞) ^ finrank ℝ E * μ (s ∩ ball z (‖z - x‖ * τ)))
    (h2 : ENNReal.ofReal ((‖z - x‖ * τ) ^ finrank ℝ E) ≤
      (C : ℝ≥0∞) ^ finrank ℝ E * μ (ball z (‖z - x‖ * τ) \ s)) :
    ENNReal.ofReal (τ ^ finrank ℝ E) ≤
        (C : ℝ≥0∞) ^ finrank ℝ E *
          μ (((fun y => x + ‖z - x‖ • y) ⁻¹' s) ∩ ball (‖z - x‖⁻¹ • (z - x)) τ) ∧
      ENNReal.ofReal (τ ^ finrank ℝ E) ≤
        (C : ℝ≥0∞) ^ finrank ℝ E *
          μ (ball (‖z - x‖⁻¹ • (z - x)) τ \ (fun y => x + ‖z - x‖ • y) ⁻¹' s) := by
  set r : ℝ := ‖z - x‖
  set w : E := r⁻¹ • (z - x)
  have hr : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hzx)
  have hxrw : x + r • w = z := by simp [w, smul_smul, mul_inv_cancel₀ hr.ne']
  have hball : (fun y : E => x + r • y) ⁻¹' ball z (r * τ) = ball w τ := by
    ext y
    simp only [mem_preimage, mem_ball, dist_eq_norm]
    rw [← hxrw, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, mul_lt_mul_iff_right₀ hr]
  have hscale (A : Set E) (hA : ENNReal.ofReal ((r * τ) ^ finrank ℝ E) ≤
      (C : ℝ≥0∞) ^ finrank ℝ E * μ A) :
      ENNReal.ofReal (τ ^ finrank ℝ E) ≤
        (C : ℝ≥0∞) ^ finrank ℝ E * μ ((fun y => x + r • y) ⁻¹' A) := by
    rw [Measure.addHaar_preimage_add_smul μ x hr.ne', mul_left_comm]
    calc ENNReal.ofReal (τ ^ finrank ℝ E)
        = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ENNReal.ofReal ((r * τ) ^ finrank ℝ E) := by
          rw [abs_of_pos (inv_pos.2 (pow_pos hr _)), ← ENNReal.ofReal_mul (by positivity),
            mul_pow, inv_mul_cancel_left₀ (pow_ne_zero _ hr.ne')]
      _ ≤ ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ((C : ℝ≥0∞) ^ finrank ℝ E * μ A) :=
          mul_le_mul_right hA _
  refine ⟨?_, ?_⟩
  · simpa only [preimage_inter, hball] using hscale (s ∩ ball z (r * τ)) h1
  · simpa only [preimage_sdiff, hball] using hscale (ball z (r * τ) \ s) h2

/-- **Normal cone estimate on uniform lower-density strata.** In dimension `n ≥ 2`, let `T` be a set
of points at which both `s` and `sᶜ` satisfy uniform lower volume density bounds up to radius
`ρ₀ > 0`. At any `x ∈ reducedBoundary μ Ω s` and for any `η > 0`, every point `z ∈ T` sufficiently
close to `x` satisfies `|⟪z - x, outerNormal μ Ω s x⟫| ≤ η * ‖z - x‖`. -/
theorem exists_pos_forall_abs_inner_sub_outerNormal_le [μ.IsAddHaarMeasure]
    (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary μ Ω s)
    {T : Set E} {C : ℝ≥0} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hs_low : ∀ z ∈ T, ∀ ρ ∈ Ioo 0 ρ₀,
      ENNReal.ofReal (ρ ^ finrank ℝ E) ≤ (C : ℝ≥0∞) ^ finrank ℝ E * μ (s ∩ ball z ρ))
    (hs_compl_low : ∀ z ∈ T, ∀ ρ ∈ Ioo 0 ρ₀,
      ENNReal.ofReal (ρ ^ finrank ℝ E) ≤ (C : ℝ≥0∞) ^ finrank ℝ E * μ (ball z ρ \ s))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > (0 : ℝ), ∀ z ∈ T, dist z x < δ →
      |⟪z - x, outerNormal μ Ω s x⟫| ≤ η * ‖z - x‖ := by
  set η' : ℝ := min η 1
  have hη'0 : 0 < η' := lt_min hη zero_lt_one
  set τ : ℝ := η' / 2
  have hτ : 0 < τ := half_pos hη'0
  set ν : E := outerNormal μ Ω s x
  have hblow := tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx
    (isCompact_closedBall (0 : E) 2)
  have hmul : Tendsto (fun r : ℝ => (C : ℝ≥0∞) ^ finrank ℝ E *
      μ ((((fun y => x + r • y) ⁻¹' s) ∆ {y | ⟪y, ν⟫ < 0}) ∩ closedBall 0 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hblow
      (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))
  have hev := hmul.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (pow_pos hτ (finrank ℝ E))))
  obtain ⟨δ₁, hδ₁, hδ₁_lt⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' zero_lt_one).1 hev
  refine ⟨min δ₁ (ρ₀ / τ), lt_min hδ₁ (div_pos hρ₀ hτ), fun z hz hzx_lt => ?_⟩
  rcases eq_or_ne z x with rfl | hzx
  · simp
  set r : ℝ := ‖z - x‖
  have hr : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hzx)
  have hr_δ₁ : r < δ₁ := by
    simpa only [r, ← dist_eq_norm] using hzx_lt.trans_le (min_le_left _ _)
  have hrτ : r * τ < ρ₀ := (lt_div_iff₀ hτ).1 <| by
    simpa only [r, ← dist_eq_norm] using hzx_lt.trans_le (min_le_right _ _)
  set w : E := r⁻¹ • (z - x)
  have hw : ‖w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_cancel₀ hr.ne']
  suffices hle : |⟪w, ν⟫| ≤ η' by
    have hzw : z - x = r • w := by simp [w, smul_smul, mul_inv_cancel₀ hr.ne']
    rw [hzw, inner_smul_left, RCLike.conj_to_real, abs_mul, abs_of_pos hr, mul_comm η]
    exact mul_le_mul_of_nonneg_left (hle.trans (min_le_left _ _)) hr.le
  by_contra! hgt
  obtain ⟨hlow1, hlow2⟩ := ofReal_pow_le_mul_measure_preimage_inter_and_sdiff (μ := μ) hzx
    (hs_low z hz (r * τ) ⟨mul_pos hr hτ, hrτ⟩) (hs_compl_low z hz (r * τ) ⟨mul_pos hr hτ, hrτ⟩)
  have hsmall : (C : ℝ≥0∞) ^ finrank ℝ E *
      μ ((((fun y => x + r • y) ⁻¹' s) ∆ {y | ⟪y, ν⟫ < 0}) ∩ closedBall 0 2) <
        ENNReal.ofReal (τ ^ finrank ℝ E) := hδ₁_lt ⟨hr, hr_δ₁⟩
  rcases inter_or_sdiff_subset_symmDiff_inter_closedBall hw (norm_outerNormal hx)
      hη'0 (min_le_right _ _) hgt with hsub | hsub
  · exact (hlow1.trans (mul_le_mul_right (measure_mono hsub) _)).not_gt hsmall
  · exact (hlow2.trans (mul_le_mul_right (measure_mono hsub) _)).not_gt hsmall

/-- **De Giorgi's rectifiability theorem.** In any finite-dimensional real inner product space `E`
equipped with an additive Haar measure `μ`, the reduced boundary `reducedBoundary μ Ω s` of any set
`s` in any open set `Ω` is countably `(dim E - 1)`-rectifiable. -/
theorem countablyRectifiable_reducedBoundary [μ.IsAddHaarMeasure] :
    CountablyRectifiable (finrank ℝ E - 1) (reducedBoundary μ Ω s) := by
  rcases le_or_gt (finrank ℝ E) 1 with hn | hn'
  · exact (countable_reducedBoundary_of_finrank_le_one hn).countablyRectifiable
  · have hn : 2 ≤ finrank ℝ E := hn'
    have hp : NNReal.HolderConjugate (finrank ℝ E) (NNReal.conjExponent (finrank ℝ E)) :=
      .conjExponent (by exact_mod_cast hn)
    let C : ℝ≥0 := (1 + 2) * finrank ℝ E *
      eLpNormLESNormFDerivOneConst μ (NNReal.conjExponent (finrank ℝ E))
    let r₀ (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
    let T (m : ℕ) : Set E := {z ∈ reducedBoundary μ Ω s |
      (∀ ρ ∈ Ioo 0 (r₀ m), ENNReal.ofReal (ρ ^ finrank ℝ E) ≤
        (C : ℝ≥0∞) ^ finrank ℝ E * μ (s ∩ ball z ρ)) ∧
      (∀ ρ ∈ Ioo 0 (r₀ m), ENNReal.ofReal (ρ ^ finrank ℝ E) ≤
        (C : ℝ≥0∞) ^ finrank ℝ E * μ (ball z ρ \ s))}
    have hcov : reducedBoundary μ Ω s = ⋃ m : ℕ, T m := by
      ext z
      simp only [T, mem_iUnion, mem_ofPred_eq]
      refine ⟨fun hz => ?_, fun ⟨_, hz, _⟩ => hz⟩
      have hev := (eventually_ofReal_pow_le_mul_measure_inter_ball hp hz (t := 2) one_lt_two).and
        (eventually_ofReal_pow_le_mul_measure_ball_sdiff hp hz (t := 2) one_lt_two)
      obtain ⟨u, hu, husub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' zero_lt_one).1 hev
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hu
      exact ⟨m, hz, fun ρ hρ => (husub ⟨hρ.1, hρ.2.trans hm⟩).1,
        fun ρ hρ => (husub ⟨hρ.1, hρ.2.trans hm⟩).2⟩
    rw [hcov]
    refine CountablyRectifiable.iUnion fun m =>
      CountablyRectifiable.of_forall_exists_abs_inner_sub_le fun x hx => ?_
    have hnorm : ‖outerNormal μ Ω s x‖ = 1 := norm_outerNormal hx.1
    have hne : outerNormal μ Ω s x ≠ 0 := fun h0 => by simp [h0] at hnorm
    obtain ⟨δ, hδ, hcone⟩ := exists_pos_forall_abs_inner_sub_outerNormal_le (μ := μ) hn hx.1
      (T := T m) (C := C) Nat.one_div_pos_of_nat (fun z hz => hz.2.1) (fun z hz => hz.2.2)
      (η := 1 / 2) one_half_pos
    exact ⟨outerNormal μ Ω s x, hne, 1 / 2, by norm_num, δ, hδ,
      fun y hy hyx => by simpa only [hnorm, mul_one] using hcone y hy hyx⟩

end TauCeti
