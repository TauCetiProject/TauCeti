/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.BoundedVariation.Multiplication
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Compactly supported smooth strict approximation

Every integrable real function on a finite-dimensional real inner product space admits
compactly supported smooth approximations converging in `L¹` and in total variation.
The variation may be infinite. For a BV function this is strict approximation, which is
weaker than convergence in the BV norm: jumps and singular derivatives are allowed.

Compact support makes the approximations suitable for choosing bounded regular superlevel
sets. Spatial cutoffs first control the error at infinity; mollification then provides
smoothness without losing compact support. The central formal inputs are
`TauCeti.totalVariationOn_top_mul_le`, the quantitative radial cutoffs in
`TauCeti.exists_forall_contDiff_cutoff_closedBall`, and
`ContDiffBump.totalVariationOn_normed_convolution_le`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §5.2.2 (smooth approximation of BV functions).
-/

public section

noncomputable section

open MeasureTheory Filter Metric Set TopologicalSpace ContinuousLinearMap
open scoped ENNReal NNReal Convolution Topology Gradient ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → ℝ}

namespace TauCeti

omit [μ.IsAddHaarMeasure] in
private theorem exists_cutoff_approximation (hu : Integrable u μ) :
    ∃ v : ℕ → E → ℝ, (∀ n, Integrable (v n) μ ∧ HasCompactSupport (v n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖v n x - u x‖ₑ ∂μ) atTop (𝓝 0) ∧
      ∃ b : ℕ → ℝ≥0∞, Tendsto b atTop (𝓝 0) ∧
        ∀ n, totalVariationOn μ ⊤ (v n) ≤ totalVariationOn μ ⊤ u + b n := by
  -- Cut off on expanding balls with derivative bound tending to zero.
  obtain ⟨c, hc, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := E)
  have hcut' (n : ℕ) := hcut (0 : E) (r := n + 1) (R := 2 * (n + 1))
    (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  choose χ hχ hχ01 hχone hχsupp hχgrad _ using hcut'
  have hχnorm (n : ℕ) (x : E) : ‖χ n x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ01 n (mem_range_self x)).1]
    exact (hχ01 n (mem_range_self x)).2
  have hχc (n : ℕ) : HasCompactSupport (χ n) :=
    (isCompact_closedBall (0 : E) (2 * (n + 1))).of_isClosed_subset
      (isClosed_tsupport _) (hχsupp n)
  have hv (n : ℕ) : Integrable (χ n * u) μ :=
    hu.bdd_mul (hχ n).continuous.aestronglyMeasurable (.of_forall (hχnorm n))
  -- Dominated convergence controls the discarded L¹ mass.
  have hlim : Tendsto (fun n => ∫⁻ x, ‖χ n x * u x - u x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hdom (n : ℕ) (x : E) : ‖χ n x * u x - u x‖ₑ ≤ ‖u x‖ₑ := by
      rw [← sub_one_mul, enorm_mul]
      have hle : ‖χ n x - 1‖ₑ ≤ 1 := by
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact (ENNReal.ofReal_le_ofReal (by
          have h0 := (hχ01 n (mem_range_self x)).1
          have h1 := (hχ01 n (mem_range_self x)).2
          rw [abs_of_nonpos (by linarith)]
          linarith)).trans_eq ENNReal.ofReal_one
      simpa using mul_le_mul_left hle ‖u x‖ₑ
    have hpoint (x : E) : ∀ᶠ n : ℕ in atTop, χ n x = 1 := by
      filter_upwards [(tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x‖)] with n hn
      exact hχone n (by simpa using (hn.trans (by linarith : (n : ℝ) ≤ n + 1)))
    simpa only [Pi.mul_apply, Pi.sub_apply, lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0) (fun x => ‖u x‖ₑ)
        (fun n => ((hv n).sub hu).aestronglyMeasurable.enorm)
        (fun n => .of_forall (hdom n)) hu.hasFiniteIntegral.ne
        (.of_forall fun x => tendsto_const_nhds.congr' ((hpoint x).mono fun n hn => by
          simp only [Pi.sub_apply, Pi.mul_apply, hn, one_mul, sub_self, enorm_zero]))
  -- The product estimate bounds the additional variation by the L¹ mass times c / (n + 1).
  let b (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (c / (n + 1)) * ∫⁻ x, ‖u x‖ₑ ∂μ
  have hb : Tendsto b atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => c / (n + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat (a := c)
    have h := ENNReal.Tendsto.mul_const
      (ENNReal.continuous_ofReal.tendsto 0 |>.comp hreal)
      (Or.inr hu.hasFiniteIntegral.ne)
    simpa [b, div_eq_mul_inv] using h
  refine ⟨fun n => χ n * u, fun n => ⟨hv n, (hχc n).mul_right⟩, hlim, b, hb, fun n => ?_⟩
  have hgrad (x : E) : ‖fderiv ℝ (χ n) x‖ ≤ c / (n + 1) := by
    have hr : 2 * ((n : ℝ) + 1) - (n + 1) = n + 1 := by ring
    simpa only [← toDual_gradient (𝕜 := ℝ), LinearIsometryEquiv.norm_map, hr] using hχgrad n x
  simpa only [b, ENNReal.ofReal_one, one_mul, Opens.coe_top, Measure.restrict_univ] using
    totalVariationOn_top_mul_le (μ := μ) (u := u) (c := 1) (Ω := ⊤) (hχ n)
      (fun x => by simpa only [Real.norm_eq_abs] using hχnorm n x)
      (subset_univ _) hgrad (hu.locallyIntegrable.locallyIntegrableOn ⊤)

end TauCeti

namespace MeasureTheory.Integrable

/-- Every integrable real function admits compactly supported smooth approximations converging
in `L¹` and in total variation on the whole space. For finite variation this is strict BV
approximation; the variation limit also holds when the original variation is infinite. -/
theorem exists_contDiff_hasCompactSupport_strict_approximation (hu : Integrable u μ) :
    ∃ w : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (w n) ∧ HasCompactSupport (w n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖w n x - u x‖ₑ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => TauCeti.totalVariationOn μ ⊤ (w n)) atTop
        (𝓝 (TauCeti.totalVariationOn μ ⊤ u)) := by
  obtain ⟨v, hv, hvlim, b, hb, hvbound⟩ := TauCeti.exists_cutoff_approximation hu
  let φ : ℕ → ContDiffBump (0 : E) := fun k =>
    ⟨1 / (k + 2), 1 / (k + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- Choose a mollification separately for each cutoff, with vanishing L¹ error.
  have happ (n : ℕ) : ∃ k, ∫⁻ x,
      ‖((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] v n) x - v n x‖ₑ ∂μ < ENNReal.ofReal (1 / (n + 1)) := by
    have h := TauCeti.tendsto_eLpNorm_normed_convolution_sub ENNReal.one_ne_top hφ
      (memLp_one_iff_integrable.mpr (hv n).1)
    have hi (k : ℕ) : Integrable ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] v n - v n) μ :=
      ((φ k).integrable_normed.integrable_convolution (lsmul ℝ ℝ) (hv n).1).sub (hv n).1
    simp_rw [eLpNorm_one_eq_lintegral_enorm (hi _).aestronglyMeasurable] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  choose k hk using happ
  let w (n : ℕ) : E → ℝ := (φ (k n)).normed μ ⋆[lsmul ℝ ℝ, μ] v n
  have hw (n : ℕ) : ContDiff ℝ ∞ (w n) ∧ HasCompactSupport (w n) :=
    ⟨(φ (k n)).hasCompactSupport_normed.contDiff_convolution_left _
      (φ (k n)).contDiff_normed (hv n).1.locallyIntegrable,
      (φ (k n)).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) (hv n).2⟩
  have hwi (n : ℕ) : Integrable (w n - v n) μ :=
    ((φ (k n)).integrable_normed.integrable_convolution (lsmul ℝ ℝ) (hv n).1).sub (hv n).1
  have hwv (n : ℕ) : TauCeti.totalVariationOn μ ⊤ (w n) ≤
      TauCeti.totalVariationOn μ ⊤ u + b n :=
    ((φ (k n)).totalVariationOn_normed_convolution_le
      ((hv n).1.locallyIntegrable.locallyIntegrableOn ⊤) (fun _ _ => subset_univ _)).trans
        (hvbound n)
  -- The two L¹ errors vanish; mollification does not increase the cutoff variation.
  have hwlim : Tendsto (fun n => ∫⁻ x, ‖w n x - u x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hzero : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, one_div, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.tendsto 0 |>.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hsum := hzero.add hvlim
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) fun n => ?_
    calc ∫⁻ x, ‖w n x - u x‖ₑ ∂μ
        ≤ ∫⁻ x, ‖w n x - v n x‖ₑ + ‖v n x - u x‖ₑ ∂μ :=
          lintegral_mono fun x => by
            simpa only [sub_add_sub_cancel] using
              (enorm_add_le (a := w n x - v n x) (b := v n x - u x))
      _ = (∫⁻ x, ‖w n x - v n x‖ₑ ∂μ) + ∫⁻ x, ‖v n x - u x‖ₑ ∂μ :=
          lintegral_add_left' (hwi n).aestronglyMeasurable.enorm _
      _ ≤ _ := add_le_add (hk n).le le_rfl
  -- Lower semicontinuity and the upper estimate give equality in the limit.
  refine ⟨w, hw, hwlim, tendsto_of_le_liminf_of_limsup_le ?_ ?_⟩
  · refine TauCeti.totalVariationOn_le_liminf
      (.of_forall fun n => (hw n).1.continuous.locallyIntegrable.locallyIntegrableOn ⊤)
      (hu.locallyIntegrable.locallyIntegrableOn ⊤) fun K _ _ => ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hwlim
      (fun _ => zero_le) (fun n => setLIntegral_le_lintegral _ _)
  · have hbound := tendsto_const_nhds.add hb (a := TauCeti.totalVariationOn μ ⊤ u)
    rw [add_zero] at hbound
    exact (limsup_le_limsup (.of_forall hwv)).trans_eq hbound.limsup_eq

end MeasureTheory.Integrable
