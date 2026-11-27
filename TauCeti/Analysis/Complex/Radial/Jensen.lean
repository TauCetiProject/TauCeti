/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.SpecialFunctions.Integrability.PosLog
import TauCeti.Topology.MetricSpace.Pseudo.Defs

/-!
# Jensen's inequality for the radial limits of a bounded holomorphic function

Let `f` be holomorphic and bounded on the disc `ball c R` and let `G` give its radial limits:
`f (circleMap c r θ) → G (circleMap c R θ)` as `r` increases to `R`, for almost every `θ`. Then
`log ‖G‖` is integrable on the circle and Jensen's inequality passes to the boundary:
`k log R + log ‖τ‖ ≤ ⨍ log ‖G‖`, with `k` the order of `f` at `c` and `τ` its trailing coefficient
(`TauCeti.circleIntegrable_log_norm_of_tendsto_circleMap`,
`TauCeti.le_circleAverage_log_norm_of_tendsto_circleMap`); at a nonvanishing centre this is
`log ‖f c‖ ≤ ⨍ log ‖G‖` (`TauCeti.log_norm_le_circleAverage_log_norm_of_tendsto_circleMap`).

The proof: on the circles of radii `ρₙ → R`, Jensen's inequality
(`AnalyticOnNhd.le_circleAverage_log_norm`) bounds the averages of
`log⁺ ‖f‖⁻¹ = log⁺ ‖f‖ - log ‖f‖`; the averages of `log⁺ ‖f‖` converge by dominated convergence,
since `f` is bounded, and Fatou's lemma (`MeasureTheory.lintegral_liminf_le'`) bounds the integral
of `log⁺ ‖G‖⁻¹`.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised first edition, Graduate Texts in
  Mathematics 236, Springer, 2007, Chapter II.
-/

public section

open Filter Metric MeasureTheory Set Topology
open Real
open scoped ENNReal

variable {f G : ℂ → ℂ} {c : ℂ} {R S : ℝ}

namespace TauCeti

/-- On a circle of radius `r ∈ (0, R)`, Jensen's inequality bounds the integral of
`log⁺ ‖f‖⁻¹` over a period by `∫ log⁺ ‖f‖ - 2π (k log r + log ‖τ‖)`, which is nonnegative. -/
private theorem lintegral_posLog_inv_le (hf : DifferentiableOn ℂ f (ball c R)) {r : ℝ}
    (hr : r ∈ Ioo 0 R) :
    ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (log⁺ ‖f (circleMap c r θ)‖⁻¹) ≤
        ENNReal.ofReal ((∫ θ in 0..2 * π, log⁺ ‖f (circleMap c r θ)‖) -
          2 * π * (analyticOrderNatAt f c * Real.log r +
            Real.log ‖meromorphicTrailingCoeffAt f c‖)) ∧
      0 ≤ (∫ θ in 0..2 * π, log⁺ ‖f (circleMap c r θ)‖) -
          2 * π * (analyticOrderNatAt f c * Real.log r +
            Real.log ‖meromorphicTrailingCoeffAt f c‖) := by
  have han : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  have hmero : MeromorphicOn f (sphere c |r|) :=
    (han.mono (sphere_abs_subset_ball hr)).meromorphicOn
  have hJ := (han.mono (s := closedBall c |r|) fun z hz ↦ ?_).le_circleAverage_log_norm hr.1.ne'
  · have hπ : 0 < 2 * π := two_pi_pos
    have hav : circleAverage (fun z ↦ log⁺ ‖f z‖) c r =
        (2 * π)⁻¹ * ∫ θ in 0..2 * π, log⁺ ‖f (circleMap c r θ)‖ := by
      rw [circleAverage_def, smul_eq_mul]
    have h3 : 0 ≤ circleAverage (fun z ↦ log⁺ ‖f z‖⁻¹) c r :=
      circleAverage_nonneg_of_nonneg fun _ _ ↦ posLog_nonneg
    rw [hmero.circleAverage_posLog_inv_norm, hav] at h3
    rw [hmero.lintegral_ofReal_posLog_inv_norm_circleMap, hav]
    set I := ∫ θ in 0..2 * π, log⁺ ‖f (circleMap c r θ)‖
    have e : 2 * π * ((2 * π)⁻¹ * I - circleAverage (fun z ↦ Real.log ‖f z‖) c r) =
        I - 2 * π * circleAverage (fun z ↦ Real.log ‖f z‖) c r := by
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul]
    have h5 := mul_nonneg hπ.le h3
    rw [e] at h5 ⊢
    exact ⟨ENNReal.ofReal_le_ofReal (by nlinarith), by nlinarith⟩
  · rw [abs_of_pos hr.1] at hz
    exact closedBall_subset_ball hr.2 hz

/-- Along radii `ρ n ∈ (0, R)` increasing to `R`, `f` on the circles tends almost everywhere to
the boundary function, which is almost everywhere strongly measurable and bounded by `S`, and the
integrals of `log⁺ ‖f‖` over a period converge to that of `log⁺ ‖G‖`. -/
private theorem tendsto_circleMap_radii (hf : DifferentiableOn ℂ f (ball c R))
    (hS : ∀ z ∈ ball c R, ‖f z‖ ≤ S)
    (hlim : ∀ᵐ θ, Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 (G (circleMap c R θ))))
    {ρ : ℕ → ℝ} (hρ : ∀ n, ρ n ∈ Ioo 0 R) (hρlim : Tendsto ρ atTop (𝓝[<] R)) :
    (∀ n : ℕ, Continuous fun θ ↦ f (circleMap c (ρ n) θ)) ∧
      AEStronglyMeasurable (fun θ ↦ G (circleMap c R θ)) volume ∧
      (∀ᵐ θ, ‖G (circleMap c R θ)‖ ≤ S) ∧
      Tendsto (fun n : ℕ ↦ ∫ θ in 0..2 * π, log⁺ ‖f (circleMap c (ρ n) θ)‖)
        atTop (𝓝 (∫ θ in 0..2 * π, log⁺ ‖G (circleMap c R θ)‖)) := by
  have hmem (n : ℕ) (θ : ℝ) : circleMap c (ρ n) θ ∈ ball c R :=
    sphere_abs_subset_ball (hρ n) (circleMap_mem_sphere' c _ θ)
  have hcont (n : ℕ) : Continuous fun θ ↦ f (circleMap c (ρ n) θ) :=
    hf.continuousOn.comp_continuous (continuous_circleMap c _) (hmem n)
  have hu := hlim.mono fun θ h ↦ h.comp hρlim
  refine ⟨hcont, aestronglyMeasurable_of_tendsto_ae atTop
    (fun n ↦ (hcont n).aestronglyMeasurable) hu,
    hu.mono fun θ h ↦ le_of_tendsto' h.norm fun n ↦ hS _ (hmem n θ), ?_⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ log⁺ S)
    (.of_forall fun n ↦ ?_) (.of_forall fun n ↦ .of_forall fun θ _ ↦ ?_) intervalIntegrable_const
    (hu.mono fun θ h _ ↦ (continuous_posLog.tendsto _).comp h.norm)
  · exact (continuous_posLog.comp (hcont n).norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg posLog_nonneg]
    exact posLog_le_posLog (by linarith [norm_nonneg (f (circleMap c (ρ n) θ))])
      (hS _ (hmem n θ))

/-- The boundary data of the main theorem: the integral of `log⁺ ‖G‖⁻¹` over a period is at most
`∫ log⁺ ‖G‖ - 2π (k log R + log ‖τ‖)`, and the boundary function is almost everywhere strongly
measurable and bounded by `S`. -/
private theorem boundary_data (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hS : ∀ z ∈ ball c R, ‖f z‖ ≤ S)
    (hlim : ∀ᵐ θ, Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 (G (circleMap c R θ)))) :
    AEStronglyMeasurable (fun θ ↦ G (circleMap c R θ)) volume ∧
      (∀ᵐ θ, ‖G (circleMap c R θ)‖ ≤ S) ∧
      ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (log⁺ ‖G (circleMap c R θ)‖⁻¹) ≤
        ENNReal.ofReal ((∫ θ in 0..2 * π, log⁺ ‖G (circleMap c R θ)‖) -
          2 * π * (analyticOrderNatAt f c * Real.log R +
            Real.log ‖meromorphicTrailingCoeffAt f c‖)) ∧
      0 ≤ (∫ θ in 0..2 * π, log⁺ ‖G (circleMap c R θ)‖) -
          2 * π * (analyticOrderNatAt f c * Real.log R +
            Real.log ‖meromorphicTrailingCoeffAt f c‖) := by
  obtain ⟨ρ, -, hρ, hρlim⟩ := exists_seq_strictMono_tendsto' hR
  have hρlim' : Tendsto ρ atTop (𝓝[<] R) :=
    tendsto_nhdsWithin_iff.2 ⟨hρlim, .of_forall fun n ↦ (hρ n).2⟩
  set u : ℕ → ℝ → ℂ := fun n θ ↦ f (circleMap c (ρ n) θ)
  obtain ⟨hcont, hgm, hgS, hA⟩ := tendsto_circleMap_radii hf hS hlim hρ hρlim'
  have hu := hlim.mono fun θ h ↦ h.comp hρlim'
  have hb : Tendsto (fun n ↦ (∫ θ in 0..2 * π, log⁺ ‖u n θ‖) -
      2 * π * (analyticOrderNatAt f c * Real.log (ρ n) +
        Real.log ‖meromorphicTrailingCoeffAt f c‖)) atTop
      (𝓝 ((∫ θ in 0..2 * π, log⁺ ‖G (circleMap c R θ)‖) -
        2 * π * (analyticOrderNatAt f c * Real.log R +
          Real.log ‖meromorphicTrailingCoeffAt f c‖))) := by
    have hlog : Tendsto (fun n ↦ Real.log (ρ n)) atTop (𝓝 (Real.log R)) :=
      ((continuousAt_log hR.ne').tendsto).comp hρlim
    exact hA.sub (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hlog).add tendsto_const_nhds))
  have hL (n : ℕ) := lintegral_posLog_inv_le hf (hρ n)
  -- Fatou's lemma
  have hmeas (n : ℕ) : AEMeasurable (fun θ ↦ ENNReal.ofReal (log⁺ ‖u n θ‖⁻¹))
      (volume.restrict (Ioc 0 (2 * π))) :=
    (continuous_posLog.measurable.comp (hcont n).measurable.norm.inv).ennreal_ofReal.aemeasurable
  have hpt : ∀ᵐ θ ∂volume.restrict (Ioc 0 (2 * π)),
      ENNReal.ofReal (log⁺ ‖G (circleMap c R θ)‖⁻¹) ≤
        liminf (fun n ↦ ENNReal.ofReal (log⁺ ‖u n θ‖⁻¹)) atTop := by
    refine ae_restrict_of_ae (hu.mono fun θ h ↦ ?_)
    rcases eq_or_ne (G (circleMap c R θ)) 0 with h0 | h0
    · simp [h0]
    · refine (Tendsto.liminf_eq ?_).ge
      exact (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_posLog.tendsto _).comp
        (h.norm.inv₀ (norm_ne_zero_iff.2 h0)))
  refine ⟨hgm, hgS, ?_, ge_of_tendsto hb (.of_forall fun n ↦ (hL n).2)⟩
  refine (lintegral_mono_ae hpt).trans ((lintegral_liminf_le' hmeas).trans ?_)
  refine (liminf_le_liminf (.of_forall fun n ↦ (hL n).1)).trans_eq ?_
  exact ((ENNReal.continuous_ofReal.tendsto _).comp hb).liminf_eq

/-- The two parts `log⁺ ‖G‖` and `log⁺ ‖G‖⁻¹` of `log ‖G‖` are integrable on a period, and the
integral of the second is bounded through Jensen's inequality. -/
private theorem integrableOn_posLog (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hS : ∀ z ∈ ball c R, ‖f z‖ ≤ S)
    (hlim : ∀ᵐ θ, Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 (G (circleMap c R θ)))) :
    IntegrableOn (fun θ ↦ log⁺ ‖G (circleMap c R θ)‖) (Ioc 0 (2 * π)) ∧
      IntegrableOn (fun θ ↦ log⁺ ‖G (circleMap c R θ)‖⁻¹) (Ioc 0 (2 * π)) ∧
      ∫ θ in 0..2 * π, log⁺ ‖G (circleMap c R θ)‖⁻¹ ≤
        (∫ θ in 0..2 * π, log⁺ ‖G (circleMap c R θ)‖) -
          2 * π * (analyticOrderNatAt f c * Real.log R +
            Real.log ‖meromorphicTrailingCoeffAt f c‖) := by
  obtain ⟨hgm, hgS, hfatou, hb₀⟩ := boundary_data hR hf hS hlim
  have I1 : IntegrableOn (fun θ ↦ log⁺ ‖G (circleMap c R θ)‖) (Ioc 0 (2 * π)) :=
    Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (continuous_posLog.comp_aestronglyMeasurable hgm.norm) (M := log⁺ S)
      (ae_restrict_of_ae (hgS.mono fun θ h ↦ by
        rw [Real.norm_of_nonneg posLog_nonneg]
        exact posLog_le_posLog (by linarith [norm_nonneg (G (circleMap c R θ))]) h))
  have hm : AEStronglyMeasurable (fun θ ↦ log⁺ ‖G (circleMap c R θ)‖⁻¹) volume :=
    (continuous_posLog.measurable.comp_aemeasurable hgm.aemeasurable.norm.inv).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))] fun θ ↦ log⁺ ‖G (circleMap c R θ)‖⁻¹ :=
    .of_forall fun _ ↦ posLog_nonneg
  have I2 : IntegrableOn (fun θ ↦ log⁺ ‖G (circleMap c R θ)‖⁻¹) (Ioc 0 (2 * π)) :=
    ⟨hm.restrict, (hasFiniteIntegral_iff_ofReal hnn).2 (hfatou.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨I1, I2, ?_⟩
  rw [intervalIntegral.integral_of_le two_pi_pos.le, ← ENNReal.ofReal_le_ofReal_iff hb₀,
    ofReal_integral_eq_lintegral_ofReal I2 hnn]
  exact hfatou

/-- **The logarithm of the radial limits is integrable.** If `f` is holomorphic and bounded on
`ball c R` and `G` gives its radial limits almost everywhere, then `log ‖G‖` is integrable on the
circle `sphere c R`. -/
theorem circleIntegrable_log_norm_of_tendsto_circleMap (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hS : ∀ z ∈ ball c R, ‖f z‖ ≤ S)
    (hlim : ∀ᵐ θ, Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 (G (circleMap c R θ)))) :
    CircleIntegrable (fun z ↦ Real.log ‖G z‖) c R := by
  obtain ⟨I1, I2, -⟩ := integrableOn_posLog hR hf hS hlim
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).2 ?_
  exact (I1.sub I2).congr_fun (fun θ _ ↦ by simp only [Pi.sub_apply, posLog_sub_posLog_inv])
    measurableSet_Ioc

/-- **Jensen's inequality for radial limits.** If `f` is holomorphic and bounded on `ball c R` and
`G` gives its radial limits almost everywhere, then `k log R + log ‖τ‖ ≤ ⨍ log ‖G‖` over the circle
`sphere c R`, where `k` is the order of `f` at `c` and `τ` its trailing coefficient there. -/
theorem le_circleAverage_log_norm_of_tendsto_circleMap (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hS : ∀ z ∈ ball c R, ‖f z‖ ≤ S)
    (hlim : ∀ᵐ θ, Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 (G (circleMap c R θ)))) :
    analyticOrderNatAt f c * Real.log R + Real.log ‖meromorphicTrailingCoeffAt f c‖ ≤
      circleAverage (fun z ↦ Real.log ‖G z‖) c R := by
  obtain ⟨I1, I2, hJ⟩ := integrableOn_posLog hR hf hS hlim
  have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).2 I1
  have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).2 I2
  have hπ : 0 < 2 * π := two_pi_pos
  have heq : (∫ θ in 0..2 * π, Real.log ‖G (circleMap c R θ)‖) =
      ∫ θ in 0..2 * π, (log⁺ ‖G (circleMap c R θ)‖ - log⁺ ‖G (circleMap c R θ)‖⁻¹) :=
    intervalIntegral.integral_congr fun θ _ ↦ posLog_sub_posLog_inv.symm
  rw [circleAverage_def, smul_eq_mul, heq, intervalIntegral.integral_sub h1 h2,
    le_inv_mul_iff₀ hπ]
  linarith

/-- **Jensen's inequality for radial limits at a nonvanishing centre.** If `f` is holomorphic and
bounded on `ball c R` with `f c ≠ 0`, and `G` gives its radial limits almost everywhere, then
`log ‖f c‖ ≤ ⨍ log ‖G‖` over the circle `sphere c R`. -/
theorem log_norm_le_circleAverage_log_norm_of_tendsto_circleMap (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hS : ∀ z ∈ ball c R, ‖f z‖ ≤ S) (hfc : f c ≠ 0)
    (hlim : ∀ᵐ θ, Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 (G (circleMap c R θ)))) :
    Real.log ‖f c‖ ≤ circleAverage (fun z ↦ Real.log ‖G z‖) c R := by
  have han : AnalyticAt ℂ f c := hf.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hord : analyticOrderNatAt f c = 0 := by
    by_contra hne
    exact hfc (apply_eq_zero_of_analyticOrderNatAt_ne_zero hne)
  have := le_circleAverage_log_norm_of_tendsto_circleMap hR hf hS hlim
  rwa [hord, han.meromorphicTrailingCoeffAt_of_ne_zero hfc, Nat.cast_zero, zero_mul,
    zero_add] at this

end TauCeti
