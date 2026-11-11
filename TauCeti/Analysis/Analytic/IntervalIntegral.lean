/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrating an analytic function over a family of contractions

Let `f` have the power series `p` on the ball of radius `r` about `c`, and let `L t` be an
almost everywhere strongly measurable family of continuous linear maps, of norm at most one for
almost every `t` between `a` and `b`. Then `z ↦ ∫ t in a..b, f (c + L t (z - c))` has a power
series on the same ball, whose `n`-th coefficient is the integral of `p n` precomposed with `L t`
in every slot (`HasFPowerSeriesOnBall.intervalIntegral_comp`). In particular this integral is
analytic at `c` (`AnalyticAt.intervalIntegral_comp`).

The scalar field `𝕜` may be any nontrivially normed field. The target space has normed-space
structures over `𝕜` and `ℝ` with commuting scalar actions; `𝕜` need not be an algebra over `ℝ`.

The typical use is the integral form of Hadamard's lemma: if `G (x, y)` vanishes on `y = y₀`, then
`G (x, y) = (y - y₀) • ∫ t in 0..1, ∂G/∂y (x, y₀ + t (y - y₀))`, and this lemma, applied with
`L t (x, y) = (x, t y)`, shows that the quotient is again analytic.
-/

public section

open Set MeasureTheory intervalIntegral
open scoped ENNReal NNReal Interval

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  [SMulCommClass 𝕜 ℝ F] [CompleteSpace F]

/-- If `f` has the power series `p` on the ball of radius `r` about `c`, and `L t` is an
a.e.-strongly measurable family of continuous linear maps of norm at most one for almost every
`t` between `a` and `b`, then `z ↦ ∫ t in a..b, f (c + L t (z - c))` has on the same ball the
power series whose `n`-th coefficient is `∫ t in a..b, p n ∘ (L t, …, L t)`. -/
theorem HasFPowerSeriesOnBall.intervalIntegral_comp {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {c : E} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p c r)
    {L : ℝ → E →L[𝕜] E} {a b : ℝ} (hL : AEStronglyMeasurable L (volume.restrict (Ι a b)))
    (hL1 : ∀ᵐ t, t ∈ Ι a b → ‖L t‖ ≤ 1) :
    HasFPowerSeriesOnBall (fun z ↦ ∫ t in a..b, f (c + L t (z - c)))
      (fun n ↦ ∫ t in a..b, (p n).compContinuousLinearMap fun _ ↦ L t) c r := by
  -- the coefficient family is measurable and bounded by `‖p n‖`, hence integrable
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun t ↦ (p n).compContinuousLinearMap fun _ ↦ L t) (volume.restrict (Ι a b)) := by
    have := ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
      (fun _ : Fin n ↦ E) (fun _ ↦ E) F).cont.comp (continuous_pi fun _ ↦ continuous_id)).clm_apply
        (continuous_const (y := p n))
    simpa using this.comp_aestronglyMeasurable hL
  have hbound (n : ℕ) : ∀ᵐ t, t ∈ Ι a b → ‖(p n).compContinuousLinearMap fun _ ↦ L t‖ ≤ ‖p n‖ :=
    hL1.mono fun t ht hmem ↦ (p.norm_compContinuousLinearMap_le (L t) n).trans <|
      mul_le_of_le_one_right (norm_nonneg _) <| pow_le_one₀ (norm_nonneg _) (ht hmem)
  have hint (n : ℕ) : IntervalIntegrable
      (fun t ↦ (p n).compContinuousLinearMap fun _ ↦ L t) volume a b :=
    (intervalIntegrable_const (c := ‖p n‖)).mono_fun (hmeas n) <|
      (ae_restrict_iff' measurableSet_uIoc).2 <| (hbound n).mono fun t ht hmem ↦ by
        simpa using ht hmem
  -- the coefficients are bounded by `‖p n‖ * |b - a|`, so the radius does not decrease
  have hradius : p.radius ≤ FormalMultilinearSeries.radius
      fun n ↦ ∫ t in a..b, (p n).compContinuousLinearMap fun _ ↦ L t := by
    refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ ↦ ?_
    obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hρ
    refine FormalMultilinearSeries.le_radius_of_bound _ (C * |b - a|) fun n ↦ ?_
    calc _ ≤ ‖p n‖ * |b - a| * (ρ : ℝ) ^ n := by
          gcongr; exact norm_integral_le_of_norm_le_const_ae (hbound n)
      _ = ‖p n‖ * (ρ : ℝ) ^ n * |b - a| := by ring
      _ ≤ C * |b - a| := by gcongr; exact hC n
  refine ⟨hf.r_le.trans hradius, hf.r_pos, fun {y} hy ↦ ?_⟩
  simp only [add_sub_cancel_left]
  have hy' : (‖y‖₊ : ℝ≥0∞) < p.radius := by
    simpa [edist_zero_right, enorm_eq_nnnorm] using lt_of_lt_of_le hy hf.r_le
  have happly (n : ℕ) : (∫ t in a..b, (p n).compContinuousLinearMap fun _ ↦ L t)
      (fun _ ↦ y) = ∫ t in a..b, p n fun _ ↦ L t y := by
    -- Evaluation is real-linear even when `𝕜` has no real algebra structure.
    let ev : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ E) F →L[ℝ] F :=
      (ContinuousMultilinearMap.applyAddHom (fun _ ↦ y)).toRealLinearMap
        (continuous_eval_const _)
    simpa [ev, AddMonoidHom.coe_toRealLinearMap, ContinuousMultilinearMap.applyAddHom] using
      (ev.intervalIntegral_comp_comm (hint n)).symm
  simp only [happly]
  -- dominated convergence, with the summable bound `‖p n‖ * ‖y‖ ^ n`
  have hLy : ∀ᵐ t, t ∈ Ι a b → ‖L t y‖ ≤ ‖y‖ := hL1.mono fun t ht hmem ↦
    ((L t).le_of_opNorm_le (ht hmem) y).trans (by simp)
  refine hasSum_integral_of_dominated_convergence (F := fun n t ↦ p n fun _ ↦ L t y)
    (f := fun t ↦ f (c + L t y)) (fun n _ ↦ ‖p n‖ * ‖y‖ ^ n) (fun n ↦ ?_)
    (fun n ↦ hLy.mono fun t ht hmem ↦ ?_)
    (Filter.Eventually.of_forall fun _ _ ↦ by simpa using p.summable_norm_mul_pow hy')
    intervalIntegrable_const (hLy.mono fun t ht hmem ↦ ?_)
  · exact ((p n).cont.comp (continuous_pi fun _ ↦ continuous_id.clm_apply continuous_const))
      |>.comp_aestronglyMeasurable hL
  · exact (p n).le_opNorm_mul_pow_of_le
      ((pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun _ ↦ ht hmem)
  · refine hf.hasSum ?_
    simp only [Metric.mem_eball, edist_zero_right] at hy ⊢
    exact lt_of_le_of_lt (by simpa [enorm_eq_nnnorm, ← NNReal.coe_le_coe] using ht hmem) hy

/-- If `f` is analytic at `c`, and `L t` is an a.e.-strongly measurable family of continuous
linear maps of norm at most one for almost every `t` between `a` and `b`, then
`z ↦ ∫ t in a..b, f (c + L t (z - c))` is analytic at `c`. -/
theorem AnalyticAt.intervalIntegral_comp {f : E → F} {c : E} (hf : AnalyticAt 𝕜 f c)
    {L : ℝ → E →L[𝕜] E} {a b : ℝ} (hL : AEStronglyMeasurable L (volume.restrict (Ι a b)))
    (hL1 : ∀ᵐ t, t ∈ Ι a b → ‖L t‖ ≤ 1) :
    AnalyticAt 𝕜 (fun z ↦ ∫ t in a..b, f (c + L t (z - c))) c := by
  obtain ⟨p, r, hp⟩ := hf
  exact (hp.intervalIntegral_comp hL hL1).analyticAt
