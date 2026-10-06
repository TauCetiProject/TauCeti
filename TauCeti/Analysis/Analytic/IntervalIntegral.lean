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
# Averaging an analytic function over a family of contractions

Let `f` have the power series `p` on the ball of radius `r` about `c`, and let `L t`, for
`t ∈ [0, 1]`, be a continuous family of continuous linear maps of norm at most one. Then the
average `z ↦ ∫ t in 0..1, f (c + L t (z - c))` has a power series on the same ball, whose `n`-th
coefficient is the average of `p n` precomposed with `L t` in every slot
(`HasFPowerSeriesOnBall.intervalIntegral_comp`). In particular the average is analytic at `c`
(`AnalyticAt.intervalIntegral_comp`).

The typical use is the integral form of Hadamard's lemma: if `G (x, y)` vanishes on `y = y₀`, then
`G (x, y) = (y - y₀) • ∫ t in 0..1, ∂G/∂y (x, y₀ + t (y - y₀))`, and this lemma, applied with
`L t (x, y) = (x, t y)`, shows that the quotient is again analytic.
-/

public section

open Set MeasureTheory intervalIntegral
open scoped ENNReal NNReal Interval

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  [IsScalarTower ℝ 𝕜 F] [CompleteSpace F]

/-- If `f` has the power series `p` on the ball of radius `r` about `c`, and `L t` is a family of
continuous linear maps of norm at most one, continuous in `t ∈ [0, 1]`, then the average
`z ↦ ∫ t in 0..1, f (c + L t (z - c))` has on the same ball the power series whose `n`-th
coefficient is `∫ t in 0..1, p n ∘ (L t, …, L t)`. -/
theorem HasFPowerSeriesOnBall.intervalIntegral_comp {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {c : E} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p c r)
    {L : ℝ → E →L[𝕜] E} (hL : ContinuousOn L (Icc 0 1)) (hL1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖L t‖ ≤ 1) :
    HasFPowerSeriesOnBall (fun z ↦ ∫ t in (0 : ℝ)..1, f (c + L t (z - c)))
      (fun n ↦ ∫ t in (0 : ℝ)..1, (p n).compContinuousLinearMap fun _ ↦ L t) c r := by
  have hIoc : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  -- the coefficient family is continuous in `t`, hence integrable
  have hcont (n : ℕ) :
      ContinuousOn (fun t ↦ (p n).compContinuousLinearMap fun _ ↦ L t) (Icc 0 1) := by
    have := ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
      (fun _ : Fin n ↦ E) (fun _ ↦ E) F).cont.comp_continuousOn
        (continuousOn_pi.2 fun _ ↦ hL)).clm_apply (continuousOn_const (c := p n))
    simpa using this
  have hint (n : ℕ) : IntervalIntegrable
      (fun t ↦ (p n).compContinuousLinearMap fun _ ↦ L t) volume 0 1 :=
    (hcont n).intervalIntegrable_of_Icc zero_le_one
  have hnorm (n : ℕ) : ‖∫ t in (0 : ℝ)..1, (p n).compContinuousLinearMap fun _ ↦ L t‖ ≤ ‖p n‖ := by
    have h : ∀ t ∈ Ι (0 : ℝ) 1, ‖(p n).compContinuousLinearMap fun _ ↦ L t‖ ≤ ‖p n‖ := by
      intro t ht
      rw [hIoc] at ht
      refine ((p n).norm_compContinuousLinearMap_le _).trans <|
        mul_le_of_le_one_right (norm_nonneg _) <|
          Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ hL1 t (Ioc_subset_Icc_self ht)
    simpa using norm_integral_le_of_norm_le_const h
  refine ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le hnorm), hf.r_pos, fun {y} hy ↦ ?_⟩
  simp only [add_sub_cancel_left]
  have hy' : (‖y‖₊ : ℝ≥0∞) < p.radius := by
    simpa [edist_zero_right, enorm_eq_nnnorm] using lt_of_lt_of_le hy hf.r_le
  have happly (n : ℕ) : (∫ t in (0 : ℝ)..1, (p n).compContinuousLinearMap fun _ ↦ L t)
      (fun _ ↦ y) = ∫ t in (0 : ℝ)..1, p n fun _ ↦ L t y := by
    simpa using (((ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin n ↦ E) F
      fun _ ↦ y).restrictScalars ℝ).intervalIntegral_comp_comm (hint n)).symm
  simp only [happly]
  -- dominated convergence, with the summable bound `‖p n‖ * ‖y‖ ^ n`
  have hLy : ∀ t ∈ Ι (0 : ℝ) 1, ‖L t y‖ ≤ ‖y‖ := fun t ht ↦
    ((L t).le_of_opNorm_le (hL1 t (Ioc_subset_Icc_self (hIoc ▸ ht))) y).trans (by simp)
  refine hasSum_integral_of_dominated_convergence (F := fun n t ↦ p n fun _ ↦ L t y)
    (f := fun t ↦ f (c + L t y)) (fun n _ ↦ ‖p n‖ * ‖y‖ ^ n) (fun n ↦ ?_)
    (fun n ↦ Filter.Eventually.of_forall fun t ht ↦ ?_)
    (Filter.Eventually.of_forall fun _ _ ↦ by simpa using p.summable_norm_mul_pow hy')
    intervalIntegrable_const (Filter.Eventually.of_forall fun t ht ↦ ?_)
  · rw [hIoc]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact ((p n).cont.comp_continuousOn (continuousOn_pi.2 fun _ ↦
      hL.clm_apply continuousOn_const)).mono Ioc_subset_Icc_self
  · refine ((p n).le_opNorm _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hLy t ht) n)
      (norm_nonneg (p n))
  · refine hf.hasSum ?_
    simp only [Metric.mem_eball, edist_zero_right] at hy ⊢
    exact lt_of_le_of_lt (by simpa [enorm_eq_nnnorm, ← NNReal.coe_le_coe] using hLy t ht) hy

/-- The average `z ↦ ∫ t in 0..1, f (c + L t (z - c))` of a function analytic at `c`, over a
family of continuous linear maps of norm at most one, continuous in `t ∈ [0, 1]`, is analytic
at `c`. -/
theorem AnalyticAt.intervalIntegral_comp {f : E → F} {c : E} (hf : AnalyticAt 𝕜 f c)
    {L : ℝ → E →L[𝕜] E} (hL : ContinuousOn L (Icc 0 1)) (hL1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖L t‖ ≤ 1) :
    AnalyticAt 𝕜 (fun z ↦ ∫ t in (0 : ℝ)..1, f (c + L t (z - c))) c := by
  obtain ⟨p, r, hp⟩ := hf
  exact (hp.intervalIntegral_comp hL hL1).analyticAt
