/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
import TauCeti.Analysis.BoundedVariation.Poincare

/-!
# Sets of zero weighted perimeter

For a `C¹` weight `W` on a finite-dimensional real inner product space `E`, a set of zero
weighted perimeter `P_μ(s) = 0` is null or conull
(`TauCeti.volume_eq_zero_or_volume_compl_eq_zero_of_weightedPerimeter_eq_zero`). On every ball `B(0, r)` the weight `e^{−W}` is bounded below by a
positive constant, so the Euclidean variation of `χ_s` on `B(0, r)` vanishes; by the Poincaré
inequality on the convex set `B(0, r)`, `χ_s` is almost everywhere equal on `B(0, r)` to its mean
over `B(0, 1)`, a constant independent of `r`.
-/

public section

noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {s : Set E}

/-- The open ball `B(0, r)` as an open set. -/
private def ballOpens (r : ℝ) : Opens E := ⟨ball 0 r, isOpen_ball⟩

/-- For a `C¹` weight, a measurable set of zero weighted perimeter has indicator almost
everywhere equal to a constant. -/
private theorem indicator_ae_eq_const_of_weightedPerimeter_eq_zero
    (hW : ContDiff ℝ 1 W) (hs : MeasurableSet s) (h0 : weightedPerimeter W ⊤ s = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂(volume : Measure E), s.indicator 1 x = c := by
  set c : ℝ := ⨍ y in ball (0 : E) 1, s.indicator (1 : E → ℝ) y
  have hu : LocallyIntegrable (s.indicator (1 : E → ℝ)) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hs
  have hball : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure E).restrict (ball 0 (n + 1)),
      s.indicator 1 x = c := by
    intro n
    -- `e^{−W}` has a positive lower bound on `closedBall 0 (n + 1)`.
    obtain ⟨m, hm, hmW⟩ := (isCompact_closedBall (0 : E) (n + 1)).exists_forall_le'
      (hW.continuous.neg.rexp).continuousOn fun x _ => Real.exp_pos (-W x)
    have hTV : totalVariationOn volume (ballOpens (n + 1)) (s.indicator 1) = 0 := by
      have hle := (mul_totalVariationOn_le_weightedVariation (m := m.toNNReal) hW
        (Ω := ballOpens (n + 1)) (hu.locallyIntegrableOn _) fun x hx => by
          rw [Real.coe_toNNReal _ hm.le]
          exact hmW x (ball_subset_closedBall hx)).trans (weightedVariation_mono le_top)
      rw [← weightedPerimeter_def, h0, nonpos_iff_eq_zero, mul_eq_zero] at hle
      have hm' : (m.toNNReal : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 (Real.toNNReal_pos.2 hm).ne'
      exact hle.resolve_left hm'
    exact ae_eq_setAverage_of_totalVariationOn_eq_zero (convex_ball 0 _) (hu.locallyIntegrableOn _)
      (ball_subset_ball (by linarith [n.cast_nonneg (α := ℝ)]))
      (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne hTV
  refine ⟨c, ?_⟩
  have hU : (⋃ n : ℕ, ball (0 : E) (n + 1)) = univ :=
    eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌈‖x‖⌉₊, mem_ball_zero_iff.2
      ((Nat.le_ceil _).trans_lt (lt_add_one _))⟩
  have := (ae_restrict_iUnion_iff _ _).2 hball
  rwa [hU, Measure.restrict_univ] at this

/-- **Sets of zero weighted perimeter are null or conull.** For a `C¹` weight `W`, a null
measurable set `s` with `P_μ(s) = 0` has `volume s = 0` or `volume sᶜ = 0`. -/
theorem volume_eq_zero_or_volume_compl_eq_zero_of_weightedPerimeter_eq_zero
    (hW : ContDiff ℝ 1 W) (hs : NullMeasurableSet s volume) (h0 : weightedPerimeter W ⊤ s = 0) :
    volume s = 0 ∨ volume sᶜ = 0 := by
  obtain ⟨t, -, ht, hst⟩ := hs.exists_measurable_subset_ae_eq
  have hst' : s =ᵐ[volume] t := hst.symm
  rw [weightedPerimeter_congr_ae (by simpa using hst')] at h0
  obtain ⟨c, hc⟩ := indicator_ae_eq_const_of_weightedPerimeter_eq_zero hW ht h0
  rw [measure_congr hst', measure_congr hst'.compl]
  by_cases h1 : c = 1
  · right
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hc] with x hx hxt
    rw [indicator_of_notMem hxt] at hx
    exact zero_ne_one (hx.trans h1)
  · left
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hc] with x hx hxt
    rw [indicator_of_mem hxt, Pi.one_apply] at hx
    exact h1 hx.symm

end TauCeti
