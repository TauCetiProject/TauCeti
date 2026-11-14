/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.HittingTime
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Probability.Process.Stopping
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Probability.BrownianMotion.LevelHit
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.BrownianMotion.Version
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Process.HittingTime
import TauCeti.Probability.Process.Stopping

/-!
# One-dimensional Brownian exit from bounded open intervals

For a real Brownian motion `B`, `x : ℝ`, and `τ := hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0`,
immediate boundary crossing and bounded optional sampling of `W` and `W² - t` give:
* `ProbabilityTheory.IsBrownianReal.hittingAfter_compl_Icc_ae_eq_compl_Ioo`: exit times from
  `[a, b]` and `(a, b)` agree almost surely.
* `ProbabilityTheory.IsBrownianReal.ae_eval_hittingAfter_compl_Ioo_eq_or_eq` and
  `measureReal_eval_hittingAfter_compl_Ioo_eq_{right,left}`: for `a < b` and `x ∈ [a, b]`,
  `x + B (τ ω).untopA ω ∈ {a, b}` a.s. with exit probabilities `(x - a) / (b - a)` and
  `(b - x) / (b - a)`.
* `ProbabilityTheory.IsBrownianReal.integrable_hittingAfter_compl_Ioo` and
  `integral_hittingAfter_compl_Ioo`: `E[(τ ω).untopA] = max 0 ((x - a) * (b - x))` for `a ≤ b`.

## References
* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., §2.8.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Pointwise

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

private theorem ae_intervalExit_ne_top (hW : IsBrownianReal W P) (x a b : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω ≠ ⊤ :=
  hW.ae_hittingAfter_compl_ne_top x fun h ↦ (h ▸ mem_univ a : a ∈ Ioo a b).1.false

private theorem isStoppingTime_intervalExit (hWm : ∀ t, StronglyMeasurable (W t))
    (hWc : ∀ ω, Continuous (W · ω)) (x a b : ℝ) :
    IsStoppingTime (Filtration.natural W hWm)
      (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) := by
  rw [hittingAfter_comp (x + ·), preimage_compl, preimage_const_add_Ioo]
  exact (Filtration.stronglyAdapted_natural hWm).adapted.isStoppingTime_hittingAfter_compl_of_isOpen
    hWc isOpen_Ioo 0

private theorem measurable_intervalExit (hWm : ∀ t, StronglyMeasurable (W t))
    (hWc : ∀ ω, Continuous (W · ω)) (x a b : ℝ) :
    Measurable (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) :=
  measurable_hittingAfter_of_isClosed (fun t ↦ (measurable_const_add x).comp (hWm t).measurable)
    (fun ω ↦ (continuous_const_add x).comp (hWc ω)) isOpen_Ioo.isClosed_compl 0

private theorem norm_stoppedProcess_le_of_mem_Icc (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) (T : ℝ≥0) (ω : Ω) :
    ‖stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω‖ ≤
      max |a - x| |b - x| := by
  have hmem : stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω ∈
      Icc (a - x) (b - x) := stoppedProcess_mem (fun u hu ↦ by
    have hY := ((continuous_const_add x).comp (hWc ω)).mem_Icc_of_le_hittingAfter_compl_Ioo
      (X := fun t ω ↦ x + W t ω) zero_le (by simpa only [hW0 ω, add_zero] using hx) hu
    exact ⟨by linarith [hY.1], by linarith [hY.2]⟩) T
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [neg_abs_le (a - x), le_max_left |a - x| |b - x|, hmem.1],
    by linarith [le_abs_self (b - x), le_max_right |a - x| |b - x|, hmem.2]⟩

private theorem sq_stoppedProcess_le_of_mem_Icc (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) (T : ℝ≥0) (ω : Ω) :
    stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω ^ 2 ≤
      max |a - x| |b - x| ^ 2 := by
  have hn := norm_stoppedProcess_le_of_mem_Icc hWc hW0 hx T ω; rw [Real.norm_eq_abs] at hn
  exact sq_le_sq.mpr (by rwa [abs_of_nonneg (le_max_of_le_left (abs_nonneg _))])

private theorem norm_stoppedValue_le_of_mem_Icc (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b)
    {ω : Ω} (hfin : hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω ≠ ⊤) :
    ‖stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) ω‖ ≤ max |a - x| |b - x| := by
  cases hτ : hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω with
  | top => exact absurd hτ hfin
  | coe s => simpa only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, hτ, min_self] using
      norm_stoppedProcess_le_of_mem_Icc hWc hW0 hx s ω

private theorem martingale_stoppedProcess_intervalExit (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω)) (x a b : ℝ) :
    Martingale (stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0))
      (Filtration.natural W hWm) P :=
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  (hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm).martingale
    |>.stoppedProcess_of_continuous hWc (isStoppingTime_intervalExit hWm hWc x a b)

private theorem integral_min_intervalExit_eq_integral_sq (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) (x a b : ℝ) (T : ℝ≥0) :
    ∫ ω, ((min (T : WithTop ℝ≥0)
        (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω)).untopA : ℝ) ∂P =
      ∫ ω, stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω ^ 2 ∂P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  let M : ℝ≥0 → Ω → ℝ := fun t ω ↦ W t ω ^ 2 - (t : ℝ)
  have hWF := hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm
  have hτ := isStoppingTime_intervalExit hWm hWc x a b
  have hMc (ω : Ω) : Continuous (M · ω) := ((hWc ω).pow 2).sub NNReal.continuous_coe
  rw [show (fun ω ↦ stoppedProcess W τ T ω ^ 2) = fun ω ↦ stoppedProcess M τ T ω +
        ((min (T : WithTop ℝ≥0) (τ ω)).untopA : ℝ) from funext fun _ ↦ by
          simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, M]; ring,
    integral_add ((hWF.martingale_sq_sub.stoppedProcess_of_continuous hMc hτ).integrable T)
      (integrable_untopA_const_min (measurable_intervalExit hWm hWc x a b).aemeasurable T),
    hWF.martingale_sq_sub.integral_stoppedProcess_eq_zero_of_ae_continuous (.of_forall hMc)
      (.of_forall fun ω ↦ by simp [hW0 ω]) hτ T, zero_add]

private theorem integral_stoppedValue_intervalExit_eq_zero (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    ∫ ω, stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) ω ∂P = 0 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  have hstop := martingale_stoppedProcess_intervalExit hW hWm hWc x a b
  refine tendsto_nhds_unique (tendsto_integral_of_dominated_convergence (f := stoppedValue W τ)
    (fun _ ↦ max |a - x| |b - x|) (fun n : ℕ ↦ (hstop.integrable (n : ℝ≥0)).aestronglyMeasurable)
    (integrable_const _)
    (fun n ↦ .of_forall (norm_stoppedProcess_le_of_mem_Icc hWc hW0 hx (n : ℝ≥0)))
    ((ae_intervalExit_ne_top hW x a b).mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((WithTop.eventually_min_natCast_eq hfin).mono fun _ hn ↦ by
        simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, τ, hn])))
    ((tendsto_const_nhds (x := (0 : ℝ))).congr fun n ↦
      ((hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm).martingale
        |>.integral_stoppedProcess_eq_zero_of_ae_continuous (.of_forall hWc) (.of_forall hW0)
        (isStoppingTime_intervalExit hWm hWc x a b) (n : ℝ≥0)).symm)

private theorem integrable_intervalExit_of_mem_Icc (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    Integrable (fun ω ↦ ((hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ)) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  let C : ℝ := max |a - x| |b - x|
  have hτ_meas := measurable_intervalExit hWm hWc x a b
  let u (n : ℕ) : Ω → ℝ := fun ω ↦ ((min ((n : ℝ≥0) : WithTop ℝ≥0) (τ ω)).untopA : ℝ)
  have hlin_tend := lintegral_tendsto_of_tendsto_of_monotone
    (f := fun n ω ↦ ENNReal.ofReal (u n ω)) (F := fun ω ↦ ENNReal.ofReal ((τ ω).untopA : ℝ))
    (fun _ ↦ ((measurable_subtype_coe.comp
      (measurable_const.min hτ_meas).untopA).ennreal_ofReal).aemeasurable)
    (.of_forall fun ω _ _ hmn ↦
      ENNReal.ofReal_le_ofReal (NNReal.coe_le_coe.mpr ((τ ω).monotone_untopA_min_natCast hmn)))
    ((ae_intervalExit_ne_top hW x a b).mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((WithTop.eventually_min_natCast_eq hfin).mono fun _ hn ↦ by dsimp only [u, τ]; rw [hn]))
  have hstop := martingale_stoppedProcess_intervalExit hW hWm hWc x a b
  have hlin_le (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (u n ω) ∂P ≤ ENNReal.ofReal (C ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_untopA_const_min hτ_meas.aemeasurable
        (n : ℝ≥0)) (.of_forall fun _ ↦ NNReal.coe_nonneg _),
      integral_min_intervalExit_eq_integral_sq hW hWm hWc hW0 x a b (n : ℝ≥0)]
    have hsq_le := sq_stoppedProcess_le_of_mem_Icc hWc hW0 hx (n : ℝ≥0)
    exact ENNReal.ofReal_le_ofReal <| by
      simpa only [Pi.pow_apply, integral_const, probReal_univ, one_smul] using integral_mono
        (Integrable.of_bound ((hstop.integrable (n : ℝ≥0)).aestronglyMeasurable.pow 2) (C ^ 2)
          (.of_forall fun ω ↦ by
            rw [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq_le ω))
        (integrable_const (C ^ 2)) hsq_le
  refine ⟨(measurable_subtype_coe.comp hτ_meas.untopA).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_congr fun _ ↦ Real.eNorm_eq_ofReal (NNReal.coe_nonneg _)]
  exact (le_of_tendsto hlin_tend (.of_forall hlin_le)).trans_lt ENNReal.ofReal_lt_top

private theorem measurable_stoppedValue_intervalExit (hWm : ∀ t, StronglyMeasurable (W t))
    (hWc : ∀ ω, Continuous (W · ω)) (x a b : ℝ) :
    Measurable (stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0)) :=
  have hτ := isStoppingTime_intervalExit hWm hWc x a b
  (measurable_stoppedValue
    ((Filtration.stronglyAdapted_natural hWm).isStronglyProgressive_of_continuous hWc) hτ).mono
    hτ.measurableSpace_le le_rfl

private theorem integrable_stoppedValue_intervalExit (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    Integrable (stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0)) P :=
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  .of_bound (measurable_stoppedValue_intervalExit hWm hWc x a b).aestronglyMeasurable
    (max |a - x| |b - x|) ((ae_intervalExit_ne_top hW x a b).mono fun _ ↦
      norm_stoppedValue_le_of_mem_Icc hWc hW0 hx)

private theorem integral_intervalExit_eq_of_mem_Icc (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    ∫ ω, ((hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P =
      (x - a) * (b - x) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  have hτ_meas := measurable_intervalExit hWm hWc x a b
  have hfin_ae := ae_intervalExit_ne_top hW x a b
  have hlim_u := integral_tendsto_of_tendsto_of_monotone
    (fun n ↦ integrable_untopA_const_min hτ_meas.aemeasurable (n : ℝ≥0))
    (integrable_intervalExit_of_mem_Icc hW hWm hWc hW0 hx)
    (.of_forall fun ω ↦ NNReal.coe_mono.comp (τ ω).monotone_untopA_min_natCast)
    (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((WithTop.eventually_min_natCast_eq hfin).mono fun _ hn ↦ by rw [hn]))
  have hstop := martingale_stoppedProcess_intervalExit hW hWm hWc x a b
  have hlim_sq := tendsto_integral_of_dominated_convergence
    (F := fun n ω ↦ stoppedProcess W τ (n : ℝ≥0) ω ^ 2) (f := fun ω ↦ stoppedValue W τ ω ^ 2)
    (fun _ ↦ max |a - x| |b - x| ^ 2)
    (fun n : ℕ ↦ (hstop.integrable (n : ℝ≥0)).aestronglyMeasurable.pow 2) (integrable_const _)
    (fun n ↦ .of_forall fun ω ↦ (Real.norm_of_nonneg (sq_nonneg _)).trans_le
      (sq_stoppedProcess_le_of_mem_Icc hWc hW0 hx (n : ℝ≥0) ω))
    (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((WithTop.eventually_min_natCast_eq hfin).mono fun _ hn ↦ by
        simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, τ, hn]))
  have hpoly : (fun ω ↦ stoppedValue W τ ω ^ 2) =ᵐ[P]
      fun ω ↦ (x - a) * (b - x) + (a + b - 2 * x) * stoppedValue W τ ω :=
    hfin_ae.mono fun ω hfin ↦ by
      have hdich := ((continuous_const_add x).comp (hWc ω))
        |>.eval_untopA_hittingAfter_compl_Ioo_eq_or_eq (X := fun t ω ↦ x + W t ω)
          (by simpa only [hW0 ω, add_zero] using hx) hfin
      have hz : (x + stoppedValue W τ ω - a) * (b - (x + stoppedValue W τ ω)) = 0 := by
        rcases hdich with h | h <;> (dsimp only [stoppedValue, τ]; rw [h]; ring)
      linarith [show stoppedValue W τ ω ^ 2 = (x - a) * (b - x) + (a + b - 2 * x) *
        stoppedValue W τ ω - (x + stoppedValue W τ ω - a) * (b - (x + stoppedValue W τ ω)) by ring]
  rw [tendsto_nhds_unique hlim_u (hlim_sq.congr fun n ↦
      (integral_min_intervalExit_eq_integral_sq hW hWm hWc hW0 x a b (n : ℝ≥0)).symm),
    integral_congr_ae hpoly, integral_add (integrable_const _)
      ((integrable_stoppedValue_intervalExit hW hWm hWc hW0 hx).const_mul _)]
  simp [integral_const_mul, integral_stoppedValue_intervalExit_eq_zero hW hWm hWc hW0 hx]

end TauCeti.Probability

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A real Brownian motion started at `x` exits every open interval `(a, b)` in finite time almost
surely. -/
theorem ae_hittingAfter_compl_Ioo_ne_top (hB : IsBrownianReal B P) (x a b : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω ≠ ⊤ :=
  ae_intervalExit_ne_top hB x a b

/-- **Open- versus closed-interval exit for Brownian motion**: for all `x, a, b : ℝ`, the first
exit time of `x + B` from `[a, b]` agrees almost surely with its first exit time from `(a, b)`. -/
theorem hittingAfter_compl_Icc_ae_eq_compl_Ioo (hB : IsBrownianReal B P) (x a b : ℝ) :
    hittingAfter (fun t ω ↦ x + B t ω) (Icc a b)ᶜ 0 =ᵐ[P]
      hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 := by
  have hc₁ : (Icc a b)ᶜ = Iio a ∪ Ioi b := by
    ext; simp only [mem_compl_iff, mem_Icc, not_and_or, not_le]; rfl
  have hc₂ : (Ioo a b)ᶜ = Iic a ∪ Ici b := by
    ext; simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt]; rfl
  rw [hc₁, hc₂, hittingAfter_union, hittingAfter_union, hittingAfter_comp (x + ·),
    hittingAfter_comp (x + ·), hittingAfter_comp (x + ·), hittingAfter_comp (x + ·),
    preimage_const_add_Iio, preimage_const_add_Ioi, preimage_const_add_Iic, preimage_const_add_Ici]
  exact ((hB.hittingAfter_Iio_ae_eq_Iic (a - x)).and (hB.hittingAfter_Ioi_ae_eq_Ici (b - x))).mono
    fun _ ⟨h₁, h₂⟩ ↦ congrArg₂ min h₁ h₂

/-- When `x ∉ (a, b)`, the first exit time of `x + B` from `(a, b)` is almost surely `0`. -/
theorem hittingAfter_compl_Ioo_ae_eq_zero_of_notMem (hB : IsBrownianReal B P) {x a b : ℝ}
    (hx : x ∉ Ioo a b) : hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 =ᵐ[P] 0 := by
  obtain ⟨W, _, _, hW0, _, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  exact ((hWB.symm.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0).trans (.of_forall fun ω ↦
    le_antisymm (hittingAfter_le_of_mem le_rfl
      (by simpa only [hW0 ω, add_zero, mem_compl_iff] using hx)) bot_le)

/-- Starting from `x ∈ [a, b]`, the position of `x + B` at its first exit from `(a, b)` equals
either `a` or `b` almost surely. -/
theorem ae_eval_hittingAfter_compl_Ioo_eq_or_eq (hB : IsBrownianReal B P) {x a b : ℝ}
    (hx : x ∈ Icc a b) :
    ∀ᵐ ω ∂P, x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a ∨
      x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b := by
  obtain ⟨W, _, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  filter_upwards [hWB, (hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0,
    hW.ae_hittingAfter_compl_Ioo_ne_top x a b] with ω hω hτ hfin
  rw [← hτ, ← hω]
  exact ((continuous_const_add x).comp (hWc ω)).eval_untopA_hittingAfter_compl_Ioo_eq_or_eq
    (X := fun t ω ↦ x + W t ω) (by simpa only [hW0 ω, add_zero] using hx) hfin

/-- **Brownian gambler's ruin (upper exit probability)**: for `a < b` and `x ∈ [a, b]`, the
probability that `x + B` exits `(a, b)` through `b` equals `(x - a) / (b - a)`. -/
theorem measureReal_eval_hittingAfter_compl_Ioo_eq_right (hB : IsBrownianReal B P)
    {x a b : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    P.real {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b} =
      (x - a) / (b - a) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  let Z : Ω → ℝ := fun ω ↦ x + stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) ω
  have hZ_meas : Measurable Z :=
    (measurable_const_add x).comp (measurable_stoppedValue_intervalExit hWm hWc x a b)
  have hset_ae : {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b}
      =ᵐ[P] Z ⁻¹' {b} := by
    filter_upwards [hWB, (hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0] with _ hω hτ
    simp only [mem_preimage, mem_singleton_iff, Z, stoppedValue, ← hτ, hω]
  have hind_eq : (fun ω ↦ Z ω - a) =ᵐ[P] fun ω ↦ (b - a) * (Z ⁻¹' {b}).indicator 1 ω := by
    filter_upwards [hW.ae_eval_hittingAfter_compl_Ioo_eq_or_eq hx] with ω hω
    rcases hω with hZa | hZb
    · rw [indicator_of_notMem (fun h ↦ hab.ne (hZa.symm.trans h)), mul_zero]
      exact sub_eq_zero.mpr hZa
    · rw [indicator_of_mem hZb, Pi.one_apply, mul_one]; exact congrArg (· - a) hZb
  have hint := integral_congr_ae hind_eq
  have hlhs : ∫ ω, (Z ω - a) ∂P = x - a := by
    rw [show (fun ω ↦ Z ω - a) = fun ω ↦ (x - a) + stoppedValue W _ ω by ext; simp [Z]; ring,
      integral_add (integrable_const _) (integrable_stoppedValue_intervalExit hW hWm hWc hW0 hx)]
    simp [integral_stoppedValue_intervalExit_eq_zero hW hWm hWc hW0 hx]
  rw [integral_const_mul, integral_indicator_one (hZ_meas (measurableSet_singleton b)),
    hlhs] at hint
  rw [measureReal_congr hset_ae, eq_div_iff (sub_ne_zero.mpr hab.ne'), mul_comm]; linarith

/-- `ℝ≥0∞`-valued upper exit probability for Brownian motion on `(a, b)`. -/
theorem measure_eval_hittingAfter_compl_Ioo_eq_right (hB : IsBrownianReal B P)
    {x a b : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    P {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b} =
      ENNReal.ofReal ((x - a) / (b - a)) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _), ← measureReal_def,
    hB.measureReal_eval_hittingAfter_compl_Ioo_eq_right hab hx]

/-- **Brownian gambler's ruin (lower exit probability)**: for `a < b` and `x ∈ [a, b]`, the
probability that `x + B` exits `(a, b)` through `a` equals `(b - x) / (b - a)`. -/
theorem measureReal_eval_hittingAfter_compl_Ioo_eq_left (hB : IsBrownianReal B P)
    {x a b : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    P.real {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a} =
      (b - x) / (b - a) := by
  have hneg := hB.neg.measureReal_eval_hittingAfter_compl_Ioo_eq_right (neg_lt_neg hab)
    ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
  have hτ : hittingAfter (fun t ω ↦ -x + (-B) t ω) (Ioo (-b) (-a))ᶜ 0 =
      hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 := by
    rw [show (fun t ω ↦ -x + (-B) t ω) = -(fun t ω ↦ x + B t ω) by ext; simp [add_comm],
      hittingAfter_neg, Set.neg_preimage, Set.compl_neg, Set.neg_Ioo, neg_neg, neg_neg]
  rw [show {ω | -x + (-B) (hittingAfter (fun t ω ↦ -x + (-B) t ω) (Ioo (-b) (-a))ᶜ 0 ω).untopA ω
      = -a} = {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a} by
    ext ω; rw [mem_ofPred_eq, mem_ofPred_eq, hτ, Pi.neg_apply, Pi.neg_apply]
    exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩] at hneg
  exact hneg.trans (by ring)

/-- `ℝ≥0∞`-valued lower exit probability for Brownian motion on `(a, b)`. -/
theorem measure_eval_hittingAfter_compl_Ioo_eq_left (hB : IsBrownianReal B P)
    {x a b : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    P {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a} =
      ENNReal.ofReal ((b - x) / (b - a)) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _), ← measureReal_def,
    hB.measureReal_eval_hittingAfter_compl_Ioo_eq_left hab hx]

/-- The first exit time `(hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA` of `x + B`
from any open interval `(a, b)` is integrable. -/
theorem integrable_hittingAfter_compl_Ioo (hB : IsBrownianReal B P) (x a b : ℝ) :
    Integrable (fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ)) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  by_cases hx : x ∈ Ioo a b
  · obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
    exact (integrable_intervalExit_of_mem_Icc hW hWm hWc hW0 (Ioo_subset_Icc_self hx)).congr
      (((hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0).mono fun _ hω ↦ by simp only [hω])
  · exact (integrable_zero Ω ℝ P).congr
      ((hB.hittingAfter_compl_Ioo_ae_eq_zero_of_notMem hx).mono fun _ hω ↦ by simp [hω])

/-- **Mean exit time of Brownian motion from `(a, b)`**: for `a ≤ b` and all `x : ℝ`,
`∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P =`
`max 0 ((x - a) * (b - x))`. -/
theorem integral_hittingAfter_compl_Ioo (hB : IsBrownianReal B P) (x : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P =
      max 0 ((x - a) * (b - x)) := by
  by_cases hx : x ∈ Ioo a b
  · obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
    rw [integral_congr_ae (((hWB.symm.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0).mono
        fun _ hω ↦ congrArg (fun q : WithTop ℝ≥0 ↦ (q.untopA : ℝ)) hω),
      integral_intervalExit_eq_of_mem_Icc hW hWm hWc hW0 (Ioo_subset_Icc_self hx),
      max_eq_right (mul_nonneg (sub_nonneg.mpr hx.1.le) (sub_nonneg.mpr hx.2.le))]
  · have hnonpos : (x - a) * (b - x) ≤ 0 := (le_or_gt x a).elim
      (fun h ↦ mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (sub_nonneg.mpr (h.trans hab)))
      (fun h ↦ mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h.le)
        (sub_nonpos.mpr (not_lt.mp fun hxb ↦ hx ⟨h, hxb⟩)))
    rw [integral_congr_ae (g := fun _ ↦ (0 : ℝ))
      ((hB.hittingAfter_compl_Ioo_ae_eq_zero_of_notMem hx).mono fun _ hω ↦ by simp [hω]),
      integral_zero, max_eq_left hnonpos]

/-- **Mean exit time of Brownian motion from `(-K, K)`**: for `K ≥ 0` and all `x : ℝ`,
`∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo (-K) K)ᶜ 0 ω).untopA : ℝ) ∂P =`
`max 0 (K ^ 2 - x ^ 2)`. -/
theorem integral_hittingAfter_compl_Ioo_neg (hB : IsBrownianReal B P) (x : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo (-K) K)ᶜ 0 ω).untopA : ℝ) ∂P =
      max 0 (K ^ 2 - x ^ 2) := by
  rw [hB.integral_hittingAfter_compl_Ioo x (neg_le_self hK)]; congr 1; ring

end ProbabilityTheory.IsBrownianReal
