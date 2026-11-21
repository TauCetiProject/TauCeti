/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.HittingTime
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Order.WithBot
import TauCeti.Probability.BrownianMotion.LevelHit
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.BrownianMotion.Version
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Process.HittingTime
import TauCeti.Probability.Process.StoppedValue
import TauCeti.Probability.Process.Stopping

/-!
# One-dimensional Brownian exit from bounded open intervals

This file solves the one-dimensional Dirichlet exit-probability and Poisson mean exit-time problems
on bounded open intervals `(a, b)` directly for native `ProbabilityTheory.IsBrownianReal`
(unwrapping finite exit times via `WithTop.untopA`, without filtration or completeness hypotheses).
For `B` a real Brownian motion, `x : ℝ`, and `τ := hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0`:
* `ProbabilityTheory.IsBrownianReal.hittingAfter_compl_Icc_ae_eq_compl_Ioo`: exit times from
  `[a, b]` and `(a, b)` agree almost surely.
* `ProbabilityTheory.IsBrownianReal.aemeasurable_eval_hittingAfter_compl_Ioo`,
  `ae_eval_hittingAfter_compl_Ioo_eq_or_eq`,
  `measureReal_eval_hittingAfter_compl_Ioo_eq_{right,left}`, and
  `hasLaw_eval_hittingAfter_compl_Ioo`: for `a < b` and `x ∈ [a, b]`, `x + B (τ ω).untopA ω` has law
  `((b - x) / (b - a)) • δ_a + ((x - a) / (b - a)) • δ_b`.
* `ProbabilityTheory.IsBrownianReal.integrable_hittingAfter_compl_Ioo` and
  `integral_hittingAfter_compl_Ioo`: `E[(τ ω).untopA] = max 0 ((x - a) * (b - x))` for `a ≤ b`.

## References
* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., §2.8.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Pointwise

/-- A real Brownian motion started at `x` exits every open interval `(a, b)` in finite time almost
surely. -/
theorem ProbabilityTheory.IsBrownianReal.ae_hittingAfter_compl_Ioo_ne_top {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (x a b : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω ≠ ⊤ :=
  hB.ae_hittingAfter_compl_ne_top x fun h ↦ (h ▸ mem_univ a : a ∈ Ioo a b).1.false

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  (hW : IsBrownianReal W P) (hWm : ∀ t, StronglyMeasurable (W t))
  (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)

include hW hWm hWc in
private theorem martingale_stoppedProcess_intervalExit (a b : ℝ) :
    Martingale (stoppedProcess W (hittingAfter W (Ioo a b)ᶜ 0)) (Filtration.natural W hWm) P :=
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  (hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm).martingale
    |>.stoppedProcess_of_continuous hWc
      ((Filtration.stronglyAdapted_natural hWm).adapted.isStoppingTime_hittingAfter_compl_of_isOpen
        hWc isOpen_Ioo 0)

section
include hW hWm hWc hW0

private theorem integral_min_intervalExit_eq_integral_sq (a b : ℝ) (T : ℝ≥0) :
    ∫ ω, ((min (T : WithTop ℝ≥0) (hittingAfter W (Ioo a b)ᶜ 0 ω)).untopA : ℝ) ∂P =
      ∫ ω, stoppedProcess W (hittingAfter W (Ioo a b)ᶜ 0) T ω ^ 2 ∂P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter W (Ioo a b)ᶜ 0; let M : ℝ≥0 → Ω → ℝ := fun t ω ↦ W t ω ^ 2 - (t : ℝ)
  have hWF := hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm
  have hτ : IsStoppingTime (Filtration.natural W hWm) τ :=
    (Filtration.stronglyAdapted_natural hWm).adapted.isStoppingTime_hittingAfter_compl_of_isOpen
      hWc isOpen_Ioo 0
  have hMc (ω : Ω) : Continuous (M · ω) := ((hWc ω).pow 2).sub NNReal.continuous_coe
  have hsq : (fun ω ↦ stoppedProcess W τ T ω ^ 2) = fun ω ↦ stoppedProcess M τ T ω +
      ((min (T : WithTop ℝ≥0) (τ ω)).untopA : ℝ) := funext fun _ ↦ by
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, M]; ring
  rw [hsq, integral_add ((hWF.martingale_sq_sub.stoppedProcess_of_continuous hMc hτ).integrable T)
      (integrable_untopA_const_min hτ.measurable'.aemeasurable T),
    hWF.martingale_sq_sub.integral_stoppedProcess_eq_zero_of_ae_continuous (.of_forall hMc)
      (.of_forall fun ω ↦ by simp [hW0 ω]) hτ T, zero_add]

private theorem integral_stoppedValue_intervalExit_eq_zero {a b : ℝ} (h0 : (0 : ℝ) ∈ Icc a b) :
    ∫ ω, stoppedValue W (hittingAfter W (Ioo a b)ᶜ 0) ω ∂P = 0 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter W (Ioo a b)ᶜ 0
  have hτ : IsStoppingTime (Filtration.natural W hWm) τ :=
    (Filtration.stronglyAdapted_natural hWm).adapted.isStoppingTime_hittingAfter_compl_of_isOpen
      hWc isOpen_Ioo 0
  have hfin_ae := hW.ae_hittingAfter_compl_Ioo_ne_top 0 a b; simp only [zero_add] at hfin_ae
  refine tendsto_nhds_unique (tendsto_integral_of_dominated_convergence (f := stoppedValue W τ)
    (fun _ ↦ max |a| |b|)
    (fun n : ℕ ↦ ((martingale_stoppedProcess_intervalExit hW hWm hWc a b).integrable
      (n : ℝ≥0)).aestronglyMeasurable)
    (integrable_const _) (fun n ↦ .of_forall fun ω ↦ by
      have hmem := (hWc ω).stoppedProcess_hittingAfter_compl_Ioo_mem_Icc
        (zero_le : (0 : ℝ≥0) ≤ n) (by simpa only [hW0 ω] using h0 : W 0 ω ∈ Icc a b)
      exact Real.norm_eq_abs _ ▸ abs_le_max_abs_abs hmem.1 hmem.2)
    (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((WithTop.eventually_min_natCast_eq hfin).mono fun _ hn ↦ by
        simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, τ, hn])))
    ((tendsto_const_nhds (x := (0 : ℝ))).congr fun n ↦
      ((hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm).martingale
        |>.integral_stoppedProcess_eq_zero_of_ae_continuous (.of_forall hWc) (.of_forall hW0)
        hτ (n : ℝ≥0)).symm)

private theorem integrable_intervalExit_of_mem_Icc {a b : ℝ} (h0 : (0 : ℝ) ∈ Icc a b) :
    Integrable (fun ω ↦ ((hittingAfter W (Ioo a b)ᶜ 0 ω).untopA : ℝ)) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter W (Ioo a b)ᶜ 0; let C : ℝ := max |a| |b|
  have hτ_meas : Measurable τ := measurable_hittingAfter_of_isClosed (fun t ↦ (hWm t).measurable)
    hWc isOpen_Ioo.isClosed_compl 0
  have hfin_ae := hW.ae_hittingAfter_compl_Ioo_ne_top 0 a b; simp only [zero_add] at hfin_ae
  let u (n : ℕ) : Ω → ℝ := fun ω ↦ ((min ((n : ℝ≥0) : WithTop ℝ≥0) (τ ω)).untopA : ℝ)
  have hlin_tend := lintegral_tendsto_of_tendsto_of_monotone
    (f := fun n ω ↦ ENNReal.ofReal (u n ω)) (F := fun ω ↦ ENNReal.ofReal ((τ ω).untopA : ℝ))
    (fun _ ↦ ((measurable_subtypeVal.comp
      (measurable_const.min hτ_meas).untopA).ennreal_ofReal).aemeasurable)
    (.of_forall fun ω _ _ hmn ↦ ENNReal.ofReal_le_ofReal
      (NNReal.coe_le_coe.mpr ((τ ω).monotone_untopA_min_coe (Nat.mono_cast hmn))))
    (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((WithTop.eventually_min_natCast_eq hfin).mono fun _ hn ↦ by dsimp only [u, τ]; rw [hn]))
  have hlin_le (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (u n ω) ∂P ≤ ENNReal.ofReal (C ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_untopA_const_min hτ_meas.aemeasurable
        (n : ℝ≥0)) (.of_forall fun _ ↦ NNReal.coe_nonneg _),
      integral_min_intervalExit_eq_integral_sq hW hWm hWc hW0 a b (n : ℝ≥0)]
    refine ENNReal.ofReal_le_ofReal <| (le_abs_self _).trans <| by
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := P) (f := fun ω ↦ stoppedProcess W τ (n : ℝ≥0) ω ^ 2)
          (C := C ^ 2) (.of_forall fun ω ↦ by
            have hmem := (hWc ω).stoppedProcess_hittingAfter_compl_Ioo_mem_Icc
              (zero_le : (0 : ℝ≥0) ≤ n) (by simpa only [hW0 ω] using h0 : W 0 ω ∈ Icc a b)
            rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_max_abs_abs hmem.1 hmem.2) 2)
  refine ⟨(measurable_subtypeVal.comp hτ_meas.untopA).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_congr fun _ ↦ Real.eNorm_eq_ofReal (NNReal.coe_nonneg _)]
  exact (le_of_tendsto hlin_tend (.of_forall hlin_le)).trans_lt ENNReal.ofReal_lt_top

private theorem integrable_stoppedValue_intervalExit {a b : ℝ} (h0 : (0 : ℝ) ∈ Icc a b) :
    Integrable (stoppedValue W (hittingAfter W (Ioo a b)ᶜ 0)) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hfin_ae := hW.ae_hittingAfter_compl_Ioo_ne_top 0 a b; simp only [zero_add] at hfin_ae
  refine .of_bound (stronglyMeasurable_stoppedValue_of_continuous hWm hWc
      (measurable_hittingAfter_of_isClosed (fun t ↦ (hWm t).measurable) hWc
        isOpen_Ioo.isClosed_compl 0)).aestronglyMeasurable (max |a| |b|)
    (hfin_ae.mono fun ω hfin ↦ ?_)
  rcases (hWc ω).eval_untopA_hittingAfter_compl_Ioo_eq_or_eq (by simpa only [hW0 ω] using h0) hfin
    with h | h <;> simp [stoppedValue, h]

private theorem integral_intervalExit_eq_of_mem_Icc {a b : ℝ} (h0 : (0 : ℝ) ∈ Icc a b) :
    ∫ ω, ((hittingAfter W (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P = -a * b := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter W (Ioo a b)ᶜ 0
  have hτ_meas : Measurable τ := measurable_hittingAfter_of_isClosed (fun t ↦ (hWm t).measurable)
    hWc isOpen_Ioo.isClosed_compl 0
  have hfin_ae := hW.ae_hittingAfter_compl_Ioo_ne_top 0 a b; simp only [zero_add] at hfin_ae
  have hlim_u := integral_tendsto_of_tendsto_of_monotone
    (fun n ↦ integrable_untopA_const_min hτ_meas.aemeasurable (n : ℝ≥0))
    (integrable_intervalExit_of_mem_Icc hW hWm hWc hW0 h0)
    (.of_forall fun ω ↦ NNReal.coe_mono.comp ((τ ω).monotone_untopA_min_coe.comp Nat.mono_cast))
    (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((WithTop.eventually_min_natCast_eq hfin).mono fun _ hn ↦ by rw [hn]))
  have hlim_sq := tendsto_integral_of_dominated_convergence
    (F := fun n ω ↦ stoppedProcess W τ (n : ℝ≥0) ω ^ 2) (f := fun ω ↦ stoppedValue W τ ω ^ 2)
    (fun _ ↦ max |a| |b| ^ 2)
    (fun n : ℕ ↦ ((martingale_stoppedProcess_intervalExit hW hWm hWc a b).integrable
      (n : ℝ≥0)).aestronglyMeasurable.pow 2) (integrable_const _)
    (fun n ↦ .of_forall fun ω ↦ by
      have hmem := (hWc ω).stoppedProcess_hittingAfter_compl_Ioo_mem_Icc
        (zero_le : (0 : ℝ≥0) ≤ n) (by simpa only [hW0 ω] using h0 : W 0 ω ∈ Icc a b)
      rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_max_abs_abs hmem.1 hmem.2) 2)
    (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((WithTop.eventually_min_natCast_eq hfin).mono fun _ hn ↦ by
        simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, τ, hn]))
  have hpoly : (fun ω ↦ stoppedValue W τ ω ^ 2) =ᵐ[P]
      fun ω ↦ -a * b + (a + b) * stoppedValue W τ ω := hfin_ae.mono fun ω hfin ↦ by
    rcases (hWc ω).eval_untopA_hittingAfter_compl_Ioo_eq_or_eq (by simpa only [hW0 ω] using h0) hfin
      with h | h <;> (dsimp only [stoppedValue, τ]; rw [h]; ring)
  rw [tendsto_nhds_unique hlim_u (hlim_sq.congr fun n ↦
      (integral_min_intervalExit_eq_integral_sq hW hWm hWc hW0 a b (n : ℝ≥0)).symm),
    integral_congr_ae hpoly, integral_add (integrable_const _)
      ((integrable_stoppedValue_intervalExit hW hWm hWc hW0 h0).const_mul _)]
  simp [integral_const_mul, integral_stoppedValue_intervalExit_eq_zero hW hWm hWc hW0 h0]

end
end TauCeti.Probability

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Open- versus closed-interval exit for Brownian motion**: for all `x, a, b : ℝ`, the first
exit time of `x + B` from `[a, b]` agrees almost surely with its first exit time from `(a, b)`. -/
theorem hittingAfter_compl_Icc_ae_eq_compl_Ioo (hB : IsBrownianReal B P) (x a b : ℝ) :
    hittingAfter (fun t ω ↦ x + B t ω) (Icc a b)ᶜ 0 =ᵐ[P]
      hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 := by
  rw [← Ici_inter_Iic, compl_inter, compl_Ici, compl_Iic, ← Ioi_inter_Iio, compl_inter, compl_Ioi,
    compl_Iio, hittingAfter_union, hittingAfter_union, hittingAfter_comp (f := (x + ·)),
    hittingAfter_comp (f := (x + ·)), hittingAfter_comp (f := (x + ·)),
    hittingAfter_comp (f := (x + ·)),
    preimage_const_add_Iio, preimage_const_add_Ioi, preimage_const_add_Iic, preimage_const_add_Ici]
  exact ((hB.hittingAfter_Iio_ae_eq_Iic (a - x)).and (hB.hittingAfter_Ioi_ae_eq_Ici (b - x))).mono
    fun _ ⟨h₁, h₂⟩ ↦ congrArg₂ min h₁ h₂

/-- When `x ∉ (a, b)`, the first exit time of `x + B` from `(a, b)` is almost surely `0`. -/
theorem hittingAfter_compl_Ioo_ae_eq_zero_of_notMem (hB : IsBrownianReal B P) {x a b : ℝ}
    (hx : x ∉ Ioo a b) : hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 =ᵐ[P] 0 := by
  obtain ⟨W, _, _, hW0, _, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  exact ((hWB.symm.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0).trans (.of_forall fun ω ↦
    le_antisymm (hittingAfter_le_of_mem le_rfl (by simpa [hW0 ω] using hx)) bot_le)

/-- Evaluating `B` at `(hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA` is almost
everywhere measurable, without assuming completeness of the ambient measurable space. -/
theorem aemeasurable_eval_hittingAfter_compl_Ioo (hB : IsBrownianReal B P) (x a b : ℝ) :
    AEMeasurable (fun ω ↦ B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω) P := by
  obtain ⟨W, hWm, hWc, _, _, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  have hτ_meas : Measurable (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) :=
    measurable_hittingAfter_of_isClosed (fun t ↦ (measurable_const_add x).comp (hWm t).measurable)
      (fun ω ↦ (continuous_const_add x).comp (hWc ω)) isOpen_Ioo.isClosed_compl 0
  exact (stronglyMeasurable_stoppedValue_of_continuous hWm hWc hτ_meas).measurable.aemeasurable
    |>.congr ((hWB.and ((hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0)).mono
      fun _ ⟨hω, hτ⟩ ↦ by simp only [stoppedValue, hτ, hω])

/-- Starting from `x ∈ [a, b]`, the position of `x + B` at its first exit from `(a, b)` equals
either `a` or `b` almost surely. -/
theorem ae_eval_hittingAfter_compl_Ioo_eq_or_eq (hB : IsBrownianReal B P) {x a b : ℝ}
    (hx : x ∈ Icc a b) : ∀ᵐ ω ∂P,
      x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a ∨
        x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b := by
  obtain ⟨W, _, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  filter_upwards [hWB, (hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0,
    hW.ae_hittingAfter_compl_Ioo_ne_top x a b] with ω hω hτ hfin
  rw [← hτ, ← hω]
  exact ((continuous_const_add x).comp (hWc ω)).eval_untopA_hittingAfter_compl_Ioo_eq_or_eq
    (X := fun t ω ↦ x + W t ω) (by simpa only [hW0 ω, add_zero] using hx) hfin

/-- **Brownian gambler's ruin (upper exit probability)**: for `a < b` and `x ∈ [a, b]`, the
probability that `x + B` exits `(a, b)` through `b` equals `(x - a) / (b - a)`. -/
theorem measureReal_eval_hittingAfter_compl_Ioo_eq_right (hB : IsBrownianReal B P) {x a b : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) :
    P.real {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b} =
      (x - a) / (b - a) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  have h0 : (0 : ℝ) ∈ Icc (a - x) (b - x) := ⟨sub_nonpos.mpr hx.1, sub_nonneg.mpr hx.2⟩
  have hτ_eq := (hittingAfter_comp W (x + ·) (Ioo a b)ᶜ 0).trans <| by
    rw [preimage_compl, preimage_const_add_Ioo]
  let Z : Ω → ℝ := fun ω ↦ x + stoppedValue W (hittingAfter W (Ioo (a - x) (b - x))ᶜ 0) ω
  have hZ_meas : Measurable Z := (measurable_const_add x).comp
    (stronglyMeasurable_stoppedValue_of_continuous hWm hWc
      (measurable_hittingAfter_of_isClosed (fun t ↦ (hWm t).measurable) hWc
        isOpen_Ioo.isClosed_compl 0)).measurable
  have hset_ae : {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b}
      =ᵐ[P] Z ⁻¹' {b} := eventuallyEqSet_iff.mpr <|
    (hWB.and ((hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0)).mono fun _ ⟨hω, hτ⟩ ↦ by
      simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, Z, stoppedValue, ← hτ_eq, hτ, hω]
  have hind_eq : (fun ω ↦ Z ω - a) =ᵐ[P] fun ω ↦ (b - a) * (Z ⁻¹' {b}).indicator 1 ω := by
    filter_upwards [hW.ae_eval_hittingAfter_compl_Ioo_eq_or_eq hx] with ω hω
    dsimp only [Z, stoppedValue]; rw [← hτ_eq]; rcases hω with hZa | hZb
    · rw [indicator_of_notMem (fun h ↦ hab.ne (hZa.symm.trans h)), mul_zero, sub_eq_zero.mpr hZa]
    · rw [indicator_of_mem hZb, Pi.one_apply, mul_one]; exact congrArg (· - a) hZb
  have hS_int := integrable_stoppedValue_intervalExit hW hWm hWc hW0 h0
  have hZa : ∫ ω, (Z ω - a) ∂P = x - a := by
    rw [integral_sub (f := Z) ((integrable_const x).add hS_int) (integrable_const a)]
    simp only [Z, integral_add (integrable_const x) hS_int, integral_const, probReal_univ, one_smul,
      integral_stoppedValue_intervalExit_eq_zero hW hWm hWc hW0 h0, add_zero]
  have hint := hZa.symm.trans (integral_congr_ae hind_eq)
  rw [integral_const_mul, integral_indicator_one (hZ_meas (measurableSet_singleton b))] at hint
  rw [measureReal_congr hset_ae, eq_div_iff (sub_ne_zero.mpr hab.ne'), mul_comm]; linarith

/-- `ℝ≥0∞`-valued upper exit probability for Brownian motion on `(a, b)`. -/
theorem measure_eval_hittingAfter_compl_Ioo_eq_right (hB : IsBrownianReal B P) {x a b : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) :
    P {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b} =
      ENNReal.ofReal ((x - a) / (b - a)) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _), ← measureReal_def,
    hB.measureReal_eval_hittingAfter_compl_Ioo_eq_right hab hx]

/-- **Brownian gambler's ruin (lower exit probability)**: for `a < b` and `x ∈ [a, b]`, the
probability that `x + B` exits `(a, b)` through `a` equals `(b - x) / (b - a)`. -/
theorem measureReal_eval_hittingAfter_compl_Ioo_eq_left (hB : IsBrownianReal B P) {x a b : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) :
    P.real {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a} =
      (b - x) / (b - a) := by
  have hneg := hB.neg.measureReal_eval_hittingAfter_compl_Ioo_eq_right (neg_lt_neg hab)
    ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
  have hτ : hittingAfter (fun t ω ↦ -x + (-B) t ω) (Ioo (-b) (-a))ᶜ 0 =
      hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 := by
    rw [hittingAfter_neg_const_add_neg, neg_preimage, compl_neg, neg_Ioo, neg_neg, neg_neg]
  rw [hτ] at hneg
  refine (congrArg P.real ?_).trans (hneg.trans (by ring))
  ext ω; simp only [mem_ofPred_eq, Pi.neg_apply]; constructor <;> intro <;> linarith

/-- `ℝ≥0∞`-valued lower exit probability for Brownian motion on `(a, b)`. -/
theorem measure_eval_hittingAfter_compl_Ioo_eq_left (hB : IsBrownianReal B P) {x a b : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) :
    P {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a} =
      ENNReal.ofReal ((b - x) / (b - a)) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _), ← measureReal_def,
    hB.measureReal_eval_hittingAfter_compl_Ioo_eq_left hab hx]

/-- **Exit-position law of Brownian motion on `(a, b)`**: for `a < b` and `x ∈ [a, b]`, the exit
position `x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω` has the two-point
law `((b - x) / (b - a)) • δ_a + ((x - a) / (b - a)) • δ_b`. -/
theorem hasLaw_eval_hittingAfter_compl_Ioo (hB : IsBrownianReal B P) {x a b : ℝ} (hab : a < b)
    (hx : x ∈ Icc a b) :
    HasLaw (fun ω ↦ x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω)
      (ENNReal.ofReal ((b - x) / (b - a)) • Measure.dirac a +
        ENNReal.ofReal ((x - a) / (b - a)) • Measure.dirac b) P := by
  have hm := (hB.aemeasurable_eval_hittingAfter_compl_Ioo x a b).const_add x
  refine ⟨hm, ?_⟩
  rw [(Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac (μ := P.map _) hab.ne).mp
      ((ae_map_iff hm ((measurableSet_singleton a).union (measurableSet_singleton b))).mpr
        (hB.ae_eval_hittingAfter_compl_Ioo_eq_or_eq hx)),
    Measure.map_apply₀ hm (measurableSet_singleton a).nullMeasurableSet,
    Measure.map_apply₀ hm (measurableSet_singleton b).nullMeasurableSet]
  exact congrArg₂ (· + ·) (congrArg (· • _) (hB.measure_eval_hittingAfter_compl_Ioo_eq_left hab hx))
    (congrArg (· • _) (hB.measure_eval_hittingAfter_compl_Ioo_eq_right hab hx))

/-- The first exit time `(hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA` of `x + B`
from any open interval `(a, b)` is integrable. -/
theorem integrable_hittingAfter_compl_Ioo (hB : IsBrownianReal B P) (x a b : ℝ) :
    Integrable (fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ)) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  by_cases hx : x ∈ Ioo a b
  · obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
    have hτ_eq := (hittingAfter_comp W (x + ·) (Ioo a b)ᶜ 0).trans <| by
      rw [preimage_compl, preimage_const_add_Ioo]
    exact (integrable_intervalExit_of_mem_Icc hW hWm hWc hW0
        ⟨sub_nonpos.mpr hx.1.le, sub_nonneg.mpr hx.2.le⟩).congr
      (((hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0).mono fun _ hω ↦ by
        simp only [← hτ_eq, hω])
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
    have hτ_eq := (hittingAfter_comp W (x + ·) (Ioo a b)ᶜ 0).trans <| by
      rw [preimage_compl, preimage_const_add_Ioo]
    rw [integral_congr_ae (((hWB.symm.fun_comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0).mono
        fun _ hω ↦ congrArg (fun q : WithTop ℝ≥0 ↦ (q.untopA : ℝ)) (hω.trans (congrFun hτ_eq _))),
      integral_intervalExit_eq_of_mem_Icc hW hWm hWc hW0
        ⟨sub_nonpos.mpr hx.1.le, sub_nonneg.mpr hx.2.le⟩,
      neg_sub, max_eq_right (mul_nonneg (sub_nonneg.mpr hx.1.le) (sub_nonneg.mpr hx.2.le))]
  · rw [integral_congr_ae (g := fun _ ↦ (0 : ℝ))
        ((hB.hittingAfter_compl_Ioo_ae_eq_zero_of_notMem hx).mono fun _ hω ↦ by simp [hω]),
      integral_zero,
      max_eq_left ((not_and_or.mp hx).elim (fun h ↦ by nlinarith) fun h ↦ by nlinarith)]

/-- **Mean exit time of Brownian motion from `(-K, K)`**: for `K ≥ 0` and all `x : ℝ`,
`∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo (-K) K)ᶜ 0 ω).untopA : ℝ) ∂P =`
`max 0 (K ^ 2 - x ^ 2)`. -/
theorem integral_hittingAfter_compl_Ioo_neg (hB : IsBrownianReal B P) (x : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo (-K) K)ᶜ 0 ω).untopA : ℝ) ∂P =
      max 0 (K ^ 2 - x ^ 2) := by
  rw [hB.integral_hittingAfter_compl_Ioo x (neg_le_self hK)]; congr 1; ring

end ProbabilityTheory.IsBrownianReal
