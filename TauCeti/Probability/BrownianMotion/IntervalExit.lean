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
import TauCeti.Probability.BrownianMotion.LevelHit
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.BrownianMotion.Version
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Process.HittingTime
import TauCeti.Probability.Process.Progressive
import TauCeti.Probability.Process.Version

/-!
# One-dimensional Brownian exit from bounded open intervals

For a real Brownian motion `B` and starting position `x : ℝ`, let
`τ := hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0`
be the first exit time of `x + B` from the open interval `(a, b)`.

Combining immediate Brownian boundary crossing with bounded optional sampling of the martingales
`W` and `W² - t` on a continuous modification gives:

1. **Open- versus closed-interval exit**: `hittingAfter (fun t ω ↦ x + B t ω) (Icc a b)ᶜ 0`
   agrees almost surely with `hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0` for all `x, a, b`.
2. **Boundary dichotomy and gambler's ruin exit probabilities**: for `a < b` and `x ∈ [a, b]`,
   the stopped position `x + B (τ ω).untopA ω` lies in `{a, b}` almost surely, with
   `P.real {ω | x + B (τ ω).untopA ω = b} = (x - a) / (b - a)` and
   `P.real {ω | x + B (τ ω).untopA ω = a} = (b - x) / (b - a)`.
3. **Integrability and exact mean of the exit time**: `(τ ω).untopA` is integrable for all
   `x, a, b : ℝ`, and for `a ≤ b`,
   `∫ ω, ((τ ω).untopA : ℝ) ∂P = max 0 ((x - a) * (b - x))`
   (in particular `max 0 (K ^ 2 - x ^ 2)` on `Ioo (-K) K` for `K ≥ 0`).

## Main results

* `ProbabilityTheory.IsBrownianReal.hittingAfter_compl_Icc_ae_eq_compl_Ioo`
* `ProbabilityTheory.IsBrownianReal.hittingAfter_compl_Ioo_ne_top`,
  `ProbabilityTheory.IsBrownianReal.hittingAfter_compl_Ioo_ae_eq_zero_of_notMem`
* `ProbabilityTheory.IsBrownianReal.eval_hittingAfter_compl_Ioo_eq_or_eq`
* `ProbabilityTheory.IsBrownianReal.measureReal_eval_hittingAfter_compl_Ioo_eq_right`,
  `ProbabilityTheory.IsBrownianReal.measure_eval_hittingAfter_compl_Ioo_eq_right`,
  `ProbabilityTheory.IsBrownianReal.measureReal_eval_hittingAfter_compl_Ioo_eq_left`,
  `ProbabilityTheory.IsBrownianReal.measure_eval_hittingAfter_compl_Ioo_eq_left`
* `ProbabilityTheory.IsBrownianReal.integrable_hittingAfter_compl_Ioo`
* `ProbabilityTheory.IsBrownianReal.integral_hittingAfter_compl_Ioo`,
  `ProbabilityTheory.IsBrownianReal.integral_hittingAfter_compl_Ioo_neg`

## References

* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed.,
  Section 2.8.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability

private theorem mem_Icc_of_le_hittingAfter_compl_Ioo {Ω : Type*} {Y : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {a b : ℝ} {s : ℝ≥0} (hYc : Continuous (Y · ω)) (h0 : Y 0 ω ∈ Icc a b)
    (hs : (s : WithTop ℝ≥0) ≤ hittingAfter Y (Ioo a b)ᶜ 0 ω) :
    Y s ω ∈ Icc a b := by
  have hsub₁ : Iic a ⊆ (Ioo a b)ᶜ := fun y hy h ↦ hy.not_gt h.1
  have hsub₂ : Ici b ⊆ (Ioo a b)ᶜ := fun y hy h ↦ hy.not_gt h.2
  exact ⟨hYc.ge_of_le_hittingAfter_Iic zero_le h0.1
      (hs.trans (hittingAfter_apply_anti Y 0 ω hsub₁)),
    hYc.le_of_le_hittingAfter_Ici zero_le h0.2
      (hs.trans (hittingAfter_apply_anti Y 0 ω hsub₂))⟩

private theorem eval_untopA_hittingAfter_compl_Ioo_eq_or_eq {Ω : Type*} {Y : ℝ≥0 → Ω → ℝ}
    {ω : Ω} {a b : ℝ} (hYc : Continuous (Y · ω)) (h0 : Y 0 ω ∈ Icc a b)
    (hfin : hittingAfter Y (Ioo a b)ᶜ 0 ω ≠ ⊤) :
    Y (hittingAfter Y (Ioo a b)ᶜ 0 ω).untopA ω = a ∨
      Y (hittingAfter Y (Ioo a b)ᶜ 0 ω).untopA ω = b := by
  obtain ⟨u, hu, _, hus⟩ := isOpen_Ioo.isClosed_compl.exists_hittingAfter_eq hYc hfin
  have hmem : Y u ω ∈ Icc a b :=
    mem_Icc_of_le_hittingAfter_compl_Ioo hYc h0 hu.symm.le
  have hut : (hittingAfter Y (Ioo a b)ᶜ 0 ω).untopA = u := by
    simp only [hu, WithTop.untopA, WithTop.untopD_coe]
  rw [hut]
  rcases hmem.1.eq_or_lt with heq | hlt
  · exact Or.inl heq.symm
  · rcases hmem.2.eq_or_lt with heq | hlt'
    · exact Or.inr heq
    · exact absurd ⟨hlt, hlt'⟩ hus

private theorem isStoppingTime_intervalExit {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (x a b : ℝ) :
    IsStoppingTime (Filtration.natural W hWm)
      (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) := by
  have hpre : (x + ·) ⁻¹' (Ioo a b)ᶜ = (Ioo (a - x) (b - x))ᶜ := by
    rw [preimage_compl, preimage_const_add_Ioo]
  rw [hittingAfter_comp (x + ·), hpre]
  exact (Filtration.stronglyAdapted_natural hWm).adapted.isStoppingTime_hittingAfter_compl_of_isOpen
    hWc isOpen_Ioo 0

private theorem norm_stoppedProcess_le_of_mem_Icc {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b)
    (T : ℝ≥0) (ω : Ω) :
    ‖stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω‖ ≤
      max |a - x| |b - x| := by
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  have hmin_ne : min (T : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  cases hq : min (T : WithTop ℝ≥0) (τ ω) with
  | top => exact absurd hq hmin_ne
  | coe s =>
    have hsτ : (s : WithTop ℝ≥0) ≤ τ ω := hq ▸ min_le_right _ _
    have hY := mem_Icc_of_le_hittingAfter_compl_Ioo (Y := fun t ω ↦ x + W t ω)
      ((continuous_const_add x).comp (hWc ω))
      (by simpa only [hW0 ω, add_zero] using hx) hsτ
    have hval : stoppedProcess W τ T ω = W s ω := by
      simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, hq, WithTop.untopA,
        WithTop.untopD_coe]
    rw [hval, Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · have hle : -|a - x| ≤ a - x := neg_abs_le _
      linarith [le_max_left |a - x| |b - x|, hY.1]
    · have hle : b - x ≤ |b - x| := le_abs_self _
      linarith [le_max_right |a - x| |b - x|, hY.2]

private theorem sq_stoppedProcess_le_of_mem_Icc {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b)
    (T : ℝ≥0) (ω : Ω) :
    stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω ^ 2 ≤
      max |a - x| |b - x| ^ 2 := by
  have hn := norm_stoppedProcess_le_of_mem_Icc hWc hW0 hx T ω
  rw [Real.norm_eq_abs] at hn
  exact sq_le_sq.mpr (by rwa [abs_of_nonneg (le_max_of_le_left (abs_nonneg _))])

private theorem norm_stoppedValue_le_of_mem_Icc {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b)
    {ω : Ω} (hfin : hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω ≠ ⊤) :
    ‖stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) ω‖ ≤
      max |a - x| |b - x| := by
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  cases hτ : τ ω with
  | top => exact absurd hτ hfin
  | coe s =>
    have heq : stoppedValue W τ ω = stoppedProcess W τ s ω := by
      simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, hτ, min_self]
    rw [heq]
    exact norm_stoppedProcess_le_of_mem_Icc hWc hW0 hx s ω

private theorem eventually_stoppedProcess_eq_stoppedValue {Ω : Type*} (u : ℝ≥0 → Ω → ℝ)
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} (hfin : τ ω ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, stoppedProcess u τ (n : ℝ≥0) ω = stoppedValue u τ ω := by
  cases hτ : τ ω with
  | top => exact absurd hτ hfin
  | coe s =>
    filter_upwards [eventually_ge_atTop ⌈s⌉₊] with n hn
    have hsn : (s : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) :=
      WithTop.coe_le_coe.mpr ((Nat.le_ceil s).trans (Nat.cast_le.mpr hn))
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, hτ, min_eq_right hsn]

private theorem monotone_untopA_min_nat (τ : WithTop ℝ≥0) :
    Monotone fun n : ℕ ↦ ((min ((n : ℝ≥0) : WithTop ℝ≥0) τ).untopA : ℝ) := by
  intro m n hmn
  cases τ with
  | top =>
    simp only [le_top, min_eq_left, WithTop.untopA, WithTop.untopD_coe, NNReal.coe_le_coe,
      Nat.cast_le, hmn]
  | coe s =>
    have hm : min ((m : ℝ≥0) : WithTop ℝ≥0) (s : WithTop ℝ≥0) = (min (m : ℝ≥0) s : ℝ≥0) := rfl
    have hn : min ((n : ℝ≥0) : WithTop ℝ≥0) (s : WithTop ℝ≥0) = (min (n : ℝ≥0) s : ℝ≥0) := rfl
    simp only [hm, hn, WithTop.untopA, WithTop.untopD_coe, NNReal.coe_le_coe]
    exact min_le_min_right s (Nat.cast_le.mpr hmn)

private theorem eventually_untopA_min_nat_eq {τ : WithTop ℝ≥0} (hfin : τ ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, ((min ((n : ℝ≥0) : WithTop ℝ≥0) τ).untopA : ℝ) = (τ.untopA : ℝ) := by
  cases τ with
  | top => exact absurd rfl hfin
  | coe s =>
    filter_upwards [eventually_ge_atTop ⌈s⌉₊] with n hn
    have hsn : (s : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) :=
      WithTop.coe_le_coe.mpr ((Nat.le_ceil s).trans (Nat.cast_le.mpr hn))
    simp only [min_eq_right hsn]

private theorem integrable_untopA_min_const {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0} (hτ : Measurable τ) (T : ℝ≥0) :
    Integrable (fun ω ↦ ((min (T : WithTop ℝ≥0) (τ ω)).untopA : ℝ)) P := by
  have hm : Measurable fun ω ↦ ((min (T : WithTop ℝ≥0) (τ ω)).untopA : ℝ) :=
    measurable_subtype_coe.comp (measurable_const.min hτ).untopA
  refine Integrable.of_bound hm.aestronglyMeasurable T (Eventually.of_forall fun ω ↦ ?_)
  cases hq : min (T : WithTop ℝ≥0) (τ ω) with
  | top => exact absurd hq (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))
  | coe s =>
    have hsT : s ≤ T := WithTop.coe_le_coe.mp (hq ▸ min_le_left _ _)
    simp only [WithTop.untopA, WithTop.untopD_coe, Real.norm_eq_abs,
      abs_of_nonneg (NNReal.coe_nonneg s), NNReal.coe_le_coe, hsT]

private theorem integral_stoppedProcess_intervalExit_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) (x a b : ℝ) (T : ℝ≥0) :
    ∫ ω, stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω ∂P = 0 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ℱ := Filtration.natural W hWm
  have hWF := hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm
  have hτ := isStoppingTime_intervalExit hWm hWc x a b
  have hprog := hWF.martingale.stronglyAdapted.isStronglyProgressive_of_isRightContinuous
    fun ω ↦ (hWc ω).isRightContinuous
  have hstop := hWF.martingale.stoppedProcess_of_ae_isRightContinuous hprog
    (Eventually.of_forall fun ω ↦ (hWc ω).isRightContinuous) hτ
  have heq := hstop.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) (@MeasurableSet.univ Ω (ℱ 0))
  simp only [Measure.restrict_univ] at heq
  have hzero (ω : Ω) :
      stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) 0 ω = 0 := by
    have h0 : min ((0 : ℝ≥0) : WithTop ℝ≥0)
        (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω) = (0 : ℝ≥0) :=
      min_eq_left bot_le
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, h0, WithTop.untopA,
      WithTop.untopD_coe, hW0 ω]
  simpa only [hzero, integral_zero] using heq.symm

private theorem integral_min_intervalExit_eq_integral_sq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) (x a b : ℝ) (T : ℝ≥0) :
    ∫ ω, ((min (T : WithTop ℝ≥0)
        (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω)).untopA : ℝ) ∂P =
      ∫ ω, stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω ^ 2 ∂P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ℱ := Filtration.natural W hWm
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  let M : ℝ≥0 → Ω → ℝ := fun t ω ↦ W t ω ^ 2 - (t : ℝ)
  have hWF := hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm
  have hτ := isStoppingTime_intervalExit hWm hWc x a b
  have hMc (ω : Ω) : Continuous (M · ω) := ((hWc ω).pow 2).sub NNReal.continuous_coe
  have hprog := hWF.martingale_sq_sub.stronglyAdapted.isStronglyProgressive_of_isRightContinuous
    fun ω ↦ (hMc ω).isRightContinuous
  have hstop := hWF.martingale_sq_sub.stoppedProcess_of_ae_isRightContinuous hprog
    (Eventually.of_forall fun ω ↦ (hMc ω).isRightContinuous) hτ
  have heq := hstop.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) (@MeasurableSet.univ Ω (ℱ 0))
  simp only [Measure.restrict_univ] at heq
  have h0 (ω : Ω) : stoppedProcess M τ 0 ω = 0 := by
    have hm : min ((0 : ℝ≥0) : WithTop ℝ≥0) (τ ω) = (0 : ℝ≥0) := min_eq_left bot_le
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, hm, WithTop.untopA,
      WithTop.untopD_coe, M, hW0 ω, NNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sub_zero]
  have hτ_meas : Measurable τ :=
    measurable_hittingAfter_of_isClosed (fun t ↦ (measurable_const_add x).comp (hWm t).measurable)
      (fun ω ↦ (continuous_const_add x).comp (hWc ω)) isOpen_Ioo.isClosed_compl 0
  let u : Ω → ℝ := fun ω ↦ ((min (T : WithTop ℝ≥0) (τ ω)).untopA : ℝ)
  have hu_int : Integrable u P := integrable_untopA_min_const hτ_meas T
  have hsq_eq :
      (fun ω ↦ stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω ^ 2) =
        fun ω ↦ stoppedProcess M τ T ω + u ω :=
    funext fun ω ↦ by
      simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, M, u, τ, sub_add_cancel]
  rw [hsq_eq, integral_add (hstop.integrable T) hu_int]
  have hM0 : ∫ ω, stoppedProcess M τ T ω ∂P = 0 := by
    dsimp only [M, τ] at h0 ⊢
    simpa only [h0, integral_zero] using heq.symm
  linarith

private theorem integral_stoppedValue_intervalExit_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    ∫ ω, stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) ω ∂P = 0 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  have hWF := hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm
  have hτ := isStoppingTime_intervalExit hWm hWc x a b
  have hprog := hWF.martingale.stronglyAdapted.isStronglyProgressive_of_isRightContinuous
    fun ω ↦ (hWc ω).isRightContinuous
  have hstop := hWF.martingale.stoppedProcess_of_ae_isRightContinuous hprog
    (Eventually.of_forall fun ω ↦ (hWc ω).isRightContinuous) hτ
  have hfin_ae : ∀ᵐ ω ∂P, τ ω ≠ ⊤ :=
    hW.hittingAfter_compl_ne_top x fun h ↦ (h ▸ mem_univ a : a ∈ Ioo a b).1.false
  have hlim : Tendsto (fun n : ℕ ↦ ∫ ω, stoppedProcess W τ (n : ℝ≥0) ω ∂P) atTop
      (𝓝 (∫ ω, stoppedValue W τ ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ max |a - x| |b - x|)
      (fun n ↦ (hstop.integrable (n : ℝ≥0)).aestronglyMeasurable)
      (integrable_const _)
      (fun n ↦ Eventually.of_forall (norm_stoppedProcess_le_of_mem_Icc hWc hW0 hx (n : ℝ≥0)))
      (hfin_ae.mono fun ω hfin ↦
        tendsto_nhds_of_eventually_eq (eventually_stoppedProcess_eq_stoppedValue W hfin))
  exact tendsto_nhds_unique hlim ((tendsto_const_nhds (x := (0 : ℝ))).congr fun n ↦
    (integral_stoppedProcess_intervalExit_eq_zero hW hWm hWc hW0 x a b (n : ℝ≥0)).symm)

private theorem integrable_intervalExit_of_mem_Icc {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    Integrable (fun ω ↦ ((hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ)) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  let C : ℝ := max |a - x| |b - x|
  have hτ_meas : Measurable τ :=
    measurable_hittingAfter_of_isClosed (fun t ↦ (measurable_const_add x).comp (hWm t).measurable)
      (fun ω ↦ (continuous_const_add x).comp (hWc ω)) isOpen_Ioo.isClosed_compl 0
  let u (n : ℕ) : Ω → ℝ := fun ω ↦ ((min ((n : ℝ≥0) : WithTop ℝ≥0) (τ ω)).untopA : ℝ)
  let U : Ω → ℝ := fun ω ↦ ((τ ω).untopA : ℝ)
  have hu_meas (n : ℕ) : Measurable (u n) :=
    measurable_subtype_coe.comp (measurable_const.min hτ_meas).untopA
  have hfin_ae : ∀ᵐ ω ∂P, τ ω ≠ ⊤ :=
    hW.hittingAfter_compl_ne_top x fun h ↦ (h ▸ mem_univ a : a ∈ Ioo a b).1.false
  have hlin_tend := lintegral_tendsto_of_tendsto_of_monotone
    (f := fun n ω ↦ ENNReal.ofReal (u n ω)) (F := fun ω ↦ ENNReal.ofReal (U ω))
    (fun n ↦ (hu_meas n).ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun ω _ _ hmn ↦
      ENNReal.ofReal_le_ofReal (monotone_untopA_min_nat (τ ω) hmn))
    (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((eventually_untopA_min_nat_eq hfin).mono fun n hn ↦ by dsimp only [u, U]; rw [hn]))
  have hWF := hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm
  have hstop := hWF.martingale.stoppedProcess_of_ae_isRightContinuous
    (hWF.martingale.stronglyAdapted.isStronglyProgressive_of_isRightContinuous
      fun ω ↦ (hWc ω).isRightContinuous)
    (Eventually.of_forall fun ω ↦ (hWc ω).isRightContinuous)
    (isStoppingTime_intervalExit hWm hWc x a b)
  have hlin_le (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (u n ω) ∂P ≤ ENNReal.ofReal (C ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_untopA_min_const hτ_meas (n : ℝ≥0))
        (Eventually.of_forall fun _ ↦ NNReal.coe_nonneg _),
      integral_min_intervalExit_eq_integral_sq hW hWm hWc hW0 x a b (n : ℝ≥0)]
    have hsq_le := sq_stoppedProcess_le_of_mem_Icc hWc hW0 hx (n : ℝ≥0)
    have hsq_int : Integrable (fun ω ↦ stoppedProcess W τ (n : ℝ≥0) ω ^ 2) P :=
      Integrable.of_bound ((hstop.integrable (n : ℝ≥0)).aestronglyMeasurable.pow 2) (C ^ 2)
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq_le ω)
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono hsq_int (integrable_const (C ^ 2)) hsq_le
  refine ⟨(measurable_subtype_coe.comp hτ_meas.untopA).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_congr fun ω ↦ Real.eNorm_eq_ofReal (NNReal.coe_nonneg _)]
  exact (le_of_tendsto hlin_tend (Eventually.of_forall hlin_le)).trans_lt ENNReal.ofReal_lt_top

private theorem measurable_stoppedValue_intervalExit {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (x a b : ℝ) :
    Measurable (stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0)) := by
  have hτ := isStoppingTime_intervalExit hWm hWc x a b
  have hprog := (Filtration.stronglyAdapted_natural hWm).isStronglyProgressive_of_isRightContinuous
    fun ω ↦ (hWc ω).isRightContinuous
  exact (measurable_stoppedValue hprog hτ).mono hτ.measurableSpace_le le_rfl

private theorem integrable_stoppedValue_intervalExit {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    Integrable (stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0)) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hfin_ae := hW.hittingAfter_compl_ne_top (A := Ioo a b) x fun h ↦
    (h ▸ mem_univ a : a ∈ Ioo a b).1.false
  exact Integrable.of_bound
    (measurable_stoppedValue_intervalExit hWm hWc x a b).aestronglyMeasurable (max |a - x| |b - x|)
    (hfin_ae.mono fun ω hfin ↦ norm_stoppedValue_le_of_mem_Icc hWc hW0 hx hfin)

private theorem integral_intervalExit_eq_of_mem_Icc {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    ∫ ω, ((hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P =
      (x - a) * (b - x) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  let C : ℝ := max |a - x| |b - x|
  have hτ_meas : Measurable τ :=
    measurable_hittingAfter_of_isClosed (fun t ↦ (measurable_const_add x).comp (hWm t).measurable)
      (fun ω ↦ (continuous_const_add x).comp (hWc ω)) isOpen_Ioo.isClosed_compl 0
  have hU_int := integrable_intervalExit_of_mem_Icc hW hWm hWc hW0 hx
  have hfin_ae : ∀ᵐ ω ∂P, τ ω ≠ ⊤ :=
    hW.hittingAfter_compl_ne_top x fun h ↦ (h ▸ mem_univ a : a ∈ Ioo a b).1.false
  have hlim_u := integral_tendsto_of_tendsto_of_monotone
    (fun n ↦ integrable_untopA_min_const hτ_meas (n : ℝ≥0)) hU_int
    (Eventually.of_forall fun ω ↦ monotone_untopA_min_nat (τ ω))
    (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq (eventually_untopA_min_nat_eq hfin))
  have hWF := hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm
  have hstop := hWF.martingale.stoppedProcess_of_ae_isRightContinuous
    (hWF.martingale.stronglyAdapted.isStronglyProgressive_of_isRightContinuous
      fun ω ↦ (hWc ω).isRightContinuous)
    (Eventually.of_forall fun ω ↦ (hWc ω).isRightContinuous)
    (isStoppingTime_intervalExit hWm hWc x a b)
  have hlim_sq : Tendsto (fun n : ℕ ↦ ∫ ω, stoppedProcess W τ (n : ℝ≥0) ω ^ 2 ∂P) atTop
      (𝓝 (∫ ω, stoppedValue W τ ω ^ 2 ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ C ^ 2)
      (fun n ↦ (hstop.integrable (n : ℝ≥0)).aestronglyMeasurable.pow 2) (integrable_const _)
      (fun n ↦ Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_stoppedProcess_le_of_mem_Icc hWc hW0 hx (n : ℝ≥0) ω)
      (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
        ((eventually_stoppedProcess_eq_stoppedValue W hfin).mono fun n hn ↦ by rw [hn]))
  have heq_U_sq : ∫ ω, ((τ ω).untopA : ℝ) ∂P = ∫ ω, stoppedValue W τ ω ^ 2 ∂P :=
    tendsto_nhds_unique hlim_u (hlim_sq.congr fun n ↦
      (integral_min_intervalExit_eq_integral_sq hW hWm hWc hW0 x a b (n : ℝ≥0)).symm)
  have hSV_int := integrable_stoppedValue_intervalExit hW hWm hWc hW0 hx
  have hpoly : (fun ω ↦ stoppedValue W τ ω ^ 2) =ᵐ[P]
      fun ω ↦ (x - a) * (b - x) + (a + b - 2 * x) * stoppedValue W τ ω :=
    hfin_ae.mono fun ω hfin ↦ by
      have hdich := eval_untopA_hittingAfter_compl_Ioo_eq_or_eq (Y := fun t ω ↦ x + W t ω)
        ((continuous_const_add x).comp (hWc ω)) (by simpa only [hW0 ω, add_zero] using hx) hfin
      have hz : (x + stoppedValue W τ ω - a) * (b - (x + stoppedValue W τ ω)) = 0 := by
        rcases hdich with h | h <;> (dsimp only [stoppedValue, τ]; rw [h]; ring)
      linarith [show stoppedValue W τ ω ^ 2 =
          (x - a) * (b - x) + (a + b - 2 * x) * stoppedValue W τ ω -
            (x + stoppedValue W τ ω - a) * (b - (x + stoppedValue W τ ω)) by ring]
  rw [heq_U_sq, integral_congr_ae hpoly,
    integral_add (integrable_const _) (hSV_int.const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_stoppedValue_intervalExit_eq_zero hW hWm hWc hW0 hx, mul_zero, add_zero]

end TauCeti.Probability

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Open- versus closed-interval exit for Brownian motion**: for all `x, a, b : ℝ`, the first
exit time of `x + B` from the closed interval `[a, b]` agrees almost surely with its first exit
time from the open interval `(a, b)`. -/
theorem hittingAfter_compl_Icc_ae_eq_compl_Ioo (hB : IsBrownianReal B P) (x a b : ℝ) :
    hittingAfter (fun t ω ↦ x + B t ω) (Icc a b)ᶜ 0 =ᵐ[P]
      hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 := by
  have hc₁ : (Icc a b)ᶜ = Iio a ∪ Ioi b := by
    ext y; simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  have hc₂ : (Ioo a b)ᶜ = Iic a ∪ Ici b := by
    ext y; simp only [mem_compl_iff, mem_Ioo, mem_union, mem_Iic, mem_Ici, not_and_or, not_lt]
  rw [hc₁, hc₂, hittingAfter_comp (x + ·), hittingAfter_comp (x + ·),
    preimage_union, preimage_union, preimage_const_add_Iio, preimage_const_add_Ioi,
    preimage_const_add_Iic, preimage_const_add_Ici, hittingAfter_union, hittingAfter_union]
  filter_upwards [hB.hittingAfter_Iio_ae_eq_Iic (a - x),
    hB.hittingAfter_Ioi_ae_eq_Ici (b - x)] with ω h₁ h₂
  simp only [Pi.inf_apply, h₁, h₂]

/-- A real Brownian motion started at `x` exits every open interval `(a, b)` in finite time almost
surely. -/
theorem hittingAfter_compl_Ioo_ne_top (hB : IsBrownianReal B P) (x a b : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω ≠ ⊤ :=
  hB.hittingAfter_compl_ne_top x fun h ↦ (h ▸ mem_univ a : a ∈ Ioo a b).1.false

/-- When the starting point `x` lies outside `(a, b)`, the first exit time of `x + B` from
`(a, b)` is almost surely `0`. -/
theorem hittingAfter_compl_Ioo_ae_eq_zero_of_notMem (hB : IsBrownianReal B P) {x a b : ℝ}
    (hx : x ∉ Ioo a b) :
    hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 =ᵐ[P] 0 := by
  obtain ⟨W, _, _, hW0, _, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  rw [hittingAfter_comp (x + ·)]
  refine (hWB.symm.hittingAfter_ae_eq _ 0).trans (Eventually.of_forall fun ω ↦ ?_)
  exact le_antisymm (hittingAfter_le_of_mem le_rfl (by simpa only [mem_preimage, hW0 ω, add_zero,
    mem_compl_iff] using hx)) bot_le

/-- Starting from `x ∈ [a, b]`, the position of `x + B` at its first exit from `(a, b)` equals
either `a` or `b` almost surely. -/
theorem eval_hittingAfter_compl_Ioo_eq_or_eq (hB : IsBrownianReal B P) {x a b : ℝ}
    (hx : x ∈ Icc a b) :
    ∀ᵐ ω ∂P,
      x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a ∨
        x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b := by
  obtain ⟨W, _, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  filter_upwards [hWB, hW.hittingAfter_compl_Ioo_ne_top x a b] with ω hω hfin
  have hτ : hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω =
      hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω := by
    classical
    simp only [hittingAfter_def, hω]
  rw [hτ, ← hω]
  exact eval_untopA_hittingAfter_compl_Ioo_eq_or_eq (Y := fun t ω ↦ x + W t ω)
    ((continuous_const_add x).comp (hWc ω)) (by simpa only [hW0 ω, add_zero] using hx) hfin

/-- **Brownian gambler's ruin (upper exit probability)**: for `a < b` and `x ∈ [a, b]`, the
probability that `x + B` exits `(a, b)` through the upper endpoint `b` equals
`(x - a) / (b - a)`. -/
theorem measureReal_eval_hittingAfter_compl_Ioo_eq_right (hB : IsBrownianReal B P)
    {x a b : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    P.real {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b} =
      (x - a) / (b - a) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  let Z : Ω → ℝ := fun ω ↦ x + stoppedValue W τ ω
  have hZ_meas : Measurable Z :=
    (measurable_const_add x).comp (measurable_stoppedValue_intervalExit hWm hWc x a b)
  have hSV_int := integrable_stoppedValue_intervalExit hW hWm hWc hW0 hx
  have hset_ae : {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b}
      =ᵐ[P] Z ⁻¹' {b} := by
    filter_upwards [hWB] with ω hω
    have hτ_eq : hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω = τ ω := by
      classical
      simp only [τ, hittingAfter_def, hω]
    simp only [mem_preimage, mem_singleton_iff, Z, stoppedValue, hτ_eq, hω]
  have hind_eq : (fun ω ↦ Z ω - a) =ᵐ[P]
      fun ω ↦ (b - a) * ((Z ⁻¹' {b}).indicator 1 ω) := by
    filter_upwards [hW.eval_hittingAfter_compl_Ioo_eq_or_eq hx] with ω hω
    rcases hω with ha_eq | hb_eq
    · have hZa : Z ω = a := ha_eq
      have hnot : ω ∉ Z ⁻¹' {b} := fun h ↦ hab.ne (hZa.symm.trans h)
      rw [indicator_of_notMem hnot, mul_zero, hZa, sub_self]
    · have hZb : Z ω = b := hb_eq
      have hmem : ω ∈ Z ⁻¹' {b} := hZb
      rw [indicator_of_mem hmem, Pi.one_apply, mul_one, hZb]
  have hint := integral_congr_ae hind_eq
  have hlhs : ∫ ω, (Z ω - a) ∂P = x - a := by
    have hsub : (fun ω ↦ Z ω - a) = fun ω ↦ (x - a) + stoppedValue W τ ω := by ext ω; simp [Z]; ring
    rw [hsub, integral_add (integrable_const _) hSV_int, integral_const, probReal_univ, one_smul,
      integral_stoppedValue_intervalExit_eq_zero hW hWm hWc hW0 hx, add_zero]
  have hrhs : ∫ ω, (b - a) * ((Z ⁻¹' {b}).indicator 1 ω) ∂P =
      (b - a) * P.real (Z ⁻¹' {b}) := by
    rw [integral_const_mul, integral_indicator_one (hZ_meas (measurableSet_singleton b))]
  rw [measureReal_congr hset_ae, eq_div_iff (sub_ne_zero.mpr hab.ne'), mul_comm]
  linarith

/-- `ℝ≥0∞`-valued upper exit probability for Brownian motion on `(a, b)`. -/
theorem measure_eval_hittingAfter_compl_Ioo_eq_right (hB : IsBrownianReal B P)
    {x a b : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    P {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b} =
      ENNReal.ofReal ((x - a) / (b - a)) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _), ← measureReal_def,
    hB.measureReal_eval_hittingAfter_compl_Ioo_eq_right hab hx]

/-- **Brownian gambler's ruin (lower exit probability)**: for `a < b` and `x ∈ [a, b]`, the
probability that `x + B` exits `(a, b)` through the lower endpoint `a` equals
`(b - x) / (b - a)`. -/
theorem measureReal_eval_hittingAfter_compl_Ioo_eq_left (hB : IsBrownianReal B P)
    {x a b : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    P.real {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a} =
      (b - x) / (b - a) := by
  have hneg := hB.neg.measureReal_eval_hittingAfter_compl_Ioo_eq_right (neg_lt_neg hab)
    ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
  have hτ : hittingAfter (fun t ω ↦ -x + (-B) t ω) (Ioo (-b) (-a))ᶜ 0 =
      hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 := by
    have hfun : (fun t ω ↦ -x + (-B) t ω) = fun t ω ↦ -(x + B t ω) := by ext t ω; simp [add_comm]
    have hpre : (fun y : ℝ ↦ -y) ⁻¹' (Ioo (-b) (-a))ᶜ = (Ioo a b)ᶜ := by
      ext y; simp only [mem_preimage, mem_compl_iff, mem_Ioo, neg_lt_neg_iff, and_comm]
    rw [hfun, hittingAfter_comp (fun y : ℝ ↦ -y), hpre]
  have hval (ω : Ω) :
      -x + (-B) (hittingAfter (fun t ω ↦ -x + (-B) t ω) (Ioo (-b) (-a))ᶜ 0 ω).untopA ω =
        -(x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω) := by
    rw [hτ]
    simp [add_comm]
  have hset : {ω | -x + (-B) (hittingAfter (fun t ω ↦ -x + (-B) t ω) (Ioo (-b) (-a))ᶜ 0 ω).untopA ω
      = -a} =
      {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a} := by
    ext ω
    simp only [mem_ofPred_eq, hval ω, neg_inj]
  rw [hset] at hneg
  refine hneg.trans ?_
  ring

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
    have hBW : (fun ω ↦ ((hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ)) =ᵐ[P]
        fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) := by
      have hτ : hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 =ᵐ[P]
          hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 := by
        simpa only [hittingAfter_comp (x + ·)] using
          hWB.hittingAfter_ae_eq ((x + ·) ⁻¹' (Ioo a b)ᶜ) 0
      exact hτ.mono fun ω hω ↦ by simp only [hω]
    exact (integrable_intervalExit_of_mem_Icc hW hWm hWc hW0 (Ioo_subset_Icc_self hx)).congr hBW
  · refine (integrable_zero Ω ℝ P).congr ?_
    filter_upwards [hB.hittingAfter_compl_Ioo_ae_eq_zero_of_notMem hx] with ω hω
    simp [hω]

/-- **Mean exit time of Brownian motion from `(a, b)`**: for `a ≤ b` and all `x : ℝ`,
`∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P =`
`max 0 ((x - a) * (b - x))`. -/
theorem integral_hittingAfter_compl_Ioo (hB : IsBrownianReal B P) (x : ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P =
      max 0 ((x - a) * (b - x)) := by
  by_cases hx : x ∈ Ioo a b
  · obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
    have hBW : (fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ)) =ᵐ[P]
        fun ω ↦ ((hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) := by
      have hτ : hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 =ᵐ[P]
          hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 := by
        simpa only [hittingAfter_comp (x + ·)] using
          hWB.symm.hittingAfter_ae_eq ((x + ·) ⁻¹' (Ioo a b)ᶜ) 0
      exact hτ.mono fun ω hω ↦ by simp only [hω]
    have hpos : 0 ≤ (x - a) * (b - x) :=
      mul_nonneg (sub_nonneg.mpr hx.1.le) (sub_nonneg.mpr hx.2.le)
    rw [integral_congr_ae hBW,
      integral_intervalExit_eq_of_mem_Icc hW hWm hWc hW0 (Ioo_subset_Icc_self hx),
      max_eq_right hpos]
  · have hnonpos : (x - a) * (b - x) ≤ 0 := by
      rcases le_or_gt x a with hxa | hax
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxa)
          (sub_nonneg.mpr (hxa.trans hab))
      · have hbx : b ≤ x := not_lt.mp fun hxb ↦ hx ⟨hax, hxb⟩
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hax.le) (sub_nonpos.mpr hbx)
    have hz : (fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ))
        =ᵐ[P] 0 := by
      filter_upwards [hB.hittingAfter_compl_Ioo_ae_eq_zero_of_notMem hx] with ω hω
      simp [hω]
    rw [integral_congr_ae hz, Pi.zero_def, integral_zero, max_eq_left hnonpos]

/-- **Mean exit time of Brownian motion from `(-K, K)`**: for `K ≥ 0` and all `x : ℝ`,
`∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo (-K) K)ᶜ 0 ω).untopA : ℝ) ∂P =`
`max 0 (K ^ 2 - x ^ 2)`. -/
theorem integral_hittingAfter_compl_Ioo_neg (hB : IsBrownianReal B P) (x : ℝ) {K : ℝ}
    (hK : 0 ≤ K) :
    ∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo (-K) K)ᶜ 0 ω).untopA : ℝ) ∂P =
      max 0 (K ^ 2 - x ^ 2) := by
  rw [hB.integral_hittingAfter_compl_Ioo x (neg_le_self hK)]
  congr 1
  ring

end ProbabilityTheory.IsBrownianReal
