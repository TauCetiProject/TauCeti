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
    Y s ω ∈ Icc a b :=
  ⟨hYc.ge_of_le_hittingAfter_Iic zero_le h0.1
      (hs.trans (hittingAfter_apply_anti Y 0 ω fun _ hy h ↦ hy.not_gt h.1)),
    hYc.le_of_le_hittingAfter_Ici zero_le h0.2
      (hs.trans (hittingAfter_apply_anti Y 0 ω fun _ hy h ↦ hy.not_gt h.2))⟩

private theorem eval_untopA_hittingAfter_compl_Ioo_eq_or_eq {Ω : Type*} {Y : ℝ≥0 → Ω → ℝ}
    {ω : Ω} {a b : ℝ} (hYc : Continuous (Y · ω)) (h0 : Y 0 ω ∈ Icc a b)
    (hfin : hittingAfter Y (Ioo a b)ᶜ 0 ω ≠ ⊤) :
    Y (hittingAfter Y (Ioo a b)ᶜ 0 ω).untopA ω = a ∨
      Y (hittingAfter Y (Ioo a b)ᶜ 0 ω).untopA ω = b := by
  obtain ⟨u, hu, _, hus⟩ := isOpen_Ioo.isClosed_compl.exists_hittingAfter_eq hYc hfin
  have hmem := mem_Icc_of_le_hittingAfter_compl_Ioo hYc h0 hu.symm.le
  simp only [hu, WithTop.untopA, WithTop.untopD_coe]
  exact hmem.1.eq_or_lt.imp Eq.symm fun hlt ↦ hmem.2.eq_or_lt.resolve_right (hus ⟨hlt, ·⟩)

private theorem isStoppingTime_intervalExit {Ω : Type*} {_ : MeasurableSpace Ω}
    {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (x a b : ℝ) :
    IsStoppingTime (Filtration.natural W hWm)
      (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) := by
  rw [hittingAfter_comp (x + ·), preimage_compl, preimage_const_add_Ioo]
  exact (Filtration.stronglyAdapted_natural hWm).adapted.isStoppingTime_hittingAfter_compl_of_isOpen
    hWc isOpen_Ioo 0

private theorem measurable_intervalExit {Ω : Type*} {_ : MeasurableSpace Ω}
    {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (x a b : ℝ) :
    Measurable (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) :=
  measurable_hittingAfter_of_isClosed (fun t ↦ (measurable_const_add x).comp (hWm t).measurable)
    (fun ω ↦ (continuous_const_add x).comp (hWc ω)) isOpen_Ioo.isClosed_compl 0

private theorem intervalExit_ne_top {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (x a b : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω ≠ ⊤ :=
  hB.hittingAfter_compl_ne_top x fun h ↦ (h ▸ mem_univ a : a ∈ Ioo a b).1.false

private theorem norm_stoppedProcess_le_of_mem_Icc {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b)
    (T : ℝ≥0) (ω : Ω) :
    ‖stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) T ω‖ ≤
      max |a - x| |b - x| := by
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  change ‖stoppedProcess W τ T ω‖ ≤ max |a - x| |b - x|
  cases hq : min (T : WithTop ℝ≥0) (τ ω) with
  | top => exact absurd hq (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))
  | coe s =>
    have hY := mem_Icc_of_le_hittingAfter_compl_Ioo (Y := fun t ω ↦ x + W t ω)
      ((continuous_const_add x).comp (hWc ω))
      (by simpa only [hW0 ω, add_zero] using hx) (hq ▸ min_le_right _ _)
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, hq, WithTop.untopA,
      WithTop.untopD_coe, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [neg_abs_le (a - x), le_max_left |a - x| |b - x|, hY.1],
      by linarith [le_abs_self (b - x), le_max_right |a - x| |b - x|, hY.2]⟩

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
    exact heq ▸ norm_stoppedProcess_le_of_mem_Icc hWc hW0 hx s ω

private theorem eventually_min_nat_eq {τ : WithTop ℝ≥0} (hfin : τ ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, min ((n : ℝ≥0) : WithTop ℝ≥0) τ = τ := by
  cases τ with
  | top => exact absurd rfl hfin
  | coe s =>
    filter_upwards [eventually_ge_atTop ⌈s⌉₊] with n hn
    exact min_eq_right (WithTop.coe_le_coe.mpr ((Nat.le_ceil s).trans (Nat.cast_le.mpr hn)))

private theorem monotone_untopA_min_nat (τ : WithTop ℝ≥0) :
    Monotone fun n : ℕ ↦ ((min ((n : ℝ≥0) : WithTop ℝ≥0) τ).untopA : ℝ) := by
  intro m n hmn
  cases τ with
  | top =>
    simp only [le_top, min_eq_left, WithTop.untopA, WithTop.untopD_coe, NNReal.coe_le_coe,
      Nat.cast_le, hmn]
  | coe s =>
    change ((min (m : ℝ≥0) s : ℝ≥0) : ℝ) ≤ ((min (n : ℝ≥0) s : ℝ≥0) : ℝ)
    exact NNReal.coe_le_coe.mpr (min_le_min_right s (Nat.cast_le.mpr hmn))

private theorem integrable_untopA_min_const {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {τ : Ω → WithTop ℝ≥0} (hτ : Measurable τ) (T : ℝ≥0) :
    Integrable (fun ω ↦ ((min (T : WithTop ℝ≥0) (τ ω)).untopA : ℝ)) P := by
  refine Integrable.of_bound
    (measurable_subtype_coe.comp (measurable_const.min hτ).untopA).aestronglyMeasurable T
    (.of_forall fun ω ↦ ?_)
  cases hq : min (T : WithTop ℝ≥0) (τ ω) with
  | top => exact absurd hq (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))
  | coe s =>
    simp only [WithTop.untopA, WithTop.untopD_coe, Real.norm_eq_abs,
      abs_of_nonneg (NNReal.coe_nonneg s), NNReal.coe_le_coe,
      WithTop.coe_le_coe.mp (hq ▸ min_le_left _ _)]

private theorem martingale_stoppedProcess_of_continuous {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) (hMc : ∀ ω, Continuous (M · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    Martingale (stoppedProcess M τ) ℱ P :=
  hM.stoppedProcess_of_ae_isRightContinuous
    (hM.stronglyAdapted.isStronglyProgressive_of_isRightContinuous fun ω ↦
      (hMc ω).isRightContinuous)
    (.of_forall fun ω ↦ (hMc ω).isRightContinuous) hτ

private theorem integral_stoppedProcess_eq_zero_of_continuous {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ P) (hMc : ∀ ω, Continuous (M · ω)) (hM0 : ∀ ω, M 0 ω = 0)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) :
    ∫ ω, stoppedProcess M τ T ω ∂P = 0 := by
  have heq := (martingale_stoppedProcess_of_continuous hM hMc hτ).setIntegral_eq
    (zero_le : (0 : ℝ≥0) ≤ T) (@MeasurableSet.univ Ω (ℱ 0))
  have h0 (ω : Ω) : stoppedProcess M τ 0 ω = 0 := by
    have hm : min ((0 : ℝ≥0) : WithTop ℝ≥0) (τ ω) = (0 : ℝ≥0) := min_eq_left bot_le
    simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, hm, WithTop.untopA,
      WithTop.untopD_coe, hM0 ω]
  simpa only [Measure.restrict_univ, h0, integral_zero] using heq.symm

private theorem martingale_stoppedProcess_intervalExit {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω)) (x a b : ℝ) :
    Martingale (stoppedProcess W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0))
      (Filtration.natural W hWm) P :=
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  martingale_stoppedProcess_of_continuous
    (hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm).martingale hWc
    (isStoppingTime_intervalExit hWm hWc x a b)

private theorem integral_min_intervalExit_eq_integral_sq {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
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
  have hM0 (ω : Ω) : M 0 ω = 0 := by simp [M, hW0 ω]
  have hstop := martingale_stoppedProcess_of_continuous hWF.martingale_sq_sub hMc hτ
  let u : Ω → ℝ := fun ω ↦ ((min (T : WithTop ℝ≥0) (τ ω)).untopA : ℝ)
  have hsq_eq : (fun ω ↦ stoppedProcess W τ T ω ^ 2) = fun ω ↦ stoppedProcess M τ T ω + u ω :=
    funext fun _ ↦ by
      simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, M, u, sub_add_cancel]
  rw [hsq_eq, integral_add (hstop.integrable T)
    (integrable_untopA_min_const (measurable_intervalExit hWm hWc x a b) T),
    integral_stoppedProcess_eq_zero_of_continuous hWF.martingale_sq_sub hMc hM0 hτ T, zero_add]

private theorem integral_stoppedValue_intervalExit_eq_zero {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    ∫ ω, stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0) ω ∂P = 0 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  have hWF := hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hWm
  have hstop := martingale_stoppedProcess_intervalExit hW hWm hWc x a b
  have hlim : Tendsto (fun n : ℕ ↦ ∫ ω, stoppedProcess W τ (n : ℝ≥0) ω ∂P) atTop
      (𝓝 (∫ ω, stoppedValue W τ ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ max |a - x| |b - x|)
      (fun n ↦ (hstop.integrable (n : ℝ≥0)).aestronglyMeasurable) (integrable_const _)
      (fun n ↦ .of_forall (norm_stoppedProcess_le_of_mem_Icc hWc hW0 hx (n : ℝ≥0)))
      ((intervalExit_ne_top hW x a b).mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
        ((eventually_min_nat_eq hfin).mono fun _ hn ↦ by
          simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, τ, hn]))
  exact tendsto_nhds_unique hlim ((tendsto_const_nhds (x := (0 : ℝ))).congr fun n ↦
    (integral_stoppedProcess_eq_zero_of_continuous hWF.martingale hWc hW0
      (isStoppingTime_intervalExit hWm hWc x a b) (n : ℝ≥0)).symm)

private theorem integrable_intervalExit_of_mem_Icc {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
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
    (.of_forall fun ω _ _ hmn ↦ ENNReal.ofReal_le_ofReal (monotone_untopA_min_nat (τ ω) hmn))
    ((intervalExit_ne_top hW x a b).mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((eventually_min_nat_eq hfin).mono fun _ hn ↦ by dsimp only [u, τ]; rw [hn]))
  have hstop := martingale_stoppedProcess_intervalExit hW hWm hWc x a b
  have hlin_le (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (u n ω) ∂P ≤ ENNReal.ofReal (C ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_untopA_min_const hτ_meas (n : ℝ≥0))
        (.of_forall fun _ ↦ NNReal.coe_nonneg _),
      integral_min_intervalExit_eq_integral_sq hW hWm hWc hW0 x a b (n : ℝ≥0)]
    have hsq_le := sq_stoppedProcess_le_of_mem_Icc hWc hW0 hx (n : ℝ≥0)
    have hsq_int : Integrable (fun ω ↦ stoppedProcess W τ (n : ℝ≥0) ω ^ 2) P :=
      Integrable.of_bound ((hstop.integrable (n : ℝ≥0)).aestronglyMeasurable.pow 2) (C ^ 2)
        (.of_forall fun ω ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq_le ω)
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono hsq_int (integrable_const (C ^ 2)) hsq_le
  refine ⟨(measurable_subtype_coe.comp hτ_meas.untopA).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_congr fun _ ↦ Real.eNorm_eq_ofReal (NNReal.coe_nonneg _)]
  exact (le_of_tendsto hlin_tend (.of_forall hlin_le)).trans_lt ENNReal.ofReal_lt_top

private theorem measurable_stoppedValue_intervalExit {Ω : Type*} {_ : MeasurableSpace Ω}
    {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (x a b : ℝ) :
    Measurable (stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0)) := by
  have hτ := isStoppingTime_intervalExit hWm hWc x a b
  have hprog := (Filtration.stronglyAdapted_natural hWm).isStronglyProgressive_of_isRightContinuous
    fun ω ↦ (hWc ω).isRightContinuous
  exact (measurable_stoppedValue hprog hτ).mono hτ.measurableSpace_le le_rfl

private theorem integrable_stoppedValue_intervalExit {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    Integrable (stoppedValue W (hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0)) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact Integrable.of_bound
    (measurable_stoppedValue_intervalExit hWm hWc x a b).aestronglyMeasurable (max |a - x| |b - x|)
    ((intervalExit_ne_top hW x a b).mono fun _ ↦ norm_stoppedValue_le_of_mem_Icc hWc hW0 hx)

private theorem integral_intervalExit_eq_of_mem_Icc {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {x a b : ℝ} (hx : x ∈ Icc a b) :
    ∫ ω, ((hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P =
      (x - a) * (b - x) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + W t ω) (Ioo a b)ᶜ 0
  have hτ_meas := measurable_intervalExit hWm hWc x a b
  have hfin_ae := intervalExit_ne_top hW x a b
  have hlim_u := integral_tendsto_of_tendsto_of_monotone
    (fun n ↦ integrable_untopA_min_const hτ_meas (n : ℝ≥0))
    (integrable_intervalExit_of_mem_Icc hW hWm hWc hW0 hx)
    (.of_forall fun ω ↦ monotone_untopA_min_nat (τ ω))
    (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
      ((eventually_min_nat_eq hfin).mono fun _ hn ↦ by rw [hn]))
  have hstop := martingale_stoppedProcess_intervalExit hW hWm hWc x a b
  have hlim_sq : Tendsto (fun n : ℕ ↦ ∫ ω, stoppedProcess W τ (n : ℝ≥0) ω ^ 2 ∂P) atTop
      (𝓝 (∫ ω, stoppedValue W τ ω ^ 2 ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ max |a - x| |b - x| ^ 2)
      (fun n ↦ (hstop.integrable (n : ℝ≥0)).aestronglyMeasurable.pow 2) (integrable_const _)
      (fun n ↦ .of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_stoppedProcess_le_of_mem_Icc hWc hW0 hx (n : ℝ≥0) ω)
      (hfin_ae.mono fun ω hfin ↦ tendsto_nhds_of_eventually_eq
        ((eventually_min_nat_eq hfin).mono fun _ hn ↦ by
          simp only [stoppedProcess_eq_stoppedValue_apply, stoppedValue, τ, hn]))
  have heq_U_sq : ∫ ω, ((τ ω).untopA : ℝ) ∂P = ∫ ω, stoppedValue W τ ω ^ 2 ∂P :=
    tendsto_nhds_unique hlim_u (hlim_sq.congr fun n ↦
      (integral_min_intervalExit_eq_integral_sq hW hWm hWc hW0 x a b (n : ℝ≥0)).symm)
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
    integral_add (integrable_const _)
      ((integrable_stoppedValue_intervalExit hW hWm hWc hW0 hx).const_mul _),
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
    hB.hittingAfter_Ioi_ae_eq_Ici (b - x)] with _ h₁ h₂
  simp only [Pi.inf_apply, h₁, h₂]

/-- A real Brownian motion started at `x` exits every open interval `(a, b)` in finite time almost
surely. -/
theorem hittingAfter_compl_Ioo_ne_top (hB : IsBrownianReal B P) (x a b : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω ≠ ⊤ :=
  intervalExit_ne_top hB x a b

/-- When the starting point `x` lies outside `(a, b)`, the first exit time of `x + B` from
`(a, b)` is almost surely `0`. -/
theorem hittingAfter_compl_Ioo_ae_eq_zero_of_notMem (hB : IsBrownianReal B P) {x a b : ℝ}
    (hx : x ∉ Ioo a b) :
    hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 =ᵐ[P] 0 := by
  obtain ⟨W, _, _, hW0, _, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  refine ((hWB.symm.comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0).trans (.of_forall fun ω ↦ ?_)
  exact le_antisymm
    (hittingAfter_le_of_mem le_rfl (by simpa only [hW0 ω, add_zero, mem_compl_iff] using hx)) bot_le

/-- Starting from `x ∈ [a, b]`, the position of `x + B` at its first exit from `(a, b)` equals
either `a` or `b` almost surely. -/
theorem eval_hittingAfter_compl_Ioo_eq_or_eq (hB : IsBrownianReal B P) {x a b : ℝ}
    (hx : x ∈ Icc a b) :
    ∀ᵐ ω ∂P,
      x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a ∨
        x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b := by
  obtain ⟨W, _, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  filter_upwards [hWB, (hWB.comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0,
    hW.hittingAfter_compl_Ioo_ne_top x a b] with ω hω hτ hfin
  rw [← hτ, ← hω]
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
  have hset_ae : {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = b}
      =ᵐ[P] Z ⁻¹' {b} := by
    filter_upwards [hWB, (hWB.comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0] with _ hω hτ
    simp only [mem_preimage, mem_singleton_iff, Z, stoppedValue, τ, ← hτ, hω]
  have hind_eq : (fun ω ↦ Z ω - a) =ᵐ[P] fun ω ↦ (b - a) * (Z ⁻¹' {b}).indicator 1 ω := by
    filter_upwards [hW.eval_hittingAfter_compl_Ioo_eq_or_eq hx] with ω hω
    change Z ω = a ∨ Z ω = b at hω
    rcases hω with hZa | hZb
    · rw [indicator_of_notMem (fun h ↦ hab.ne (hZa.symm.trans h)), mul_zero, hZa, sub_self]
    · rw [indicator_of_mem hZb, Pi.one_apply, mul_one, hZb]
  have hint := integral_congr_ae hind_eq
  have hlhs : ∫ ω, (Z ω - a) ∂P = x - a := by
    have hsub : (fun ω ↦ Z ω - a) = fun ω ↦ (x - a) + stoppedValue W τ ω := by ext; simp [Z]; ring
    rw [hsub, integral_add (integrable_const _)
        (integrable_stoppedValue_intervalExit hW hWm hWc hW0 hx),
      integral_const, probReal_univ, one_smul,
      integral_stoppedValue_intervalExit_eq_zero hW hWm hWc hW0 hx, add_zero]
  rw [integral_const_mul, integral_indicator_one (hZ_meas (measurableSet_singleton b)),
    hlhs] at hint
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
    have hfun : (fun t ω ↦ -x + (-B) t ω) = fun t ω ↦ -(x + B t ω) := by ext; simp [add_comm]
    have hpre : (fun y : ℝ ↦ -y) ⁻¹' (Ioo (-b) (-a))ᶜ = (Ioo a b)ᶜ := by
      ext y; simp only [mem_preimage, mem_compl_iff, mem_Ioo, neg_lt_neg_iff, and_comm]
    rw [hfun, hittingAfter_comp (fun y : ℝ ↦ -y), hpre]
  have hset : {ω | -x + (-B) (hittingAfter (fun t ω ↦ -x + (-B) t ω) (Ioo (-b) (-a))ᶜ 0 ω).untopA ω
      = -a} = {ω | x + B (hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA ω = a} := by
    ext ω; rw [mem_ofPred_eq, mem_ofPred_eq, hτ, Pi.neg_apply, Pi.neg_apply]
    constructor <;> intro h <;> linarith
  rw [hset] at hneg
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
    refine (integrable_intervalExit_of_mem_Icc hW hWm hWc hW0 (Ioo_subset_Icc_self hx)).congr ?_
    exact ((hWB.comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0).mono fun _ hω ↦ by simp only [hω]
  · refine (integrable_zero Ω ℝ P).congr ?_
    exact (hB.hittingAfter_compl_Ioo_ae_eq_zero_of_notMem hx).mono fun _ hω ↦ by simp [hω]

/-- **Mean exit time of Brownian motion from `(a, b)`**: for `a ≤ b` and all `x : ℝ`,
`∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P =`
`max 0 ((x - a) * (b - x))`. -/
theorem integral_hittingAfter_compl_Ioo (hB : IsBrownianReal B P) (x : ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ ω, ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ) ∂P =
      max 0 ((x - a) * (b - x)) := by
  by_cases hx : x ∈ Ioo a b
  · obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
    have hBW := ((hWB.symm.comp (x + ·)).hittingAfter_ae_eq (Ioo a b)ᶜ 0).mono fun _ hω ↦
      congrArg (fun q : WithTop ℝ≥0 ↦ (q.untopA : ℝ)) hω
    rw [integral_congr_ae hBW,
      integral_intervalExit_eq_of_mem_Icc hW hWm hWc hW0 (Ioo_subset_Icc_self hx),
      max_eq_right (mul_nonneg (sub_nonneg.mpr hx.1.le) (sub_nonneg.mpr hx.2.le))]
  · have hnonpos : (x - a) * (b - x) ≤ 0 := by
      rcases le_or_gt x a with hxa | hax
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxa) (sub_nonneg.mpr (hxa.trans hab))
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hax.le)
          (sub_nonpos.mpr (not_lt.mp fun hxb ↦ hx ⟨hax, hxb⟩))
    have hz : (fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) (Ioo a b)ᶜ 0 ω).untopA : ℝ))
        =ᵐ[P] 0 :=
      (hB.hittingAfter_compl_Ioo_ae_eq_zero_of_notMem hx).mono fun _ hω ↦ by simp [hω]
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
