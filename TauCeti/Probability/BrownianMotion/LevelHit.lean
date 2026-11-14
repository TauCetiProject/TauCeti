/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.HittingTime
public import TauCeti.Analysis.SpecialFunctions.Erf.Basic
public import TauCeti.Probability.Distributions.Levy.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Probability.CDF
import TauCeti.Probability.BrownianMotion.Reflection
import TauCeti.Probability.BrownianMotion.Version
import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Probability.Distributions.Levy.Cdf
import TauCeti.Probability.Distributions.Levy.Transforms
import TauCeti.Probability.Process.HittingTime
import TauCeti.Probability.Process.HittingTime.Countable

/-!
# One-dimensional Brownian level-hitting times and Laplace transforms

For a real Brownian motion `B` and starting position `x : ℝ`, let
`τ_a ω = hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω` be the first hitting time of `{a}`.
Combining path continuity on a measurable modification with the reflection principle gives:

1. **Immediate level crossing** (`ProbabilityTheory.IsBrownianReal.hittingAfter_Ioi_ae_eq_Ici`,
   `ProbabilityTheory.IsBrownianReal.hittingAfter_Iio_ae_eq_Iic`): `hittingAfter B (Ioi a) 0`
   agrees almost surely with `hittingAfter B (Ici a) 0` (and `Iio a` with `Iic a`).
2. **Reflection cumulative distribution function**
   (`ProbabilityTheory.IsBrownianReal.measure_hittingAfter_singleton_le`,
   `ProbabilityTheory.IsBrownianReal.measureReal_hittingAfter_singleton_le`): for `x ≠ a`,
   `P {ω | τ_a ω ≤ t} = 2 * P {ω | |a - x| ≤ B t ω}`, and for `t ≠ 0`,
   `P.real {ω | τ_a ω ≤ t} = erfc (|a - x| / √(2 * t))`.
3. **Almost-sure recurrence of levels and exits from proper subsets**
   (`ProbabilityTheory.IsBrownianReal.ae_hittingAfter_singleton_ne_top`,
   `ProbabilityTheory.IsBrownianReal.ae_hittingAfter_compl_ne_top`): `τ_a ω ≠ ⊤` almost surely for
   all `x, a : ℝ`, hence `hittingAfter (fun t ω ↦ x + B t ω) Aᶜ 0 ω ≠ ⊤` almost surely whenever
   `A ≠ univ`.
4. **Exact Lévy law and Laplace transform**
   (`ProbabilityTheory.IsBrownianReal.hasLaw_hittingAfter_singleton`,
   `ProbabilityTheory.IsBrownianReal.hasLaw_hittingAfter_singleton_self`,
   `ProbabilityTheory.IsBrownianReal.integral_exp_neg_mul_hittingAfter_singleton`): `(τ_a ω).untopA`
   has law `levyMeasure 0 ((a - x) ^ 2)` for `x ≠ a` and `Measure.dirac 0` for `x = a`, with
   Laplace transform `∫ ω, exp (-θ * (τ_a ω).untopA) ∂P = exp (-√(2 * θ) * |a - x|)` for `θ ≥ 0`.

## References

* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., §2.8.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Pointwise

namespace TauCeti.Probability

private theorem hittingAfter_Ioi_ae_eq_Ici_of_pos {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {a : ℝ} (ha : 0 < a) :
    hittingAfter W (Ioi a) 0 =ᵐ[P] hittingAfter W (Ici a) 0 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ₁ := hittingAfter W (Ici a) 0
  let τ₂ := hittingAfter W (Ioi a) 0
  have hτ₂_meas : Measurable τ₂ :=
    measurable_hittingAfter_of_isOpen (fun t ↦ (hWm t).measurable) hWc isOpen_Ioi 0
  have hstep (t : ℝ≥0) : ∀ᵐ ω ∂P, τ₁ ω ≤ t → τ₂ ω ≤ t := by
    have hST : {ω | τ₂ ω ≤ t} ⊆ {ω | τ₁ ω ≤ t} :=
      fun ω hω ↦ (hittingAfter_apply_anti W 0 ω Ioi_subset_Ici_self).trans hω
    have hT_eq : {ω | τ₁ ω ≤ t} = {ω | ∃ s ≤ t, a ≤ W s ω} := by
      ext ω; simp only [τ₁, mem_ofPred_eq, isClosed_Ici.hittingAfter_le_iff (hWc ω), mem_Icc,
        zero_le, true_and, mem_Ici]
    have hWt_eq : P {ω | a ≤ W t ω} = P {ω | a < W t ω} := by
      rcases eq_or_ne t 0 with rfl | ht0
      · rw [show {ω | a ≤ W 0 ω} = ∅ by ext ω; simp [hW0 ω, ha.not_ge],
          show {ω | a < W 0 ω} = ∅ by ext ω; simp [hW0 ω, ha.not_gt]]
      · have := nullSingletonClass_gaussianReal (μ := 0) ht0
        exact ((hW.hasLaw_eval t).measure_eq (p := (· ∈ Ici a)) measurableSet_Ici).trans
          ((measure_congr Ioi_ae_eq_Ici.symm).trans
            ((hW.hasLaw_eval t).measure_eq (p := (· ∈ Ioi a)) measurableSet_Ioi).symm)
    have hle : P {ω | τ₁ ω ≤ t} ≤ P {ω | τ₂ ω ≤ t} := by
      rw [hT_eq, hW.measure_exists_le_ge t ha, hWt_eq, ← hW.measure_exists_le_gt t ha.le]
      exact measure_mono fun ω ⟨s, hst, hs⟩ ↦
        (hittingAfter_le_of_mem bot_le hs).trans (WithTop.coe_le_coe.mpr hst)
    exact (ae_eq_of_subset_of_measure_ge hST hle
      (measurableSet_Iic.preimage hτ₂_meas).nullMeasurableSet
        (measure_ne_top P _)).mem_iff.mono fun _ ↦ Iff.mpr
  filter_upwards [ae_all_iff.mpr fun k ↦ hstep (TopologicalSpace.denseSeq ℝ≥0 k)] with ω hω
  refine le_antisymm (le_of_forall_gt fun b hb ↦ ?_)
    (hittingAfter_apply_anti W 0 ω Ioi_subset_Ici_self)
  obtain ⟨u, h₁u, hub⟩ := WithTop.lt_iff_exists_coe_btwn.mp hb
  obtain ⟨v, huv, hvb⟩ := WithTop.lt_iff_exists_coe_btwn.mp hub
  obtain ⟨k, hk₁, hk₂⟩ := (TopologicalSpace.denseRange_denseSeq ℝ≥0).exists_mem_open isOpen_Ioo
    (nonempty_Ioo.mpr (WithTop.coe_lt_coe.mp huv))
  exact (hω k (h₁u.le.trans (WithTop.coe_le_coe.mpr hk₁.le))).trans_lt
    ((WithTop.coe_lt_coe.mpr hk₂).trans hvb)

end TauCeti.Probability

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- First entrance of a real Brownian motion from any starting time `u` into any closed set is
almost-everywhere measurable, without assuming completeness of the ambient measurable space. -/
theorem aemeasurable_hittingAfter_of_isClosed (hB : IsBrownianReal B P) {s : Set ℝ}
    (hs : IsClosed s) (u : ℝ≥0) : AEMeasurable (hittingAfter B s u) P :=
  MeasureTheory.aemeasurable_hittingAfter_of_isClosed
    (fun t ↦ (hB.integrable_eval t).aestronglyMeasurable) hB.cont hs u

/-- First entrance of a real Brownian motion from any starting time `u` into any open set is
almost-everywhere measurable, without assuming completeness of the ambient measurable space. -/
theorem aemeasurable_hittingAfter_of_isOpen (hB : IsBrownianReal B P) {s : Set ℝ}
    (hs : IsOpen s) (u : ℝ≥0) : AEMeasurable (hittingAfter B s u) P :=
  MeasureTheory.aemeasurable_hittingAfter_of_isOpen
    (fun t ↦ (hB.integrable_eval t).aemeasurable) hB.cont hs u

/-- **Immediate upward level crossing**: for every real threshold `a`, a real Brownian motion
enters `(a, ∞)` at the same time it enters `[a, ∞)` almost surely. -/
theorem hittingAfter_Ioi_ae_eq_Ici (hB : IsBrownianReal B P) (a : ℝ) :
    hittingAfter B (Ioi a) 0 =ᵐ[P] hittingAfter B (Ici a) 0 := by
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  refine (hWB.symm.hittingAfter_ae_eq (Ioi a) 0).trans
    (Filter.EventuallyEq.trans ?_ (hWB.hittingAfter_ae_eq (Ici a) 0))
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · exact .of_forall fun ω ↦
      (le_antisymm (hittingAfter_le_of_mem le_rfl (by simpa [hW0 ω] using ha)) bot_le).trans
        (le_antisymm (hittingAfter_le_of_mem le_rfl (by simpa [hW0 ω] using ha.le)) bot_le).symm
  · exact hW.hittingAfter_Ioi_zero_ae_eq_zero.mono fun ω hω ↦ hω.trans
      (le_antisymm (hittingAfter_le_of_mem le_rfl (by simp [hW0 ω])) bot_le).symm
  · exact hittingAfter_Ioi_ae_eq_Ici_of_pos hW hWm hWc hW0 ha

/-- **Immediate downward level crossing**: for every real threshold `a`, a real Brownian motion
enters `(-∞, a)` at the same time it enters `(-∞, a]` almost surely. -/
theorem hittingAfter_Iio_ae_eq_Iic (hB : IsBrownianReal B P) (a : ℝ) :
    hittingAfter B (Iio a) 0 =ᵐ[P] hittingAfter B (Iic a) 0 := by
  simpa only [hittingAfter_neg, Set.neg_preimage, Set.neg_Ioi, Set.neg_Ici, neg_neg] using
    hB.neg.hittingAfter_Ioi_ae_eq_Ici (-a)

/-- When the Brownian path starts at `x`, its hitting time of `{x}` is almost surely `0`. -/
theorem hittingAfter_singleton_self_ae_eq_zero (hB : IsBrownianReal B P) (x : ℝ) :
    hittingAfter (fun t ω ↦ x + B t ω) {x} 0 =ᵐ[P] 0 := by
  obtain ⟨W, _, _, hW0, _, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  exact ((hWB.symm.fun_comp (x + ·)).hittingAfter_ae_eq {x} 0).trans (.of_forall fun ω ↦
    le_antisymm (hittingAfter_le_of_mem le_rfl (by simp [hW0 ω])) bot_le)

/-- For `x ≤ a`, the hitting time of `{a}` by `x + B` agrees almost surely with that of `[a, ∞)`. -/
theorem hittingAfter_singleton_ae_eq_Ici (hB : IsBrownianReal B P) {x a : ℝ} (hxa : x ≤ a) :
    hittingAfter (fun t ω ↦ x + B t ω) {a} 0 =ᵐ[P]
      hittingAfter (fun t ω ↦ x + B t ω) (Ici a) 0 := by
  obtain ⟨W, _, hWc, hW0, _, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  refine ((hWB.symm.fun_comp (x + ·)).hittingAfter_ae_eq {a} 0).trans
    (Filter.EventuallyEq.trans ?_ ((hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Ici a) 0))
  exact .of_forall fun ω ↦ ((continuous_const_add x).comp (hWc ω)).hittingAfter_singleton_eq_Ici
    (by simpa only [hW0 ω, add_zero] using hxa)

/-- For `a ≤ x`, the hitting time of `{a}` by `x + B` agrees almost surely with that of `(-∞, a]`.
-/
theorem hittingAfter_singleton_ae_eq_Iic (hB : IsBrownianReal B P) {x a : ℝ} (hax : a ≤ x) :
    hittingAfter (fun t ω ↦ x + B t ω) {a} 0 =ᵐ[P]
      hittingAfter (fun t ω ↦ x + B t ω) (Iic a) 0 := by
  obtain ⟨W, _, hWc, hW0, _, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  refine ((hWB.symm.fun_comp (x + ·)).hittingAfter_ae_eq {a} 0).trans
    (Filter.EventuallyEq.trans ?_ ((hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Iic a) 0))
  exact .of_forall fun ω ↦ ((continuous_const_add x).comp (hWc ω)).hittingAfter_singleton_eq_Iic
    (by simpa only [hW0 ω, add_zero] using hax)

private theorem measure_hittingAfter_singleton_le_of_lt (hB : IsBrownianReal B P) {x a : ℝ}
    (hxa : x < a) (t : ℝ≥0) :
    P {ω | hittingAfter (fun s ω ↦ x + B s ω) {a} 0 ω ≤ t} = 2 * P {ω | |a - x| ≤ B t ω} := by
  obtain ⟨W, _, hWc, _, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  have hsub : 0 < a - x := sub_pos.mpr hxa
  have hτ : hittingAfter (fun s ω ↦ x + B s ω) {a} 0 =ᵐ[P] hittingAfter W (Ici (a - x)) 0 := by
    refine (hB.hittingAfter_singleton_ae_eq_Ici hxa.le).trans ?_
    rw [hittingAfter_comp (x + ·), preimage_const_add_Ici]
    exact hWB.symm.hittingAfter_ae_eq _ 0
  have heq₁ : {ω | hittingAfter (fun s ω ↦ x + B s ω) {a} 0 ω ≤ t} =ᵐ[P]
      {ω | ∃ s ≤ t, a - x ≤ W s ω} := hτ.mono fun ω hω ↦
    (congrArg (· ≤ (t : WithTop ℝ≥0)) hω).to_iff.trans <| by
      simp only [mem_ofPred_eq, isClosed_Ici.hittingAfter_le_iff (hWc ω), mem_Icc, zero_le,
        true_and, mem_Ici]
  have heq₂ : {ω | a - x ≤ W t ω} =ᵐ[P] {ω | |a - x| ≤ B t ω} :=
    (hWB.ae_eq_eval t).mono fun _ hω ↦ by simp only [mem_ofPred_eq, hω, abs_of_pos hsub]
  rw [measure_congr heq₁, hW.measure_exists_le_ge t hsub, measure_congr heq₂]

/-- **Reflection formula for the Brownian level-hitting time**: for `x ≠ a` and `t ≥ 0`
(including `t = 0`, where both sides vanish), the probability that `x + B` hits `a` by time `t`
equals `2 * P {ω | |a - x| ≤ B t ω}`. -/
theorem measure_hittingAfter_singleton_le (hB : IsBrownianReal B P) {x a : ℝ} (hx : x ≠ a)
    (t : ℝ≥0) :
    P {ω | hittingAfter (fun s ω ↦ x + B s ω) {a} 0 ω ≤ t} = 2 * P {ω | |a - x| ≤ B t ω} := by
  rcases hx.lt_or_gt with hxa | hax
  · exact measure_hittingAfter_singleton_le_of_lt hB hxa t
  · have hneg := measure_hittingAfter_singleton_le_of_lt hB.neg (neg_lt_neg hax) t
    have hτ : hittingAfter (fun s ω ↦ -x + (-B) s ω) {-a} 0 =
        hittingAfter (fun s ω ↦ x + B s ω) {a} 0 := by
      have hfun : (fun s ω ↦ -x + (-B) s ω) = -(fun s ω ↦ x + B s ω) := by ext s ω; simp [add_comm]
      rw [hfun, hittingAfter_neg, Set.neg_preimage, Set.neg_singleton, neg_neg]
    have hlaw : P {ω | |a - x| ≤ (-B) t ω} = P {ω | |a - x| ≤ B t ω} :=
      ((hB.neg.hasLaw_eval t).measure_eq (p := (|a - x| ≤ ·)) measurableSet_Ici).trans
        ((hB.hasLaw_eval t).measure_eq (p := (|a - x| ≤ ·)) measurableSet_Ici).symm
    rwa [hτ, neg_sub_neg, abs_sub_comm, hlaw] at hneg

/-- Real-valued complementary-error-function formula for the Brownian level-hitting cumulative
distribution function at positive time `t ≠ 0` when `x ≠ a`. -/
theorem measureReal_hittingAfter_singleton_le (hB : IsBrownianReal B P) {x a : ℝ} (hx : x ≠ a)
    {t : ℝ≥0} (ht : t ≠ 0) :
    P.real {ω | hittingAfter (fun s ω ↦ x + B s ω) {a} 0 ω ≤ t} =
      TauCeti.Real.erfc (|a - x| / √(2 * (t : ℝ))) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have := nullSingletonClass_gaussianReal (μ := 0) ht
  have hlaw : P {ω | |a - x| ≤ B t ω} = gaussianReal 0 t (Ioi |a - x|) :=
    ((hB.hasLaw_eval t).measure_eq (p := (|a - x| ≤ ·)) measurableSet_Ici).trans
      (measure_congr (μ := gaussianReal 0 t) (Ioi_ae_eq_Ici (a := |a - x|)).symm)
  rw [measureReal_def, hB.measure_hittingAfter_singleton_le hx t, hlaw, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ← measureReal_def, measureReal_Ioi_gaussianReal 0 ht |a - x|, sub_zero]
  ring

/-- **One-dimensional Brownian recurrence of levels**: starting from any `x : ℝ`, the path
`t ↦ x + B t ω` hits every real level `a` in finite time almost surely. -/
theorem ae_hittingAfter_singleton_ne_top (hB : IsBrownianReal B P) (x a : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω ≠ ⊤ := by
  rcases eq_or_ne x a with rfl | hx
  · exact (hB.hittingAfter_singleton_self_ae_eq_zero x).mono fun _ hω ↦ by simp [hω]
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, _, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  let τ := hittingAfter (fun t ω ↦ x + W t ω) {a} 0
  have hτ_meas : Measurable τ :=
    measurable_hittingAfter_of_isClosed (fun t ↦ (measurable_const_add x).comp (hWm t).measurable)
      (fun ω ↦ (continuous_const_add x).comp (hWc ω)) isClosed_singleton 0
  have hinner : Tendsto (fun n : ℕ ↦ |a - x| / √(2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop <| Real.tendsto_sqrt_atTop.comp <|
      Tendsto.const_mul_atTop zero_lt_two (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim : Tendsto (fun n : ℕ ↦ 1 - TauCeti.Real.erfc (|a - x| / √(2 * ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, TauCeti.Real.erfc_zero, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub ((TauCeti.Real.continuous_erfc.tendsto 0).comp hinner)
  have hreal : P.real {ω | τ ω = ⊤} = 0 := le_antisymm (ge_of_tendsto' hlim fun n ↦ by
    have hsub : {ω | τ ω = ⊤} ⊆ {ω | τ ω ≤ (((n : ℝ≥0) + 1 : ℝ≥0) : WithTop ℝ≥0)}ᶜ :=
      fun _ (h : τ _ = ⊤) (hle : τ _ ≤ _) ↦ WithTop.coe_ne_top (top_le_iff.mp (h ▸ hle))
    refine (measureReal_mono hsub).trans_eq ?_
    rw [probReal_compl_eq_one_sub (measurableSet_le hτ_meas measurable_const),
      hW.measureReal_hittingAfter_singleton_le hx (Nat.cast_add_one_ne_zero n)]
    push_cast; rfl) measureReal_nonneg
  have hW_ae : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
    rw [ae_iff]; simp only [Classical.not_not]
    exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right (measure_ne_top P _)
  exact hW_ae.mp (((hWB.fun_comp (x + ·)).hittingAfter_ae_eq {a} 0).mono fun _ h₁ h₂ ↦ h₁ ▸ h₂)

/-- Starting from any `x : ℝ`, a one-dimensional Brownian path exits every proper subset `A ≠ univ`
(i.e. hits `Aᶜ`) in finite time almost surely. -/
theorem ae_hittingAfter_compl_ne_top (hB : IsBrownianReal B P) (x : ℝ) {A : Set ℝ} (hA : A ≠ univ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + B t ω) Aᶜ 0 ω ≠ ⊤ := by
  obtain ⟨y, hy⟩ := nonempty_compl.mpr hA
  exact (hB.ae_hittingAfter_singleton_ne_top x y).mono fun ω hω ↦
    ne_top_of_le_ne_top hω (hittingAfter_apply_anti _ 0 ω (singleton_subset_iff.mpr hy))

/-- When `x ≠ a`, the level-hitting time `(hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω).untopA`
of `x + B` has the Lévy law `levyMeasure 0 ((a - x) ^ 2)`. -/
theorem hasLaw_hittingAfter_singleton (hB : IsBrownianReal B P) {x a : ℝ} (hx : x ≠ a) :
    HasLaw (fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω).untopA : ℝ))
      (levyMeasure 0 ((a - x) ^ 2)) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hc : 0 < (a - x) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx.symm)
  have := isProbabilityMeasure_levyMeasure hc 0
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  let τ := hittingAfter (fun t ω ↦ x + W t ω) {a} 0
  let X : Ω → ℝ := fun ω ↦ ((τ ω).untopA : ℝ)
  have hX_meas : Measurable X := measurable_subtype_coe.comp
    (measurable_hittingAfter_of_isClosed (fun t ↦ (measurable_const_add x).comp (hWm t).measurable)
      (fun ω ↦ (continuous_const_add x).comp (hWc ω)) isClosed_singleton 0).untopA
  have hXB : X =ᵐ[P] fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω).untopA : ℝ) :=
    ((hWB.fun_comp (x + ·)).hittingAfter_ae_eq {a} 0).mono fun _ hω ↦ by simp only [X, τ, hω]
  refine ⟨hX_meas.aemeasurable.congr hXB, (Measure.map_congr hXB.symm).trans ?_⟩
  have : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX_meas.aemeasurable).mpr ‹_›
  refine Measure.eq_of_cdf _ _ (StieltjesFunction.ext fun u ↦ ?_)
  rw [cdf_eq_real, map_measureReal_apply hX_meas measurableSet_Iic, cdf_levyMeasure_eq hc 0 u]
  have hae (t : ℝ≥0) : X ⁻¹' Iic (t : ℝ) =ᵐ[P] {ω | τ ω ≤ t} := by
    filter_upwards [hW.ae_hittingAfter_singleton_ne_top x a] with ω hfin
    cases hτ : τ ω with
    | top => exact absurd hτ hfin
    | coe v =>
      simp only [mem_preimage, mem_Iic, X, hτ, WithTop.untopA, WithTop.untopD_coe,
        NNReal.coe_le_coe, WithTop.coe_le_coe]
  by_cases hu : u ≤ 0
  · rw [ite_eq_left hu]
    rcases hu.lt_or_eq with hlt | rfl
    · rw [eq_empty_of_forall_notMem (s := X ⁻¹' Iic u) fun ω hω ↦
        (hlt.trans_le (NNReal.coe_nonneg _)).not_ge hω, measureReal_empty]
    · have hz : P {ω | τ ω ≤ (0 : ℝ≥0)} = 0 := by
        rw [hW.measure_hittingAfter_singleton_le hx 0, show {ω | |a - x| ≤ W 0 ω} = ∅ by
          ext ω; simp [hW0 ω, (abs_pos.mpr (sub_ne_zero.mpr hx.symm)).not_ge],
          measure_empty, mul_zero]
      rw [← NNReal.coe_zero, measureReal_congr (hae 0), measureReal_def, hz, ENNReal.toReal_zero,
        NNReal.coe_zero]
  · rw [ite_eq_right hu]
    lift u to ℝ≥0 using (not_le.mp hu).le with t
    have ht : t ≠ 0 := fun h0 ↦ hu (by simp [h0])
    rw [measureReal_congr (hae t), hW.measureReal_hittingAfter_singleton_le hx ht]
    congr 1; rw [sub_zero, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- At `a = x`, the level-hitting time `(hittingAfter (fun t ω ↦ x + B t ω) {x} 0 ω).untopA`
has law `Measure.dirac 0`. -/
theorem hasLaw_hittingAfter_singleton_self (hB : IsBrownianReal B P) (x : ℝ) :
    HasLaw (fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) {x} 0 ω).untopA : ℝ))
      (Measure.dirac 0) P :=
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  hasLaw_dirac_of_ae_eq ((hB.hittingAfter_singleton_self_ae_eq_zero x).mono fun _ hω ↦ by simp [hω])

/-- **Laplace transform of the Brownian level-hitting time**: for all `x, a : ℝ` and `θ ≥ 0`
(including `θ = 0` and `x = a`), `∫ ω, exp (-θ * (τ_a ω).untopA) ∂P = exp (-√(2 * θ) * |a - x|)`.
-/
theorem integral_exp_neg_mul_hittingAfter_singleton (hB : IsBrownianReal B P) (x a : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (-θ * ((hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω).untopA : ℝ)) ∂P =
      Real.exp (-√(2 * θ) * |a - x|) := by
  rcases eq_or_ne x a with rfl | hx
  · simpa only [mgf, zero_mul, sub_self, abs_zero, mul_zero] using
      mgf_dirac (hB.hasLaw_hittingAfter_singleton_self x) (-θ)
  · have hc : 0 < (a - x) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx.symm)
    refine (mgf_of_hasLaw_levyMeasure hc (hB.hasLaw_hittingAfter_singleton hx)
      (neg_nonpos.mpr hθ)).trans ?_
    rw [zero_mul, zero_sub, show -2 * (a - x) ^ 2 * -θ = (2 * θ) * (a - x) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, neg_mul]

end ProbabilityTheory.IsBrownianReal
