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

This file establishes open/closed half-line hit equivalence, level recurrence, finite exit from
proper subsets, and explicit hitting-time distributions and Laplace transforms directly on native
`ProbabilityTheory.IsBrownianReal` (unwrapping finite hitting times via `WithTop.untopA` without
filtration or completeness hypotheses). For `B` a real Brownian motion, `x : ℝ`, and
`τ_a := hittingAfter (fun t ω ↦ x + B t ω) {a} 0`:
* `ProbabilityTheory.IsBrownianReal.hittingAfter_Ioi_ae_eq_Ici` and `hittingAfter_Iio_ae_eq_Iic`
  identify open and closed half-line hitting times almost surely.
* `ProbabilityTheory.IsBrownianReal.measure_hittingAfter_singleton_le` gives
  `P {ω | τ_a ω ≤ t} = 2 * P {ω | |a - x| ≤ B t ω}` for `x ≠ a`, while
  `measureReal_hittingAfter_singleton_le` gives `erfc (|a - x| / √(2 * t))` for all `x, a : ℝ` and
  `t ≠ 0`; this yields `τ_a ω ≠ ⊤` a.s. (`ae_hittingAfter_singleton_ne_top`) and finite exit from
  any `A ≠ univ` (`ae_hittingAfter_compl_ne_top`).
* `ProbabilityTheory.IsBrownianReal.hasLaw_hittingAfter_singleton` establishes the Lévy law
  `levyMeasure 0 ((a - x) ^ 2)` for `x ≠ a` (`Measure.dirac 0` at `x = a` via
  `hasLaw_hittingAfter_singleton_self`), and `integral_exp_neg_mul_hittingAfter_singleton` proves
  the Laplace transform `exp (-√(2 * θ) * |a - x|)` for `θ ≥ 0`.

## References
* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., §2.8.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Pointwise

namespace TauCeti.Probability

private theorem hittingAfter_Ioi_ae_eq_Ici_of_pos {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) (hWc : ∀ ω, Continuous (W · ω)) {a : ℝ} (ha : 0 < a) :
    hittingAfter W (Ioi a) 0 =ᵐ[P] hittingAfter W (Ici a) 0 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τ₁ := hittingAfter W (Ici a) 0; let τ₂ := hittingAfter W (Ioi a) 0
  have hτ₂_meas : Measurable τ₂ :=
    measurable_hittingAfter_of_isOpen (fun t ↦ (hWm t).measurable) hWc isOpen_Ioi 0
  have hstep (t : ℝ≥0) : ∀ᵐ ω ∂P, τ₁ ω ≤ t → τ₂ ω ≤ t := by
    have hST : {ω | τ₂ ω ≤ t} ⊆ {ω | τ₁ ω ≤ t} :=
      fun ω hω ↦ (hittingAfter_apply_anti W 0 ω Ioi_subset_Ici_self).trans hω
    have hτ₁ : {ω | τ₁ ω ≤ t} = {ω | ∃ s ≤ t, a ≤ W s ω} := by
      ext ω; simp only [τ₁, mem_ofPred_eq]; rw [isClosed_Ici.hittingAfter_le_iff (hWc ω)]; simp
    have hle : P {ω | τ₁ ω ≤ t} ≤ P {ω | τ₂ ω ≤ t} := by
      rw [hτ₁, hW.measure_exists_le_ge t ha,
        hW.toIsPreBrownianReal.measure_eval_ge_eq_measure_eval_gt (.inr ha.ne'),
        ← hW.measure_exists_le_gt t ha.le]
      exact measure_mono fun ω ⟨s, hst, hs⟩ ↦
        (hittingAfter_le_of_mem bot_le hs).trans (WithTop.coe_le_coe.mpr hst)
    exact ((ae_eq_of_subset_of_measure_ge hST hle (measurableSet_Iic.preimage
      hτ₂_meas).nullMeasurableSet (measure_ne_top P _)).mem_iff).mono fun _ ↦ Iff.mpr
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
theorem aemeasurable_hittingAfter_of_isOpen (hB : IsBrownianReal B P) {s : Set ℝ} (hs : IsOpen s)
    (u : ℝ≥0) : AEMeasurable (hittingAfter B s u) P :=
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
  · exact hittingAfter_Ioi_ae_eq_Ici_of_pos hW hWm hWc ha

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

/-- For `x ≤ a`, the hitting time of `{a}` by `x + B` agrees almost surely with `[a, ∞)`. -/
theorem hittingAfter_singleton_ae_eq_Ici (hB : IsBrownianReal B P) {x a : ℝ} (hxa : x ≤ a) :
    hittingAfter (fun t ω ↦ x + B t ω) {a} 0 =ᵐ[P]
      hittingAfter (fun t ω ↦ x + B t ω) (Ici a) 0 := by
  obtain ⟨W, _, hWc, hW0, _, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  have hW_eq := funext fun ω ↦ ((continuous_const_add x).comp (hWc ω)).hittingAfter_singleton_eq_Ici
    (X := fun t ω ↦ x + W t ω) (a := 0) (C := a) (by simpa [hW0 ω] using hxa)
  exact ((hWB.symm.fun_comp (x + ·)).hittingAfter_ae_eq {a} 0).trans
    (hW_eq ▸ (hWB.fun_comp (x + ·)).hittingAfter_ae_eq (Ici a) 0)

/-- For `a ≤ x`, the hitting time of `{a}` by `x + B` agrees almost surely with `(-∞, a]`. -/
theorem hittingAfter_singleton_ae_eq_Iic (hB : IsBrownianReal B P) {x a : ℝ} (hax : a ≤ x) :
    hittingAfter (fun t ω ↦ x + B t ω) {a} 0 =ᵐ[P]
      hittingAfter (fun t ω ↦ x + B t ω) (Iic a) 0 := by
  simpa only [hittingAfter_neg_const_add_neg, Set.neg_preimage, Set.neg_singleton,
    Set.neg_Ici, neg_neg] using hB.neg.hittingAfter_singleton_ae_eq_Ici (neg_le_neg hax)

private theorem measure_hittingAfter_singleton_le_of_lt (hB : IsBrownianReal B P) {x a : ℝ}
    (hxa : x < a) (t : ℝ≥0) :
    P {ω | hittingAfter (fun s ω ↦ x + B s ω) {a} 0 ω ≤ t} = 2 * P {ω | |a - x| ≤ B t ω} := by
  obtain ⟨W, _, hWc, _, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  have hsub : 0 < a - x := sub_pos.mpr hxa
  have hτ : hittingAfter (fun s ω ↦ x + B s ω) {a} 0 =ᵐ[P] hittingAfter W (Ici (a - x)) 0 := by
    refine (hB.hittingAfter_singleton_ae_eq_Ici hxa.le).trans ?_
    rw [hittingAfter_comp (f := (x + ·)), preimage_const_add_Ici]
    exact hWB.symm.hittingAfter_ae_eq _ 0
  rw [measure_congr (t := {ω | ∃ s ≤ t, a - x ≤ W s ω}) (eventuallyEqSet_iff.mpr (hτ.mono
      fun ω hω ↦ by simp only [mem_ofPred_eq, hω]; rw [isClosed_Ici.hittingAfter_le_iff (hWc ω)]
                    simp)), hW.measure_exists_le_ge t hsub,
    measure_congr (s := {ω | a - x ≤ W t ω}) (t := {ω | |a - x| ≤ B t ω}) (eventuallyEqSet_iff.mpr
      ((hWB.ae_eq_eval t).mono fun _ hω ↦ by simp only [mem_ofPred_eq, hω, abs_of_pos hsub]))]

/-- **Reflection formula for the Brownian level-hitting time**: for `x ≠ a` and `t ≥ 0`
(including `t = 0`, where both sides vanish), the probability that `x + B` hits `a` by time `t`
equals `2 * P {ω | |a - x| ≤ B t ω}`. -/
theorem measure_hittingAfter_singleton_le (hB : IsBrownianReal B P) {x a : ℝ} (hx : x ≠ a)
    (t : ℝ≥0) : P {ω | hittingAfter (fun s ω ↦ x + B s ω) {a} 0 ω ≤ t} =
      2 * P {ω | |a - x| ≤ B t ω} := by
  rcases hx.lt_or_gt with hxa | hax
  · exact measure_hittingAfter_singleton_le_of_lt hB hxa t
  · have hneg := measure_hittingAfter_singleton_le_of_lt hB.neg (neg_lt_neg hax) t
    have hτ : hittingAfter (fun s ω ↦ -x + (-B) s ω) {-a} 0 =
        hittingAfter (fun s ω ↦ x + B s ω) {a} 0 := by
      rw [hittingAfter_neg_const_add_neg, Set.neg_preimage, Set.neg_singleton, neg_neg]
    rwa [hτ, neg_sub_neg, abs_sub_comm, ((hB.neg.hasLaw_eval t).measure_eq (p := (|a - x| ≤ ·))
      measurableSet_Ici).trans ((hB.hasLaw_eval t).measure_eq (p := (|a - x| ≤ ·))
        measurableSet_Ici).symm] at hneg

/-- Real-valued complementary-error-function formula for the Brownian level-hitting cumulative
distribution function at positive time `t ≠ 0` for all `x, a : ℝ`. -/
theorem measureReal_hittingAfter_singleton_le (hB : IsBrownianReal B P) (x a : ℝ) {t : ℝ≥0}
    (ht : t ≠ 0) : P.real {ω | hittingAfter (fun s ω ↦ x + B s ω) {a} 0 ω ≤ t} =
      TauCeti.Real.erfc (|a - x| / √(2 * (t : ℝ))) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rcases eq_or_ne x a with rfl | hx
  · have huniv : ({ω | hittingAfter (fun s ω ↦ x + B s ω) {x} 0 ω ≤ t} : Set Ω) =ᵐ[P] univ :=
      eventuallyEqSet_univ.mpr ((hB.hittingAfter_singleton_self_ae_eq_zero x).mono fun _ hω ↦
        (hω.trans rfl).trans_le (bot_le : (0 : WithTop ℝ≥0) ≤ t))
    rw [measureReal_congr huniv]; simp [TauCeti.Real.erfc_zero]
  · rw [measureReal_def, hB.measure_hittingAfter_singleton_le hx t,
      hB.toIsPreBrownianReal.measure_eval_ge_eq_measure_eval_gt (.inl ht),
      (hB.hasLaw_eval t).measure_eq (p := (|a - x| < ·)) measurableSet_Ioi, Ioi_def,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← measureReal_def,
      measureReal_Ioi_gaussianReal 0 ht |a - x|, sub_zero]; ring

/-- **One-dimensional Brownian recurrence of levels**: starting from any `x : ℝ`, the path
`t ↦ x + B t ω` hits every real level `a` in finite time almost surely. -/
theorem ae_hittingAfter_singleton_ne_top (hB : IsBrownianReal B P) (x a : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω ≠ ⊤ := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  let τ := hittingAfter (fun t ω ↦ x + B t ω) {a} 0
  have hτ_ae : AEMeasurable τ P := (hittingAfter_comp B (x + ·) {a} 0).symm.subst
    (motive := (AEMeasurable · P)) <| hB.aemeasurable_hittingAfter_of_isClosed
      (isClosed_singleton.preimage (continuous_const_add x)) 0
  have hlim : Tendsto (fun n : ℕ ↦ 1 - TauCeti.Real.erfc (|a - x| / √(2 * ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, TauCeti.Real.erfc_zero, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub ((TauCeti.Real.continuous_erfc.tendsto 0).comp
        (tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop
          zero_lt_two (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)))))
  have hreal : P.real {ω | τ ω = ⊤} = 0 := le_antisymm (ge_of_tendsto' hlim fun n ↦ by
    refine (measureReal_mono (s₂ := (τ ⁻¹' Iic (((n : ℝ≥0) + 1 : ℝ≥0) : WithTop ℝ≥0))ᶜ)
      fun ω h ↦ by simp [mem_ofPred_eq.mp h]).trans_eq ?_
    rw [probReal_compl_eq_one_sub₀ (hτ_ae.nullMeasurable measurableSet_Iic)]
    congr 1; exact (hB.measureReal_hittingAfter_singleton_le x a (Nat.cast_add_one_ne_zero n)).trans
      (by push_cast; rfl)) measureReal_nonneg
  rw [ae_iff]; simp only [Classical.not_not]
  exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right (measure_ne_top P _)

/-- Starting from any `x : ℝ`, a one-dimensional Brownian path exits every proper subset `A ≠ univ`
(i.e. hits `Aᶜ`) in finite time almost surely. -/
theorem ae_hittingAfter_compl_ne_top (hB : IsBrownianReal B P) (x : ℝ) {A : Set ℝ} (hA : A ≠ univ) :
    ∀ᵐ ω ∂P, hittingAfter (fun t ω ↦ x + B t ω) Aᶜ 0 ω ≠ ⊤ :=
  let ⟨y, hy⟩ := nonempty_compl.mpr hA
  (hB.ae_hittingAfter_singleton_ne_top x y).mono fun ω hω ↦
    ne_top_of_le_ne_top hω (hittingAfter_apply_anti _ 0 ω (singleton_subset_iff.mpr hy))

/-- When `x ≠ a`, the level-hitting time `(hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω).untopA`
of `x + B` has the Lévy law `levyMeasure 0 ((a - x) ^ 2)`. -/
theorem hasLaw_hittingAfter_singleton (hB : IsBrownianReal B P) {x a : ℝ} (hx : x ≠ a) :
    HasLaw (fun ω ↦ ((hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω).untopA : ℝ))
      (levyMeasure 0 ((a - x) ^ 2)) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hc : 0 < (a - x) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx.symm)
  have := isProbabilityMeasure_levyMeasure hc 0
  let τ := hittingAfter (fun t ω ↦ x + B t ω) {a} 0; let X : Ω → ℝ := fun ω ↦ ((τ ω).untopA : ℝ)
  have hX_ae : AEMeasurable X P :=
    (NNReal.continuous_coe.measurable.comp
      (measurable_id (α := WithTop ℝ≥0)).untopA).comp_aemeasurable <|
        (hittingAfter_comp B (x + ·) {a} 0).symm.subst (motive := (AEMeasurable · P)) <|
          hB.aemeasurable_hittingAfter_of_isClosed
            (isClosed_singleton.preimage (continuous_const_add x)) 0
  refine ⟨hX_ae, ?_⟩
  have := (Measure.isProbabilityMeasure_map_iff hX_ae).mpr ‹IsProbabilityMeasure P›
  refine Measure.eq_of_cdf _ _ (StieltjesFunction.ext fun u ↦ ?_)
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hX_ae measurableSet_Iic,
    cdf_levyMeasure_eq hc 0 u]
  have hae (t : ℝ≥0) : X ⁻¹' Iic (t : ℝ) =ᵐ[P] {ω | τ ω ≤ t} :=
    eventuallyEqSet_iff.mpr <| (hB.ae_hittingAfter_singleton_ne_top x a).mono fun ω hfin ↦ by
      simp [X, τ, WithTop.untopA_le_iff hfin]
  by_cases hu : u ≤ 0
  · rw [ite_eq_left hu]
    rcases hu.lt_or_eq with hlt | rfl
    · rw [eq_empty_of_forall_notMem (s := X ⁻¹' Iic u) fun ω hω ↦
        (hlt.trans_le (NNReal.coe_nonneg _)).not_ge hω, measureReal_empty]
    · rw [← NNReal.coe_zero, measureReal_congr (hae 0), measureReal_def,
        hB.measure_hittingAfter_singleton_le hx 0,
        (hB.hasLaw_eval 0).measure_eq (p := (|a - x| ≤ ·)) measurableSet_Ici]
      simp [(abs_pos.mpr (sub_ne_zero.mpr hx.symm)).not_ge]
  · rw [ite_eq_right hu]; lift u to ℝ≥0 using (not_le.mp hu).le with t
    rw [measureReal_congr (hae t),
      hB.measureReal_hittingAfter_singleton_le x a fun h0 ↦ hu (by simp [h0])]
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
theorem integral_exp_neg_mul_hittingAfter_singleton (hB : IsBrownianReal B P) (x a : ℝ) {θ : ℝ}
    (hθ : 0 ≤ θ) : ∫ ω, Real.exp (-θ * ((hittingAfter (fun t ω ↦ x + B t ω) {a} 0 ω).untopA : ℝ))
      ∂P = Real.exp (-√(2 * θ) * |a - x|) := by
  rcases eq_or_ne x a with rfl | hx
  · simpa [mgf] using mgf_dirac (hB.hasLaw_hittingAfter_singleton_self x) (-θ)
  · refine (mgf_of_hasLaw_levyMeasure (sq_pos_of_ne_zero (sub_ne_zero.mpr hx.symm))
      (hB.hasLaw_hittingAfter_singleton hx) (neg_nonpos.mpr hθ)).trans ?_
    rw [zero_mul, zero_sub, neg_mul, neg_mul_neg, mul_right_comm 2 _ θ,
      Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, neg_mul]

end ProbabilityTheory.IsBrownianReal
