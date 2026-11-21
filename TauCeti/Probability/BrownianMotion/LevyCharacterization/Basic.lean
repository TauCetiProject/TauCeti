/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Process.Predictable.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Basic
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.BrownianMotion.QuadraticVariation.Basic
import TauCeti.Probability.Independence.CharacteristicFunction
import TauCeti.Probability.Martingale.Basic
import TauCeti.Probability.Martingale.Exponential.Local
import TauCeti.Probability.Martingale.Local.Dominated
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Martingale.MaximalInequality.Lp
import TauCeti.Probability.Martingale.QuadraticVariation
import TauCeti.Probability.Process.LocalProperty
import TauCeti.Topology.Instances.Real.UniformGrid

/-!
# Scalar Lévy characterization of Brownian motion

Proves Lévy's characterization for an almost-surely continuous real local martingale `M` on a raw
filtration `ℱ` with `t ↦ M t ^ 2 - M 0 ^ 2 - c * t` a local martingale: Gaussian increment laws,
increment independence from `ℱ s`, filtered and law-form Brownian characterizations (arbitrary start
and zero start), strongly predictable indistinguishable Brownian versions (arbitrary start and zero
start), and the converse that a Brownian motion on `ℱ` which is a local martingale admits a
strongly predictable filtered pre-Brownian version and (when adapted) is a filtered pre-Brownian
motion on `ℱ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 3.3.16.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, Theorem 3.6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set TauCeti TauCeti.Probability
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace ProbabilityTheory.Locally

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

/-- **Gaussian increment law under Lévy's hypothesis.**
If `M` is an almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - c * t` is a local martingale (`c : ℝ≥0`), then for `s ≤ t`,
`M t - M s` has Gaussian law `N(0, c * (t - s))`. No literal adaptation or initial moment
assumption on `M` is required. -/
theorem hasLaw_sub_gaussianReal [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ} {c : ℝ≥0}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (c : ℝ) * t) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ M t ω - M s ω) (gaussianReal 0 (c * (t - s))) P :=
  hasLaw_of_forall_integral_exp_inner_mul_I
    (hM.aestronglyMeasurable_sub (fun _ h ↦ h.stronglyAdapted) s t).aemeasurable fun α ↦ by
    have hset := setIntegral_exp_I_mul_sub hM hQ hcont α hst MeasurableSet.univ
    simp only [Measure.restrict_univ, measure_univ, ENNReal.toReal_one, ofReal_one, one_mul] at hset
    simp_rw [TauCeti.exp_inner_mul_I_real, ofReal_sub, hset, charFun_gaussianReal]
    congr 1; simp [NNReal.coe_mul, NNReal.coe_sub hst]; ring

/-- **Increment independence from the past under Lévy's hypothesis.**
If `M` is an almost-surely continuous real local martingale and `t ↦ M t ^ 2 - M 0 ^ 2 - c * t`
is a local martingale, then for every `s ≤ t`, the increment `M t - M s` is independent of `ℱ s`.
No sign assumption on `c`, literal adaptation of `M`, or initial moment assumption is required. -/
theorem indep_comap_sub [IsZeroOrProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (.comap (fun ω ↦ M t ω - M s ω) inferInstance) (ℱ s) P :=
  indep_comap_of_setIntegral_exp_inner_mul_I (ℱ.le s)
    (hM.aestronglyMeasurable_sub (fun _ h ↦ h.stronglyAdapted) s t).aemeasurable
    (φ := fun α ↦ exp (-((α ^ 2 * c * ((t : ℝ) - s) / 2 : ℝ) : ℂ))) fun α _ hA ↦ by
      simp_rw [TauCeti.exp_inner_mul_I_real, ofReal_sub]
      exact setIntegral_exp_I_mul_sub hM hQ hcont α hst hA

/-- **Lévy's characterization for adapted continuous local martingales (arbitrary start).**
If `M` is an adapted, almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - t` is a local martingale, then `t ↦ M t - M 0` is a filtered
pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownianReal_sub_initialValue [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (hA : Adapted ℱ M) :
    IsFilteredPreBrownianReal ℱ (fun t ω ↦ M t ω - M 0 ω) P :=
  have hQ1 : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - ((1 : ℝ≥0) : ℝ) * (t : ℝ)) P := by simpa using hQ
  have hsub_adapt : Adapted ℱ (fun t ω ↦ M t ω - M 0 ω) := fun t ↦
    (hA t).sub ((hA 0).mono (ℱ.mono bot_le) le_rfl)
  hsub_adapt.isFilteredPreBrownianReal (ae_of_all P fun _ ↦ sub_self _)
    (fun _ _ hst ↦ by
      simpa only [Pi.sub_def, sub_sub_sub_cancel_right, one_mul] using
        hasLaw_sub_gaussianReal hM hQ1 hcont hst)
    (fun _ _ hst ↦ by
      simpa only [Pi.sub_def, sub_sub_sub_cancel_right] using indep_comap_sub hM hQ1 hcont hst)

/-- **Predictable centered Brownian version and initial-value decomposition (arbitrary start).**
Without assuming literal adaptation of `M`, if `M` is an almost-surely continuous real local
martingale on a probability space and `t ↦ M t ^ 2 - M 0 ^ 2 - t` is a local martingale, then
there exist an `ℱ 0`-strongly measurable initial random variable `Y₀` and a strongly predictable
process `W` such that `M` is indistinguishable from `t ↦ Y₀ + W t`, `W` is indistinguishable
from `t ↦ M t - M 0`, `W` is a real Brownian motion, and `W` is a filtered pre-Brownian motion
relative to `ℱ`. -/
theorem exists_isStronglyPredictable_indist_sub_initialValue_isFilteredPreBrownianReal
    [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    ∃ Y₀ : Ω → ℝ, ∃ W : ℝ≥0 → Ω → ℝ,
      StronglyMeasurable[ℱ 0] Y₀ ∧ IsStronglyPredictable ℱ W ∧
      M ≡ᵐ[P] (fun t ω ↦ Y₀ ω + W t ω) ∧ W ≡ᵐ[P] (fun t ω ↦ M t ω - M 0 ω) ∧
      IsBrownianReal W P ∧ IsFilteredPreBrownianReal ℱ W P := by
  obtain ⟨Y, hYp, hYM, hYc, hYl, _, hQY⟩ :=
    hM.exists_isStronglyPredictable_indist_sq_sub_initialValue_sub (A := fun t _ ↦ (t : ℝ)) hQ
      NNReal.continuous_coe.isStronglyPredictable_fst hcont (ae_of_all P fun _ _ ↦ rfl)
  have hY0 : StronglyMeasurable[ℱ ⊥] (Y 0) := by
    simpa only [bot_eq_zero] using hYp.isStronglyProgressive.stronglyAdapted 0
  have hY0' : StronglyMeasurable[ℱ 0] (Y 0) := by simpa only [← bot_eq_zero] using hY0
  have hWp : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω - Y 0 ω) :=
    StronglyMeasurable.sub hYp hY0.isStronglyPredictable_snd
  have hFW : IsFilteredPreBrownianReal ℱ (fun t ω ↦ Y t ω - Y 0 ω) P :=
    isFilteredPreBrownianReal_sub_initialValue hYl hQY hYc
      hYp.isStronglyProgressive.stronglyAdapted.adapted
  have hWc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω - Y 0 ω) :=
    hYc.mono fun _ h ↦ h.sub continuous_const
  exact ⟨Y 0, fun t ω ↦ Y t ω - Y 0 ω, hY0', hWp,
    hYM.mono fun _ hω t ↦ by simp [hω t], hYM.mono fun _ hω t ↦ by simp [hω t, hω 0],
    ⟨hFW.toIsPreBrownianReal, hWc⟩, hFW⟩

/-- **Lévy's characterization (law form, arbitrary start, no literal adaptation).**
If `M` is an almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - t` is a local martingale, then `t ↦ M t - M 0` is a real Brownian
motion. -/
theorem isBrownianReal_sub_initialValue [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) : IsBrownianReal (fun t ω ↦ M t ω - M 0 ω) P := by
  obtain ⟨_, W, _, _, _, hWM, hBW, _⟩ :=
    exists_isStronglyPredictable_indist_sub_initialValue_isFilteredPreBrownianReal hM hQ hcont
  exact ⟨hBW.toIsPreBrownianReal.congr fun t ↦ hWM.mono fun _ hω ↦ hω t,
    hcont.mono fun _ hω ↦ hω.sub continuous_const⟩

/-- **Predictable Brownian version under bare native locality.**
Without assuming literal adaptation of `M`, if `M` is an almost-surely continuous real local
martingale on a probability space with `M 0 = 0` almost surely and `t ↦ M t ^ 2 - t` is a local
martingale, then `M` admits a strongly predictable indistinguishable version `W` that is both a
real Brownian motion and a filtered pre-Brownian motion relative to `ℱ`. -/
theorem exists_isStronglyPredictable_indist_isFilteredPreBrownianReal [IsProbabilityMeasure P]
    {M : ℝ≥0 → Ω → ℝ} (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    ∃ W : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ W ∧ W ≡ᵐ[P] M ∧
      IsBrownianReal W P ∧ IsFilteredPreBrownianReal ℱ W P := by
  obtain ⟨Y, hYp, hYM, hYc, hYl, _, hQY⟩ :=
    hM.exists_isStronglyPredictable_indist_sq_sub_initialValue_sub (A := fun t _ ↦ (t : ℝ)) hQ
      NNReal.continuous_coe.isStronglyPredictable_fst hcont (h0.mono fun _ h0ω _ ↦ by simp [h0ω])
  have hYa := hYp.isStronglyProgressive.stronglyAdapted.adapted
  have hFY := (isFilteredPreBrownianReal_sub_initialValue hYl hQY hYc hYa).congr hYa fun _ ↦
    h0.mp <| hYM.mono fun _ heq h0ω ↦ by simp [heq 0, h0ω]
  exact ⟨Y, hYp, hYM, ⟨hFY.toIsPreBrownianReal, hYc⟩, hFY⟩

/-- **Lévy's characterization for adapted continuous local martingales started at zero.**
If `M` is an adapted, almost-surely continuous real local martingale on a probability space with
`M 0 = 0` almost surely and `t ↦ M t ^ 2 - t` is a local martingale, then `M` is a filtered
pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownianReal [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (hA : Adapted ℱ M) :
    IsFilteredPreBrownianReal ℱ M P :=
  let ⟨_, _, hWM, _, hF⟩ :=
    exists_isStronglyPredictable_indist_isFilteredPreBrownianReal hM hQ h0 hcont
  hF.congr hA fun t ↦ hWM.mono fun _ hω ↦ hω t

/-- **Lévy's characterization (law form, started at zero, no literal adaptation).**
If `M` is an almost-surely continuous real local martingale on a probability space with `M 0 = 0`
almost surely and `t ↦ M t ^ 2 - t` is a local martingale, then `M` is a real Brownian motion. -/
theorem isBrownianReal [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) : IsBrownianReal M P :=
  let ⟨_, _, hWM, hB, _⟩ :=
    exists_isStronglyPredictable_indist_isFilteredPreBrownianReal hM hQ h0 hcont
  ⟨hB.toIsPreBrownianReal.congr fun t ↦ hWM.mono fun _ hω ↦ hω t, hcont⟩

end ProbabilityTheory.Locally

namespace ProbabilityTheory.IsBrownianReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

private lemma martingale_of_locally_martingale (hB : IsBrownianReal B P) (hA : Adapted ℱ B)
    (hloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B P) : Martingale B ℱ P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hnat := hB.toIsPreBrownianReal.isFilteredPreBrownianReal_natural
    fun t ↦ (hA.stronglyAdapted t).mono (ℱ.le t)
  refine hA.stronglyAdapted.martingale_of_locally_martingale_of_dominated hloc fun T ↦ ?_
  have hrc : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ B u ω) (Ioi t) t :=
    hB.cont.mono fun _ hω _ _ ↦ hω.continuousWithinAt
  refine ⟨fun ω ↦ (⨆ s ≤ T, ‖B s ω‖ₑ).toReal,
    (hnat.martingale.memLp_toReal_iSup_eNorm hrc (by norm_num) ENNReal.ofNat_ne_top
      (hB.memLp_eval T ENNReal.ofNat_ne_top)).integrable one_le_two, ?_⟩
  filter_upwards [hnat.martingale.ae_iSup_eNorm_lt_top hrc] with ω hfin s hs
  rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
  exact ENNReal.toReal_mono hfin.ne (le_iSup₂_of_le s hs le_rfl)

/-- **Filtered Brownian-law corollary.**
A real Brownian motion `B` (in law) that is adapted to a filtration `ℱ` and is a local martingale
on `ℱ` is automatically a filtered pre-Brownian motion relative to `ℱ`: in particular, every
increment `B t - B s` (`s ≤ t`) is independent of `ℱ s`. -/
theorem isFilteredPreBrownianReal_of_locally_martingale (hB : IsBrownianReal B P)
    (hA : Adapted ℱ B) (hloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B P) :
    IsFilteredPreBrownianReal ℱ B P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hBM := martingale_of_locally_martingale hB hA hloc
  refine Locally.isFilteredPreBrownianReal hloc (Locally.of_prop ?_) hB.eval_zero_ae_eq_zero
    hB.cont hA
  have hQ_adapt : StronglyAdapted ℱ (fun t ω ↦ B t ω ^ 2 - (t : ℝ)) := fun t ↦
    ((hA t).pow_const 2 |>.sub measurable_const).stronglyMeasurable
  rw [hQ_adapt.martingale_iff_setIntegral_eq
    fun t ↦ (hB.integrable_pow_eval t 2).sub (integrable_const (t : ℝ))]
  intro s t hst E hE
  have hsq_lim := hB.toIsPreBrownianReal.tendsto_integral_sq_quadraticSum_sub (a := s) (b := t)
    (grid := uniformGridFin s t) (δ := fun k ↦ ((t : ℝ) - s) / ((k + 1 : ℕ) : ℝ))
    (uniformGridFin_monotone s t) (fun _ ↦ uniformGridFin_zero s t _)
    (fun _ ↦ uniformGridFin_last hst _)
    (fun k i ↦ by simpa only [Nat.cast_add, Nat.cast_one] using
      (coe_uniformGridFin_succ_sub_castSucc hst k i).le)
    (tendsto_uniformGrid_mesh s t)
  have hEq k : ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P - ∫ _ in E, ((t : ℝ) - s) ∂P =
      ∫ ω in E, (quadraticSum B (uniformGridFin s t k) ω - ((t : ℝ) - s)) ∂P := by
    rw [integral_sub ((hB.memLp_quadraticSum _).integrable one_le_two).integrableOn
      (integrable_const _).integrableOn, ← hBM.setIntegral_sq_sub_eq_quadraticSum hE
      (uniformGridFin_monotone s t k) (uniformGridFin_zero s t k) (uniformGridFin_last hst k)
      (fun _ ↦ hB.memLp_eval _ (by simp))]
  have hzero : ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P - ∫ _ in E, ((t : ℝ) - s) ∂P = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr hEq) (squeeze_zero_norm (fun k ↦
      (Real.norm_eq_abs _).trans_le <| abs_setIntegral_le_sqrt_integral_sq_mul_sqrt_measureReal
        ((hB.memLp_quadraticSum (uniformGridFin s t k)).sub (memLp_const ((t : ℝ) - s)))
        (measure_ne_top P E)) <| by
      simpa only [Function.comp_def, Real.sqrt_zero, zero_mul] using
        (Real.continuous_sqrt.continuousAt.tendsto.comp hsq_lim).mul_const √(P.real E))
  have hI2 u := (hB.integrable_pow_eval u 2).integrableOn (s := E)
  simp only [integral_sub (hI2 _) (hI2 _), integral_sub (integrable_const _).integrableOn
    (integrable_const _).integrableOn, integral_sub (hI2 _) (integrable_const _).integrableOn]
    at hzero ⊢; linarith

/-- **Predictable filtered Brownian version from a Brownian local martingale.**
Without assuming literal adaptation of `B`, if `B` is a real Brownian motion (in law) that is a
native local martingale on `ℱ`, then `B` admits a strongly predictable indistinguishable version
`W` that is both a real Brownian motion and a filtered pre-Brownian motion relative to `ℱ`. -/
theorem exists_isStronglyPredictable_indist_isFilteredPreBrownianReal (hB : IsBrownianReal B P)
    (hloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B P) :
    ∃ W : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ W ∧ W ≡ᵐ[P] B ∧
      IsBrownianReal W P ∧ IsFilteredPreBrownianReal ℱ W P := by
  obtain ⟨W, hWp, hWc, hWB, hWloc⟩ :=
    hloc.exists_isStronglyPredictable_indist_locally_martingale_of_ae_continuous hB.cont
  have hBW : IsBrownianReal W P :=
    ⟨hB.toIsPreBrownianReal.congr fun t ↦ hWB.mono fun _ hω ↦ (hω t).symm, hWc⟩
  exact ⟨W, hWp, hWB, hBW,
    hBW.isFilteredPreBrownianReal_of_locally_martingale
      hWp.isStronglyProgressive.stronglyAdapted.adapted hWloc⟩

end ProbabilityTheory.IsBrownianReal
