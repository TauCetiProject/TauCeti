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
import TauCeti.Probability.Process.LocalProperty

/-!
# Scalar Lévy characterization of Brownian motion

Proves Lévy's characterization for an almost-surely continuous real local martingale `M` on a raw
filtration `ℱ` with `t ↦ M t ^ 2 - M 0 ^ 2 - c * t` a local martingale: Gaussian increment laws,
increment independence from `ℱ s`, filtered and law-form Brownian characterizations (arbitrary start
and zero start), strongly predictable indistinguishable Brownian versions, and the converse that a
Brownian motion adapted and locally martingale on `ℱ` is a filtered pre-Brownian motion on `ℱ`.

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
  (show Adapted ℱ (fun t ω ↦ M t ω - M 0 ω) from fun t ↦
      (hA t).sub ((hA 0).mono (ℱ.mono bot_le) le_rfl)).isFilteredPreBrownianReal
    (ae_of_all P fun _ ↦ sub_self _) (fun _ _ hst ↦ by
      simpa only [Pi.sub_def, sub_sub_sub_cancel_right, one_mul] using
        hasLaw_sub_gaussianReal hM hQ1 hcont hst)
    (fun _ _ hst ↦ by
      simpa only [Pi.sub_def, sub_sub_sub_cancel_right] using indep_comap_sub hM hQ1 hcont hst)

/-- **Lévy's characterization (law form, arbitrary start, no literal adaptation).**
If `M` is an almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - t` is a local martingale, then `t ↦ M t - M 0` is a real Brownian
motion. -/
theorem isBrownianReal_sub_initialValue [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) : IsBrownianReal (fun t ω ↦ M t ω - M 0 ω) P := by
  obtain ⟨Y, hYp, hYM, hYc, hYl, _, hQY⟩ :=
    hM.exists_isStronglyPredictable_indist_sq_sub_initialValue_sub (A := fun t _ ↦ (t : ℝ)) hQ
      (NNReal.continuous_coe.stronglyMeasurable.comp_measurable ℱ.measurable_fst_predictable)
      hcont (ae_of_all P fun _ _ ↦ rfl)
  exact ⟨(isFilteredPreBrownianReal_sub_initialValue hYl hQY hYc
    hYp.isStronglyProgressive.stronglyAdapted.adapted).toIsPreBrownianReal.congr fun t ↦
      hYM.mono fun _ hω ↦ by simp [hω t, hω 0], hcont.mono fun _ hω ↦ hω.sub continuous_const⟩

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
      (NNReal.continuous_coe.stronglyMeasurable.comp_measurable ℱ.measurable_fst_predictable)
      hcont (h0.mono fun _ h0ω _ ↦ by simp [h0ω])
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

private lemma setIntegral_sq_sub_eq_quadraticSum (hB : IsBrownianReal B P)
    (hBM : Martingale B ℱ P) {s t : ℝ≥0} {E : Set Ω} (hE : MeasurableSet[ℱ s] E)
    {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) (hg0 : g 0 = s) (hgl : g (Fin.last n) = t) :
    ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P = ∫ ω in E, quadraticSum B g ω ∂P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hI2 u := (hB.integrable_pow_eval u 2).integrableOn (s := E)
  have hstep (i : Fin n) : ∫ ω in E, (B (g i.succ) ω ^ 2 - B (g i.castSucc) ω ^ 2) ∂P =
      ∫ ω in E, (B (g i.succ) ω - B (g i.castSucc) ω) ^ 2 ∂P := by
    have hEu : MeasurableSet[ℱ (g i.castSucc)] E := ℱ.mono (hg0 ▸ hg (Fin.zero_le _)) E hE
    have h1 := setIntegral_congr_ae (ℱ.le _ E hEu) ((hBM.condExp_sq (hg (Fin.castSucc_le_succ i))
      (hB.memLp_eval _ (by simp))).mono fun _ hω _ ↦ hω)
    rw [setIntegral_condExp (ℱ.le _) (hB.integrable_pow_eval _ 2) hEu,
      integral_add (hI2 _) integrable_condExp.integrableOn,
      setIntegral_condExp (ℱ.le _) (hB.integrable_pow_sub _ _ 2) hEu] at h1
    rw [integral_sub (hI2 _) (hI2 _)]; linarith
  rw [quadraticSum_def, integral_finsetSum _ fun _ _ ↦ (hB.integrable_pow_sub _ _ 2).integrableOn,
    ← Finset.sum_congr rfl fun i _ ↦ hstep i, ← integral_finsetSum Finset.univ
      (f := fun (i : Fin n) ω ↦ B (g i.succ) ω ^ 2 - B (g i.castSucc) ω ^ 2)
      fun i _ ↦ show IntegrableOn _ E P from (hI2 (g i.succ)).sub (hI2 (g i.castSucc))]
  congr 1; funext ω; rw [Finset.sum_sub_distrib]
  linarith [Fin.sum_univ_succ (fun i ↦ B (g i) ω ^ 2),
    Fin.sum_univ_castSucc (fun i ↦ B (g i) ω ^ 2),
    congrArg (fun u ↦ B u ω ^ 2) hg0, congrArg (fun u ↦ B u ω ^ 2) hgl]

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
  rw [(show StronglyAdapted ℱ (fun t ω ↦ B t ω ^ 2 - (t : ℝ)) from fun t ↦
      ((hA t).pow_const 2 |>.sub measurable_const).stronglyMeasurable).martingale_iff_setIntegral_eq
    fun t ↦ (hB.integrable_pow_eval t 2).sub (integrable_const (t : ℝ))]
  intro s t hst E hE
  let g (k : ℕ) (i : Fin (k + 2)) : ℝ≥0 := s + (i : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0) * (t - s)
  have hg k : Monotone (g k) := fun _ _ hij ↦ by dsimp only [g]; gcongr; exact_mod_cast hij
  have hsq_lim := hB.toIsPreBrownianReal.tendsto_integral_sq_quadraticSum_sub (a := s) (b := t)
    (δ := fun k ↦ ((t : ℝ) - s) / ((k + 1 : ℕ) : ℝ)) hg (fun _ ↦ by simp [g])
    (fun _ ↦ by simp [g, add_tsub_cancel_of_le hst]) (fun _ _ ↦ le_of_eq <| by
      simp [g, NNReal.coe_sub hst]; ring)
    (by simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((t : ℝ) - s))
  have hEq k : ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P - ∫ _ in E, ((t : ℝ) - s) ∂P =
      ∫ ω in E, (quadraticSum B (g k) ω - ((t : ℝ) - s)) ∂P := by
    rw [integral_sub ((hB.memLp_quadraticSum _).integrable one_le_two).integrableOn
      (integrable_const _).integrableOn, ← setIntegral_sq_sub_eq_quadraticSum hB hBM hE
      (t := t) (hg k) (by simp [g]) (by simp [g, add_tsub_cancel_of_le hst])]
  have hzero : ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P - ∫ _ in E, ((t : ℝ) - s) ∂P = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr hEq) (squeeze_zero_norm (fun k ↦
      (Real.norm_eq_abs _).trans_le <| abs_setIntegral_le_sqrt_integral_sq_mul_sqrt_measureReal
        ((hB.memLp_quadraticSum (g k)).sub (memLp_const ((t : ℝ) - s))) (measure_ne_top P E)) <| by
      simpa only [Function.comp_def, Real.sqrt_zero, zero_mul] using
        (Real.continuous_sqrt.continuousAt.tendsto.comp hsq_lim).mul_const √(P.real E))
  have hI2 u := (hB.integrable_pow_eval u 2).integrableOn (s := E)
  simp only [integral_sub (hI2 _) (hI2 _), integral_sub (integrable_const _).integrableOn
    (integrable_const _).integrableOn, integral_sub (hI2 _) (integrable_const _).integrableOn]
    at hzero ⊢; linarith

end ProbabilityTheory.IsBrownianReal
