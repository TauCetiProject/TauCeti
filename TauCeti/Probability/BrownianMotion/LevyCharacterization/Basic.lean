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
import TauCeti.MeasureTheory.Constructions.BorelSpace.RightContinuous
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.Probability.BrownianMotion.ExponentialMartingale
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.BrownianMotion.QuadraticVariation
import TauCeti.Probability.BrownianMotion.RunningMaximum
import TauCeti.Probability.Independence.CharacteristicFunction
import TauCeti.Probability.Martingale.Basic
import TauCeti.Probability.Martingale.Exponential.Local
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.Dominated
import TauCeti.Probability.Martingale.Local.Version
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

open Complex Filter MeasureTheory ProbabilityTheory Set TauCeti.Probability
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace ProbabilityTheory.Locally

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

private lemma exp_inner_I_eq (x y α : ℝ) : exp ((⟪x - y, α⟫ : ℂ) * I) = exp (I * α * (x - y)) := by
  simp only [RCLike.inner_apply, conj_trivial]; congr 1; push_cast; ring

private lemma isStronglyProgressive_sq_sub_zero_sub {Y : ℝ≥0 → Ω → ℝ}
    (hY : IsStronglyPredictable ℱ Y) :
    IsStronglyProgressive ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - (t : ℝ)) := fun T ↦
  let : MeasurableSpace Ω := ℱ T
  (((hY.isStronglyProgressive T).pow 2).sub ((((hY.isStronglyProgressive.stronglyAdapted 0).pow 2)
    |>.mono (ℱ.mono bot_le)).comp_measurable measurable_snd)).sub
    ((NNReal.continuous_coe.comp continuous_subtype_val).stronglyMeasurable.comp_measurable
      measurable_fst)

/-- **Gaussian increment law under Lévy's hypothesis.**
If `M` is an almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - c * t` is a local martingale (`c : ℝ≥0`), then for `s ≤ t`,
`M t - M s` has Gaussian law `N(0, c * (t - s))`. No literal adaptation or initial moment
assumption on `M` is required. -/
theorem hasLaw_sub_gaussianReal [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ} {c : ℝ≥0}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (c : ℝ) * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ M t ω - M s ω) (gaussianReal 0 (c * (t - s))) P :=
  hasLaw_of_forall_integral_exp_inner_I
    (hM.aestronglyMeasurable_sub (fun _ h ↦ h.stronglyAdapted) s t).aemeasurable fun α ↦ by
    have hset := setIntegral_exp_I_mul_sub hM hQ hcont α hst MeasurableSet.univ
    simp only [Measure.restrict_univ, measure_univ, ENNReal.toReal_one, Complex.ofReal_one,
      one_mul] at hset
    simp_rw [exp_inner_I_eq, hset, charFun_gaussianReal]; congr 1
    simp [NNReal.coe_mul, NNReal.coe_sub hst]; ring

/-- **Increment independence from the past under Lévy's hypothesis.**
If `M` is an almost-surely continuous real local martingale and `t ↦ M t ^ 2 - M 0 ^ 2 - c * t`
is a local martingale, then for every `s ≤ t`, the increment `M t - M s` is independent of `ℱ s`.
No sign assumption on `c`, literal adaptation of `M`, or initial moment assumption is required. -/
theorem indep_comap_sub [IsZeroOrProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (.comap (fun ω ↦ M t ω - M s ω) inferInstance) (ℱ s) P :=
  indep_comap_of_setIntegral_exp_inner_I (ℱ.le s)
    (hM.aestronglyMeasurable_sub (fun _ h ↦ h.stronglyAdapted) s t).aemeasurable
    (φ := fun α ↦ exp (-((α ^ 2 * c * ((t : ℝ) - s) / 2 : ℝ) : ℂ))) fun α _ hA ↦ by
      simp_rw [exp_inner_I_eq]; exact setIntegral_exp_I_mul_sub hM hQ hcont α hst hA

/-- **Lévy's characterization for adapted continuous local martingales (arbitrary start).**
If `M` is an adapted, almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - t` is a local martingale, then `t ↦ M t - M 0` is a filtered
pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownianReal_sub_zero [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (hA : Adapted ℱ M) :
    IsFilteredPreBrownianReal ℱ (fun t ω ↦ M t ω - M 0 ω) P := by
  have hQ1 : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - ((1 : ℝ≥0) : ℝ) * (t : ℝ)) P := by
    simpa only [NNReal.coe_one, one_mul] using hQ
  exact (show Adapted ℱ (fun t ω ↦ M t ω - M 0 ω) from fun t ↦
      (hA t).sub ((hA 0).mono (ℱ.mono bot_le) le_rfl)).isFilteredPreBrownianReal
    (ae_of_all P fun _ ↦ sub_self _)
    (fun _ _ hst ↦ by
      simpa only [Pi.sub_def, sub_sub_sub_cancel_right, one_mul] using
        hasLaw_sub_gaussianReal hM hQ1 hcont hst)
    (fun _ _ hst ↦ by
      simpa only [Pi.sub_def, sub_sub_sub_cancel_right] using
        indep_comap_sub hM hQ1 hcont hst)

/-- **Lévy's characterization (law form, arbitrary start, no literal adaptation).**
If `M` is an almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - t` is a local martingale, then `t ↦ M t - M 0` is a real Brownian
motion. -/
theorem isBrownianReal_sub_zero [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    IsBrownianReal (fun t ω ↦ M t ω - M 0 ω) P := by
  obtain ⟨Y, hYp, hYM, hYl⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hFY := isFilteredPreBrownianReal_sub_zero hYl
    ((isStronglyProgressive_sq_sub_zero_sub hYp).locally_martingale_of_indist hQ
      (hYM.mono fun _ hω t ↦ by simp [hω t, hω 0]))
    (hcont.mp <| hYM.mono fun _ heq hω ↦ by simpa only [funext heq] using hω)
    hYp.isStronglyProgressive.stronglyAdapted.adapted
  exact ⟨hFY.toIsPreBrownianReal.congr fun t ↦ hYM.mono fun _ hω ↦ by simp [hω t, hω 0],
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
  obtain ⟨Y, hYp, hYM, hYl⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hYc : ∀ᵐ ω ∂P, Continuous (Y · ω) :=
    hcont.mp <| hYM.mono fun _ heq hω ↦ by simpa only [funext heq] using hω
  have hFY := (isFilteredPreBrownianReal_sub_zero hYl
    ((isStronglyProgressive_sq_sub_zero_sub hYp).locally_martingale_of_indist hQ
      (h0.mp <| hYM.mono fun _ heq h0ω t ↦ by simp [heq t, heq 0, h0ω]))
    hYc hYp.isStronglyProgressive.stronglyAdapted.adapted).congr
    hYp.isStronglyProgressive.stronglyAdapted.adapted fun _ ↦
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
  let ⟨_, _, hWM, _, hWFB⟩ :=
    exists_isStronglyPredictable_indist_isFilteredPreBrownianReal hM hQ h0 hcont
  hWFB.congr hA fun t ↦ hWM.mono fun _ hω ↦ hω t

/-- **Lévy's characterization (law form, started at zero, no literal adaptation).**
If `M` is an almost-surely continuous real local martingale on a probability space with `M 0 = 0`
almost surely and `t ↦ M t ^ 2 - t` is a local martingale, then `M` is a real Brownian motion. -/
theorem isBrownianReal [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    IsBrownianReal M P :=
  let ⟨_, _, hWM, hWB, _⟩ :=
    exists_isStronglyPredictable_indist_isFilteredPreBrownianReal hM hQ h0 hcont
  ⟨hWB.toIsPreBrownianReal.congr fun t ↦ hWM.mono fun _ hω ↦ hω t, hcont⟩

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
  -- Dominate `|B s|` on `[0, T]` by `exp (T / 2)` times the running maxima of `exp (±B - t/2)`.
  have hrc : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ B u ω) (Ioi t) t :=
    hB.cont.mono fun _ hω _ _ ↦ hω.continuousWithinAt
  let M (θ : ℝ) (ω : Ω) : ℝ≥0∞ := ⨆ s ≤ T, ENNReal.ofReal (exponentialMartingale θ B s ω)
  have hM_lt (θ : ℝ) := hnat.lintegral_iSup_exponentialMartingale_lt_top hrc θ
  have hM_ae (θ : ℝ) : AEMeasurable (M θ) P := aemeasurable_iSup_le_ofReal
    (fun t ↦ (funext (exponentialMartingale_def θ B t) ▸
      ((((hA t).mono (ℱ.le t) le_rfl).const_mul θ |>.sub measurable_const).exp)).aemeasurable)
    (hrc.mono fun _ hω t ht ↦ by
      simp_rw [exponentialMartingale_def]
      exact (((hω t ht).const_mul _).sub
        ((NNReal.continuous_coe.const_mul _).div_const _).continuousWithinAt).rexp)
  have hside (θ : ℝ) (hθ : θ ^ 2 = 1) (ω : Ω) (hfin : M θ ω ≠ ∞) {s : ℝ≥0} (hs : s ≤ T) :
      θ * B s ω ≤ Real.exp ((T : ℝ) / 2) * (M θ ω).toReal := by
    have hsT : (s : ℝ) ≤ T := hs
    refine ((le_of_lt <| by linarith [Real.add_one_le_exp (θ * B s ω)]).trans <|
      (Real.exp_le_exp.2 (show θ * B s ω ≤ (T : ℝ) / 2 + (θ * B s ω - θ ^ 2 * (s : ℝ) / 2) by
        rw [hθ]; linarith)).trans_eq (by rw [Real.exp_add, ← exponentialMartingale_def])).trans <|
      mul_le_mul_of_nonneg_left (show exponentialMartingale θ B s ω ≤ (M θ ω).toReal from
        (ENNReal.toReal_ofReal (by rw [exponentialMartingale_def]; exact (Real.exp_pos _).le)
          ).symm.trans_le (ENNReal.toReal_mono hfin (le_iSup₂ (f := fun u (_ : u ≤ T) ↦
          ENNReal.ofReal (exponentialMartingale θ B u ω)) s hs))) (Real.exp_pos _).le
  refine ⟨fun ω ↦ Real.exp ((T : ℝ) / 2) * ((M 1 ω).toReal + (M (-1) ω).toReal),
    ((integrable_toReal_of_lintegral_ne_top (hM_ae 1) (hM_lt 1).ne).add
      (integrable_toReal_of_lintegral_ne_top (hM_ae (-1)) (hM_lt (-1)).ne)).const_mul _, ?_⟩
  filter_upwards [ae_lt_top' (hM_ae 1) (hM_lt 1).ne, ae_lt_top' (hM_ae (-1)) (hM_lt (-1)).ne]
    with ω hpos hneg s hs
  have h1 := hside 1 (by norm_num) ω hpos.ne hs; have h2 := hside (-1) (by norm_num) ω hneg.ne hs
  rw [Real.norm_eq_abs, abs_le, mul_add]
  exact ⟨by nlinarith [Real.exp_pos ((T : ℝ) / 2), ENNReal.toReal_nonneg (a := M 1 ω)],
    by nlinarith [Real.exp_pos ((T : ℝ) / 2), ENNReal.toReal_nonneg (a := M (-1) ω)]⟩

private lemma setIntegral_sq_sub_eq_quadraticSum (hB : IsBrownianReal B P)
    (hBM : Martingale B ℱ P) {s t : ℝ≥0} {E : Set Ω} (hE : MeasurableSet[ℱ s] E)
    {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g) (hg0 : g 0 = s) (hgl : g (Fin.last n) = t) :
    ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P = ∫ ω in E, quadraticSum B g ω ∂P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hI2 u := (hB.integrable_pow_eval u 2).integrableOn (s := E)
  have hstep (i : Fin n) : ∫ ω in E, (B (g i.succ) ω ^ 2 - B (g i.castSucc) ω ^ 2) ∂P =
      ∫ ω in E, (B (g i.succ) ω - B (g i.castSucc) ω) ^ 2 ∂P := by
    have hEu : MeasurableSet[ℱ (g i.castSucc)] E := ℱ.mono (hg0 ▸ hg (Fin.zero_le _)) E hE
    have h1 := setIntegral_congr_ae (ℱ.le _ E hEu) ((hBM.condExp_sq (hg (Fin.castSucc_le_succ i))
      (hB.memLp_eval _ (by simp))).mono fun _ hω _ ↦ hω)
    rw [setIntegral_condExp (ℱ.le (g i.castSucc)) (hB.integrable_pow_eval _ 2) hEu,
      integral_add (hI2 _) integrable_condExp.integrableOn,
      setIntegral_condExp (ℱ.le (g i.castSucc)) (hB.integrable_pow_sub _ _ 2) hEu] at h1
    rw [integral_sub (hI2 _) (hI2 _)]; linarith
  rw [quadraticSum_def, integral_finsetSum _ fun _ _ ↦ (hB.integrable_pow_sub _ _ 2).integrableOn,
    ← Finset.sum_congr rfl fun i _ ↦ hstep i, ← integral_finsetSum Finset.univ
      (f := fun (i : Fin n) ω ↦ B (g i.succ) ω ^ 2 - B (g i.castSucc) ω ^ 2)
      fun i _ ↦ Integrable.sub (hI2 (g i.succ)) (hI2 (g i.castSucc))]
  congr 1; funext ω
  have h1 := Fin.sum_univ_succ (fun i : Fin (n + 1) ↦ B (g i) ω ^ 2)
  have h2 := Fin.sum_univ_castSucc (fun i : Fin (n + 1) ↦ B (g i) ω ^ 2)
  rw [hg0] at h1; rw [hgl] at h2; rw [Finset.sum_sub_distrib]; linarith

/-- **Filtered Brownian-law corollary.**
A real Brownian motion `B` (in law) that is adapted to a filtration `ℱ` and is a local martingale
on `ℱ` is automatically a filtered pre-Brownian motion relative to `ℱ`: in particular, every
increment `B t - B s` (`s ≤ t`) is independent of `ℱ s`. -/
theorem isFilteredPreBrownianReal_of_locally_martingale (hB : IsBrownianReal B P)
    (hA : Adapted ℱ B) (hloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B P) :
    IsFilteredPreBrownianReal ℱ B P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  -- Upgrade `B` to a true martingale, then check `B^2 - t` is a martingale via quadratic sums.
  have hBM := martingale_of_locally_martingale hB hA hloc
  refine Locally.isFilteredPreBrownianReal hloc (Locally.of_prop ?_) hB.eval_zero_ae_eq_zero
    hB.cont hA
  rw [(show StronglyAdapted ℱ (fun t ω ↦ B t ω ^ 2 - (t : ℝ)) from fun t ↦
      ((hA t).pow_const 2 |>.sub measurable_const).stronglyMeasurable).martingale_iff_setIntegral_eq
    fun t ↦ (hB.integrable_pow_eval t 2).sub (integrable_const (t : ℝ))]
  intro s t hst E hE
  let g (k : ℕ) (i : Fin (k + 2)) : ℝ≥0 := s + (i : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0) * (t - s)
  have hg k : Monotone (g k) := fun _ _ hij ↦ by dsimp only [g]; gcongr; exact_mod_cast hij
  -- Quadratic sums along uniform grids converge to `t - s` in `L^2`, hence in `L^1(E)`.
  have hD k := (hB.memLp_quadraticSum (g k)).sub (memLp_const ((t : ℝ) - s))
  have hsq_lim := hB.toIsPreBrownianReal.tendsto_integral_sq_quadraticSum_sub (a := s) (b := t)
    (δ := fun k ↦ ((t : ℝ) - s) / ((k + 1 : ℕ) : ℝ)) hg (fun _ ↦ by simp [g])
    (fun _ ↦ by simp [g, add_tsub_cancel_of_le hst]) (fun _ _ ↦ le_of_eq <| by
      simp only [g, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
        NNReal.coe_one, NNReal.coe_sub hst, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
        Nat.cast_one]; ring)
    (by simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((t : ℝ) - s))
  have hzero : ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P - ∫ _ in E, ((t : ℝ) - s) ∂P = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr
        (f₂ := fun k ↦ ∫ ω in E, (quadraticSum B (g k) ω - ((t : ℝ) - s)) ∂P) fun k ↦ by
          rw [integral_sub ((hB.memLp_quadraticSum _).integrable one_le_two).integrableOn
              (integrable_const _).integrableOn, ← setIntegral_sq_sub_eq_quadraticSum hB hBM hE
              (t := t) (hg k) (by simp [g]) (by simp [g, add_tsub_cancel_of_le hst])])
      (squeeze_zero_norm (fun k ↦ show ‖∫ ω in E, (quadraticSum B (g k) ω - ((t : ℝ) - s)) ∂P‖ ≤
            Real.sqrt (∫ ω, (quadraticSum B (g k) ω - ((t : ℝ) - s)) ^ 2 ∂P) by
          rw [Real.norm_eq_abs]; refine abs_integral_le_integral_abs.trans ((setIntegral_le_integral
            ((hD k).integrable one_le_two).abs (ae_of_all P fun _ ↦ abs_nonneg _)).trans <|
            Real.le_sqrt_of_sq_le (by
              simpa [Real.norm_eq_abs] using TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq
                (hD k).norm (memLp_const (1 : ℝ)))))
        (by simpa only [Function.comp_def, Real.sqrt_zero] using
          Real.continuous_sqrt.continuousAt.tendsto.comp hsq_lim))
  have hI2 u := (hB.integrable_pow_eval u 2).integrableOn (s := E)
  simp only [integral_sub (hI2 _) (hI2 _), integral_sub (integrable_const _).integrableOn
      (integrable_const _).integrableOn, integral_sub (hI2 _) (integrable_const _).integrableOn]
    at hzero ⊢
  linarith

end ProbabilityTheory.IsBrownianReal
