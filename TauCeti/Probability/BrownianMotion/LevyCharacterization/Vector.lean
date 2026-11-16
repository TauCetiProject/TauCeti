/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Process.Predictable.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic
import TauCeti.Probability.BrownianMotion.LevyCharacterization.Basic
import TauCeti.Probability.BrownianMotion.LevyCharacterization.Exponential
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Independence.CharacteristicFunction
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.Stopping

/-!
# Vector Lévy characterization of Brownian motion

Let `M : ι → ℝ≥0 → Ω → ℝ` be a family of almost-surely continuous real local martingales on a raw
filtration `ℱ` under `P` such that for all `i, j`,
`t ↦ M i t * M j t - M i 0 * M j 0 - C i j * t` is a local martingale. This file proves the
multivariate Lévy characterization of Brownian motion:

* `setIntegral_exp_I_mul_sum_sub_of_locally_martingale`: Cramér–Wold characteristic-function
  factorization for finite linear combinations `∑ i, v i * (M i t - M i s)` on events in `ℱ s`;
* `indep_comap_sub_pi_of_locally_martingale`: joint independence of the coordinate increments
  `ω ↦ (M i t ω - M i s ω)_i` from `ℱ s` for any index type `ι` and covariance matrix `C`;
* `hasLaw_sub_pi_gaussianReal_of_locally_martingale`: for a finite index type `ι` and diagonal
  covariance `c i * δ_{ij}`, joint product Gaussian increment law
  `Measure.pi (fun i ↦ gaussianReal 0 (c i * (t - s)))`;
* `iIndepFun_sub_zero_of_locally_martingale` and `iIndepFun_of_locally_martingale`: global
  pathwise independence of the coordinate processes `i ↦ (t ↦ M i t - M i 0)` (and `i ↦ M i`
  when `M i 0 = 0` a.s.) for any index type `ι`;
* `exists_isStronglyPredictable_indist_pi_isFilteredPreBrownianReal_of_locally_martingale`:
  under bare native locality (without literal adaptation), existence of a strongly predictable
  indistinguishable family of independent filtered Brownian motions relative to `ℱ`;
* `martingale_mul_of_indepFun_isBrownianReal` and
  `indep_comap_sub_pi_of_iIndepFun_isBrownianReal_locally_martingale`: conversely, independent
  Brownian motions that are adapted local martingales on `ℱ` have martingale cross-products (by
  polarization `(B i + B j) / √2`) and jointly independent vector increments relative to `ℱ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 3.3.16.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, Theorem 3.6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

section LocalMartingaleLinearComb

private lemma continuous_stoppedProcess {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hω : Continuous (X · ω)) : Continuous (stoppedProcess X τ · ω) := by
  cases h : τ ω with
  | top =>
    have heq : (fun t ↦ stoppedProcess X τ t ω) = fun t ↦ X t ω := by
      funext t; simp only [stoppedProcess, h, min_top_right]; rfl
    rw [heq]; exact hω
  | coe a =>
    have heq : (fun t ↦ stoppedProcess X τ t ω) = fun t ↦ X (min t a) ω := by
      funext t; simp only [stoppedProcess, h, ← WithTop.coe_min]; rfl
    rw [heq]; exact hω.comp (continuous_id.min continuous_const)

private lemma isStronglyProgressive_stoppedProcess_indicator {X : ℝ≥0 → Ω → ℝ}
    (hprog : IsStronglyProgressive ℱ X) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsStronglyProgressive ℱ
      (stoppedProcess (fun t ↦ {ω | 0 < σ ω}.indicator (X t)) σ) := by
  intro T
  let : MeasurableSpace Ω := ℱ T
  have hpos : MeasurableSet[ℱ T] {ω | 0 < σ ω} :=
    ℱ.mono bot_le _ (by simpa only [bot_eq_zero, WithTop.coe_zero] using hσ.measurableSet_gt ⊥)
  have heq : (fun p : Set.Iic T × Ω ↦
      stoppedProcess (fun t ↦ {ω | 0 < σ ω}.indicator (X t)) σ p.1 p.2) =
      (Set.univ ×ˢ {ω | 0 < σ ω}).indicator
        (fun p : Set.Iic T × Ω ↦ stoppedProcess X σ p.1 p.2) := by
    ext ⟨t, ω⟩
    rw [stoppedProcess_indicator_comm]
    by_cases hω : 0 < σ ω <;> simp [hω]
  rw [heq]
  exact ((hprog.stoppedProcess hσ) T).indicator (MeasurableSet.univ.prod hpos)

private lemma martingale_stoppedProcess_indicator_of_le [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}
    (hprog : IsStronglyProgressive ℱ X) (hcont : ∀ᵐ ω ∂P, Continuous (X · ω))
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hle : τ ≤ σ)
    (hmart : Martingale (stoppedProcess (fun t ↦ {ω | 0 < σ ω}.indicator (X t)) σ) ℱ P) :
    Martingale (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) ℱ P := by
  have hstage_prog := isStronglyProgressive_stoppedProcess_indicator hprog hσ
  have hstage_rc : ∀ᵐ ω ∂P, IsRightContinuous
      (fun t ↦ stoppedProcess (fun u ↦ {ω | 0 < σ ω}.indicator (X u)) σ t ω) := by
    filter_upwards [hcont] with ω hω
    have heq : (fun t ↦ stoppedProcess (fun u ↦ {ω | 0 < σ ω}.indicator (X u)) σ t ω) =
        fun t ↦ if 0 < σ ω then stoppedProcess X σ t ω else 0 := by
      funext t; rw [stoppedProcess_indicator_comm]; simp [Set.indicator_apply]
    rw [heq]; split_ifs
    · exact (continuous_stoppedProcess hω).isRightContinuous
    · exact continuous_const.isRightContinuous
  convert hmart.stoppedProcess_indicator_of_ae_isRightContinuous hstage_prog hstage_rc hτ using 1
  simp only [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
  ext t ω
  have hmin : min (τ ω) (σ ω) = τ ω := min_eq_left (hle ω)
  by_cases hω : 0 < τ ω
  · simp [Set.indicator_of_mem, hω, lt_of_lt_of_le hω (hle ω), stoppedProcess, hmin]
  · simp [Set.indicator_of_notMem, hω]

private lemma locally_martingale_const_mul {X : ℝ≥0 → Ω → ℝ} (a : ℝ)
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ a * X t ω) P := by
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  convert (hX.stoppedProcess_localSeq n).smul a using 1
  ext t ω
  simp only [Pi.smul_apply, smul_eq_mul, stoppedProcess_indicator_comm, Set.indicator_apply]
  split_ifs <;> simp [stoppedProcess]

private lemma locally_martingale_add_of_isStronglyPredictable [IsFiniteMeasure P]
    {U V : ℝ≥0 → Ω → ℝ}
    (hU : Locally (fun Y ↦ Martingale Y ℱ P) ℱ U P)
    (hV : Locally (fun Y ↦ Martingale Y ℱ P) ℱ V P)
    (hUp : IsStronglyPredictable ℱ U) (hVp : IsStronglyPredictable ℱ V)
    (hUc : ∀ᵐ ω ∂P, Continuous (U · ω)) (hVc : ∀ᵐ ω ∂P, Continuous (V · ω)) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ U t ω + V t ω) P := by
  let τ := min hU.localSeq hV.localSeq
  have hτ : IsLocalizingSequence ℱ τ P :=
    hU.isLocalizingSequence_localSeq.min hV.isLocalizingSequence_localSeq
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  have hUn := martingale_stoppedProcess_indicator_of_le hUp.isStronglyProgressive hUc
    (hU.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
    (fun ω ↦ min_le_left _ _) (hU.stoppedProcess_localSeq n)
  have hVn := martingale_stoppedProcess_indicator_of_le hVp.isStronglyProgressive hVc
    (hV.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
    (fun ω ↦ min_le_right _ _) (hV.stoppedProcess_localSeq n)
  convert hUn.add hVn using 1
  ext t ω
  simp only [Pi.add_apply, stoppedProcess_indicator_comm, Set.indicator_apply, Set.mem_ofPred_eq,
    bot_eq_zero]
  split_ifs <;> simp [stoppedProcess]

private lemma isStronglyPredictable_zero :
    IsStronglyPredictable ℱ (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) :=
  StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const.isLeftContinuous)

private lemma locally_martingale_finset_sum [IsFiniteMeasure P] {κ : Type*} (s : Finset κ)
    {X : κ → ℝ≥0 → Ω → ℝ}
    (hloc : ∀ k ∈ s, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (X k) P)
    (hpred : ∀ k ∈ s, IsStronglyPredictable ℱ (X k))
    (hcont : ∀ k ∈ s, ∀ᵐ ω ∂P, Continuous (X k · ω)) :
    IsStronglyPredictable ℱ (fun t ω ↦ ∑ k ∈ s, X k t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ ∑ k ∈ s, X k t ω)) ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ ∑ k ∈ s, X k t ω) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨isStronglyPredictable_zero, ae_of_all P fun _ ↦ continuous_const,
      Locally.of_prop (martingale_zero ℝ ℱ P)⟩
  | @insert a s ha ih =>
    obtain ⟨hsp, hsc, hsl⟩ := ih (fun k hk ↦ hloc k (Finset.mem_insert_of_mem hk))
      (fun k hk ↦ hpred k (Finset.mem_insert_of_mem hk))
      (fun k hk ↦ hcont k (Finset.mem_insert_of_mem hk))
    have hap := hpred a (Finset.mem_insert_self a s)
    have hac := hcont a (Finset.mem_insert_self a s)
    have hal := hloc a (Finset.mem_insert_self a s)
    have heq : (fun t ω ↦ ∑ k ∈ insert a s, X k t ω) =
        fun t ω ↦ X a t ω + ∑ k ∈ s, X k t ω := by
      ext t ω; exact Finset.sum_insert ha
    have hcont_ins : ∀ᵐ ω ∂P, Continuous (fun t ↦ ∑ k ∈ insert a s, X k t ω) := by
      filter_upwards [hac, hsc] with ω haω hsω
      have hω : (fun t ↦ ∑ k ∈ insert a s, X k t ω) = fun t ↦ X a t ω + ∑ k ∈ s, X k t ω :=
        funext fun t ↦ Finset.sum_insert ha
      rw [hω]; exact haω.add hsω
    rw [heq]
    exact ⟨hap.add hsp, by simpa only [← heq] using hcont_ins,
      locally_martingale_add_of_isStronglyPredictable hal hsl hap hsp hac hsc⟩

private lemma isStronglyPredictable_prod_sub_zero_sub_linear {U V : ℝ≥0 → Ω → ℝ}
    (hU : IsStronglyPredictable ℱ U) (hV : IsStronglyPredictable ℱ V) (c : ℝ) :
    IsStronglyPredictable ℱ (fun t ω ↦ U t ω * V t ω - U 0 ω * V 0 ω - c * (t : ℝ)) := by
  have h0sm : StronglyMeasurable[ℱ 0] (fun ω ↦ U 0 ω * V 0 ω) :=
    (hU.isStronglyProgressive.stronglyAdapted 0).mul (hV.isStronglyProgressive.stronglyAdapted 0)
  have h0 : IsStronglyPredictable ℱ (fun (_ : ℝ≥0) ω ↦ U 0 ω * V 0 ω) :=
    StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
      (fun _ ↦ h0sm.mono (ℱ.mono bot_le)) (fun _ ↦ continuous_const.isLeftContinuous)
  have ht : IsStronglyPredictable ℱ (fun (t : ℝ≥0) (_ : Ω) ↦ c * (t : ℝ)) :=
    StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
      (fun _ ↦ stronglyMeasurable_const)
      (fun _ ↦ (continuous_const.mul NNReal.continuous_coe).isLeftContinuous)
  have h1 : IsStronglyPredictable ℱ (fun t ω ↦ U t ω * V t ω - U 0 ω * V 0 ω) := by
    simpa only [sub_eq_add_neg, neg_one_mul] using (hU.mul hV).add (h0.const_mul (-1))
  simpa only [sub_eq_add_neg, neg_one_mul] using h1.add (ht.const_mul (-1))

/-- Pass from a family of continuous local martingales to strongly predictable indistinguishable
representatives preserving both coordinate and cross-bracket locality. -/
private lemma exists_predictable_vector_rep {ι : Type*}
    {M : ι → ℝ≥0 → Ω → ℝ} {C : ι → ι → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    ∃ Y : ι → ℝ≥0 → Ω → ℝ,
      (∀ i, IsStronglyPredictable ℱ (Y i)) ∧
      (∀ i, Y i ≡ᵐ[P] M i) ∧
      (∀ i, ∀ᵐ ω ∂P, Continuous (Y i · ω)) ∧
      (∀ i, Locally (fun U ↦ Martingale U ℱ P) ℱ (Y i) P) ∧
      (∀ i j, Locally (fun U ↦ Martingale U ℱ P) ℱ
        (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω - C i j * (t : ℝ)) P) := by
  have hex : ∀ i, ∃ Yi : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ Yi ∧ Yi ≡ᵐ[P] M i ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ Yi P := fun i ↦
    (hM i).exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      ((hcont i).mono fun _ h ↦ h.isLeftContinuous)
  choose Y hYp hYM hYl using hex
  have hYc : ∀ i, ∀ᵐ ω ∂P, Continuous (Y i · ω) := fun i ↦ by
    filter_upwards [hcont i, hYM i] with ω hω heq
    simpa only [funext heq] using hω
  have hQY : ∀ i j, Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω - C i j * (t : ℝ)) P := fun i j ↦ by
    refine (isStronglyPredictable_prod_sub_zero_sub_linear (hYp i) (hYp j)
      (C i j)).isStronglyProgressive.locally_martingale_of_indist (hQ i j) ?_
    filter_upwards [hYM i, hYM j] with ω hi hj t
    simp [hi t, hj t, hi 0, hj 0]
  exact ⟨Y, hYp, hYM, hYc, hYl, hQY⟩

private lemma aemeasurable_sub_coord {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (s t : ℝ≥0) :
    AEMeasurable (fun ω ↦ M t ω - M s ω) P := by
  obtain ⟨Y, hYp, hYM, _⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hm : Measurable (fun ω ↦ Y t ω - Y s ω) :=
    ((hYp.isStronglyProgressive.stronglyAdapted t).mono (ℱ.le t)).measurable.sub
      ((hYp.isStronglyProgressive.stronglyAdapted s).mono (ℱ.le s)).measurable
  exact hm.aemeasurable.congr (hYM.mono fun ω hω ↦ by simp [hω t, hω s])

private lemma aemeasurable_sub_pi {ι : Type*} [Countable ι]
    {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) (s t : ℝ≥0) :
    AEMeasurable (fun ω i ↦ M i t ω - M i s ω) P :=
  aemeasurable_pi_iff.2 fun i ↦ aemeasurable_sub_coord (hM i) (hcont i) s t

end LocalMartingaleLinearComb

section VectorCharacteristicFunction

/-- **Cramér–Wold characteristic-function factorization for vector continuous local martingales.**
If `M : ι → ℝ≥0 → Ω → ℝ` is a finite family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets `M i t * M j t - M i 0 * M j 0 - C i j * t` are local martingales, then for
every frequency vector `v : ι → ℝ`, every `s ≤ t`, and every `A ∈ ℱ s`, the complex exponential
of the linear combination `∑ i, v i * (M i t - M i s)` integrates over `A` to
`(P A).toReal * exp (-(∑ i, ∑ j, v i * v j * C i j) * (t - s) / 2)`. -/
theorem setIntegral_exp_I_mul_sum_sub_of_locally_martingale [IsFiniteMeasure P] {ι : Type*}
    [Fintype ι] {M : ι → ℝ≥0 → Ω → ℝ} {C : ι → ι → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω))
    (v : ι → ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, exp (I * ∑ i, v i * (M i t ω - M i s ω)) ∂P =
      ((P A).toReal : ℂ) *
        exp (-((∑ i, ∑ j, v i * v j * C i j) * ((t : ℝ) - s) / 2 : ℝ)) := by
  obtain ⟨Y, hYp, hYM, hYc, hYl, hQY⟩ := exists_predictable_vector_rep hM hQ hcont
  let Y_v : ℝ≥0 → Ω → ℝ := fun u ω ↦ ∑ i, v i * Y i u ω
  obtain ⟨_, hYv_c, hYv_l⟩ := locally_martingale_finset_sum Finset.univ
    (X := fun i u ω ↦ v i * Y i u ω)
    (fun i _ ↦ locally_martingale_const_mul (v i) (hYl i))
    (fun i _ ↦ (hYp i).const_mul (v i))
    (fun i _ ↦ (hYc i).mono fun _ h ↦ continuous_const.mul h)
  have hinner (i : ι) := locally_martingale_finset_sum Finset.univ
    (X := fun j u ω ↦
      (v i * v j) * (Y i u ω * Y j u ω - Y i 0 ω * Y j 0 ω - C i j * (u : ℝ)))
    (fun j _ ↦ locally_martingale_const_mul (v i * v j) (hQY i j))
    (fun j _ ↦ (isStronglyPredictable_prod_sub_zero_sub_linear (hYp i) (hYp j)
      (C i j)).const_mul (v i * v j))
    (fun j _ ↦ (hYc i).mp ((hYc j).mono fun _ hj hi ↦
      continuous_const.mul (((hi.mul hj).sub continuous_const).sub
        (continuous_const.mul NNReal.continuous_coe))))
  obtain ⟨_, _, hQsum⟩ := locally_martingale_finset_sum Finset.univ
    (fun i _ ↦ (hinner i).2.2) (fun i _ ↦ (hinner i).1) (fun i _ ↦ (hinner i).2.1)
  have hQeq : (fun u ω ↦ Y_v u ω ^ 2 - Y_v 0 ω ^ 2 - (∑ i, ∑ j, v i * v j * C i j) * (u : ℝ)) =
      fun u ω ↦ ∑ i, ∑ j, (v i * v j) *
        (Y i u ω * Y j u ω - Y i 0 ω * Y j 0 ω - C i j * (u : ℝ)) := by
    ext u ω
    have hsq (f : ι → ℝ) : (∑ i, f i) ^ 2 = ∑ i, ∑ j, f i * f j := by
      rw [sq, Finset.sum_mul]; simp_rw [Finset.mul_sum]
    simp only [Y_v, hsq]
    simp_rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hQYv : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun u ω ↦ Y_v u ω ^ 2 - Y_v 0 ω ^ 2 - (∑ i, ∑ j, v i * v j * C i j) * (u : ℝ)) P :=
    hQeq ▸ hQsum
  have hscalar := Locally.setIntegral_exp_I_mul_sub hYv_l hQYv hYv_c 1 hst hA
  have hae : ∀ᵐ ω ∂P, ∀ i, ∀ u, Y i u ω = M i u ω := ae_all_iff.2 hYM
  have hint : ∫ ω in A, exp (I * ∑ i, v i * (M i t ω - M i s ω)) ∂P =
      ∫ ω in A, exp (I * (1 : ℝ) * (Y_v t ω - Y_v s ω)) ∂P := by
    refine setIntegral_congr_ae (ℱ.le s A hA) (hae.mono fun ω hω _ ↦ ?_)
    congr 1
    simp only [Y_v, Complex.ofReal_one, mul_one]
    rw [← Complex.ofReal_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hω i t, hω i s, mul_sub]
  rw [hint, hscalar]; simp only [one_pow, one_mul]

private lemma indep_comap_sub_pi_fintype [IsZeroOrProbabilityMeasure P] {ι : Type*} [Finite ι]
    {M : ι → ℝ≥0 → Ω → ℝ} {C : ι → ι → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (.comap (fun ω i ↦ M i t ω - M i s ω) inferInstance) (ℱ s) P := by
  have := Fintype.ofFinite ι
  let e : (ι → ℝ) ≃ᵐ EuclideanSpace ℝ ι := MeasurableEquiv.toLp 2 (ι → ℝ)
  let X : Ω → EuclideanSpace ℝ ι := fun ω ↦ e (fun i ↦ M i t ω - M i s ω)
  have hX : AEMeasurable X P :=
    e.measurable.comp_aemeasurable (aemeasurable_sub_pi hM hcont s t)
  have hcomap : MeasurableSpace.comap (fun ω i ↦ M i t ω - M i s ω) inferInstance =
      MeasurableSpace.comap X inferInstance := by
    refine le_antisymm ?_ ?_
    · have heq : (fun ω i ↦ M i t ω - M i s ω) = e.symm ∘ X := by ext ω i; simp [X, e]
      rw [heq, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono e.symm.measurable.comap_le
    · have heq : X = e ∘ (fun ω i ↦ M i t ω - M i s ω) := rfl
      rw [heq, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono e.measurable.comap_le
  rw [hcomap]
  refine indep_comap_of_setIntegral_exp_inner_I (ℱ.le s) hX
    (φ := fun v : EuclideanSpace ℝ ι ↦
      exp (-((∑ i, ∑ j, v i * v j * C i j) * ((t : ℝ) - s) / 2 : ℝ))) fun v A hA ↦ ?_
  have hlhs : (fun ω ↦ exp ((⟪X ω, v⟫ : ℂ) * I)) =
      fun ω ↦ exp (I * ∑ i, v i * (M i t ω - M i s ω)) := by
    ext ω
    simp only [X, e, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      MeasurableEquiv.toLp_apply]
    congr 1; push_cast; ring
  rw [hlhs]
  exact setIntegral_exp_I_mul_sum_sub_of_locally_martingale hM hQ hcont (fun i ↦ v i) hst hA

/-- **Joint increment independence from the past for vector continuous local martingales.**
If `M : ι → ℝ≥0 → Ω → ℝ` is a family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets `M i t * M j t - M i 0 * M j 0 - C i j * t` are local martingales, then for
every `s ≤ t`, the vector increment `ω ↦ (M i t ω - M i s ω)_i` is independent of `ℱ s`. -/
theorem indep_comap_sub_pi_of_locally_martingale [IsZeroOrProbabilityMeasure P] {ι : Type*}
    {M : ι → ℝ≥0 → Ω → ℝ} {C : ι → ι → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (.comap (fun ω i ↦ M i t ω - M i s ω) inferInstance) (ℱ s) P := by
  have hid : @Measurable Ω Ω mΩ (ℱ s) id := fun _ hA ↦ ℱ.le s _ hA
  have hind : @IndepFun Ω (ι → ℝ) Ω mΩ inferInstance (ℱ s)
      (fun ω i ↦ M i t ω - M i s ω) id P := by
    refine @IndepFun.process_indepFun₀ ι Ω mΩ P (fun _ ↦ ℝ) Ω (fun _ ↦ inferInstance) (ℱ s)
      (fun i ω ↦ M i t ω - M i s ω) id
      (fun i ↦ aemeasurable_sub_coord (hM i) (hcont i) s t)
      (@Measurable.aemeasurable Ω Ω mΩ (ℱ s) id P hid) (fun I ↦ ?_) _
    have hI := indep_comap_sub_pi_fintype (M := fun (i : I) ↦ M i) (C := fun (i j : I) ↦ C i j)
      (fun i ↦ hM i) (fun i j ↦ hQ i j) (fun i ↦ hcont i) hst
    simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hI
  simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hind

/-- **Product Gaussian increment law under orthogonal vector Lévy hypotheses.**
If `M : ι → ℝ≥0 → Ω → ℝ` is a finite family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets satisfy `M i t * M j t - M i 0 * M j 0 - δ_{ij} c_i t` is a local
martingale (`c : ι → ℝ≥0`), then for `s ≤ t` the vector increment `ω ↦ (M i t ω - M i s ω)_i` has
product Gaussian law `Measure.pi (fun i ↦ gaussianReal 0 (c i * (t - s)))`. -/
theorem hasLaw_sub_pi_gaussianReal_of_locally_martingale [IsProbabilityMeasure P] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ} {c : ι → ℝ≥0}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω -
        (if i = j then (c i : ℝ) * (t : ℝ) else 0)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω i ↦ M i t ω - M i s ω)
      (Measure.pi fun i : ι ↦ gaussianReal 0 (c i * (t - s))) P where
  aemeasurable := aemeasurable_sub_pi hM hcont s t
  map_eq := by
    have hX := aemeasurable_sub_pi hM hcont s t
    have : IsFiniteMeasure (P.map (fun ω i ↦ M i t ω - M i s ω)) := Measure.isFiniteMeasure_map P _
    rw [← charFun_eq_pi_iff]
    intro v
    have hQ' : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
        (fun u ω ↦ M i u ω * M j u ω - M i 0 ω * M j 0 ω -
          (if i = j then (c i : ℝ) else 0) * (u : ℝ)) P := fun i j ↦ by
      simpa only [ite_mul, zero_mul] using hQ i j
    have hset := setIntegral_exp_I_mul_sum_sub_of_locally_martingale hM hQ' hcont
      (fun i ↦ v i) hst MeasurableSet.univ
    rw [Measure.restrict_univ, measure_univ, ENNReal.toReal_one, Complex.ofReal_one,
      one_mul] at hset
    have hX2 : AEMeasurable (fun ω ↦ WithLp.toLp 2 (fun i ↦ M i t ω - M i s ω)) P :=
      (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp_aemeasurable hX
    have hmap : (P.map (fun ω i ↦ M i t ω - M i s ω)).map (WithLp.toLp 2) =
        P.map (fun ω ↦ WithLp.toLp 2 (fun i ↦ M i t ω - M i s ω)) :=
      (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.aemeasurable.map_map_of_aemeasurable hX
    have hf_asm : AEStronglyMeasurable
        (fun x : PiLp 2 (fun _ : ι ↦ ℝ) ↦ exp ((⟪x, v⟫ : ℂ) * I))
        (P.map (fun ω ↦ WithLp.toLp 2 (fun i ↦ M i t ω - M i s ω))) :=
      (continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_id.inner continuous_const)).mul continuous_const)).aestronglyMeasurable
    rw [hmap, charFun_apply, integral_map hX2 hf_asm]
    have hlhs : (fun ω ↦ exp ((⟪WithLp.toLp 2 (fun i ↦ M i t ω - M i s ω), v⟫ : ℂ) * I)) =
        fun ω ↦ exp (I * ∑ i, v i * (M i t ω - M i s ω)) := by
      ext ω; simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      congr 1; push_cast; ring
    rw [hlhs, hset]
    simp_rw [charFun_gaussianReal, ← Complex.exp_sum]
    congr 1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      NNReal.coe_mul, NNReal.coe_sub hst, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
      Finset.sum_neg_distrib, ← Finset.sum_div]
    push_cast
    rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring

end VectorCharacteristicFunction

section PathwiseCoordinateIndependence

/-- If a two-parameter family `(X i j)` of measurable random variables is independent across `i`
as tuples `(X i ·)` and independent across `j` for each fixed `i`, then it is also independent
across `j` as tuples `(X · j)`. -/
private lemma iIndepFun_swap [IsProbabilityMeasure P] {α β E : Type*} [MeasurableSpace E]
    {X : α → β → Ω → E} (mX : ∀ a b, Measurable (X a b))
    (h1 : iIndepFun (fun a ω b ↦ X a b ω) P) (h2 : ∀ a, iIndepFun (X a) P) :
    iIndepFun (fun b ω a ↦ X a b ω) P := by
  have hprod : iIndepFun (fun (p : α × β) ω ↦ X p.1 p.2 ω) P := iIndepFun_uncurry' mX h1 h2
  have hsig : iIndepFun (fun (p : Sigma fun _ : β ↦ α) ω ↦ X p.2 p.1 ω) P :=
    hprod.precomp (g := fun (p : Sigma fun _ : β ↦ α) ↦ (p.2, p.1)) fun p q h ↦ by
      rcases p with ⟨b₁, a₁⟩; rcases q with ⟨b₂, a₂⟩
      simp only [Prod.mk.injEq] at h; cases h.1; cases h.2; rfl
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  have hcur : (MeasurableEquiv.piCurry (fun (_ : β) (_ : α) ↦ E)) ∘
      (fun ω (p : Sigma fun _ : β ↦ α) ↦ X p.2 p.1 ω) = fun ω b a ↦ X a b ω := by
    ext; simp [Sigma.curry]
  rw [← hcur, ← Measure.map_map (by fun_prop) (by fun_prop),
    (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 hsig,
    Measure.infinitePi_map_piCurry (fun b a ↦ P.map (X a b))]
  congrm Measure.infinitePi fun b ↦ ?_
  have hb : iIndepFun (fun a ω ↦ X a b ω) P :=
    hsig.precomp (g := fun a ↦ ⟨b, a⟩) fun _ _ h ↦ by simpa using h
  exact ((iIndepFun_iff_map_fun_eq_infinitePi_map (fun a ↦ mX a b)).1 hb).symm

/-- Telescoping cumulative sum on a finite sorted grid `g : Fin (m + 1) → ℝ≥0` starting at `0`. -/
private lemma eval_eq_sum_increments {m : ℕ} (g : Fin (m + 1) → ℝ≥0) {f : ℝ≥0 → ℝ}
    (hf0 : f (g 0) = 0) (k : Fin (m + 1)) :
    f (g k) = ∑ j ∈ Finset.univ.filter (fun j : Fin m ↦ j.val < k.val),
      (f (g j.succ) - f (g j.castSucc)) := by
  induction k using Fin.induction with
  | zero =>
    have hempty : Finset.univ.filter (fun j : Fin m ↦ j.val < (0 : Fin (m + 1)).val) = ∅ := by
      ext j; simp
    rw [hempty, Finset.sum_empty, hf0]
  | succ k ih =>
    have hsplit : Finset.univ.filter (fun j : Fin m ↦ j.val < k.succ.val) =
        insert k (Finset.univ.filter (fun j : Fin m ↦ j.val < k.castSucc.val)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_iff, le_iff_lt_or_eq, Fin.ext_iff]
      tauto
    have hnot : k ∉ Finset.univ.filter (fun j : Fin m ↦ j.val < k.castSucc.val) := by simp
    rw [hsplit, Finset.sum_insert hnot, ← ih]; ring

/-- Coordinatewise independence for a measurable vector process `V` starting at `0` with
independent increments whose finite-subset increments have mutually independent coordinates. -/
private lemma iIndepFun_process_of_hasIndepIncrements [IsProbabilityMeasure P] {ι : Type*}
    {V : ℝ≥0 → Ω → ι → ℝ} (hV_meas : ∀ t i, Measurable (fun ω ↦ V t ω i))
    (hV0 : ∀ ω i, V 0 ω i = 0) (hinc : HasIndepIncrements V P)
    (hcoord : ∀ (I : Finset ι) s t, s ≤ t → iIndepFun (fun (i : I) ω ↦ V t ω i - V s ω i) P) :
    iIndepFun (fun i ω t ↦ V t ω i) P := by
  refine iIndepFun.iIndepFun_process (fun i t ↦ hV_meas t i) fun I J ↦ ?_
  classical
  let T : Finset ℝ≥0 := insert 0 (Finset.univ.biUnion J)
  have h0T : (0 : ℝ≥0) ∈ T := Finset.mem_insert_self 0 _
  set m : ℕ := T.card - 1
  have hm : T.card = m + 1 := (Nat.sub_add_cancel (Finset.card_pos.2 ⟨0, h0T⟩)).symm
  let e : Fin (m + 1) ≃o T := T.orderIsoOfFin hm
  let g : Fin (m + 1) → ℝ≥0 := fun k ↦ (e k : ℝ≥0)
  have hg_mono : Monotone g := fun a b hab ↦ e.monotone hab
  have hg0 : g 0 = 0 := by
    have hle : e 0 ≤ ⟨0, h0T⟩ :=
      (e.monotone (Fin.zero_le (e.symm ⟨0, h0T⟩))).trans_eq (e.apply_symm_apply ⟨0, h0T⟩)
    exact le_antisymm (Subtype.coe_le_coe.2 hle) bot_le
  let D : Fin m → I → Ω → ℝ := fun k i ω ↦ V (g k.succ) ω i - V (g k.castSucc) ω i
  have hmD : ∀ k (i : I), Measurable (D k i) := fun k i ↦ (hV_meas _ i).sub (hV_meas _ i)
  have hincI : iIndepFun (fun (k : Fin m) ω (i : I) ↦ D k i ω) P :=
    (hinc m g hg_mono).comp (fun _ (f : ι → ℝ) (i : I) ↦ f i)
      (fun _ ↦ measurable_pi_iff.2 fun i ↦ measurable_pi_apply i.1)
  have hswap : iIndepFun (fun (i : I) ω (k : Fin m) ↦ D k i ω) P :=
    iIndepFun_swap hmD hincI fun k ↦ hcoord I _ _ (hg_mono (Fin.castSucc_le_succ k))
  let idx (i : I) (t : J i) : Fin (m + 1) :=
    e.symm ⟨t.1, Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, t.2⟩)⟩
  let Φ (i : I) (d : Fin m → ℝ) (t : J i) : ℝ :=
    ∑ j ∈ Finset.univ.filter (fun j : Fin m ↦ j.val < (idx i t).val), d j
  have hΦ : ∀ i : I, Measurable (Φ i) := fun i ↦
    measurable_pi_iff.2 fun _ ↦ Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  convert hswap.comp Φ hΦ using 1
  ext i ω t
  have hgt : g (idx i t) = t.1 := congrArg Subtype.val (e.apply_symm_apply _)
  simpa only [Φ, D, hgt, Function.comp_apply] using
    eval_eq_sum_increments g (f := fun u ↦ V u ω i) (by rw [hg0, hV0]) (idx i t)

/-- **Global pathwise coordinate independence under orthogonal vector Lévy hypotheses (arbitrary
start).**
If `M : ι → ℝ≥0 → Ω → ℝ` is a family of almost-surely continuous local martingales on `ℱ`
whose cross-brackets `M i t * M j t - M i 0 * M j 0 - δ_{ij} c_i t` are local martingales
(`c : ι → ℝ≥0`), then the centered coordinate processes `i ↦ (t ↦ M i t - M i 0)` are mutually
independent as random paths `Ω → (ℝ≥0 → ℝ)`. -/
theorem iIndepFun_sub_zero_of_locally_martingale [IsProbabilityMeasure P] {ι : Type*}
    [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ} {c : ι → ℝ≥0}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω -
        (if i = j then (c i : ℝ) * (t : ℝ) else 0)) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    iIndepFun (fun i ω t ↦ M i t ω - M i 0 ω) P := by
  let C : ι → ι → ℝ := fun i j ↦ if i = j then (c i : ℝ) else 0
  have hQ' : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ)) P := fun i j ↦ by
    simpa only [C, ite_mul, zero_mul] using hQ i j
  obtain ⟨Y, hYp, hYM, hYc, hYl, hQY⟩ := exists_predictable_vector_rep hM hQ' hcont
  let V : ℝ≥0 → Ω → ι → ℝ := fun t ω i ↦ Y i t ω - Y i 0 ω
  have hV_adapt : Adapted ℱ V := fun t ↦
    @measurable_pi_iff _ _ _ (ℱ t) _ _ |>.2 fun i ↦
      ((hYp i).isStronglyProgressive.stronglyAdapted t).measurable.sub
        (((hYp i).isStronglyProgressive.stronglyAdapted 0).measurable.mono (ℱ.mono bot_le) le_rfl)
  have hQY' : ∀ i j, Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω -
        (if i = j then (c i : ℝ) * (t : ℝ) else 0)) P := fun i j ↦ by
    simpa only [C, ite_mul, zero_mul] using hQY i j
  have hinc : HasIndepIncrements V P := hV_adapt.hasIndepIncrements fun s t hst ↦ by
    simpa only [V, Pi.sub_def, sub_sub_sub_cancel_right] using
      indep_comap_sub_pi_of_locally_martingale hYl hQY hYc hst
  have hcoord (I : Finset ι) (s t : ℝ≥0) (hst : s ≤ t) :
      iIndepFun (fun (i : I) ω ↦ V t ω i - V s ω i) P := by
    have hlaw_i (i : I) :
        HasLaw (fun ω ↦ Y i t ω - Y i s ω) (gaussianReal 0 (c i * (t - s))) P :=
      Locally.hasLaw_sub_gaussianReal (hYl i) (by simpa [sq] using hQY' i i) (hYc i) hst
    have hlaw_pi := hasLaw_sub_pi_gaussianReal_of_locally_martingale
      (M := fun (i : I) ↦ Y i) (c := fun (i : I) ↦ c i)
      (fun i ↦ hYl i) (fun i j ↦ by simpa only [Subtype.ext_iff] using hQY' i.1 j.1)
      (fun i ↦ hYc i) hst
    simpa only [V, sub_sub_sub_cancel_right] using (iIndepFun_iff_hasLaw_pi_pi hlaw_i).2 hlaw_pi
  have hV_ind : iIndepFun (fun i ω t ↦ V t ω i) P :=
    iIndepFun_process_of_hasIndepIncrements
      (fun t i ↦ (measurable_pi_apply i).comp ((hV_adapt t).mono (ℱ.le t) le_rfl))
      (fun ω i ↦ sub_self (Y i 0 ω)) hinc hcoord
  exact hV_ind.process_congr fun i t ↦ (hYM i).mono fun ω hω ↦ by simp [V, hω t, hω 0]

/-- **Global pathwise coordinate independence under orthogonal vector Lévy hypotheses (started at
zero).**
If `M : ι → ℝ≥0 → Ω → ℝ` is a family of almost-surely continuous local martingales on `ℱ`
with `M i 0 = 0` almost surely and cross-brackets `M i t * M j t - δ_{ij} c_i t` local
martingales (`c : ι → ℝ≥0`), then the coordinate processes `i ↦ M i` are mutually independent. -/
theorem iIndepFun_of_locally_martingale [IsProbabilityMeasure P] {ι : Type*} [DecidableEq ι]
    {M : ι → ℝ≥0 → Ω → ℝ} {c : ι → ℝ≥0}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - if i = j then (c i : ℝ) * (t : ℝ) else 0) P)
    (h0 : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    iIndepFun (fun i ω t ↦ M i t ω) P := by
  have hex : ∀ i, ∃ Yi : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ Yi ∧ Yi ≡ᵐ[P] M i ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ Yi P := fun i ↦
    (hM i).exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      ((hcont i).mono fun _ h ↦ h.isLeftContinuous)
  choose Y hYp hYM hYl using hex
  have hYc : ∀ i, ∀ᵐ ω ∂P, Continuous (Y i · ω) := fun i ↦ by
    filter_upwards [hcont i, hYM i] with ω hω heq; simpa only [funext heq] using hω
  have hQY : ∀ i j, Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω -
        if i = j then (c i : ℝ) * (t : ℝ) else 0) P := fun i j ↦ by
    have hp : IsStronglyProgressive ℱ
        (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω -
          if i = j then (c i : ℝ) * (t : ℝ) else 0) := by
      simpa only [ite_mul, zero_mul] using
        (isStronglyPredictable_prod_sub_zero_sub_linear (hYp i) (hYp j)
          (if i = j then (c i : ℝ) else 0)).isStronglyProgressive
    refine hp.locally_martingale_of_indist (hQ i j) ?_
    filter_upwards [hYM i, hYM j, h0 i, h0 j] with ω hi hj h0i h0j t
    simp [hi t, hj t, hi 0, hj 0, h0i, h0j]
  have hindY := iIndepFun_sub_zero_of_locally_martingale hYl hQY hYc
  refine hindY.process_congr fun i t ↦ ?_
  filter_upwards [hYM i, h0 i] with ω hω h0ω
  simp [hω t, hω 0, h0ω]

/-- **Predictable vector Brownian version under bare native locality.**
Without assuming literal adaptation of `M`, if `M : ι → ℝ≥0 → Ω → ℝ` is a family of
almost-surely continuous local martingales on `ℱ` with `M i 0 = 0` almost surely and
`M i t * M j t - δ_{ij} t` a local martingale for all `i, j`, then `M` admits a strongly
predictable indistinguishable family `W` whose coordinates are mutually independent
filtered Brownian motions relative to `ℱ` with vector increments independent of `ℱ s`. -/
theorem exists_isStronglyPredictable_indist_pi_isFilteredPreBrownianReal_of_locally_martingale
    [IsProbabilityMeasure P] {ι : Type*} [DecidableEq ι] {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M i t ω * M j t ω - if i = j then (t : ℝ) else 0) P)
    (h0 : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω)) :
    ∃ W : ι → ℝ≥0 → Ω → ℝ,
      (∀ i, IsStronglyPredictable ℱ (W i)) ∧
      (∀ i, W i ≡ᵐ[P] M i) ∧
      (∀ i, IsBrownianReal (W i) P) ∧
      (∀ i, IsFilteredPreBrownianReal ℱ (W i) P) ∧
      iIndepFun (fun i ω t ↦ W i t ω) P ∧
      (∀ s t, s ≤ t → Indep (.comap (fun ω i ↦ W i t ω - W i s ω) inferInstance) (ℱ s) P) := by
  have hex : ∀ i, ∃ Wi : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ Wi ∧ Wi ≡ᵐ[P] M i ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ Wi P := fun i ↦
    (hM i).exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      ((hcont i).mono fun _ h ↦ h.isLeftContinuous)
  choose W hWp hWM hWl using hex
  have hWc : ∀ i, ∀ᵐ ω ∂P, Continuous (W i · ω) := fun i ↦ by
    filter_upwards [hcont i, hWM i] with ω hω heq; simpa only [funext heq] using hω
  have hW0 : ∀ i, ∀ᵐ ω ∂P, W i 0 ω = 0 := fun i ↦ by
    filter_upwards [h0 i, hWM i] with ω h0ω heq; rw [heq 0, h0ω]
  have hQW : ∀ i j, Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ W i t ω * W j t ω - W i 0 ω * W j 0 ω -
        (if i = j then (1 : ℝ) else 0) * (t : ℝ)) P := fun i j ↦ by
    refine (isStronglyPredictable_prod_sub_zero_sub_linear (hWp i) (hWp j)
      (if i = j then (1 : ℝ) else 0)).isStronglyProgressive.locally_martingale_of_indist
      (hQ i j) ?_
    filter_upwards [hWM i, hWM j, h0 i, h0 j] with ω hi hj h0i h0j t
    simp [hi t, hj t, hi 0, hj 0, h0i, h0j]
  have hQdiag (i : ι) : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ W i t ω ^ 2 - W i 0 ω ^ 2 - (t : ℝ)) P := by
    simpa only [sq, ↓reduceIte, one_mul] using hQW i i
  have hFB (i : ι) : IsFilteredPreBrownianReal ℱ (W i) P :=
    (Locally.isFilteredPreBrownianReal_sub_zero (hWl i) (hQdiag i) (hWc i)
      (hWp i).isStronglyProgressive.stronglyAdapted.adapted).congr
      (hWp i).isStronglyProgressive.stronglyAdapted.adapted fun t ↦
        (hW0 i).mono fun ω h0ω ↦ by simp [h0ω]
  have hindW : iIndepFun (fun i ω t ↦ W i t ω) P := by
    refine (iIndepFun_sub_zero_of_locally_martingale (c := fun _ ↦ 1) hWl
      (fun i j ↦ by simpa only [NNReal.coe_one, one_mul, ite_mul, zero_mul] using hQW i j)
      hWc).process_congr fun i t ↦ (hW0 i).mono fun ω h0ω ↦ by simp [h0ω]
  exact ⟨W, hWp, hWM, fun i ↦ ⟨(hFB i).toIsPreBrownianReal, hWc i⟩, hFB, hindW,
    fun s t hst ↦ indep_comap_sub_pi_of_locally_martingale hWl hQW hWc hst⟩

end PathwiseCoordinateIndependence

section FilteredVectorBrownianLaw

private lemma indepFun_to_iIndepFun_bool [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E]
    {X Y : Ω → E} (h : IndepFun X Y P) :
    iIndepFun (fun b : Bool ↦ cond b Y X) P := by
  rw [iIndepFun_iff]
  intro s f hf
  by_cases h0 : false ∈ s <;> by_cases h1 : true ∈ s
  · have hs : s = {false, true} := by ext b; cases b <;> simp [h0, h1]
    subst hs
    rw [Finset.set_biInter_insert, Finset.set_biInter_singleton, Finset.prod_pair (by decide)]
    exact (Indep_iff _ _ _).1 ((IndepFun_iff_Indep _ _ _).1 h) (f false) (f true)
      (hf false (by simp)) (hf true (by simp))
  · have hs : s = {false} := by ext b; cases b <;> simp [h0, h1]
    subst hs; simp
  · have hs : s = {true} := by ext b; cases b <;> simp [h0, h1]
    subst hs; simp
  · have hs : s = ∅ := by ext b; cases b <;> simp [h0, h1]
    subst hs; simp

/-- The normalized sum `(B₁ + B₂) / √2` of two independent real Brownian motions with measurable
marginals is a real Brownian motion. -/
private lemma isBrownianReal_add_div_sqrt_two {B₁ B₂ : ℝ≥0 → Ω → ℝ}
    (hB₁ : IsBrownianReal B₁ P) (hB₂ : IsBrownianReal B₂ P)
    (hind : IndepFun (fun ω t ↦ B₁ t ω) (fun ω t ↦ B₂ t ω) P)
    (hm₁ : ∀ t, Measurable (B₁ t)) (hm₂ : ∀ t, Measurable (B₂ t)) :
    IsBrownianReal (fun t ω ↦ (1 / Real.sqrt 2) * (B₁ t ω + B₂ t ω)) P := by
  have : IsProbabilityMeasure P := (hB₁.hasLaw_eval 0).isProbabilityMeasure
  have hlaw (t : ℝ≥0) :
      HasLaw (fun ω ↦ (1 / Real.sqrt 2) * (B₁ t ω + B₂ t ω)) (gaussianReal 0 t) P := by
    have hind_t : IndepFun (B₁ t) (B₂ t) P :=
      hind.comp (measurable_pi_apply t) (measurable_pi_apply t)
    have hsum_map : P.map (B₁ t + B₂ t) = gaussianReal 0 (t + t) := by
      simpa only [add_zero] using gaussianReal_add_gaussianReal_of_indepFun
        hind_t (hB₁.hasLaw_eval t) (hB₂.hasLaw_eval t)
    have hsum : HasLaw (B₁ t + B₂ t) (gaussianReal 0 (t + t)) P :=
      ⟨(hm₁ t).aemeasurable.add (hm₂ t).aemeasurable, hsum_map⟩
    have hmul := gaussianReal_const_mul hsum (1 / Real.sqrt 2)
    have hvar : NNReal.mk ((1 / Real.sqrt 2) ^ 2) (sq_nonneg _) * (t + t) = t := by
      ext; push_cast
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    simpa only [Pi.add_apply, mul_zero, hvar] using hmul
  have hinc : HasIndepIncrements (fun t ω ↦ (1 / Real.sqrt 2) * (B₁ t ω + B₂ t ω)) P := by
    intro n g hg
    let Δ : Bool → Fin n → Ω → ℝ := fun b k ω ↦
      cond b (B₂ (g k.succ) ω - B₂ (g k.castSucc) ω) (B₁ (g k.succ) ω - B₁ (g k.castSucc) ω)
    have hΔ_meas : ∀ b k, Measurable (Δ b k) := fun b k ↦ by
      cases b
      · exact (hm₁ _).sub (hm₁ _)
      · exact (hm₂ _).sub (hm₂ _)
    have hinc_map : Measurable (fun (f : ℝ≥0 → ℝ) (k : Fin n) ↦ f (g k.succ) - f (g k.castSucc)) :=
      measurable_pi_iff.2 fun k ↦ (measurable_pi_apply _).sub (measurable_pi_apply _)
    have h1 : iIndepFun (fun b ω k ↦ Δ b k ω) P := by
      convert indepFun_to_iIndepFun_bool (hind.comp hinc_map hinc_map) using 1
      ext b ω k; cases b <;> rfl
    have h2 : ∀ b, iIndepFun (Δ b) P := fun b ↦ by
      cases b
      · exact hB₁.hasIndepIncrements n g hg
      · exact hB₂.hasIndepIncrements n g hg
    have hswap := iIndepFun_swap hΔ_meas h1 h2
    have hcomb : Measurable (fun (f : Bool → ℝ) ↦ (1 / Real.sqrt 2) * (f false + f true)) :=
      measurable_const.mul ((measurable_pi_apply false).add (measurable_pi_apply true))
    convert hswap.comp (fun _ ↦ fun f ↦ (1 / Real.sqrt 2) * (f false + f true))
      (fun _ ↦ hcomb) using 1
    ext k ω; simp only [Δ, Function.comp_apply, Bool.cond_false, Bool.cond_true]; ring
  exact ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw hlaw hinc,
    hB₁.cont.mp (hB₂.cont.mono fun _ h₂ h₁ ↦ continuous_const.mul (h₁.add h₂))⟩

/-- **Cross-product martingale property for independent Brownian local martingales.**
If `B₁` and `B₂` are independent real Brownian motions that are adapted local martingales on `ℱ`,
then their product `t ↦ B₁ t * B₂ t` is a true `ℱ`-martingale. The proof polarizes via the
Brownian motion `(B₁ + B₂) / √2`. -/
theorem martingale_mul_of_indepFun_isBrownianReal {B₁ B₂ : ℝ≥0 → Ω → ℝ}
    (hB₁ : IsBrownianReal B₁ P) (hB₂ : IsBrownianReal B₂ P)
    (hind : IndepFun (fun ω t ↦ B₁ t ω) (fun ω t ↦ B₂ t ω) P)
    (hA₁ : Adapted ℱ B₁) (hA₂ : Adapted ℱ B₂)
    (hloc₁ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B₁ P)
    (hloc₂ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B₂ P) :
    Martingale (fun t ω ↦ B₁ t ω * B₂ t ω) ℱ P := by
  have hFB₁ := hB₁.isFilteredPreBrownianReal_of_locally_martingale hA₁ hloc₁
  have hFB₂ := hB₂.isFilteredPreBrownianReal_of_locally_martingale hA₂ hloc₂
  let W : ℝ≥0 → Ω → ℝ := fun t ω ↦ (1 / Real.sqrt 2) * (B₁ t ω + B₂ t ω)
  have hW : IsBrownianReal W P := isBrownianReal_add_div_sqrt_two hB₁ hB₂ hind
    (fun t ↦ (hA₁ t).mono (ℱ.le t) le_rfl) (fun t ↦ (hA₂ t).mono (ℱ.le t) le_rfl)
  have hWA : Adapted ℱ W := fun t ↦ measurable_const.mul ((hA₁ t).add (hA₂ t))
  have hWM : Martingale W ℱ P := by
    convert (hFB₁.martingale.add hFB₂.martingale).smul (1 / Real.sqrt 2) using 1
  have hFW := hW.isFilteredPreBrownianReal_of_locally_martingale hWA (Locally.of_prop hWM)
  have hpol : Martingale (fun t ω ↦ (W t ω ^ 2 - (t : ℝ)) -
      (1 / 2 : ℝ) * (B₁ t ω ^ 2 - (t : ℝ)) - (1 / 2 : ℝ) * (B₂ t ω ^ 2 - (t : ℝ))) ℱ P := by
    convert (hFW.martingale_sq_sub.sub (hFB₁.martingale_sq_sub.smul (1 / 2))).sub
      (hFB₂.martingale_sq_sub.smul (1 / 2)) using 1
  convert hpol using 1
  ext t ω
  have hsq : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [W, mul_pow, hsq]; ring

/-- **Filtered vector Brownian-law corollary.**
If `B : ι → ℝ≥0 → Ω → ℝ` is a family of mutually independent real Brownian motions that
are adapted local martingales on `ℱ`, then for every `s ≤ t` the vector increment
`ω ↦ (B i t ω - B i s ω)_i` is independent of `ℱ s`. -/
theorem indep_comap_sub_pi_of_iIndepFun_isBrownianReal_locally_martingale
    {ι : Type*} {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t ↦ B i t ω) P)
    (hA : ∀ i, Adapted ℱ (B i))
    (hloc : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (B i) P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (.comap (fun ω i ↦ B i t ω - B i s ω) inferInstance) (ℱ s) P := by
  classical
  have := hind.isProbabilityMeasure
  let C : ι → ι → ℝ := fun i j ↦ if i = j then 1 else 0
  have hQ (i j : ι) : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun u ω ↦ B i u ω * B j u ω - B i 0 ω * B j 0 ω - C i j * (u : ℝ)) P := by
    have hsm : StronglyAdapted ℱ
        (fun u ω ↦ B i u ω * B j u ω - B i 0 ω * B j 0 ω - C i j * (u : ℝ)) := fun u ↦
      ((((hA i u).mul (hA j u)).sub
        (((hA i 0).mul (hA j 0)).mono (ℱ.mono bot_le) le_rfl)).sub
        measurable_const).stronglyMeasurable
    have h0ae : ∀ᵐ ω ∂P, B i 0 ω * B j 0 ω = 0 :=
      (hB i).eval_zero_ae_eq_zero.mono fun ω hω ↦ by simp [hω]
    by_cases hij : i = j
    · subst hij
      have hmart := ((hB i).isFilteredPreBrownianReal_of_locally_martingale (hA i)
        (hloc i)).martingale_sq_sub
      refine Locally.of_prop (hmart.congr hsm fun u ↦ h0ae.mono fun ω h0ω ↦ ?_)
      simp [C, sq, h0ω]
    · have hmart := martingale_mul_of_indepFun_isBrownianReal (hB i) (hB j) (hind.indepFun hij)
        (hA i) (hA j) (hloc i) (hloc j)
      refine Locally.of_prop (hmart.congr hsm fun u ↦ h0ae.mono fun ω h0ω ↦ ?_)
      simp [C, hij, h0ω]
  exact indep_comap_sub_pi_of_locally_martingale hloc hQ (fun i ↦ (hB i).cont) hst

end FilteredVectorBrownianLaw

end TauCeti.Probability
