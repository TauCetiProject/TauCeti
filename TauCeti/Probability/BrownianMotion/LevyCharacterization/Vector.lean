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

Multivariate Lévy characterization for a family `M : ι → ℝ≥0 → Ω → ℝ` of almost-surely continuous
real local martingales on a raw filtration `ℱ` with local-martingale cross-brackets
`M i t * M j t - M i 0 * M j 0 - C i j * t`: Cramér–Wold characteristic-function factorization,
joint increment independence from `ℱ s`, product Gaussian increment laws, global pathwise
coordinate independence, strongly predictable indistinguishable vector Brownian versions, and the
converse cross-product martingale and vector increment independence theorems for independent
Brownian local martingales.

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

private abbrev maskStop (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ

private lemma martingale_maskStop_of_le [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}
    (hprog : IsStronglyProgressive ℱ X) (hcont : ∀ᵐ ω ∂P, Continuous (X · ω))
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hle : τ ≤ σ) (hmart : Martingale (maskStop X σ) ℱ P) : Martingale (maskStop X τ) ℱ P := by
  convert hmart.stoppedProcess_indicator_of_ae_isRightContinuous (fun T ↦ by
      let : MeasurableSpace Ω := ℱ T
      convert ((hprog.stoppedProcess hσ) T).indicator (MeasurableSet.univ.prod (ℱ.mono bot_le _
        (by simpa only [bot_eq_zero, WithTop.coe_zero] using hσ.measurableSet_gt ⊥))) using 1
      ext ⟨t, ω⟩; rw [maskStop, stoppedProcess_indicator_comm]; by_cases hω : 0 < σ ω <;> simp [hω])
    (hcont.mono fun ω hω ↦ by
      rw [show (maskStop X σ · ω) = fun t ↦ if 0 < σ ω then stoppedProcess X σ t ω else 0 by
        funext t; simp [maskStop, stoppedProcess_indicator_comm, Set.indicator_apply]]
      split_ifs
      · exact fun _ ↦ hω.continuousWithinAt.stoppedProcess
      · exact continuous_const.isRightContinuous) hτ using 1
  simp only [maskStop, stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
  ext t ω; by_cases hω : 0 < τ ω
  · simp [Set.indicator_of_mem, hω, lt_of_lt_of_le hω (hle ω), stoppedProcess, min_eq_left (hle ω)]
  · simp [Set.indicator_of_notMem, hω]

private lemma locally_martingale_const_mul {X : ℝ≥0 → Ω → ℝ} (a : ℝ)
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ a * X t ω) P :=
  ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ by
    convert (hX.stoppedProcess_localSeq n).smul a using 1
    ext t ω; simp only [Pi.smul_apply, smul_eq_mul, stoppedProcess_indicator_comm,
      Set.indicator_apply]; split_ifs <;> simp [stoppedProcess]⟩

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
    exact ⟨StronglyAdapted.isStronglyPredictable_of_continuous (fun _ ↦ stronglyMeasurable_const)
      (fun _ ↦ continuous_const), ae_of_all P fun _ ↦ continuous_const,
      Locally.of_prop (martingale_zero ℝ ℱ P)⟩
  | @insert a s ha ih =>
    obtain ⟨hsp, hsc, hsl⟩ := ih (fun k hk ↦ hloc k (Finset.mem_insert_of_mem hk))
      (fun k hk ↦ hpred k (Finset.mem_insert_of_mem hk))
      (fun k hk ↦ hcont k (Finset.mem_insert_of_mem hk))
    have hap := hpred a (Finset.mem_insert_self a s)
    have hac := hcont a (Finset.mem_insert_self a s)
    have hal := hloc a (Finset.mem_insert_self a s)
    have hτ := hal.isLocalizingSequence_localSeq.min hsl.isLocalizingSequence_localSeq
    simp_rw [Finset.sum_insert ha]
    refine ⟨hap.add hsp, hac.mp (hsc.mono fun _ hs' ha' ↦ ha'.add hs'),
      min hal.localSeq hsl.localSeq, hτ, fun n ↦ ?_⟩
    convert (martingale_maskStop_of_le hap.isStronglyProgressive hac
        (hal.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
        (fun _ ↦ min_le_left _ _) (hal.stoppedProcess_localSeq n)).add
      (martingale_maskStop_of_le hsp.isStronglyProgressive hsc
        (hsl.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
        (fun _ ↦ min_le_right _ _) (hsl.stoppedProcess_localSeq n)) using 1
    ext t ω; simp only [Pi.add_apply, maskStop, stoppedProcess_indicator_comm, Set.indicator_apply,
      Set.mem_ofPred_eq, bot_eq_zero]; split_ifs <;> simp [stoppedProcess]

private lemma isStronglyPredictable_prod_sub_zero_sub_linear {U V : ℝ≥0 → Ω → ℝ}
    (hU : IsStronglyPredictable ℱ U) (hV : IsStronglyPredictable ℱ V) (c : ℝ) :
    IsStronglyPredictable ℱ (fun t ω ↦ U t ω * V t ω - U 0 ω * V 0 ω - c * (t : ℝ)) := by
  simpa only [sub_eq_add_neg, neg_one_mul, Pi.mul_apply] using ((hU.mul hV).add
    ((StronglyAdapted.isStronglyPredictable_of_continuous (fun _ ↦
      ((hU.isStronglyProgressive.stronglyAdapted 0).mul
        (hV.isStronglyProgressive.stronglyAdapted 0)).mono (ℱ.mono bot_le))
      (fun _ ↦ continuous_const)).const_mul (-1))).add
    ((StronglyAdapted.isStronglyPredictable_of_continuous (fun _ ↦ stronglyMeasurable_const)
      (fun _ ↦ continuous_const.mul NNReal.continuous_coe)).const_mul (-1))

private lemma exists_predictable_rep {ι : Type*} {M : ι → ℝ≥0 → Ω → ℝ} {C : ι → ι → ℝ}
    {Q : ι → ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (M i) P)
    (hQ : ∀ i j, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (Q i j) P)
    (hcont : ∀ i, ∀ᵐ ω ∂P, Continuous (M i · ω))
    (hQM : ∀ i j, ∀ᵐ ω ∂P, ∀ t,
      M i t ω * M j t ω - M i 0 ω * M j 0 ω - C i j * (t : ℝ) = Q i j t ω) :
    ∃ Y : ι → ℝ≥0 → Ω → ℝ, (∀ i, IsStronglyPredictable ℱ (Y i)) ∧ (∀ i, Y i ≡ᵐ[P] M i) ∧
      (∀ i, ∀ᵐ ω ∂P, Continuous (Y i · ω)) ∧
      (∀ i, Locally (fun U ↦ Martingale U ℱ P) ℱ (Y i) P) ∧
      (∀ i j, Locally (fun U ↦ Martingale U ℱ P) ℱ
        (fun t ω ↦ Y i t ω * Y j t ω - Y i 0 ω * Y j 0 ω - C i j * (t : ℝ)) P) := by
  choose Y hYp hYM hYl using fun i ↦
    (hM i).exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      ((hcont i).mono fun _ h ↦ h.isLeftContinuous)
  refine ⟨Y, hYp, hYM,
    fun i ↦ by filter_upwards [hcont i, hYM i] with _ hω heq; simpa only [funext heq] using hω,
    hYl, fun i j ↦ (isStronglyPredictable_prod_sub_zero_sub_linear (hYp i) (hYp j)
      (C i j)).isStronglyProgressive.locally_martingale_of_indist (hQ i j) ?_⟩
  filter_upwards [hYM i, hYM j, hQM i j] with _ hi hj hq t
  simpa [hi t, hj t, hi 0, hj 0] using (hq t).symm

private lemma aemeasurable_sub_coord {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (s t : ℝ≥0) :
    AEMeasurable (fun ω ↦ M t ω - M s ω) P := by
  obtain ⟨Y, hYp, hYM, _⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  exact (((hYp.isStronglyProgressive.stronglyAdapted t).mono (ℱ.le t)).measurable.sub
    ((hYp.isStronglyProgressive.stronglyAdapted s).mono (ℱ.le s)).measurable).aemeasurable.congr
      (hYM.mono fun _ hω ↦ by simp [hω t, hω s])

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
  obtain ⟨Y, hYp, hYM, hYc, hYl, hQY⟩ :=
    exists_predictable_rep hM hQ hcont (fun _ _ ↦ ae_of_all P fun _ _ ↦ rfl)
  obtain ⟨_, hYv_c, hYv_l⟩ := locally_martingale_finset_sum Finset.univ
    (X := fun i u ω ↦ v i * Y i u ω) (fun i _ ↦ locally_martingale_const_mul (v i) (hYl i))
    (fun i _ ↦ (hYp i).const_mul (v i)) (fun i _ ↦ (hYc i).mono fun _ h ↦ continuous_const.mul h)
  obtain ⟨_, _, hQsum⟩ := locally_martingale_finset_sum (Finset.univ : Finset (ι × ι))
    (X := fun p u ω ↦
      (v p.1 * v p.2) * (Y p.1 u ω * Y p.2 u ω - Y p.1 0 ω * Y p.2 0 ω - C p.1 p.2 * (u : ℝ)))
    (fun p _ ↦ locally_martingale_const_mul (v p.1 * v p.2) (hQY p.1 p.2))
    (fun p _ ↦ (isStronglyPredictable_prod_sub_zero_sub_linear (hYp p.1) (hYp p.2)
      (C p.1 p.2)).const_mul (v p.1 * v p.2))
    (fun p _ ↦ (hYc p.1).mp ((hYc p.2).mono fun _ hj hi ↦ continuous_const.mul
      (((hi.mul hj).sub continuous_const).sub (continuous_const.mul NNReal.continuous_coe))))
  have hQeq : (fun u ω ↦ (∑ i, v i * Y i u ω) ^ 2 - (∑ i, v i * Y i 0 ω) ^ 2 -
        (∑ i, ∑ j, v i * v j * C i j) * (u : ℝ)) =
      fun u ω ↦ ∑ p : ι × ι, (v p.1 * v p.2) *
        (Y p.1 u ω * Y p.2 u ω - Y p.1 0 ω * Y p.2 0 ω - C p.1 p.2 * (u : ℝ)) := by
    ext u ω; rw [Fintype.sum_prod_type]
    have hsq (f : ι → ℝ) : (∑ i, f i) ^ 2 = ∑ i, ∑ j, f i * f j := by
      rw [sq, Finset.sum_mul]; simp_rw [Finset.mul_sum]
    simp only [hsq]; simp_rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [setIntegral_congr_ae (ℱ.le s A hA)
      (g := fun ω ↦ exp (I * (1 : ℝ) * ((∑ i, v i * Y i t ω) - ∑ i, v i * Y i s ω)))
      ((ae_all_iff.2 hYM).mono fun ω hω _ ↦ by
        simp only [Complex.ofReal_one, mul_one, ← Complex.ofReal_sub, ← Finset.sum_sub_distrib]
        congr 3; exact Finset.sum_congr rfl fun i _ ↦ by rw [hω i t, hω i s, mul_sub]),
    Locally.setIntegral_exp_I_mul_sub hYv_l (hQeq ▸ hQsum) hYv_c 1 hst hA]
  simp only [one_pow, one_mul]

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
  simpa only [IndepFun_iff_Indep, @MeasurableSpace.comap_id _ (ℱ s)] using
    @IndepFun.process_indepFun₀ ι Ω mΩ P (fun _ ↦ ℝ) Ω (fun _ ↦ inferInstance) (ℱ s)
      (fun i ω ↦ M i t ω - M i s ω) id (fun i ↦ aemeasurable_sub_coord (hM i) (hcont i) s t)
      (@Measurable.aemeasurable Ω Ω mΩ (ℱ s) id P fun _ hA ↦ ℱ.le s _ hA) (fun S ↦ by
        rw [IndepFun_iff_Indep (mγ := ℱ s), @MeasurableSpace.comap_id _ (ℱ s)]
        let e : (S → ℝ) ≃ᵐ EuclideanSpace ℝ S := MeasurableEquiv.toLp 2 (S → ℝ)
        let X : Ω → EuclideanSpace ℝ S := fun ω ↦ e (fun i ↦ M i t ω - M i s ω)
        rw [show MeasurableSpace.comap (fun ω (i : S) ↦ M i t ω - M i s ω) inferInstance =
            MeasurableSpace.comap X inferInstance from le_antisymm
          (by rw [show (fun ω (i : S) ↦ M i t ω - M i s ω) = e.symm ∘ X by ext; simp [X, e],
                ← MeasurableSpace.comap_comp]
              exact MeasurableSpace.comap_mono e.symm.measurable.comap_le)
          (by rw [show X = e ∘ (fun ω (i : S) ↦ M i t ω - M i s ω) from rfl,
                ← MeasurableSpace.comap_comp]
              exact MeasurableSpace.comap_mono e.measurable.comap_le)]
        refine indep_comap_of_setIntegral_exp_inner_I (ℱ.le s) (e.measurable.comp_aemeasurable
            (aemeasurable_pi_iff.2 fun i ↦ aemeasurable_sub_coord (hM i) (hcont i) s t))
          (φ := fun v : EuclideanSpace ℝ S ↦
            exp (-((∑ i : S, ∑ j : S, v i * v j * C i j) * ((t : ℝ) - s) / 2 : ℝ))) fun v _ hA ↦ ?_
        rw [show (fun ω ↦ exp ((⟪X ω, v⟫ : ℂ) * I)) =
            fun ω ↦ exp (I * ∑ i : S, v i * (M i t ω - M i s ω)) by
          ext ω; simp only [X, e, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
            MeasurableEquiv.toLp_apply]; congr 1; push_cast; ring]
        exact setIntegral_exp_I_mul_sum_sub_of_locally_martingale (M := fun i : S ↦ M i)
          (C := fun i j : S ↦ C i j) (fun i ↦ hM i) (fun i j ↦ hQ i j) (fun i ↦ hcont i)
          (fun i ↦ v i) hst hA) _

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
      (Measure.pi fun i : ι ↦ gaussianReal 0 (c i * (t - s))) P := by
  have hX : AEMeasurable (fun ω i ↦ M i t ω - M i s ω) P :=
    aemeasurable_pi_iff.2 fun i ↦ aemeasurable_sub_coord (hM i) (hcont i) s t
  refine ⟨hX, ?_⟩
  have : IsFiniteMeasure (P.map (fun ω i ↦ M i t ω - M i s ω)) := Measure.isFiniteMeasure_map P _
  rw [← charFun_eq_pi_iff]; intro v
  have hset := setIntegral_exp_I_mul_sum_sub_of_locally_martingale hM
    (C := fun i j ↦ if i = j then (c i : ℝ) else 0)
    (fun i j ↦ by simpa only [ite_mul, zero_mul] using hQ i j) hcont
    (fun i ↦ v i) hst MeasurableSet.univ
  simp only [Measure.restrict_univ, measure_univ, ENNReal.toReal_one, Complex.ofReal_one,
    one_mul] at hset
  rw [show (P.map (fun ω i ↦ M i t ω - M i s ω)).map (WithLp.toLp 2) =
      P.map (fun ω ↦ WithLp.toLp 2 (fun i ↦ M i t ω - M i s ω)) from
    ((MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.aemeasurable).map_map_of_aemeasurable hX,
    charFun_apply, integral_map
      (show AEMeasurable (fun ω ↦ WithLp.toLp 2 (fun i ↦ M i t ω - M i s ω)) P from
        (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp_aemeasurable hX)
      (show AEStronglyMeasurable (fun x : PiLp 2 (fun _ : ι ↦ ℝ) ↦ exp ((⟪x, v⟫ : ℂ) * I)) _ from
        (continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_id.inner continuous_const)).mul continuous_const)).aestronglyMeasurable),
    show (fun ω ↦ exp ((⟪WithLp.toLp 2 (fun i ↦ M i t ω - M i s ω), v⟫ : ℂ) * I)) =
        fun ω ↦ exp (I * ∑ i, v i * (M i t ω - M i s ω)) by
      ext ω; simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      congr 1; push_cast; ring, hset]
  simp_rw [charFun_gaussianReal, ← Complex.exp_sum]; congr 1
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, NNReal.coe_mul,
    NNReal.coe_sub hst, Complex.ofReal_zero, zero_mul, zero_sub, Finset.sum_neg_distrib,
    ← Finset.sum_div]
  push_cast; rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div]
  congr 1; exact Finset.sum_congr rfl fun i _ ↦ by ring

end VectorCharacteristicFunction

section PathwiseCoordinateIndependence

private lemma iIndepFun_swap [IsProbabilityMeasure P] {α β E : Type*} [MeasurableSpace E]
    {X : α → β → Ω → E} (mX : ∀ a b, Measurable (X a b))
    (h1 : iIndepFun (fun a ω b ↦ X a b ω) P) (h2 : ∀ a, iIndepFun (X a) P) :
    iIndepFun (fun b ω a ↦ X a b ω) P := by
  have hsig : iIndepFun (fun (p : Sigma fun _ : β ↦ α) ω ↦ X p.2 p.1 ω) P :=
    (iIndepFun_uncurry' mX h1 h2).precomp (g := fun (p : Sigma fun _ : β ↦ α) ↦ (p.2, p.1))
      fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by simp only [Prod.mk.injEq] at h; cases h.1; cases h.2; rfl
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop),
    show (fun ω b a ↦ X a b ω) = (MeasurableEquiv.piCurry (fun (_ : β) (_ : α) ↦ E)) ∘
      (fun ω (p : Sigma fun _ : β ↦ α) ↦ X p.2 p.1 ω) by ext; simp [Sigma.curry],
    ← Measure.map_map (by fun_prop) (by fun_prop),
    (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 hsig,
    Measure.infinitePi_map_piCurry (fun b a ↦ P.map (X a b))]
  congrm Measure.infinitePi fun b ↦ ?_
  exact ((iIndepFun_iff_map_fun_eq_infinitePi_map (fun a ↦ mX a b)).1
    (hsig.precomp (g := fun a ↦ ⟨b, a⟩) fun _ _ h ↦ by simpa using h)).symm

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
  obtain ⟨Y, hYp, hYM, hYc, hYl, hQY⟩ := exists_predictable_rep (C := C) hM hQ hcont
    (fun _ _ ↦ ae_of_all P fun _ _ ↦ by simp [C])
  let V : ℝ≥0 → Ω → ι → ℝ := fun t ω i ↦ Y i t ω - Y i 0 ω
  have hV_adapt : Adapted ℱ V := fun t ↦ @measurable_pi_iff _ _ _ (ℱ t) _ _ |>.2 fun i ↦
    ((hYp i).isStronglyProgressive.stronglyAdapted t).measurable.sub
      (((hYp i).isStronglyProgressive.stronglyAdapted 0).measurable.mono (ℱ.mono bot_le) le_rfl)
  have hV_meas (t : ℝ≥0) (i : ι) : Measurable (fun ω ↦ V t ω i) :=
    (measurable_pi_apply i).comp ((hV_adapt t).mono (ℱ.le t) le_rfl)
  refine (iIndepFun.iIndepFun_process (fun i t ↦ hV_meas t i) fun S J ↦ ?_).process_congr
    fun i t ↦ (hYM i).mono fun _ hω ↦ by simp [V, hω t, hω 0]
  let T : Finset ℝ≥0 := insert 0 (Finset.univ.biUnion J)
  have h0T : (0 : ℝ≥0) ∈ T := Finset.mem_insert_self 0 _
  set m := T.card - 1
  let e : Fin (m + 1) ≃o T := T.orderIsoOfFin (Nat.sub_add_cancel (Finset.card_pos.2 ⟨0, h0T⟩)).symm
  let g (k : Fin (m + 1)) : ℝ≥0 := (e k : ℝ≥0)
  have hswap : iIndepFun (fun (i : S) ω (k : Fin m) ↦ V (g k.succ) ω i - V (g k.castSucc) ω i) P :=
    iIndepFun_swap (fun _ i ↦ (hV_meas _ i).sub (hV_meas _ i))
      (((hV_adapt.hasIndepIncrements fun _ _ hst ↦ by
          simpa only [V, Pi.sub_def, sub_sub_sub_cancel_right] using
            indep_comap_sub_pi_of_locally_martingale hYl hQY hYc hst)
        m g fun _ _ h ↦ e.monotone h).comp (fun _ (f : ι → ℝ) (i : S) ↦ f i)
        (fun _ ↦ measurable_pi_iff.2 fun i ↦ measurable_pi_apply i.1))
      fun k ↦ by
        have hst := e.monotone (Fin.castSucc_le_succ k)
        simpa only [V, Function.comp_apply, sub_sub_sub_cancel_right] using
          (iIndepFun_iff_hasLaw_pi_pi fun i : S ↦ Locally.hasLaw_sub_gaussianReal (hYl i)
            (by simpa only [C, ↓reduceIte, sq] using hQY i i) (hYc i) hst).2
          (hasLaw_sub_pi_gaussianReal_of_locally_martingale (M := fun i : S ↦ Y i)
            (c := fun i : S ↦ c i) (fun i ↦ hYl i)
            (fun i j ↦ by simpa only [C, Subtype.ext_iff, ite_mul, zero_mul] using hQY i.1 j.1)
            (fun i ↦ hYc i) hst)
  let idx (i : S) (t : J i) : Fin (m + 1) :=
    e.symm ⟨t.1, Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, t.2⟩)⟩
  convert hswap.comp (fun (i : S) (d : Fin m → ℝ) (t : J i) ↦
      ∑ j ∈ Finset.univ.filter (fun j : Fin m ↦ j.val < (idx i t).val), d j)
    (fun _ ↦ measurable_pi_iff.2 fun _ ↦
      Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _) using 1
  ext i ω t
  have heval (k : Fin (m + 1)) : V (g k) ω i = ∑ j ∈ Finset.univ.filter
      (fun j : Fin m ↦ j.val < k.val), (V (g j.succ) ω i - V (g j.castSucc) ω i) := by
    induction k using Fin.induction with
    | zero =>
      simp [g, le_antisymm (Subtype.coe_le_coe.2
        ((e.monotone (Fin.zero_le _)).trans_eq (e.apply_symm_apply ⟨0, h0T⟩))) bot_le, V]
    | succ k ih =>
      rw [show Finset.univ.filter (fun j : Fin m ↦ j.val < k.succ.val) =
          insert k (Finset.univ.filter (fun j : Fin m ↦ j.val < k.castSucc.val)) by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_iff, le_iff_lt_or_eq, Fin.ext_iff]; tauto,
        Finset.sum_insert (by simp), ← ih]; ring
  simpa only [show g (idx i t) = t.1 from congrArg Subtype.val (e.apply_symm_apply _),
    Function.comp_apply] using heval (idx i t)

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
  obtain ⟨Y, _, hYM, hYc, hYl, hQY⟩ := exists_predictable_rep
    (C := fun i j ↦ if i = j then (c i : ℝ) else 0) hM hQ hcont
    (fun i j ↦ (h0 i).mp ((h0 j).mono fun _ h0j h0i _ ↦ by simp [h0i, h0j]))
  refine (iIndepFun_sub_zero_of_locally_martingale hYl
    (fun i j ↦ by simpa only [ite_mul, zero_mul] using hQY i j) hYc).process_congr fun i t ↦ ?_
  filter_upwards [hYM i, h0 i] with _ hω h0ω; simp [hω t, hω 0, h0ω]

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
  obtain ⟨W, hWp, hWM, hWc, hWl, hQW⟩ := exists_predictable_rep
    (C := fun i j ↦ if i = j then (1 : ℝ) else 0) hM hQ hcont
    (fun i j ↦ (h0 i).mp ((h0 j).mono fun _ h0j h0i _ ↦ by simp [h0i, h0j]))
  have hW0 (i : ι) : ∀ᵐ ω ∂P, W i 0 ω = 0 :=
    (h0 i).mp ((hWM i).mono fun _ heq h0ω ↦ by rw [heq 0, h0ω])
  have hFB (i : ι) : IsFilteredPreBrownianReal ℱ (W i) P :=
    (Locally.isFilteredPreBrownianReal_sub_zero (hWl i)
      (by simpa only [sq, ↓reduceIte, one_mul] using hQW i i) (hWc i)
      (hWp i).isStronglyProgressive.stronglyAdapted.adapted).congr
      (hWp i).isStronglyProgressive.stronglyAdapted.adapted
      fun _ ↦ (hW0 i).mono fun _ h0ω ↦ by simp [h0ω]
  refine ⟨W, hWp, hWM, fun i ↦ ⟨(hFB i).toIsPreBrownianReal, hWc i⟩, hFB,
    (iIndepFun_sub_zero_of_locally_martingale (c := fun _ ↦ 1) hWl
      (fun i j ↦ by simpa only [NNReal.coe_one, one_mul, ite_mul, zero_mul] using hQW i j)
      hWc).process_congr fun i _ ↦ (hW0 i).mono fun _ h0ω ↦ by simp [h0ω],
    fun _ _ hst ↦ indep_comap_sub_pi_of_locally_martingale hWl hQW hWc hst⟩

end PathwiseCoordinateIndependence

section FilteredVectorBrownianLaw

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
  have : IsProbabilityMeasure P := (hB₁.hasLaw_eval 0).isProbabilityMeasure
  have hm₁ (t : ℝ≥0) : Measurable (B₁ t) := (hA₁ t).mono (ℱ.le t) le_rfl
  have hm₂ (t : ℝ≥0) : Measurable (B₂ t) := (hA₂ t).mono (ℱ.le t) le_rfl
  have hsq : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hW : IsBrownianReal (fun t ω ↦ (1 / Real.sqrt 2) * (B₁ t ω + B₂ t ω)) P :=
    ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ by
        have hsum : HasLaw (B₁ t + B₂ t) (gaussianReal 0 (t + t)) P :=
          ⟨(hm₁ t).aemeasurable.add (hm₂ t).aemeasurable, by
            simpa only [add_zero] using gaussianReal_add_gaussianReal_of_indepFun
              (show IndepFun (B₁ t) (B₂ t) P from
                hind.comp (measurable_pi_apply t) (measurable_pi_apply t))
              (hB₁.hasLaw_eval t) (hB₂.hasLaw_eval t)⟩
        simpa only [Pi.add_apply, mul_zero,
          show NNReal.mk ((1 / Real.sqrt 2) ^ 2) (sq_nonneg _) * (t + t) = t by
            ext; push_cast; rw [hsq]; ring] using gaussianReal_const_mul hsum (1 / Real.sqrt 2))
      (fun n g hg ↦ by
        let Δ : Bool → Fin n → Ω → ℝ := fun b k ω ↦
          cond b (B₂ (g k.succ) ω - B₂ (g k.castSucc) ω) (B₁ (g k.succ) ω - B₁ (g k.castSucc) ω)
        have hm : Measurable (fun (f : ℝ≥0 → ℝ) (k : Fin n) ↦ f (g k.succ) - f (g k.castSucc)) :=
          measurable_pi_iff.2 fun _ ↦ (measurable_pi_apply _).sub (measurable_pi_apply _)
        have hbool : iIndepFun (fun b ω k ↦ Δ b k ω) P := by
          rw [iIndepFun_iff]; intro s f hf
          by_cases h0 : false ∈ s <;> by_cases h1 : true ∈ s
          · rw [show s = {false, true} by ext b; cases b <;> simp [h0, h1],
              Finset.set_biInter_insert, Finset.set_biInter_singleton, Finset.prod_pair (by decide)]
            exact (Indep_iff _ _ _).1 ((IndepFun_iff_Indep _ _ _).1 (hind.comp hm hm)) _ _
              (hf false h0) (hf true h1)
          · simp [show s = {false} by ext b; cases b <;> simp [h0, h1]]
          · simp [show s = {true} by ext b; cases b <;> simp [h0, h1]]
          · simp [show s = ∅ by ext b; cases b <;> simp [h0, h1]]
        convert (iIndepFun_swap (X := Δ)
          (fun b _ ↦ match b with | false => (hm₁ _).sub (hm₁ _) | true => (hm₂ _).sub (hm₂ _))
          hbool (fun b ↦ match b with
            | false => hB₁.hasIndepIncrements n g hg | true => hB₂.hasIndepIncrements n g hg)
          ).comp (fun _ (f : Bool → ℝ) ↦ (1 / Real.sqrt 2) * (f false + f true))
          (fun _ ↦ by fun_prop) using 1
        ext _ _; simp only [Δ, Function.comp_apply, Bool.cond_false, Bool.cond_true]; ring),
      hB₁.cont.mp (hB₂.cont.mono fun _ h₂ h₁ ↦ continuous_const.mul (h₁.add h₂))⟩
  have hFB₁ := hB₁.isFilteredPreBrownianReal_of_locally_martingale hA₁ hloc₁
  have hFB₂ := hB₂.isFilteredPreBrownianReal_of_locally_martingale hA₂ hloc₂
  have hFW := hW.isFilteredPreBrownianReal_of_locally_martingale
    (fun t ↦ measurable_const.mul ((hA₁ t).add (hA₂ t)))
    (Locally.of_prop (by convert (hFB₁.martingale.add hFB₂.martingale).smul (1 / Real.sqrt 2)))
  convert (hFW.martingale_sq_sub.sub (hFB₁.martingale_sq_sub.smul (1 / 2))).sub
    (hFB₂.martingale_sq_sub.smul (1 / 2)) using 1
  ext t ω; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_pow, hsq]; ring

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
  refine indep_comap_sub_pi_of_locally_martingale (C := C) hloc (fun i j ↦ ?_)
    (fun i ↦ (hB i).cont) hst
  have hsm : StronglyAdapted ℱ
      (fun u ω ↦ B i u ω * B j u ω - B i 0 ω * B j 0 ω - C i j * (u : ℝ)) := fun u ↦
    ((((hA i u).mul (hA j u)).sub (((hA i 0).mul (hA j 0)).mono
      (ℱ.mono bot_le) le_rfl)).sub measurable_const).stronglyMeasurable
  have h0ae := (hB i).eval_zero_ae_eq_zero.mono fun ω hω ↦ show B i 0 ω * B j 0 ω = 0 by simp [hω]
  by_cases hij : i = j
  · subst hij
    exact Locally.of_prop (((hB i).isFilteredPreBrownianReal_of_locally_martingale (hA i)
      (hloc i)).martingale_sq_sub.congr hsm fun _ ↦ h0ae.mono fun _ h0ω ↦ by simp [C, sq, h0ω])
  · exact Locally.of_prop ((martingale_mul_of_indepFun_isBrownianReal (hB i) (hB j)
      (hind.indepFun hij) (hA i) (hA j) (hloc i) (hloc j)).congr hsm
      fun _ ↦ h0ae.mono fun _ h0ω ↦ by simp [C, hij, h0ω])

end FilteredVectorBrownianLaw

end TauCeti.Probability
