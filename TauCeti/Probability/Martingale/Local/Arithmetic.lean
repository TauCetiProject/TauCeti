/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
public import TauCeti.Probability.Martingale.ContinuousStopping
public import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.Stopping

/-!
# Linear combinations of local martingales on raw filtrations

Continuous real-linear maps, deterministic scalar multiples, and negations preserve native local
martingales (`ProbabilityTheory.Locally`) on arbitrary linearly ordered time indices with a bottom
element: the same localizing sequence works stage by stage because continuous linear maps preserve
zero and commute with conditional expectation.

Adding two native local martingales on `ℝ≥0` is more delicate on an unaugmented filtration, because
stopping one stage at the other's possibly uncountable-range localizing time requires progressive
measurability and right continuity of the stopped path. For almost-surely continuous native local
martingales `X` and `Y` under a finite measure, passing to predictable versions supplies
progressively measurable, almost-surely continuous local-martingale representatives `X'` and `Y'`.
Stopping each native stage at the partner's localizing time via
`MeasureTheory.Martingale.stoppedProcess_indicator_of_ae_isRightContinuous` shows that `X' + Y'` is
a native local martingale, and progressive congruence transfers locality to any strongly
progressive process indistinguishable from `X + Y` (in particular to `X + Y` itself when `X` and
`Y` are strongly progressive).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

section ContinuousLinearMap

variable {ι Ω E F : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ι mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {X : ι → Ω → E}

/-- Applying a continuous real-linear map preserves native local martingales, without any path
regularity, progressivity, or finite-measure assumption. -/
theorem ContinuousLinearMap.comp_locally_martingale (L : E →L[ℝ] F)
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ L (X t ω)) P := by
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  convert L.comp_martingale (hX.stoppedProcess_localSeq n) using 1
  ext t ω
  simp only [stoppedProcess_indicator_pos_apply]
  split_ifs <;> simp

namespace ProbabilityTheory.Locally

/-- Deterministic scalar multiplication preserves native local martingales. -/
theorem martingale_smul (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) (c : ℝ) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ c • X t ω) P :=
  (ContinuousLinearMap.lsmul ℝ ℝ c).comp_locally_martingale hX

/-- Negation preserves native local martingales. -/
theorem martingale_neg (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (-X) P :=
  (-ContinuousLinearMap.id ℝ E).comp_locally_martingale hX

/-- Perturbing a native local martingale by a strongly progressive process indistinguishable from
zero preserves native locality, with no progressivity, regularity, or measure-finiteness assumption
on `X` or `P`. -/
theorem martingale_add_of_indist_zero
    [SecondCountableTopology ι] [TopologicalSpace.PseudoMetrizableSpace ι]
    [MeasurableSpace ι] [BorelSpace ι] {D : ι → Ω → E}
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P)
    (hD : IsStronglyProgressive ℱ D) (hD0 : D ≡ᵐ[P] 0) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (X + D) P := by
  have hloc := hX.isLocalizingSequence_localSeq
  refine ⟨hX.localSeq, hloc, fun n ↦ (hX.stoppedProcess_localSeq n).congr (fun t ↦ ?_) fun t ↦ ?_⟩
  · have hτ := hloc.isStoppingTime n
    have h1 := (hX.stoppedProcess_localSeq n).stronglyAdapted t
    have h2 : StronglyMeasurable[ℱ t] (stoppedProcess
        (fun s ↦ {ω | (⊥ : WithTop ι) < hX.localSeq n ω}.indicator (D s))
        (hX.localSeq n) t) := by
      rw [stoppedProcess_indicator_comm']
      exact ((hD.stoppedProcess hτ).stronglyAdapted t).indicator
        (ℱ.mono bot_le _ (hτ.measurableSet_gt ⊥))
    convert h1.add h2 using 1
    ext ω
    simp only [Pi.add_apply, stoppedProcess_indicator_pos_apply]
    split_ifs <;> simp
  · filter_upwards [hD0] with ω hω
    simp [stoppedProcess_indicator_pos_apply, hω _]

end ProbabilityTheory.Locally

end ContinuousLinearMap

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {X Y Z : ℝ≥0 → Ω → E}

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem isStronglyProgressive_stopped_indicator (hX : IsStronglyProgressive ℱ X)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsStronglyProgressive ℱ
      (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) := by
  rw [stoppedProcess_indicator_comm']
  intro t
  have hprod : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ t)]
      ((univ : Set (Iic t)) ×ˢ {ω | 0 < τ ω}) :=
    MeasurableSet.univ.prod (ℱ.mono bot_le _ (hτ.measurableSet_gt 0))
  convert (hX.stoppedProcess hτ t).indicator hprod using 1
  ext ⟨s, ω⟩
  by_cases hω : 0 < τ ω <;> simp [hω]

omit [IsFiniteMeasure P] [NormedSpace ℝ E] [CompleteSpace E] in
private theorem ae_isRightContinuous_stopped_indicator
    (hcX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) (τ : Ω → WithTop ℝ≥0) :
    ∀ᵐ ω ∂P, IsRightContinuous
      (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ · ω) := by
  filter_upwards [hcX] with ω hω t
  rw [stoppedProcess_indicator_comm']
  by_cases hpos : 0 < τ ω
  · simpa [Set.indicator_apply, hpos] using (hω t).stoppedProcess
  · simpa [Set.indicator_apply, hpos] using continuousWithinAt_const

private theorem locally_martingale_add_progressive
    (hXprog : IsStronglyProgressive ℱ X) (hYprog : IsStronglyProgressive ℱ Y)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω))
    (hcY : ∀ᵐ ω ∂P, IsRightContinuous (Y · ω)) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (X + Y) P := by
  have hτ := hX.isLocalizingSequence_localSeq
  have hσ := hY.isLocalizingSequence_localSeq
  refine ⟨min hX.localSeq hY.localSeq, hτ.min hσ, fun n ↦ ?_⟩
  have hUmart := (hX.stoppedProcess_localSeq n).stoppedProcess_indicator_of_ae_isRightContinuous
    (isStronglyProgressive_stopped_indicator hXprog (hτ.isStoppingTime n))
    (ae_isRightContinuous_stopped_indicator hcX (hX.localSeq n)) (hσ.isStoppingTime n)
  have hVmart := (hY.stoppedProcess_localSeq n).stoppedProcess_indicator_of_ae_isRightContinuous
    (isStronglyProgressive_stopped_indicator hYprog (hσ.isStoppingTime n))
    (ae_isRightContinuous_stopped_indicator hcY (hY.localSeq n)) (hτ.isStoppingTime n)
  convert hUmart.add hVmart using 1
  simp only [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
  ext t ω
  by_cases h1 : 0 < hX.localSeq n ω <;> by_cases h2 : 0 < hY.localSeq n ω <;>
    simp [stoppedProcess, Pi.inf_apply, lt_min_iff, inf_comm, h1, h2]

/-- On a finite measure space, any strongly progressive process `Z` indistinguishable from the sum
of two almost-surely continuous native local martingales is itself a native local martingale on the
same raw filtration. Neither summand need be literally adapted or progressive. -/
theorem IsStronglyProgressive.locally_martingale_of_indist_add (hZ : IsStronglyProgressive ℱ Z)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hcY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (hZXY : Z ≡ᵐ[P] X + Y) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ Z P := by
  obtain ⟨X', hX'pred, hX'eq, hX'loc⟩ :=
    hX.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcX.mono fun _ h ↦ h.isLeftContinuous)
  obtain ⟨Y', hY'pred, hY'eq, hY'loc⟩ :=
    hY.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcY.mono fun _ h ↦ h.isLeftContinuous)
  have hcX' : ∀ᵐ ω ∂P, IsRightContinuous (X' · ω) := by
    filter_upwards [hcX, hX'eq] with ω hc heq
    exact (hc.congr fun t ↦ (heq t).symm).isRightContinuous
  have hcY' : ∀ᵐ ω ∂P, IsRightContinuous (Y' · ω) := by
    filter_upwards [hcY, hY'eq] with ω hc heq
    exact (hc.congr fun t ↦ (heq t).symm).isRightContinuous
  have hsum := locally_martingale_add_progressive hX'pred.isStronglyProgressive
    hY'pred.isStronglyProgressive hX'loc hY'loc hcX' hcY'
  exact hZ.locally_martingale_of_indist hsum ((hX'eq.add hY'eq).trans hZXY.symm)

/-- The sum of two strongly progressive, almost-surely continuous native local martingales on a raw
filtration is a native local martingale. -/
theorem IsStronglyProgressive.locally_martingale_add (hXprog : IsStronglyProgressive ℱ X)
    (hYprog : IsStronglyProgressive ℱ Y)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hcY : ∀ᵐ ω ∂P, Continuous (Y · ω)) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (X + Y) P :=
  (hXprog.add hYprog).locally_martingale_of_indist_add hX hY hcX hcY .rfl

/-- Any strongly progressive process indistinguishable from the difference of two almost-surely
continuous native local martingales is a native local martingale. -/
theorem IsStronglyProgressive.locally_martingale_of_indist_sub (hZ : IsStronglyProgressive ℱ Z)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hcY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (hZXY : Z ≡ᵐ[P] X - Y) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ Z P := by
  refine hZ.locally_martingale_of_indist_add hX hY.martingale_neg hcX
    (hcY.mono fun _ h ↦ h.neg) (hZXY.trans ?_)
  exact .of_forall fun _ _ ↦ sub_eq_add_neg _ _

/-- The difference of two strongly progressive, almost-surely continuous native local martingales
on a raw filtration is a native local martingale. -/
theorem IsStronglyProgressive.locally_martingale_sub (hXprog : IsStronglyProgressive ℱ X)
    (hYprog : IsStronglyProgressive ℱ Y)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hcY : ∀ᵐ ω ∂P, Continuous (Y · ω)) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (X - Y) P :=
  (hXprog.sub hYprog).locally_martingale_of_indist_sub hX hY hcX hcY .rfl

/-- A finite sum of strongly progressive, almost-surely continuous native local martingales on a
raw filtration is a native local martingale. -/
theorem IsStronglyProgressive.locally_martingale_sum {ι : Type*} {s : Finset ι}
    {U : ι → ℝ≥0 → Ω → E}
    (hprog : ∀ i ∈ s, IsStronglyProgressive ℱ (U i))
    (hloc : ∀ i ∈ s, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (U i) P)
    (hc : ∀ i ∈ s, ∀ᵐ ω ∂P, Continuous (U i · ω)) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ ∑ i ∈ s, U i t ω) P := by
  classical
  let S : Finset ι → ℝ≥0 → Ω → E := fun r t ω ↦ ∑ i ∈ r, U i t ω
  suffices IsStronglyProgressive ℱ (S s) ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ (S s) P ∧
      (∀ᵐ ω ∂P, Continuous (S s · ω)) from this.2.1
  induction s using Finset.induction_on with
  | empty =>
    simpa only [S, Finset.sum_empty] using
      ⟨isStronglyProgressive_const ℱ 0, Locally.of_prop (martingale_zero E ℱ P),
        ae_of_all P fun _ ↦ continuous_const⟩
  | insert a s ha ih =>
    obtain ⟨hps, hls, hcs⟩ := ih (fun i hi ↦ hprog i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hloc i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi))
    have hpa := hprog a (Finset.mem_insert_self a s)
    have hla := hloc a (Finset.mem_insert_self a s)
    have hca := hc a (Finset.mem_insert_self a s)
    have heq : S (insert a s) = U a + S s := by
      ext t ω
      simp [S, Finset.sum_insert ha]
    rw [heq]
    exact ⟨hpa.add hps, hpa.locally_martingale_add hps hla hls hca hcs,
      (hca.and hcs).mono fun _ h ↦ h.1.add h.2⟩

/-- Stopping a strongly progressive, almost-surely right-continuous native local martingale at an
arbitrary stopping time preserves native locality on the same raw filtration. -/
theorem IsStronglyProgressive.locally_martingale_stoppedProcess
    (hXprog : IsStronglyProgressive ℱ X)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hcX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (MeasureTheory.stoppedProcess X τ) P := by
  have hloc := hX.isLocalizingSequence_localSeq
  refine ⟨hX.localSeq, hloc, fun n ↦ ?_⟩
  have hmart := (hX.stoppedProcess_localSeq n).stoppedProcess_of_ae_isRightContinuous
    (isStronglyProgressive_stopped_indicator hXprog (hloc.isStoppingTime n))
    (ae_isRightContinuous_stopped_indicator hcX (hX.localSeq n)) hτ
  convert hmart using 1
  simp only [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
  ext t ω
  by_cases hpos : 0 < hX.localSeq n ω <;> simp [MeasureTheory.stoppedProcess, inf_comm, hpos]

end MeasureTheory
