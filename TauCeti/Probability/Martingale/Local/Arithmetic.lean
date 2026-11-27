/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
public import TauCeti.Probability.Martingale.Local.Stability
public import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Process.ContinuousAE
import TauCeti.Probability.Process.LocalProperty
import TauCeti.Probability.Process.Stopping

/-!
# Linear combinations of local martingales on raw filtrations

Continuous real-linear maps, scalar multiples, negations, and strongly progressive perturbations
indistinguishable from zero (`martingale_add_of_indist_zero`, `martingale_sub_of_indist_right`)
preserve native local martingales (`ProbabilityTheory.Locally`). On `ℝ≥0` under a finite measure,
predictable versions and continuous-time stopping extend this to sums and finite sums of a.s.
continuous native local martingales.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

section ContinuousLinearMap

variable {ι Ω E F : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ι mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {X : ι → Ω → E}

/-- Applying a continuous real-linear map preserves native local martingales. -/
theorem ContinuousLinearMap.comp_locally_martingale (L : E →L[ℝ] F)
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ L (X t ω)) P := by
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  convert L.comp_martingale (hX.stoppedProcess_localSeq n) using 1
  ext; simp only [stoppedProcess_indicator_pos_apply]; split_ifs <;> simp

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
zero preserves native locality. -/
theorem martingale_add_of_indist_zero
    [SecondCountableTopology ι] [TopologicalSpace.PseudoMetrizableSpace ι]
    [MeasurableSpace ι] [BorelSpace ι] {D : ι → Ω → E}
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P)
    (hD : IsStronglyProgressive ℱ D) (hD0 : D ≡ᵐ[P] 0) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (X + D) P := by
  have hloc := hX.isLocalizingSequence_localSeq
  refine ⟨hX.localSeq, hloc, fun n ↦ (hX.stoppedProcess_localSeq n).congr (fun t ↦ ?_) fun t ↦ ?_⟩
  · convert ((hX.stoppedProcess_localSeq n).stronglyAdapted t).add
      ((ℱ.isStable_isStronglyProgressive D hD _ (hloc.isStoppingTime n)).stronglyAdapted t) using 1
    ext; simp only [Pi.add_apply, stoppedProcess_indicator_pos_apply]; split_ifs <;> simp
  · exact hD0.mono fun _ hω ↦ by simp [stoppedProcess_indicator_pos_apply, hω _]

/-- Replacing the subtrahend `A` of a native local martingale `X - A` by an indistinguishable
strongly progressive process `A'` preserves native locality. -/
theorem martingale_sub_of_indist_right
    [SecondCountableTopology ι] [TopologicalSpace.PseudoMetrizableSpace ι]
    [MeasurableSpace ι] [BorelSpace ι] {A A' : ι → Ω → E}
    (hXA : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (X - A) P)
    (hA : IsStronglyProgressive ℱ A) (hA' : IsStronglyProgressive ℱ A') (hAA' : A ≡ᵐ[P] A') :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (X - A') P := by
  convert hXA.martingale_add_of_indist_zero (hA.sub hA')
    (hAA'.mono fun _ hω t ↦ sub_eq_zero.2 (hω t)) using 1
  ext; simp only [Pi.add_apply, Pi.sub_apply]; abel

end ProbabilityTheory.Locally

end ContinuousLinearMap

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {X Y Z : ℝ≥0 → Ω → E}

private theorem locally_martingale_add_progressive
    (hXprog : IsStronglyProgressive ℱ X) (hYprog : IsStronglyProgressive ℱ Y)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P) (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) (hcY : ∀ᵐ ω ∂P, IsRightContinuous (Y · ω)) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (X + Y) P := by
  have hτ := hX.isLocalizingSequence_localSeq; have hσ := hY.isLocalizingSequence_localSeq
  refine ⟨min hX.localSeq hY.localSeq, hτ.min hσ, fun n ↦ ?_⟩
  convert ((hX.stoppedProcess_localSeq n).stoppedProcess_indicator_of_ae_isRightContinuous
      (ℱ.isStable_isStronglyProgressive X hXprog _ (hτ.isStoppingTime n))
      (ℱ.isStable_ae_isRightContinuous P X hcX _ (hτ.isStoppingTime n)) (hσ.isStoppingTime n)).add
    ((hY.stoppedProcess_localSeq n).stoppedProcess_indicator_of_ae_isRightContinuous
      (ℱ.isStable_isStronglyProgressive Y hYprog _ (hσ.isStoppingTime n))
      (ℱ.isStable_ae_isRightContinuous P Y hcY _ (hσ.isStoppingTime n)) (hτ.isStoppingTime n))
    using 1
  simp only [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
  ext _ ω; by_cases h1 : 0 < hX.localSeq n ω <;> by_cases h2 : 0 < hY.localSeq n ω <;>
    simp [stoppedProcess, Pi.inf_apply, lt_min_iff, inf_comm, h1, h2]

/-- On a finite measure space, any strongly progressive process `Z` indistinguishable from the sum
of two almost-surely continuous native local martingales is itself a native local martingale. -/
theorem IsStronglyProgressive.locally_martingale_of_indist_add (hZ : IsStronglyProgressive ℱ Z)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P) (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hcY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (hZXY : Z ≡ᵐ[P] X + Y) : Locally (fun U ↦ Martingale U ℱ P) ℱ Z P := by
  obtain ⟨X', hX'p, hX'eq, hX'loc⟩ :=
    hX.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcX.mono fun _ h ↦ h.isLeftContinuous)
  obtain ⟨Y', hY'p, hY'eq, hY'loc⟩ :=
    hY.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcY.mono fun _ h ↦ h.isLeftContinuous)
  exact hZ.locally_martingale_of_indist
    (locally_martingale_add_progressive hX'p.isStronglyProgressive hY'p.isStronglyProgressive
      hX'loc hY'loc
      ((hcX.and hX'eq).mono fun _ ⟨hc, h⟩ ↦ (hc.congr fun t ↦ (h t).symm).isRightContinuous)
      ((hcY.and hY'eq).mono fun _ ⟨hc, h⟩ ↦ (hc.congr fun t ↦ (h t).symm).isRightContinuous))
    ((hX'eq.add hY'eq).trans hZXY.symm)

/-- The sum of two strongly progressive, almost-surely continuous native local martingales is a
native local martingale. -/
theorem IsStronglyProgressive.locally_martingale_add
    (hXprog : IsStronglyProgressive ℱ X) (hYprog : IsStronglyProgressive ℱ Y)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P) (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hcY : ∀ᵐ ω ∂P, Continuous (Y · ω)) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (X + Y) P :=
  (hXprog.add hYprog).locally_martingale_of_indist_add hX hY hcX hcY .rfl

/-- Any strongly progressive process indistinguishable from the difference of two almost-surely
continuous native local martingales is a native local martingale. -/
theorem IsStronglyProgressive.locally_martingale_of_indist_sub (hZ : IsStronglyProgressive ℱ Z)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P) (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hcY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (hZXY : Z ≡ᵐ[P] X - Y) : Locally (fun U ↦ Martingale U ℱ P) ℱ Z P :=
  hZ.locally_martingale_of_indist_add hX hY.martingale_neg hcX (hcY.mono fun _ h ↦ h.neg)
    (hZXY.trans (.of_forall fun _ _ ↦ sub_eq_add_neg _ _))

/-- The difference of two strongly progressive, almost-surely continuous native local martingales is
a native local martingale. -/
theorem IsStronglyProgressive.locally_martingale_sub
    (hXprog : IsStronglyProgressive ℱ X) (hYprog : IsStronglyProgressive ℱ Y)
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P) (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hcY : ∀ᵐ ω ∂P, Continuous (Y · ω)) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (X - Y) P :=
  (hXprog.sub hYprog).locally_martingale_of_indist_sub hX hY hcX hcY .rfl

/-- A finite sum of strongly progressive, almost-surely continuous native local martingales is a
native local martingale. -/
theorem IsStronglyProgressive.locally_martingale_sum {ι : Type*} {s : Finset ι}
    {U : ι → ℝ≥0 → Ω → E} (hprog : ∀ i ∈ s, IsStronglyProgressive ℱ (U i))
    (hloc : ∀ i ∈ s, Locally (fun Y ↦ Martingale Y ℱ P) ℱ (U i) P)
    (hc : ∀ i ∈ s, ∀ᵐ ω ∂P, Continuous (U i · ω)) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ ∑ i ∈ s, U i t ω) P := by
  classical
  induction s using Finset.induction_on with
  | empty => convert Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) (martingale_zero E ℱ P)
      using 1; ext; simp
  | insert a s ha ih =>
    have hps := IsStronglyProgressive.finsetSum fun i hi ↦ hprog i (Finset.mem_insert_of_mem hi)
    have hcs := s.ae_continuous_sum fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
    convert (hprog a (Finset.mem_insert_self a s)).locally_martingale_add hps
      (hloc a (Finset.mem_insert_self a s))
      (ih (fun i hi ↦ hprog i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hloc i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)))
      (hc a (Finset.mem_insert_self a s)) hcs using 1
    ext; simp [Finset.sum_insert ha]

end MeasureTheory
