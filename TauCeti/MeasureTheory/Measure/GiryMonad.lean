/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Random measures: evaluations and sigma-finiteness

The measurable space on measures is induced by the map of all measurable-set evaluations.
Consequently, any measure-valued map generates the same σ-algebra as its joint evaluations,
without a measurability assumption. These identities let laws and independence of random
measures be checked through their evaluation processes.

A random measure with sigma-finite average is almost surely sigma-finite. More precisely,
one fixed measurable exhaustion of the average has finite mass for almost every realization,
simultaneously on all its sets. No topology or probability normalization is required.

We also construct a measurable version whose values are all sigma-finite, by replacing the
exceptional realizations by zero. This permits constructions on sigma-finite measures to be
applied everywhere without changing the law of the random measure. The conclusion is not
almost-sure absolute continuity with respect to the average: a uniformly located Dirac
measure is a counterexample to that stronger assertion.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2–3, on random measures and sigma-finite Poisson intensities.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- The measurable space on measures is induced by the joint evaluation map on all
measurable sets. -/
theorem measurableSpace_eq_comap_eval :
    (Measure.instMeasurableSpace : MeasurableSpace (Measure X)) =
      MeasurableSpace.comap
        (fun (μ : Measure X) (A : {A : Set X // MeasurableSet A}) ↦ μ A.val)
        MeasurableSpace.pi := by
  let e : Measure X → ({A : Set X // MeasurableSet A} → ℝ≥0∞) := fun μ A ↦ μ A.val
  apply le_antisymm
  · have hid : Measurable[MeasurableSpace.comap e inferInstance]
        (id : Measure X → Measure X) :=
      measurable_of_measurable_coe _ fun A hA ↦
        (measurable_pi_apply (⟨A, hA⟩ : {A : Set X // MeasurableSet A})).comp
          (comap_measurable e)
    simpa only [MeasurableSpace.comap_id] using hid.comap_le
  · exact (Measurable.of_eval fun A ↦ measurable_coe A.property).comap_le

/-- A measure-valued map generates the same measurable space as its joint evaluations
on all measurable sets. No measurability assumption on the map is needed. -/
theorem measurableSpace_comap_eq_comap_eval {Ω : Type*} (N : Ω → Measure X) :
    MeasurableSpace.comap N inferInstance =
      MeasurableSpace.comap
        (fun ω (A : {A : Set X // MeasurableSet A}) ↦ N ω A.val)
        MeasurableSpace.pi := by
  rw [measurableSpace_eq_comap_eval, MeasurableSpace.comap_comp, Function.comp_def]

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure X}

/-- On any countable family of measurable sets with finite average mass, almost every
realization has finite mass on every set in that family. -/
theorem ae_forall_measure_lt_top_of_bind [Countable ι]
    (hN : AEMeasurable N P) {s : ι → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hfinite : ∀ i, P.bind N (s i) < ∞) :
    ∀ᵐ ω ∂P, ∀ i, N ω (s i) < ∞ := by
  rw [ae_all_iff]
  intro i
  apply ae_lt_top' (f := fun ω => N ω (s i))
    ((Measure.measurable_coe (hs i)).comp_aemeasurable hN)
  rw [← bind_apply (hs i) hN]
  exact (hfinite i).ne

/-- A random measure whose average is sigma-finite is almost surely sigma-finite.
The sample measure need not be finite, and no topology on either space is needed. -/
theorem ae_sigmaFinite_of_bind (hN : AEMeasurable N P) [SigmaFinite (P.bind N)] :
    ∀ᵐ ω ∂P, SigmaFinite (N ω) := by
  filter_upwards [ae_forall_measure_lt_top_of_bind hN
    (measurableSet_spanningSets (P.bind N)) (measure_spanningSets_lt_top (P.bind N))]
    with ω hω
  let S : (N ω).FiniteSpanningSetsIn {s | MeasurableSet s} :=
    ⟨spanningSets (P.bind N), measurableSet_spanningSets (P.bind N), hω,
      iUnion_spanningSets (P.bind N)⟩
  exact S.sigmaFinite

/-- An almost-everywhere measurable random measure with sigma-finite average admits a
measurable version with sigma-finite values everywhere, without changing its law. -/
theorem exists_measurable_ae_eq_sigmaFinite_of_bind (hN : AEMeasurable N P)
    [SigmaFinite (P.bind N)] :
    ∃ M : Ω → Measure X, Measurable M ∧ M =ᵐ[P] N ∧ ∀ ω, SigmaFinite (M ω) := by
  classical
  let N' := hN.mk N
  have hm : Measurable N' := hN.measurable_mk
  have hbind : P.bind N' = P.bind N := bind_congr_right hN.ae_eq_mk.symm
  let s := spanningSets (P.bind N)
  let good := {ω | ∀ n, N' ω (s n) < ∞}
  have hs : ∀ n, MeasurableSet (s n) := measurableSet_spanningSets (P.bind N)
  have hgood : MeasurableSet good := by
    simp only [good, ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_lt
      ((Measure.measurable_coe (hs n)).comp hm) measurable_const
  have hae : ∀ᵐ ω ∂P, ω ∈ good :=
    ae_forall_measure_lt_top_of_bind hm.aemeasurable hs fun n => by
      rw [hbind]
      exact measure_spanningSets_lt_top (P.bind N) n
  refine ⟨good.indicator N', hm.indicator hgood, ?_, ?_⟩
  · filter_upwards [hae, hN.ae_eq_mk] with ω hω heq
    exact (indicator_of_mem hω N').trans heq.symm
  · intro ω
    by_cases hω : ω ∈ good
    · rw [indicator_of_mem hω]
      let S : (N' ω).FiniteSpanningSetsIn {s | MeasurableSet s} :=
        ⟨s, hs, hω, iUnion_spanningSets (P.bind N)⟩
      exact S.sigmaFinite
    · rw [indicator_of_notMem hω]
      infer_instance

end MeasureTheory.Measure
