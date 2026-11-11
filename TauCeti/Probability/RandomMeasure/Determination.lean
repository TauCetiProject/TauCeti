/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMeasure.LaplaceFunctional
public import TauCeti.Probability.RandomMeasure.Law
import TauCeti.Probability.Moments.LaplaceDeterminacy.Multivariate

/-!
# Determination of random-measure laws by Laplace functionals

The Laplace functional on nonnegative measurable tests determines the law of a random
measure on an arbitrary measurable space. It suffices to use finite sums of indicators
of disjoint measurable sets with natural-number coefficients. The realizations may have infinite
masses, and may live on different measure spaces. Only the first sample measure must be finite:
the zero test forces equal total masses. Neither local finiteness nor integrality is needed.

The finite indicator tests recover the mixed Laplace transforms of every finite family
of evaluations. Finite-dimensional Laplace determinacy, including infinite coordinates,
then gives the evaluation laws, which determine the law on the evaluation sigma-field.
This is the uniqueness input for identifying random measures constructed by their
Laplace functionals, in particular Poisson random measures.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 2 and 13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {Ω Ω' X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
  {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P]
  {N : Ω → Measure X} {M : Ω' → Measure X}

/-- Laplace functionals on finite sums of disjoint measurable indicators with natural
coefficients already determine random-measure laws. Counts may be infinite. -/
theorem map_eq_of_laplaceFunctional_sum_indicator_eq
    (hN : AEMeasurable N P) (hM : AEMeasurable M Q)
    (h : ∀ (k : ℕ) (A : Fin k → Set X), (∀ i, MeasurableSet (A i)) →
      Pairwise (Function.onFun Disjoint A) → ∀ c : Fin k → ℕ,
        P.laplaceFunctional N (fun x ↦ ∑ i, (A i).indicator (fun _ ↦ (c i : ℝ≥0∞)) x) =
          Q.laplaceFunctional M (fun x ↦ ∑ i, (A i).indicator (fun _ ↦ (c i : ℝ≥0∞)) x)) :
    P.map N = Q.map M := by
  classical
  have hmass : P univ = Q univ := by
    simpa [laplaceFunctional_def] using
      h 0 (fun _ ↦ ∅) (fun _ ↦ .empty) (by simp [Pairwise]) (fun _ ↦ 0)
  have : IsFiniteMeasure Q := ⟨by rw [← hmass]; exact measure_lt_top P univ⟩
  apply (map_eq_iff_forall_map_eval_eq_of_pairwise_disjoint hN hM).mpr
  intro k A hA hd
  apply TauCeti.Measure.ext_of_forall_lintegral_prod_exp_neg_pow_eq
  intro c
  have hprod : Measurable (fun v : Fin k → ℝ≥0∞ ↦
      ∏ i, EReal.exp (-(v i : EReal)) ^ c i) := by fun_prop
  have hNv : AEMeasurable (fun ω i ↦ N ω (A i)) P :=
    aemeasurable_pi_iff.mpr fun i ↦ (measurable_coe (hA i)).comp_aemeasurable hN
  have hMv : AEMeasurable (fun ω i ↦ M ω (A i)) Q :=
    aemeasurable_pi_iff.mpr fun i ↦ (measurable_coe (hA i)).comp_aemeasurable hM
  rw [lintegral_map' hprod.aemeasurable hNv, lintegral_map' hprod.aemeasurable hMv]
  simpa only [laplaceFunctional_sum_indicator_natCast _ _ hA] using h k A hA hd c

/-- Equality of Laplace functionals on all nonnegative measurable tests determines the
law, even for random measures with infinite masses on arbitrary measurable spaces. -/
theorem map_eq_of_laplaceFunctional_eq (hN : AEMeasurable N P) (hM : AEMeasurable M Q)
    (h : ∀ f : X → ℝ≥0∞, Measurable f →
      P.laplaceFunctional N f = Q.laplaceFunctional M f) :
    P.map N = Q.map M := by
  apply map_eq_of_laplaceFunctional_sum_indicator_eq hN hM
  intro k A hA _ c
  exact h _ (Finset.measurable_fun_sum _ fun i _ ↦ measurable_const.indicator (hA i))

/-- The measurable-test Laplace functional is a complete invariant of a random-measure
law. This is equality in distribution, not almost-sure equality of realizations. -/
theorem map_eq_iff_laplaceFunctional_eq (hN : AEMeasurable N P) (hM : AEMeasurable M Q) :
    P.map N = Q.map M ↔ ∀ f : X → ℝ≥0∞, Measurable f →
      P.laplaceFunctional N f = Q.laplaceFunctional M f := by
  constructor
  · intro h f hf
    exact (IdentDistrib.mk hN hM h).laplaceFunctional_eq hf
  · exact map_eq_of_laplaceFunctional_eq hN hM

end MeasureTheory.Measure
