/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Marking.Tuple
public import TauCeti.MeasureTheory.Measure.Count.Enumeration
import TauCeti.Probability.RandomMeasure.Determination

/-!
# Enumeration independence of independent marking

The law of independently marking a countable family of occurrences depends only on its
counting measure. Conversely, its ground projection recovers that measure, so equality of
marked laws is equivalent to equality of the original measures. This makes the tuple
construction usable without retaining an arbitrary labeling of the occurrences.

For optional occurrence sequences, Laplace-functional determinacy yields enumeration
independence on any measurable ground space, with no measurable-singleton, standard Borel,
nonemptiness, simplicity, or local-finiteness hypothesis, and with gaps (`none`) and infinite
multiplicities allowed.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5 (independent marking).

The marked laws are `Kernel.tupleMarking` and `Kernel.optionalTupleMarking`; invariance of
`tupleMarking` uses `Kernel.tupleMarking_comp_equiv` after matching occurrence fibers, while
invariance of `optionalTupleMarking` uses Laplace-functional determinacy.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

section Tuple

variable {X E : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace E] (κ : Kernel X E) [IsMarkovKernel κ]

/-- Independently marking two enumerations of the same counting measure gives the same law,
even when the enumerations use different countable index types. -/
theorem tupleMarking_eq_of_sum_dirac_eq {ι ι' : Type*} [Countable ι] [Countable ι']
    {x : ι → X} {y : ι' → X}
    (h : (Measure.sum fun i => Measure.dirac (x i)) =
      (Measure.sum fun j => Measure.dirac (y j))) :
    κ.tupleMarking ι x = κ.tupleMarking ι' y := by
  obtain ⟨e, he⟩ := TauCeti.sum_dirac_eq_sum_dirac_iff_exists_equiv.1 h
  have hxy : y ∘ e = x := funext he
  rw [← hxy]
  exact κ.tupleMarking_comp_equiv e y

/-- Marked tuple laws agree exactly when their underlying counting measures agree. Thus no
information about ground multiplicities is lost by passing to the marked law. -/
@[simp]
theorem tupleMarking_eq_iff_sum_dirac_eq {ι ι' : Type*} [Countable ι] [Countable ι']
    {x : ι → X} {y : ι' → X} :
    κ.tupleMarking ι x = κ.tupleMarking ι' y ↔
      (Measure.sum fun i => Measure.dirac (x i)) =
        (Measure.sum fun j => Measure.dirac (y j)) := by
  refine ⟨fun h => ?_, κ.tupleMarking_eq_of_sum_dirac_eq⟩
  have hground := congrArg (fun ν : Measure (Measure (X × E)) =>
    ν.map (fun μ => μ.map Prod.fst)) h
  simp only [map_map_fst_tupleMarking] at hground
  ext s hs
  have heval := congrArg (fun ν : Measure (Measure X) => ν.map (fun μ => μ s)) hground
  simpa only [Measure.map_dirac' (Measure.measurable_coe hs),
    MeasureTheory.dirac_eq_dirac_iff] using heval

end Tuple

section Optional

variable {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
  (κ : Kernel X E) [IsMarkovKernel κ]

/-- Independently marking two optional occurrence enumerations of the same measure gives the same
marked law, even across different countable index types and different arrangements of `none` gaps.
No assumption on the ground measurable space is required. -/
theorem optionalTupleMarking_eq_of_sum_elim_dirac_eq {ι ι' : Type*} [Countable ι] [Countable ι']
    {x : ι → Option X} {y : ι' → Option X}
    (h : (Measure.sum fun i => (x i).elim 0 Measure.dirac) =
      (Measure.sum fun j => (y j).elim 0 Measure.dirac)) :
    κ.optionalTupleMarking ι x = κ.optionalTupleMarking ι' y := by
  simpa only [Measure.map_id] using
    Measure.map_eq_of_laplaceFunctional_eq (P := κ.optionalTupleMarking ι x)
      (Q := κ.optionalTupleMarking ι' y)
      measurable_id.aemeasurable measurable_id.aemeasurable fun f hf => by
        rw [Measure.laplaceFunctional_def, Measure.laplaceFunctional_def]
        simp only [id_eq, lintegral_expNeg_optionalTupleMarking_eq_expNeg_lintegral κ _ hf, h]

/-- Marked optional-tuple laws agree if and only if the counting measures of their present entries
agree. -/
@[simp]
theorem optionalTupleMarking_eq_iff_sum_elim_dirac_eq {ι ι' : Type*} [Countable ι] [Countable ι']
    {x : ι → Option X} {y : ι' → Option X} :
    κ.optionalTupleMarking ι x = κ.optionalTupleMarking ι' y ↔
      (Measure.sum fun i => (x i).elim 0 Measure.dirac) =
        (Measure.sum fun j => (y j).elim 0 Measure.dirac) := by
  refine ⟨fun h => ?_, κ.optionalTupleMarking_eq_of_sum_elim_dirac_eq⟩
  have hground := congrArg (fun ν : Measure (Measure (X × E)) =>
    ν.map (fun μ => μ.map Prod.fst)) h
  simp only [map_map_fst_optionalTupleMarking] at hground
  ext s hs
  have heval := congrArg (fun ν : Measure (Measure X) => ν.map (fun μ => μ s)) hground
  simpa only [Measure.map_dirac' (Measure.measurable_coe hs),
    MeasureTheory.dirac_eq_dirac_iff] using heval

end Optional

end ProbabilityTheory.Kernel
