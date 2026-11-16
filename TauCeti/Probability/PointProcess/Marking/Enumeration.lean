/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Marking.Tuple
public import TauCeti.MeasureTheory.Measure.Count.Enumeration

/-!
# Enumeration independence of independent marking

The law of independently marking a countable family of occurrences — whether every entry is
present (`Kernel.tupleMarking`) or some entries are absent (`Kernel.optionalTupleMarking`) —
depends only on its counting measure. Conversely, its ground projection recovers that measure,
so equality of marked laws is equivalent to equality of the original measures. This makes the
tuple constructions usable without retaining an arbitrary labeling of the occurrences or
distinguishing absent padding entries.

Dropping absent entries leaves `Kernel.optionalTupleMarking` unchanged without any separation
assumption on the ground space. Matching arbitrary enumerations needs only measurable singletons
on the ground space; no standard Borel, nonemptiness, simplicity or local-finiteness hypothesis
is needed. Multiplicities may be infinite.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5 (independent marking).

The marked laws are `Kernel.tupleMarking` and `Kernel.optionalTupleMarking`; invariance uses
`Kernel.tupleMarking_comp_equiv` after restricting optional tuples to their present indices and
matching occurrence fibers.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace ProbabilityTheory.Kernel

section OptionalReduction

variable {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
  (κ : Kernel X E) [IsMarkovKernel κ]

private theorem sum_elim_dirac_eq_sum_isSome {ι : Type*} (x : ι → Option X) :
    (Measure.sum fun i => (x i).elim 0 Measure.dirac) =
      (Measure.sum fun i : {i : ι // (x i).isSome} => Measure.dirac ((x i.1).get i.2)) := by
  ext A hA
  rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA,
    ← tsum_subtype_eq_of_support_subset (s := {i : ι | (x i).isSome}) fun i hi => by
      by_contra h
      simp only [mem_ofPred_eq, Option.not_isSome_iff_eq_none] at h
      simp [h] at hi]
  refine tsum_congr fun ⟨i, hi⟩ => ?_
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hi
  simp [ha]

/-- Dropping absent entries from an optional tuple does not change its independent marking law.
No measurable-singleton or local-finiteness assumption on the ground space is required. -/
theorem optionalTupleMarking_eq_tupleMarking_isSome {ι : Type*} [Countable ι]
    (x : ι → Option X) :
    κ.optionalTupleMarking ι x =
      κ.tupleMarking {i : ι // (x i).isSome} (fun i => (x i.1).get i.2) := by
  classical
  let S := {i : ι // (x i).isSome}
  let x' : S → Option X := fun i => some ((x i.1).get i.2)
  have hx' (i : S) : x' i = x i.1 := Option.some_get i.2
  let pad : (S → Measure (X × E)) → (ι → Measure (X × E)) :=
    fun z i => if h : (x i).isSome then z ⟨i, h⟩ else 0
  have hpad : Measurable pad := Measurable.of_eval fun i => by
    dsimp [pad]
    split_ifs with h
    · exact measurable_pi_apply (⟨i, h⟩ : S)
    · exact measurable_const
  have hsum : ∀ z : S → Measure (X × E), Measure.sum (pad z) = Measure.sum z := by
    intro z
    ext A hA
    rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA,
      ← tsum_subtype_eq_of_support_subset (s := {i : ι | (x i).isSome}) fun i hi => by
        by_contra h
        simp only [mem_ofPred_eq] at h
        simp [pad, h] at hi]
    refine tsum_congr fun ⟨i, hi⟩ => ?_
    dsimp only [pad]
    rw [dite_eq_left (mem_ofPred_eq.mp hi)]
  have hpi : (Measure.infinitePi fun i : S => κ.optionalMark (x' i)).map pad =
      Measure.infinitePi fun i : ι => κ.optionalMark (x i) := by
    apply Measure.eq_infinitePi
    intro s t ht
    rw [Measure.map_apply hpad (.pi s.countable_toSet fun i _ => ht i)]
    by_cases hzero : ∀ i ∈ s, ¬ (x i).isSome → (0 : Measure (X × E)) ∈ t i
    · have hpre : pad ⁻¹' (s : Set ι).pi t =
          (s.subtype fun i => (x i).isSome : Set S).pi (fun i => t i.1) := by
        ext z
        simp only [mem_preimage, mem_pi, Finset.mem_coe, pad]
        constructor
        · intro hz i hi
          simpa [i.2] using hz i.1 (Finset.mem_subtype.mp hi)
        · intro hz i hi
          split_ifs with h
          · exact hz ⟨i, h⟩ (Finset.mem_subtype.mpr hi)
          · exact hzero i hi h
      rw [hpre, Measure.infinitePi_pi _ (fun i _ => ht i.1)]
      simp_rw [hx']
      rw [Finset.prod_subtype_eq_prod_filter (f := fun i => κ.optionalMark (x i) (t i))]
      symm
      rw [← Finset.prod_filter_mul_prod_filter_not s (fun i => (x i).isSome)]
      have hone :
          ∏ i ∈ s.filter (fun i => ¬ (x i).isSome), κ.optionalMark (x i) (t i) = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        rw [Finset.mem_filter] at hi
        have hnone : x i = none := Option.not_isSome_iff_eq_none.mp hi.2
        rw [hnone, optionalMark_none, Measure.dirac_apply' _ (ht i),
          Set.indicator_of_mem (hzero i hi.1 hi.2), Pi.one_apply]
      rw [hone, mul_one]
    · push Not at hzero
      obtain ⟨i₀, hi₀s, hi₀none, hi₀notmem⟩ := hzero
      have hpre : pad ⁻¹' (s : Set ι).pi t = ∅ := by
        ext z
        simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_empty_iff_false, iff_false, not_forall]
        exact ⟨i₀, hi₀s, by simpa [pad, hi₀none] using hi₀notmem⟩
      rw [hpre, measure_empty]
      symm
      refine Finset.prod_eq_zero hi₀s ?_
      have hnone : x i₀ = none := Option.not_isSome_iff_eq_none.mp hi₀none
      rw [hnone, optionalMark_none, Measure.dirac_apply' _ (ht i₀),
        Set.indicator_of_notMem hi₀notmem]
  rw [← optionalTupleMarking_some, optionalTupleMarking_apply, optionalTupleMarking_apply,
    ← hpi, Measure.map_map TauCeti.MeasureTheory.measurable_measure_sum hpad]
  congr 1
  funext z
  exact hsum z

end OptionalReduction

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

/-- Independently marking two optional enumerations of the same counting measure gives the same
law, even across different countable index types and different placements of `none` entries. -/
theorem optionalTupleMarking_eq_of_sum_elim_dirac_eq {ι ι' : Type*} [Countable ι] [Countable ι']
    {x : ι → Option X} {y : ι' → Option X}
    (h : (Measure.sum fun i => (x i).elim 0 Measure.dirac) =
      (Measure.sum fun j => (y j).elim 0 Measure.dirac)) :
    κ.optionalTupleMarking ι x = κ.optionalTupleMarking ι' y := by
  rw [κ.optionalTupleMarking_eq_tupleMarking_isSome x,
    κ.optionalTupleMarking_eq_tupleMarking_isSome y]
  apply κ.tupleMarking_eq_of_sum_dirac_eq
  simpa only [sum_elim_dirac_eq_sum_isSome] using h

/-- Marked optional-tuple laws agree exactly when their underlying counting measures agree. -/
@[simp]
theorem optionalTupleMarking_eq_iff_sum_elim_dirac_eq
    {ι ι' : Type*} [Countable ι] [Countable ι']
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

end ProbabilityTheory.Kernel
