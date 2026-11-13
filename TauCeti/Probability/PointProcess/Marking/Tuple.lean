/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Marking.Optional
import TauCeti.Probability.RandomMeasure.Determination

/-!
# Independent marking of countable occurrence tuples

`Kernel.tupleMarking κ ι` attaches mutually independent marks with laws `κ (x i)`
to the occurrences of a countable tuple `x : ι → X`, retaining multiplicities.
Its values are probability laws on measures on `X × E`. No local finiteness or
simplicity is imposed on the tuple, and finite and empty index types are allowed.

The marked law projects to the point mass at the original counting measure, has
intensity equal to the sum of the individual marked occurrence laws, and is
unchanged by bijective relabeling. Its Laplace functional is the infinite
product of the individual mark transforms, including extended-valued tests.
These are the sequence-level construction and
consistency identities used when defining independent marking through an
occurrence enumeration. This file does not choose an enumeration of a measure.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 5 (independent marking).

The construction specializes `Kernel.optionalTupleMarking` to tuples with every
entry present, reusing its countable marking identities.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
  (κ : Kernel X E) [IsMarkovKernel κ]

/-- The law of independently marking each occurrence of a countable tuple.
Equal ground locations still receive independent marks. -/
def tupleMarking (ι : Type*) [Countable ι] : Kernel (ι → X) (Measure (X × E)) :=
  (κ.optionalTupleMarking ι).comap (fun x i => some (x i)) (by fun_prop)

/-- Marking a tuple with no absent entries agrees with ordinary tuple marking. -/
@[simp]
theorem optionalTupleMarking_some {ι : Type*} [Countable ι] (x : ι → X) :
    κ.optionalTupleMarking ι (fun i => some (x i)) = κ.tupleMarking ι x := (rfl)

/-- Evaluation of the tuple marking kernel as a pushforward of the product of
individual marked occurrence laws. -/
theorem tupleMarking_apply {ι : Type*} [Countable ι] (x : ι → X) :
    κ.tupleMarking ι x =
      (Measure.infinitePi fun i => (Kernel.id ×ₖ κ) (x i)).map
        (fun z => Measure.sum fun i => Measure.dirac (z i)) := by
  rw [← optionalTupleMarking_some, optionalTupleMarking_apply]
  simp only [optionalMark_some]
  rw [← Measure.infinitePi_map_pi _ (fun _ => Measure.measurable_dirac),
    Measure.map_map TauCeti.MeasureTheory.measurable_measure_sum (by fun_prop)]
  rfl

/-- Tuple marking is a probability kernel, including for an empty tuple. -/
instance (ι : Type*) [Countable ι] : IsMarkovKernel (κ.tupleMarking ι) := by
  unfold tupleMarking
  infer_instance

/-- Nonnegative integration against the marking law is integration over the
independent marked occurrences. -/
theorem lintegral_tupleMarking {ι : Type*} [Countable ι] (x : ι → X)
    {f : Measure (X × E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ μ, f μ ∂κ.tupleMarking ι x =
      ∫⁻ z, f (Measure.sum fun i => Measure.dirac (z i))
        ∂Measure.infinitePi (fun i => (Kernel.id ×ₖ κ) (x i)) := by
  rw [tupleMarking_apply,
    MeasureTheory.lintegral_map hf TauCeti.MeasureTheory.measurable_sum_dirac]

/-- The intensity of a marked tuple is the sum of its individual marked
occurrence laws. Neither the tuple nor its intensity need be locally finite. -/
theorem bind_tupleMarking {ι : Type*} [Countable ι] (x : ι → X) :
    (κ.tupleMarking ι x).bind id = Measure.sum fun i => (Kernel.id ×ₖ κ) (x i) := by
  simpa only [optionalTupleMarking_some, Option.elim_some] using
    bind_optionalTupleMarking κ (fun i => some (x i))

/-- Bijective relabeling of occurrences does not change their marked law. -/
theorem tupleMarking_comp_equiv {ι ι' : Type*} [Countable ι] [Countable ι']
    (e : ι' ≃ ι) (x : ι → X) :
    κ.tupleMarking ι' (x ∘ e) = κ.tupleMarking ι x := by
  simpa only [Function.comp_def, optionalTupleMarking_some] using
    optionalTupleMarking_comp_equiv κ e (fun i => some (x i))

/-- Forgetting all marks gives the point mass at the original counting measure.
No countable-generation or measurable-singleton assumption on the ground space is needed. -/
@[simp]
theorem map_map_fst_tupleMarking {ι : Type*} [Countable ι] (x : ι → X) :
    (κ.tupleMarking ι x).map (fun μ => μ.map Prod.fst) =
      Measure.dirac (Measure.sum fun i => Measure.dirac (x i)) := by
  simpa only [optionalTupleMarking_some, Option.elim_some] using
    map_map_fst_optionalTupleMarking κ (fun i => some (x i))

/-- The Laplace functional of a countable marked tuple is the product of the mark
transforms. Infinite test values contribute zero at their occurrences. -/
theorem lintegral_expNeg_tupleMarking {ι : Type*} [Countable ι] (x : ι → X)
    {f : X × E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ μ, (ENNReal.expNeg (∫⁻ p, f p ∂μ) : ℝ≥0∞) ∂κ.tupleMarking ι x =
      ∏' i, ∫⁻ e, (ENNReal.expNeg (f (x i, e)) : ℝ≥0∞) ∂κ (x i) := by
  simpa only [optionalTupleMarking_some, Option.elim_some] using
    lintegral_expNeg_optionalTupleMarking κ (fun i => some (x i)) hf

/-- Deterministic marks give a deterministic marked counting measure, for finite
or infinite tuples and with multiplicities retained. -/
@[simp]
theorem tupleMarking_deterministic {ι : Type*} [Countable ι] {g : X → E}
    (hg : Measurable g) (x : ι → X) :
    (Kernel.deterministic g hg).tupleMarking ι x =
      Measure.dirac (Measure.sum fun i => Measure.dirac (x i, g (x i))) := by
  simpa only [optionalTupleMarking_some, Option.elim_some] using
    optionalTupleMarking_deterministic hg (fun i => some (x i))

/-- Marking an empty tuple gives the empty measure with probability one. -/
@[simp]
theorem tupleMarking_of_isEmpty {ι : Type*} [Countable ι] [IsEmpty ι] (x : ι → X) :
    κ.tupleMarking ι x = Measure.dirac 0 := by
  simpa only [optionalTupleMarking_some] using
    optionalTupleMarking_of_isEmpty κ (fun i => some (x i))

/-- Optional tuple marking coincides with ordinary tuple marking restricted to the subtype of
present indices. No assumption on the ground measurable space is required. -/
theorem optionalTupleMarking_eq_tupleMarking {ι : Type*} [Countable ι] (x : ι → Option X) :
    κ.optionalTupleMarking ι x =
      κ.tupleMarking {i : ι // (x i).isSome} (fun j => (x j.1).get j.2) := by
  simpa only [Measure.map_id] using
    Measure.map_eq_of_laplaceFunctional_eq (P := κ.optionalTupleMarking ι x)
      (Q := κ.tupleMarking {i : ι // (x i).isSome} (fun j => (x j.1).get j.2))
      measurable_id.aemeasurable measurable_id.aemeasurable fun f hf => by
        rw [Measure.laplaceFunctional_def, Measure.laplaceFunctional_def]
        simp only [id_eq, lintegral_expNeg_optionalTupleMarking κ x hf,
          lintegral_expNeg_tupleMarking κ _ hf]
        classical
        let g : ι → ℝ≥0∞ :=
          fun i => (x i).elim 1 (fun a => ∫⁻ e, (ENNReal.expNeg (f (a, e)) : ℝ≥0∞) ∂κ a)
        have hsub : (∏' j : {i : ι // (x i).isSome},
              ∫⁻ e, (ENNReal.expNeg (f ((x j.1).get j.2, e)) : ℝ≥0∞) ∂κ ((x j.1).get j.2)) =
            ∏' j : ({i : ι | (x i).isSome = true} : Set ι), g j.1 :=
          tprod_congr fun j => by
            dsimp only [g]
            conv_rhs => rw [← Option.some_get j.2]
            rfl
        symm
        rw [hsub, tprod_subtype {i : ι | (x i).isSome = true} g]
        refine tprod_congr fun i => ?_
        cases hx : x i <;> simp [g, hx]

end ProbabilityTheory.Kernel
