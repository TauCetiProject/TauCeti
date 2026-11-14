/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Marking.Optional

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
  (κ.optionalTupleMarking ι).comap (fun (x : ι → X) i => some (x i))
    (Measurable.of_eval fun i => Option.measurable_some.comp (measurable_pi_apply i))

/-- Kernel-level characterization of `Kernel.tupleMarking` as the pullback of
`Kernel.optionalTupleMarking` along `fun x i => some (x i)`. -/
theorem tupleMarking_def (ι : Type*) [Countable ι] :
    κ.tupleMarking ι =
      (κ.optionalTupleMarking ι).comap (fun (x : ι → X) i => some (x i))
        (Measurable.of_eval fun i => Option.measurable_some.comp (measurable_pi_apply i)) :=
  (rfl)

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

/-- Exponential-integral form of the Laplace functional of tuple marking, expressed as an integral
against the ground counting measure of the tuple. -/
theorem lintegral_expNeg_tupleMarking_eq_expNeg_lintegral {ι : Type*} [Countable ι] (x : ι → X)
    {f : X × E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ μ, (ENNReal.expNeg (∫⁻ p, f p ∂μ) : ℝ≥0∞) ∂κ.tupleMarking ι x =
      (ENNReal.expNeg (∫⁻ a,
        (-ENNReal.log (∫⁻ e, (ENNReal.expNeg (f (a, e)) : ℝ≥0∞) ∂κ a)).toENNReal
        ∂Measure.sum (fun i => Measure.dirac (x i))) : ℝ≥0∞) := by
  simpa only [optionalTupleMarking_some, Option.elim_some] using
    lintegral_expNeg_optionalTupleMarking_eq_expNeg_lintegral κ (fun i => some (x i)) hf

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

/-- Under tuple marking, the ground projection on any measurable set almost surely equals the
counting-measure mass of the tuple. No assumption on the ground measurable space is required. -/
theorem ae_map_fst_apply_tupleMarking {ι : Type*} [Countable ι] (x : ι → X)
    {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ μ ∂κ.tupleMarking ι x,
      μ.map Prod.fst A = (Measure.sum fun i => Measure.dirac (x i)) A := by
  simpa only [optionalTupleMarking_some, Option.elim_some] using
    ae_map_fst_apply_optionalTupleMarking κ (fun i => some (x i)) hA

/-- Setwise ground-projection recovery for tuple marking of an arbitrary random measure: on any
fixed measurable set `A`, projecting the marked realization back to `X` almost surely recovers
`N z.1 A`. -/
theorem ae_map_fst_apply_compProd_tupleMarking {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {N : Ω → Measure X}
    {e : Ω → ι → X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i => Measure.dirac (e ω i)))
    {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ z ∂(P ⊗ₘ (κ.tupleMarking ι).comap e he), z.2.map Prod.fst A = N z.1 A := by
  rw [tupleMarking_def, ← Kernel.comap_comp_right]
  exact κ.ae_map_fst_apply_compProd_optionalTupleMarking _
    (by simpa only [Function.comp_apply, Option.elim_some] using hae) hA

/-- Measure-level ground-projection recovery for tuple marking on a countably generated ground
space: if `N` is almost surely finite on each piece of a countable measurable cover of `X`,
projecting the marked realization onto the first coordinate recovers `N z.1` almost surely. -/
theorem ae_map_fst_compProd_tupleMarking [MeasurableSpace.CountablyGenerated X]
    {Ω ι ι' : Type*} [MeasurableSpace Ω] [Countable ι] [Countable ι']
    {P : Measure Ω} {N : Ω → Measure X}
    {e : Ω → ι → X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i => Measure.dirac (e ω i)))
    {s : ι' → Set X} (hs : ∀ j, MeasurableSet (s j)) (hcover : ⋃ j, s j = Set.univ)
    (hfin : ∀ j, ∀ᵐ ω ∂P, N ω (s j) ≠ ∞) :
    ∀ᵐ z ∂(P ⊗ₘ (κ.tupleMarking ι).comap e he), z.2.map Prod.fst = N z.1 := by
  rw [tupleMarking_def, ← Kernel.comap_comp_right]
  exact κ.ae_map_fst_compProd_optionalTupleMarking _
    (by simpa only [Function.comp_apply, Option.elim_some] using hae) hs hcover hfin

end ProbabilityTheory.Kernel
