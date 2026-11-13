/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProductKernel
public import TauCeti.MeasureTheory.Measure.Measurability
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Independence.InfinitePi
public import TauCeti.Analysis.SpecialFunctions.Exp.Negative
import Mathlib.Probability.Independence.Integration

/-!
# Independent marking of countable occurrence tuples

`Kernel.tupleMarking κ ι` attaches mutually independent marks with laws `κ (x i)`
to the occurrences of a countable tuple `x : ι → X`, retaining multiplicities.
Its values are probability laws on measures on `X × E`. No local finiteness or
simplicity is imposed on the tuple, and finite and empty index types are allowed.

The marked law projects to the point mass at the original counting measure, has
intensity equal to the sum of the individual marked occurrence laws, and is
unchanged by bijective relabeling. For finite tuples its Laplace functional is the
product of the individual mark transforms, including extended-valued tests.
These are the sequence-level construction and
consistency identities used when defining independent marking through an
occurrence enumeration. This file does not choose an enumeration of a measure.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 5 (independent marking).

The construction uses Mathlib's `Measure.infinitePi` and the measurable
product-law API in `TauCeti.MeasureTheory.Measure.ProductKernel`.
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
def tupleMarking (ι : Type*) [Countable ι] : Kernel (ι → X) (Measure (X × E)) where
  toFun x := (Measure.infinitePi fun i => (Kernel.id ×ₖ κ) (x i)).map
    (fun z => Measure.sum fun i => Measure.dirac (z i))
  measurable' := by
    apply (Measure.measurable_map _ TauCeti.MeasureTheory.measurable_sum_dirac).comp
    have hp : Measurable (fun x : ι → X => fun i =>
        (⟨(Kernel.id ×ₖ κ) (x i), inferInstance⟩ : ProbabilityMeasure (X × E))) :=
      Measurable.of_eval fun i =>
        (((Kernel.id ×ₖ κ).measurable).comp (measurable_pi_apply i)).subtype_mk
    exact TauCeti.MeasureTheory.measurable_infinitePi.comp hp

/-- Evaluation of the tuple marking kernel as a pushforward of the product of
individual marked occurrence laws. -/
theorem tupleMarking_apply {ι : Type*} [Countable ι] (x : ι → X) :
    κ.tupleMarking ι x =
      (Measure.infinitePi fun i => (Kernel.id ×ₖ κ) (x i)).map
        (fun z => Measure.sum fun i => Measure.dirac (z i)) := (rfl)

/-- Tuple marking is a probability kernel, including for an empty tuple. -/
instance (ι : Type*) [Countable ι] : IsMarkovKernel (κ.tupleMarking ι) where
  isProbabilityMeasure x := by
    rw [tupleMarking_apply]
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
  ext s hs
  rw [Measure.bind_apply hs measurable_id.aemeasurable]
  simp only [id_eq]
  rw [lintegral_tupleMarking κ x (Measure.measurable_coe hs)]
  simp only [Measure.sum_apply _ hs]
  rw [lintegral_tsum]
  · congr 1
    funext i
    simpa [Function.comp_def, Measure.dirac_apply' _ hs, ← Set.indicator_apply,
      lintegral_indicator hs] using
      (measurePreserving_eval_infinitePi (fun i => (Kernel.id ×ₖ κ) (x i)) i).lintegral_comp
        (Measure.measurable_coe hs |>.comp Measure.measurable_dirac)
  · exact fun i => ((Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp (measurable_pi_apply i))).aemeasurable

/-- Bijective relabeling of occurrences does not change their marked law. -/
theorem tupleMarking_comp_equiv {ι ι' : Type*} [Countable ι] [Countable ι']
    (e : ι' ≃ ι) (x : ι → X) :
    κ.tupleMarking ι' (x ∘ e) = κ.tupleMarking ι x := by
  have hmap := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun i => (Kernel.id ×ₖ κ) (x i)) e.injective
  simp only [tupleMarking_apply, Function.comp_apply]
  rw [← hmap, Measure.map_map TauCeti.MeasureTheory.measurable_sum_dirac (by fun_prop)]
  congr 1
  funext z
  exact Measure.sum_comp_equiv e (fun i => Measure.dirac (z i))

/-- Forgetting all marks gives the point mass at the original counting measure.
No countable-generation or measurable-singleton assumption on the ground space is needed. -/
@[simp]
theorem map_map_fst_tupleMarking {ι : Type*} [Countable ι] (x : ι → X) :
    (κ.tupleMarking ι x).map (fun μ => μ.map Prod.fst) =
      Measure.dirac (Measure.sum fun i => Measure.dirac (x i)) := by
  have hm : Measurable (fun z : ι → X × E => fun i => (z i).1) := by fun_prop
  have hground (z : ι → X × E) :
      (Measure.sum fun i => Measure.dirac (z i)).map Prod.fst =
        Measure.sum fun i => Measure.dirac (z i).1 := by
    rw [Measure.map_sum measurable_fst.aemeasurable]
    simp only [Measure.map_dirac' measurable_fst]
  rw [tupleMarking_apply,
    Measure.map_map (Measure.measurable_map _ measurable_fst)
      TauCeti.MeasureTheory.measurable_sum_dirac]
  simp_rw [Function.comp_def, hground]
  have hmap := Measure.map_map (μ := Measure.infinitePi fun i => (Kernel.id ×ₖ κ) (x i))
    TauCeti.MeasureTheory.measurable_sum_dirac hm
  simp only [Function.comp_def] at hmap
  rw [← hmap, Measure.infinitePi_map_pi _ (fun _ => measurable_fst)]
  have hcoord (i : ι) : ((Kernel.id ×ₖ κ) (x i)).map Prod.fst = Measure.dirac (x i) := by
    rw [← Kernel.fst_apply, Kernel.fst_prod, Kernel.id_apply]
  simp_rw [hcoord]
  rw [Measure.infinitePi_dirac, Measure.map_dirac' TauCeti.MeasureTheory.measurable_sum_dirac]

/-- The Laplace functional of a finite marked tuple is the product of the mark
transforms. Infinite test values contribute zero at their occurrences. -/
theorem lintegral_expNeg_tupleMarking {ι : Type*} [Fintype ι] (x : ι → X)
    {f : X × E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ μ, (ENNReal.expNeg (∫⁻ p, f p ∂μ) : ℝ≥0∞) ∂κ.tupleMarking ι x =
      ∏ i, ∫⁻ e, (ENNReal.expNeg (f (x i, e)) : ℝ≥0∞) ∂κ (x i) := by
  classical
  have hg : Measurable (fun p => (ENNReal.expNeg (f p) : ℝ≥0∞)) := by fun_prop
  have hM : Measurable (fun μ : Measure (X × E) =>
      (ENNReal.expNeg (∫⁻ p, f p ∂μ) : ℝ≥0∞)) := by fun_prop
  rw [lintegral_tupleMarking κ x hM]
  simp_rw [lintegral_sum_measure, lintegral_dirac' _ hf, tsum_fintype,
    ENNReal.expNeg_sum, ENNReal.ofNNReal_finsetProd]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
    (iIndepFun_infinitePi fun _ => hg) (fun i => hg.comp (measurable_pi_apply i))]
  congr 1
  funext i
  rw [(measurePreserving_eval_infinitePi (fun i => (Kernel.id ×ₖ κ) (x i)) i).lintegral_comp hg,
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    MeasureTheory.lintegral_map hg measurable_prodMk_left]

/-- Deterministic marks give a deterministic marked counting measure, for finite
or infinite tuples and with multiplicities retained. -/
@[simp]
theorem tupleMarking_deterministic {ι : Type*} [Countable ι] {g : X → E}
    (hg : Measurable g) (x : ι → X) :
    (Kernel.deterministic g hg).tupleMarking ι x =
      Measure.dirac (Measure.sum fun i => Measure.dirac (x i, g (x i))) := by
  simp [tupleMarking_apply, Kernel.prod_apply, Kernel.id_apply, Kernel.deterministic_apply,
    Measure.dirac_prod_dirac, Measure.map_dirac' TauCeti.MeasureTheory.measurable_sum_dirac]

/-- Marking an empty tuple gives the empty measure with probability one. -/
@[simp]
theorem tupleMarking_of_isEmpty {ι : Type*} [Countable ι] [IsEmpty ι] (x : ι → X) :
    κ.tupleMarking ι x = Measure.dirac 0 := by
  simp [tupleMarking_apply, Measure.sum_of_isEmpty]

end ProbabilityTheory.Kernel
