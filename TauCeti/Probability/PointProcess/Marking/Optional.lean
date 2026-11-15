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
public import TauCeti.Probability.RandomMeasure.Superposition
public import TauCeti.MeasureTheory.MeasurableSpace.Option

/-!
# Independent marking of optional occurrence sequences

`Kernel.optionalTupleMarking` attaches independent marks to the occurrences in a
countable `Option`-valued tuple. A `none` entry contributes the zero measure, not a
point at a chosen default location. Thus finite configurations, empty spaces, gaps
in an enumeration, and repeated locations are all allowed.

The construction first samples zero or one marked occurrence at each index with
`Kernel.optionalMark`, and then superposes the independently sampled measures.
The intensity and infinite-product Laplace formula require neither local finiteness
nor finite test integrals. These identities allow optional occurrence enumerations
to be used for independent marking of integer-valued measures.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 5 (independent marking).

Ordinary tuple marking is recovered by making every entry present. The construction uses
Mathlib's infinite product measures and the countable Laplace factorization in
`TauCeti.Probability.RandomMeasure.Superposition`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
  (κ : Kernel X E)

/-- Independently mark one optional occurrence. An absent occurrence gives the
point mass at the zero measure. -/
def optionalMark : Kernel (Option X) (Measure (X × E)) where
  toFun x := x.elim (Measure.dirac 0) fun a =>
    ((Kernel.id ×ₖ κ) a).map Measure.dirac
  measurable' := Option.measurable_elim _
    ((Measure.measurable_map _ Measure.measurable_dirac).comp (Kernel.id ×ₖ κ).measurable)

@[simp]
theorem optionalMark_none : κ.optionalMark none = Measure.dirac 0 := (rfl)

@[simp]
theorem optionalMark_some (x : X) :
    κ.optionalMark (some x) = ((Kernel.id ×ₖ κ) x).map Measure.dirac := (rfl)

/-- Integration against the law of one optional marked occurrence. -/
theorem lintegral_optionalMark [IsSFiniteKernel κ] (x : Option X) {f : Measure (X × E) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ μ, f μ ∂κ.optionalMark x =
      x.elim (f 0) (fun a => ∫⁻ e, f (Measure.dirac (a, e)) ∂κ a) := by
  cases x with
  | none => simp [lintegral_dirac' _ hf]
  | some a =>
    have hfd : Measurable (fun p : X × E => f (Measure.dirac p)) :=
      hf.comp Measure.measurable_dirac
    rw [optionalMark_some, MeasureTheory.lintegral_map hf Measure.measurable_dirac,
      Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
      MeasureTheory.lintegral_map hfd measurable_prodMk_left]
    -- Beta reduction identifies `hfd` composed with `Prod.mk a` with the displayed integrand.
    rfl

variable [IsMarkovKernel κ]

/-- Marking an optional occurrence is a probability kernel, also when the ground
or mark space is empty. -/
instance : IsMarkovKernel κ.optionalMark where
  isProbabilityMeasure x := by
    cases x <;> simp only [optionalMark_none, optionalMark_some] <;> infer_instance

/-- The law obtained by independently marking the present entries of an optional
tuple and superposing the results. Absent entries contribute no points. -/
def optionalTupleMarking (ι : Type*) [Countable ι] :
    Kernel (ι → Option X) (Measure (X × E)) where
  toFun x := (Measure.infinitePi fun i => κ.optionalMark (x i)).map Measure.sum
  measurable' := by
    apply (Measure.measurable_map _ TauCeti.MeasureTheory.measurable_measure_sum).comp
    have hp : Measurable (fun x : ι → Option X => fun i =>
        (⟨κ.optionalMark (x i), inferInstance⟩ : ProbabilityMeasure (Measure (X × E)))) :=
      Measurable.of_eval fun i =>
        (κ.optionalMark.measurable.comp (measurable_pi_apply i)).subtype_mk
    exact TauCeti.MeasureTheory.measurable_infinitePi.comp hp

/-- Product-measure evaluation of optional tuple marking. -/
theorem optionalTupleMarking_apply {ι : Type*} [Countable ι] (x : ι → Option X) :
    κ.optionalTupleMarking ι x =
      (Measure.infinitePi fun i => κ.optionalMark (x i)).map Measure.sum := (rfl)

/-- Optional tuple marking is a probability kernel, including for an empty tuple. -/
instance (ι : Type*) [Countable ι] : IsMarkovKernel (κ.optionalTupleMarking ι) where
  isProbabilityMeasure x := by
    rw [optionalTupleMarking_apply]
    infer_instance

/-- Nonnegative integration against optional tuple marking is integration over the
independent optional marked occurrences followed by superposition. -/
theorem lintegral_optionalTupleMarking {ι : Type*} [Countable ι] (x : ι → Option X)
    {f : Measure (X × E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ μ, f μ ∂κ.optionalTupleMarking ι x =
      ∫⁻ z, f (Measure.sum z) ∂Measure.infinitePi (fun i => κ.optionalMark (x i)) := by
  rw [optionalTupleMarking_apply,
    MeasureTheory.lintegral_map hf TauCeti.MeasureTheory.measurable_measure_sum]

/-- Bijectively relabeling optional occurrences leaves their marked law unchanged. -/
theorem optionalTupleMarking_comp_equiv {ι ι' : Type*} [Countable ι] [Countable ι']
    (e : ι' ≃ ι) (x : ι → Option X) :
    κ.optionalTupleMarking ι' (x ∘ e) = κ.optionalTupleMarking ι x := by
  have hs : Measurable (Measure.sum : (ι' → Measure (X × E)) → Measure (X × E)) :=
    TauCeti.MeasureTheory.measurable_measure_sum
  have hmap := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun i => κ.optionalMark (x i)) e.injective
  simp only [optionalTupleMarking_apply, Function.comp_apply]
  rw [← hmap, Measure.map_map hs (by fun_prop)]
  congr 1
  funext z
  exact Measure.sum_comp_equiv e z

/-- The Laplace functional is the product of the individual mark transforms.
An absent occurrence contributes one; an infinite test value contributes zero. -/
theorem lintegral_expNeg_optionalTupleMarking {ι : Type*} [Countable ι]
    (x : ι → Option X) {f : X × E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ μ, (ENNReal.expNeg (∫⁻ p, f p ∂μ) : ℝ≥0∞) ∂κ.optionalTupleMarking ι x =
      ∏' i, (x i).elim 1 (fun a =>
        ∫⁻ e, (ENNReal.expNeg (f (a, e)) : ℝ≥0∞) ∂κ a) := by
  have hL : Measurable (fun μ : Measure (X × E) =>
      (ENNReal.expNeg (∫⁻ p, f p ∂μ) : ℝ≥0∞)) := by fun_prop
  rw [lintegral_optionalTupleMarking κ x hL]
  have hind := iIndepFun_infinitePi (P := fun i => κ.optionalMark (x i))
    (X := fun _ μ => μ) (fun _ => measurable_id)
  rw [← Measure.laplaceFunctional_def,
    hind.laplaceFunctional_sum (fun i => measurable_pi_apply i) hf]
  apply tprod_congr
  intro i
  rw [Measure.laplaceFunctional_def,
    (measurePreserving_eval_infinitePi (fun i => κ.optionalMark (x i)) i).lintegral_comp hL,
    lintegral_optionalMark κ (x i) hL]
  cases x i <;> simp [lintegral_dirac' _ hf]

/-- An entirely absent tuple gives the empty configuration almost surely. -/
@[simp]
theorem optionalTupleMarking_none (ι : Type*) [Countable ι] :
    κ.optionalTupleMarking ι (fun _ => none) = Measure.dirac 0 := by
  simp [optionalTupleMarking_apply, Measure.infinitePi_dirac,
    Measure.map_dirac' TauCeti.MeasureTheory.measurable_measure_sum]

/-- The intensity of optional tuple marking is the sum of the individual marked
occurrence laws. Absent entries have zero intensity. -/
theorem bind_optionalTupleMarking {ι : Type*} [Countable ι] (x : ι → Option X) :
    (κ.optionalTupleMarking ι x).bind id =
      Measure.sum (fun i => (x i).elim 0 (fun a => (Kernel.id ×ₖ κ) a)) := by
  ext s hset
  rw [Measure.bind_apply hset measurable_id.aemeasurable]
  simp only [id_eq]
  rw [lintegral_optionalTupleMarking κ x (Measure.measurable_coe hset)]
  simp only [Measure.sum_apply _ hset]
  have hm (i : ι) : Measurable (fun z : ι → Measure (X × E) => z i s) :=
    (Measure.measurable_coe hset).comp (measurable_pi_apply i)
  rw [lintegral_tsum (fun i => (hm i).aemeasurable)]
  congr 1
  funext i
  rw [(measurePreserving_eval_infinitePi (fun i => κ.optionalMark (x i)) i).lintegral_comp
    (Measure.measurable_coe hset)]
  cases x i with
  | none => simp [lintegral_dirac' _ (Measure.measurable_coe hset)]
  | some a =>
    rw [optionalMark_some,
      MeasureTheory.lintegral_map (Measure.measurable_coe hset) Measure.measurable_dirac]
    simp [Measure.dirac_apply' _ hset, lintegral_indicator hset]

/-- Forgetting the mark of one optional occurrence recovers that occurrence. -/
@[simp]
theorem map_map_fst_optionalMark (x : Option X) :
    (κ.optionalMark x).map (fun μ => μ.map Prod.fst) =
      Measure.dirac (x.elim 0 Measure.dirac) := by
  cases x with
  | none => simp [Measure.map_dirac' (Measure.measurable_map _ measurable_fst)]
  | some a =>
    rw [optionalMark_some, Measure.map_map (Measure.measurable_map _ measurable_fst)
      Measure.measurable_dirac]
    simp only [Function.comp_def, Measure.map_dirac' measurable_fst, Option.elim_some]
    rw [← Function.comp_def Measure.dirac Prod.fst,
      ← Measure.map_map Measure.measurable_dirac measurable_fst,
      ← Kernel.fst_apply, Kernel.fst_prod, Kernel.id_apply,
      Measure.map_dirac' Measure.measurable_dirac]

/-- Forgetting every mark recovers the counting measure of the present entries,
with multiplicities and with zero contribution from absent entries. -/
@[simp]
theorem map_map_fst_optionalTupleMarking {ι : Type*} [Countable ι]
    (x : ι → Option X) :
    (κ.optionalTupleMarking ι x).map (fun μ => μ.map Prod.fst) =
      Measure.dirac (Measure.sum fun i => (x i).elim 0 Measure.dirac) := by
  have hs : Measurable (Measure.sum : (ι → Measure X) → Measure X) :=
    TauCeti.MeasureTheory.measurable_measure_sum
  have ht : Measurable (Measure.sum : (ι → Measure (X × E)) → Measure (X × E)) :=
    TauCeti.MeasureTheory.measurable_measure_sum
  have hm : Measurable (fun z : ι → Measure (X × E) => fun i => (z i).map Prod.fst) := by
    exact Measurable.of_eval fun i =>
      (Measure.measurable_map _ measurable_fst).comp (measurable_pi_apply i)
  rw [optionalTupleMarking_apply,
    Measure.map_map (Measure.measurable_map _ measurable_fst) ht]
  simp_rw [Function.comp_def, Measure.map_sum measurable_fst.aemeasurable]
  rw [← Function.comp_def Measure.sum
      (fun z : ι → Measure (X × E) => fun i => (z i).map Prod.fst),
    ← Measure.map_map hs hm,
    Measure.infinitePi_map_pi _ (fun _ => Measure.measurable_map _ measurable_fst)]
  simp only [map_map_fst_optionalMark, Measure.infinitePi_dirac,
    Measure.map_dirac' hs]

/-- Marking an empty tuple gives the empty configuration. -/
@[simp]
theorem optionalTupleMarking_of_isEmpty {ι : Type*} [Countable ι] [IsEmpty ι]
    (x : ι → Option X) : κ.optionalTupleMarking ι x = Measure.dirac 0 := by
  rw [Subsingleton.elim x (fun _ => none), optionalTupleMarking_none]

/-- Deterministic marking gives the point mass at the marked counting measure,
with absent entries removed. -/
@[simp]
theorem optionalTupleMarking_deterministic {ι : Type*} [Countable ι] {g : X → E}
    (hg : Measurable g) (x : ι → Option X) :
    (Kernel.deterministic g hg).optionalTupleMarking ι x =
      Measure.dirac (Measure.sum fun i => (x i).elim 0
        (fun a => Measure.dirac (a, g a))) := by
  have hs : Measurable (Measure.sum : (ι → Measure (X × E)) → Measure (X × E)) :=
    TauCeti.MeasureTheory.measurable_measure_sum
  have hc (a : Option X) : (Kernel.deterministic g hg).optionalMark a =
      Measure.dirac (a.elim 0 (fun b => Measure.dirac (b, g b))) := by
    cases a <;> simp [Kernel.prod_apply, Kernel.id_apply, Kernel.deterministic_apply,
      Measure.dirac_prod_dirac, Measure.map_dirac' Measure.measurable_dirac]
  simp only [optionalTupleMarking_apply, hc, Measure.infinitePi_dirac,
    Measure.map_dirac' hs]

end ProbabilityTheory.Kernel
