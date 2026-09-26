/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.CutNorm
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Average
import TauCeti.MeasureTheory.Integral.Finpartition
import TauCeti.MeasureTheory.MeasurableSpace.Finpartition

/-!
# Block averaging and the cut norm

Block averaging a graphon over a measurable finite partition interacts well with the cut norm.
Each block average is a Lipschitz function of the graphon in cut norm, with constant the inverse
measure of the block (`abs_blockAverage_sub_blockAverage_le`), and block averaging is a
contraction: the cut norm of the difference of two block-average step graphons is at most the cut
norm of the difference of the graphons (`cutNorm_stepGraphonAvg_sub_stepGraphonAvg_le`).

The contraction holds because the integral of a block-average step graphon over a measurable
rectangle `S ×ˢ T` is the integral of the graphon against the two `[0, 1]`-valued test functions
recording, on each part, the proportion of the part lying in `S` (respectively `T`); such test
integrals are bounded by the cut norm.

## Main results

* `TauCeti.DenseGraphLimits.abs_blockAverage_sub_blockAverage_le` -- block averages are cut-norm
  Lipschitz;
* `TauCeti.DenseGraphLimits.cutNorm_stepGraphonAvg_sub_stepGraphonAvg_le` -- block averaging is a
  cut-norm contraction.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  (P : Finpartition (Set.univ : Set Ω))

/-- A block average is a Lipschitz function of the graphon in cut norm, with constant the inverse
measure of the block.  On a null block both averages are zero and the constant is zero. -/
theorem abs_blockAverage_sub_blockAverage_le (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (W W' : Graphon Ω μ) (p q : P.parts) :
    |(blockAverage P W p q : ℝ) - blockAverage P W' p q| ≤
      (μ.real (p : Set Ω) * μ.real (q : Set Ω))⁻¹ *
        cutNorm μ (W.toSymmKernel - W'.toSymmKernel) := by
  rw [coe_blockAverage_eq_inv_mul_rectIntegral, coe_blockAverage_eq_inv_mul_rectIntegral,
    ← mul_sub, ← SymmKernel.rectIntegral_sub, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (abs_rectIntegral_le_cutNorm μ _ (hP p p.property) (hP q q.property)) (by positivity)

/-- The proportion of the part containing `x` that lies in `S`, as a test function on `Ω`.  It is
zero on null parts. -/
private def partProportion (S : Set Ω) (x : Ω) : ℝ :=
  μ.real ((P.indexedPartition.index x : Set Ω) ∩ S) / μ.real (P.indexedPartition.index x : Set Ω)

omit [IsProbabilityMeasure μ] in
private theorem measurable_partProportion (hP : ∀ p ∈ P.parts, MeasurableSet p) (S : Set Ω) :
    Measurable (partProportion (μ := μ) P S) := by
  let : MeasurableSpace P.parts := ⊤
  exact (measurable_of_countable
    (fun p : P.parts => μ.real ((p : Set Ω) ∩ S) / μ.real (p : Set Ω))).comp
    (P.measurable_indexedPartition_index hP)

private theorem partProportion_mem_Icc (S : Set Ω) (x : Ω) :
    partProportion (μ := μ) P S x ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg measureReal_nonneg measureReal_nonneg,
    div_le_one_of_le₀ (measureReal_mono inter_subset_left) measureReal_nonneg⟩

private theorem partProportion_mem_Icc_neg_one_one (S : Set Ω) (x : Ω) :
    partProportion (μ := μ) P S x ∈ Icc (-1 : ℝ) 1 :=
  Icc_subset_Icc (by norm_num) le_rfl (partProportion_mem_Icc P S x)

omit [IsProbabilityMeasure μ] in
private theorem partProportion_apply (S : Set Ω) {p : P.parts} {x : Ω} (hx : x ∈ (p : Set Ω)) :
    partProportion (μ := μ) P S x = μ.real ((p : Set Ω) ∩ S) / μ.real (p : Set Ω) := by
  rw [partProportion, P.indexedPartition.mem_iff_index_eq.1 hx]

/-- The integral of the difference of two block-average step graphons over a measurable rectangle
is the test integral of the difference of the graphons against the part-proportion functions. -/
private theorem rectIntegral_stepGraphonAvg_sub_eq_testIntegral
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (W W' : Graphon Ω μ) {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ((stepGraphonAvg (μ := μ) P hP W).toSymmKernel -
        (stepGraphonAvg (μ := μ) P hP W').toSymmKernel).rectIntegral μ S T =
      (W.toSymmKernel - W'.toSymmKernel).testIntegral μ (partProportion (μ := μ) P S)
        (partProportion (μ := μ) P T) := by
  set D := W.toSymmKernel - W'.toSymmKernel
  rw [SymmKernel.rectIntegral_def, SymmKernel.testIntegral_def,
    Finpartition.setIntegral_prod_eq_sum_parts μ P hP hS hT
      (SymmKernel.integrable_uncurry μ _).integrableOn,
    Finpartition.integral_eq_sum_parts μ P hP
      (D.integrable_testIntegrand μ (measurable_partProportion P hP S)
        (measurable_partProportion P hP T) (partProportion_mem_Icc_neg_one_one P S)
        (partProportion_mem_Icc_neg_one_one P T))]
  refine Finset.sum_congr rfl fun pq _ => ?_
  obtain ⟨p, q⟩ := pq
  -- Both integrands are constant on the rectangle, so both integrals are explicit products.
  have hleft : ∫ z in ((p : Set Ω) ∩ S) ×ˢ ((q : Set Ω) ∩ T),
      ((stepGraphonAvg (μ := μ) P hP W).toSymmKernel -
        (stepGraphonAvg (μ := μ) P hP W').toSymmKernel) z.1 z.2 ∂(μ.prod μ) =
      μ.real ((p : Set Ω) ∩ S) * μ.real ((q : Set Ω) ∩ T) *
        ((blockAverage P W p q : ℝ) - blockAverage P W' p q) := by
    rw [setIntegral_congr_fun (((hP p p.property).inter hS).prod ((hP q q.property).inter hT))
      (g := fun _ => (blockAverage P W p q : ℝ) - blockAverage P W' p q)
      (fun z hz => by
        simp only [SymmKernel.coe_sub, Pi.sub_apply, Graphon.coe_toSymmKernel,
          stepGraphonAvg_apply P hP W hz.1.1 hz.2.1, stepGraphonAvg_apply P hP W' hz.1.1 hz.2.1,
          coe_blockAverage]),
      setIntegral_const, measureReal_prod_prod, smul_eq_mul]
  have hright : ∫ z in (p : Set Ω) ×ˢ (q : Set Ω),
      partProportion (μ := μ) P S z.1 * partProportion (μ := μ) P T z.2 * D z.1 z.2 ∂(μ.prod μ) =
      μ.real ((p : Set Ω) ∩ S) / μ.real (p : Set Ω) *
        (μ.real ((q : Set Ω) ∩ T) / μ.real (q : Set Ω)) *
          D.rectIntegral μ (p : Set Ω) (q : Set Ω) := by
    rw [setIntegral_congr_fun ((hP p p.property).prod (hP q q.property))
      (g := fun z => μ.real ((p : Set Ω) ∩ S) / μ.real (p : Set Ω) *
        (μ.real ((q : Set Ω) ∩ T) / μ.real (q : Set Ω)) * D z.1 z.2)
      (fun z hz => by rw [partProportion_apply P S hz.1, partProportion_apply P T hz.2]),
      integral_const_mul, SymmKernel.rectIntegral_def]
  rw [hleft, hright, coe_blockAverage_eq_inv_mul_rectIntegral,
    coe_blockAverage_eq_inv_mul_rectIntegral, ← mul_sub, ← SymmKernel.rectIntegral_sub,
    mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **Block averaging is a cut-norm contraction.** -/
theorem cutNorm_stepGraphonAvg_sub_stepGraphonAvg_le (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (W W' : Graphon Ω μ) :
    cutNorm μ ((stepGraphonAvg (μ := μ) P hP W).toSymmKernel -
        (stepGraphonAvg (μ := μ) P hP W').toSymmKernel) ≤
      cutNorm μ (W.toSymmKernel - W'.toSymmKernel) := by
  refine cutNorm_le μ fun S hS T hT => ?_
  rw [rectIntegral_stepGraphonAvg_sub_eq_testIntegral P hP W W' hS hT]
  exact abs_testIntegral_le_cutNorm μ _ (measurable_partProportion P hP S)
    (measurable_partProportion P hP T) (partProportion_mem_Icc P S) (partProportion_mem_Icc P T)

end DenseGraphLimits

end TauCeti
