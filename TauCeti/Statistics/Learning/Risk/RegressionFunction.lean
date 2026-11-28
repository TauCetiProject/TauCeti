/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Regression functions for binary classification

For a finite joint measure of features and Boolean labels, a regression function gives the
conditional probability of the label `true` as a function of the feature. Its integrals over feature
sets recover the positive-label rectangle masses, and integrating its complement recovers the
negative-label masses. These identities allow classification risk to be evaluated on the feature
marginal.

A finite joint measure admits a regression function, unique almost everywhere for its feature
marginal. For a finite feature measure and a Markov kernel, the kernel's mass at `true` is a
regression function for the resulting joint measure. Existence uses Mathlib's conditional kernel
`MeasureTheory.Measure.condKernel`.

## References

* L. Devroye, L. Györfi, G. Lugosi, *A Probabilistic Theory of Pattern Recognition* (1996), §2.1.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]

/-- A version of the conditional probability of label `true` given the feature under a finite
joint measure. It is measurable, takes values in `[0, 1]`, and integrates against the feature
marginal over each measurable feature set to give the mass of that set with label `true`. -/
@[mk_iff]
structure IsRegressionFunction (P : Measure (X × Bool)) [IsFiniteMeasure P] (η : X → ℝ) : Prop where
  /-- The regression function is measurable. -/
  measurable : Measurable η
  /-- The regression function takes values in the unit interval at every feature. -/
  mem_Icc : ∀ x, η x ∈ Icc (0 : ℝ) 1
  /-- Integrating over a feature set gives its positive-label mass. -/
  measureReal_prod_true : ∀ ⦃A : Set X⦄, MeasurableSet A →
    P.real (A ×ˢ {true}) = ∫ x in A, η x ∂(P.map Prod.fst)

variable {P : Measure (X × Bool)} [IsFiniteMeasure P] {η η' : X → ℝ}

/-- A regression function is integrable for the feature marginal of a finite measure. -/
theorem IsRegressionFunction.integrable (hη : IsRegressionFunction P η) :
    Integrable η (P.map Prod.fst) :=
  Integrable.of_bound hη.measurable.aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hη.mem_Icc x).1]
      exact (hη.mem_Icc x).2)

/-- The complement of a regression function integrates to the negative-label mass. -/
theorem IsRegressionFunction.measureReal_prod_false (hη : IsRegressionFunction P η)
    {A : Set X} (hA : MeasurableSet A) :
    P.real (A ×ˢ {false}) = ∫ x in A, (1 - η x) ∂(P.map Prod.fst) := by
  have hfalse : A ×ˢ ({false} : Set Bool) = Prod.fst ⁻¹' A \ (A ×ˢ {true}) := by
    ext ⟨x, b⟩
    cases b <;> simp [mem_sdiff]
  rw [hfalse,
    measureReal_sdiff (prod_subset_preimage_fst _ _) (hA.prod (measurableSet_singleton _)),
    hη.measureReal_prod_true hA, integral_sub (integrable_const _) hη.integrable.integrableOn,
    setIntegral_one_eq_measureReal, map_measureReal_apply measurable_fst hA]

/-- The feature marginal of a label slice is the full marginal weighted by the conditional
probability of that label. -/
theorem IsRegressionFunction.map_restrict_prod_eq_withDensity (hη : IsRegressionFunction P η)
    (b : Bool) :
    (P.restrict (univ ×ˢ {b})).map Prod.fst =
      (P.map Prod.fst).withDensity (fun x ↦ ENNReal.ofReal (if b then η x else 1 - η x)) := by
  ext A hA
  have hinter : Prod.fst ⁻¹' A ∩ (univ ×ˢ ({b} : Set Bool)) = A ×ˢ {b} := by
    rw [← prod_univ]
    simp [prod_inter_prod]
  rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA), hinter,
    withDensity_apply _ hA]
  have hmass : P.real (A ×ˢ {b}) =
      ∫ x in A, (if b then η x else 1 - η x) ∂(P.map Prod.fst) := by
    cases b
    · simpa only [Bool.false_eq_true, ite_false] using hη.measureReal_prod_false hA
    · simpa only [ite_true] using hη.measureReal_prod_true hA
  have hInt : Integrable (fun x ↦ if b then η x else 1 - η x) (P.map Prod.fst) := by
    cases b
    · simpa only [Bool.false_eq_true, ite_false] using (integrable_const 1).sub' hη.integrable
    · simpa only [ite_true] using hη.integrable
  have hnonneg : 0 ≤ᵐ[(P.map Prod.fst).restrict A]
      (fun x ↦ if b then η x else 1 - η x) := ae_of_all _ fun x ↦ by
    simp only [Pi.zero_apply]
    split
    · exact (hη.mem_Icc x).1
    · exact sub_nonneg.mpr (hη.mem_Icc x).2
  rw [← ofReal_integral_eq_lintegral_ofReal hInt.integrableOn hnonneg, ← hmass,
    ofReal_measureReal]

/-- A measurable, unit-interval-valued modification on a marginal null set is still a regression
function. -/
theorem IsRegressionFunction.congr (hη : IsRegressionFunction P η)
    (h : η =ᵐ[P.map Prod.fst] η') (hη' : Measurable η') (h01 : ∀ x, η' x ∈ Icc (0 : ℝ) 1) :
    IsRegressionFunction P η' :=
  ⟨hη', h01, fun _ hA ↦ (hη.measureReal_prod_true hA).trans
    (integral_congr_ae (ae_restrict_of_ae h))⟩

/-- Two regression functions for the same finite joint measure agree almost everywhere with
respect to its feature marginal. -/
theorem IsRegressionFunction.ae_eq (hη : IsRegressionFunction P η)
    (hη' : IsRegressionFunction P η') : η =ᵐ[P.map Prod.fst] η' :=
  hη.integrable.ae_eq_of_forall_setIntegral_eq η η' hη'.integrable
    (fun _ hA _ ↦ (hη.measureReal_prod_true hA).symm.trans (hη'.measureReal_prod_true hA))

end TauCeti

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- For a finite feature measure, a Markov kernel's probability of `true` is a regression function
of the resulting joint measure. -/
theorem isRegressionFunction_compProd (μ : Measure X) [IsFiniteMeasure μ] (κ : Kernel X Bool)
    [IsMarkovKernel κ] : TauCeti.IsRegressionFunction (μ ⊗ₘ κ) (fun x ↦ (κ x).real {true}) := by
  have hm := κ.measurable_coe (measurableSet_singleton true)
  refine ⟨hm.ennreal_toReal, fun x ↦ ⟨measureReal_nonneg, measureReal_le_one⟩, fun A hA ↦ ?_⟩
  have hfst : (μ ⊗ₘ κ).map Prod.fst = μ := by rw [← Measure.fst, Measure.fst_compProd]
  rw [hfst, measureReal_def, Measure.compProd_apply_prod hA (measurableSet_singleton true)]
  exact (integral_toReal hm.aemeasurable
    (ae_of_all _ fun x ↦ measure_lt_top (κ x) {true})).symm

/-- Every finite joint measure of features and Boolean labels admits a regression function. -/
theorem exists_isRegressionFunction (P : Measure (X × Bool)) [IsFiniteMeasure P] :
    ∃ η : X → ℝ, TauCeti.IsRegressionFunction P η := by
  refine ⟨fun x ↦ (P.condKernel x).real {true}, ?_⟩
  simpa only [P.disintegrate P.condKernel] using P.fst.isRegressionFunction_compProd P.condKernel

end MeasureTheory.Measure
