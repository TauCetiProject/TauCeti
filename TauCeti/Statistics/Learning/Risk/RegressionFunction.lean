/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Data.Bool.Set
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import TauCeti.MeasureTheory.Measure.MapRestrictDensity

/-!
# Regression functions for binary classification

For a finite joint measure of features and Boolean labels, a regression function gives the
conditional probability of the label `true` as a function of the feature. Its integrals over feature
sets recover the positive-label rectangle masses, and integrating its complement recovers the
negative-label masses. These identities allow classification risk to be evaluated on the feature
marginal.

A finite joint measure admits a regression function, unique almost everywhere for its feature
marginal. For a finite feature measure and a Markov kernel, the kernel's mass at `true` is a
regression function for the resulting joint measure.

## References

* L. Devroye, L. Györfi, G. Lugosi, *A Probabilistic Theory of Pattern Recognition* (1996), §2.1.
* The existence proof uses `TauCeti.MeasureTheory.mapRestrictDensity` for the positive-label slice.
-/

public section

open MeasureTheory ProbabilityTheory Set
open TauCeti.MeasureTheory (integral_mapRestrictDensity_mul mapRestrictDensity
  mapRestrictDensity_mem_Icc measurable_mapRestrictDensity)

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]

/-- A version of the conditional probability of label `true` given the feature under a finite
joint measure. It is measurable, takes values in `[0, 1]`, and integrates against the feature
marginal over each measurable feature set to give the mass of that set with label `true`. -/
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
  have hdisj : Disjoint (A ×ˢ ({false} : Set Bool)) (A ×ˢ {true}) :=
    disjoint_prod.mpr (Or.inr (by simp))
  have hpartition : (A ×ˢ ({false} : Set Bool)) ∪ (A ×ˢ {true}) = Prod.fst ⁻¹' A := by
    rw [← prod_union, ← insert_eq, ← Bool.univ_eq, prod_univ]
  have hmass := measureReal_union (μ := P) hdisj (hA.prod (measurableSet_singleton true))
  rw [hpartition, hη.measureReal_prod_true hA] at hmass
  rw [integral_sub (integrable_const _) hη.integrable.integrableOn, setIntegral_const,
    smul_eq_mul, mul_one]
  simp only [measureReal_def, Measure.map_apply measurable_fst hA] at hmass ⊢
  linarith only [hmass]

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

/-- Every finite joint measure of features and Boolean labels admits a regression function. -/
theorem exists_isRegressionFunction (P : Measure (X × Bool)) [IsFiniteMeasure P] :
    ∃ η : X → ℝ, TauCeti.IsRegressionFunction P η := by
  let s : Set (X × Bool) := univ ×ˢ {true}
  let μ := P.map Prod.fst
  let η := mapRestrictDensity Prod.fst P μ s
  refine ⟨η, measurable_mapRestrictDensity Prod.fst P μ s,
    mapRestrictDensity_mem_Icc Prod.fst P μ s, fun A hA ↦ ?_⟩
  have hpre : MeasurableSet ((Prod.fst : X × Bool → X) ⁻¹' A) := measurable_fst hA
  have hinter : s ∩ (Prod.fst ⁻¹' A) = A ×ˢ ({true} : Set Bool) := by
    rw [← prod_univ]
    simp [s, prod_inter_prod]
  calc
    P.real (A ×ˢ {true}) = ∫ z in s, A.indicator (1 : X → ℝ) z.1 ∂P := by
      simp only [← indicator_comp_right Prod.fst, Pi.one_def, Function.comp_apply,
        setIntegral_indicator hpre, hinter, setIntegral_const, smul_eq_mul, mul_one]
    _ = ∫ x, η x * A.indicator (1 : X → ℝ) x ∂μ :=
      (integral_mapRestrictDensity_mul measurable_fst.aemeasurable le_rfl s
        (measurable_const.indicator hA).aestronglyMeasurable).symm
    _ = ∫ x in A, η x ∂μ := by
      rw [← integral_indicator hA]
      simp only [← indicator_mul_right, Pi.one_apply, mul_one]

/-- For a finite feature measure, a Markov kernel's probability of `true` is a regression function
of the resulting joint measure. -/
theorem isRegressionFunction_compProd (μ : Measure X) [IsFiniteMeasure μ] (κ : Kernel X Bool)
    [IsMarkovKernel κ] : TauCeti.IsRegressionFunction (μ ⊗ₘ κ) (fun x ↦ (κ x).real {true}) := by
  have hm := κ.measurable_coe (measurableSet_singleton true)
  refine ⟨hm.ennreal_toReal, fun x ↦ ⟨measureReal_nonneg, measureReal_le_one⟩, fun A hA ↦ ?_⟩
  have hfst : (μ ⊗ₘ κ).map Prod.fst = μ := Measure.fst_compProd μ κ
  rw [hfst, measureReal_def, Measure.compProd_apply_prod hA (measurableSet_singleton true)]
  exact (integral_toReal hm.aemeasurable
    (ae_of_all _ fun x ↦ measure_lt_top (κ x) {true})).symm

end MeasureTheory.Measure
