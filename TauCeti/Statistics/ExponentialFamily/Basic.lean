/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import TauCeti.MeasureTheory.Measure.Tilted

/-!
# Natural exponential families

The natural parameter space consists of the parameters at which the exponential weight is
integrable. It is convex. The associated law is Mathlib's exponential tilt. Pushing the
reference measure forward by the statistic preserves the parameter space and the log
partition function, and gives the law of the statistic under each tilt.

## References

* L. D. Brown, *Fundamentals of Statistical Exponential Families* (1986), Definition 1.1 and
  Theorem 1.13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ν : Measure X} {T : X → E} {η : E}

/-- The set of parameters for which the exponential weight of the statistic is integrable. -/
def naturalParameterSpace (ν : Measure X) (T : X → E) : Set E :=
  {η | Integrable (fun x ↦ exp ⟪η, T x⟫) ν}

theorem mem_naturalParameterSpace :
    η ∈ naturalParameterSpace ν T ↔ Integrable (fun x ↦ exp ⟪η, T x⟫) ν := (Iff.rfl)

/-- The logarithm of the normalizing integral of an exponential tilt. -/
def logPartition (ν : Measure X) (T : X → E) (η : E) : ℝ :=
  log (∫ x, exp ⟪η, T x⟫ ∂ν)

theorem logPartition_def (ν : Measure X) (T : X → E) (η : E) :
    logPartition ν T η = log (∫ x, exp ⟪η, T x⟫ ∂ν) := (rfl)

@[simp]
theorem logPartition_zero_measure (T : X → E) :
    logPartition (0 : Measure X) T = 0 := by
  funext η
  simp [logPartition_def]

/-- The exponential-family measure with reference measure `ν` and statistic `T`. -/
def exponentialFamilyMeasure (ν : Measure X) (T : X → E) (η : E) : Measure X :=
  ν.tilted fun x ↦ ⟪η, T x⟫

theorem exponentialFamilyMeasure_def (ν : Measure X) (T : X → E) (η : E) :
    exponentialFamilyMeasure ν T η = ν.tilted (fun x ↦ ⟪η, T x⟫) := (rfl)

/-- The integral of a real observable under an exponential-family measure is its weighted
reference integral divided by the normalizing integral. -/
theorem integral_exponentialFamilyMeasure_eq_div (g : X → ℝ) :
    (∫ x, g x ∂exponentialFamilyMeasure ν T η) =
      (∫ x, exp ⟪η, T x⟫ * g x ∂ν) / ∫ x, exp ⟪η, T x⟫ ∂ν := by
  rw [exponentialFamilyMeasure_def, integral_tilted, div_eq_inv_mul, ← integral_const_mul]
  congr with x
  simp only [smul_eq_mul]
  ring

@[simp]
theorem exponentialFamilyMeasure_zero_measure (T : X → E) (η : E) :
    exponentialFamilyMeasure (0 : Measure X) T η = 0 := by
  rw [exponentialFamilyMeasure_def, tilted_zero_measure]

/-- An exponential tilt is either a probability measure or the zero measure. -/
instance isZeroOrProbabilityMeasure_exponentialFamilyMeasure :
    IsZeroOrProbabilityMeasure (exponentialFamilyMeasure ν T η) := by
  rw [exponentialFamilyMeasure_def]
  infer_instance

/-- An exponential family is minimal when no nonzero linear functional of its statistic
is almost everywhere constant. -/
def IsMinimalExponentialFamily (ν : Measure X) (T : X → E) : Prop :=
  ∀ u : E, u ≠ 0 → ∀ c : ℝ, ¬ ∀ᵐ x ∂ν, ⟪u, T x⟫ = c

theorem isMinimalExponentialFamily_iff :
    IsMinimalExponentialFamily ν T ↔
      ∀ u : E, u ≠ 0 → ∀ c : ℝ, ¬ ∀ᵐ x ∂ν, ⟪u, T x⟫ = c := (Iff.rfl)

/-- Convex combinations of parameters with integrable weights again have integrable weights. -/
theorem convex_naturalParameterSpace (ν : Measure X) (T : X → E) :
    Convex ℝ (naturalParameterSpace ν T) := by
  intro u hu v hv a b ha hb hab
  rw [mem_naturalParameterSpace] at hu hv ⊢
  have hu' : AEStronglyMeasurable (fun x ↦ ⟪u, T x⟫) ν :=
    (aemeasurable_of_aemeasurable_exp hu.aemeasurable).aestronglyMeasurable
  have hv' : AEStronglyMeasurable (fun x ↦ ⟪v, T x⟫) ν :=
    (aemeasurable_of_aemeasurable_exp hv.aemeasurable).aestronglyMeasurable
  simp only [inner_add_left, real_inner_smul_left]
  refine ((hu.const_mul a).add (hv.const_mul b)).mono'
    (((hu'.const_mul a).add (hv'.const_mul b)).aemeasurable.exp.aestronglyMeasurable) ?_
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab

/-- On the natural parameter space a nonzero reference measure gives a probability law. -/
theorem isProbabilityMeasure_exponentialFamilyMeasure [NeZero ν]
    (hη : η ∈ naturalParameterSpace ν T) :
    IsProbabilityMeasure (exponentialFamilyMeasure ν T η) := by
  rw [exponentialFamilyMeasure_def]
  exact isProbabilityMeasure_tilted (mem_naturalParameterSpace.mp hη)

/-- The zero parameter is in the natural domain exactly for finite reference measures. -/
@[simp]
theorem zero_mem_naturalParameterSpace :
    (0 : E) ∈ naturalParameterSpace ν T ↔ IsFiniteMeasure ν := by
  simp [mem_naturalParameterSpace, integrable_const_iff]

/-- For a real statistic the natural parameter space is Mathlib's scalar domain. -/
theorem naturalParameterSpace_eq_integrableExpSet (T : X → ℝ) :
    naturalParameterSpace ν T = integrableExpSet T ν := by
  ext t
  simp [mem_naturalParameterSpace, integrableExpSet, mul_comm]

/-- For a real statistic the log partition function is Mathlib's cumulant-generating function. -/
theorem logPartition_eq_cgf (T : X → ℝ) : logPartition ν T = cgf T ν := by
  funext t
  simp [logPartition_def, cgf, mgf, mul_comm]

section Map

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- Passing to the reference law of the statistic preserves the natural parameter space. -/
@[simp]
theorem naturalParameterSpace_map (hT : AEMeasurable T ν) :
    naturalParameterSpace (ν.map T) id = naturalParameterSpace ν T := by
  ext t
  simpa [mem_naturalParameterSpace, Function.comp_def] using
    (integrable_map_measure (g := fun x : E ↦ exp ⟪t, x⟫)
      (by fun_prop) (μ := ν) hT)

/-- Passing to the reference law of the statistic preserves the log partition function. -/
@[simp]
theorem logPartition_map (hT : AEMeasurable T ν) :
    logPartition (ν.map T) id = logPartition ν T := by
  funext t
  simp only [logPartition_def, id_eq]
  rw [integral_map hT (by fun_prop)]

/-- The law of the statistic is the exponential tilt of its reference law. -/
@[simp]
theorem map_exponentialFamilyMeasure (hT : AEMeasurable T ν) :
    (exponentialFamilyMeasure ν T η).map T = exponentialFamilyMeasure (ν.map T) id η := by
  simp only [exponentialFamilyMeasure_def, id_eq]
  let U := hT.mk T
  have hTU : T =ᵐ[ν] U := hT.ae_eq_mk
  have hg : Measurable (fun x : E ↦ ⟪η, x⟫) := by fun_prop
  have htilt : ν.tilted (fun x ↦ ⟪η, T x⟫) = ν.tilted (fun x ↦ ⟪η, U x⟫) :=
    tilted_congr (hTU.fun_comp (fun x ↦ ⟪η, x⟫))
  rw [htilt, Measure.map_congr (hTU.filter_mono (tilted_absolutelyContinuous ν _).ae_le),
    Measure.map_congr hTU]
  exact ν.map_tilted hT.measurable_mk hg

end Map

end TauCeti
