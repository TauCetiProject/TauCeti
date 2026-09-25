/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.PontryaginDualEval
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Positive-definite transforms of measures on a Pontryagin dual

Integration of characters against a finite positive measure gives a
positive-definite function on an additive topological group. This is the positivity part
of the measure-to-function direction of Bochner representation on locally compact abelian groups.
-/

public section

open MeasureTheory ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]

variable [MeasurableSpace (PontryaginDual (Multiplicative G))]

/-- The Fourier–Stieltjes transform of a finite measure on the Pontryagin dual of an
additive group. -/
noncomputable def _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) (g : G) : ℂ :=
  ∫ χ, (χ (Multiplicative.ofAdd g) : ℂ) ∂μ.toMeasure

/-- The defining integral of the Fourier–Stieltjes transform. -/
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_apply
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) (g : G) :
    μ.pontryaginMeasureTransform g =
      ∫ χ, (χ (Multiplicative.ofAdd g) : ℂ) ∂μ.toMeasure := by
  simp only [FiniteMeasure.pontryaginMeasureTransform]

/-- At the identity, the transform records the total mass of the measure. -/
@[simp]
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_zero
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    μ.pontryaginMeasureTransform 0 = (μ.toMeasure.real Set.univ : ℂ) := by
  simp [FiniteMeasure.pontryaginMeasureTransform]

/-- The transform of the zero measure vanishes. -/
@[simp]
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_zero_measure :
    (0 : FiniteMeasure (PontryaginDual (Multiplicative G))).pontryaginMeasureTransform = 0 := by
  funext g
  simp [FiniteMeasure.pontryaginMeasureTransform]

/-- The transform commutes with nonnegative scalar multiplication of finite measures. -/
@[simp]
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_smul
    (c : NNReal) (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    (c • μ).pontryaginMeasureTransform = c • μ.pontryaginMeasureTransform := by
  funext g
  simp [FiniteMeasure.pontryaginMeasureTransform]

variable [OpensMeasurableSpace (PontryaginDual (Multiplicative G))]

/-- The transform commutes with addition of finite measures. -/
@[simp]
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_add
    (μ ν : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    (μ + ν).pontryaginMeasureTransform =
      μ.pontryaginMeasureTransform + ν.pontryaginMeasureTransform := by
  funext g
  rw [FiniteMeasure.pontryaginMeasureTransform_apply, FiniteMeasure.toMeasure_add,
    integral_add_measure (PontryaginDual.integrable_eval_ofAdd (μ := μ.toMeasure) g)
      (PontryaginDual.integrable_eval_ofAdd (μ := ν.toMeasure) g)]
  rfl

/-- The transform of a finite positive measure on the dual is positive definite. -/
theorem _root_.MeasureTheory.FiniteMeasure.isPositiveDefiniteSub_pontryaginMeasureTransform
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    IsPositiveDefiniteSub μ.pontryaginMeasureTransform := by
  refine isPositiveDefiniteSub_iff_forall_sum_nonneg.mpr ?_
  intro n c v
  have hint (i j : Fin n) :
      Integrable (fun χ : PontryaginDual (Multiplicative G) =>
        (c i * conj (c j)) * (χ (Multiplicative.ofAdd (v i - v j)) : ℂ)) μ.toMeasure :=
    (PontryaginDual.integrable_eval_ofAdd (μ := μ.toMeasure) (v i - v j)).const_mul _
  have hsum :
      (∫ χ, ∑ i : Fin n, ∑ j : Fin n,
        (c i * conj (c j)) * (χ (Multiplicative.ofAdd (v i - v j)) : ℂ) ∂μ.toMeasure) =
      ∑ i : Fin n, ∑ j : Fin n,
        (c i * conj (c j)) * μ.pontryaginMeasureTransform (v i - v j) := by
    rw [integral_finsetSum]
    · congr 1
      ext i
      rw [integral_finsetSum]
      · simp only [integral_const_mul, FiniteMeasure.pontryaginMeasureTransform]
      · intro j _
        exact hint i j
    · intro i _
      exact integrable_finsetSum _ (fun j _ => hint i j)
  rw [← hsum]
  exact integral_nonneg fun χ => (isPositiveDefiniteSub_iff_forall_sum_nonneg.mp
    (PontryaginDual.isPositiveDefiniteSub χ).2) n c v

/-- The absolute value of a measure transform is bounded by the measure's total mass. -/
theorem _root_.MeasureTheory.FiniteMeasure.norm_pontryaginMeasureTransform_le
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) (g : G) :
    ‖μ.pontryaginMeasureTransform g‖ ≤ μ.toMeasure.real Set.univ := by
  simpa using
    μ.isPositiveDefiniteSub_pontryaginMeasureTransform.norm_apply_le_map_zero_re g

end TauCeti
