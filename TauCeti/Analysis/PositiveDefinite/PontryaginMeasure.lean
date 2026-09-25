/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.AdditiveCharacter
public import TauCeti.Analysis.Fourier.PontryaginMeasure

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
  [OpensMeasurableSpace (PontryaginDual (Multiplicative G))]

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
