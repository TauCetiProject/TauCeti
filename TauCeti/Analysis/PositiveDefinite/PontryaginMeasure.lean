/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.AdditiveCharacter
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

private theorem continuous_character_eval (g : G) :
    Continuous (fun χ : PontryaginDual (Multiplicative G) =>
      (χ (Multiplicative.ofAdd g) : ℂ)) := by
  have h : Continuous (fun χ : (Multiplicative G →ₜ* Circle) =>
      (χ (Multiplicative.ofAdd g) : Circle)) :=
    continuous_eval_const (Multiplicative.ofAdd g)
  exact (LipschitzWith.subtype_val (Submonoid.unitSphere ℂ).carrier).continuous.comp h

variable [MeasurableSpace (PontryaginDual (Multiplicative G))]

/-- The Fourier–Stieltjes transform of a measure on the Pontryagin dual of an
additive group. -/
noncomputable def pontryaginMeasureTransform
    (μ : Measure (PontryaginDual (Multiplicative G))) (g : G) : ℂ :=
  ∫ χ, (χ (Multiplicative.ofAdd g) : ℂ) ∂μ

/-- At the identity, the transform records the total mass of the measure. -/
@[simp]
theorem pontryaginMeasureTransform_zero
    (μ : Measure (PontryaginDual (Multiplicative G))) :
    pontryaginMeasureTransform μ 0 = (μ.real Set.univ : ℂ) := by
  simp [pontryaginMeasureTransform]

variable [OpensMeasurableSpace (PontryaginDual (Multiplicative G))]

private theorem integrable_character_eval
    (μ : Measure (PontryaginDual (Multiplicative G))) [IsFiniteMeasure μ] (g : G) :
    Integrable (fun χ : PontryaginDual (Multiplicative G) =>
      (χ (Multiplicative.ofAdd g) : ℂ)) μ :=
  (integrable_const (1 : ℝ)).mono'
    (continuous_character_eval g).aestronglyMeasurable
    (.of_forall fun χ => by simp)

/-- The transform of a finite positive measure on the dual is positive definite. -/
theorem isPositiveDefiniteSub_pontryaginMeasureTransform
    (μ : Measure (PontryaginDual (Multiplicative G))) [IsFiniteMeasure μ] :
    IsPositiveDefiniteSub (pontryaginMeasureTransform μ) := by
  refine isPositiveDefiniteSub_iff_forall_sum_nonneg.mpr ?_
  intro n c v
  have hint (i j : Fin n) :
      Integrable (fun χ : PontryaginDual (Multiplicative G) =>
        (c i * conj (c j)) * (χ (Multiplicative.ofAdd (v i - v j)) : ℂ)) μ :=
    (integrable_character_eval μ (v i - v j)).const_mul _
  have hsum :
      (∫ χ, ∑ i : Fin n, ∑ j : Fin n,
        (c i * conj (c j)) * (χ (Multiplicative.ofAdd (v i - v j)) : ℂ) ∂μ) =
      ∑ i : Fin n, ∑ j : Fin n,
        (c i * conj (c j)) * pontryaginMeasureTransform μ (v i - v j) := by
    rw [integral_finsetSum]
    · congr 1
      ext i
      rw [integral_finsetSum]
      · simp only [integral_const_mul, pontryaginMeasureTransform]
      · intro j _
        exact hint i j
    · intro i _
      exact integrable_finsetSum _ (fun j _ => hint i j)
  rw [← hsum]
  exact integral_nonneg fun χ => (isPositiveDefiniteSub_iff_forall_sum_nonneg.mp
    (PontryaginDual.isPositiveDefiniteSub χ).2) n c v

/-- The absolute value of a measure transform is bounded by the measure's total mass. -/
theorem norm_pontryaginMeasureTransform_le
    (μ : Measure (PontryaginDual (Multiplicative G))) [IsFiniteMeasure μ] (g : G) :
    ‖pontryaginMeasureTransform μ g‖ ≤ μ.real Set.univ := by
  simpa using
    (isPositiveDefiniteSub_pontryaginMeasureTransform μ).norm_apply_le_map_zero_re g

end TauCeti
