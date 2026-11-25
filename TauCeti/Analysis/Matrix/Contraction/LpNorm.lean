/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import TauCeti.Analysis.Matrix.Contraction
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Contracting a field of operators with a coefficient field in `Lᵖ`

Contracting an a.e. strongly measurable field `T` of endomorphisms of `ℝⁿ` against an a.e.
strongly measurable field `a` of matrices gives an a.e. strongly measurable function
(`MeasureTheory.AEStronglyMeasurable.matrix_contraction`). If moreover `T ∈ Lᵖ` and the entries of
`a` are bounded by `Λ`, then `∑ᵢⱼ aᵢⱼ Tᵢⱼ ∈ Lᵖ` with `‖∑ᵢⱼ aᵢⱼ Tᵢⱼ‖ ≤ n² Λ ‖T‖`
(`Matrix.memLp_contraction_and_lpNorm_le`). For `T` a Hessian, this is the principal part of a
non-divergence-form operator with bounded measurable coefficients.
-/

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {a : X → Matrix (Fin n) (Fin n) ℝ}
  {T : X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}

/-- Contracting an a.e. strongly measurable field of operators on `ℝⁿ` against an a.e. strongly
measurable coefficient field gives an a.e. strongly measurable function. -/
theorem MeasureTheory.AEStronglyMeasurable.matrix_contraction (ha : AEStronglyMeasurable a μ)
    (hT : AEStronglyMeasurable T μ) :
    AEStronglyMeasurable (fun x => Matrix.contraction (a x) (T x)) μ := by
  simp only [Matrix.contraction_apply]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  exact ((continuous_id.matrix_elem i j).comp_aestronglyMeasurable ha).mul
    (((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i 1)).continuous
      |>.comp_aestronglyMeasurable hT).inner aestronglyMeasurable_const)

/-- Contracting an `Lᵖ` field of operators on `ℝⁿ` against a coefficient field with entries
bounded by `Λ` gives an `Lᵖ` function, with `‖∑ᵢⱼ aᵢⱼ Tᵢⱼ‖ ≤ n² Λ ‖T‖`. -/
theorem Matrix.memLp_contraction_and_lpNorm_le {p : ℝ≥0∞} {Λ : ℝ}
    (ha : AEStronglyMeasurable a μ) (haΛ : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ Λ) (hT : MemLp T p μ) :
    MemLp (fun x => Matrix.contraction (a x) (T x)) p μ ∧
      lpNorm (fun x => Matrix.contraction (a x) (T x)) p μ ≤ n ^ 2 * Λ * lpNorm T p μ := by
  have hmeas := ha.matrix_contraction hT.aestronglyMeasurable
  have hle : ∀ᵐ x ∂μ, ‖Matrix.contraction (a x) (T x)‖ ≤ n ^ 2 * Λ * ‖T x‖ :=
    haΛ.mono fun x hx => by
      rw [Real.norm_eq_abs]
      exact Matrix.abs_contraction_le hx _
  exact ⟨hT.of_le_mul hmeas hle, lpNorm_le_mul_lpNorm_of_ae_le_mul hmeas hT hle⟩
