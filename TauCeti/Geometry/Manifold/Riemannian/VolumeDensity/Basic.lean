/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Riemannian volume density in a chart

The local Riemannian volume density is the positive square root of the determinant of
the metric Gram matrix. Under a `C^n` metric on a `C^(n+1)` manifold, it is `C^n` on
its chart and transforms by the absolute determinant of a change of frame. Thus it
applies without an orientation, including
on manifolds with boundary.

The frame is `Riemannian.Tensor.chartLocalFrame`, based on `Module.finBasis ℝ E`.
Accordingly the coordinate measure to be weighted by this density is the Haar measure
normalized by that basis. No orthonormality of the model-space basis is assumed.
This file supplies the local density, its transition rule, and its derivative
`dρ = ρ trace P` for a metric-compatible connection, where `P` is the matrix of the
connection form in the chart frame; it does not assemble a measure on the manifold.

The convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Springer GTM 176 (2018), Propositions 2.41 and 2.44.
-/

public section

open Bundle FiberBundle Riemannian.Tensor
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Riemannian volume density in the frame of the chart centred at `α`, relative to
the model-space basis `Module.finBasis ℝ E`. -/
def chartVolumeDensity (α x : M) : ℝ :=
  Real.sqrt (chartGramMatrix (I := I) α x).det

/-- The coordinate formula for Riemannian volume density. -/
theorem chartVolumeDensity_def (α x : M) :
    chartVolumeDensity (I := I) α x = Real.sqrt (chartGramMatrix (I := I) α x).det :=
  (rfl)

/-- The chart density is nonnegative, including at its values outside the chart. -/
theorem chartVolumeDensity_nonneg (α x : M) : 0 ≤ chartVolumeDensity (I := I) α x :=
  Real.sqrt_nonneg _

/-- The chart density is strictly positive on the chart domain. -/
theorem chartVolumeDensity_pos (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    0 < chartVolumeDensity (I := I) α x :=
  Real.sqrt_pos.mpr (chartGramMatrix_det_pos α hx)

/-- Squaring the density recovers the Gram determinant, including outside the chart domain. -/
@[simp]
theorem chartVolumeDensity_sq (α x : M) :
    chartVolumeDensity (I := I) α x ^ 2 = (chartGramMatrix (I := I) α x).det := by
  rw [chartVolumeDensity_def]
  exact Real.sq_sqrt (chartGramMatrix_det_nonneg α x)

/-- A `C^n` metric has a `C^n` volume density in every chart of a `C^(n+1)` manifold. -/
theorem contMDiffOn_chartVolumeDensity {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] (α : M) :
    ContMDiffOn I 𝓘(ℝ) n (chartVolumeDensity (I := I) α)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  exact (Real.contDiffAt_sqrt (chartGramMatrix_det_pos α hx).ne').comp_contMDiffWithinAt
    (f := fun y : M ↦ (chartGramMatrix (I := I) α y).det)
    (contMDiffOn_chartGramMatrix_det α x hx)

/-- Changing from the frame at `β` to the frame at `α` multiplies the volume density by
the absolute determinant of the frame-coordinate matrix. The absolute value makes
the rule valid for orientation-reversing transitions as well. -/
theorem chartVolumeDensity_changeFrame (α β : M) {x : M}
    (hα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hβ : x ∈ (trivializationAt E (TangentSpace I) β).baseSet) :
    chartVolumeDensity (I := I) α x =
      |(((trivializationAt E (TangentSpace I) β).basisAt (Module.finBasis ℝ E) hβ).toMatrix
        ((trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hα)).det| *
        chartVolumeDensity (I := I) β x := by
  let bα := (trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hα
  let bβ := (trivializationAt E (TangentSpace I) β).basisAt (Module.finBasis ℝ E) hβ
  have hdet : (chartGramMatrix (I := I) α x).det =
      (bβ.toMatrix bα).det ^ 2 * (chartGramMatrix (I := I) β x).det := by
    rw [chartGramMatrix_eq_toMatrix α hα, chartGramMatrix_eq_toMatrix β hβ,
      ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix bβ bα (innerₗ (TangentSpace I x))]
    simp only [Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [chartVolumeDensity_def, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    chartVolumeDensity_def]

section Derivative

variable [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The derivative of the volume density.** For a connection `∇` compatible with the metric,
the derivative along `v` of the chart volume density `ρ = √det G` at `α` is `ρ` times the trace
`∑ₖ (∇ᵥ eₖ)ᵏ` of the connection form in the chart frame; that is, `d log ρ` is this trace. -/
theorem mvfderiv_chartVolumeDensity
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (α : M) {y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I y) :
    mvfderiv I (chartVolumeDensity (I := I) α) y v =
      chartVolumeDensity (I := I) α y *
        ∑ k, (trivializationAt E (TangentSpace I) α).localFrameCoeff I (Module.finBasis ℝ E) k y
          (cov (chartLocalFrame (I := I) α k) y v) := by
  have : IsManifold I (1 + 1) M := by norm_num; infer_instance
  have hdet : MDifferentiableAt I 𝓘(ℝ) (fun z ↦ (chartGramMatrix (I := I) α z).det) y :=
    ((contMDiffOn_chartGramMatrix_det (n := 1) α).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hy)).mdifferentiableAt
        one_ne_zero
  have hsqrt := Real.hasDerivAt_sqrt (chartGramMatrix_det_pos α hy).ne'
  -- Differentiate `ρ = √det G` by the chain rule.
  have hcomp := mvfderiv_comp_apply_of_differentiableAt (φ := Real.sqrt)
    (g := fun z ↦ (chartGramMatrix (I := I) α z).det) hsqrt.differentiableAt hdet v
  rw [Function.comp_def, hsqrt.hasFDerivAt.fderiv, mvfderiv_det_chartGramMatrix hcov α hy v,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    show (fun z ↦ √(chartGramMatrix (I := I) α z).det) = chartVolumeDensity (I := I) α from
      funext fun z ↦ (chartVolumeDensity_def α z).symm, ← chartVolumeDensity_def,
    ← chartVolumeDensity_sq] at hcomp
  rw [hcomp]
  have hρ := (chartVolumeDensity_pos (I := I) α hy).ne'
  field_simp

end Derivative

end TauCeti
