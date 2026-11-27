/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.InnerProductSpace.Gram.VolumeDensity
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
`sqrt_det_gram_eq_abs_det_mul_chartVolumeDensity` identifies the Gram density of an arbitrary
linear map into a tangent space with its coordinate determinant times chart density. This is
the common algebraic step in the Riemannian Jacobian and isometry change-of-variables formulas.

This file supplies the local density, its transition rule, and its derivative
`dρ = ρ trace P` for a metric-compatible connection, where `P` is the matrix of the
connection form in the chart frame; it does not assemble a measure on the manifold.

When the model space is `EuclideanSpace ℝ (Fin m)`, `TauCeti.stdChartVolumeDensity` gives the
standard-basis density in the frame of `EuclideanSpace.basisFun`, used for coordinate integrals
against Lebesgue measure, together with `TauCeti.stdChartVolumeDensity_eq_sqrt_det_gram` and
`TauCeti.contMDiffOn_stdChartVolumeDensity`.

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

private theorem chartVolumeDensity_eq_metricVolumeDensity (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartVolumeDensity (I := I) α x =
      ((trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hx).metricVolumeDensity
        (innerSL ℝ) := by
  rw [chartVolumeDensity_def, Module.Basis.metricVolumeDensity_innerSL_eq_sqrt_det_gram]
  congr 2
  ext i j
  simp only [chartGramMatrix_apply, chartLocalFrame_apply_of_mem_chart_source α
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hx), Matrix.gram_apply]

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
  rw [chartVolumeDensity_eq_metricVolumeDensity α hα,
    chartVolumeDensity_eq_metricVolumeDensity β hβ]
  exact Module.Basis.metricVolumeDensity_change_basis _ _ (innerSL ℝ)

/-- The Gram density of a linear map into a tangent space is the absolute determinant of its
chart-coordinate map times chart volume density. The equivalence `C` matches the coordinate
bases, so the formula also applies to independent model vector spaces. -/
theorem sqrt_det_gram_eq_abs_det_mul_chartVolumeDensity
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {C : F ≃L[ℝ] E} {σ : Fin (Module.finrank ℝ E) ≃ Fin (Module.finrank ℝ F)}
    (hC : (Module.finBasis ℝ F).map C.toLinearEquiv = (Module.finBasis ℝ E).reindex σ)
    {α x : M} (hx : x ∈ (chartAt H α).source) (D : F →L[ℝ] TangentSpace I x) :
    Real.sqrt (Matrix.gram ℝ (fun i ↦ D (Module.finBasis ℝ F i))).det =
      |(C.symm.toContinuousLinearMap ∘L mfderiv I 𝓘(ℝ, E) (extChartAt I α) x ∘L D).det| *
        chartVolumeDensity (I := I) α x := by
  have hα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  let b := Module.finBasis ℝ F
  let bα := (trivializationAt E (TangentSpace I) α).basisAt (b.map C.toLinearEquiv) hα
  let L := C.symm.toContinuousLinearMap ∘L mfderiv I 𝓘(ℝ, E) (extChartAt I α) x ∘L D
  have hmat : LinearMap.toMatrix b bα D.toLinearMap =
      LinearMap.toMatrix b b L.toLinearMap := by
    ext i j
    simp only [LinearMap.toMatrix_apply, bα, Trivialization.basisAt, Module.Basis.map_repr,
      LinearEquiv.trans_apply, LinearEquiv.symm_symm, Trivialization.linearEquivAt_apply]
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hα,
      TangentBundle.continuousLinearMapAt_trivializationAt hx]
    -- The tangent space of the self-model is definitionally the model space. Read the
    -- remaining chart derivative as an `E`-valued map before evaluating composition.
    change (b.repr (C.symm (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x (D (b j))))) i =
      (b.repr ((C.symm.toContinuousLinearMap ∘L
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x : TangentSpace I x →L[ℝ] E) ∘L D) (b j))) i
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    -- The inner composition has the self-model tangent space as codomain; its evaluation
    -- reduces to the ordinary composition once this definitional identification is made.
    rfl
  have hbα : bα = (trivializationAt E (TangentSpace I) α).basisAt
      ((Module.finBasis ℝ E).reindex σ) hα := congrArg
    (fun c ↦ (trivializationAt E (TangentSpace I) α).basisAt c hα) hC
  have htarget : (LinearMap.BilinForm.toMatrix bα (innerₗ (TangentSpace I x))).det =
      (chartGramMatrix (I := I) α x).det := by
    have hgram : LinearMap.BilinForm.toMatrix bα (innerₗ (TangentSpace I x)) =
        Matrix.gram ℝ bα := by
      ext i j
      simp only [LinearMap.BilinForm.toMatrix_apply, innerₗ_apply_apply, Matrix.gram_apply]
    rw [hgram, hbα, gram_basisAt_finBasis_reindex, Matrix.det_submatrix_equiv_self]
  have hgram : Matrix.gram ℝ (fun i ↦ D (b i)) = LinearMap.BilinForm.toMatrix b
      (LinearMap.BilinForm.comp (innerₗ (TangentSpace I x)) D.toLinearMap D.toLinearMap) := by
    ext i j
    simp [Matrix.gram_apply, LinearMap.BilinForm.toMatrix_apply]
  have hdet : (Matrix.gram ℝ (fun i ↦ D (b i))).det =
      L.det ^ 2 * (chartGramMatrix (I := I) α x).det := by
    rw [hgram, LinearMap.BilinForm.toMatrix_comp bα b, hmat]
    simp only [Matrix.det_mul, Matrix.det_transpose, htarget, LinearMap.det_toMatrix,
      ContinuousLinearMap.det]
    ring
  rw [hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, chartVolumeDensity_def]

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

section StdChart

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Riemannian volume density in the chart frame induced by `EuclideanSpace.basisFun`. -/
def stdChartVolumeDensity (α x : M) : ℝ :=
  EuclideanSpace.finBasisAddHaarFactor m * chartVolumeDensity (I := I) α x

/-- Defining relation expressing `TauCeti.stdChartVolumeDensity` as a rescaling of
`TauCeti.chartVolumeDensity`. -/
theorem stdChartVolumeDensity_def (α x : M) :
    stdChartVolumeDensity (I := I) α x =
      EuclideanSpace.finBasisAddHaarFactor m * chartVolumeDensity (I := I) α x := (rfl)

/-- On the trivialization base set, `stdChartVolumeDensity` equals the square root of the Gram
determinant of the standard Euclidean basis chart frame. -/
theorem stdChartVolumeDensity_eq_sqrt_det_gram (α : M) {y : M}
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α).baseSet) :
    stdChartVolumeDensity (I := I) α y =
      √(Matrix.gram ℝ ((trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α).basisAt
        (EuclideanSpace.basisFun (Fin m) ℝ).toBasis hy)).det := by
  set e := trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace I) α
  set stdB := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  set finσ := finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m))
  set finB := Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))
  set B_std := e.basisAt stdB hy
  set B_fin := e.basisAt (finB.reindex finσ) hy
  have hmat : B_std.toMatrix B_fin = stdB.toMatrix (finB.reindex finσ) := by
    dsimp only [B_std, B_fin, Bundle.Trivialization.basisAt]
    rw [Module.Basis.toMatrix_map, Module.Basis.coe_map]
    congr 1
    ext k
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
  have hreindex : B_fin = (e.basisAt finB hy).reindex finσ := by
    ext i
    simp [B_fin, Bundle.Trivialization.basisAt]
  have hchart : chartVolumeDensity (I := I) α y = B_fin.metricVolumeDensity (innerSL ℝ) := by
    rw [chartVolumeDensity_eq_metricVolumeDensity α hy, hreindex,
      Module.Basis.metricVolumeDensity_reindex]
  have hcov := Module.Basis.metricVolumeDensity_change_basis B_std B_fin (innerSL ℝ)
  rw [hmat, ← Module.Basis.det_apply, ← hchart] at hcov
  rw [stdChartVolumeDensity_def, hcov, B_std.metricVolumeDensity_innerSL_eq_sqrt_det_gram,
    EuclideanSpace.finBasisAddHaarFactor_def,
    inv_mul_cancel_left₀ (abs_ne_zero.2 (stdB.isUnit_det _).ne_zero)]

/-- A `C^n` metric has a `C^n` standard-frame volume density on every chart source of a `C^(n+1)`
manifold. -/
theorem contMDiffOn_stdChartVolumeDensity {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n (EuclideanSpace ℝ (Fin m))
      (fun x : M ↦ TangentSpace I x)] (α : M) :
    ContMDiffOn I 𝓘(ℝ) n (stdChartVolumeDensity (I := I) α) (chartAt H α).source :=
  contMDiffOn_const.mul (by simpa only [TangentBundle.trivializationAt_baseSet] using
    contMDiffOn_chartVolumeDensity (I := I) (n := n) α)

end StdChart

end TauCeti
