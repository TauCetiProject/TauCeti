/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Smoothness of the curvature tensor

The pointwise curvature tensor of a smooth connection is a smooth section of the
iterated hom bundle. We express the existing algebraic `curvatureTensor` using
continuous linear maps, so Mathlib's hom-bundle topology and smooth structure apply.
The application equation identifies the two tensors, without any new choice of extensions.

This smooth tensor-field packaging makes curvature available for subsequent geometric
constructions, including Ricci and sectional curvature, while retaining the original
pointwise tensor as its evaluation. It requires neither metric compatibility nor
vanishing torsion.

Evaluating curvature on tangent and bundle lifts of class `C^n` (`n ≤ ∞`) along a
map gives a bundle lift of the same class, including within arbitrary parameter sets.
This permits curvature evaluation along curves, immersions, and variation families
without extending the fields to the ambient manifold. No fibre norms are required.

The curvature convention follows J. M. Lee, *Introduction to Riemannian Manifolds*,
2nd ed., Springer GTM 176 (2018), Chapter 7, pp. 196–198, as in `curvatureTensor`.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- The curvature tensor as an iterated continuous linear map, in the fibre of the
iterated hom bundle. Its underlying trilinear map is `curvatureTensor`. -/
def curvatureTensorCLM (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x →L[ℝ] V x :=
  haveI := VectorBundle.finiteDimensional ℝ F V x
  haveI := FiberBundle.t2Space F V x
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((cov.curvatureTensor x).compr₂ LinearMap.toContinuousLinearMap.toLinearMap))

/-- The continuous-linear curvature tensor evaluates to the original pointwise tensor. -/
@[simp]
theorem curvatureTensorCLM_apply (x : M) (u v : TangentSpace I x) (w : V x) :
    cov.curvatureTensorCLM x u v w = cov.curvatureTensor x u v w := by
  simp only [curvatureTensorCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearMap.compr₂_apply]

/-- The curvature tensor of a smooth connection is a smooth section of the iterated
hom bundle. This requires neither metric compatibility nor vanishing torsion. -/
theorem contMDiff_curvatureTensorCLM :
    -- Cache the standard model instances while elaborating the nested operator spaces.
    let _ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) x
        (cov.curvatureTensorCLM x)) := by
  intro normEnd spaceEnd
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro σ hσ
  simpa only [curvatureTensorCLM_apply, curvatureTensor_apply cov _ hX hY hσ] using
    cov.contMDiff_curvatureOperator hX hY hσ

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {f : P → M} {X Y : Π p : P, TangentSpace I (f p)} {σ : Π p : P, V (f p)}
  {s : Set P} {p : P} {n : ℕ∞ω}

/-- For a smooth connection on a finite-rank smooth vector bundle, evaluating curvature
on tangent and bundle lifts of class `C^n` (`n ≤ ∞`) gives a bundle lift of class `C^n`
within `s` at `p`. No fibre norms, metric compatibility, or torsion assumption are needed. -/
theorem contMDiffWithinAt_curvatureTensor_apply
    (hX : ContMDiffWithinAt I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (X q)) s p)
    (hY : ContMDiffWithinAt I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (Y q)) s p)
    (hσ : ContMDiffWithinAt I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (σ q)) s p) (hn : n ≤ ∞) :
    ContMDiffWithinAt I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q)
        (cov.curvatureTensor (f q) (X q) (Y q) (σ q))) s p := by
  let _ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
  have hf : ContMDiffWithinAt I' I n f s p := (contMDiffWithinAt_totalSpace_iff.mp hσ).1
  have hR := (cov.contMDiff_curvatureTensorCLM.of_le hn).contMDiffAt.comp_contMDiffWithinAt
    p hf
  simpa only [curvatureTensorCLM_apply] using
    ((hR.clm_bundle_apply hX).clm_bundle_apply hY).clm_bundle_apply hσ

/-- Evaluating the curvature of a smooth connection on tangent and bundle lifts of class
`C^n` (`n ≤ ∞`) gives a bundle lift of class `C^n` at `p`. -/
theorem contMDiffAt_curvatureTensor_apply
    (hX : ContMDiffAt I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (X q)) p)
    (hY : ContMDiffAt I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (Y q)) p)
    (hσ : ContMDiffAt I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (σ q)) p) (hn : n ≤ ∞) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q)
        (cov.curvatureTensor (f q) (X q) (Y q) (σ q))) p :=
  cov.contMDiffWithinAt_curvatureTensor_apply hX hY hσ hn

/-- Evaluating the curvature of a smooth connection on tangent and bundle lifts of class
`C^n` (`n ≤ ∞`) gives a bundle lift of class `C^n` on `s`. -/
theorem contMDiffOn_curvatureTensor_apply
    (hX : ContMDiffOn I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (X q)) s)
    (hY : ContMDiffOn I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (Y q)) s)
    (hσ : ContMDiffOn I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (σ q)) s) (hn : n ≤ ∞) :
    ContMDiffOn I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q)
        (cov.curvatureTensor (f q) (X q) (Y q) (σ q))) s :=
  fun q hq ↦ cov.contMDiffWithinAt_curvatureTensor_apply (hX q hq) (hY q hq) (hσ q hq) hn

/-- Evaluating the curvature of a smooth connection on tangent and bundle lifts of class
`C^n` (`n ≤ ∞`) gives a bundle lift of class `C^n` everywhere. -/
theorem contMDiff_curvatureTensor_apply
    (hX : ContMDiff I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (X q)))
    (hY : ContMDiff I' I.tangent n
      (fun q ↦ TotalSpace.mk' E (f q) (Y q)))
    (hσ : ContMDiff I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (σ q))) (hn : n ≤ ∞) :
    ContMDiff I' (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q)
        (cov.curvatureTensor (f q) (X q) (Y q) (σ q))) :=
  fun q ↦ cov.contMDiffAt_curvatureTensor_apply (hX q) (hY q) (hσ q) hn

end CovariantDerivative
