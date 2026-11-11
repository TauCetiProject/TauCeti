/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness

/-!
# Regularity of sectional curvature

Sectional curvature varies smoothly with an independent pair of tangent vectors, including
when their base point varies. The statements allow a parameter manifold and relative
regularity on a parameter set, so they apply both to local frames and to families of planes.
Independence is needed only at the point in the pointwise statements. No regularity is
asserted for the quotient's junk values at dependent pairs.

The proof uses the native smooth curvature tensor `curvatureTensorCLM`, smooth evaluation
in Hom bundles, and the Gram determinant. No frame or Grassmannian carrier is chosen.
The convention and quotient follow J. M. Lee, *Introduction to Riemannian Manifolds*,
second edition, Chapter 8.
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold Matrix

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]
  (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  {P : Type*} [TopologicalSpace P] [ChartedSpace K P]
  {n : ℕ∞} [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
  {f : P → M} {u v : (p : P) → TangentSpace I (f p)} {s : Set P} {p : P}

/-- Sectional curvature of a `C^n` family of tangent pairs is `C^n` within a set at an
independent pair. Both the vectors and their common base point may vary. -/
theorem contMDiffWithinAt_sectionalCurvature
    (hu : ContMDiffWithinAt J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (u q)) s p)
    (hv : ContMDiffWithinAt J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (v q)) s p)
    (huv : LinearIndependent ℝ ![u p, v p]) :
    ContMDiffWithinAt J 𝓘(ℝ) n (fun q ↦ cov.sectionalCurvature hcov (f q) (u q) (v q))
      s p := by
  -- Cache the operator-space instances before elaborating the iterated Hom bundle.
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
  have hf : ContMDiffWithinAt J I n f s p := (contMDiffWithinAt_totalSpace.mp hu).1
  have hR := ((cov.contMDiff_curvatureTensorCLM (V := fun x : M ↦ TangentSpace I x)
    (fiberNorm := fun x ↦ inferInstance)).of_le (by simp : (n : ℕ∞ω) ≤ ∞)).contMDiffAt
      |>.comp_contMDiffWithinAt p hf
  have hRuvv := ((hR.clm_bundle_apply hu).clm_bundle_apply hv).clm_bundle_apply hv
  have hnum := ContMDiffWithinAt.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) hRuvv hu
  have huu := ContMDiffWithinAt.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) hu hu
  have hvv := ContMDiffWithinAt.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) hv hv
  have huv' := ContMDiffWithinAt.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) hu hv
  have hden := (huu.mul hvv).sub (huv'.pow 2)
  have hne : inner ℝ (u p) (u p) * inner ℝ (v p) (v p) - inner ℝ (u p) (v p) ^ 2 ≠ 0 := by
    rw [← Matrix.real_det_gram_fin_two]
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr huv
  convert hnum.div₀ hden hne using 1
  ext q
  simp only [sectionalCurvature_apply, curvatureTensorCLM_apply,
    Matrix.real_det_gram_fin_two, Pi.div_apply, Pi.mul_apply]

/-- Sectional curvature is `C^n` at an independent pair in a `C^n` family. -/
theorem contMDiffAt_sectionalCurvature
    (hu : ContMDiffAt J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (u q)) p)
    (hv : ContMDiffAt J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (v q)) p)
    (huv : LinearIndependent ℝ ![u p, v p]) :
    ContMDiffAt J 𝓘(ℝ) n (fun q ↦ cov.sectionalCurvature hcov (f q) (u q) (v q)) p :=
  cov.contMDiffWithinAt_sectionalCurvature hcov hu hv huv

/-- Sectional curvature is `C^n` on a parameter set where a `C^n` family of tangent pairs
is independent. No openness or unique-derivative hypothesis on the set is required. -/
theorem contMDiffOn_sectionalCurvature
    (hu : ContMDiffOn J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (u q)) s)
    (hv : ContMDiffOn J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (v q)) s)
    (huv : ∀ q ∈ s, LinearIndependent ℝ ![u q, v q]) :
    ContMDiffOn J 𝓘(ℝ) n (fun q ↦ cov.sectionalCurvature hcov (f q) (u q) (v q)) s :=
  fun q hq ↦ cov.contMDiffWithinAt_sectionalCurvature hcov (hu q hq) (hv q hq) (huv q hq)

/-- Sectional curvature of an everywhere independent `C^n` family of tangent pairs is `C^n`.
The family may have a varying base point. -/
theorem contMDiff_sectionalCurvature
    (hu : ContMDiff J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (u q)))
    (hv : ContMDiff J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (v q)))
    (huv : ∀ q, LinearIndependent ℝ ![u q, v q]) :
    ContMDiff J 𝓘(ℝ) n (fun q ↦ cov.sectionalCurvature hcov (f q) (u q) (v q)) :=
  fun q ↦ cov.contMDiffAt_sectionalCurvature hcov (hu q) (hv q) (huv q)

end CovariantDerivative
