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
vanishing torsion. The bundle is any smooth finite-rank real vector bundle, with no
fibre norms required. Evaluating the tensor on three `C^n` section lifts preserves their
regularity for `n ≤ ∞`, over an arbitrary parameter manifold; pointwise, within-set and global
forms are provided.

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
  haveI := FiberBundle.t2Space F V x
  haveI := VectorBundle.finiteDimensional ℝ F V x
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

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  {P : Type*} [TopologicalSpace P] [ChartedSpace K P]
  {f : P → M} {U W : ∀ p, TangentSpace I (f p)} {σ : ∀ p, V (f p)}
  {n : ℕ∞ω}

/-- Curvature evaluated on three section lifts of class `C^n` is `C^n` within a set at a
parameter, for `n ≤ ∞`. The parameter manifold is arbitrary and the bundle is any smooth
finite-rank real vector bundle, without a metric or fibre norms. -/
theorem contMDiffWithinAt_curvatureTensor {s : Set P} {p : P} (hn : n ≤ ∞)
    (hU : ContMDiffWithinAt J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (U q)) s p)
    (hW : ContMDiffWithinAt J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (W q)) s p)
    (hσ : ContMDiffWithinAt J (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (σ q)) s p) :
    ContMDiffWithinAt J (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (cov.curvatureTensor (f q) (U q) (W q) (σ q))) s p := by
  -- Cache the iterated hom-fibre instances while elaborating bundle applications.
  let _ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] F) := inferInstance
  have hf : ContMDiffWithinAt J I n f s p :=
    (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := n)).contMDiffAt
      |>.comp_contMDiffWithinAt p hU
  have hR := ((cov.contMDiff_curvatureTensorCLM.of_le hn).contMDiffAt
    (x := f p)).comp_contMDiffWithinAt p hf
  simpa only [curvatureTensorCLM_apply] using
    ((hR.clm_bundle_apply hU).clm_bundle_apply hW).clm_bundle_apply hσ

/-- Curvature evaluated on `C^n` section lifts is `C^n` at a parameter, for `n ≤ ∞`. -/
theorem contMDiffAt_curvatureTensor {p : P} (hn : n ≤ ∞)
    (hU : ContMDiffAt J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (U q)) p)
    (hW : ContMDiffAt J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (W q)) p)
    (hσ : ContMDiffAt J (I.prod 𝓘(ℝ, F)) n (fun q ↦ TotalSpace.mk' F (f q) (σ q)) p) :
    ContMDiffAt J (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (cov.curvatureTensor (f q) (U q) (W q) (σ q))) p := by
  rw [← contMDiffWithinAt_univ] at *
  exact cov.contMDiffWithinAt_curvatureTensor hn hU hW hσ

/-- Curvature evaluated on `C^n` section lifts is `C^n` on a parameter set, for `n ≤ ∞`. -/
theorem contMDiffOn_curvatureTensor {s : Set P} (hn : n ≤ ∞)
    (hU : ContMDiffOn J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (U q)) s)
    (hW : ContMDiffOn J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (W q)) s)
    (hσ : ContMDiffOn J (I.prod 𝓘(ℝ, F)) n (fun q ↦ TotalSpace.mk' F (f q) (σ q)) s) :
    ContMDiffOn J (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (cov.curvatureTensor (f q) (U q) (W q) (σ q))) s :=
  fun p hp ↦ cov.contMDiffWithinAt_curvatureTensor hn (hU p hp) (hW p hp) (hσ p hp)

/-- Curvature evaluated on `C^n` section lifts is `C^n` globally, for `n ≤ ∞`. -/
theorem contMDiff_curvatureTensor (hn : n ≤ ∞)
    (hU : ContMDiff J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (U q)))
    (hW : ContMDiff J I.tangent n (fun q ↦ TotalSpace.mk' E (f q) (W q)))
    (hσ : ContMDiff J (I.prod 𝓘(ℝ, F)) n (fun q ↦ TotalSpace.mk' F (f q) (σ q))) :
    ContMDiff J (I.prod 𝓘(ℝ, F)) n
      (fun q ↦ TotalSpace.mk' F (f q) (cov.curvatureTensor (f q) (U q) (W q) (σ q))) :=
  fun _ ↦ cov.contMDiffAt_curvatureTensor hn (hU _) (hW _) (hσ _)

end CovariantDerivative
