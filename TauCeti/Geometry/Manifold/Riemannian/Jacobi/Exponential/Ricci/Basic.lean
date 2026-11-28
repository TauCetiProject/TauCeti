/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Transverse
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci

/-!
# Radial exponential Jacobians and Ricci curvature

The full and transverse curvature traces of the native radial Jacobi operator are Ricci
curvature along the radial geodesic. Radial/transverse equations and determinant identities
are supplied independently in the upstream exponential Jacobi module.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold.IsNormalDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}

/-- In the genuine parallel frame, the curvature trace is the actual radial Ricci tensor. -/
theorem trace_radialJacobiCurvature (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (h0 : 0 ∈ Icc l r) {t : ℝ} (ht : t ∈ Icc l r) :
    LinearMap.trace ℝ (TangentSpace I p)
        (h.radialJacobiCurvature b v hlr.le hseg t).toLinearMap =
      (leviCivitaConnection I M).ricciTensor (riemannianExp I M p (t • v))
        (curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t)
        (curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t) := by
  let e := h.radialParallelIsometry b v hlr hseg h0 ht
  rw [LinearMap.trace_eq_sum_inner _ b,
    (leviCivitaConnection I M).ricciTensor_eq_sum_inner _ (b.map e)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.coe_coe, radialJacobiCurvature_apply,
    h.radialFrameCoordinates_eq_symm b v hlr hseg h0 ht,
    ← h.radialParallelIsometry_apply b v hlr hseg h0 ht, OrthonormalBasis.map_apply]
  exact (e.inner_map_eq_flip _ _).symm

/-- Removing the radial zero eigenvalue preserves the trace of the curvature operator. -/
theorem trace_compression_radialJacobiCurvature (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p)
    {l r : ℝ} (hlr : l < r) (hseg : ∀ s ∈ Icc l r, s • v ∈ U)
    (h0 : 0 ∈ Icc l r) {t : ℝ} (ht : t ∈ Icc l r) :
    LinearMap.trace ℝ (ℝ ∙ v)ᗮ
        ((h.radialJacobiCurvature b v hlr.le hseg t).compression
          (ℝ ∙ v)ᗮ.subtypeL).toLinearMap =
      (leviCivitaConnection I M).ricciTensor (riemannianExp I M p (t • v))
        (curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t)
        (curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t) := by
  let W := (ℝ ∙ v)ᗮ
  let K := h.radialJacobiCurvature b v hlr.le hseg t
  have hline (x : TangentSpace I p) (hx : x ∈ ℝ ∙ v) : K x = 0 := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, h.radialJacobiCurvature_radial b v hlr hseg h0 ht, smul_zero]
  have hcomp : K.toLinearMap ∘ₗ W.subtype ∘ₗ W.orthogonalProjectionOnto.toLinearMap =
      K.toLinearMap := by
    ext x
    -- The projection's subtype coercion is its ambient star projection.
    change K (W.starProjection x) = K x
    rw [Submodule.starProjection_orthogonal_val, map_sub,
      hline _ ((ℝ ∙ v).starProjection_apply_mem x), sub_zero]
  rw [ContinuousLinearMap.compression_def, Submodule.adjoint_subtypeL]
  -- Expose only the linear-map coercions needed by cyclic invariance of trace.
  change LinearMap.trace ℝ W
    (W.orthogonalProjectionOnto.toLinearMap ∘ₗ (K.toLinearMap ∘ₗ W.subtype)) = _
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, hcomp]
  exact h.trace_radialJacobiCurvature b v hlr hseg h0 ht


end TauCeti.Manifold.IsNormalDomain
