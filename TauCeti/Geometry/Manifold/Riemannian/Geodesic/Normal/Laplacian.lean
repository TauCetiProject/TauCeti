/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Coordinates
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# Hessians and Laplacians in normal coordinates

Composition with the Riemannian logarithm preserves the Hessian and Laplacian at the expansion
center. The scalar differential identity is in `Normal.Basic`. The Hessian identity uses normal
coordinate fields, whose Levi–Civita covariant derivatives vanish at the center. These identities
transport Euclidean
upper supports to intrinsic distance barriers.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapters 3 and 5.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace TauCeti.Manifold.IsNormalDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M]
  {p : M} {U : Set (TangentSpace I p)}

/-- At the center of normal coordinates, the Riemannian Hessian is the second Fréchet
derivative of the coordinate function. -/
theorem hessian_comp_riemannianLog_self (h : IsNormalDomain I M p U)
    {P : TangentSpace I p → ℝ} (hP : ContDiffAt ℝ 2 P 0) (v w : TangentSpace I p) :
    hessian I (P ∘ riemannianLog I M p U) p v w =
      fderiv ℝ (fderiv ℝ P) 0 v w := by
  have hlog := h.contMDiffOn_riemannianLog.contMDiffAt
    (h.isOpen_image.mem_nhds h.self_mem_image)
  have hPlog : ContDiffAt ℝ 2 P (riemannianLog I M p U p) := by
    simpa only [h.riemannianLog_self] using hP
  have hf : ContMDiffAt I 𝓘(ℝ) 2 (P ∘ riemannianLog I M p U) p :=
    hPlog.comp_contMDiffAt (hlog.of_le (by simp))
  have htend : Tendsto (riemannianLog I M p U) (𝓝 p) (𝓝 0) := by
    simpa only [h.riemannianLog_self] using hlog.continuousAt.tendsto
  have hdW : (fun y ↦ mvfderiv I (P ∘ riemannianLog I M p U) y
      (normalCoordinateField I M p U w y)) =ᶠ[𝓝 p]
      (fun z ↦ fderiv ℝ P z w) ∘ riemannianLog I M p U := by
    filter_upwards [h.isOpen_image.mem_nhds h.self_mem_image,
      htend (hP.eventually (by simp))] with y hy hyP
    -- Expose the pulled-back regularity premise at the logarithmic coordinate.
    change ContDiffAt ℝ 2 P (riemannianLog I M p U y) at hyP
    rw [mvfderiv_comp_apply y (hyP.differentiableAt (by simp)).mdifferentiableAt
      (h.mdifferentiableAt_riemannianLog hy), h.mfderiv_riemannianLog_normalCoordinateField w hy,
      mvfderiv_eq_fderiv]
    rfl
  have hs := hessian_apply_eq_mvfderiv_sub p hf
    (normalCoordinateField I M p U v) (normalCoordinateField I M p U w)
    (h.mdifferentiableAt_normalCoordinateField w h.self_mem_image)
  simp only [h.normalCoordinateField_self, h.leviCivitaConnection_normalCoordinateField_self,
    zero_apply, map_zero, sub_zero] at hs
  have hdP : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ)
      (fun z ↦ fderiv ℝ P z w) (riemannianLog I M p U p) := by
    rw [h.riemannianLog_self]
    exact (hP.hasFDerivAt_fderiv_apply le_rfl w).differentiableAt.mdifferentiableAt
  rw [hs, hdW.mvfderiv_eq, mvfderiv_comp_apply p hdP
    (h.mdifferentiableAt_riemannianLog h.self_mem_image), mvfderiv_eq_fderiv]
  -- Express the model-space manifold derivative in Fréchet form so the
  -- center identities for the logarithm can rewrite its point and tangent vector.
  change fderiv ℝ (fun z ↦ fderiv ℝ P z w) (riemannianLog I M p U p)
    (mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p U) p v) = _
  rw [h.mfderiv_riemannianLog_self_apply, h.riemannianLog_self]
  exact fderiv_clm_apply_const_apply (hP.hasFDerivAt_fderiv le_rfl).differentiableAt w v

/-- At the center of normal coordinates, the Laplace–Beltrami operator is the Euclidean
Laplacian of the coordinate function. -/
theorem laplaceBeltrami_comp_riemannianLog_self (h : IsNormalDomain I M p U)
    {P : TangentSpace I p → ℝ} (hP : ContDiffAt ℝ 2 P 0) :
    laplaceBeltrami I (P ∘ riemannianLog I M p U) p = Laplacian.laplacian P 0 := by
  rw [laplaceBeltrami_eq_sum_hessian I _ p (stdOrthonormalBasis ℝ (TangentSpace I p)),
    TauCeti.laplacian_eq_traceL, TauCeti.traceL_apply]
  exact Finset.sum_congr rfl fun i _ ↦ h.hessian_comp_riemannianLog_self hP _ _

end TauCeti.Manifold.IsNormalDomain
