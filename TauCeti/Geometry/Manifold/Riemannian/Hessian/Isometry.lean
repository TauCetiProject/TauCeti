/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita

/-!
# Hessians and local Riemannian isometries

The Hessian of a pulled-back scalar function is the pullback of its Hessian under a local
Riemannian isometry. This allows Hessians to be compared on distinct manifold carriers without
identifying their metric instances. The result uses the native Levi-Civita connection and its
naturality under local Riemannian isometries.

Taking traces in orthonormal bases, the Laplace–Beltrami operator is natural as well:
`Δ_M (u ∘ f) = (Δ_N u) ∘ f` for every local Riemannian isometry `f : M → N`. Applied to the
covering map of a quotient by a free isometric action, this says that the Laplacian of a pulled-back
function is the pullback of the Laplacian on the quotient; applied to an isometry `q` of `M`, it
says that the Laplacian commutes with the action `u ↦ u ∘ q⁻¹` on functions.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 5 (naturality of the connection).
-/

public section

open Bundle VectorField TauCeti.Manifold
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti.IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 2 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

/-- A local Riemannian isometry pulls back the scalar Hessian. -/
theorem hessian_comp {f : M → N} (hf : IsLocalRiemannianIsometry I J f)
    {u : N → ℝ} {x : M} (hu : ContMDiffAt J 𝓘(ℝ) 2 u (f x))
    (v w : TangentSpace I x) :
    hessian I (u ∘ f) x v w =
      hessian J u (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  let V : (y : N) → TangentSpace J y := FiberBundle.extend F (mfderiv I J f x v)
  let W : (y : N) → TangentSpace J y := FiberBundle.extend F (mfderiv I J f x w)
  have hW : MDiffAt (T% W) (f x) := FiberBundle.mdifferentiableAt_extend J F _
  have hVx : mpullback I J f V x = v :=
    (hf.mpullback_apply_eq_iff V v).2 (FiberBundle.extend_apply_self F _)
  have hWx : mpullback I J f W x = w :=
    (hf.mpullback_apply_eq_iff W w).2 (FiberBundle.extend_apply_self F _)
  have hd (y : M) (huy : MDifferentiableAt J 𝓘(ℝ) u (f y))
      (z : TangentSpace I y) :
      mvfderiv I (u ∘ f) y z = mvfderiv J u (f y) (mfderiv I J f y z) := by
    rw [mvfderiv, mfderiv_comp y huy (hf.mdifferentiableAt y)]
    rfl
  have hdW : (fun y ↦ mvfderiv I (u ∘ f) y (mpullback I J f W y)) =ᶠ[𝓝 x]
      (fun y ↦ mvfderiv J u y (W y)) ∘ f := by
    filter_upwards [(hf.mdifferentiableAt x).continuousAt.tendsto
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hu)] with y huy
    rw [hd y (huy.mdifferentiableAt (by simp)), hf.mfderiv_apply_mpullback]
    rfl
  have hsource := hessian_apply_eq_mvfderiv_sub x
    (hu.comp x (hf.contMDiff.contMDiffAt.of_le (by simp)))
    (mpullback I J f V) (mpullback I J f W) (hf.mdifferentiableAt_mpullback hW)
  rw [hVx, hWx, hdW.mvfderiv_eq, hd x (hu.mdifferentiableAt (by simp)),
    hf.mfderiv_leviCivitaConnection_mpullback hW] at hsource
  have htarget := hessian_apply_eq_mvfderiv_sub (f x) hu V W hW
  simp only [V, W, FiberBundle.extend_apply_self] at htarget
  have hdirectional := mfderiv_comp x
    (TauCeti.mdifferentiableAt_mvfderiv_apply hu le_rfl hW) (hf.mdifferentiableAt x)
  rw [hsource, htarget]
  congr 1
  exact congrArg (fun L ↦ L v) hdirectional

/-- A local Riemannian isometry pulls back the Laplace–Beltrami operator:
`Δ_M (u ∘ f) = (Δ_N u) ∘ f` at every point where `u` is `C²`. -/
theorem laplaceBeltrami_comp {f : M → N} (hf : IsLocalRiemannianIsometry I J f)
    {u : N → ℝ} {x : M} (hu : ContMDiffAt J 𝓘(ℝ) 2 u (f x)) :
    laplaceBeltrami I (u ∘ f) x = laplaceBeltrami J u (f x) := by
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [laplaceBeltrami_eq_sum_hessian I (u ∘ f) x b,
    laplaceBeltrami_eq_sum_hessian J u (f x) (b.map e)]
  simp only [OrthonormalBasis.map_apply, he, hf.hessian_comp hu]

end TauCeti.IsLocalRiemannianIsometry
