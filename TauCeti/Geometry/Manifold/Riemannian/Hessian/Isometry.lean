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

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 5 (naturality of the connection).
-/

public section

open Bundle VectorField TauCeti.Manifold
open scoped Manifold ContDiff

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
    {u : N → ℝ} (hu : ContMDiff J 𝓘(ℝ) 2 u) (x : M) (v w : TangentSpace I x) :
    hessian I (u ∘ f) x v w =
      hessian J u (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  let V : (y : N) → TangentSpace J y := FiberBundle.extend F (mfderiv I J f x v)
  let W : (y : N) → TangentSpace J y := FiberBundle.extend F (mfderiv I J f x w)
  have hW : MDiffAt (T% W) (f x) := FiberBundle.mdifferentiableAt_extend J F _
  have hVx : mpullback I J f V x = v :=
    (hf.mpullback_apply_eq_iff V v).2 (FiberBundle.extend_apply_self F _)
  have hWx : mpullback I J f W x = w :=
    (hf.mpullback_apply_eq_iff W w).2 (FiberBundle.extend_apply_self F _)
  have hd (y : M) (z : TangentSpace I y) :
      mvfderiv I (u ∘ f) y z = mvfderiv J u (f y) (mfderiv I J f y z) := by
    rw [mvfderiv, mfderiv_comp y (hu.mdifferentiableAt (by simp)) (hf.mdifferentiableAt y)]
    rfl
  have hdW : (fun y ↦ mvfderiv I (u ∘ f) y (mpullback I J f W y)) =
      (fun y ↦ mvfderiv J u y (W y)) ∘ f := by
    funext y
    rw [hd, hf.mfderiv_apply_mpullback]
    rfl
  have hsource := hessian_apply_eq_mvfderiv_sub x
    (hu.comp (hf.contMDiff.of_le (by simp))).contMDiffAt
    (mpullback I J f V) (mpullback I J f W) (hf.mdifferentiableAt_mpullback hW)
  rw [hVx, hWx, hdW, hd, hf.mfderiv_leviCivitaConnection_mpullback hW] at hsource
  have htarget := hessian_apply_eq_mvfderiv_sub (f x) hu.contMDiffAt V W hW
  simp only [V, W, FiberBundle.extend_apply_self] at htarget
  let _ : IsManifold J (minSmoothness ℝ 2) N :=
    IsManifold.of_le (n := 2) (by simp)
  have hdirectional := mfderiv_comp x
    (TauCeti.mdifferentiableAt_mvfderiv_apply hu.contMDiffAt (by simp) hW) (hf.mdifferentiableAt x)
  rw [hsource, htarget]
  congr 1
  exact congrArg (fun L ↦ L v) hdirectional

end TauCeti.IsLocalRiemannianIsometry
