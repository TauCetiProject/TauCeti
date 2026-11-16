/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Hessians on one-dimensional manifolds

In dimension at most one the trace determines the whole Hessian: it is the Laplace–Beltrami
operator multiplied by the metric. This identifies the Hessian term in warped-product
curvature with the scalar radial second derivative.
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- In dimension at most one the Hessian is its trace times the metric. No regularity of the
function is needed for this identity between the totalized differential operators. -/
theorem hessian_eq_laplaceBeltrami_mul_inner_of_finrank_le_one
    (hn : Module.finrank ℝ E ≤ 1) (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) :
    hessian I f x v w = laplaceBeltrami I f x * inner ℝ v w := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [hessian_def]
  have hn' : Module.finrank ℝ (TangentSpace I x) = 1 := by
    have hpos := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).2 ⟨v, hv⟩
    have hle := (finrank_tangentSpace (I := I) x).le.trans hn
    omega
  rw [hessian_def, laplaceBeltrami_def, divergence_def]
  have h := LinearMap.congr_fun (LinearMap.eq_trace_smul_one_of_finrank_eq_one hn'
    (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x).toLinearMap) v
  simpa only [ContinuousLinearMap.coe_coe, LinearMap.smul_apply, one_apply_eq_self,
    real_inner_smul_left] using congrArg (fun z ↦ inner ℝ z w) h

end TauCeti.Manifold
