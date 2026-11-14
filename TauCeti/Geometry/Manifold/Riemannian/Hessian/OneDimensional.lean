/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Hessians on one-dimensional manifolds

In dimension one the trace determines the whole Hessian: it is the Laplace–Beltrami
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

/-- In dimension one the Hessian is its trace times the metric. No regularity of the
function is needed for this identity between the totalized differential operators. -/
theorem hessian_eq_laplaceBeltrami_mul_inner_of_finrank_eq_one
    (hn : Module.finrank ℝ E = 1) (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) :
    hessian I f x v w = laplaceBeltrami I f x * inner ℝ v w := by
  let b := (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex
    (finCongr ((finrank_tangentSpace x).trans hn))
  have hb : b (0 : Fin 1) ≠ 0 := b.orthonormal.ne_zero 0
  obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' (b 0) hb).1
    ((finrank_tangentSpace x).trans hn) v
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' (b 0) hb).1
    ((finrank_tangentSpace x).trans hn) w
  rw [laplaceBeltrami_eq_sum_hessian I f x b]
  simp [hessian_smul_left, hessian_smul_right, real_inner_smul_left, real_inner_smul_right]
  ring

end TauCeti.Manifold
