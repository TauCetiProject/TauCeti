/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# The Hessian of a solution of the eikonal equation

If the gradient of a twice differentiable real function has locally constant length, its
Hessian vanishes whenever one of its arguments is the gradient. This follows from metric
compatibility of the Levi–Civita connection and Hessian symmetry.

See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11.
-/

public noncomputable section

open Bundle CovariantDerivative Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The Hessian of a local solution of the constant-speed eikonal equation annihilates its
Riemannian gradient. -/
theorem hessian_mgradient_eq_zero_of_eventually_norm_sq_eq_const {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) {c : ℝ}
    (hc : (fun y ↦ ‖mgradient I f y‖ ^ 2) =ᶠ[𝓝 x] fun _ ↦ c)
    (v : TangentSpace I x) : hessian I f x (mgradient I f x) v = 0 := by
  have : IsManifold I (1 + 1) M := by simpa only [one_add_one_eq_two] using
    (inferInstance : IsManifold I 2 M)
  have hG : MDiffAt (T% (mgradient I f)) x :=
    (contMDiffAt_mgradient (n := 1) hf).mdifferentiableAt (by simp)
  have heq : (fun y ↦ inner ℝ (mgradient I f y) (mgradient I f y)) =ᶠ[𝓝 x]
      fun _ ↦ c := by simpa only [real_inner_self_eq_norm_sq] using hc
  have hm := (isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
    (FiberBundle.extend E v) hG hG
  rw [heq.mvfderiv_eq, mvfderiv_const] at hm
  simp only [zero_apply, FiberBundle.extend_apply_self,
    real_inner_comm (mgradient I f x)] at hm
  rw [hessian_symm x hf, hessian_def, real_inner_comm]
  linarith

end TauCeti.Manifold
