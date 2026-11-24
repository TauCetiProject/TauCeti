/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# Differentiating the squared norm of a Riemannian gradient

For a locally `C²` real function and a `C¹` Riemannian metric, metric compatibility
differentiates the squared gradient norm. Symmetry of the native Hessian identifies its
gradient with twice the covariant derivative of the original gradient in its own direction.
These identities hold in every dimension and require no boundary or global topological
assumptions.

These identities are ported from Otis Chodosh's `ForTauCeti` formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory), module
`ForTauCeti/Geometry/Manifold/Riemannian/Gradient/NormSq.lean`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 3.
-/

public noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff Manifold InnerProductSpace

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M}

/-- Metric compatibility differentiates the squared norm of a Riemannian gradient. -/
theorem mvfderiv_norm_sq_mgradient (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ ‖mgradient I f y‖ ^ 2) x v =
      2 * ⟪leviCivitaConnection I M (mgradient I f) x v, mgradient I f x⟫_ℝ := by
  have : IsManifold I (1 + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hG : MDiffAt (T% (mgradient I f)) x :=
    (contMDiffAt_mgradient (n := 1) hf).mdifferentiableAt (by simp)
  have hm := (isMetricCompatible_leviCivitaConnection I (M := M)).mvfderiv_inner_eq
    (FiberBundle.extend E v) hG hG
  simp only [FiberBundle.extend_apply_self, real_inner_self_eq_norm_sq] at hm
  rw [real_inner_comm (leviCivitaConnection I M (mgradient I f) x v)] at hm
  linarith only [hm]

/-- The gradient of the squared gradient norm is twice the covariant derivative of the
original gradient in its own direction. -/
theorem mgradient_norm_sq_mgradient (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    mgradient I (fun y ↦ ‖mgradient I f y‖ ^ 2) x =
      (2 : ℝ) • leviCivitaConnection I M (mgradient I f) x (mgradient I f x) := by
  symm
  apply eq_mgradient_iff.mpr
  intro v
  rw [real_inner_smul_left, mvfderiv_norm_sq_mgradient hf v]
  simpa only [hessian_def] using
    congrArg (fun r : ℝ ↦ 2 * r) (hessian_symm x hf (mgradient I f x) v)

end TauCeti.Manifold
