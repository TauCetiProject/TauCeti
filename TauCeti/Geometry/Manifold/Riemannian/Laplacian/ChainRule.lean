/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hessian.ChainRule
import Mathlib.Tactic

/-!
# The pointwise Laplace–Beltrami chain rule

Tracing the native Hessian chain rule gives the Laplacian chain rule under pointwise `C²`
regularity, without global regularity or a common open range for the scalar profile.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 3.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section
open Bundle
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The scalar Laplacian chain rule needs only pointwise second-order smoothness. -/
theorem laplaceBeltrami_comp_of_contMDiffAt
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    {h : ℝ → ℝ} {f : M → ℝ} {x : M} (hh : ContDiffAt ℝ 2 h (f x))
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    laplaceBeltrami I (h ∘ f) x = deriv h (f x) * laplaceBeltrami I f x +
      deriv (deriv h) (f x) * ‖mgradient I f x‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hs : ∑ i, (mvfderiv I f x (b i)) ^ 2 = ‖mgradient I f x‖ ^ 2 := by
    simp_rw [← inner_mgradient]
    exact b.sum_sq_inner_left (mgradient I f x)
  rw [laplaceBeltrami_eq_sum_hessian I (h ∘ f) x b,
    laplaceBeltrami_eq_sum_hessian I f x b]
  simp_rw [hessian_comp hh hf]
  calc
    _ = deriv h (f x) * ∑ i, hessian I f x (b i) (b i) +
        deriv (deriv h) (f x) * ∑ i, (mvfderiv I f x (b i)) ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hs]

end TauCeti.Manifold
