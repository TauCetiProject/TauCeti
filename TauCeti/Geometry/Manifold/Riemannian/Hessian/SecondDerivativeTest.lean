/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Giada Franz
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.CriticalHessian

/-!
# The second derivative test on a Riemannian manifold

Let `f` be a real function on a finite-dimensional Riemannian manifold, `C²` at an interior
critical point `x`. If the Riemannian Hessian of `f` at `x` is positive definite, then `x` is a
strict local minimum of `f`.

The strict test gives a sufficient condition for a critical point to be a strict local
minimum. The necessary tests give the Hessian sign at interior local extrema and supply the
pointwise sign tests and contact comparisons for the Laplace–Beltrami operator in
`TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple`.

## Main results

* `ContMDiffAt.eventually_lt_of_hessian_pos`: the strict second derivative test.
* `TauCeti.Manifold.hessian_self_nonpos_of_isLocalMax`,
  `TauCeti.Manifold.hessian_self_nonneg_of_isLocalMin`: the necessary second derivative tests.

The strict test is adapted from Giada Franz's formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/master/ForTauCeti/Geometry/Manifold/Riemannian/Hessian/SecondDerivativeTest.lean).
Its metric-free interior-point argument is `ContMDiffAt.eventually_lt_of_criticalHessian_pos`.
-/

public section

open Bundle Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M}

/-- **The second derivative test.** If `x` is an interior critical point of a function `f` which
is `C²` at `x` on a finite-dimensional Riemannian manifold, and the Riemannian Hessian
of `f` at `x` is positive definite, then `f(x) < f(y)` for all `y ≠ x` close to `x`. -/
theorem _root_.ContMDiffAt.eventually_lt_of_hessian_pos (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hx : I.IsInteriorPoint x) (hcrit : mvfderiv I f x = 0)
    (hpos : ∀ v : TangentSpace I x, v ≠ 0 → 0 < hessian I f x v v) :
    ∀ᶠ y in 𝓝[≠] x, f x < f y := by
  apply hf.eventually_lt_of_criticalHessian_pos hx hcrit
  intro v hv
  rw [← hessian_eq_criticalHessian hf hx hcrit]
  exact hpos v hv

/-- At an interior local minimum of a `C²` function on a finite-dimensional Riemannian
manifold, the Hessian is positive semidefinite. -/
theorem hessian_self_nonneg_of_isLocalMin (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hx : I.IsInteriorPoint x) (hmin : IsLocalMin f x) (v : TangentSpace I x) :
    0 ≤ hessian I f x v v := by
  have hcrit := mem_criticalPoints.1 (hmin.mem_criticalPoints hx)
  rw [hessian_eq_criticalHessian hf hx hcrit]
  exact (hf.of_le one_le_two).criticalHessian_self_nonneg_of_isLocalMin hx hmin v

/-- At an interior local maximum of a `C²` function on a finite-dimensional Riemannian
manifold, the Hessian is negative semidefinite. -/
theorem hessian_self_nonpos_of_isLocalMax (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hx : I.IsInteriorPoint x) (hmax : IsLocalMax f x) (v : TangentSpace I x) :
    hessian I f x v v ≤ 0 := by
  have h : 0 ≤ hessian I (-f) x v v :=
    hessian_self_nonneg_of_isLocalMin hf.neg hx hmax.neg v
  rw [I.hessian_neg_of_mdifferentiableAt_mgradient (mdifferentiableAt_mgradient hf)] at h
  exact neg_nonneg.mp h

end TauCeti.Manifold
