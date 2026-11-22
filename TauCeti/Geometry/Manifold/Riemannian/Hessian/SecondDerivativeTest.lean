/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Giada Franz
-/
module

import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
public import TauCeti.Geometry.Manifold.Riemannian.CriticalHessian

/-!
# The second derivative test on a Riemannian manifold

Let `f` be a real function on a finite-dimensional Riemannian manifold without boundary, `C²` at
a critical point `x`. If the Riemannian Hessian of `f` at `x` is positive definite, then `x` is a
strict local minimum of `f`.

At a critical point, the Riemannian Hessian is the second derivative of `f` read in the preferred
chart (`TauCeti.Manifold.hessian_eq_criticalHessian`), and the first derivative of the coordinate
expression vanishes, so the test reduces to the second derivative test on the model space
(`eventually_lt_of_fderiv_eq_zero_of_fderiv_fderiv_pos`).

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
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M}

/-- **The second derivative test.** If `x` is a critical point of a function `f` which is `C²`
at `x` on a finite-dimensional Riemannian manifold without boundary, and the Riemannian Hessian
of `f` at `x` is positive definite, then `f(x) < f(y)` for all `y ≠ x` close to `x`. -/
theorem _root_.ContMDiffAt.eventually_lt_of_hessian_pos (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hcrit : mvfderiv I f x = 0) (hpos : ∀ v : TangentSpace I x, v ≠ 0 → 0 < hessian I f x v v) :
    ∀ᶠ y in 𝓝[≠] x, f x < f y := by
  apply hf.eventually_lt_of_criticalHessian_pos BoundarylessManifold.isInteriorPoint hcrit
  intro v hv
  rw [← hessian_eq_criticalHessian hf hcrit]
  exact hpos v hv

/-- At a local maximum of a `C²` function on a boundaryless Riemannian manifold, the Hessian is
negative semidefinite. -/
theorem hessian_self_nonpos_of_isLocalMax (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmax : IsLocalMax f x) (v : TangentSpace I x) : hessian I f x v v ≤ 0 := by
  have hmax' : IsLocalMax (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hm : IsLocalMax f ((extChartAt I x).symm (extChartAt I x x)) := by simpa using hmax
    exact hm.comp_continuous (continuousAt_extChartAt_symm x)
  rw [hessian_eq_criticalHessian hf (mem_criticalPoints.1 (hmax.mem_criticalPoints (I := I))),
    criticalHessian_apply_eq_fderiv_fderiv]
  exact fderiv_fderiv_self_nonpos_of_isLocalMax
    (hf.contDiffAt_comp_extChartAt_symm.eventually_differentiableAt (by norm_num)) hmax'
    (tangentSpaceCastModel I x v)

/-- At a local minimum of a `C²` function on a boundaryless Riemannian manifold, the Hessian is
positive semidefinite. -/
theorem hessian_self_nonneg_of_isLocalMin (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmin : IsLocalMin f x) (v : TangentSpace I x) : 0 ≤ hessian I f x v v := by
  have hmin' : IsLocalMin (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hm : IsLocalMin f ((extChartAt I x).symm (extChartAt I x x)) := by simpa using hmin
    exact hm.comp_continuous (continuousAt_extChartAt_symm x)
  rw [hessian_eq_criticalHessian hf (mem_criticalPoints.1 (hmin.mem_criticalPoints (I := I))),
    criticalHessian_apply_eq_fderiv_fderiv]
  exact fderiv_fderiv_self_nonneg_of_isLocalMin
    (hf.contDiffAt_comp_extChartAt_symm.eventually_differentiableAt (by norm_num)) hmin'
    (tangentSpaceCastModel I x v)

end TauCeti.Manifold
