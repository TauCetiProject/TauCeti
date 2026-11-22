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
  have hg := hf.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx
  have hm : IsLocalMin f ((extChartAt I x).symm (extChartAt I x x)) := by
    rwa [extChartAt_to_inv]
  have hcrit : mvfderiv I f x = 0 := by
    rw [← mem_criticalPoints,
      mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero_of_differentiableAt
        (hg.differentiableAt (by norm_num))]
    exact (hm.comp_continuous (continuousAt_extChartAt_symm x)).fderiv_eq_zero
  rw [hessian_eq_criticalHessian hf hx hcrit]
  exact (hf.of_le one_le_two).criticalHessian_self_nonneg_of_isLocalMin hx hmin v

/-- At an interior local maximum of a `C²` function on a finite-dimensional Riemannian
manifold, the Hessian is negative semidefinite. -/
theorem hessian_self_nonpos_of_isLocalMax (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hx : I.IsInteriorPoint x) (hmax : IsLocalMax f x) (v : TangentSpace I x) :
    hessian I f x v v ≤ 0 := by
  have h : 0 ≤ hessian I (-f) x v v :=
    hessian_self_nonneg_of_isLocalMin hf.neg hx hmax.neg v
  rw [hessian_neg_of_contMDiffAt I hf] at h
  exact neg_nonneg.mp h

end TauCeti.Manifold
