/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Lemma
public import TauCeti.Geometry.Manifold.Morse.ExponentialConvergence
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Exponential convergence of gradient trajectories to a Morse–Bott critical submanifold

Let `i : S → M` be a nondegenerate, or Morse–Bott, critical submanifold of a function `f` on a
boundaryless manifold carrying a Riemannian metric. Its points are critical points of `f`, but
they need not be isolated, so they need not be nondegenerate critical points, and the exponential
convergence of negative gradient trajectories to nondegenerate critical points does not apply to
them as stated. What that convergence uses is only Łojasiewicz's gradient inequality with exponent
`1 / 2` at the limit.

This file proves that inequality at every point `i s` of a Morse–Bott critical submanifold, for
the Riemannian gradient and any continuous metric: near `i s`,

`lam * |f y - f (i s)| ≤ ‖grad f y‖ ^ 2`

(`IsNondegenerateCriticalSubmanifold.exists_mul_abs_sub_le_norm_mgradient_sq`, in the namespace
`TauCeti.SmoothEmbedding`). It is the inequality in the preferred chart at `i s`
(`IsNondegenerateCriticalSubmanifold.exists_mul_abs_sub_le_norm_fderiv_comp_extChartAt_symm_sq`),
carried to the gradient by
`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm`, since in that
chart the differential of `f` is bounded by a multiple of the length of its gradient.

Consequently a negative gradient trajectory converging to a point of a Morse–Bott critical
submanifold converges to it exponentially fast in the Riemannian distance
(`exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient` in the same namespace), by
the decay theorem `TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`
for limits at which the Łojasiewicz inequality holds. This exponential decay at both ends of a
trajectory between two critical components is what makes its two limits well-behaved endpoints,
as needed for the source and target maps of spaces of trajectories between critical components of
a Morse–Bott function.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_mul_abs_sub_le_norm_mgradient_sq`: the Łojasiewicz inequality with exponent `1 / 2`
  near a point of a Morse–Bott critical submanifold, for the Riemannian gradient.
* `exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`: a trajectory of
  `-grad f` converging to a point of the submanifold converges to it exponentially fast.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87--89.
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse homology*, Kluwer Texts in the Mathematical
  Sciences 29, Kluwer, 2004, Chapter 6 (the Morse–Bott case of the gradient flow).
-/

public section

open Bundle Filter Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M}

/-- **The Morse–Bott form of Łojasiewicz's gradient inequality on a Riemannian manifold.** If
`i : S → M` is a nondegenerate critical submanifold of `f`, with `i` of class `C²`, then near each
point `i s` the absolute energy difference `|f y - f (i s)|` is bounded by a multiple of the
squared Riemannian length of the gradient of `f` at `y`, for any continuous Riemannian metric. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hi : i.IsNondegenerateCriticalSubmanifold f) (hn : 2 ≤ n) (s : S) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 (i s), lam * |f y - f (i s)| ≤ ‖mgradient I f y‖ ^ 2 :=
  exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm
    (hi.exists_mul_abs_sub_le_norm_fderiv_comp_extChartAt_symm_sq hn s)

/-- **A trajectory converging to a point of a Morse–Bott critical submanifold converges to it
exponentially fast.** Let `i : S → M` be a nondegenerate critical submanifold of a `C²` function
`f`, with `i` of class `C²`, and let the metric be `C¹`. If the maximal integral curve `γ` of
`-grad f` through `x` converges to a point `i s` of the submanifold, then the Riemannian distance
from `γ t` to `i s` is at most `C * exp (-μ * t)` for some `μ, C > 0` and all large `t`. -/
theorem exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient [T2Space M]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (hi : i.IsNondegenerateCriticalSubmanifold f) (hn : 2 ≤ n) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    {x : M} {s : S} (hconv : Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 (i s))) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) (i s) ≤
        ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  exact TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient
    (hi.mem_criticalPoints s) (hi.exists_mul_abs_sub_le_norm_mgradient_sq hn s) hconv hf

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

end TauCeti
