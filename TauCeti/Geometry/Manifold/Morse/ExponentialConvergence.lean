/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.GradientFlow
-- Private: the normed-space Łojasiewicz inequality, Grönwall's inequality and the continuity of a
-- `C¹` metric are used only inside proofs; no declaration below exposes their APIs.
import TauCeti.Analysis.Calculus.Morse.Basic
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Exponential decay of the energy along a negative gradient trajectory on a manifold

Let `f` be a function on a manifold `M` carrying a continuous Riemannian metric, and let `p` be a
nondegenerate critical point of `f`. Near `p` the **Morse form of Łojasiewicz's gradient
inequality** holds with the optimal exponent `1/2`:

`lam * |f y - f p| ≤ ‖grad f y‖ ^ 2`

(`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`). It is
transported from the normed-space inequality
`TauCeti.IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_fderiv_sq` for the coordinate
expression of `f` in the preferred chart at `p`: near `p` the differential of that expression is
bounded by a multiple of the Riemannian length of the gradient
(`TauCeti.Manifold.eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient`). The metric
need not be adapted to the chart, nor smooth.

Now let `γ` be the maximal integral curve of `-grad f` through `x`, defined for all positive time
and converging to `p`. The energy `f (γ t) - f p` is nonnegative
(`TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`), since `f` decreases along `γ` and tends to
`f p`. Its derivative is `-‖grad f (γ t)‖ ^ 2`, which the inequality above bounds by `-lam` times
the energy once `γ` stays near `p`, so by Grönwall's inequality the energy decays like
`exp (-lam * t)` (`TauCeti.exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient`). This is the
manifold counterpart, for an arbitrary `C¹` metric, of the vector-space theorem
`TauCeti.IsIntegralCurveOn.exists_sub_le_mul_exp_atTop`.

## Main results

* `TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`: the
  Łojasiewicz inequality with exponent `1/2` near a nondegenerate critical point, for the
  Riemannian gradient.
* `TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`: the energy along a forward negative
  gradient trajectory is bounded below by its value at the limit point.
* `TauCeti.exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient`: along a forward negative
  gradient trajectory converging to a nondegenerate critical point the energy decays exponentially.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87--89.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Bundle Filter Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

section Lojasiewicz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {p : M}

/-- **The Morse form of Łojasiewicz's gradient inequality on a Riemannian manifold.** Near a
nondegenerate critical point `p` of `f`, the absolute energy difference `|f y - f p|` is bounded by
a multiple of the squared Riemannian length of the gradient of `f` at `y`, for any continuous
Riemannian metric. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq
    (hp : IsManifoldNondegenerateCriticalPoint I f p) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2 := by
  obtain ⟨lam, hlam, hloj⟩ :=
    ((isManifoldNondegenerateCriticalPoint_iff I).1 hp).exists_mul_abs_sub_le_norm_fderiv_sq
  obtain ⟨C, hC, hbd⟩ :=
    eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient (I := I) f p
  refine ⟨lam / C ^ 2, by positivity, ?_⟩
  filter_upwards [(continuousAt_extChartAt (I := I) p).eventually hloj, hbd,
    extChartAt_source_mem_nhds (I := I) p] with y hy hyb hys
  simp only [Function.comp_apply, (extChartAt I p).left_inv hys,
    (extChartAt I p).left_inv (mem_extChartAt_source p)] at hy
  calc lam / C ^ 2 * |f y - f p| = lam * |f y - f p| / C ^ 2 := by ring
    _ ≤ ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y)‖ ^ 2 / C ^ 2 := by gcongr
    _ ≤ (C * ‖mgradient I f y‖) ^ 2 / C ^ 2 := by gcongr
    _ = ‖mgradient I f y‖ ^ 2 := by field_simp

end Lojasiewicz

section Decay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x p : M}

/-- **The energy along a convergent trajectory is nonnegative.** If the maximal integral curve of
`-grad f` through `x` exists for all positive time and converges to `p`, then `f p ≤ f (γ t)` for
every `t ≥ 0`: the function `f` decreases along the curve and tends to `f p`. -/
theorem le_comp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hconv : Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p)) {t : ℝ}
    (ht : 0 ≤ t) :
    f p ≤ f (maximalIntegralCurve (-mgradient I f) x t) := by
  refine le_of_tendsto ((hf.continuous.tendsto p).comp hconv) ?_
  filter_upwards [eventually_ge_atTop t] with s hs
  exact antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf (hx ht) (hx (ht.trans hs)) hs

/-- **The energy along a trajectory converging to a nondegenerate critical point decays
exponentially.** If the maximal integral curve `γ` of `-grad f` through `x` exists for all positive
time and converges to a nondegenerate critical point `p`, then `f (γ t) - f p ≤ C * exp (-μ * t)`
for some `μ, C > 0` and all large `t`. -/
theorem exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hp : IsManifoldNondegenerateCriticalPoint I f p)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hconv : Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
      f (maximalIntegralCurve (-mgradient I f) x t) - f p ≤ C * Real.exp (-(μ * t)) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I f) x
  obtain ⟨lam, hlam, hloj⟩ := hp.exists_mul_abs_sub_le_norm_mgradient_sq
  -- After some time `T ≥ 0` the trajectory stays where the Łojasiewicz inequality holds.
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((hconv.eventually hloj).and (eventually_ge_atTop 0))
  let g : ℝ → ℝ := fun s ↦ f (γ s) - f p
  have hg : ∀ s ∈ Ici T, HasDerivAt g (-‖mgradient I f (γ s)‖ ^ 2) s := fun s hs ↦
    (hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf
      (hx ((hT T le_rfl).2.trans hs))).sub_const _
  have hloj' : ∀ s ∈ Ici T, lam * |g s| ≤ ‖mgradient I f (γ s)‖ ^ 2 := fun s hs ↦ (hT s hs).1
  -- On `[T, ∞)` the energy `g` satisfies `g' = -‖grad f‖² ≤ -lam * g`, so it decays exponentially.
  exact ⟨lam, hlam, exists_le_mul_exp_atTop_of_hasDerivAt_le_neg_mul (lam := lam) hg fun s hs ↦
    by linarith [hloj' s hs, mul_le_mul_of_nonneg_left (le_abs_self (g s)) hlam.le]⟩

end Decay

end TauCeti
