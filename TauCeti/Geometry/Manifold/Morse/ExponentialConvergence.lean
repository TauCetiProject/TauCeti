/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.Morse.GradientFlow
-- Private: the scalar and normed-space Łojasiewicz inequalities and the comparison lemma,
-- Grönwall's inequality, the continuity of a `C¹` metric and the length of a curve as the integral
-- of its speed are used only inside proofs; no declaration below exposes their APIs.
import TauCeti.Analysis.Calculus.Lojasiewicz
import TauCeti.Analysis.Calculus.Lojasiewicz.Comparison
import TauCeti.Analysis.Calculus.Morse.Basic
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Exponential convergence of a negative gradient trajectory on a manifold

Let `f` be a function on a manifold `M` carrying a continuous Riemannian metric, and let `p` be a
nondegenerate critical point of `f`. Near `p` the **Morse form of Łojasiewicz's gradient
inequality** holds with the optimal exponent `1/2`:

`lam * |f y - f p| ≤ ‖grad f y‖ ^ 2`

(`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`). It is
transported from the normed-space inequality
`TauCeti.IsNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_fderiv_sq` for the coordinate
expression of `f` in the preferred chart at `p`: near `p` the differential of that expression is
bounded by a multiple of the Riemannian length of the gradient
(`TauCeti.Manifold.eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient`), so any
Łojasiewicz inequality in that chart gives one for the gradient
(`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm`). The metric
need not be adapted to the chart, nor smooth.

Now let `γ` be the maximal integral curve of `-grad f` through `x`, defined for all positive time
and converging to a critical point `p` near which such a Łojasiewicz inequality holds. Besides
nondegenerate critical points, this covers the points of Morse–Bott critical submanifolds
(`SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_mul_abs_sub_le_norm_mgradient_sq`),
where the critical points need not be isolated. The energy `f (γ t) - f p` is nonnegative
(`TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`), since `f` decreases along `γ` and tends to
`f p`. Its derivative is `-‖grad f (γ t)‖ ^ 2`, which the inequality above bounds by `-lam` times
the energy once `γ` stays near `p`, so by Grönwall's inequality the energy decays like
`exp (-lam * t)` (`TauCeti.exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient`). This is the
manifold counterpart, for an arbitrary `C¹` metric, of the vector-space theorem
`IsIntegralCurveOn.exists_sub_le_mul_exp_atTop`.

Energy decay alone does not bound the distance from `γ t` to `p`, since the Hessian at a saddle
has null directions. The distance is recovered from the Riemannian length of `γ`. Along any
stretch of time during which `γ` stays where the inequality holds, the excess
`e = f (γ t) - f p` satisfies `e' = -‖grad f‖²` and `√lam * √e ≤ ‖grad f‖`, so the length of `γ`
over that stretch is at most `2 / √lam` times the drop of `√e`
(`TauCeti.pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz`, from the scalar
bound `TauCeti.integral_le_rpow_sub_rpow_of_lojasiewicz`). This bounds the tail length of `γ`
after time `t`, and with it the Riemannian distance from `γ t` to `p`, by a multiple of
`sqrt (f (γ t) - f p)`. Hence that distance decays exponentially
(`TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`), as in
`IsIntegralCurveOn.exists_norm_sub_le_mul_exp_atTop`. The distance is
`Manifold.riemannianEDist`, the infimum of lengths of `C¹` paths; on a Riemannian manifold in the
sense of `IsRiemannianManifold` it is the ambient extended distance.

Convergence itself need not be assumed. **Łojasiewicz's convergence theorem**
(`TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`) says that a forward
trajectory converges to each of its cluster points near which the inequality above holds. Here `p`
is only a cluster point, but `f` still stays above `f p` along `γ`, so the same length bound
applies. Once `γ` comes close enough to `p`, at a time when `√e` is small, it therefore cannot
travel far enough to leave the neighbourhood, and its remaining length is small. Unlike the
convergence theorem `TauCeti.exists_tendsto_maximalIntegralCurve_neg_mgradient`, nothing is
assumed about the other critical points: they need not be isolated, as on a Morse–Bott critical
submanifold.

A forward trajectory trapped in a compact set `K` has a cluster point in `K`, which is critical. So
if the inequality holds near every critical point in `K`, the trajectory converges exponentially
fast to a critical point in `K`, in the namespace `TauCeti`
(`exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`).
This applies when the critical points in `K` are all nondegenerate
(`TauCeti.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`). In
particular every forward negative gradient trajectory of a proper Morse function bounded below
converges exponentially fast to a critical point
(`IsMorse.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`).

## Main results

* `TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm`: a
  Łojasiewicz inequality with exponent `1/2` in the preferred chart at `p` gives one for the
  Riemannian gradient.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`: the
  Łojasiewicz inequality with exponent `1/2` near a nondegenerate critical point, for the
  Riemannian gradient.
* `TauCeti.exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient`: along a forward negative
  gradient trajectory converging to a critical point with a Łojasiewicz inequality, such as a
  nondegenerate critical point, the energy decays exponentially.
* `TauCeti.exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient` and
  `TauCeti.exists_riemannianEDist_le_mul_sqrt_maximalIntegralCurve_neg_mgradient`: the tail length
  of such a trajectory, and its Riemannian distance to the limit, are bounded by a multiple of the
  square root of the energy.
* `TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`: such a
  trajectory converges to its limit exponentially fast in the Riemannian distance.
* `TauCeti.pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz`: Łojasiewicz's
  bound on the length of a trajectory along which the inequality holds.
* `TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`: Łojasiewicz's convergence
  theorem, a forward trajectory converges to a cluster point near which the inequality holds.
* `exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`
  and `TauCeti.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`:
  a forward trajectory trapped in a compact set near whose critical points the inequality holds,
  such as nondegenerate ones, converges exponentially fast to one of them.
* `IsMorse.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`:
  every forward negative gradient trajectory of a proper Morse function bounded below converges
  exponentially fast to a critical point.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87--89.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Bundle Filter MeasureTheory Set Topology TauCeti.Manifold
open scoped ContDiff ENNReal Manifold NNReal

namespace TauCeti

section Lojasiewicz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {p : M}

/-- **Łojasiewicz's gradient inequality passes from the preferred chart to the Riemannian
gradient.** If near `p` the absolute energy difference `|f y - f p|` is bounded by a multiple of
the squared norm of the differential of `f` read in the preferred extended chart at `p`, then it is
bounded by a multiple of the squared Riemannian length of the gradient of `f` at `y`, for any
continuous Riemannian metric. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm
    (h : ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤
      ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y)‖ ^ 2) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2 := by
  obtain ⟨C, -, hbd⟩ :=
    eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient (I := I) p
  exact exists_mul_le_sq_of_eventually_le_mul h (.of_forall fun _ ↦ norm_nonneg _)
    (hbd.mono fun y hy ↦ hy f)

/-- **The Morse form of Łojasiewicz's gradient inequality on a Riemannian manifold.** Near a
nondegenerate critical point `p` of `f`, the absolute energy difference `|f y - f p|` is bounded by
a multiple of the squared Riemannian length of the gradient of `f` at `y`, for any continuous
Riemannian metric. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq
    (hp : IsManifoldNondegenerateCriticalPoint I f p) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2 := by
  obtain ⟨lam, hlam, hloj⟩ :=
    ((isManifoldNondegenerateCriticalPoint_iff I).1 hp).exists_mul_abs_sub_le_norm_fderiv_sq
  refine exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm ⟨lam, hlam, ?_⟩
  filter_upwards [(continuousAt_extChartAt (I := I) p).eventually hloj,
    extChartAt_source_mem_nhds (I := I) p] with y hy hys
  simpa only [Function.comp_apply, (extChartAt I p).left_inv hys,
    (extChartAt I p).left_inv (mem_extChartAt_source p)] using hy

end Lojasiewicz

section Decay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x p : M}

/-- **The energy along a trajectory converging to a critical point with a Łojasiewicz inequality
decays exponentially.** If the maximal integral curve `γ` of `-grad f` through `x` converges to a
critical point `p` near which `lam * |f y - f p| ≤ ‖grad f y‖ ^ 2` for some `lam > 0`, then
`f (γ t) - f p ≤ C * exp (-μ * t)` for some `μ, C > 0` and all large `t`. The inequality holds near
a nondegenerate critical point
(`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`) and near a
point of a Morse–Bott critical submanifold
(`SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_mul_abs_sub_le_norm_mgradient_sq`).
-/
theorem exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hp : p ∈ criticalPoints I f)
    (hloj : ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2)
    (hconv : Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p)) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
      f (maximalIntegralCurve (-mgradient I f) x t) - f p ≤ C * Real.exp (-(μ * t)) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have hx := Ici_subset_maximalIntegralCurveInterval_neg_mgradient_of_tendsto hp hconv
  set γ := maximalIntegralCurve (-mgradient I f) x
  obtain ⟨lam, hlam, hloj⟩ := hloj
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

/-! ### Length of a trajectory and distance to its limit -/

/-- **Łojasiewicz's length bound.** Let the maximal integral curve `γ` of `-grad f` through `x` be
defined on `[a, b]`, and let `c ≤ f (γ b)`. If `lam * (f (γ t) - c) ≤ ‖grad f (γ t)‖ ^ 2` for
`t ∈ [a, b)`, with `lam > 0`, then the Riemannian length of `γ` on `[a, b]` is at most
`2 / √lam * (√(f (γ a) - c) - √(f (γ b) - c))`. -/
theorem pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz
    (hf : ContMDiff I 𝓘(ℝ) 2 f) {a b c lam : ℝ} (hlam : 0 < lam) (hab : a ≤ b)
    (hsub : Icc a b ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hc : c ≤ f (maximalIntegralCurve (-mgradient I f) x b))
    (hloj : ∀ t ∈ Ico a b, lam * (f (maximalIntegralCurve (-mgradient I f) x t) - c) ≤
      ‖mgradient I f (maximalIntegralCurve (-mgradient I f) x t)‖ ^ 2) :
    Manifold.pathELength I (maximalIntegralCurve (-mgradient I f) x) a b ≤
      ENNReal.ofReal (2 / √lam * (√(f (maximalIntegralCurve (-mgradient I f) x a) - c) -
        √(f (maximalIntegralCurve (-mgradient I f) x b) - c))) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I f) x
  set e : ℝ → ℝ := fun t ↦ f (γ t) - c
  set g : ℝ → ℝ := fun t ↦ ‖mgradient I f (γ t)‖
  -- The excess `e` of `f` over `c` has derivative `-g²`, stays nonnegative, and satisfies the
  -- scalar Łojasiewicz inequality `√lam * e ^ (1 / 2) ≤ g`.
  have he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t := fun t ht ↦
    ((hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf (hsub ht)).sub_const
      c).hasDerivWithinAt
  have he₀ : ∀ t ∈ Icc a b, 0 ≤ e t := fun t ht ↦ sub_nonneg.2 (hc.trans
    (antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf (hsub ht)
      (hsub (right_mem_Icc.2 hab)) ht.2))
  have hL : ∀ t ∈ Ico a b, √lam * e t ^ (1 / 2 : ℝ) ≤ g t := fun t ht ↦ by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul hlam.le]
    calc √(lam * e t) ≤ √(g t ^ 2) := Real.sqrt_le_sqrt (hloj t ht)
      _ = g t := Real.sqrt_sq (norm_nonneg _)
  have hint := integral_le_rpow_sub_rpow_of_lojasiewicz hab (Real.sqrt_pos.2 hlam)
    (by norm_num : (1 / 2 : ℝ) < 1) he he₀ hL
  -- The length of `γ` is the integral of its speed `g`.
  have hspeed : ∀ t ∈ uIcc a b,
      ‖curveVelocityWithin I γ (maximalIntegralCurveInterval (-mgradient I f) x) t‖ = g t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    rw [curveVelocityWithin_of_mem_nhds (isOpen_maximalIntegralCurveInterval.mem_nhds (hsub ht)),
      curveVelocity_maximalIntegralCurve_neg_mgradient hf (hsub ht), norm_neg]
  rw [(contMDiffOn_maximalIntegralCurve_neg_mgradient
    hf).pathELength_eq_ofReal_integral_norm_curveVelocityWithin hsub,
    intervalIntegral.integral_congr hspeed]
  refine ENNReal.ofReal_le_ofReal (hint.trans_eq ?_)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  simp only [e]
  field_simp

/-- The length bound of `pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz` with
`c = f p`, in the form used for convergence to an ω-limit point `p`, below which `f` stays along
the trajectory. -/
private theorem pathELength_le_of_forall_abs_le (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hle : ∀ t ∈ Ici (0 : ℝ), f p ≤ f (maximalIntegralCurve (-mgradient I f) x t))
    {lam : ℝ} (hlam : 0 < lam) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s)
    (hloj : ∀ u ∈ Ico t s, lam * |f (maximalIntegralCurve (-mgradient I f) x u) - f p| ≤
      ‖mgradient I f (maximalIntegralCurve (-mgradient I f) x u)‖ ^ 2) :
    Manifold.pathELength I (maximalIntegralCurve (-mgradient I f) x) t s ≤
      ENNReal.ofReal (2 / √lam * √(f (maximalIntegralCurve (-mgradient I f) x t) - f p)) := by
  refine (pathELength_maximalIntegralCurve_neg_mgradient_le_of_lojasiewicz hf hlam hts
    (fun u hu ↦ hx (ht.trans hu.1)) (hle s (ht.trans hts)) fun u hu ↦ ?_).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · simpa only [abs_of_nonneg (sub_nonneg.2 (hle u (ht.trans hu.1)))] using hloj u hu
  · have := Real.sqrt_nonneg (f (maximalIntegralCurve (-mgradient I f) x s) - f p)
    have : 0 ≤ 2 / √lam := by positivity
    nlinarith

variable (hp : p ∈ criticalPoints I f)
  (hloj : ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2)
  (hconv : Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p))
include hp hloj hconv

/-- **The tail length of a trajectory converging to a critical point with a Łojasiewicz inequality
is controlled by the square root of its energy.** If the maximal integral curve `γ` of `-grad f`
through `x` converges to a critical point `p` near which `lam * |f y - f p| ≤ ‖grad f y‖ ^ 2` for
some `lam > 0`, then for some `K > 0` and all large `t`, every piece of `γ` starting at time `t`
has Riemannian length at most `K * sqrt (f (γ t) - f p)`. -/
theorem exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient
    (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    ∃ K > 0, ∀ᶠ t in atTop, ∀ s,
      Manifold.pathELength I (maximalIntegralCurve (-mgradient I f) x) t s ≤
        ENNReal.ofReal (K * √(f (maximalIntegralCurve (-mgradient I f) x t) - f p)) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have hx := Ici_subset_maximalIntegralCurveInterval_neg_mgradient_of_tendsto hp hconv
  obtain ⟨lam, hlam, hloj⟩ := hloj
  -- After some time `T ≥ 0` the trajectory stays where the Łojasiewicz inequality holds, so its
  -- length after any time `t ≥ T` is at most `2 / √lam * √(f (γ t) - f p)`.
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((hconv.eventually hloj).and (eventually_ge_atTop 0))
  refine ⟨2 / √lam, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht s
  rcases le_total t s with hts | hst
  · exact pathELength_le_of_forall_abs_le hf hx
      (fun u hu ↦ le_comp_maximalIntegralCurve_neg_mgradient hf hx hconv.mapClusterPt hu) hlam
      ((hT T le_rfl).2.trans ht) hts fun u hu ↦ (hT u (ht.trans hu.1)).1
  · exact (Manifold.pathELength_mono le_rfl hst).trans (by simp)

/-- **The Riemannian distance from a trajectory to its limit is controlled by the square root of
its energy.** If the maximal integral curve `γ` of `-grad f` through `x` converges to a critical
point `p` near which `lam * |f y - f p| ≤ ‖grad f y‖ ^ 2` for some `lam > 0`, then for some
`K > 0` and all large `t`, the Riemannian distance from `γ t` to `p` is at most
`K * sqrt (f (γ t) - f p)`. -/
theorem exists_riemannianEDist_le_mul_sqrt_maximalIntegralCurve_neg_mgradient
    (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    ∃ K > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
        ENNReal.ofReal (K * √(f (maximalIntegralCurve (-mgradient I f) x t) - f p)) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I f) x
  obtain ⟨K, hK, hlen⟩ := exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient
    hp hloj hconv hf
  have hx := Ici_subset_maximalIntegralCurveInterval_neg_mgradient_of_tendsto hp hconv
  refine ⟨K, hK, ?_⟩
  filter_upwards [hlen, eventually_ge_atTop 0] with t ht ht0
  exact Manifold.riemannianEDist_le_of_tendsto_of_forall_pathELength_le
    ((contMDiffOn_maximalIntegralCurve_neg_mgradient hf).mono fun u hu ↦ hx (ht0.trans hu)) hconv
    ht

/-- **A trajectory converging to a critical point with a Łojasiewicz inequality converges
exponentially fast in the Riemannian distance.** If the maximal integral curve `γ` of `-grad f`
through `x` converges to a critical point `p` near which `lam * |f y - f p| ≤ ‖grad f y‖ ^ 2` for
some `lam > 0`, such as a nondegenerate critical point or a point of a Morse–Bott critical
submanifold, then the Riemannian distance from `γ t` to `p` is at most `C * exp (-μ * t)` for some
`μ, C > 0` and all large `t`.
This is the manifold counterpart, for an arbitrary `C¹` metric, of the vector-space theorem
`IsIntegralCurveOn.exists_norm_sub_le_mul_exp_atTop`. -/
theorem exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient
    (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
        ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  obtain ⟨K, hK, hdist⟩ := exists_riemannianEDist_le_mul_sqrt_maximalIntegralCurve_neg_mgradient
    hp hloj hconv hf
  obtain ⟨μ, hμ, C, hC, henergy⟩ :=
    exists_sub_le_mul_exp_maximalIntegralCurve_neg_mgradient hf hp hloj hconv
  refine ⟨μ / 2, by positivity, K * √C, by positivity, ?_⟩
  filter_upwards [hdist, henergy] with t ht hte
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  calc K * √(f (maximalIntegralCurve (-mgradient I f) x t) - f p)
      ≤ K * √(C * Real.exp (-(μ * t))) := by gcongr
    _ = K * √C * Real.exp (-(μ / 2 * t)) := by
        rw [Real.sqrt_mul hC.le, ← Real.exp_half, mul_assoc]
        ring_nf

end Decay

/-! ### Convergence to an ω-limit point with a Łojasiewicz inequality -/

section ClusterPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x p : M}

/-- **A trajectory cannot leave a Łojasiewicz ball once it is deep inside.** Let `f` stay above
`f p` along the forward trajectory `γ` of `-grad f`, and let the Łojasiewicz inequality hold on the
Riemannian ball of radius `r` about `p`. If at some time `t₀ ≥ 0` the point `γ t₀` lies within
`r / 2` of `p` and the length bound `2 / √lam * √(f (γ t₀) - f p)` is at most `r / 2`, then `γ`
stays in the ball after `t₀`: at a first exit time `τ`, the length of `γ` on `[t₀, τ]` would be at
most `r / 2`, which keeps `γ τ` inside the ball. -/
private theorem riemannianEDist_lt_of_lojasiewicz (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hle : ∀ t ∈ Ici (0 : ℝ), f p ≤ f (maximalIntegralCurve (-mgradient I f) x t))
    {lam : ℝ} (hlam : 0 < lam) {r : ℝ≥0}
    (hrU : ∀ y, Manifold.riemannianEDist I p y < r → lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2)
    {t₀ : ℝ} (ht₀0 : 0 ≤ t₀)
    (ht₀ : Manifold.riemannianEDist I p (maximalIntegralCurve (-mgradient I f) x t₀) < r / 2)
    (hL : ENNReal.ofReal (2 / √lam * √(f (maximalIntegralCurve (-mgradient I f) x t₀) - f p)) ≤
      r / 2)
    {s : ℝ} (hs : t₀ ≤ s) :
    Manifold.riemannianEDist I p (maximalIntegralCurve (-mgradient I f) x s) < r := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  set γ := maximalIntegralCurve (-mgradient I f) x
  have hγ₀ : ∀ {s}, CMDiff[Icc t₀ s] 1 γ :=
    (contMDiffOn_maximalIntegralCurve_neg_mgradient hf).mono
      (Icc_subset_Ici_self.trans ((Ici_subset_Ici.2 ht₀0).trans hx))
  by_contra! hsr
  -- The first time `τ ∈ [t₀, s]` at which `γ` is outside the ball.
  set F := Icc t₀ s ∩ γ ⁻¹' {y | Manifold.riemannianEDist I p y < r}ᶜ
  have hFc : IsClosed F := hγ₀.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
    (Manifold.isOpen_setOfPred_riemannianEDist_lt I p r).isClosed_compl
  have hFb : BddBelow F := ⟨t₀, fun u hu ↦ hu.1.1⟩
  have hτ : sInf F ∈ F := hFc.csInf_mem ⟨s, ⟨hs, le_rfl⟩, not_lt.2 hsr⟩ hFb
  have hin : ∀ u ∈ Ico t₀ (sInf F), Manifold.riemannianEDist I p (γ u) < r := fun u hu ↦ by
    by_contra! h
    exact (csInf_le hFb ⟨⟨hu.1, hu.2.le.trans hτ.1.2⟩, not_lt.2 h⟩).not_gt hu.2
  -- Before `τ` the trajectory stays in the ball, so its length on `[t₀, τ]` is at most `r / 2`.
  have hdist : Manifold.riemannianEDist I (γ t₀) (γ (sInf F)) ≤ r / 2 :=
    (Manifold.riemannianEDist_le_pathELength hγ₀ rfl rfl hτ.1.1).trans
      ((pathELength_le_of_forall_abs_le hf hx hle hlam ht₀0 hτ.1.1 fun u hu ↦
        hrU _ (hin u hu)).trans hL)
  refine hτ.2 ?_
  calc Manifold.riemannianEDist I p (γ (sInf F))
      ≤ Manifold.riemannianEDist I p (γ t₀) + Manifold.riemannianEDist I (γ t₀) (γ (sInf F)) :=
        Manifold.riemannianEDist_triangle
    _ < r / 2 + r / 2 :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top (by finiteness) hdist) ht₀ hdist
    _ = r := ENNReal.add_halves _

/-- **Łojasiewicz's convergence theorem.** If the maximal integral curve `γ` of `-grad f` through
`x` exists for all positive time and has a cluster point `p` as `t → ∞` near which
`lam * |f y - f p| ≤ ‖grad f y‖ ^ 2` for some `lam > 0`, then `γ` converges to `p`.

The inequality holds near a nondegenerate critical point
(`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`) and near
a point of a Morse–Bott critical submanifold
(`SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_mul_abs_sub_le_norm_mgradient_sq`),
where the critical points need not be isolated. -/
theorem tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x)
    (hp : MapClusterPt p atTop (maximalIntegralCurve (-mgradient I f) x))
    (hloj : ∃ lam > 0, ∀ᶠ y in 𝓝 p, lam * |f y - f p| ≤ ‖mgradient I f y‖ ^ 2) :
    Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  set γ := maximalIntegralCurve (-mgradient I f) x
  obtain ⟨lam, hlam, hU⟩ := hloj
  have hle : ∀ t ∈ Ici (0 : ℝ), f p ≤ f (γ t) := fun t ht ↦
    le_comp_maximalIntegralCurve_neg_mgradient hf hx hp ht
  -- The bound on the length of `γ` after time `t` tends to `0`, since `f (γ t) → f p`.
  have hL0 : Tendsto (fun t ↦ ENNReal.ofReal (2 / √lam * √(f (γ t) - f p))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ f (γ t) - f p) atTop (𝓝 (f p - f p)) :=
      (tendsto_comp_maximalIntegralCurve_neg_mgradient hf hx hp).sub_const _
    rw [sub_self] at hlim
    simpa using ENNReal.tendsto_ofReal
      ((tendsto_const_nhds (x := 2 / √lam)).mul ((Real.continuous_sqrt.tendsto 0).comp hlim))
  -- Choose a radius `r` such that the Riemannian ball of radius `r` about `p` lies where the
  -- Łojasiewicz inequality holds, then a time `t₀ ≥ 0` at which `γ` is within `r / 2` of `p` and
  -- after which the length bound is at most `r / 2`. After `t₀` the trajectory stays in the ball.
  obtain ⟨r, hr, hrU⟩ := setOfPred_riemannianEDist_lt_subset_nhds I hU
  have hr2 : (0 : ℝ≥0∞) < (r : ℝ≥0∞) / 2 := ENNReal.half_pos (by exact_mod_cast hr.ne')
  obtain ⟨T, hT⟩ := eventually_atTop.1
    ((ENNReal.tendsto_nhds_zero.1 hL0 _ hr2).and (eventually_ge_atTop 0))
  obtain ⟨t₀, ht₀, ht₀T⟩ := ((hp.frequently (eventually_riemannianEDist_lt I p hr2)).and_eventually
    (eventually_ge_atTop T)).exists
  have hstay : ∀ s ≥ t₀, Manifold.riemannianEDist I p (γ s) < r := fun s hs ↦
    riemannianEDist_lt_of_lojasiewicz hf hx hle hlam (fun y hy ↦ hrU hy) (hT t₀ ht₀T).2 ht₀
      (hT t₀ ht₀T).1 hs
  -- Hence the tail lengths of `γ` after `t₀` tend to `0`.
  refine Manifold.tendsto_of_mapClusterPt_of_forall_pathELength_le
    ((contMDiffOn_maximalIntegralCurve_neg_mgradient hf).mono hx) hp fun ε hε ↦ ?_
  filter_upwards [eventually_ge_atTop t₀, ENNReal.tendsto_nhds_zero.1 hL0 ε hε] with t ht hLt s
  rcases le_total t s with hts | hst
  · exact (pathELength_le_of_forall_abs_le hf hx hle hlam ((hT t₀ ht₀T).2.trans ht) hts
      fun u hu ↦ hrU (hstay u (ht.trans hu.1))).trans hLt
  · exact (Manifold.pathELength_mono le_rfl hst).trans (by simp)

/-- **A trapped trajectory converges exponentially fast to a critical point with a Łojasiewicz
inequality.** If the forward part of the maximal integral curve `γ` of `-grad f` through `x` stays
in a compact set `K`, and near every critical point `y` of `f` in `K` the inequality
`lam * |f z - f y| ≤ ‖grad f z‖ ^ 2` holds for some `lam > 0`, then `γ` converges to a critical
point `p` in `K`, and the Riemannian distance from `γ t` to `p` is at most `C * exp (-μ * t)` for
some `μ, C > 0` and all large `t`. The critical points in `K` need not be isolated. -/
theorem
    exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_of_lojasiewicz
    {K : Set M} (hf : ContMDiff I 𝓘(ℝ) 2 f) (hK : IsCompact K)
    (hmem : MapsTo (maximalIntegralCurve (-mgradient I f) x)
      (maximalIntegralCurveInterval (-mgradient I f) x ∩ Ici 0) K)
    (hloj : ∀ y ∈ criticalPoints I f ∩ K,
      ∃ lam > 0, ∀ᶠ z in 𝓝 y, lam * |f z - f y| ≤ ‖mgradient I f z‖ ^ 2) :
    ∃ p ∈ criticalPoints I f ∩ K,
      Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) ∧
        ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
          Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
            ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  have hx := Ici_subset_maximalIntegralCurveInterval_neg_mgradient hK hmem hf
  -- The trajectory has a cluster point in `K`, which is critical.
  obtain ⟨p, hpK, hp⟩ := hK.exists_mapClusterPt (f := atTop)
    (u := maximalIntegralCurve (-mgradient I f) x) (tendsto_principal.2
      (by filter_upwards [eventually_ge_atTop 0] with t ht using hmem ⟨hx ht, ht⟩))
  have hpc : p ∈ criticalPoints I f ∩ K :=
    ⟨mem_criticalPoints_of_mapClusterPt_maximalIntegralCurve_neg_mgradient hK hmem hf hp, hpK⟩
  have hconv := tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt hf hx hp (hloj p hpc)
  exact ⟨p, hpc, hconv,
    exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient hpc.1 (hloj p hpc)
      hconv hf⟩

end ClusterPoint

/-! ### Trapped trajectories and proper Morse functions -/

section Trapped

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M} {K : Set M}

/-- **A trapped trajectory converges exponentially fast.** If the forward part of the maximal
integral curve `γ` of `-grad f` through `x` stays in a compact set `K` all of whose critical points
are nondegenerate, then `γ` converges to a critical point `p` in `K`, and the Riemannian distance
from `γ t` to `p` is at most `C * exp (-μ * t)` for some `μ, C > 0` and all large `t`. The metric is
an arbitrary `C¹` metric, `M` need not be compact, and the limit may be a saddle. -/
theorem exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hK : IsCompact K)
    (hmem : MapsTo (maximalIntegralCurve (-mgradient I f) x)
      (maximalIntegralCurveInterval (-mgradient I f) x ∩ Ici 0) K)
    (hnd : ∀ y ∈ criticalPoints I f ∩ K, IsManifoldNondegenerateCriticalPoint I f y) :
    ∃ p ∈ criticalPoints I f ∩ K,
      Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) ∧
        ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
          Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
            ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  exact
    exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_of_lojasiewicz
      hf hK hmem fun y hy ↦ (hnd y hy).exists_mul_abs_sub_le_norm_mgradient_sq

/-- **Negative gradient trajectories of a proper Morse function converge exponentially fast.** If
`f` is a proper Morse function bounded below, the maximal integral curve of `-grad f` through any
point `x` converges to a critical point `p` of `f`, and the Riemannian distance from its value at
time `t` to `p` is at most `C * exp (-μ * t)` for some `μ, C > 0` and all large `t`, for any `C¹`
Riemannian metric. -/
theorem IsMorse.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient
    (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) (x : M) :
    ∃ p ∈ criticalPoints I f,
      Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) ∧
        ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
          Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) p ≤
            ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  have hf2 : ContMDiff I 𝓘(ℝ) 2 f := hf.contMDiff.of_le (by norm_cast)
  obtain ⟨m, hm⟩ := hbdd
  -- The forward trajectory stays in the compact band `m ≤ f ≤ f x`.
  obtain ⟨p, hp, h⟩ :=
    TauCeti.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient hf2
      (hp.isCompact_preimage (isCompact_Icc (a := m) (b := f x)))
      (fun s hs ↦
        ⟨hm (mem_range_self _), mapsTo_maximalIntegralCurve_neg_mgradient_preimage_Iic hf2 hs⟩)
      fun _ hy ↦ hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hy.1
  exact ⟨p, hp.1, h⟩

end Trapped

end TauCeti
