/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
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

For a Morse–Bott function, presented by a family `i a : S a → M` of critical submanifolds
(`TauCeti.IsMorseBottFamily`), the inequality therefore holds near every critical point. The
critical points are not isolated, so for a merely smooth function a trapped trajectory need not
converge; here it does, by Łojasiewicz's theorem
(`TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`), which needs the inequality
only at a cluster point. So if `f` is proper and bounded below, every forward negative gradient
trajectory converges exponentially fast to a point `i a s` of one of the critical submanifolds. On
a compact manifold the same holds in backward time, and the forward limit, as well as the backward
limit, of each trajectory lies on exactly one critical submanifold: every point lies in the stable
set, and in the unstable set, of exactly one critical submanifold. These limits are the source and
target of a trajectory between critical submanifolds.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_mul_abs_sub_le_norm_mgradient_sq`: the Łojasiewicz inequality with exponent `1 / 2`
  near a point of a Morse–Bott critical submanifold, for the Riemannian gradient.
* `exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`: a trajectory of
  `-grad f` converging to a point of the submanifold converges to it exponentially fast.

In the namespace `TauCeti.IsMorseBottFamily`:

* `exists_mul_abs_sub_le_norm_mgradient_sq`: the Łojasiewicz inequality with exponent `1 / 2`
  near every critical point of a Morse–Bott function.
* `exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`: every
  forward negative gradient trajectory of a proper Morse–Bott function bounded below converges
  exponentially fast to a point of a critical submanifold.
* `exists_tendsto_atBot_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`: on a
  compact manifold, the same in backward time.
* `existsUnique_exists_tendsto_maximalIntegralCurve_neg_mgradient` and
  `existsUnique_exists_tendsto_atBot_maximalIntegralCurve_neg_mgradient`: on a compact manifold,
  the forward and the backward limit of each trajectory lie on exactly one critical submanifold.

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

namespace IsMorseBottFamily

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  [∀ a, (J a).Boundaryless] {S : ι → Type*} [∀ a, TopologicalSpace (S a)]
  [∀ a, ChartedSpace (H' a) (S a)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {n : ℕ∞ω} {i : ∀ a, SmoothEmbedding (J a) I n (S a) M}

/-- **The Łojasiewicz inequality for a Morse–Bott function.** If the family `i` of `C²` embeddings
exhibits `f` as a Morse–Bott function, then near every critical point `y` of `f` the absolute
energy difference `|f z - f y|` is bounded by a multiple of the squared Riemannian length of the
gradient of `f` at `z`, for any continuous Riemannian metric. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (h : IsMorseBottFamily i f) (hn : 2 ≤ n) {y : M} (hy : y ∈ criticalPoints I f) :
    ∃ lam > 0, ∀ᶠ z in 𝓝 y, lam * |f z - f y| ≤ ‖mgradient I f z‖ ^ 2 := by
  obtain ⟨a, s, rfl⟩ := h.mem_criticalPoints_iff.1 hy
  exact (h.isNondegenerateCriticalSubmanifold a).exists_mul_abs_sub_le_norm_mgradient_sq hn s

variable [T2Space M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Negative gradient trajectories of a proper Morse–Bott function converge exponentially
fast.** If the family `i` of `C²` embeddings exhibits a proper function `f`, bounded below, as a
Morse–Bott function, the maximal integral curve of `-grad f` through any point `x` converges to a
point `i a s` of one of its critical submanifolds, and the Riemannian distance from its value at
time `t` to `i a s` is at most `C * exp (-μ * t)` for some `μ, C > 0` and all large `t`, for any
`C¹` Riemannian metric. -/
theorem exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient
    (h : IsMorseBottFamily i f) (hn : 2 ≤ n) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (x : M) :
    ∃ a s, Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 (i a s)) ∧
      ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atTop,
        Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) (i a s) ≤
          ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  have hf2 : ContMDiff I 𝓘(ℝ) 2 f := h.contMDiff.of_le (by norm_cast)
  obtain ⟨m, hm⟩ := hbdd
  -- The forward trajectory stays in the compact band `m ≤ f ≤ f x`.
  obtain ⟨p, hpc, hconv⟩ :=
    exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_of_lojasiewicz
      hf2 (hp.isCompact_preimage (isCompact_Icc (a := m) (b := f x)))
      (fun s hs ↦
        ⟨hm (mem_range_self _), mapsTo_maximalIntegralCurve_neg_mgradient_preimage_Iic hf2 hs⟩)
      fun y hy ↦ h.exists_mul_abs_sub_le_norm_mgradient_sq hn hy.1
  obtain ⟨a, s, rfl⟩ := h.mem_criticalPoints_iff.1 hpc.1
  exact ⟨a, s, hconv⟩

/-- **Negative gradient trajectories of a Morse–Bott function on a compact manifold converge in
backward time.** If the family `i` of `C²` embeddings exhibits `f` as a Morse–Bott function on a
compact manifold, the maximal integral curve of `-grad f` through any point `x` converges as
`t → -∞` to a point `i a s` of one of its critical submanifolds, and the Riemannian distance from
its value at time `t` to `i a s` is at most `C * exp (μ * t)` for some `μ, C > 0` and all `t` near
`-∞`. -/
theorem exists_tendsto_atBot_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient
    [CompactSpace M] (h : IsMorseBottFamily i f) (hn : 2 ≤ n) (x : M) :
    ∃ a s, Tendsto (maximalIntegralCurve (-mgradient I f) x) atBot (𝓝 (i a s)) ∧
      ∃ μ > 0, ∃ C > 0, ∀ᶠ t in atBot,
        Manifold.riemannianEDist I (maximalIntegralCurve (-mgradient I f) x t) (i a s) ≤
          ENNReal.ofReal (C * Real.exp (μ * t)) := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have hf2 : ContMDiff I 𝓘(ℝ) 2 f := h.contMDiff.of_le (by norm_cast)
  -- Reversing time turns the trajectory of `-grad f` into the trajectory of `-grad (-f)`, and the
  -- same family exhibits `-f` as a Morse–Bott function.
  have hrev : maximalIntegralCurve (-mgradient I (-f)) x =
      maximalIntegralCurve (-mgradient I f) x ∘ (· * -1) :=
    maximalIntegralCurve_neg_mgradient_neg hf2
      (isMIntegralCurve_maximalIntegralCurve (contMDiff_neg_mgradient_one hf2))
  obtain ⟨a, s, hlim, μ, hμ, C, hC, hrate⟩ :=
    h.neg.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient hn
      h.neg.contMDiff.continuous.isProperMap (isCompact_range h.neg.contMDiff.continuous).bddBelow
      x
  rw [hrev] at hlim hrate
  have hbot : Tendsto (fun t : ℝ ↦ t * -1) atBot atTop := by
    simpa only [mul_neg_one] using tendsto_neg_atBot_atTop
  refine ⟨a, s, ?_, μ, hμ, C, hC, ?_⟩
  · simpa [Function.comp_def] using hlim.comp hbot
  · filter_upwards [hbot.eventually hrate] with t ht
    simpa [Function.comp_def, mul_comm μ t] using ht

omit [I.Boundaryless] [∀ a, (J a).Boundaryless]
  [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x] in
/-- The limits along a nontrivial filter of the trajectory through a point lie on at most one
critical submanifold of a Morse–Bott function, since distinct critical submanifolds are disjoint. -/
private theorem eq_of_tendsto_maximalIntegralCurve (h : IsMorseBottFamily i f) {l : Filter ℝ}
    [l.NeBot] {x : M} {a b : ι} {s : S a} {s' : S b}
    (ha : Tendsto (maximalIntegralCurve (-mgradient I f) x) l (𝓝 (i a s)))
    (hb : Tendsto (maximalIntegralCurve (-mgradient I f) x) l (𝓝 (i b s'))) : a = b := by
  by_contra hab
  exact disjoint_left.1 (h.pairwise_disjoint_range hab) (mem_range_self s)
    (tendsto_nhds_unique ha hb ▸ mem_range_self s')

/-- **Every point lies in the stable set of exactly one critical submanifold.** If the family `i`
of `C²` embeddings exhibits `f` as a Morse–Bott function on a compact manifold, the maximal
integral curve of `-grad f` through any point `x` converges as `t → ∞` to a point of exactly one
critical submanifold `i a`. -/
theorem existsUnique_exists_tendsto_maximalIntegralCurve_neg_mgradient [CompactSpace M]
    (h : IsMorseBottFamily i f) (hn : 2 ≤ n) (x : M) :
    ∃! a, ∃ s, Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 (i a s)) := by
  obtain ⟨a, s, hlim, -⟩ :=
    h.exists_tendsto_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient hn
      h.contMDiff.continuous.isProperMap (isCompact_range h.contMDiff.continuous).bddBelow x
  exact ⟨a, ⟨s, hlim⟩, fun b ⟨s', hb⟩ ↦ (h.eq_of_tendsto_maximalIntegralCurve hlim hb).symm⟩

/-- **Every point lies in the unstable set of exactly one critical submanifold.** If the family
`i` of `C²` embeddings exhibits `f` as a Morse–Bott function on a compact manifold, the maximal
integral curve of `-grad f` through any point `x` converges as `t → -∞` to a point of exactly one
critical submanifold `i a`. -/
theorem existsUnique_exists_tendsto_atBot_maximalIntegralCurve_neg_mgradient [CompactSpace M]
    (h : IsMorseBottFamily i f) (hn : 2 ≤ n) (x : M) :
    ∃! a, ∃ s, Tendsto (maximalIntegralCurve (-mgradient I f) x) atBot (𝓝 (i a s)) := by
  obtain ⟨a, s, hlim, -⟩ :=
    h.exists_tendsto_atBot_and_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient hn x
  exact ⟨a, ⟨s, hlim⟩, fun b ⟨s', hb⟩ ↦ (h.eq_of_tendsto_maximalIntegralCurve hlim hb).symm⟩

end IsMorseBottFamily

end TauCeti
