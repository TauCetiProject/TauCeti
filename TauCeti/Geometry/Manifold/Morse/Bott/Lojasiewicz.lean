/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Analysis.Calculus.Morse.Bott
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.Morse.Bott.Lemma
import TauCeti.Geometry.Manifold.Morse.ExponentialConvergence

/-!
# Łojasiewicz's gradient inequality near a Morse–Bott critical submanifold

Let `i : S → M` be a Morse–Bott critical submanifold of a function `f` on a boundaryless manifold
`M` carrying a continuous Riemannian metric
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`). This file proves that near every
point `i s` the **Łojasiewicz inequality with exponent `1 / 2`** holds for the Riemannian gradient,

`lam * |f y - f (i s)| ≤ ‖grad f y‖ ^ 2`,

and that, when `S` is compact and connected, a single constant `lam` works on a whole
neighbourhood of the image of `i`, along which `f` takes a single value. For an isolated critical
point this is the Morse form of the inequality,
`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_mul_abs_sub_le_norm_mgradient_sq`. Here the
critical points are not isolated, and the inequality is the estimate that controls negative
gradient trajectories approaching the submanifold: while a trajectory stays where it holds, the
drop of `f` bounds its length, which is how one shows that such trajectories converge to single
points of the submanifold rather than drifting along it, and so gives the spaces of trajectories
between the critical submanifolds of a Morse–Bott function their endpoint maps. That convergence
argument is not part of this file.

The proof reads `f` in a slice chart of the submanifold, in which `i` is the zero section of
`E' × F` (`SmoothEmbedding.IsNondegenerateCriticalSubmanifold.sliceChart_criticalZeroSection`).
There the coordinate expression has a critical zero section whose Hessian kernel consists of base
directions, and the inequality holds by `TauCeti.exists_mul_abs_sub_le_norm_fderiv_sq_of_ker_le`.
It is transported to the extended chart at `i s` through the `C¹` chart transition
(`TauCeti.exists_mul_abs_sub_le_norm_fderiv_sq_of_comp`), and from there to the Riemannian
gradient (`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_comp_extChartAt_symm`).

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_mul_abs_sub_le_norm_mgradient_sq`: the Łojasiewicz inequality near a point of a
  Morse–Bott critical submanifold.
* `exists_mul_abs_sub_le_norm_mgradient_sq_nhdsSet`: the same with one constant on a neighbourhood
  of a compact connected Morse–Bott critical submanifold.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87--89.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott trajectory spaces and their endpoint
  maps).
-/

public section

open Bundle Filter Function Manifold Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M}

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-- **Łojasiewicz's gradient inequality near a Morse–Bott critical submanifold.** If `i : S → M`
is a Morse–Bott critical submanifold of `f`, with `i` of class `C²`, then near each point `i s`
the absolute energy difference `|f y - f (i s)|` is bounded by a multiple of the squared Riemannian
length of the gradient of `f` at `y`, for any continuous Riemannian metric. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq (hi : i.IsNondegenerateCriticalSubmanifold f)
    (hn : 2 ≤ n) (s : S) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 (i s), lam * |f y - f (i s)| ≤ ‖mgradient I f y‖ ^ 2 := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  -- Slice charts of `i` at `s`, with complement `F`: `h.codChart` is a chart of `M` and
  -- `h.equiv : E' × F ≃ E` straightens the submanifold to the zero section, where the coordinate
  -- expression of `f` satisfies the inequality.
  let F := i.isImmersion.complement
  have h : IsImmersionAtOfComplement F J I n i s :=
    i.isImmersion.isImmersionOfComplement_complement s
  obtain ⟨hxe, hxL, hga, hcrit, hker⟩ := hi.sliceChart_criticalZeroSection h hn
  have : FiniteDimensional ℝ (E' × F) := h.equiv.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ F :=
    Module.Finite.of_surjective (LinearMap.snd ℝ E' F) LinearMap.snd_surjective
  obtain ⟨lam, hlam, hloj⟩ := exists_mul_abs_sub_le_norm_fderiv_sq_of_ker_le hga hcrit hker
  have he1 : h.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) (IsManifold.maximalAtlas_subset_of_le hn
      h.codChart_mem_maximalAtlas)
  have hfz₀ : f ((h.codChart.extend I).symm (h.equiv (h.domChart.extend J s, 0))) = f (i s) := by
    rw [← hxL, h.codChart.extend_left_inv hxe]
  exact exists_mul_abs_sub_le_norm_mgradient_sq_of_mem_maximalAtlas he1 hxe h.equiv hxL
    (hi.contMDiffAt s) hlam (by simpa only [comp_apply, hfz₀] using hloj)

/-- **Łojasiewicz's gradient inequality near a compact connected Morse–Bott critical
submanifold.** If `i : S → M` is a Morse–Bott critical submanifold of `f`, with `S` compact and
connected and `i` of class `C²`, then `f` takes a single value `f (i s₀)` on the image of `i`, and
a single constant `lam > 0` bounds `lam * |f y - f (i s₀)|` by the squared Riemannian length of
the gradient of `f` on a whole neighbourhood of the image, for any continuous Riemannian
metric. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq_nhdsSet [IsManifold J 1 S] [CompactSpace S]
    [PreconnectedSpace S] (hi : i.IsNondegenerateCriticalSubmanifold f) (hn : 2 ≤ n) (s₀ : S) :
    ∃ lam > 0, ∀ᶠ y in 𝓝ˢ (range i), lam * |f y - f (i s₀)| ≤ ‖mgradient I f y‖ ^ 2 := by
  -- The function is constant on the image, since it is locally constant along `i`.
  have hconst (s : S) : f (i s) = f (i s₀) :=
    (hi.isLocallyConstant_comp (by rintro rfl; simp at hn)).apply_eq_of_preconnectedSpace s s₀
  refine (isCompact_range i.isEmbedding.continuous).induction_on
    (p := fun K ↦ ∃ lam > 0, ∀ᶠ y in 𝓝ˢ K, lam * |f y - f (i s₀)| ≤ ‖mgradient I f y‖ ^ 2)
    ⟨1, one_pos, by simp⟩ (fun K K' hKK' ⟨lam, hlam, hK'⟩ ↦ ⟨lam, hlam, hK'.filter_mono
      (nhdsSet_mono hKK')⟩) (fun K K' ⟨lam, hlam, hK⟩ ⟨lam', hlam', hK'⟩ ↦ ?_) ?_
  · -- Two neighbourhoods combine with the smaller constant.
    refine ⟨min lam lam', lt_min hlam hlam', ?_⟩
    rw [nhdsSet_union, eventually_sup]
    exact ⟨hK.mono fun y hy ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)).trans
      hy, hK'.mono fun y hy ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (abs_nonneg _)).trans hy⟩
  · -- Each point of the image has an open neighbourhood on which the inequality holds.
    rintro _ ⟨s, rfl⟩
    obtain ⟨lam, hlam, hloj⟩ := hi.exists_mul_abs_sub_le_norm_mgradient_sq hn s
    obtain ⟨U, hU, hUo, hsU⟩ := eventually_nhds_iff.1 hloj
    exact ⟨U, mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hsU), lam, hlam,
      hUo.mem_nhdsSet.2 subset_rfl |> fun hmem ↦ eventually_of_mem hmem fun y hy ↦
        hconst s ▸ hU y hy⟩

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

end TauCeti
