/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local injectivity from an injective derivative within a convex set

A map on a finite-dimensional normed space over `ℝ` or `ℂ` (more generally, over a field `𝕜`
with `IsRCLikeNormedField 𝕜`) whose derivative at `x` is injective, and whose derivative is
continuous at `x`, is injective near `x`. This file proves this *within* a convex
set `s`, using only derivatives within `s`. The inverse function theorem is not available there,
since `s` need not be open, but the mean value inequality is: near `x` within `s`, the map
differs from its derivative `L` at `x` by a map with small Lipschitz constant, while `L` is
antilipschitz.

The relative form is what applies to a manifold with boundary or corners, read in an extended
chart, where the coordinate expression of a `C¹` map is only `C¹` within the convex range of the
model with corners.

## Main results

* `Convex.exists_nhdsWithin_injOn_of_hasFDerivWithinAt`: a map with derivatives within a convex
  set `s` near `x`, continuous within `s` at `x` and injective at `x`, is injective on a
  neighbourhood of `x` within `s`.
* `ContDiffWithinAt.exists_nhdsWithin_injOn`: the same for a map that is `C¹` within `s` at
  `x ∈ s`, with injective derivative within `s` at `x`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 4, where the local injectivity of immersions is derived from the rank
  theorem on open sets.
-/

public section

open Function Set Filter
open scoped NNReal Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set E} {x : E} {f : E → F}

/-- Let `s` be a convex set in a finite-dimensional normed space over `ℝ` or `ℂ` and `f` a map
with derivatives `f' y` within `s` at all points `y` near `x` within `s`. If `f'` is continuous
within `s` at `x` and `f' x` is injective, then `f` is injective on a neighbourhood of `x`
within `s`. -/
theorem Convex.exists_nhdsWithin_injOn_of_hasFDerivWithinAt (hs : Convex ℝ s)
    {f' : E → E →L[𝕜] F} (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y)
    (hcont : ContinuousWithinAt f' s x) (hinj : Injective (f' x)) :
    ∃ t ∈ 𝓝[s] x, InjOn f t := by
  let := IsRCLikeNormedField.rclike 𝕜
  set L := f' x
  obtain ⟨K, hK, hL⟩ := (L : E →ₗ[𝕜] F).injective_iff_antilipschitz.1 hinj
  -- Near `x` within `s`, the difference `f - L` has derivative close to `f' x - L = 0`, so it is
  -- Lipschitz with constant `(2 * K)⁻¹`, below the antilipschitz modulus `K⁻¹` of `L`.
  obtain ⟨t, ht, hlip⟩ := hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
    (f := fun y ↦ f y - L y) (f' := fun y ↦ f' y - L)
    (hder.mono fun y hy ↦ hy.sub L.hasFDerivWithinAt) (hcont.sub continuousWithinAt_const)
    (2 * K)⁻¹ (by simpa [L] using hK)
  refine ⟨t, ht, injOn_iff_injective.2 ?_⟩
  exact ((hL.domRestrict t).add_sub_lipschitzWith (g := t.domRestrict f) hlip.to_restrict
    (by gcongr; exact lt_two_mul_self hK)).injective

/-- A map that is `C¹` within a convex set `s` at a point `x ∈ s` where `s` has unique
derivatives, and whose derivative within `s` at `x` is injective, is injective on a neighbourhood
of `x` within `s`. -/
theorem ContDiffWithinAt.exists_nhdsWithin_injOn (hf : ContDiffWithinAt 𝕜 1 f s x)
    (hs : Convex ℝ s) (hx : x ∈ s) (hu : UniqueDiffWithinAt 𝕜 s x)
    (hinj : Injective (fderivWithin 𝕜 f s x)) : ∃ t ∈ 𝓝[s] x, InjOn f t := by
  rw [← zero_add (1 : WithTop ℕ∞)] at hf
  obtain ⟨u, hu', -, -, f', hder, hcont⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (by simp)).1 hf
  rw [insert_eq_of_mem hx] at hu'
  have hxu : x ∈ u := mem_of_mem_nhdsWithin hx hu'
  rw [(hder x hxu).fderivWithin hu] at hinj
  exact hs.exists_nhdsWithin_injOn_of_hasFDerivWithinAt (Filter.mem_of_superset hu' hder)
    hcont.continuousWithinAt hinj
