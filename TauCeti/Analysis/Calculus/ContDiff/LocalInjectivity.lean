/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local injectivity from an injective derivative within a convex set

A map on a finite-dimensional real normed space whose derivative at `x` is injective, and whose
derivative is continuous at `x`, is injective near `x`. This file proves this *within* a convex
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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {x : E} {f : E → F}

/-- Let `s` be a convex set in a finite-dimensional real normed space and `f` a map with
derivatives `f' y` within `s` at all points `y` near `x` within `s`. If `f'` is continuous within
`s` at `x` and `f' x` is injective, then `f` is injective on a neighbourhood of `x` within `s`. -/
theorem Convex.exists_nhdsWithin_injOn_of_hasFDerivWithinAt (hs : Convex ℝ s)
    {f' : E → E →L[ℝ] F} (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y)
    (hcont : ContinuousWithinAt f' s x) (hinj : Injective (f' x)) :
    ∃ t ∈ 𝓝[s] x, InjOn f t := by
  set L := f' x
  obtain ⟨K, hK, hL⟩ := (L : E →ₗ[ℝ] F).injective_iff_antilipschitz.1 hinj
  -- Near `x` within `s`, the difference `f - L` has derivative close to `f' x - L = 0`, so it is
  -- Lipschitz with constant `(2 * K)⁻¹`, half the antilipschitz modulus of `L`.
  obtain ⟨t, ht, hlip⟩ := hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
    (f := fun y ↦ f y - L y) (f' := fun y ↦ f' y - L)
    (hder.mono fun y hy ↦ hy.sub L.hasFDerivWithinAt) (hcont.sub continuousWithinAt_const)
    (2 * K)⁻¹ (by simpa [L] using hK)
  refine ⟨t, ht, fun a ha b hb hab ↦ ?_⟩
  have hsmall : ‖L (a - b)‖ ≤ ((2 * K)⁻¹ : ℝ≥0) * ‖a - b‖ := by
    have := hlip.norm_sub_le ha hb
    rwa [hab, sub_sub_sub_cancel_left, ← map_sub, ← neg_sub a b, map_neg, norm_neg] at this
  have hlarge : ‖a - b‖ ≤ K * ‖L (a - b)‖ := ZeroHomClass.bound_of_antilipschitz L hL (a - b)
  have hK' : (K : ℝ) * ((2 * K)⁻¹ : ℝ≥0) = 2⁻¹ := by
    push_cast
    field_simp
  have : ‖a - b‖ ≤ 2⁻¹ * ‖a - b‖ := by
    calc ‖a - b‖ ≤ K * (((2 * K)⁻¹ : ℝ≥0) * ‖a - b‖) := hlarge.trans (by gcongr)
      _ = 2⁻¹ * ‖a - b‖ := by rw [← mul_assoc, hK']
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  linarith [norm_nonneg (a - b)]

/-- A map that is `C¹` within a convex set `s` at a point `x ∈ s` where `s` has unique
derivatives, and whose derivative within `s` at `x` is injective, is injective on a neighbourhood
of `x` within `s`. -/
theorem ContDiffWithinAt.exists_nhdsWithin_injOn (hf : ContDiffWithinAt ℝ 1 f s x)
    (hs : Convex ℝ s) (hx : x ∈ s) (hu : UniqueDiffWithinAt ℝ s x)
    (hinj : Injective (fderivWithin ℝ f s x)) : ∃ t ∈ 𝓝[s] x, InjOn f t := by
  rw [← zero_add (1 : WithTop ℕ∞)] at hf
  obtain ⟨u, hu', -, -, f', hder, hcont⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (by simp)).1 hf
  rw [insert_eq_of_mem hx] at hu'
  have hxu : x ∈ u := mem_of_mem_nhdsWithin hx hu'
  rw [(hder x hxu).fderivWithin hu] at hinj
  exact hs.exists_nhdsWithin_injOn_of_hasFDerivWithinAt (Filter.mem_of_superset hu' hder)
    hcont.continuousWithinAt hinj
