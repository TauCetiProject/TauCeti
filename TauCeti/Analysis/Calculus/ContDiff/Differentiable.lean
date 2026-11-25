/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Differentiability of `C^n` maps

Because `ContDiffWithinAt 𝕜 1 f s x` propagates to a `𝓝[insert x s] x`-neighborhood
(`ContDiffWithinAt.eventually`) and implies `DifferentiableWithinAt`, any map that is `C^n` at (or
within `s` at) `x` with `1 ≤ n` is differentiable near `x`. Lowering to order `1` first avoids the
`n ≠ ∞` restriction of `ContDiffAt.eventually`, so both `n = ∞` and `n = ω` are covered. On an
open set, the iterated derivatives of order `m < n` of a `C^n` map are differentiable.

## Main declarations

* `ContDiffWithinAt.eventually_differentiableWithinAt`: `C^n` within `s` at `x` (`1 ≤ n`) implies
  `DifferentiableWithinAt` eventually in `𝓝[insert x s] x`.
* `ContDiffAt.eventually_differentiableAt`: `C^n` at `x` (`1 ≤ n`) implies `DifferentiableAt`
  eventually in `𝓝 x`.
* `ContDiffAt.differentiableAt_deriv_two`: the derivative of a function of one variable that is
  `C²` at `x` is differentiable at `x`.
* `ContDiffOn.differentiableOn_iteratedFDeriv_of_isOpen`: a map `C^n` on an open set has
  differentiable iterated derivatives of order `m < n` there.
* `ContDiffOn.continuousOn_fderivWithin_of_inter`: the derivative within a set of unique
  differentiability `s` of a `C¹` map on `s ∩ O`, for `O` open, is continuous on `s ∩ O`.
* `ContDiffOn.exists_eventually_norm_fderiv_le`: a `C¹` map on a set of unique differentiability
  `s` has a locally bounded derivative at the interior points of `s`.
-/

public section

open scoped ContDiff Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} {f : E → F} {s : Set E} {x : E}

/-- If `f` is `C^n` within `s` at `x` with `1 ≤ n`, then `f` is differentiable within `s` at all
points in a `𝓝[insert x s] x`-neighborhood of `x`. -/
theorem ContDiffWithinAt.eventually_differentiableWithinAt
    (hf : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    ∀ᶠ y in 𝓝[insert x s] x, DifferentiableWithinAt 𝕜 f s y :=
  ((hf.of_le hn).eventually (by simp)).mono fun _ hy ↦ hy.differentiableWithinAt one_ne_zero

/-- If `f` is `C^n` at `x` with `1 ≤ n`, then `f` is differentiable on a neighborhood of `x`. -/
theorem ContDiffAt.eventually_differentiableAt (hf : ContDiffAt 𝕜 n f x) (hn : 1 ≤ n) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  ((hf.of_le hn).eventually (by simp)).mono fun _ hy ↦ hy.differentiableAt_one

/-- The derivative of a function of one variable that is `C²` at `x` is differentiable at `x`. -/
theorem ContDiffAt.differentiableAt_deriv_two {f : 𝕜 → F} {x : 𝕜} (hf : ContDiffAt 𝕜 2 f x) :
    DifferentiableAt 𝕜 (deriv f) x :=
  (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- A map that is `C^n` on an open set has differentiable iterated derivatives of every order
`m < n` there. -/
theorem ContDiffOn.differentiableOn_iteratedFDeriv_of_isOpen {m : ℕ} (hf : ContDiffOn 𝕜 n f s)
    (hmn : m < n) (hs : IsOpen s) : DifferentiableOn 𝕜 (iteratedFDeriv 𝕜 m f) s :=
  (hf.differentiableOn_iteratedFDerivWithin hmn hs.uniqueDiffOn).congr fun _ hx ↦
    (iteratedFDerivWithin_of_isOpen m hs hx).symm

/-- If `f` is `C¹` on the part `s ∩ O` of a set of unique differentiability `s` in an open set `O`,
its derivative within `s` is continuous on `s ∩ O`. -/
theorem ContDiffOn.continuousOn_fderivWithin_of_inter {O : Set E} (hf : ContDiffOn 𝕜 n f (s ∩ O))
    (hs : UniqueDiffOn 𝕜 s) (hO : IsOpen O) (hn : 1 ≤ n) :
    ContinuousOn (fderivWithin 𝕜 f s) (s ∩ O) :=
  (hf.continuousOn_fderivWithin (hs.inter hO) hn).congr
    fun _ hz ↦ (fderivWithin_inter (hO.mem_nhds hz.2)).symm

/-- A map `C^n` (`1 ≤ n`) on a set of unique differentiability `s` is, near each point of `s`,
differentiable with a uniformly bounded derivative at the interior points of `s`. -/
theorem ContDiffOn.exists_eventually_norm_fderiv_le (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (hn : 1 ≤ n) (hx : x ∈ s) :
    ∃ B, 0 ≤ B ∧ ∀ᶠ y in 𝓝[s] x, y ∈ interior s →
      DifferentiableAt 𝕜 f y ∧ ‖fderiv 𝕜 f y‖ ≤ B := by
  refine ⟨‖fderivWithin 𝕜 f s x‖ + 1, by positivity, ?_⟩
  filter_upwards [(hf.continuousOn_fderivWithin hs hn x hx).norm.eventually
    (gt_mem_nhds (lt_add_one _))] with y hy hys
  -- at an interior point, `fderivWithin` is `fderiv`
  have hsy := mem_interior_iff_mem_nhds.1 hys
  refine ⟨((hf.contDiffAt hsy).of_le hn).differentiableAt_one, ?_⟩
  rw [← fderivWithin_of_mem_nhds hsy]
  exact hy.le

end
