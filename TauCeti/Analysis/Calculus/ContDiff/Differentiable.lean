/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Eventual differentiability of `C^n` maps

Because `ContDiffWithinAt 𝕜 1 f s x` propagates to a `𝓝[insert x s] x`-neighborhood
(`ContDiffWithinAt.eventually`) and implies `DifferentiableWithinAt`, any map that is `C^n` at (or
within `s` at) `x` with `1 ≤ n` is differentiable near `x`. Lowering to order `1` first avoids the
`n ≠ ∞` restriction of `ContDiffAt.eventually`, so both `n = ∞` and `n = ω` are covered.

## Main declarations

* `ContDiffWithinAt.eventually_differentiableWithinAt`: `C^n` within `s` at `x` (`1 ≤ n`) implies
  `DifferentiableWithinAt` eventually in `𝓝[insert x s] x`.
* `ContDiffAt.eventually_differentiableAt`: `C^n` at `x` (`1 ≤ n`) implies `DifferentiableAt`
  eventually in `𝓝 x`.
* `ContDiffAt.eventually_differentiableAt_comp`: if `f` is `C^n` at `g a` (`1 ≤ n`) and `g` is
  continuous at `a`, then `f` is differentiable at `g z` for all `z` near `a`.
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

/-- If `f` is `C^n` at `g a` with `1 ≤ n` and `g` is continuous at `a`, then `f` is differentiable
at `g z` for all `z` near `a`. -/
theorem ContDiffAt.eventually_differentiableAt_comp {α : Type*} [TopologicalSpace α] {g : α → E}
    {a : α} (hf : ContDiffAt 𝕜 n f (g a)) (hg : ContinuousAt g a) (hn : 1 ≤ n) :
    ∀ᶠ z in 𝓝 a, DifferentiableAt 𝕜 f (g z) :=
  hg.eventually (hf.eventually_differentiableAt hn)

end
