/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Derivatives of iterated derivatives within a set

At a point `x` with `s ∈ 𝓝 x`, the `k`-th iterated derivative within `s` of a function that is
`C^n` with `k < n` has an ordinary derivative at `x`, namely the `(k+1)`-th iterated derivative
within `s`. This upgrades
Mathlib's `ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin` to a `HasDerivAt`
statement with an explicit derivative.

## Main declarations

* `ContDiffWithinAt.hasDerivAt_iteratedDerivWithin`: the pointwise statement.
* `ContDiffOn.hasDerivAt_iteratedDerivWithin`: the same, from smoothness on all of `s`.

For the plain fundamental-theorem identity on a compact interval use Mathlib's
`intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc` together with
`iteratedDerivWithin_one`.
-/

public section

open Set
open scoped ContDiff Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {g : 𝕜 → E} {s : Set 𝕜} {x : 𝕜} {n : ℕ∞ω} {k : ℕ}

/-- If `g` is `C^n` within `s` at a point `x` with `s ∈ 𝓝 x`, then for `k < n` the `k`-th
iterated derivative within `s` has derivative at `x` equal to the `(k+1)`-th iterated derivative
within `s`. -/
theorem ContDiffWithinAt.hasDerivAt_iteratedDerivWithin (hg : ContDiffWithinAt 𝕜 n g s x)
    (hk : k < n) (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  -- Near `x` the set `s` agrees with its interior, which is open and so uniquely differentiable.
  have hu : interior s ∈ 𝓝 x := interior_mem_nhds.2 hx
  have hev (j : ℕ) : iteratedDerivWithin j g s =ᶠ[𝓝 x] iteratedDerivWithin j g (interior s) := by
    have hset : s =ᶠ[𝓝 x] interior s := by
      filter_upwards [hu] with y hy
      exact ⟨fun _ => hy, fun _ => interior_subset hy⟩
    filter_upwards [iteratedFDerivWithin_eventually_congr_set (𝕜 := 𝕜) (f := g) hset j] with y hy
    simp only [iteratedDerivWithin_eq_iteratedFDerivWithin, hy]
  have h : HasDerivAt (iteratedDerivWithin k g (interior s))
      (iteratedDerivWithin (k + 1) g (interior s) x) x := by
    rw [iteratedDerivWithin_succ]
    exact ((hg.mono interior_subset).differentiableWithinAt_iteratedDerivWithin hk
      (by
        rw [insert_eq_of_mem (mem_of_mem_nhds hu)]
        exact isOpen_interior.uniqueDiffOn)
      ).hasDerivWithinAt.hasDerivAt hu
  rw [(hev (k + 1)).eq_of_nhds]
  exact h.congr_of_eventuallyEq (hev k)

/-- If `g` is `C^n` on `s` and `s ∈ 𝓝 x`, then for `k < n` the `k`-th iterated derivative within
`s` has derivative at `x` equal to the `(k+1)`-th iterated derivative within `s`. -/
theorem ContDiffOn.hasDerivAt_iteratedDerivWithin (hg : ContDiffOn 𝕜 n g s) (hk : k < n)
    (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x :=
  (hg x (mem_of_mem_nhds hx)).hasDerivAt_iteratedDerivWithin hk hx
