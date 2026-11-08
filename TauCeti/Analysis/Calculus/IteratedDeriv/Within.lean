/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Derivatives of iterated derivatives within a set

At a point `x` with `s ∈ 𝓝 x`, the `k`-th iterated derivative within a
unique-differentiability set `s` of a function that is `C^n` with `k < n` has an ordinary
derivative at `x`, namely the `(k+1)`-th iterated derivative within `s`. This upgrades
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

/-- If `g` is `C^n` within a unique-differentiability set `s` at a point `x` with `s ∈ 𝓝 x`,
then for `k < n` the `k`-th iterated derivative within `s` has derivative at `x` equal to the
`(k+1)`-th iterated derivative within `s`. -/
theorem ContDiffWithinAt.hasDerivAt_iteratedDerivWithin (hg : ContDiffWithinAt 𝕜 n g s x)
    (hk : k < n) (hs : UniqueDiffOn 𝕜 s) (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  rw [iteratedDerivWithin_succ]
  exact (hg.differentiableWithinAt_iteratedDerivWithin hk
    (by rwa [insert_eq_of_mem (mem_of_mem_nhds hx)])).hasDerivWithinAt.hasDerivAt hx

/-- If `g` is `C^n` on a unique-differentiability set `s` and `s ∈ 𝓝 x`, then for `k < n` the
`k`-th iterated derivative within `s` has derivative at `x` equal to the `(k+1)`-th iterated
derivative within `s`. -/
theorem ContDiffOn.hasDerivAt_iteratedDerivWithin (hg : ContDiffOn 𝕜 n g s) (hk : k < n)
    (hs : UniqueDiffOn 𝕜 s) (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x :=
  (hg x (mem_of_mem_nhds hx)).hasDerivAt_iteratedDerivWithin hk hs hx
