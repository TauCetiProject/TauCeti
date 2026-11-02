/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Continuity of an L-series on a closed half-plane of summability

If a Dirichlet series is summable at `s`, then at every point `z` with `s.re ≤ z.re` its terms
have norms at most those of the terms at `s`, so the series converges uniformly on the closed
half-plane `{z | s.re ≤ z.re}` and `LSeries a` is continuous there. Continuity along the vertical
line `s + ℝ * I` and from the right along the real axis are special cases.

Mathlib's `LSeries_differentiableOn` gives more, but only *strictly* inside the half-plane of
absolute convergence: it needs `abscissaOfAbsConv a < s.re`, whereas `LSeriesSummable a s` only
gives `abscissaOfAbsConv a ≤ s.re`. The line through a point of summability may therefore be the
boundary line of that half-plane, which is exactly the situation in the Wiener--Ikehara argument.

## Main results

* `LSeriesSummable.continuousOn_LSeries`: `LSeries a` is continuous on the closed half-plane
  `{z | s.re ≤ z.re}` whenever `LSeriesSummable a s`.
* `LSeriesSummable.continuous_LSeries_vertical`: `fun t : ℝ ↦ LSeries a (s + t * I)` is
  continuous whenever `LSeriesSummable a s`.
* `LSeriesSummable.tendsto_LSeries_nhdsGE`: at a real point of summability `σ`, the values of
  `LSeries a` along the real half-line `[σ, ∞)` tend to its value at `σ`.
-/

public section

namespace LSeriesSummable

open Complex Filter Topology

variable {a : ℕ → ℂ} {s : ℂ}

/-- A Dirichlet series summable at `s` is continuous on the closed half-plane
`{z | s.re ≤ z.re}`, including its boundary line `{z | z.re = s.re}`. When
`s.re = abscissaOfAbsConv a`, Mathlib's `LSeries_differentiableOn` says nothing on that line. -/
theorem continuousOn_LSeries (hs : LSeriesSummable a s) :
    ContinuousOn (LSeries a) {z : ℂ | s.re ≤ z.re} :=
  continuousOn_tsum
    (fun n z _ ↦ (LSeries.hasDerivAt_term a n z).continuousAt.continuousWithinAt)
    (summable_norm_iff.mpr hs) (fun n _ hz ↦ LSeries.norm_term_le_of_re_le_re a hz n)

/-- A Dirichlet series summable at `s` is continuous along the vertical line through `s`. -/
theorem continuous_LSeries_vertical (hs : LSeriesSummable a s) :
    Continuous fun t : ℝ ↦ LSeries a (s + t * I) :=
  hs.continuousOn_LSeries.comp_continuous (by fun_prop) fun t ↦ by simp

/-- Approaching a real point of summability `σ` along the real half-line `[σ, ∞)`, the values of
a Dirichlet series converge to its value at `σ`. -/
theorem tendsto_LSeries_nhdsGE {σ : ℝ} (hs : LSeriesSummable a σ) :
    Tendsto (fun τ : ℝ ↦ LSeries a τ) (𝓝[≥] σ) (𝓝 (LSeries a σ)) :=
  (hs.continuousOn_LSeries σ (by simp)).tendsto.comp <|
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun τ hτ ↦ by simpa using hτ

end LSeriesSummable
