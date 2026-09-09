/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Continuity of an L-series along a vertical line

If a Dirichlet series is summable at `s`, then at every point of the vertical line `s + ℝ * I`
its terms have exactly the same norms, so the series converges uniformly along that line and
`LSeries a` is continuous there.

Mathlib's `LSeries_differentiableOn` gives more, but only *strictly* inside the half-plane of
absolute convergence: it needs `abscissaOfAbsConv a < s.re`, whereas `LSeriesSummable a s` only
gives `abscissaOfAbsConv a ≤ s.re`. The line through a point of summability may therefore be the
boundary line of that half-plane, which is exactly the situation in the Wiener--Ikehara argument.

## Main results

* `TauCeti.LSeries.continuousOn_LSeries`: `LSeries a` is continuous on the closed half-plane
  `{z | s.re ≤ z.re}` whenever `LSeriesSummable a s`.
* `TauCeti.LSeries.continuous_LSeries_vertical`: `fun t : ℝ ↦ LSeries a (s + t * I)` is continuous
  whenever `LSeriesSummable a s`.
* `TauCeti.LSeries.tendsto_LSeries_nhdsGT`: the real one-sided limit of `LSeries a` at a real
  point of summability is the value there.
-/

public section

namespace TauCeti.LSeries

open Complex Filter Topology

variable {a : ℕ → ℂ} {s : ℂ}

/-- A Dirichlet series summable at `s` converges uniformly on the closed half-plane
`{z | s.re ≤ z.re}`, hence is continuous there.

Mathlib's `LSeries_differentiableOn` gives more on the *open* half-plane cut out by the abscissa
of absolute convergence, but says nothing on its boundary line, which is where the
Wiener--Ikehara argument works. -/
theorem continuousOn_LSeries (hs : LSeriesSummable a s) :
    ContinuousOn (LSeries a) {z : ℂ | s.re ≤ z.re} :=
  continuousOn_tsum
    (fun n z _ ↦ (_root_.LSeries.hasDerivAt_term a n z).continuousAt.continuousWithinAt)
    (summable_norm_iff.mpr hs) (fun n _ hz ↦ _root_.LSeries.norm_term_le_of_re_le_re a hz n)

/-- A Dirichlet series summable at `s` is continuous along the vertical line through `s`. -/
theorem continuous_LSeries_vertical (hs : LSeriesSummable a s) :
    Continuous fun t : ℝ ↦ LSeries a (s + t * I) := by
  refine (continuousOn_LSeries hs).comp_continuous (by fun_prop) fun t ↦ ?_
  simp

/-- Approaching a real point of summability from the right along the real axis, the values of a
Dirichlet series converge to its value there. -/
theorem tendsto_LSeries_nhdsGT {σ : ℝ} (hs : LSeriesSummable a σ) :
    Tendsto (fun τ : ℝ ↦ LSeries a τ) (𝓝[>] σ) (𝓝 (LSeries a σ)) := by
  refine Filter.Tendsto.comp (continuousOn_LSeries hs (σ : ℂ) (by simp)) ?_
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((Complex.continuous_ofReal.tendsto σ).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  simpa using hτ.le

end TauCeti.LSeries
