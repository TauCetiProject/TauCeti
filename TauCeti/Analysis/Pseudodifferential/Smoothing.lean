/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Smoothing operators with compact spatial support produce smooth functions

Let `a` be a smoothing symbol on `ℝⁿ` (`TauCeti.Symbol.IsSmoothing`: its coefficient satisfies the
symbol estimates of every real order) that vanishes for positions outside a compact set. For every
real `s`, its quantization extends to a bounded operator `Op(a) : H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`
(`TauCeti.Symbol.quantizeSobolev`). This file shows that `Op(a)` sends every element of `H^s`,
including distributions of negative order, to a smooth function.

Since `a` has every real order `m'`, the same operator also maps `H^s` into `H^{s - m'}` for every
`m'`: the Sobolev extension of `Op(a)` depends only on the coefficient of `a`
(`TauCeti.Symbol.toDistr_quantizeSobolev_congr`), because two continuous extensions that agree on
the dense subspace of Schwartz functions agree everywhere. Hence `Op(a) u` lies in `H^t` for every
real `t` (`TauCeti.Symbol.IsSmoothing.memSobolev_toDistr_quantizeSobolev`), and the Sobolev
embedding `H^t ⊆ C^k`, `t > k + n / 2`
(`TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev`), makes it a smooth
function.

## Main results

* `TauCeti.Symbol.IsSmoothing.exists_contDiff_quantizeSobolev`: `Op(a) u` is a smooth function.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (operators
  with symbols of order `-∞`).
* G. B. Folland, *Real Analysis*, 2nd ed., §9.3 (the Sobolev embedding `H_s ⊆ C^k` for
  `s > k + n / 2`).
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap BesselPotentialSpace ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Smoothing operators produce smooth functions.** For a smoothing symbol `a` with compact
spatial support and every `u ∈ H^s`, `s` real, the quantization `Op(a) u` is a smooth function
`g`: it pairs with every Schwartz function `φ` as `∫ φ • g`. Taking `s` negative, this applies to
distributions that are not functions. -/
theorem IsSmoothing.exists_contDiff_quantizeSobolev {a : Symbol n V W m} (ha : a.IsSmoothing)
    (hc : a.HasCompactSpatialSupport) (s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ∃ g : CoordinateSpace n → W, ContDiff ℝ ∞ g ∧
      ∀ φ : 𝓢(CoordinateSpace n, ℂ), (a.quantizeSobolev hc s u).toDistr φ = ∫ x, φ x • g x :=
  exists_contDiff_eq_integral_of_forall_memSobolev fun t ↦
    ha.memSobolev_toDistr_quantizeSobolev hc s t u

end Symbol

end TauCeti
