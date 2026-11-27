/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Meromorphic.Counting.Basic
import TauCeti.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# The zero count and the logarithmic counting function

For a function `f` on a proper nontrivially normed field,
`TauCeti.zeroCount f univ (closedBall 0 r)` is the unintegrated count `n(r)` of the zeros of `f` in
the closed disc of radius `r`, with multiplicity. Its log-weighted integral is
`ValueDistribution.logCounting f 0`, the logarithmic counting function of the positive part of the
divisor of `f`, and not the signed
`Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f univ)`, in which poles count
negatively:

* `TauCeti.logCounting_zero_eq_integral_zeroCount`: for `0 ≤ r`,
  `ValueDistribution.logCounting f 0 r = ∫ t in 0..r, (n(t) - n(0)) / t + n(0) * log r`;
* `TauCeti.zeroCount_mul_log_le_logCounting_sub`: for all positive radii `r` and `R`,
  `n(r) * log (R / r) ≤ ValueDistribution.logCounting f 0 R - ValueDistribution.logCounting f 0 r`.

They are the divisor-level statements `Function.locallyFinsuppWithin.logCounting_eq_integral` and
`Function.locallyFinsuppWithin.finsum_mem_closedBall_mul_log_le_logCounting_sub` for the positive
part of the divisor, whose counting function is the zero count
(`TauCeti.zeroCount_eq_finsum_posPart`).

## References

* S. Lang, *Introduction to Complex Hyperbolic Spaces*, Springer, 1987, §VI.1.
* J. Noguchi, J. Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
  Approximation*, Springer, 2014, §1.1.
-/

public section

open Metric Set

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The logarithmic counting function of the zeros is the log-weighted integral of the zero
count.** With `n(t) = zeroCount f univ (closedBall 0 t)`, for every `0 ≤ r`,
`ValueDistribution.logCounting f 0 r = ∫ t in 0..r, (n(t) - n(0)) / t + n(0) * log r`. -/
theorem logCounting_zero_eq_integral_zeroCount (f : 𝕜 → F) {r : ℝ} (hr : 0 ≤ r) :
    ValueDistribution.logCounting f 0 r =
      (∫ t in (0 : ℝ)..r, ((zeroCount f univ (closedBall 0 t) : ℝ) -
        zeroCount f univ (closedBall 0 0)) / t) +
        zeroCount f univ (closedBall 0 0) * Real.log r := by
  have h0 : (zeroCount f univ (closedBall 0 0) : ℝ) = ((MeromorphicOn.divisor f univ)⁺ 0 : ℝ) := by
    rw [zeroCount_eq_finsum_posPart, closedBall_zero, finsum_mem_singleton]
  rw [ValueDistribution.logCounting_zero, h0]
  simp only [zeroCount_eq_finsum_posPart]
  exact Function.locallyFinsuppWithin.logCounting_eq_integral _ hr

/-- **The zero count against the logarithmic counting function.** For positive radii `r` and `R`,
the zero count `n(r) = zeroCount f univ (closedBall 0 r)` satisfies
`n(r) * log (R / r) ≤ ValueDistribution.logCounting f 0 R - ValueDistribution.logCounting f 0 r`.
For `r ≤ R` this bounds the increment of the logarithmic counting function from `r` to `R` from
below; for `R < r` it bounds the increment from `R` to `r` from above by `n(r) * log (r / R)`. -/
theorem zeroCount_mul_log_le_logCounting_sub (f : 𝕜 → F) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (zeroCount f univ (closedBall 0 r) : ℝ) * Real.log (R / r) ≤
      ValueDistribution.logCounting f 0 R - ValueDistribution.logCounting f 0 r := by
  rw [ValueDistribution.logCounting_zero, zeroCount_eq_finsum_posPart]
  refine Function.locallyFinsuppWithin.finsum_mem_closedBall_mul_log_le_logCounting_sub _
    (fun z _ ↦ ?_) hr hR
  rw [Function.locallyFinsuppWithin.posPart_apply]
  exact posPart_nonneg _

end TauCeti
