/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Censoring
public import TauCeti.Probability.Distributions.TruncatedNormal.Basic

/-!
# Censored Gaussian laws versus conditional truncation

Censoring a Gaussian random variable `X ∼ N(m, v)` by projecting onto a closed interval `[l, r]`
or onto a closed half-line `[l, ∞)` or `(-∞, r]` accumulates the clipped tail probabilities as
endpoint point masses (`TauCeti.Probability.Distributions.Gaussian.Censoring`), whereas conditional
truncation (`truncatedNormalMeasure m' v' s`) conditions on `s` and renormalizes the surviving
density.

Because every censored Gaussian law fails to have null singletons across all variances `v : ℝ≥0`
(including at the Dirac boundary `v = 0` and on degenerate intervals `l = r`), while every
positive-variance `truncatedNormalMeasure m' v' s` has null singletons for every conditioning set
`s` (`nullSingletonClass_truncatedNormalMeasure`), no two-sided or one-sided censored Gaussian law
ever coincides with a positive-variance conditionally truncated normal law.

## Main results

* `TauCeti.Probability.map_coe_projIcc_gaussianReal_ne_truncatedNormalMeasure` — no `[l, r]`-
  censored Gaussian law equals a positive-variance `truncatedNormalMeasure`;
* `TauCeti.Probability.map_coe_projIci_gaussianReal_ne_truncatedNormalMeasure` — no lower-censored
  Gaussian law equals a positive-variance `truncatedNormalMeasure`;
* `TauCeti.Probability.map_coe_projIic_gaussianReal_ne_truncatedNormalMeasure` — no upper-censored
  Gaussian law equals a positive-variance `truncatedNormalMeasure`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), Chapter 13.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

local notation "clip[" l ", " r "; " h "]" =>
  (fun x : ℝ ↦ (Set.projIcc l r h x : ℝ))

/-- No `[l, r]`-censored Gaussian law (even at zero variance) equals a positive-variance
conditionally truncated normal law `truncatedNormalMeasure m' v' s` for any set `s`. -/
theorem map_coe_projIcc_gaussianReal_ne_truncatedNormalMeasure (m m' : ℝ) (v : ℝ≥0)
    {v' : ℝ≥0} (hv' : v' ≠ 0) {l r : ℝ} (hlr : l ≤ r) (s : Set ℝ) :
    (gaussianReal m v).map clip[l, r; hlr] ≠ truncatedNormalMeasure m' v' s := fun h ↦
  not_nullSingletonClass_map_coe_projIcc_gaussianReal m v hlr
    (h ▸ nullSingletonClass_truncatedNormalMeasure m' hv' s)

/-- No lower-censored Gaussian law equals a positive-variance `truncatedNormalMeasure`. -/
theorem map_coe_projIci_gaussianReal_ne_truncatedNormalMeasure (m m' : ℝ) (v : ℝ≥0)
    {v' : ℝ≥0} (hv' : v' ≠ 0) (l : ℝ) (s : Set ℝ) :
    (gaussianReal m v).map (fun x : ℝ ↦ (Set.projIci l x : ℝ)) ≠
      truncatedNormalMeasure m' v' s := fun h ↦
  not_nullSingletonClass_map_coe_projIci_gaussianReal m v l
    (h ▸ nullSingletonClass_truncatedNormalMeasure m' hv' s)

/-- No upper-censored Gaussian law equals a positive-variance `truncatedNormalMeasure`. -/
theorem map_coe_projIic_gaussianReal_ne_truncatedNormalMeasure (m m' : ℝ) (v : ℝ≥0)
    {v' : ℝ≥0} (hv' : v' ≠ 0) (r : ℝ) (s : Set ℝ) :
    (gaussianReal m v).map (fun x : ℝ ↦ (Set.projIic r x : ℝ)) ≠
      truncatedNormalMeasure m' v' s := fun h ↦
  not_nullSingletonClass_map_coe_projIic_gaussianReal m v r
    (h ▸ nullSingletonClass_truncatedNormalMeasure m' hv' s)

end TauCeti.Probability
