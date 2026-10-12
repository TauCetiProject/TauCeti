/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Binomial

import TauCeti.MeasureTheory.Measure.Measurability
/-!
# Parameter measurability for the binomial distribution

Joint measurability in the number of trials and success probability lets measurable parameter
maps produce measurable measure-valued binomial families, in particular kernels.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability
/-- **The binomial family is measurable in its number of trials and its success probability.**

`ProbabilityTheory.binomial_eq_sum_dirac` writes `Bin(n, p)` as a finite weighted sum of Dirac
measures whose weights are polynomial in `p`, so each fibre `n` is measurable in `p`, and `ℕ` is
countable and discrete. -/
@[fun_prop] theorem measurable_binomial :
    Measurable fun q : ℕ × unitInterval => binomial q.1 q.2 := by
  refine measurable_from_prod_countable_right fun n => Measure.measurable_measure.2 fun s hs => ?_
  simp only [binomial_eq_sum_dirac, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]
  exact Finset.measurable_sum _ fun k _ => (by fun_prop : Measurable _).mul_const _
end TauCeti.Probability
