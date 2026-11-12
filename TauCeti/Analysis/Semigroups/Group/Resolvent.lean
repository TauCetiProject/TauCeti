/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.ComplexLinear
public import TauCeti.Analysis.Semigroups.Resolvent.Complex
import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Shift

/-!
# Resolvents of strongly continuous groups

For a complex-linear strongly continuous group with two-sided growth bound `(ω, M)`, the
complex generator has resolvent on both half-planes `ω < re z` and `re z < -ω`. The forward
Laplace integral represents the resolvent on the first half-plane, and the negative backward
Laplace integral represents it on the second. Together these give the estimate
`‖R(z, A)‖ ≤ M / (|re z| - ω)` whenever `ω < |re z|`.

The backward formulas use time reversal and the generic negation law for unbounded resolvents.

## Main results

* `StronglyContinuousGroup.mem_resolventSet_complexGenerator`: resolvent membership outside
  the growth strip.
* `StronglyContinuousGroup.resolvent_complexGenerator_apply_of_re_gt` and
  `StronglyContinuousGroup.resolvent_complexGenerator_apply_of_re_lt_neg`: the two Laplace
  integral formulas.
* `StronglyContinuousGroup.norm_resolvent_complexGenerator_le`: the bound from the growth strip.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition
(1987), Section 3.1, Proposition 3.1.6, pp. 166–168, and the following group remark on p. 169
for the application to both half-planes:
[official chapter](https://doi.org/10.1007/978-3-662-02520-8_3).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Semigroups.StronglyContinuousGroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {ω M : ℝ} {z : ℂ}

/-- The left half-plane of a two-sided growth bound belongs to the complex generator's
resolvent set. -/
theorem mem_resolventSet_complexGenerator_of_re_lt_neg (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (hb : U.HasGrowthBound ω M) (hz : z.re < -ω) :
    z ∈ LinearPMap.resolventSet (U.toSemigroup.complexGenerator hU) := by
  have hmem := U.reflect.toSemigroup.mem_resolventSet_complexGenerator
    (U.reflect_isComplexLinear hU) hb.reflect.toSemigroup (lambda := -z)
    (by simpa using neg_lt_neg hz)
  rw [U.reflect_complexGenerator hU] at hmem
  exact LinearPMap.mem_resolventSet_neg_iff.mp hmem

/-- Both half-planes outside the vertical strip of a two-sided growth bound belong to the
complex generator's resolvent set. -/
theorem mem_resolventSet_complexGenerator (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (hb : U.HasGrowthBound ω M) (hz : ω < |z.re|) :
    z ∈ LinearPMap.resolventSet (U.toSemigroup.complexGenerator hU) := by
  rcases le_or_gt 0 z.re with hsign | hsign
  · exact U.toSemigroup.mem_resolventSet_complexGenerator hU hb.toSemigroup
      (by simpa [abs_of_nonneg hsign] using hz)
  · exact U.mem_resolventSet_complexGenerator_of_re_lt_neg hU hb
      (by rw [abs_of_neg hsign] at hz; linarith)

/-- On the right half-plane of a growth bound, the complex generator's resolvent is the forward
Laplace integral of the group. -/
theorem resolvent_complexGenerator_apply_of_re_gt (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (hb : U.HasGrowthBound ω M) (hz : ω < z.re) (x : X) :
    LinearPMap.resolvent (U.toSemigroup.complexGenerator hU) z x =
      ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(z * t)) • U t x := by
  rw [U.toSemigroup.resolvent_complexGenerator_apply hU hb.toSemigroup hz]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by
    rw [U.toSemigroup_realOperator_of_nonneg (le_of_lt ht)]

/-- On the left half-plane of a growth bound, the complex generator's resolvent is the negative
backward Laplace integral of the group. -/
theorem resolvent_complexGenerator_apply_of_re_lt_neg (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (hb : U.HasGrowthBound ω M) (hz : z.re < -ω) (x : X) :
    LinearPMap.resolvent (U.toSemigroup.complexGenerator hU) z x =
      -(∫ t in Set.Ioi (0 : ℝ), Complex.exp (z * t) • U (-t) x) := by
  have hmem := U.mem_resolventSet_complexGenerator_of_re_lt_neg hU hb hz
  have hneg : LinearPMap.resolvent (U.toSemigroup.complexGenerator hU) z =
      -LinearPMap.resolvent
        (U.reflect.toSemigroup.complexGenerator (U.reflect_isComplexLinear hU)) (-z) := by
    rw [U.reflect_complexGenerator hU, LinearPMap.resolvent_neg hmem, neg_neg]
  rw [hneg, neg_apply,
    U.reflect.resolvent_complexGenerator_apply_of_re_gt (U.reflect_isComplexLinear hU)
      hb.reflect (by simpa using neg_lt_neg hz)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [reflect_apply, neg_mul, neg_neg]

/-- The two-sided growth bound controls the complex generator's resolvent by its distance from
the boundary of the vertical strip. This also covers negative growth rates on the zero space. -/
theorem norm_resolvent_complexGenerator_le (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (hb : U.HasGrowthBound ω M) (hz : ω < |z.re|) :
    ‖LinearPMap.resolvent (U.toSemigroup.complexGenerator hU) z‖ ≤ M / (|z.re| - ω) := by
  rcases le_or_gt 0 z.re with hsign | hsign
  · simpa only [abs_of_nonneg hsign] using
      U.toSemigroup.norm_resolvent_complexGenerator_le hU hb.toSemigroup
        (by simpa only [abs_of_nonneg hsign] using hz)
  · have hmem := U.mem_resolventSet_complexGenerator_of_re_lt_neg hU hb
      (by rw [abs_of_neg hsign] at hz; linarith)
    have hnorm := U.reflect.toSemigroup.norm_resolvent_complexGenerator_le
      (U.reflect_isComplexLinear hU) hb.reflect.toSemigroup (lambda := -z)
      (by simpa only [Complex.neg_re, abs_of_neg hsign] using hz)
    rw [U.reflect_complexGenerator hU, LinearPMap.resolvent_neg hmem, norm_neg] at hnorm
    simpa only [Complex.neg_re, abs_of_neg hsign] using hnorm

end TauCeti.Semigroups.StronglyContinuousGroup
