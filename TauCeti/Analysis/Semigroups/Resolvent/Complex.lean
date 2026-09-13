/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Analytic
import TauCeti.Analysis.Normed.Operator.Resolvent.RestrictScalars
import TauCeti.Analysis.Normed.Operator.Resolvent.Shift
public import TauCeti.Analysis.Semigroups.PhaseShift
public import TauCeti.Analysis.Semigroups.Resolvent.Identity

/-!
# The complex resolvent of a strongly continuous semigroup

A C₀-semigroup acting by complex-linear operators on a complex Banach space `X` has a complex
generator `A` (`TauCeti.Semigroups.StronglyContinuousSemigroup.complexGenerator`), an unbounded
operator over `ℂ`. This file locates the **open half-plane** `{lambda | omega < re lambda}` of a
growth bound `(omega, M)` inside the complex resolvent set of `A`, identifies the resolvent there
with the Laplace transform

`R(lambda, A) x = ∫₀^∞ exp (-lambda t) S(t) x dt`,

bounds it by `M / (re lambda - omega)`, and concludes that `lambda ↦ R(lambda, A)` is
**holomorphic** on that half-plane.

The Laplace-transform resolvent of `TauCeti/Analysis/Semigroups/Resolvent/Basic.lean` is a
real-variable construction: the semigroup is indexed by nonnegative reals and acts by real
bounded operators, so it only produces *real* points of the resolvent set. Two bridges cross to
the complex picture. Moving parallel to the imaginary axis is the phase shift
`t ↦ exp (-i b t) S(t)`, whose generator is `A - i b`
(`TauCeti.Semigroups.StronglyContinuousSemigroup.complexGenerator_phaseShift`) and whose growth
bound is that of `S`; moving from a real to a complex scalar field is
`TauCeti.LinearPMap.mem_resolventSet_restrictScalars_iff`, which upgrades a bounded real-linear
inverse of `mu • I - A` to the complex resolvent. Holomorphy is then the abstract
`LinearPMap.analyticOnNhd_resolvent` restricted to the half-plane.

## Main results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.mem_resolventSet_complexGenerator` and
  `TauCeti.Semigroups.StronglyContinuousSemigroup.setOf_lt_re_subset_resolventSet_complexGenerator`:
  the half-plane `omega < re lambda` lies in the complex resolvent set.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.resolvent_complexGenerator_apply`: the complex
  resolvent is the Laplace transform of the semigroup.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.norm_resolvent_complexGenerator_le`: the
  Hille--Yosida bound `‖R(lambda, A)‖ ≤ M / (re lambda - omega)`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.analyticOnNhd_resolvent_complexGenerator`: the
  complex resolvent is holomorphic on the half-plane.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.1.10 and Section IV.1.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Theorem 1.5.3.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {omega M : ℝ} {lambda : ℂ}

/-- **The complex resolvent set of the generator contains the half-plane of the growth bound.**
Every `lambda` with `omega < re lambda` is a resolvent point of the complex generator. -/
theorem mem_resolventSet_complexGenerator (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (hb : S.HasGrowthBound omega M)
    (hlambda : omega < lambda.re) :
    lambda ∈ TauCeti.LinearPMap.resolventSet (S.complexGenerator hS) := by
  have hT : (S.phaseShift hS lambda.im).IsComplexLinear := hS.phaseShift lambda.im
  have hreal : lambda.re ∈
      TauCeti.LinearPMap.resolventSet
        (((S.phaseShift hS lambda.im).complexGenerator hT).restrictScalars ℝ) := by
    rw [(S.phaseShift hS lambda.im).complexGenerator_restrictScalars hT]
    exact (S.phaseShift hS lambda.im).mem_resolventSet_generator
      (hb.phaseShift hS lambda.im) hlambda
  have hc := TauCeti.LinearPMap.mem_resolventSet_restrictScalars_iff.mp hreal
  rw [Complex.coe_algebraMap, complexGenerator_phaseShift] at hc
  have hshift := (TauCeti.LinearPMap.mem_resolventSet_subScalar_iff
    (A := S.complexGenerator hS) (omega := (lambda.im : ℂ) * Complex.I)
    (lambda := (lambda.re : ℂ))).mp hc
  rwa [Complex.re_add_im] at hshift

/-- The resolvent of the complex generator at a point of the open half-plane
`omega < re lambda`, read over the reals, is the Laplace-transform resolvent of the phase-shifted
semigroup `t ↦ exp (-i (im lambda) t) S(t)` at the real point `re lambda`. -/
theorem restrictScalars_resolvent_complexGenerator (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (hb : S.HasGrowthBound omega M)
    (hlambda : omega < lambda.re) :
    (TauCeti.LinearPMap.resolvent (S.complexGenerator hS) lambda).restrictScalars ℝ
      = (S.phaseShift hS lambda.im).resolvent (hb.phaseShift hS lambda.im) lambda.re hlambda := by
  have hT : (S.phaseShift hS lambda.im).IsComplexLinear := hS.phaseShift lambda.im
  have hreal : lambda.re ∈
      TauCeti.LinearPMap.resolventSet (S.phaseShift hS lambda.im).generator :=
    (S.phaseShift hS lambda.im).mem_resolventSet_generator (hb.phaseShift hS lambda.im) hlambda
  have hrestrict :
      ((S.phaseShift hS lambda.im).complexGenerator hT).restrictScalars ℝ =
        (S.phaseShift hS lambda.im).generator :=
    (S.phaseShift hS lambda.im).complexGenerator_restrictScalars hT
  have hmem : (lambda.re : ℂ) + (lambda.im : ℂ) * Complex.I ∈
      TauCeti.LinearPMap.resolventSet (S.complexGenerator hS) := by
    rw [Complex.re_add_im]
    exact S.mem_resolventSet_complexGenerator hS hb hlambda
  have hshift : TauCeti.LinearPMap.resolvent
      ((S.phaseShift hS lambda.im).complexGenerator hT) (lambda.re : ℂ)
      = TauCeti.LinearPMap.resolvent (S.complexGenerator hS) lambda := by
    rw [complexGenerator_phaseShift]
    rw [TauCeti.LinearPMap.resolvent_subScalar (A := S.complexGenerator hS)
      (omega := (lambda.im : ℂ) * Complex.I) (lambda := (lambda.re : ℂ)) hmem, Complex.re_add_im]
  have hbridge := TauCeti.LinearPMap.restrictScalars_resolvent
    (A := (S.phaseShift hS lambda.im).complexGenerator hT) (mu := lambda.re)
    (by rwa [hrestrict])
  rw [Complex.coe_algebraMap, hshift, hrestrict] at hbridge
  rw [hbridge, (S.phaseShift hS lambda.im).generator_resolvent_eq
    (hb.phaseShift hS lambda.im) hlambda]

/-- The open half-plane `omega < re lambda` of a growth bound `(omega, M)` lies in the complex
resolvent set of the generator. -/
theorem setOf_lt_re_subset_resolventSet_complexGenerator (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (hb : S.HasGrowthBound omega M) :
    {z : ℂ | omega < z.re} ⊆ TauCeti.LinearPMap.resolventSet (S.complexGenerator hS) :=
  fun _ hz => S.mem_resolventSet_complexGenerator hS hb hz

/-- **The complex Laplace-transform bridge.** On the half-plane `omega < re lambda` the resolvent
of the complex generator is the pointwise Bochner integral
`R(lambda, A) x = ∫₀^∞ exp (-lambda t) S(t) x dt`. -/
theorem resolvent_complexGenerator_apply (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (hb : S.HasGrowthBound omega M)
    (hlambda : omega < lambda.re) (x : X) :
    TauCeti.LinearPMap.resolvent (S.complexGenerator hS) lambda x
      = ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(lambda * t)) • S.realOperator t x := by
  have hrestrict := congrArg (fun R : X →L[ℝ] X => R x)
    (S.restrictScalars_resolvent_complexGenerator hS hb hlambda)
  simp only [ContinuousLinearMap.coe_restrictScalars'] at hrestrict
  rw [hrestrict, (S.phaseShift hS lambda.im).resolvent_apply]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [S.phaseShift_realOperator_apply_of_nonneg hS lambda.im t (le_of_lt ht),
    ← algebraMap_smul ℂ (Real.exp (-(lambda.re * t))), Complex.coe_algebraMap, smul_smul,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  conv_rhs => rw [← Complex.re_add_im lambda]
  push_cast
  ring

/-- **The Hille--Yosida bound at a complex spectral parameter**: on the half-plane of a growth
bound `(omega, M)`, `‖R(lambda, A)‖ ≤ M / (re lambda - omega)`. -/
theorem norm_resolvent_complexGenerator_le (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (hb : S.HasGrowthBound omega M)
    (hlambda : omega < lambda.re) :
    ‖TauCeti.LinearPMap.resolvent (S.complexGenerator hS) lambda‖ ≤ M / (lambda.re - omega) := by
  rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ),
    S.restrictScalars_resolvent_complexGenerator hS hb hlambda]
  exact (S.phaseShift hS lambda.im).resolvent_norm_le (hb.phaseShift hS lambda.im) lambda.re
    hlambda

/-- **The resolvent of a C₀-semigroup is holomorphic.** On the half-plane `omega < re lambda` of a
growth bound `(omega, M)`, the resolvent of the complex generator is analytic in operator norm. -/
theorem analyticOnNhd_resolvent_complexGenerator (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (hb : S.HasGrowthBound omega M) :
    AnalyticOnNhd ℂ (TauCeti.LinearPMap.resolvent (S.complexGenerator hS))
      {z : ℂ | omega < z.re} :=
  (LinearPMap.analyticOnNhd_resolvent (S.complexGenerator hS)).mono
    (S.setOf_lt_re_subset_resolventSet_complexGenerator hS hb)

end TauCeti.Semigroups.StronglyContinuousSemigroup

end
