/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.RestrictScalars
public import TauCeti.Analysis.Semigroups.Complexification

/-!
# The resolvent of a complexified strongly continuous semigroup

Let `S` be a C₀-semigroup on a real Banach space `X` with generator `A`, and let `S_ℂ` be its
componentwise complexification on `X_ℂ` (`StronglyContinuousSemigroup.complexify`), a complex-linear
semigroup whose complex generator `A_ℂ` acts by `A_ℂ (x + i y) = A x + i A y`.

This file shows that the resolvent commutes with complexification at real spectral parameters:
every real point `lambda` of the resolvent set of `A` is a point of the complex resolvent set of
`A_ℂ`, and there

`R(lambda, A_ℂ) = R(lambda, A)_ℂ`.

No growth bound is needed; the proof goes through the componentwise description of the generator
graph and the graph form of `TauCeti.LinearPMap.IsResolventAt`.

Together with the complex half-plane theory of
`TauCeti/Analysis/Semigroups/Resolvent/Complex.lean`, applied to `S_ℂ` with the growth bound
`HasGrowthBound.complexify`, this realizes the complex resolvent of a real semigroup: the half-plane
`omega < re lambda` lies in the resolvent set of `A_ℂ`, the resolvent is holomorphic there and
satisfies `‖R(lambda, A_ℂ)ⁿ‖ ≤ M / (re lambda - omega)ⁿ`, and on the real axis it is the
complexification of the real resolvent of `A`, with the same norm.

## Main results

* `StronglyContinuousSemigroup.isResolventAt_complexify_generator`: a real inverse of
  `lambda • I - A` complexifies to an inverse of `lambda • I - A_ℂ` over the reals.
* `StronglyContinuousSemigroup.resolvent_complexify_generator`: the real resolvent of the
  generator of `S_ℂ` is the complexified resolvent.
* `StronglyContinuousSemigroup.ofReal_mem_resolventSet_complexify_complexGenerator` and
  `StronglyContinuousSemigroup.resolvent_complexify_complexGenerator_ofReal`: the same statements
  for the complex generator `A_ℂ` at the real point `(lambda : ℂ)`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Sections II.2.1 and IV.1.
-/

public section

noncomputable section

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

open TauCeti.Complexification

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A real inverse `R` of `lambda • I - A`, with `A` the generator of `S`, complexifies to an
inverse of `lambda • I - A_ℂ` for the generator `A_ℂ` of the complexified semigroup. -/
theorem isResolventAt_complexify_generator (S : StronglyContinuousSemigroup X) {lambda : ℝ}
    {R : X →L[ℝ] X} (h : LinearPMap.IsResolventAt S.generator lambda R) :
    LinearPMap.IsResolventAt S.complexify.generator lambda (R.complexify.restrictScalars ℝ) := by
  rw [LinearPMap.isResolventAt_iff_forall_mem_graph] at h ⊢
  refine ⟨fun z => ?_, fun p hp => ?_⟩
  · rw [mem_complexify_generator_graph_iff]
    simpa only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.complexify_apply_re,
      ContinuousLinearMap.complexify_apply_im, sub_re, sub_im, real_smul_re, real_smul_im]
      using And.intro (h.1 z.re) (h.1 z.im)
  · rw [mem_complexify_generator_graph_iff] at hp
    apply TauCeti.Complexification.ext
    · simpa only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.complexify_apply_re,
        sub_re, real_smul_re] using h.2 _ hp.1
    · simpa only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.complexify_apply_im,
        sub_im, real_smul_im] using h.2 _ hp.2

/-- Every real point of the resolvent set of the generator of `S` lies in the resolvent set of the
generator of the complexified semigroup. -/
theorem mem_resolventSet_complexify_generator (S : StronglyContinuousSemigroup X) {lambda : ℝ}
    (h : lambda ∈ LinearPMap.resolventSet S.generator) :
    lambda ∈ LinearPMap.resolventSet S.complexify.generator :=
  (S.isResolventAt_complexify_generator (LinearPMap.isResolventAt_resolvent h)).mem_resolventSet

/-- **The resolvent commutes with complexification**, read over the reals: at a point `lambda` of
the resolvent set of `A`, the resolvent of the generator of `S_ℂ` is the complexification of
`R(lambda, A)`. -/
theorem resolvent_complexify_generator (S : StronglyContinuousSemigroup X) {lambda : ℝ}
    (h : lambda ∈ LinearPMap.resolventSet S.generator) :
    LinearPMap.resolvent S.complexify.generator lambda =
      (LinearPMap.resolvent S.generator lambda).complexify.restrictScalars ℝ :=
  LinearPMap.resolvent_eq_of_isResolventAt
    (S.isResolventAt_complexify_generator (LinearPMap.isResolventAt_resolvent h))

/-- Every real point `lambda` of the resolvent set of `A` gives the point `(lambda : ℂ)` of the
complex resolvent set of the complex generator `A_ℂ` of the complexified semigroup. -/
theorem ofReal_mem_resolventSet_complexify_complexGenerator (S : StronglyContinuousSemigroup X)
    {lambda : ℝ} (h : lambda ∈ LinearPMap.resolventSet S.generator) :
    (lambda : ℂ) ∈
      LinearPMap.resolventSet (S.complexify.complexGenerator S.isComplexLinear_complexify) := by
  have hreal : lambda ∈ LinearPMap.resolventSet
      ((S.complexify.complexGenerator S.isComplexLinear_complexify).restrictScalars ℝ) := by
    rw [complexGenerator_restrictScalars]
    exact S.mem_resolventSet_complexify_generator h
  simpa only [Complex.coe_algebraMap] using
    LinearPMap.mem_resolventSet_restrictScalars_iff.mp hreal

/-- **The complex resolvent on the real axis.** At a real point `lambda` of the resolvent set of
`A`, the resolvent of the complex generator `A_ℂ` of the complexified semigroup is the
complexification of `R(lambda, A)`. -/
theorem resolvent_complexify_complexGenerator_ofReal (S : StronglyContinuousSemigroup X)
    {lambda : ℝ} (h : lambda ∈ LinearPMap.resolventSet S.generator) :
    LinearPMap.resolvent (S.complexify.complexGenerator S.isComplexLinear_complexify) lambda =
      (LinearPMap.resolvent S.generator lambda).complexify := by
  have hreal : lambda ∈ LinearPMap.resolventSet
      ((S.complexify.complexGenerator S.isComplexLinear_complexify).restrictScalars ℝ) := by
    rw [complexGenerator_restrictScalars]
    exact S.mem_resolventSet_complexify_generator h
  have hrestrict := LinearPMap.restrictScalars_resolvent hreal
  rw [Complex.coe_algebraMap, complexGenerator_restrictScalars,
    S.resolvent_complexify_generator h] at hrestrict
  ext1 z
  exact congrArg (fun T : TauCeti.Complexification X →L[ℝ] TauCeti.Complexification X => T z)
    hrestrict

end TauCeti.Semigroups.StronglyContinuousSemigroup

end
