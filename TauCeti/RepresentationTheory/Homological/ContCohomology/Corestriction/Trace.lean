/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro

/-!
# The degree-zero trace/corestriction comparison

The coinduced trace is developed with the rest of the coinduced-module API in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced`. This file proves that in
degree zero its composite with the explicit Shapiro isomorphism is exactly the corestriction norm
`m ↦ ∑ x, t x • m` of `TauCeti.ContCohomology.explicitCor0`: a `G`-invariant element of
`Coind_U^G M` is the constant function at its value at `1`
(`TauCeti.ContCohomology.apply_eq_apply_one_of_mem_H0`), so the trace of it is the norm of that
value.

## Main declarations

* `TauCeti.ContCohomology.explicitCoeff0_trace_eq_explicitCor0_comp_explicitShapiro0` and
  `TauCeti.ContCohomology.explicitCor0_eq_explicitCoeff0_trace`: in degree zero the trace
  induces the corestriction norm, and corestriction is Shapiro's isomorphism followed by it.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (1.5.7), for the
  normalization of corestriction.
-/

public section

namespace TauCeti

namespace ContCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {U : Subgroup G}
  [U.FiniteIndex] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **In degree zero the trace is the corestriction norm.** A `G`-invariant element of
`Coind_U^G M` is constant, so the trace sends it to the norm `∑ x, x • m` of the `U`-invariant
value `m` that Shapiro's isomorphism `TauCeti.ContCohomology.explicitShapiro0` reads off it. This
is the degree-zero factorization through Shapiro's isomorphism and the trace. -/
theorem explicitCoeff0_trace_eq_explicitCor0_comp_explicitShapiro0 :
    explicitCoeff0 G (DiscreteCoind G U M) (DiscreteCoind.trace G U M) =
      (explicitCor0 G M U).comp (explicitShapiro0 G U M).toAddMonoidHom := by
  refine AddMonoidHom.ext fun f => Subtype.ext ?_
  rw [coe_explicitCoeff0, AddMonoidHom.comp_apply, coe_explicitCor0, DiscreteCoind.trace_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [AddEquiv.coe_toAddMonoidHom, explicitShapiro0_apply, apply_eq_apply_one_of_mem_H0 f]

/-- **Degree-zero corestriction factors through Shapiro's isomorphism and the trace.** This is
`TauCeti.ContCohomology.explicitCoeff0_trace_eq_explicitCor0_comp_explicitShapiro0` read through
the inverse of the degree-zero Shapiro isomorphism. -/
theorem explicitCor0_eq_explicitCoeff0_trace :
    explicitCor0 G M U =
      (explicitCoeff0 G (DiscreteCoind G U M) (DiscreteCoind.trace G U M)).comp
        (explicitShapiro0 G U M).symm.toAddMonoidHom := by
  refine AddMonoidHom.ext fun a => ?_
  have h := DFunLike.congr_fun explicitCoeff0_trace_eq_explicitCor0_comp_explicitShapiro0
    ((explicitShapiro0 G U M).symm a)
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply] at h
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]

end ContCohomology

end TauCeti
