/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.PointMass
public import TauCeti.Analysis.Normed.Operator.LinearPMap.Cayley

/-!
# The spectral measure of the Cayley transform at its singular point

Let `A` be a partial linear map on a complex Hilbert space with `-i` as a resolvent point, for
instance a self-adjoint one, and let `U` be its Cayley transform `LinearPMap.cayley A`. Since
`1` is not an eigenvalue of `U` (`LinearPMap.not_hasEigenvalue_cayley_one`), the spectral projection
of the point `1` for the spectral measure of a normal `U` vanishes, and every diagonal measure of
that spectral measure assigns mass zero to `{1}`.

This is the null set on which the inverse Cayley map `w ↦ i (1 + w) / (1 - w)` is singular, so the
value chosen for that map at `1` does not affect the real spectral measure of `A` obtained by
reindexing the spectral measure of `U` along it.

## Main results

* `LinearPMap.spectralPVM_cayley_proj_preimage_one`: the spectral projection of `U` at `1` is
  zero.
* `LinearPMap.diagMeasure_cayley_preimage_one`: every diagonal measure of the spectral
  measure of `U` assigns mass zero to `{1}`.

## References

* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Section 13.1.
-/

public section

open Complex

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H} [IsStarNormal A.cayley]

/-- **The Cayley spectral projection at `1` vanishes.** If `-i` is a resolvent point of `A` and
its Cayley transform is normal, as for self-adjoint `A` (`IsSelfAdjoint.isStarNormal_cayley`),
the spectral projection of the Cayley transform at the point `1` is zero. -/
@[simp]
theorem spectralPVM_cayley_proj_preimage_one (h : -I ∈ A.resolventSet) :
    A.cayley.spectralPVM.proj (Subtype.val ⁻¹' {1})
      (measurable_subtype_coe (measurableSet_singleton 1)) = 0 :=
  A.cayley.spectralPVM_proj_preimage_singleton_eq_zero (not_hasEigenvalue_cayley_one h)

/-- **Zero mass at the Cayley singular point.** If `-i` is a resolvent point of `A` and its
Cayley transform is normal, as for self-adjoint `A` (`IsSelfAdjoint.isStarNormal_cayley`), every
diagonal measure of the spectral measure of the Cayley transform assigns mass zero to `{1}`. -/
@[simp]
theorem diagMeasure_cayley_preimage_one (h : -I ∈ A.resolventSet) (ξ : H) :
    A.cayley.diagMeasure ξ (Subtype.val ⁻¹' {1}) = 0 :=
  A.cayley.diagMeasure_preimage_singleton_eq_zero (not_hasEigenvalue_cayley_one h) ξ

end LinearPMap
