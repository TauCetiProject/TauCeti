/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Orthonormal

/-!
# Cardinality invariance of nonarchimedean model spaces

Over an ultrametric normed ring satisfying the strong rank condition,
a continuous linear map with dense range from `C₀(I, R)` to `C₀(J, R)` implies
`#J ≤ #I`. Consequently continuously linearly equivalent model spaces have
equally many coordinates. The indices may be empty, finite, or infinite and
may lie in different universes. Neither completeness nor a discrete value group
is required.

These are special cases of the cardinality bounds for dense spanning families
and orthonormal families in `TauCeti.Analysis.Normed.Module.Bases.Orthonormal`.
The general results also apply to incomplete ultrametric modules.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §1.
-/

public section

open scoped ZeroAtInfty Cardinal

universe u v w

variable {I : Type u} {J : Type v} {R : Type w}
  [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J] [DiscreteTopology J]
  [NormedRing R] [IsUltrametricDist R] [StrongRankCondition R]

/-- A continuous linear map with dense range between ultrametric model spaces
cannot increase the cardinality of the coordinate index. -/
theorem ContinuousLinearMap.lift_mk_le_of_denseRange_zeroAtInfty
    (f : C₀(I, R) →L[R] C₀(J, R)) (hf : DenseRange f) :
    Cardinal.lift.{u} #J ≤ Cardinal.lift.{v} #I := by
  classical
  exact TauCeti.IsOrthonormalFamily.lift_mk_le_of_denseRange
    (TauCeti.isOrthonormalBasis_single_one (R := R) (I := J)).isOrthonormalFamily
    (ZeroAtInftyContinuousMap.dense_span_single_one (R := R) (I := I)) f hf

/-- Continuously linearly equivalent ultrametric model spaces have coordinate
indices of the same cardinality. -/
theorem ContinuousLinearEquiv.lift_mk_eq_zeroAtInfty
    (e : C₀(I, R) ≃L[R] C₀(J, R)) :
    Cardinal.lift.{v} #I = Cardinal.lift.{u} #J := by
  classical
  exact TauCeti.IsOrthonormalBasis.lift_mk_eq_of_continuousLinearEquiv
    (TauCeti.isOrthonormalBasis_single_one (R := R) (I := I))
    (TauCeti.isOrthonormalBasis_single_one (I := J)) e
