/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Matrix
public import TauCeti.AlgebraicGeometry.SpecialFiber.Weight

/-!
# Exceptional components of the special fibre

Let `X` be a regular model over a local ring `R` of dimension at most one. If a component `Cⱼ` of
the special fibre, with its reduced structure, is an exceptional curve of the first kind, then its
diagonal entry `aⱼⱼ` of the intersection matrix is minus its weight `wⱼ`
(`AlgebraicGeometry.Scheme.Hom.specialFiberIntersectionMatrix_self_eq_neg_specialFiberWeight`).
Together with the vanishing of the genus of `Cⱼ` over its constant field
(`IsExceptionalCurveOfFirstKind.finrank_globalSections_cohomology_one_trivial_eq_zero`), this
says that `j` is a `(-1)`-index of the numerical type
(`TauCeti.NumericalType.IsMinusOneIndex`). This is the numerical shadow of an exceptional curve
on which the combinatorial theory of minimal numerical types rests.

## Main results

* `AlgebraicGeometry.Scheme.Hom.specialFiberIntersectionMatrix_self_eq_neg_specialFiberWeight`:
  the diagonal entry of the intersection matrix of a regular model at an exceptional component.

## References

* [The Stacks Project, Tag 0C76](https://stacks.math.columbia.edu/tag/0C76): `(-1)`-indices of
  numerical types, the numerical counterpart of exceptional curves.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.3, on exceptional divisors and
  Castelnuovo's criterion on regular fibred surfaces.
-/

public section

open AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R]
  {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]
  [TauCeti.AlgebraicGeometry.IsRegular X]

/-- **An exceptional component of the special fibre is a `(-1)`-component.** Let `X` be a regular
Noetherian integral scheme over a local ring `R` of dimension at most one, with all points of
codimension at most two and generic point away from the closed point. If the component `Cⱼ` of
the special fibre, with its reduced structure, is an exceptional curve of the first kind, then the
diagonal entry `aⱼⱼ = (Cⱼ · Cⱼ)` of the intersection matrix of the special fibre is minus the
weight `wⱼ = dim_k H⁰(Cⱼ, 𝒪_{Cⱼ})` over the residue field `k` of `R`. Together with
`IsExceptionalCurveOfFirstKind.finrank_globalSections_cohomology_one_trivial_eq_zero`, which
makes the genus of `Cⱼ` over its constant field zero, this is the condition of a `(-1)`-index of
the numerical type. -/
theorem specialFiberIntersectionMatrix_self_eq_neg_specialFiberWeight
    (hX : ∀ x : X, coheight x ≤ 2) (hη : toBase (genericPoint X) ≠ closedPoint R)
    (j : (toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset)
    (hj : (vanishingIdeal ⟨closure {((j : CodimensionOnePoint X) : X)},
      isClosed_closure⟩).IsExceptionalCurveOfFirstKind) :
    toBase.specialFiberIntersectionMatrix hX hη j j =
      -(toBase.specialFiberWeight ((Set.Finite.mem_toFinset _).mp j.property) : ℤ) := by
  let := subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
    ((Set.Finite.mem_toFinset _).mp j.property))
  rw [specialFiberIntersectionMatrix_apply, specialFiberWeight_def]
  exact hj.intersectionNumber_self (ResidueField R)

end AlgebraicGeometry.Scheme.Hom
