/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Basic
public import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
public import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
-- Proof-only: regularity of local rings and codimension bounds.
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.Topology.KrullDimension.Basic

/-!
# The two-chart model of a function field is a regular curve

Let `F / k` be an algebraic function field and `x ∈ F` transcendental over `k`. The scheme
`TauCeti.AlgebraicGeometry.twoChartModel hF hx` is glued from `Spec 𝒪_x` and `Spec 𝒪_{x⁻¹}`, where
`𝒪_x` and `𝒪_{x⁻¹}` are the rings of functions regular wherever `x`, respectively `x⁻¹`, is
regular. These are the integral closures of `k[x]` and `k[x⁻¹]` in `F`: Dedekind domains that are
finitely generated `k`-algebras (`TauCeti.isDedekindDomain_holomorphyRing_setOf_mem` and
`TauCeti.finiteType_holomorphyRing_setOf_mem`). Reading these properties chart by chart shows
that the scheme is a curve over `k` in the sense used to compare it with the function field:

* it is locally of finite type over `k` and Noetherian;
* it has dimension one, because its function field `F` has transcendence degree one over `k`;
* it is regular: every local ring is a regular local ring;
* its points other than the generic point are exactly its points of codimension one, and the
  local ring at each of them is a discrete valuation ring.

The last property is the hypothesis under which `TauCeti.AlgebraicGeometry.Scheme.toPlace`
attaches a place of the function field to a point, and, with the dimension bound, it is the
hypothesis on the local rings in the comparison of the points of a curve with the places of its
function field (`TauCeti.AlgebraicGeometry.CodimensionOnePoint.equivPlace`).

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.locallyOfFiniteType`: the structure morphism to
  `Spec k` is locally of finite type.
* `TauCeti.AlgebraicGeometry.twoChartModel.isNoetherian`: the scheme is Noetherian.
* `TauCeti.AlgebraicGeometry.twoChartModel.topologicalKrullDim_eq_one`: the scheme has dimension
  one.
* `TauCeti.AlgebraicGeometry.twoChartModel.isFunctionField_functionField` and
  `TauCeti.AlgebraicGeometry.twoChartModel.isIntegrallyClosedIn_functionField`: `k(X)` is an
  algebraic function field over `k`, with exact constant field `k` whenever `k` is integrally
  closed in `F`.
* `TauCeti.AlgebraicGeometry.twoChartModel.coheight_le_one`: every point has codimension at most
  one.
* `TauCeti.AlgebraicGeometry.twoChartModel.isRegularLocalRing_stalk`: every local ring is a
  regular local ring.
* `TauCeti.AlgebraicGeometry.twoChartModel.isDiscreteValuationRing_stalk`: the local ring at a
  codimension-one point is a discrete valuation ring.
* `TauCeti.AlgebraicGeometry.twoChartModel.valuationRing_stalk`: every local ring is a valuation
  ring, the hypothesis under which rational maps from the scheme to proper schemes extend.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2 and Appendix B.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6.
-/

public section

open CategoryTheory Order _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F] {hF : IsFunctionField k F} {x : F}
  {hx : x ≠ 0}

/-- **The two-chart model is locally of finite type over `k`**, for `x` transcendental over `k`:
both charts are spectra of finitely generated `k`-algebras. -/
theorem locallyOfFiniteType (hxt : Transcendental k x) :
    LocallyOfFiniteType (twoChartModel hF hx ↘ Spec (.of k)) := by
  -- Instance search does not find that `LocallyOfFiniteType` is local at the source, so the
  -- instance coming from its ring-hom property is supplied by hand.
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  refine IsZariskiLocalAtSource.of_openCover (chartCover hF hx) fun b ↦ ?_
  cases b
  · rw [chartCover_f_false, ιFinite_over]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr (finiteType_holomorphyRing_setOf_mem hF hxt))
  · rw [chartCover_f_true, ιInfinity_over]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr
        (finiteType_holomorphyRing_setOf_mem hF fun h ↦ hxt (IsAlgebraic.inv_iff.mp h)))

/-- **The two-chart model is a Noetherian scheme**, for `x` transcendental over `k`: it is of
finite type over the field `k` and covered by two affine charts. -/
theorem isNoetherian (hxt : Transcendental k x) : IsNoetherian (twoChartModel hF hx) := by
  have := locallyOfFiniteType (hF := hF) (hx := hx) hxt
  have := LocallyOfFiniteType.isLocallyNoetherian (twoChartModel hF hx ↘ Spec (.of k))
  refine { toCompactSpace := ⟨?_⟩ }
  rw [← range_ιFinite_union_range_ιInfinity hF hx]
  exact (isCompact_range (ιFinite hF hx).continuous).union
    (isCompact_range (ιInfinity hF hx).continuous)

/-- **The two-chart model has dimension one**, for `x` transcendental over `k`: its dimension is
the transcendence degree of its function field `F` over `k`. -/
theorem topologicalKrullDim_eq_one (hxt : Transcendental k x) :
    topologicalKrullDim (twoChartModel hF hx) = 1 := by
  have := locallyOfFiniteType (hF := hF) (hx := hx) hxt
  rw [topologicalKrullDim_eq_toNat_trdeg_functionField k, (functionFieldEquiv hxt).trdeg_eq,
    hF.trdeg_eq_one]
  simp

/-- **The function field of the two-chart model is an algebraic function field over `k`**, for `x`
transcendental over `k`. -/
theorem isFunctionField_functionField (hxt : Transcendental k x) :
    IsFunctionField k (twoChartModel hF hx).functionField := by
  have := locallyOfFiniteType (hF := hF) (hx := hx) hxt
  exact (isFunctionField_functionField_iff k).mpr (topologicalKrullDim_eq_one hxt)

/-- **Exactness of the constant field transfers to the function field of the two-chart model**: if
`k` is integrally closed in `F`, then `k` is integrally closed in `k(twoChartModel hF hx)`. -/
theorem isIntegrallyClosedIn_functionField (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    IsIntegrallyClosedIn k (twoChartModel hF hx).functionField :=
  (functionFieldEquiv hxt).isIntegrallyClosedIn.mpr hk

/-- **Every point of the two-chart model has codimension at most one**, for `x` transcendental
over `k`. -/
theorem coheight_le_one (hxt : Transcendental k x) (p : twoChartModel hF hx) :
    coheight p ≤ 1 := by
  have := TauCeti.coheight_le_topologicalKrullDim p
  rw [topologicalKrullDim_eq_one hxt] at this
  exact_mod_cast this

/-- **The two-chart model is regular**, for `x` transcendental over `k`: its local rings are the
local rings of the Dedekind domains `𝒪_x` and `𝒪_{x⁻¹}`, which are regular. -/
theorem isRegularLocalRing_stalk (hxt : Transcendental k x) (p : twoChartModel hF hx) :
    IsRegularLocalRing ((twoChartModel hF hx).presheaf.stalk p) := by
  have := isDedekindDomain_holomorphyRing_setOf_mem hF hxt
  have := isDedekindDomain_holomorphyRing_setOf_mem hF fun h ↦ hxt (IsAlgebraic.inv_iff.mp h)
  rcases (Set.ext_iff.mp (range_ιFinite_union_range_ιInfinity hF hx) p).mpr trivial with
    ⟨q, rfl⟩ | ⟨q, rfl⟩
  · exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ q).mpr inferInstance
  · exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ q).mpr inferInstance

/-- **The local rings of the two-chart model at its codimension-one points are discrete valuation
rings**, for `x` transcendental over `k`: they are regular local rings of dimension one. -/
theorem isDiscreteValuationRing_stalk (hxt : Transcendental k x)
    (p : CodimensionOnePoint (twoChartModel hF hx)) :
    IsDiscreteValuationRing ((twoChartModel hF hx).presheaf.stalk (p : twoChartModel hF hx)) := by
  have := isRegularLocalRing_stalk hxt (p : twoChartModel hF hx)
  exact CodimensionOnePoint.isDiscreteValuationRing_stalk p

/-- **The local rings of the two-chart model are valuation rings**, for `x` transcendental over
`k`: at the generic point the local ring is the function field, and at every other point it is a
discrete valuation ring. -/
theorem valuationRing_stalk (hxt : Transcendental k x) (p : twoChartModel hF hx) :
    ValuationRing ((twoChartModel hF hx).presheaf.stalk p) := by
  have := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  exact Scheme.valuationRing_stalk_of_topologicalKrullDim_le_one
    (topologicalKrullDim_eq_one hxt).le p

end TauCeti.AlgebraicGeometry.twoChartModel
