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

Let `F / k` be an algebraic function field and `x ∈ F` nonzero. The scheme
`TauCeti.AlgebraicGeometry.twoChartModel hF hx` is glued from `Spec 𝒪_x` and `Spec 𝒪_{x⁻¹}`, where
`𝒪_x` and `𝒪_{x⁻¹}` are the rings of functions regular wherever `x`, respectively `x⁻¹`, is
regular. For every `x`, these holomorphy rings are the integral closures `R_x` and `R_{x⁻¹}` of
`k[x]` and `k[x⁻¹]` in `F` (`TauCeti.restrictScalars_integralClosure_adjoin_eq_holomorphyRing`):
the affine models over `k[x]` and `k[x⁻¹]` when `x` is transcendental over `k`, both collapsing to
the constant field `algebraicClosure k F` when `x` is algebraic. Either way they are Dedekind
domains that are finitely generated `k`-algebras
(`TauCeti.isDedekindDomain_holomorphyRing_setOf_mem` and
`TauCeti.finiteType_holomorphyRing_setOf_mem`). Reading these properties chart by chart shows, for
every nonzero `x`:

* the scheme is locally of finite type over `k` and Noetherian;
* it has dimension at most one, so every point has codimension at most one;
* it is regular: every local ring is a regular local ring;
* the local ring at each codimension-one point is a discrete valuation ring, and every local ring
  is a valuation ring.

These properties are instances. When `x` is transcendental over `k`, the function field of the
scheme is `F`, which has transcendence degree one over `k`, so the scheme has dimension exactly one
and is a curve over `k` in the sense used to compare it with the function field: its points other
than the generic point are exactly its points of codimension one. When `x` is algebraic, both
charts are the spectrum of the constant field, so the scheme has dimension zero.

That the local ring at a codimension-one point is a discrete valuation ring (found by instance
search from `TauCeti.AlgebraicGeometry.twoChartModel.isRegularLocalRing_stalk` through
`TauCeti.AlgebraicGeometry.CodimensionOnePoint.isDiscreteValuationRing_stalk`) is the hypothesis
under which `AlgebraicGeometry.Scheme.toPlace` attaches a place of the function field to a point,
and, with the dimension bound `TauCeti.AlgebraicGeometry.twoChartModel.coheight_le_one`, it is the
hypothesis on the local rings in the comparison of the points of a curve with the places of its
function field (`TauCeti.AlgebraicGeometry.CodimensionOnePoint.equivPlace`). That every local ring
is a valuation ring (`TauCeti.AlgebraicGeometry.twoChartModel.valuationRing_stalk`) is the
hypothesis under which rational maps from the scheme to proper schemes extend
(`AlgebraicGeometry.Scheme.homOfFunctionField`).

## Main results

For every nonzero `x`:

* `TauCeti.AlgebraicGeometry.twoChartModel.locallyOfFiniteType`: the structure morphism to
  `Spec k` is locally of finite type.
* `TauCeti.AlgebraicGeometry.twoChartModel.isNoetherian`: the scheme is Noetherian.
* `TauCeti.AlgebraicGeometry.twoChartModel.topologicalKrullDim_le_one`: the scheme has dimension
  at most one.
* `TauCeti.AlgebraicGeometry.twoChartModel.coheight_le_one`: every point has codimension at most
  one, also available as the instance
  `TauCeti.AlgebraicGeometry.twoChartModel.fact_coheight_le_one`.
* `TauCeti.AlgebraicGeometry.twoChartModel.isRegularLocalRing_stalk`: every local ring is a
  regular local ring, so the local ring at a codimension-one point is a discrete valuation ring
  (`TauCeti.AlgebraicGeometry.CodimensionOnePoint.isDiscreteValuationRing_stalk`).
* `TauCeti.AlgebraicGeometry.twoChartModel.valuationRing_stalk`: every local ring is a valuation
  ring.

For `x` transcendental over `k`:

* `TauCeti.AlgebraicGeometry.twoChartModel.topologicalKrullDim_eq_one`: the scheme has dimension
  one.
* `TauCeti.AlgebraicGeometry.twoChartModel.isFunctionField_functionField` and
  `TauCeti.AlgebraicGeometry.twoChartModel.isIntegrallyClosedIn_functionField`: `k(X)` is an
  algebraic function field over `k`, with exact constant field `k` whenever `k` is integrally
  closed in `F`.

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

/-- **The two-chart model is locally of finite type over `k`**: both charts are spectra of
finitely generated `k`-algebras. -/
instance locallyOfFiniteType :
    LocallyOfFiniteType (twoChartModel hF hx ↘ Spec (.of k)) := by
  -- Instance search does not find that `LocallyOfFiniteType` is local at the source, so the
  -- instance coming from its ring-hom property is supplied by hand.
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  refine IsZariskiLocalAtSource.of_openCover (chartCover hF hx) fun b ↦ ?_
  cases b
  · rw [chartCover_f_false, ιFinite_over]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr (finiteType_holomorphyRing_setOf_mem hF x))
  · rw [chartCover_f_true, ιInfinity_over]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr (finiteType_holomorphyRing_setOf_mem hF x⁻¹))

/-- **The two-chart model is a Noetherian scheme**: it is of finite type over the field `k` and
covered by two affine charts. -/
instance isNoetherian : IsNoetherian (twoChartModel hF hx) where
  toIsLocallyNoetherian :=
    LocallyOfFiniteType.isLocallyNoetherian (twoChartModel hF hx ↘ Spec (.of k))
  toCompactSpace := inferInstance

/-- **The two-chart model has dimension one**, for `x` transcendental over `k`: its dimension is
the transcendence degree of its function field `F` over `k`. -/
theorem topologicalKrullDim_eq_one (hxt : Transcendental k x) :
    topologicalKrullDim (twoChartModel hF hx) = 1 := by
  rw [topologicalKrullDim_eq_toNat_trdeg_functionField k, (functionFieldEquiv hxt).trdeg_eq,
    hF.trdeg_eq_one]
  simp

/-- **The function field of the two-chart model is an algebraic function field over `k`**, for `x`
transcendental over `k`. -/
theorem isFunctionField_functionField (hxt : Transcendental k x) :
    IsFunctionField k (twoChartModel hF hx).functionField :=
  (isFunctionField_functionField_iff k).mpr (topologicalKrullDim_eq_one hxt)

/-- **Exactness of the constant field transfers to the function field of the two-chart model**: if
`k` is integrally closed in `F`, then `k` is integrally closed in `k(twoChartModel hF hx)`. -/
theorem isIntegrallyClosedIn_functionField (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    IsIntegrallyClosedIn k (twoChartModel hF hx).functionField :=
  (functionFieldEquiv hxt).isIntegrallyClosedIn.mpr hk

/-- **The two-chart model has dimension at most one**, for every nonzero `x`: its dimension is
one when `x` is transcendental over `k`
(`TauCeti.AlgebraicGeometry.twoChartModel.topologicalKrullDim_eq_one`) and zero when `x` is
algebraic over `k`, both charts then being the spectrum of the constant field. -/
theorem topologicalKrullDim_le_one : topologicalKrullDim (twoChartModel hF hx) ≤ 1 := by
  -- The finite chart is a nonempty open subscheme of the irreducible scheme, so it has the same
  -- dimension, and it is the spectrum of the Dedekind domain `𝒪_x`.
  have := isDedekindDomain_holomorphyRing_setOf_mem hF x
  rw [← topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
    (twoChartModel hF hx ↘ Spec (.of k)) (ιFinite hF hx).isOpenEmbedding]
  -- the underlying space of `Spec 𝒪_x` is the prime spectrum of `𝒪_x`
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := holomorphyRing _)).le.trans
    (Ring.krullDimLE_iff.mp inferInstance)

/-- **Every point of the two-chart model has codimension at most one**, the scheme having
dimension at most one. -/
theorem coheight_le_one (p : twoChartModel hF hx) : coheight p ≤ 1 := by
  exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim p).trans topologicalKrullDim_le_one

/-- Every point of the two-chart model has codimension at most one, as a `Fact` for the API of
Weil divisors and line bundles on schemes whose points have codimension at most one. -/
instance fact_coheight_le_one : Fact (∀ p : twoChartModel hF hx, coheight p ≤ 1) :=
  ⟨coheight_le_one⟩

/-- **The two-chart model is regular**: its local rings are the local rings of the Dedekind
domains `𝒪_x` and `𝒪_{x⁻¹}`, which are regular. -/
instance isRegularLocalRing_stalk (p : twoChartModel hF hx) :
    IsRegularLocalRing ((twoChartModel hF hx).presheaf.stalk p) := by
  have := isDedekindDomain_holomorphyRing_setOf_mem hF x
  have := isDedekindDomain_holomorphyRing_setOf_mem hF x⁻¹
  rcases (Set.ext_iff.mp (range_ιFinite_union_range_ιInfinity hF hx) p).mpr trivial with
    ⟨q, rfl⟩ | ⟨q, rfl⟩
  · exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ q).mpr inferInstance
  · exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ q).mpr inferInstance

/-- **The local rings of the two-chart model are valuation rings**: at the generic point the local
ring is the function field, and at every other point it is a discrete valuation ring. -/
instance valuationRing_stalk (p : twoChartModel hF hx) :
    ValuationRing ((twoChartModel hF hx).presheaf.stalk p) :=
  Scheme.valuationRing_stalk_of_topologicalKrullDim_le_one topologicalKrullDim_le_one p

end TauCeti.AlgebraicGeometry.twoChartModel
