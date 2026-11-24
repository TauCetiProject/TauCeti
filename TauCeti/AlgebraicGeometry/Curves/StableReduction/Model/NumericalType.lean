/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.RegularModel
public import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The numerical type of a proper regular model over a discrete valuation ring

For a proper regular integral `TauCeti.Model` with connected special fibre, all points of
codimension at most two, and finite-dimensional `H¹` on each component of the special fibre over a
discrete valuation ring `R`, `TauCeti.Model.numericalType` packages
`AlgebraicGeometry.Scheme.Hom.specialFiberNumericalType` without choosing a uniformizer; by
`TauCeti.Model.numericalType_eq_specialFiberNumericalType`, it agrees with the numerical type
computed from any uniformizer of `R`.

## References

* [The Stacks Project, Section 55.9 (Tag 0C5Y)](https://stacks.math.columbia.edu/tag/0C5Y) and
  [Definition 55.3.1 (Tag 0C6Z)](https://stacks.math.columbia.edu/tag/0C6Z); Q. Liu, *Algebraic
  Geometry and Arithmetic Curves*, Section 9.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)

universe u

namespace TauCeti.Model

attribute [local instance] Model.isNoetherian_total

section Connected

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
  (M : Model R K C toK) [ConnectedSpace (specialFiber R M.toBase).left]

/-- The preimage of the closed point in `M.total` is preconnected when the special fibre of `M`
is connected. -/
theorem isPreconnected_preimage_closedPoint :
    _root_.IsPreconnected (M.toBase ⁻¹' {closedPoint R}) :=
  (preconnectedSpace_specialFiber_iff R M.toBase).mp inferInstance

end Connected

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
  (M : Model R K C toK) [M.IsProper] [IsIntegral M.total]
  [TauCeti.AlgebraicGeometry.IsRegular M.total] [ConnectedSpace (specialFiber R M.toBase).left]
  (hX : ∀ x : M.total, coheight x ≤ 2)
  (hC : M.toBase.HasFiniteDimensionalSpecialFiberComponentTrivialCohomologyOne)

/-- **The numerical type of a proper regular model** over a discrete valuation ring
([Stacks, Section 55.9 (Tag 0C5Y)](https://stacks.math.columbia.edu/tag/0C5Y)), independent of a
uniformizer (`TauCeti.Model.numericalType_eq_specialFiberNumericalType`). The body is exposed so
`Component` is definitionally the finite subtype of codimension-one points of `M.total` lying in
the special fibre. -/
@[expose]
def numericalType : NumericalType.{u} :=
  M.toBase.specialFiberNumericalType hX
    (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint

/-- For any uniformizer `π` of `R`, `M.numericalType` equals `specialFiberNumericalType`. -/
theorem numericalType_eq_specialFiberNumericalType {π : R} (hπ : maximalIdeal R = Ideal.span {π}) :
    M.numericalType hX hC = M.toBase.specialFiberNumericalType hX
      (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) hC hπ
      (.of_ne_zero (M.toBase.ne_zero_of_base_ne_closedPoint
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) hπ))
      M.isPreconnected_preimage_closedPoint :=
  M.toBase.specialFiberNumericalType_congr hX
    (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint hπ _

/-- The component type of `M.numericalType` is the finite subtype of codimension-one points of
`M.total` lying in the special fibre. -/
theorem numericalType_Component :
    (M.numericalType hX hC).Component =
      ↥(M.toBase.finite_setOf_base_eq_closedPoint (IsDiscreteValuationRing.not_a_field R)
        (M.toBase.base_genericPoint_ne_closedPoint
          (IsDiscreteValuationRing.not_a_field R))).toFinset := (rfl)

/-- Every component of `M.numericalType` lies over `closedPoint R`. -/
theorem base_eq_closedPoint_of_numericalType (i : (M.numericalType hX hC).Component) :
    M.toBase (i.val : M.total) = closedPoint R := (Set.Finite.mem_toFinset _).mp i.property

/-- For any generator `π` of `maximalIdeal R`, `((M.numericalType hX hC).multiplicity i : ℕ)` is
`M.toBase.specialFiberMultiplicity π i`. -/
theorem numericalType_multiplicity {π : R} (hπ : maximalIdeal R = Ideal.span {π})
    (i : (M.numericalType hX hC).Component) :
    ((M.numericalType hX hC).multiplicity i : ℕ) = M.toBase.specialFiberMultiplicity π i.val :=
  M.toBase.specialFiberMultiplicity_congr
    (TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose.symm.trans hπ)
    i.val

/-- The weight of the `i`-th component in `M.numericalType`, in `ℕ`. -/
@[simp]
theorem numericalType_weight (i : (M.numericalType hX hC).Component) :
    ((M.numericalType hX hC).weight i : ℕ) =
      M.toBase.specialFiberWeight (M.base_eq_closedPoint_of_numericalType hX hC i) := (rfl)

/-- The intersection matrix of `M.numericalType` is `M.toBase.specialFiberIntersectionMatrix`. -/
@[simp]
theorem numericalType_intersection :
    (M.numericalType hX hC).intersection = M.toBase.specialFiberIntersectionMatrix hX
      (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) := (rfl)

/-- The `(i, j)`-entry of the intersection matrix of `M.numericalType`. -/
theorem numericalType_intersection_apply (i j : (M.numericalType hX hC).Component) :
    (M.numericalType hX hC).intersection i j =
      letI := subschemeOverResidueField
        (M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
          (M.base_eq_closedPoint_of_numericalType hX hC i))
      LineBundleClass.intersectionNumber (ResidueField R)
        (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subschemeι
        (LineBundleClass.mk
          (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular
            hX j.val.property).toInvertibleSheaf)⁻¹ :=
  M.toBase.specialFiberIntersectionMatrix_apply hX _ i j

/-- The genus of the `i`-th component in `M.numericalType` is `dim_{κᵢ} H¹(Cᵢ, 𝒪_{Cᵢ})`. -/
@[simp]
theorem numericalType_genus (i : (M.numericalType hX hC).Component) :
    (M.numericalType hX hC).genus i = Module.finrank
      Γ((vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme, ⊤)
      (Cohomology (InvertibleSheaf.trivial
        (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme).obj 1) :=
  (rfl)

/-- On every component `Cᵢ` of `M`, `wᵢ * gᵢ = dim_k H¹(Cᵢ, 𝒪_{Cᵢ})`. -/
theorem weight_mul_genus_numericalType (i : (M.numericalType hX hC).Component) :
    letI := subschemeOverResidueField
      (M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
        (M.base_eq_closedPoint_of_numericalType hX hC i))
    ((M.numericalType hX hC).weight i : ℕ) * (M.numericalType hX hC).genus i =
      Module.finrank (ResidueField R) (Cohomology (InvertibleSheaf.trivial
        (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme).obj 1) :=
  M.toBase.specialFiberWeight_mul_finrank_cohomology_one
    (M.base_eq_closedPoint_of_numericalType hX hC i)

/-- The special fibre of `M` is reduced iff every component has multiplicity `1` in
`M.numericalType`. -/
theorem isReduced_specialFiber_iff_multiplicity_eq_one :
    IsReduced (specialFiber R M.toBase).left ↔ ∀ i, (M.numericalType hX hC).multiplicity i = 1 :=
  M.toBase.isReduced_specialFiber_iff_multiplicity_eq_one hX
    (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint

end TauCeti.Model

end
