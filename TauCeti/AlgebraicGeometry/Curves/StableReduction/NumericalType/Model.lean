/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.RegularModel

/-!
# The numerical type of a bundled regular model over a DVR

For a proper integral regular model `M : TauCeti.Model R K C toK` of relative dimension at most one
over a discrete valuation ring `R`, with connected special fibre and finite-dimensional
`H¹(Cᵢ, 𝒪_{Cᵢ})` on every reduced irreducible component `Cᵢ` of the special fibre, generator
independence (`AlgebraicGeometry.Scheme.Hom.specialFiberNumericalType_congr`) yields the
uniformizer-free invariant `TauCeti.Model.numericalType`.

## Main declarations

* `TauCeti.Model.numericalType`: the uniformizer-free numerical type of the special fibre of `M`.
* `TauCeti.Model.numericalType_multiplicity`, `TauCeti.Model.numericalType_weight`,
  `TauCeti.Model.numericalType_intersection`, and `TauCeti.Model.numericalType_genus`: its data.
* `TauCeti.Model.numericalType_eq_specialFiberNumericalType`: agreement with
  `AlgebraicGeometry.Scheme.Hom.specialFiberNumericalType` for any uniformizer `π`.
* `TauCeti.Model.numericalType_adj_iff` and
  `TauCeti.Model.forall_numericalType_multiplicity_eq_one_iff`: graph adjacency and reducedness of
  the scheme-theoretic special fibre.
* `TauCeti.Model.numericalType_weight_mul_genus_sub_one`,
  `TauCeti.Model.numericalType_arithmeticGenus_eulerCharBelow_selfIntersection`, and
  `TauCeti.Model.two_mul_numericalType_arithmeticGenus_eulerCharBelow_selfIntersection`:
  residue-field cohomology formulas and the total arithmetic-genus identity.

## References

* [The Stacks Project, Section 55.9](https://stacks.math.columbia.edu/tag/0C5Y) and
  [Lemma 55.9.9 (Tag 0C9U)](https://stacks.math.columbia.edu/tag/0C9U).
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal)
open AlgebraicGeometry.Scheme.Modules (eulerCharBelow)

universe u

namespace TauCeti.Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- **The numerical type of a proper regular model.** For a proper integral regular model `M` of
relative dimension at most one over a discrete valuation ring `R`, with connected special fibre and
finite-dimensional `H¹` on the reduced irreducible components of the special fibre, this is the
uniformizer-free `TauCeti.NumericalType` of the special fibre. Both `[M.IsProper]` and
`[RelativeDimensionLE 1 M.toBase]` are synthesized automatically whenever
`[FamilyOfCurves M.toBase]` is in scope. -/
@[expose] def numericalType (M : Model R K C toK) [M.IsProper] [RelativeDimensionLE 1 M.toBase]
    [IsIntegral M.total] [TauCeti.AlgebraicGeometry.IsRegular M.total]
    (hC : M.toBase.HasFiniteDimensionalSpecialFiberComponentTrivialCohomologyOne)
    (hconn : _root_.IsPreconnected (M.toBase ⁻¹' {closedPoint R})) : NumericalType.{u} :=
  M.toBase.specialFiberNumericalType M.toBase.coheight_le_succ_of_relativeDimensionLE
    (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
    hC
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec.maximalIdeal_eq
    (mul_right_injective₀ (IsDiscreteValuationRing.exists_irreducible R).choose_spec.ne_zero)
    hconn

section ModelAPI

variable (M : Model R K C toK) [M.IsProper] [RelativeDimensionLE 1 M.toBase] [IsIntegral M.total]
  [TauCeti.AlgebraicGeometry.IsRegular M.total]
  (hC : M.toBase.HasFiniteDimensionalSpecialFiberComponentTrivialCohomologyOne)
  (hconn : _root_.IsPreconnected (M.toBase ⁻¹' {closedPoint R}))

/-- A codimension-one point of `M.total` arises as a component of `M.numericalType` if and only if
it maps to `closedPoint R`. -/
theorem exists_numericalType_component_iff (x : CodimensionOnePoint M.total) :
    (∃ i : (M.numericalType hC hconn).Component, i.val = x) ↔ M.toBase x = closedPoint R :=
  M.toBase.exists_specialFiberNumericalType_component_iff _ _ hC _ _ hconn x

/-- Every component of `M.numericalType` maps to `closedPoint R`. -/
theorem base_numericalType_component (i : (M.numericalType hC hconn).Component) :
    M.toBase i.val = closedPoint R :=
  M.toBase.base_specialFiberNumericalType_component _ _ hC _ _ hconn i

/-- For any generator `π` of `maximalIdeal R`, the multiplicity of `i` in `M.numericalType` is
`M.toBase.specialFiberMultiplicity π i.val`. -/
theorem numericalType_multiplicity {π : R} (hπ : maximalIdeal R = Ideal.span {π})
    (i : (M.numericalType hC hconn).Component) :
    ((M.numericalType hC hconn).multiplicity i : ℕ) =
      M.toBase.specialFiberMultiplicity π i.val :=
  M.toBase.specialFiberMultiplicity_eq_of_span_eq
    ((IsDiscreteValuationRing.exists_irreducible R).choose_spec.maximalIdeal_eq.symm.trans hπ) i.val

/-- The weight of a component in `M.numericalType` is `dim_k H⁰(Cᵢ, 𝒪_{Cᵢ})`. -/
@[simp] theorem numericalType_weight (i : (M.numericalType hC hconn).Component) :
    ((M.numericalType hC hconn).weight i : ℕ) =
      M.toBase.specialFiberWeight (M.base_numericalType_component hC hconn i) :=
  rfl

/-- The intersection matrix of `M.numericalType` is the special-fibre intersection matrix. -/
@[simp] theorem numericalType_intersection :
    (M.numericalType hC hconn).intersection =
      M.toBase.specialFiberIntersectionMatrix M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) :=
  rfl

/-- The genus of a component in `M.numericalType` is `dim_{κᵢ} H¹(Cᵢ, 𝒪_{Cᵢ})` over `κᵢ`. -/
@[simp] theorem numericalType_genus (i : (M.numericalType hC hconn).Component) :
    (M.numericalType hC hconn).genus i =
      Module.finrank
        Γ((vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme, ⊤)
        (Cohomology (InvertibleSheaf.trivial
          (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme).obj 1) :=
  rfl

/-- Two components of `M.numericalType` are adjacent iff they are distinct and their closures in
`M.total` meet. -/
theorem numericalType_adj_iff (i j : (M.numericalType hC hconn).Component) :
    (M.numericalType hC hconn).Adj i j ↔
      i ≠ j ∧ (closure {(i.val : M.total)} ∩ closure {(j.val : M.total)}).Nonempty :=
  M.toBase.specialFiberNumericalType_adj_iff _ _ hC _ _ hconn i j

/-- For any generator `π` of `maximalIdeal R`, `M.numericalType` equals
`M.toBase.specialFiberNumericalType`. -/
theorem numericalType_eq_specialFiberNumericalType (hX : ∀ x : M.total, coheight x ≤ 2)
    (hη : M.toBase (genericPoint M.total) ≠ closedPoint R) {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) (hreg : IsSMulRegular R π) :
    M.numericalType hC hconn =
      M.toBase.specialFiberNumericalType hX hη hC hπ hreg hconn :=
  M.toBase.specialFiberNumericalType_congr _ _ hC _ _ hconn hπ hreg

/-- Every component of `M.numericalType` has multiplicity one iff the scheme-theoretic special fibre
of `M` is reduced. -/
theorem forall_numericalType_multiplicity_eq_one_iff :
    (∀ i, (M.numericalType hC hconn).multiplicity i = 1) ↔
      IsReduced (specialFiber R M.toBase).left :=
  M.toBase.forall_specialFiberNumericalType_multiplicity_eq_one_iff _ _ hC _ _ hconn

/-- For each component `Cᵢ` of `M.numericalType`, `wᵢ gᵢ = dim_k H¹(Cᵢ, 𝒪_{Cᵢ})`. -/
theorem numericalType_weight_mul_genus (i : (M.numericalType hC hconn).Component) :
    letI := subschemeOverResidueField <|
      M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
        (M.base_numericalType_component hC hconn i)
    ((M.numericalType hC hconn).weight i : ℕ) * (M.numericalType hC hconn).genus i =
      Module.finrank (ResidueField R) (Cohomology (InvertibleSheaf.trivial
        (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme).obj 1) :=
  M.toBase.specialFiberNumericalType_weight_mul_genus _ _ hC _ _ hconn i

/-- For each component `Cᵢ` of `M.numericalType`, `wᵢ (gᵢ - 1) = -χ_k(𝒪_{Cᵢ})`. -/
theorem numericalType_weight_mul_genus_sub_one (i : (M.numericalType hC hconn).Component) :
    letI := subschemeOverResidueField <|
      M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
        (M.base_numericalType_component hC hconn i)
    ((M.numericalType hC hconn).weight i : ℤ) *
        (((M.numericalType hC hconn).genus i : ℤ) - 1) =
      -eulerCharBelow (ResidueField R)
        (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme
        (InvertibleSheaf.trivial
          (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme).obj 2 :=
  M.toBase.specialFiberNumericalType_weight_mul_genus_sub_one _ _ hC _ _ hconn i

/-- Weighted sum of `mᵢ wᵢ (gᵢ - 1)` across `M.numericalType`, equal to `-∑ᵢ mᵢ χ_k(𝒪_{Cᵢ})`. -/
theorem sum_numericalType_multiplicity_mul_weight_mul_genus_sub_one :
    ∑ i : (M.numericalType hC hconn).Component,
        ((M.numericalType hC hconn).multiplicity i : ℤ) *
          ((M.numericalType hC hconn).weight i : ℤ) *
          (((M.numericalType hC hconn).genus i : ℤ) - 1) =
      -∑ i : (M.numericalType hC hconn).Component,
        ((M.numericalType hC hconn).multiplicity i : ℤ) *
          (letI := subschemeOverResidueField <|
            M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              (M.base_numericalType_component hC hconn i)
          eulerCharBelow (ResidueField R)
            (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme
            (InvertibleSheaf.trivial
              (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme).obj 2) :=
  M.toBase.sum_specialFiberNumericalType_multiplicity_mul_weight_mul_genus_sub_one _ _ hC _ _
    hconn

/-- The signed genus of `M.numericalType` in terms of `χ_k(𝒪_{Cᵢ})` and self-intersections. -/
theorem numericalType_arithmeticGenus_eulerCharBelow_selfIntersection :
    (M.numericalType hC hconn).arithmeticGenus =
      1 - (∑ i : (M.numericalType hC hconn).Component,
          ((M.numericalType hC hconn).multiplicity i : ℤ) *
            (letI := subschemeOverResidueField <|
              M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
                (M.base_numericalType_component hC hconn i)
            eulerCharBelow (ResidueField R)
              (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme
              (InvertibleSheaf.trivial (vanishingIdeal
                ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme).obj 2)) -
        (∑ i : (M.numericalType hC hconn).Component,
          ((M.numericalType hC hconn).multiplicity i : ℤ) *
            (M.numericalType hC hconn).intersection i i) / 2 :=
  M.toBase.specialFiberNumericalType_arithmeticGenus_eulerCharBelow_selfIntersection _ _ hC _ _
    hconn

/-- Division-free form of `Model.numericalType_arithmeticGenus_eulerCharBelow_selfIntersection`:
`2 g(T) = 2 - 2 ∑ᵢ mᵢ χ_k(𝒪_{Cᵢ}) - ∑ᵢ mᵢ (Cᵢ · Cᵢ)`. -/
theorem two_mul_numericalType_arithmeticGenus_eulerCharBelow_selfIntersection :
    2 * (M.numericalType hC hconn).arithmeticGenus =
      2 - 2 * (∑ i : (M.numericalType hC hconn).Component,
          ((M.numericalType hC hconn).multiplicity i : ℤ) *
            (letI := subschemeOverResidueField <|
              M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
                (M.base_numericalType_component hC hconn i)
            eulerCharBelow (ResidueField R)
              (vanishingIdeal ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme
              (InvertibleSheaf.trivial (vanishingIdeal
                ⟨closure {(i.val : M.total)}, isClosed_closure⟩).subscheme).obj 2)) -
        ∑ i : (M.numericalType hC hconn).Component,
          ((M.numericalType hC hconn).multiplicity i : ℤ) *
            (M.numericalType hC hconn).intersection i i :=
  M.toBase.two_mul_specialFiberNumericalType_arithmeticGenus_eulerCharBelow_selfIntersection _ _ hC
    _ _ hconn

end ModelAPI

end TauCeti.Model

end
