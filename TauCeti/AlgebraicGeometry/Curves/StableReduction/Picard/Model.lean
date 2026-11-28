/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.SpecialFiber

/-!
# Uniformizer-free vertical Cartier kernel theorems for regular models over a DVR

This file provides uniformizer-free `TauCeti.Model` counterparts of the vertical Cartier and
numerical Picard kernel theorems developed for general scheme morphisms in
`TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.SpecialFiber`, building on
`TauCeti.Model.totalPicSpecialization` from
`TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Specialization` and
`AlgebraicGeometry.Scheme.Hom.verticalLineBundleLinear` from
`TauCeti.AlgebraicGeometry.SpecialFiber.LinearEquivalence`.

For a proper integral regular model `M` with connected special fibre, all points of codimension at
most two, and finite-dimensional `H¹(Cᵢ, 𝒪_{Cᵢ})` on each reduced irreducible component `Cᵢ` of
the special fibre, write `T = M.numericalType hX hC`.

## Main declarations

* `TauCeti.Model.map_specialFiberMultidegree_range_verticalLineBundleLinear`,
  `TauCeti.Model.totalPicSpecialization_comp_verticalLineBundleLinear`,
  `TauCeti.Model.ker_totalPicSpecialization`, and
  `TauCeti.Model.totalPicSpecialization_ofMul_eq_zero_iff`: kernel characterization of
  `M.totalPicSpecialization`
  ([Stacks, Lemma 55.10.1 (Tag 0CDG)](https://stacks.math.columbia.edu/tag/0CDG)), with the
  numerical Picard quotient from
  [Stacks, Definition 55.4.1 (Tag 0C7H)](https://stacks.math.columbia.edu/tag/0C7H).
* `TauCeti.Model.multiplicity_mem_ker_verticalLineBundleLinear`,
  `TauCeti.Model.finrank_ker_verticalLineBundleLinear`,
  `TauCeti.Model.ker_verticalLineBundleLinear_eq_span_of_gcd_eq_one`,
  `TauCeti.Model.ker_verticalLineBundleLinear_eq_span_of_multiplicity_eq_one`, and
  `TauCeti.Model.mem_ker_verticalLineBundleLinear_iff_of_isReduced`: membership, rank, and span of
  the vertical Cartier kernel.

## References

* [The Stacks Project, Definition 55.4.1 (Tag 0C7H)](https://stacks.math.columbia.edu/tag/0C7H),
  [Section 55.9 (Tag 0C5Y)](https://stacks.math.columbia.edu/tag/0C5Y), and
  [Lemma 55.10.1 (Tag 0CDG)](https://stacks.math.columbia.edu/tag/0CDG).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order Matrix
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal
  isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular)
open LineBundleClass (intersectionNumber)

universe u

namespace TauCeti.Model

attribute [local instance] Model.isNoetherian_total

section ModelPicard

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
  (M : Model R K C toK) [M.IsProper] [IsIntegral M.total]
  [TauCeti.AlgebraicGeometry.IsRegular M.total] [ConnectedSpace (specialFiber R M.toBase).left]
  (hX : ∀ x : M.total, coheight x ≤ 2)
  (hC : M.toBase.HasFiniteDimensionalSpecialFiberComponentTrivialCohomologyOne)

local notation "𝒯ₘ" => M.numericalType hX hC
local notation "mbase" => M.base_eq_closedPoint_of_numericalType hX hC

/-- Vertical combinations of special-fibre components of `M` map onto `principalDivisors`. -/
theorem map_specialFiberMultidegree_range_verticalLineBundleLinear :
    (LinearMap.range (M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)))).map
        (M.toBase.specialFiberMultidegree hX
          (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
          M.toBase.specialFiberCohomologyFiniteDimensional_zero
          hC.finiteDimensional_one).toIntLinearMap =
      (𝒯ₘ).principalDivisors :=
  M.toBase.map_specialFiberMultidegree_range_verticalLineBundleLinear hX _ hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint

/-- Vertical combinations of special-fibre components of `M` map to `0` in `Pic`. -/
@[simp] theorem totalPicSpecialization_comp_verticalLineBundleLinear :
    (M.totalPicSpecialization hX hC).toIntLinearMap ∘ₗ M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) =
      0 := by
  ext v
  simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.zero_apply,
    M.totalPicSpecialization_apply hX hC]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  rw [M.toBase.specialFiberMultidegree_verticalLineBundleLinear]
  change _ ∈ (M.toBase.specialFiberNumericalType hX
      (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) hC
      TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
      TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
      M.isPreconnected_preimage_closedPoint).principalDivisors
  rw [M.toBase.specialFiberNumericalType_principalDivisors]
  exact ⟨v, rfl⟩

/-- Pointwise form of `M.totalPicSpecialization_comp_verticalLineBundleLinear`. -/
@[simp high] lemma totalPicSpecialization_verticalLineBundleLinear (v : (𝒯ₘ).Component → ℤ) :
    M.totalPicSpecialization hX hC (M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) v) =
      0 :=
  LinearMap.congr_fun (M.totalPicSpecialization_comp_verticalLineBundleLinear hX hC) v

/-- **Kernel of `M.totalPicSpecialization`**
([Stacks, Lemma 55.10.1 (Tag 0CDG)](https://stacks.math.columbia.edu/tag/0CDG)):
`ker M.totalPicSpecialization.toIntLinearMap =
  ker specialFiberMultidegree.toIntLinearMap ⊔ range verticalLineBundleLinear`. -/
theorem ker_totalPicSpecialization :
    LinearMap.ker (M.totalPicSpecialization hX hC).toIntLinearMap =
      LinearMap.ker (M.toBase.specialFiberMultidegree hX
          (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
          M.toBase.specialFiberCohomologyFiniteDimensional_zero
          hC.finiteDimensional_one).toIntLinearMap ⊔
        LinearMap.range (M.toBase.verticalLineBundleLinear hX
          (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) := by
  have hcomp :
      (M.totalPicSpecialization hX hC).toIntLinearMap =
        (𝒯ₘ).principalDivisors.mkQ ∘ₗ (M.toBase.specialFiberMultidegree hX
          (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
          M.toBase.specialFiberCohomologyFiniteDimensional_zero
          hC.finiteDimensional_one).toIntLinearMap :=
    LinearMap.ext fun x ↦ M.totalPicSpecialization_apply hX hC x
  refine (congrArg LinearMap.ker hcomp).trans ?_
  refine (LinearMap.ker_comp _ _).trans ?_
  rw [Submodule.ker_mkQ, ← M.map_specialFiberMultidegree_range_verticalLineBundleLinear hX hC]
  exact (Submodule.comap_map_eq _ _).trans (sup_comm _ _)

/-- **Pointwise kernel characterization of `M.totalPicSpecialization`**: a class `a` on `M.total`
maps to `0` in `(𝒯ₘ).Pic` iff some vertical twist has degree zero on every component `Cⱼ`. -/
theorem totalPicSpecialization_ofMul_eq_zero_iff (a : LineBundleClass M.total) :
    M.totalPicSpecialization hX hC (Additive.ofMul a) = 0 ↔ ∃ v : (𝒯ₘ).Component → ℤ,
        ∀ j : (𝒯ₘ).Component,
          (letI := subschemeOverResidueField
            (M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton (mbase j))
          intersectionNumber (ResidueField R)
            (vanishingIdeal ⟨closure {(j.val : M.total)}, isClosed_closure⟩).subschemeι
            (a * ∏ i : (𝒯ₘ).Component,
              (LineBundleClass.mk (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular
                hX i.val.property).toInvertibleSheaf)⁻¹ ^ v i)) = 0 := by
  let vlin := M.toBase.verticalLineBundleLinear hX
    (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
  have hbmul (w : (𝒯ₘ).Component → ℤ) :
      (Additive.ofMul a + vlin w).toMul =
        a * ∏ i : (𝒯ₘ).Component,
          (LineBundleClass.mk (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular
            hX i.val.property).toInvertibleSheaf)⁻¹ ^ w i := by
    rw [toMul_add, toMul_ofMul]
    exact congrArg (a * ·) (M.toBase.toMul_verticalLineBundleLinear_apply hX _ w)
  change Additive.ofMul a ∈ LinearMap.ker (M.totalPicSpecialization hX hC).toIntLinearMap ↔ _
  rw [ker_totalPicSpecialization, Submodule.mem_sup]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, hb, _, ⟨v, rfl⟩, hbv⟩
    have hb' : Additive.ofMul a + vlin (-v) = b := by
      rw [map_neg, ← hbv, add_neg_cancel_right]
    rw [← hb', LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, ← ofMul_toMul
      (Additive.ofMul a + vlin (-v)), M.toBase.specialFiberMultidegree_eq_zero_iff] at hb
    exact ⟨-v, fun j ↦ by rw [← hbmul (-v)]; exact hb j⟩
  · rintro ⟨v, hv⟩
    have hneg : vlin (-v) = -vlin v := map_neg _ _
    refine ⟨Additive.ofMul a + vlin v, ?_, vlin (-v), ⟨-v, rfl⟩, by rw [hneg, add_neg_cancel_right]⟩
    rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, ← ofMul_toMul
      (Additive.ofMul a + vlin v), M.toBase.specialFiberMultidegree_eq_zero_iff]
    exact fun j ↦ by rw [hbmul v]; exact hv j

/-- The multiplicity vector `i ↦ ((𝒯ₘ).multiplicity i : ℤ)` of `M` lies in
`ker verticalLineBundleLinear`. -/
theorem multiplicity_mem_ker_verticalLineBundleLinear :
    (fun i : (𝒯ₘ).Component ↦ ((𝒯ₘ).multiplicity i : ℤ)) ∈
      LinearMap.ker (M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) :=
  M.toBase.multiplicity_mem_ker_verticalLineBundleLinear hX _
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose

/-- Every vertical divisor linearly equivalent to zero on `M.total` lies in
`ker T.intersection.vecMulLinear`. -/
theorem ker_verticalLineBundleLinear_le_ker_vecMulLinear_intersection :
    LinearMap.ker (M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) ≤
      LinearMap.ker (𝒯ₘ).intersection.vecMulLinear :=
  M.toBase.ker_verticalLineBundleLinear_le_ker_vecMulLinear_intersection hX _ hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint

/-- Any `v ∈ ker verticalLineBundleLinear` satisfies `mⱼ vᵢ = mᵢ vⱼ` for all `i, j`. -/
theorem multiplicity_mul_eq_of_mem_ker_verticalLineBundleLinear {v : (𝒯ₘ).Component → ℤ}
    (hv : v ∈ LinearMap.ker (M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))))
    (i j : (𝒯ₘ).Component) :
    ((𝒯ₘ).multiplicity j : ℤ) * v i = ((𝒯ₘ).multiplicity i : ℤ) * v j :=
  M.toBase.multiplicity_mul_eq_of_mem_ker_verticalLineBundleLinear hX _ hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint hv i j

include hC in
/-- The kernel of `verticalLineBundleLinear` on `M` has `ℤ`-rank `1`. -/
theorem finrank_ker_verticalLineBundleLinear :
    Module.finrank ℤ (LinearMap.ker (M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)))) =
      1 :=
  M.toBase.finrank_ker_verticalLineBundleLinear hX _ hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint

/-- If the component multiplicities of `M.numericalType` are coprime (`gcd = 1`),
`ker verticalLineBundleLinear` is spanned over `ℤ` by the multiplicity vector `i ↦ mᵢ`. -/
theorem ker_verticalLineBundleLinear_eq_span_of_gcd_eq_one
    (hgcd : Finset.univ.gcd (fun i : (𝒯ₘ).Component ↦ ((𝒯ₘ).multiplicity i : ℕ)) = 1) :
    LinearMap.ker (M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) =
      Submodule.span ℤ {fun i ↦ ((𝒯ₘ).multiplicity i : ℤ)} :=
  M.toBase.ker_verticalLineBundleLinear_eq_span_of_gcd_eq_one hX _ hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint hgcd

/-- If some component of `M.numericalType` has multiplicity `1`, `ker verticalLineBundleLinear`
is spanned by the multiplicity vector. -/
theorem ker_verticalLineBundleLinear_eq_span_of_multiplicity_eq_one
    {i₀ : (𝒯ₘ).Component} (hi₀ : (𝒯ₘ).multiplicity i₀ = 1) :
    LinearMap.ker (M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) =
      Submodule.span ℤ {fun i ↦ ((𝒯ₘ).multiplicity i : ℤ)} :=
  M.toBase.ker_verticalLineBundleLinear_eq_span_of_multiplicity_eq_one hX _ hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint hi₀

/-- When `M_s` is reduced, `ker verticalLineBundleLinear` consists of constant tuples. -/
theorem mem_ker_verticalLineBundleLinear_iff_of_isReduced
    [IsReduced (specialFiber R M.toBase).left] (v : (𝒯ₘ).Component → ℤ) :
    v ∈ LinearMap.ker (M.toBase.verticalLineBundleLinear hX
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) ↔
      ∃ c : ℤ, v = fun _ ↦ c :=
  M.toBase.mem_ker_verticalLineBundleLinear_iff_of_isReduced hX _ hC
    TauCeti.IsDiscreteValuationRing.maximalIdeal_eq_span_exists_irreducible_choose
    TauCeti.IsDiscreteValuationRing.isSMulRegular_exists_irreducible_choose
    M.isPreconnected_preimage_closedPoint v

end ModelPicard

end TauCeti.Model

end
