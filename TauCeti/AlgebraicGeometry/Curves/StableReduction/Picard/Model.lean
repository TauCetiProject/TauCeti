/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Model
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.SpecialFiber

/-!
# Uniformizer-free Picard specialization for regular models over a DVR

This file provides uniformizer-free `TauCeti.Model` counterparts of the numerical Picard
specialization, `ZMod ℓ`-linear torsion specialization, and vertical Cartier kernel theorems
developed for general scheme morphisms in
`TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.SpecialFiber`, building on the linear
multidegree maps from `TauCeti.AlgebraicGeometry.IntersectionNumber.Specialization` and the
vertical Cartier homomorphism from `TauCeti.AlgebraicGeometry.SpecialFiber.LinearEquivalence`.

For a proper integral regular model `M` of relative dimension at most one over a discrete valuation
ring `R` with connected special fibre and finite-dimensional `H¹(Cᵢ, 𝒪_{Cᵢ})` on each reduced
irreducible component `Cᵢ` of the special fibre, write `T = M.numericalType hC hconn`. The
torsion specialization maps `reducedSpecialFiberNumericalPicTorsionMap`,
`specialFiberNumericalPicTorsionMap`, and `numericalPicTorsionMap` vanish identically for every
`ℓ > 0` because multidegrees take values in the torsion-free group `T.Component → ℤ`.

## Main declarations

* `TauCeti.Model.reducedSpecialFiberNumericalPicLinear`,
  `TauCeti.Model.specialFiberNumericalPicLinear`, and `TauCeti.Model.numericalPicLinear`:
  `ℤ`-linear numerical Picard specialization maps into `T.Pic`.
* `TauCeti.Model.reducedSpecialFiberNumericalPicTorsionMap`,
  `TauCeti.Model.specialFiberNumericalPicTorsionMap`, and `TauCeti.Model.numericalPicTorsionMap`:
  `ZMod ℓ`-linear specialization maps into `T.torsion ℓ` (vanishing for `ℓ > 0`).
* `TauCeti.Model.ker_numericalPicLinear` and `TauCeti.Model.numericalPicLinear_ofMul_eq_zero_iff`:
  [Stacks, Lemma 55.10.1 (Tag 0CDG)](https://stacks.math.columbia.edu/tag/0CDG).
* `TauCeti.Model.finrank_ker_verticalLineBundleLinear`,
  `TauCeti.Model.ker_verticalLineBundleLinear_eq_span_of_gcd_eq_one`,
  `TauCeti.Model.ker_verticalLineBundleLinear_eq_span_of_multiplicity_eq_one`, and
  `TauCeti.Model.mem_ker_verticalLineBundleLinear_iff_of_isReduced`: rank and span of the vertical
  Cartier kernel.

## References

* [The Stacks Project, Tag 0C7H](https://stacks.math.columbia.edu/tag/0C7H),
  [Section 55.9 (Tag 0C5Y)](https://stacks.math.columbia.edu/tag/0C5Y), and
  [Lemma 55.10.1 (Tag 0CDG)](https://stacks.math.columbia.edu/tag/0CDG).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order Matrix
open AddSubgroup (torsionBy)
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal
  isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular)
open LineBundleClass (intersectionNumber pullbackLinearMap pullbackTorsionLinearMap
  pullbackTorsionLinearEquiv)

universe u

namespace TauCeti.Model

section ModelPicard

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
  (M : Model R K C toK) [M.IsProper] [RelativeDimensionLE 1 M.toBase] [IsIntegral M.total]
  [TauCeti.AlgebraicGeometry.IsRegular M.total]
  (hC : M.toBase.HasFiniteDimensionalSpecialFiberComponentTrivialCohomologyOne)
  (hconn : _root_.IsPreconnected (M.toBase ⁻¹' {closedPoint R}))

local notation "𝒯ₘ" => M.numericalType hC hconn
local notation "mbase" => M.base_numericalType_component hC hconn

/-- **Numerical Picard specialization on `M_{s,red}`.** -/
def reducedSpecialFiberNumericalPicLinear :
    Additive (LineBundleClass (reducedSpecialFiber R M.toBase)) →ₗ[ℤ] (𝒯ₘ).Pic :=
  M.toBase.reducedSpecialFiberNumericalPicLinear _ _ hC _ _ hconn

/-- **Numerical Picard specialization on `M_s`.** -/
def specialFiberNumericalPicLinear :
    Additive (LineBundleClass (specialFiber R M.toBase).left) →ₗ[ℤ] (𝒯ₘ).Pic :=
  M.toBase.specialFiberNumericalPicLinear _ _ hC _ _ hconn

/-- **Numerical Picard specialization on `M.total`.** -/
def numericalPicLinear : Additive (LineBundleClass M.total) →ₗ[ℤ] (𝒯ₘ).Pic :=
  M.toBase.numericalPicLinear _ _ hC _ _ hconn

/-- **`ZMod ℓ`-linear torsion specialization on `M_{s,red}`.** Since
`reducedSpecialFiberMultidegree` takes values in the torsion-free group `(𝒯ₘ).Component → ℤ`, this
map vanishes identically for every `ℓ > 0`
(`Model.reducedSpecialFiberNumericalPicTorsionMap_eq_zero`). -/
def reducedSpecialFiberNumericalPicTorsionMap (ℓ : ℕ) :
    torsionBy (Additive (LineBundleClass (reducedSpecialFiber R M.toBase))) (ℓ : ℤ) →ₗ[ZMod ℓ]
      (𝒯ₘ).torsion ℓ :=
  M.toBase.reducedSpecialFiberNumericalPicTorsionMap _ _ hC _ _ hconn ℓ

/-- **`ZMod ℓ`-linear torsion specialization on `M_s`.** Since `specialFiberMultidegreeOnFiber`
takes values in the torsion-free group `(𝒯ₘ).Component → ℤ`, this map vanishes identically for every
`ℓ > 0` (`Model.specialFiberNumericalPicTorsionMap_eq_zero`). -/
def specialFiberNumericalPicTorsionMap (ℓ : ℕ) :
    torsionBy (Additive (LineBundleClass (specialFiber R M.toBase).left)) (ℓ : ℤ) →ₗ[ZMod ℓ]
      (𝒯ₘ).torsion ℓ :=
  M.toBase.specialFiberNumericalPicTorsionMap _ _ hC _ _ hconn ℓ

/-- **`ZMod ℓ`-linear torsion specialization on `M.total`.** Since `specialFiberMultidegree` takes
values in the torsion-free group `(𝒯ₘ).Component → ℤ`, this map vanishes identically for every
`ℓ > 0` (`Model.numericalPicTorsionMap_eq_zero`). -/
def numericalPicTorsionMap (ℓ : ℕ) :
    torsionBy (Additive (LineBundleClass M.total)) (ℓ : ℤ) →ₗ[ZMod ℓ] (𝒯ₘ).torsion ℓ :=
  M.toBase.numericalPicTorsionMap _ _ hC _ _ hconn ℓ

/-- `M.reducedSpecialFiberNumericalPicLinear` sends `a` to the quotient class of its multidegree. -/
@[simp] lemma reducedSpecialFiberNumericalPicLinear_apply
    (a : Additive (LineBundleClass (reducedSpecialFiber R M.toBase))) :
    M.reducedSpecialFiberNumericalPicLinear hC hconn a =
      Submodule.Quotient.mk (M.toBase.reducedSpecialFiberMultidegree
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
        M.toBase.specialFiberCohomologyFiniteDimensional_zero
        hC.specialFiberCohomologyFiniteDimensional_one a) := by
  exact M.toBase.reducedSpecialFiberNumericalPicLinear_apply _ _ hC _ _ hconn a

/-- `M.specialFiberNumericalPicLinear` sends `a` to the quotient class of its multidegree. -/
lemma specialFiberNumericalPicLinear_apply
    (a : Additive (LineBundleClass (specialFiber R M.toBase).left)) :
    M.specialFiberNumericalPicLinear hC hconn a =
      Submodule.Quotient.mk (M.toBase.specialFiberMultidegreeOnFiber
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
        M.toBase.specialFiberCohomologyFiniteDimensional_zero
        hC.specialFiberCohomologyFiniteDimensional_one a) := by
  exact M.toBase.specialFiberNumericalPicLinear_apply _ _ hC _ _ hconn a

/-- `M.numericalPicLinear` sends `a` to the quotient class of its multidegree. -/
@[simp] lemma numericalPicLinear_apply (a : Additive (LineBundleClass M.total)) :
    M.numericalPicLinear hC hconn a =
      Submodule.Quotient.mk (M.toBase.specialFiberMultidegree
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
        M.toBase.specialFiberCohomologyFiniteDimensional_zero
        hC.specialFiberCohomologyFiniteDimensional_one a) := by
  exact M.toBase.numericalPicLinear_apply _ _ hC _ _ hconn a

/-- `M.specialFiberNumericalPicLinear` factors through pullback to `M_{s,red}`. -/
@[simp] lemma
  reducedSpecialFiberNumericalPicLinear_comp_pullbackLinearMap_reducedSpecialFiberToSpecialFiber :
    M.reducedSpecialFiberNumericalPicLinear hC hconn ∘ₗ
        pullbackLinearMap (reducedSpecialFiberToSpecialFiber R M.toBase) =
      M.specialFiberNumericalPicLinear hC hconn := by
  let f := M.toBase; exact
  f.reducedSpecialFiberNumericalPicLinear_comp_pullbackLinearMap_reducedSpecialFiberToSpecialFiber
    _ _ hC _ _ hconn

/-- `M.numericalPicLinear` factors through pullback along `M_s ⟶ M.total`. -/
@[simp] lemma specialFiberNumericalPicLinear_comp_pullbackLinearMap_specialFiberι :
    M.specialFiberNumericalPicLinear hC hconn ∘ₗ pullbackLinearMap (specialFiberι R M.toBase) =
      M.numericalPicLinear hC hconn := by
  exact M.toBase.specialFiberNumericalPicLinear_comp_pullbackLinearMap_specialFiberι
    _ _ hC _ _ hconn

/-- `M.numericalPicLinear` factors through pullback along `M_{s,red} ⟶ M.total`. -/
@[simp] lemma reducedSpecialFiberNumericalPicLinear_comp_pullbackLinearMap_reducedSpecialFiberι :
    M.reducedSpecialFiberNumericalPicLinear hC hconn ∘ₗ
        pullbackLinearMap (reducedSpecialFiberι R M.toBase) = M.numericalPicLinear hC hconn := by
  exact M.toBase.reducedSpecialFiberNumericalPicLinear_comp_pullbackLinearMap_reducedSpecialFiberι
    _ _ hC _ _ hconn

/-- The numerical degree of `M.reducedSpecialFiberNumericalPicLinear a` is `∑ⱼ mⱼ (a · Cⱼ)`. -/
theorem degree_reducedSpecialFiberNumericalPicLinear
    (a : Additive (LineBundleClass (reducedSpecialFiber R M.toBase))) :
    (𝒯ₘ).degree (M.reducedSpecialFiberNumericalPicLinear hC hconn a) =
      ∑ j : (𝒯ₘ).Component, ((𝒯ₘ).multiplicity j : ℤ) *
          (letI := subschemeOverResidueField
            (M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton (mbase j))
          intersectionNumber (ResidueField R) (subschemeToReducedSpecialFiber
            (M.toBase.ker_reducedSpecialFiberι_le_vanishingIdeal_closure_singleton (mbase j)))
            a.toMul) := by
  exact M.toBase.degree_reducedSpecialFiberNumericalPicLinear _ _ hC _ _ hconn a

/-- The numerical degree of `M.specialFiberNumericalPicLinear a` is `∑ⱼ mⱼ (a · Cⱼ)`. -/
theorem degree_specialFiberNumericalPicLinear
    (a : Additive (LineBundleClass (specialFiber R M.toBase).left)) :
    (𝒯ₘ).degree (M.specialFiberNumericalPicLinear hC hconn a) =
      ∑ j : (𝒯ₘ).Component, ((𝒯ₘ).multiplicity j : ℤ) *
          (letI := subschemeOverResidueField
            (M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton (mbase j))
          intersectionNumber (ResidueField R) (subschemeToSpecialFiber
            (M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton (mbase j)))
            a.toMul) := by
  exact M.toBase.degree_specialFiberNumericalPicLinear _ _ hC _ _ hconn a

/-- The numerical degree of `M.numericalPicLinear a` is `∑ⱼ mⱼ (a · Cⱼ)`. -/
theorem degree_numericalPicLinear (a : Additive (LineBundleClass M.total)) :
    (𝒯ₘ).degree (M.numericalPicLinear hC hconn a) =
      ∑ j : (𝒯ₘ).Component, ((𝒯ₘ).multiplicity j : ℤ) *
          (letI := subschemeOverResidueField
            (M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton (mbase j))
          intersectionNumber (ResidueField R)
            (vanishingIdeal ⟨closure {(j.val : M.total)}, isClosed_closure⟩).subschemeι
            a.toMul) := by
  exact M.toBase.degree_numericalPicLinear _ _ hC _ _ hconn a

/-- Underlying `Pic` value of `M.reducedSpecialFiberNumericalPicTorsionMap`. -/
@[simp] lemma coe_reducedSpecialFiberNumericalPicTorsionMap_apply (ℓ : ℕ)
    (a : torsionBy (Additive (LineBundleClass (reducedSpecialFiber R M.toBase))) (ℓ : ℤ)) :
    (M.reducedSpecialFiberNumericalPicTorsionMap hC hconn ℓ a : (𝒯ₘ).Pic) =
      M.reducedSpecialFiberNumericalPicLinear hC hconn a.val := by
  exact M.toBase.coe_reducedSpecialFiberNumericalPicTorsionMap_apply _ _ hC _ _ hconn ℓ a

/-- Underlying `Pic` value of `M.specialFiberNumericalPicTorsionMap`. -/
lemma coe_specialFiberNumericalPicTorsionMap_apply (ℓ : ℕ)
    (a : torsionBy (Additive (LineBundleClass (specialFiber R M.toBase).left)) (ℓ : ℤ)) :
    (M.specialFiberNumericalPicTorsionMap hC hconn ℓ a : (𝒯ₘ).Pic) =
      M.specialFiberNumericalPicLinear hC hconn a.val := by
  exact M.toBase.coe_specialFiberNumericalPicTorsionMap_apply _ _ hC _ _ hconn ℓ a

/-- Underlying `Pic` value of `M.numericalPicTorsionMap`. -/
@[simp] lemma coe_numericalPicTorsionMap_apply (ℓ : ℕ)
    (a : torsionBy (Additive (LineBundleClass M.total)) (ℓ : ℤ)) :
    (M.numericalPicTorsionMap hC hconn ℓ a : (𝒯ₘ).Pic) =
      M.numericalPicLinear hC hconn a.val := by
  exact M.toBase.coe_numericalPicTorsionMap_apply _ _ hC _ _ hconn ℓ a

/-- For every `ℓ > 0` (`hℓ : ℓ ≠ 0`), `M.reducedSpecialFiberNumericalPicTorsionMap` vanishes
identically because `reducedSpecialFiberMultidegree` takes values in the torsion-free group
`(𝒯ₘ).Component → ℤ`. -/
@[simp] theorem reducedSpecialFiberNumericalPicTorsionMap_eq_zero {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    M.reducedSpecialFiberNumericalPicTorsionMap hC hconn ℓ = 0 :=
  M.toBase.reducedSpecialFiberNumericalPicTorsionMap_eq_zero _ _ hC _ _ hconn hℓ

/-- For every `ℓ > 0` (`hℓ : ℓ ≠ 0`), `M.specialFiberNumericalPicTorsionMap` vanishes identically
because `specialFiberMultidegreeOnFiber` takes values in the torsion-free group
`(𝒯ₘ).Component → ℤ`. -/
@[simp] theorem specialFiberNumericalPicTorsionMap_eq_zero {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    M.specialFiberNumericalPicTorsionMap hC hconn ℓ = 0 :=
  M.toBase.specialFiberNumericalPicTorsionMap_eq_zero _ _ hC _ _ hconn hℓ

/-- For every `ℓ > 0` (`hℓ : ℓ ≠ 0`), `M.numericalPicTorsionMap` vanishes identically because
`specialFiberMultidegree` takes values in the torsion-free group `(𝒯ₘ).Component → ℤ`. -/
@[simp] theorem numericalPicTorsionMap_eq_zero {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    M.numericalPicTorsionMap hC hconn ℓ = 0 :=
  M.toBase.numericalPicTorsionMap_eq_zero _ _ hC _ _ hconn hℓ

/-- `M.specialFiberNumericalPicTorsionMap` factors through torsion pullback to `M_{s,red}`. -/
@[simp] lemma reducedSpecialFiberNumericalPicTorsionMap_comp_pullbackTorsionLinearMap
    (ℓ : ℕ) : M.reducedSpecialFiberNumericalPicTorsionMap hC hconn ℓ ∘ₗ
        pullbackTorsionLinearMap (reducedSpecialFiberToSpecialFiber R M.toBase) ℓ =
      M.specialFiberNumericalPicTorsionMap hC hconn ℓ := by
  exact M.toBase.reducedSpecialFiberNumericalPicTorsionMap_comp_pullbackTorsionLinearMap
    _ _ hC _ _ hconn ℓ

/-- `M.numericalPicTorsionMap` factors through torsion pullback along `M_s ⟶ M.total`. -/
@[simp] lemma specialFiberNumericalPicTorsionMap_comp_pullbackTorsionLinearMap_specialFiberι
    (ℓ : ℕ) : M.specialFiberNumericalPicTorsionMap hC hconn ℓ ∘ₗ
        pullbackTorsionLinearMap (specialFiberι R M.toBase) ℓ =
      M.numericalPicTorsionMap hC hconn ℓ := by
  exact M.toBase.specialFiberNumericalPicTorsionMap_comp_pullbackTorsionLinearMap_specialFiberι
    _ _ hC _ _ hconn ℓ

/-- `M.numericalPicTorsionMap` factors through torsion pullback along `M_{s,red} ⟶ M.total`. -/
@[simp] lemma
  reducedSpecialFiberNumericalPicTorsionMap_comp_pullbackTorsionLinearMap_reducedSpecialFiberι
    (ℓ : ℕ) : M.reducedSpecialFiberNumericalPicTorsionMap hC hconn ℓ ∘ₗ
        pullbackTorsionLinearMap (reducedSpecialFiberι R M.toBase) ℓ =
      M.numericalPicTorsionMap hC hconn ℓ := by
  let f := M.toBase; exact
  f.reducedSpecialFiberNumericalPicTorsionMap_comp_pullbackTorsionLinearMap_reducedSpecialFiberι
    _ _ hC _ _ hconn ℓ

/-- When `M_s` is reduced, `M.specialFiberNumericalPicTorsionMap` factors through
`LineBundleClass.pullbackTorsionLinearEquiv` along `M_{s,red} ≅ M_s`. -/
theorem specialFiberNumericalPicTorsionMap_eq_comp_pullbackTorsionLinearEquiv
    [IsReduced (specialFiber R M.toBase).left] (ℓ : ℕ) :
    haveI := (isIso_reducedSpecialFiberToSpecialFiber_iff R M.toBase).mpr inferInstance
    M.specialFiberNumericalPicTorsionMap hC hconn ℓ =
      M.reducedSpecialFiberNumericalPicTorsionMap hC hconn ℓ ∘ₗ (pullbackTorsionLinearEquiv
          (asIso (reducedSpecialFiberToSpecialFiber R M.toBase)) ℓ).toLinearMap := by
  exact M.toBase.specialFiberNumericalPicTorsionMap_eq_comp_pullbackTorsionLinearEquiv _ _ hC _ _
    hconn ℓ

/-- Vertical combinations of special-fibre components of `M` map onto `principalDivisors`. -/
theorem map_specialFiberMultidegree_range_verticalLineBundleLinear :
    (LinearMap.range (M.toBase.verticalLineBundleLinear
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)))).map
        (M.toBase.specialFiberMultidegree M.toBase.coheight_le_succ_of_relativeDimensionLE
          (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
          M.toBase.specialFiberCohomologyFiniteDimensional_zero
          hC.specialFiberCohomologyFiniteDimensional_one) =
      (𝒯ₘ).principalDivisors := by
  exact M.toBase.map_specialFiberMultidegree_range_verticalLineBundleLinear _ _ hC _ _ hconn

/-- Vertical combinations of special-fibre components of `M` map to `0` in `Pic`. -/
@[simp] theorem numericalPicLinear_comp_verticalLineBundleLinear :
    M.numericalPicLinear hC hconn ∘ₗ M.toBase.verticalLineBundleLinear
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) =
      0 := by
  exact M.toBase.numericalPicLinear_comp_verticalLineBundleLinear _ _ hC _ _ hconn

/-- Pointwise form of `M.numericalPicLinear_comp_verticalLineBundleLinear`. -/
@[simp high] lemma numericalPicLinear_verticalLineBundleLinear (v : (𝒯ₘ).Component → ℤ) :
    M.numericalPicLinear hC hconn (M.toBase.verticalLineBundleLinear
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)) v) =
      0 := by
  exact M.toBase.numericalPicLinear_verticalLineBundleLinear _ _ hC _ _ hconn v

/-- **[Stacks, Lemma 55.10.1 (Tag 0CDG)](https://stacks.math.columbia.edu/tag/0CDG) for `M`:**
`ker M.numericalPicLinear = ker specialFiberMultidegree ⊔ range verticalLineBundleLinear`. -/
theorem ker_numericalPicLinear : LinearMap.ker (M.numericalPicLinear hC hconn) =
      LinearMap.ker (M.toBase.specialFiberMultidegree
          M.toBase.coheight_le_succ_of_relativeDimensionLE
          (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))
          M.toBase.specialFiberCohomologyFiniteDimensional_zero
          hC.specialFiberCohomologyFiniteDimensional_one) ⊔
        LinearMap.range (M.toBase.verticalLineBundleLinear
          M.toBase.coheight_le_succ_of_relativeDimensionLE
          (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) := by
  exact M.toBase.ker_numericalPicLinear _ _ hC _ _ hconn

/-- **[Stacks, Lemma 55.10.1 (Tag 0CDG)](https://stacks.math.columbia.edu/tag/0CDG).** A class `a`
on `M.total` maps to `0` in `(𝒯ₘ).Pic` iff some vertical twist has degree zero on every component
`Cⱼ`. -/
theorem numericalPicLinear_ofMul_eq_zero_iff (a : LineBundleClass M.total) :
    M.numericalPicLinear hC hconn (Additive.ofMul a) = 0 ↔ ∃ v : (𝒯ₘ).Component → ℤ,
        ∀ j : (𝒯ₘ).Component,
          (letI := subschemeOverResidueField
            (M.toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton (mbase j))
          intersectionNumber (ResidueField R)
            (vanishingIdeal ⟨closure {(j.val : M.total)}, isClosed_closure⟩).subschemeι
            (a * ∏ i : (𝒯ₘ).Component,
              (LineBundleClass.mk (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular
                M.toBase.coheight_le_succ_of_relativeDimensionLE
                i.val.property).toInvertibleSheaf)⁻¹ ^ v i)) = 0 := by
  exact M.toBase.numericalPicLinear_ofMul_eq_zero_iff _ _ hC _ _ hconn a

/-- Every vertical divisor linearly equivalent to zero on `M.total` lies in `ker intersection`. -/
theorem ker_verticalLineBundleLinear_le_ker_intersection :
    LinearMap.ker (M.toBase.verticalLineBundleLinear
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) ≤
      LinearMap.ker (𝒯ₘ).intersection.vecMulLinear := by
  exact M.toBase.ker_verticalLineBundleLinear_le_ker_intersection _ _ hC _ _ hconn

/-- Any `v ∈ ker verticalLineBundleLinear` satisfies `mⱼ vᵢ = mᵢ vⱼ` for all `i, j`. -/
theorem multiplicity_mul_eq_of_mem_ker_verticalLineBundleLinear {v : (𝒯ₘ).Component → ℤ}
    (hv : v ∈ LinearMap.ker (M.toBase.verticalLineBundleLinear
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))))
    (i j : (𝒯ₘ).Component) :
    ((𝒯ₘ).multiplicity j : ℤ) * v i = ((𝒯ₘ).multiplicity i : ℤ) * v j := by
  exact M.toBase.multiplicity_mul_eq_of_mem_ker_verticalLineBundleLinear _ _ hC _ _ hconn hv i j

include hC hconn in
/-- The kernel of `verticalLineBundleLinear` on `M` has `ℤ`-rank `1`. -/
theorem finrank_ker_verticalLineBundleLinear :
    Module.finrank ℤ (LinearMap.ker (M.toBase.verticalLineBundleLinear
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R)))) =
      1 := by
  exact M.toBase.finrank_ker_verticalLineBundleLinear _ _ hC
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec.maximalIdeal_eq
    (mul_right_injective₀ (IsDiscreteValuationRing.exists_irreducible R).choose_spec.ne_zero)
    hconn

/-- If the component multiplicities of `M.numericalType` are coprime (`gcd = 1`),
`ker verticalLineBundleLinear` is spanned over `ℤ` by the multiplicity vector `i ↦ mᵢ`. -/
theorem ker_verticalLineBundleLinear_eq_span_of_gcd_eq_one
    (hgcd : Finset.univ.gcd (fun i : (𝒯ₘ).Component ↦ ((𝒯ₘ).multiplicity i : ℕ)) = 1) :
    LinearMap.ker (M.toBase.verticalLineBundleLinear
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) =
      Submodule.span ℤ {fun i ↦ ((𝒯ₘ).multiplicity i : ℤ)} := by
  exact M.toBase.ker_verticalLineBundleLinear_eq_span_of_gcd_eq_one _ _ hC _ _ hconn hgcd

/-- If some component of `M.numericalType` has multiplicity `1`, `ker verticalLineBundleLinear`
is spanned by the multiplicity vector. -/
theorem ker_verticalLineBundleLinear_eq_span_of_multiplicity_eq_one
    {i₀ : (𝒯ₘ).Component} (hi₀ : (𝒯ₘ).multiplicity i₀ = 1) :
    LinearMap.ker (M.toBase.verticalLineBundleLinear
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) =
      Submodule.span ℤ {fun i ↦ ((𝒯ₘ).multiplicity i : ℤ)} := by
  exact M.toBase.ker_verticalLineBundleLinear_eq_span_of_multiplicity_eq_one _ _ hC _ _ hconn hi₀

/-- When `M_s` is reduced, `ker verticalLineBundleLinear` consists of constant tuples. -/
theorem mem_ker_verticalLineBundleLinear_iff_of_isReduced
    [IsReduced (specialFiber R M.toBase).left] (v : (𝒯ₘ).Component → ℤ) :
    v ∈ LinearMap.ker (M.toBase.verticalLineBundleLinear
        M.toBase.coheight_le_succ_of_relativeDimensionLE
        (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))) ↔
      ∃ c : ℤ, v = fun _ ↦ c := by
  exact M.toBase.mem_ker_verticalLineBundleLinear_iff_of_isReduced _ _ hC _ _ hconn v

end ModelPicard

end TauCeti.Model

end
