/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis

/-!
# A constant field extension as a tensor product

Let `F' = F · k'` be the compositum of a field `F` over `k` with an algebraic extension `k'` of
`k`. Multiplication `F ⊗[k] k' → F'` is onto, because the constants generate `F'` as an
`F`-algebra. When `F ⊗[k] k'` is a domain it is a field, `k'` being algebraic, so multiplication is
an isomorphism `F ⊗[k] k' ≃ F'`. For a function field `F` this is the case when the curve with
function field `F` is geometrically integral over `k`, and it holds for inseparable `k' / k` as
well.

If moreover `F` is the fraction field of a `k`-algebra `A`, for instance the coordinate ring of an
affine open of such a curve, then `F'` is the fraction field of `A ⊗[k] k'`, the coordinate ring
of the base change of that affine open: `F ⊗[k] k'` is the localization of `A ⊗[k] k'` at the
nonzero elements of `A`. This identifies the function field of the base change of a geometrically
integral curve with the constant field extension of its function field.

## Main results

* `TauCeti.productMap_surjective_of_constantCompositum_eq_top`: multiplication
  `F ⊗[k] k' → F · k'` is onto for algebraic `k' / k`.
* `TauCeti.productMap_bijective_of_constantCompositum_eq_top`: multiplication
  `F ⊗[k] k' → F · k'` is bijective when `F ⊗[k] k'` is a domain and `k' / k` is algebraic.
* `TauCeti.isFractionRing_tensorProduct_of_constantCompositum_eq_top`: then `F · k'` is the
  fraction field of `A ⊗[k] k'` for every `A` with fraction field `F`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Multiplication `F ⊗[k] k' → F · k'` is onto for an algebraic extension `k' / k`: the
constants generate the compositum as an `F`-algebra. -/
theorem productMap_surjective_of_constantCompositum_eq_top [Algebra.IsIntegral k k']
    (h : constantCompositum F k' F' = ⊤) :
    Function.Surjective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) := by
  rw [← AlgHom.range_eq_top, Algebra.TensorProduct.productMap_range,
    ← Algebra.adjoin_eq (IsScalarTower.toAlgHom k k' F').range, AlgHom.coe_range,
    IsScalarTower.coe_toAlgHom', ← Algebra.Subalgebra.restrictScalars_adjoin,
    adjoin_range_algebraMap_of_constantCompositum_eq_top (k := k) h, Subalgebra.restrictScalars_top]

/-- **A constant field extension is a tensor product.** If `k' / k` is algebraic and
`F ⊗[k] k'` is a domain, then multiplication `F ⊗[k] k' → F · k'` is bijective. -/
theorem productMap_bijective_of_constantCompositum_eq_top [Algebra.IsAlgebraic k k']
    [IsDomain (F ⊗[k] k')] (h : constantCompositum F k' F' = ⊤) :
    Function.Bijective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) := by
  -- `F ⊗[k] k'` is a field, since `k'` is algebraic over `k`
  let _ : Field (F ⊗[k] k') :=
    (Algebra.TensorProduct.isField_of_isAlgebraic k F k' (.inr inferInstance)).toField
  have : Algebra.IsIntegral k k' := Algebra.IsAlgebraic.isIntegral
  exact ⟨RingHom.injective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F') : F ⊗[k] k' →+* F'),
    productMap_surjective_of_constantCompositum_eq_top h⟩

/-- **The constant field extension is the fraction field of the base change.** Let `F` be the
fraction field of a `k`-algebra `A`, let `k' / k` be algebraic with `F ⊗[k] k'` a domain, and let
`F' = F · k'`. Then `F'` is the fraction field of `A ⊗[k] k'`, through the map
`a ⊗ c ↦ a · c`. -/
theorem isFractionRing_tensorProduct_of_constantCompositum_eq_top {A : Type*} [CommRing A]
    [Algebra k A] [Algebra A F] [IsScalarTower k A F] [IsFractionRing A F]
    [Algebra.IsAlgebraic k k'] [IsDomain (F ⊗[k] k')] (h : constantCompositum F k' F' = ⊤) :
    letI := (((Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')).comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k k'))) :
        A ⊗[k] k' →+* F').toAlgebra
    IsFractionRing (A ⊗[k] k') F' := by
  set π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  set ρ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k k')
  let _ := ((π.comp ρ : A ⊗[k] k' →ₐ[k] F') : A ⊗[k] k' →+* F').toAlgebra
  have hπ := productMap_bijective_of_constantCompositum_eq_top (k := k) (F' := F') h
  -- `A ⊗[k] k' → F ⊗[k] k'` is injective, since `k'` is flat over the field `k`
  have hρ : Function.Injective ρ :=
    Module.Flat.rTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom k A F).toLinearMap
      (IsFractionRing.injective A F)
  have hψ : Function.Injective (algebraMap (A ⊗[k] k') F') := hπ.injective.comp hρ
  have : FaithfulSMul (A ⊗[k] k') F' := (faithfulSMul_iff_algebraMap_injective _ _).mpr hψ
  -- `F ⊗[k] k'` is the localization of `A ⊗[k] k'` at the nonzero elements of `A`
  let _ : Algebra (A ⊗[k] k') (F ⊗[k] k') := (ρ : A ⊗[k] k' →+* F ⊗[k] k').toAlgebra
  have : IsScalarTower A (A ⊗[k] k') (F ⊗[k] k') := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, ρ]
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] k') (nonZeroDivisors A))
      (F ⊗[k] k') :=
    IsLocalization.tensorProduct_tensorProduct k k' (nonZeroDivisors A) F
      (by ext; simp [RingHom.algebraMap_toAlgebra, ρ])
  refine .of_field _ _ fun z ↦ ?_
  obtain ⟨t, rfl⟩ := hπ.surjective z
  obtain ⟨⟨r, s, hs⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (A ⊗[k] k') (nonZeroDivisors A)) t
  refine ⟨r, s, ?_⟩
  have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A F).mpr inferInstance
  have hs0 : algebraMap (A ⊗[k] k') F' s ≠ 0 := by
    obtain ⟨a, ha, rfl⟩ := hs
    refine (map_ne_zero_iff _ hψ).mpr ((map_ne_zero_iff _ ?_).mpr (nonZeroDivisors.ne_zero ha))
    exact Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k k').injective
  rw [eq_div_iff hs0]
  have := congrArg π (IsLocalization.mk'_spec (F ⊗[k] k') r ⟨s, hs⟩)
  simpa only [map_mul, RingHom.algebraMap_toAlgebra, AlgHom.coe_toRingHom, AlgHom.comp_apply,
    RingHom.coe_coe] using this

end TauCeti
