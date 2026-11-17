/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
public import TauCeti.RingTheory.Localization.FractionRing

/-!
# A constant field extension as a tensor product

Let `F' = F · k'` be the compositum of a field `F` over `k` with an algebraic extension `k'` of
`k`. Multiplication `F ⊗[k] k' → F'` is onto, because the constants generate `F'` as an
`F`-algebra. When `F ⊗[k] k'` is a domain it is a field, `k'` being algebraic, so multiplication is
an isomorphism `F ⊗[k] k' ≃ F'`. For a function field `F` this is the case when the curve with
function field `F` is geometrically integral over `k`, and it holds for inseparable `k' / k` as
well.

Without an algebraicity assumption on `k' / k`, linear disjointness of `F` and `k'` over `k` still
makes multiplication `F ⊗[k] k' → F'` injective and exhibits the compositum `F' = F · k'` as the
fraction field of `F ⊗[k] k'`.

If moreover `F` is the fraction field of a `k`-algebra `A`, for instance the coordinate ring of an
affine open of such a curve, then in both cases `F'` is the fraction field of `A ⊗[k] k'`, the
coordinate ring of the base change of that affine open: `F ⊗[k] k'` is the localization of
`A ⊗[k] k'` at the nonzero elements of `A`. This identifies the function field of the base change
of a geometrically integral curve with the constant field extension of its function field.

## Main results

* `TauCeti.productMap_surjective_of_constantCompositum_eq_top`: multiplication
  `F ⊗[k] k' → F · k'` is onto for algebraic `k' / k`.
* `TauCeti.productMap_bijective_of_constantCompositum_eq_top`: multiplication
  `F ⊗[k] k' → F · k'` is bijective when `F ⊗[k] k'` is a domain and `k' / k` is algebraic.
* `TauCeti.finrank_eq_finrank_of_constantCompositum_eq_top`: then `[F · k' : F] = [k' : k]`.
* `TauCeti.productMap_injective_of_linearDisjoint` and
  `TauCeti.isFractionRing_field_tensorProduct_of_linearDisjoint`: multiplication
  `F ⊗[k] k' → F · k'` is injective and exhibits `F · k'` as the fraction field of `F ⊗[k] k'`
  for any linearly disjoint extension `k' / k`.
* `TauCeti.isFractionRing_tensorProduct_of_constantCompositum_eq_top` and
  `TauCeti.isFractionRing_tensorProduct_of_linearDisjoint`: `F · k'` is the fraction field of
  `A ⊗[k] k'` for every `A` with fraction field `F`, in both the algebraic domain case and the
  general linearly disjoint case.

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

/-- **The degree of a constant field extension that is a tensor product.** If `k' / k` is
algebraic and `F ⊗[k] k'` is a domain, then `[F · k' : F] = [k' : k]`. -/
theorem finrank_eq_finrank_of_constantCompositum_eq_top [Algebra.IsAlgebraic k k']
    [IsDomain (F ⊗[k] k')] (h : constantCompositum F k' F' = ⊤) :
    Module.finrank F F' = Module.finrank k k' := by
  -- multiplication `F ⊗[k] k' → F'` is `F`-linear for the left `F`-module structure
  let φ := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId F F')
    (IsScalarTower.toAlgHom k k' F')
  have hφ : Function.Bijective φ := by
    convert productMap_bijective_of_constantCompositum_eq_top (k := k) (F' := F') h using 1
    exact congrArg DFunLike.coe (Algebra.TensorProduct.ext' fun _ _ ↦ by simp [φ] :
      φ.restrictScalars k = _)
  rw [← (LinearEquiv.ofBijective φ.toLinearMap hφ).finrank_eq, Module.finrank_baseChange]

/-- **Linear disjointness makes multiplication `F ⊗[k] k' → F'` injective**, with no algebraicity
hypothesis on `k' / k`. -/
theorem productMap_injective_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F) :
    Function.Injective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) := by
  let fF := IsScalarTower.toAlgHom k F F'
  let fk := IsScalarTower.toAlgHom k k' F'
  let e : F ⊗[k] k' ≃ₐ[k] fF.range ⊗[k] fk.range :=
    Algebra.TensorProduct.congr (AlgEquiv.ofInjectiveField fF) (AlgEquiv.ofInjectiveField fk)
  have hdisj : fF.range.LinearDisjoint fk.range := by
    rw [← AlgHom.fieldRange_toSubalgebra]
    exact Subalgebra.LinearDisjoint.symm H
  have hcomp : Algebra.TensorProduct.productMap fF fk =
      (Algebra.TensorProduct.productMap fF.range.val fk.range.val).comp e.toAlgHom :=
    Algebra.TensorProduct.ext' fun _ _ ↦ rfl
  rw [hcomp, AlgHom.coe_comp]
  exact hdisj.injective.comp e.injective

/-- **The linearly disjoint compositum `F · k'` is the fraction field of `F ⊗[k] k'`.** -/
theorem isFractionRing_field_tensorProduct_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) :
    letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F') : F ⊗[k] k' →+* F').toAlgebra
    IsFractionRing (F ⊗[k] k') F' := by
  set π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let _ : Algebra (F ⊗[k] k') F' := (π : F ⊗[k] k' →+* F').toAlgebra
  have hπ : Function.Injective (algebraMap (F ⊗[k] k') F') :=
    productMap_injective_of_linearDisjoint H
  have : FaithfulSMul (F ⊗[k] k') F' := (faithfulSMul_iff_algebraMap_injective _ _).mpr hπ
  have hring : (π : F ⊗[k] k' →+* F').range =
      Subring.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap k' F')) := by
    rw [RingHom.range_eq_map, ← Algebra.TensorProduct.closure_range_union_range_eq_top k F k',
      RingHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp]
    congr 2 <;> ext <;> simp [π]
  refine IsFractionRing.of_field (F ⊗[k] k') F' fun z ↦ ?_
  have hz : z ∈ Subfield.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap k' F')) := by
    have htop := congrArg IntermediateField.toSubfield h
    rw [constantCompositum_def, IntermediateField.adjoin_toSubfield] at htop
    simp [htop]
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hz
  rw [← hring] at ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x, y, rfl⟩

/-- If multiplication `F ⊗[k] k' → F'` makes `F'` the fraction field of `F ⊗[k] k'`, then `F'` is
also the fraction field of `A ⊗[k] k'` for every `k`-algebra `A` with fraction field `F`, through
the map `a ⊗ c ↦ a · c`. -/
private theorem isFractionRing_tensorProduct_of_isFractionRing {A : Type*} [CommRing A]
    [Algebra k A] [Algebra A F] [IsScalarTower k A F] [IsFractionRing A F]
    (hF' : letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
        (IsScalarTower.toAlgHom k k' F') : F ⊗[k] k' →+* F').toAlgebra
      IsFractionRing (F ⊗[k] k') F') :
    letI := (((Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')).comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k k'))) :
        A ⊗[k] k' →+* F').toAlgebra
    IsFractionRing (A ⊗[k] k') F' := by
  set π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  set ρ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k k')
  let _ := ((π.comp ρ : A ⊗[k] k' →ₐ[k] F') : A ⊗[k] k' →+* F').toAlgebra
  let _ : Algebra (F ⊗[k] k') F' := (π : F ⊗[k] k' →+* F').toAlgebra
  have : IsFractionRing (F ⊗[k] k') F' := hF'
  have hπ : Function.Injective π := IsFractionRing.injective (F ⊗[k] k') F'
  -- `A ⊗[k] k' → F ⊗[k] k'` is injective, since `k'` is flat over the field `k`
  have hρ : Function.Injective ρ :=
    Module.Flat.rTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom k A F).toLinearMap
      (IsFractionRing.injective A F)
  have hψ : Function.Injective (algebraMap (A ⊗[k] k') F') := hπ.comp hρ
  -- `F ⊗[k] k'` is the localization of `A ⊗[k] k'` at the nonzero elements of `A`
  let _ : Algebra (A ⊗[k] k') (F ⊗[k] k') := (ρ : A ⊗[k] k' →+* F ⊗[k] k').toAlgebra
  have : IsScalarTower A (A ⊗[k] k') (F ⊗[k] k') := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, ρ]
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] k') (nonZeroDivisors A))
      (F ⊗[k] k') :=
    IsLocalization.tensorProduct_tensorProduct k k' (nonZeroDivisors A) F
      (by ext; simp [RingHom.algebraMap_toAlgebra, ρ])
  have : IsScalarTower (A ⊗[k] k') (F ⊗[k] k') F' := .of_algebraMap_eq fun _ ↦ rfl
  have : NoZeroDivisors (A ⊗[k] k') := hψ.noZeroDivisors _ (map_zero _) (map_mul _)
  exact IsFractionRing.of_isLocalization_of_isFractionRing
    (Algebra.algebraMapSubmonoid (A ⊗[k] k') (nonZeroDivisors A)) (F ⊗[k] k') F'
    (IsLocalization.le_nonZeroDivisors_of_nontrivial _ (F ⊗[k] k'))

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
  refine isFractionRing_tensorProduct_of_isFractionRing (k := k) (F := F) ?_
  -- `F'` is the fraction field of the field `F ⊗[k] k'`, through the bijection `π`
  let _ : Field (F ⊗[k] k') :=
    (Algebra.TensorProduct.isField_of_isAlgebraic k F k' (.inr inferInstance)).toField
  let _ : Algebra (F ⊗[k] k') F' := (Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom k F F') (IsScalarTower.toAlgHom k k' F') : F ⊗[k] k' →+* F').toAlgebra
  exact .of_algEquiv (AlgEquiv.ofBijective (Algebra.ofId (F ⊗[k] k') F')
    (productMap_bijective_of_constantCompositum_eq_top (k := k) (F' := F') h))

/-- **The linearly disjoint compositum `F · k'` is the fraction field of `A ⊗[k] k'`** for every
`k`-algebra `A` with fraction field `F`, with no algebraicity assumption on `k' / k`. -/
theorem isFractionRing_tensorProduct_of_linearDisjoint {A : Type*} [CommRing A]
    [Algebra k A] [Algebra A F] [IsScalarTower k A F] [IsFractionRing A F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) :
    letI := (((Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')).comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k k'))) :
        A ⊗[k] k' →+* F').toAlgebra
    IsFractionRing (A ⊗[k] k') F' :=
  isFractionRing_tensorProduct_of_isFractionRing
    (isFractionRing_field_tensorProduct_of_linearDisjoint H h)

end TauCeti
