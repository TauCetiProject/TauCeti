/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.FieldTheory.AlgebraicClosure
public import TauCeti.FieldTheory.FunctionField.ConstantField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
public import TauCeti.RingTheory.TensorProduct.IsDomain

/-!
# The function field of a geometrically integral scheme

Let `X` be an integral scheme over a field `k` that is geometrically integral over `k`. Then for
every field extension `L / k` the ring `k(X) ⊗[k] L` is a domain, and consequently `k` is
algebraically closed in the function field `k(X)`, that is, `k` is the full field of constants of
`k(X)`.

For the first statement, choose a nonempty affine open `U` of `X`. The base change
`Spec (Γ(X, U) ⊗[k] L)` of `U` to `L` is a nonempty open subscheme of the integral scheme
`X ×_k Spec L`, so `Γ(X, U) ⊗[k] L` is a domain, and `k(X) ⊗[k] L` is a localization of it because
`k(X)` is the fraction field of `Γ(X, U)`. The second statement follows by taking for `L` an
algebraic closure of `k` (`TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`).

The same chart describes the function field of the base change `Y = X ×_k Spec K` to an algebraic
extension `K / k`. The function field of `Y` is the fraction field of `Γ(X, U) ⊗[k] K`, and so is
the constant field extension `k(X) · K`, because `k(X) ⊗[k] K` is a field
(`TauCeti.isFractionRing_tensorProduct_of_constantCompositum_eq_top`). Hence `K(Y) ≃ k(X) · K`
as `K`-algebras, also when `K / k` is inseparable. In particular `K` is the exact constant field
of `k(X) · K`, the base change being geometrically integral over `K`. This is how invariants of
the function field of a geometrically integral curve, such as its genus, are compared with those
of its base change.

The constant-field hypothesis `IsIntegrallyClosedIn k X.functionField` is how the function-field
theory of curves (Weil differentials, the genus of the function field, Serre duality for divisor
sheaves) is applied to a curve. This file derives it from geometric integrality, which in turn
holds for smooth geometrically connected schemes over `k`
(`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`).

The proof is built on Andrew Yang's formalization of geometrically integral morphisms in Mathlib
(`AlgebraicGeometry.GeometricallyIntegral`, in `Mathlib/AlgebraicGeometry/Geometrically/Integral`),
which supplies the integrality of the base change `X ×_k Spec L`.

## Main results

* `TauCeti.AlgebraicGeometry.isDomain_functionField_tensorProduct_of_geometricallyIntegral`:
  `k(X) ⊗[k] L` is a domain for every field extension `L / k`;
* `TauCeti.AlgebraicGeometry.isIntegrallyClosedIn_functionField_of_geometricallyIntegral`:
  `k` is algebraically closed in `k(X)`;
* `TauCeti.AlgebraicGeometry.nonempty_functionField_algEquiv_of_isPullback`: the function field of
  the base change of `X` to an algebraic extension `K / k` is the compositum `k(X) · K`;
* `TauCeti.AlgebraicGeometry.isIntegrallyClosedIn_of_constantCompositum_eq_top`: `K` is
  algebraically closed in `k(X) · K`.
* `TauCeti.AlgebraicGeometry.baseChangeFunctionFieldAlgebra`,
  `TauCeti.AlgebraicGeometry.isScalarTower_functionField_of_isPullback`: the `k`-algebra
  structure on `K(Y)` induced through `K` and its scalar-tower compatibilities with `K` and
  `k(X)`.
* `TauCeti.AlgebraicGeometry.functionFieldTensorToBaseChange`,
  `TauCeti.AlgebraicGeometry.isFractionRing_functionField_tensorProduct_of_isPullback`,
  `TauCeti.AlgebraicGeometry.constantCompositum_functionField_eq_top_of_isPullback`,
  `TauCeti.AlgebraicGeometry.linearDisjoint_functionField_of_isPullback`: `K(Y)` as the fraction
  field of `k(X) ⊗[k] K`, constant compositum, and linear disjointness over arbitrary `K / k`.
* `TauCeti.AlgebraicGeometry.finrank_functionField_eq_of_isPullback`,
  `TauCeti.AlgebraicGeometry.isSeparable_functionField_iff_of_isPullback`: invariance of generic
  degree and separability of dominant morphisms under arbitrary field extensions.

The chart arguments use `TauCeti.AlgebraicGeometry.exists_affineOpen_isFractionRing` and
`AlgebraicGeometry.Scheme.Hom.functionFieldAlgEquivOfIsOpenImmersion` (the function
field of an integral scheme is the fraction field of any affine chart), from
`TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`, and
`TauCeti.AlgebraicGeometry.exists_isOpenImmersion_spec_tensorProduct_of_isPullback` (affine
tensor-product charts on a pullback square), from `TauCeti/AlgebraicGeometry/Pullback/SpecMap.lean`.
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti

namespace AlgebraicGeometry

universe u

section

/-- Base change an affine chart `U` of `X` along `k → L` into an open chart `Spec (Γ(X, U) ⊗[k] L)`
of `Y`. -/
private lemma exists_isOpenImmersion_tensorProduct_chart
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    {X Y : Scheme.{u}} {pX : X ⟶ Spec (.of k)} {pY : Y ⟶ Spec (.of L)} {g : Y ⟶ X}
    (H : IsPullback g pY pX (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {U : X.Opens} (hU : IsAffineOpen U) [Algebra k Γ(X, U)]
    (hw : hU.fromSpec ≫ pX = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) :
    ∃ ι : Spec (.of (Γ(X, U) ⊗[k] L)) ⟶ Y, IsOpenImmersion ι ∧
      ι ≫ g = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ hU.fromSpec ∧
      ι ≫ pY = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : L →ₐ[k] Γ(X, U) ⊗[k] L).toRingHom) := by
  have := hU.isOpenImmersion_fromSpec
  obtain ⟨ι, hι, h₁, h₂, -⟩ := exists_isOpenImmersion_spec_tensorProduct_of_isPullback H.flip
    (iY := 𝟙 (Spec (.of k))) (iY' := hU.fromSpec) (iX := 𝟙 (Spec (.of L)))
    ((Category.comp_id _).trans hw.symm) ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact ⟨ι, hι, h₁, h₂.trans (Category.comp_id _)⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- The function field of a geometrically integral scheme over `k` stays a domain after extending
scalars to any field extension `L` of `k`. -/
instance isDomain_functionField_tensorProduct_of_geometricallyIntegral (L : Type u) [Field L]
    [Algebra k L] : IsDomain (X.functionField ⊗[k] L) := by
  obtain ⟨U, hU, _, _, _, _, hw⟩ := exists_affineOpen_isFractionRing (k := k) (X := X)
  -- `Spec (Γ(X, U) ⊗[k] L)` is the base change of `U` to `L`, an open subscheme of the integral
  -- scheme `X ×_k Spec L`.
  let s := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : IsIntegral (pullback (X ↘ Spec (.of k)) s) :=
    pullback_of_geometrically GeometricallyIntegral.geometrically_isIntegral L s
  have : Nontrivial (Γ(X, U) ⊗[k] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k _ _
      (algebraMap k Γ(X, U)).injective (algebraMap k L).injective
  obtain ⟨ι, _, -, -⟩ := exists_isOpenImmersion_tensorProduct_chart
    (IsPullback.of_hasPullback (X ↘ Spec (.of k)) s) hU hw
  have : IsIntegral (Spec (.of (Γ(X, U) ⊗[k] L))) := isIntegral_of_isOpenImmersion ι
  have : IsDomain (Γ(X, U) ⊗[k] L) := (affine_isIntegral_iff _).mp this
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors Γ(X, U)) le_rfl
    X.functionField L

/-- **The constant field of a geometrically integral scheme.** If `X` is integral and
geometrically integral over `k`, then `k` is algebraically closed in the function field `k(X)`. -/
theorem isIntegrallyClosedIn_functionField_of_geometricallyIntegral :
    IsIntegrallyClosedIn k X.functionField :=
  algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mp
    (algebraicClosure_eq_bot_of_isDomain_tensorProduct (AlgebraicClosure k))

/-- **The function field of the base change is the constant field extension.** Let `X` be a
geometrically integral scheme over `k` and `Y = X ×_k Spec K` its base change to an algebraic
extension `K / k`. Then the function field of `Y` is, as a `K`-algebra, the compositum
`F' = k(X) · K`, for inseparable `K / k` as well. -/
theorem nonempty_functionField_algEquiv_of_isPullback {K : Type u} [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] {Y : Scheme.{u}} [Y.Over (Spec (.of K))] {g : Y ⟶ X}
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {F' : Type*} [Field F'] [Algebra K F'] [Algebra X.functionField F'] [Algebra k F']
    [IsScalarTower k K F'] [IsScalarTower k X.functionField F']
    (h : constantCompositum X.functionField K F' = ⊤) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    Nonempty (Y.functionField ≃ₐ[K] F') := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  obtain ⟨U, hU, _, _, _, _, hw⟩ := exists_affineOpen_isFractionRing (k := k) (X := X)
  -- the base change `Spec (Γ(X, U) ⊗[k] K)` of `U` is an open subscheme of `Y` over `Spec K`
  obtain ⟨ι, _, -, hι⟩ := exists_isOpenImmersion_tensorProduct_chart H hU hw
  let _ : Algebra K (Γ(X, U) ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  -- and `F' = k(X) · K` is a fraction field of `Γ(X, U) ⊗[k] K`
  let _ : Algebra (Γ(X, U) ⊗[k] K) F' := (((Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom k X.functionField F') (IsScalarTower.toAlgHom k K F')).comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k Γ(X, U) X.functionField)
      (AlgHom.id k K))) : Γ(X, U) ⊗[k] K →+* F').toAlgebra
  have : IsFractionRing (Γ(X, U) ⊗[k] K) F' :=
    isFractionRing_tensorProduct_of_constantCompositum_eq_top h
  have : IsScalarTower K (Γ(X, U) ⊗[k] K) F' := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  exact ⟨ι.functionFieldAlgEquivOfIsOpenImmersion hι F'⟩

/-- **The constants of a constant field extension.** Let `X` be a geometrically integral scheme
over `k` and `F' = k(X) · K` for an algebraic extension `K / k`, separable or not. Then `K` is
algebraically closed in `F'`: it is the exact constant field of `F'`. -/
theorem isIntegrallyClosedIn_of_constantCompositum_eq_top {K : Type u} [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] {F' : Type*} [Field F'] [Algebra K F']
    [Algebra X.functionField F'] [Algebra k F'] [IsScalarTower k K F']
    [IsScalarTower k X.functionField F'] (h : constantCompositum X.functionField K F' = ⊤) :
    IsIntegrallyClosedIn K F' := by
  -- `F'` is the function field of the base change `X ×_k Spec K`, geometrically integral over `K`
  let s := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let _ : (pullback (X ↘ Spec (.of k)) s).Over (Spec (.of K)) := ⟨pullback.snd _ _⟩
  have H : IsPullback (pullback.fst _ _) (pullback (X ↘ Spec (.of k)) s ↘ Spec (.of K))
      (X ↘ Spec (.of k)) s :=
    IsPullback.of_hasPullback _ _
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have : GeometricallyIntegral (pullback (X ↘ Spec (.of k)) s ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H inferInstance
  obtain ⟨e⟩ := nonempty_functionField_algEquiv_of_isPullback H h
  exact isIntegrallyClosedIn_functionField_of_geometricallyIntegral.of_ringEquiv
    (RingEquiv.refl K) e.toRingEquiv e.commutes

/-- Scalar-restriction `k`-algebra structure on `Y.functionField` along `k → K → K(Y)`. -/
noncomputable abbrev baseChangeFunctionFieldAlgebra (k K : Type u) [CommRing k]
    [CommRing K] [Algebra k K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))] [IsIntegral Y] :
    Algebra k Y.functionField :=
  ((algebraMap K Y.functionField).comp (algebraMap k K)).toAlgebra

/-- Under `baseChangeFunctionFieldAlgebra`, the scalar map `k → K(Y)` factors through `K`. -/
theorem algebraMap_baseChangeFunctionFieldAlgebra (k K : Type u) [CommRing k]
    [CommRing K] [Algebra k K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))] [IsIntegral Y]
    (c : k) :
    letI := baseChangeFunctionFieldAlgebra k K Y
    algebraMap k Y.functionField c = algebraMap K Y.functionField (algebraMap k K c) :=
  rfl

section ArbitraryExtension

variable {K : Type u} [Field K] [Algebra k K] {Y : Scheme.{u}} [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include H

/-- Pullback of rational functions along `g : Y ⟶ X` agrees on `k` with `k → K → K(Y)`. -/
theorem functionFieldMap_baseChange_algebraMap (c : k) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    haveI := isDominant_of_isPullback_spec H
    g.functionFieldMap (algebraMap k X.functionField c) =
      algebraMap K Y.functionField (algebraMap k K c) := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have := isDominant_of_isPullback_spec H
  have h : Spec.map (CommRingCat.ofHom (algebraMap k X.functionField) ≫ g.functionFieldMap) =
      Spec.map (CommRingCat.ofHom ((algebraMap K Y.functionField).comp (algebraMap k K))) := by
    rw [Spec.map_comp, ← Scheme.fromSpecStalk_genericPoint_comp_over,
      g.SpecMap_functionFieldMap_fromSpecStalk_assoc, H.w,
      reassoc_of% Scheme.fromSpecStalk_genericPoint_comp_over, ← Spec.map_comp,
      CommRingCat.ofHom_comp]
  exact congr($(Spec.map_injective h) c)

/-- For a base change `Y` of `X` along `K / k`, `baseChangeFunctionFieldAlgebra k K Y` forms scalar
towers with both `K` and `X.functionField`. -/
theorem isScalarTower_functionField_of_isPullback :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
    letI : Algebra k Y.functionField := baseChangeFunctionFieldAlgebra k K Y
    IsScalarTower k K Y.functionField ∧ IsScalarTower k X.functionField Y.functionField :=
  haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  haveI := isDominant_of_isPullback_spec H
  letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
  letI : Algebra k Y.functionField := baseChangeFunctionFieldAlgebra k K Y
  ⟨.of_algebraMap_eq fun _ ↦ rfl,
    .of_algebraMap_eq fun c ↦ (functionFieldMap_baseChange_algebraMap H c).symm⟩

/-- The canonical `K`-algebra map `k(X) ⊗[k] K →ₐ[K] K(Y)` for `Y = X ×_k Spec K`. -/
noncomputable def functionFieldTensorToBaseChange :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    (X.functionField ⊗[k] K) →ₐ[K] Y.functionField :=
  haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  haveI := isDominant_of_isPullback_spec H
  letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
  letI : Algebra k Y.functionField := baseChangeFunctionFieldAlgebra k K Y
  haveI := (isScalarTower_functionField_of_isPullback H).1
  haveI := (isScalarTower_functionField_of_isPullback H).2
  let φX : X.functionField →ₐ[k] Y.functionField :=
    IsScalarTower.toAlgHom k X.functionField Y.functionField
  (Algebra.TensorProduct.liftEquivRight k K X.functionField Y.functionField φX).comp
    (Algebra.TensorProduct.commRight k K X.functionField).symm.toAlgHom

/-- On pure tensors, `functionFieldTensorToBaseChange` sends `a ⊗ₜ c` to `g^* a * c`. -/
@[simp]
theorem functionFieldTensorToBaseChange_tmul (a : X.functionField) (c : K) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    functionFieldTensorToBaseChange H (a ⊗ₜ[k] c) =
      g.functionFieldMap a * algebraMap K Y.functionField c := by
  rw [mul_comm]
  simp [functionFieldTensorToBaseChange, RingHom.algebraMap_toAlgebra]

/-- Embed `Γ(X, U) ⊗[k] K` into `K(Y)` as a fraction-field map compatible with `g` and `K`. -/
private lemma exists_chart_to_baseChange_functionField {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] [Algebra k Γ(X, U)]
    (hw : hU.fromSpec ≫ (X ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    haveI := isDominant_of_isPullback_spec H
    ∃ (_ : IsDomain (Γ(X, U) ⊗[k] K)) (α : (Γ(X, U) ⊗[k] K) →+* Y.functionField),
      (letI := α.toAlgebra; IsFractionRing (Γ(X, U) ⊗[k] K) Y.functionField) ∧
      (∀ a : Γ(X, U), α (a ⊗ₜ[k] 1) = g.functionFieldMap (algebraMap Γ(X, U) X.functionField a)) ∧
      (∀ c : K, α (1 ⊗ₜ[k] c) = algebraMap K Y.functionField c) := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have := isDominant_of_isPullback_spec H
  let A := Γ(X, U)
  -- Base change the affine chart `U` to an affine open chart `ι : Spec (A ⊗[k] K) ⟶ Y`.
  obtain ⟨ι, _, hιg, hιK⟩ := exists_isOpenImmersion_tensorProduct_chart H hU hw
  have : IsIntegral (Spec (.of (A ⊗[k] K))) := isIntegral_of_isOpenImmersion ι
  have hDomR : IsDomain (A ⊗[k] K) := (affine_isIntegral_iff (.of (A ⊗[k] K))).mp this
  -- Transport `IsFractionRing` from `Spec (A ⊗[k] K)` to `Y.functionField`.
  obtain ⟨α, hFrac, hSpecα⟩ := ι.exists_isFractionRing_functionField_of_isOpenImmersion
  refine ⟨hDomR, α, hFrac, fun a ↦ ?_, fun c ↦ ?_⟩
  · -- Compatibility with `g.functionFieldMap` on the left factor `A`.
    have h1 : Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
        CommRingCat.ofHom α) ≫ hU.fromSpec =
        Spec.map (X.germToFunctionField U ≫ g.functionFieldMap) ≫ hU.fromSpec := by
      rw [Spec.map_comp_assoc, ← hιg, ← Category.assoc, hSpecα,
        ← g.SpecMap_functionFieldMap_fromSpecStalk, Spec.map_comp_assoc,
        hU.specMap_germToFunctionField_fromSpec]
    exact congr($(Spec.map_injective ((cancel_mono hU.fromSpec).mp h1)) a)
  · -- Compatibility with `algebraMap K Y.functionField` on the right factor `K`.
    have h2 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : K →ₐ[k] A ⊗[k] K).toRingHom ≫
        CommRingCat.ofHom α) = Spec.map (CommRingCat.ofHom (algebraMap K Y.functionField)) := by
      rw [Spec.map_comp, ← hιK, ← Category.assoc, hSpecα,
        Scheme.fromSpecStalk_genericPoint_comp_over]
    exact congr($(Spec.map_injective h2) c)

/-- **The function field of any field-extension base change:** `K(Y)` is the fraction field of
`k(X) ⊗[k] K` via `functionFieldTensorToBaseChange H` for arbitrary `K / k`. -/
theorem isFractionRing_functionField_tensorProduct_of_isPullback :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra (X.functionField ⊗[k] K) Y.functionField :=
      (functionFieldTensorToBaseChange H).toRingHom.toAlgebra
    IsFractionRing (X.functionField ⊗[k] K) Y.functionField := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have := isDominant_of_isPullback_spec H
  obtain ⟨U, hU, _, _, _, _, hw⟩ := exists_affineOpen_isFractionRing (k := k) (X := X)
  let A := Γ(X, U)
  obtain ⟨_, α, hFracA, hα_left, hα_right⟩ := exists_chart_to_baseChange_functionField H hU hw
  let _ : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra (X.functionField ⊗[k] K) Y.functionField :=
    (functionFieldTensorToBaseChange H).toRingHom.toAlgebra
  let _ : Algebra (A ⊗[k] K) Y.functionField := α.toAlgebra
  have : IsFractionRing (A ⊗[k] K) Y.functionField := hFracA
  exact isFractionRing_tensorProduct_of_isFractionRing_base_tensorProduct fun a c ↦ by
    have hmul : (a ⊗ₜ[k] c : A ⊗[k] K) = (a ⊗ₜ[k] 1) * (1 ⊗ₜ[k] c) := by simp
    calc
      (algebraMap (A ⊗[k] K) Y.functionField) (a ⊗ₜ[k] c)
        = α ((a ⊗ₜ[k] 1) * (1 ⊗ₜ[k] c)) := by rw [RingHom.algebraMap_toAlgebra, hmul]
      _ = g.functionFieldMap (algebraMap A X.functionField a) * algebraMap K Y.functionField c := by
        rw [map_mul, hα_left, hα_right]
      _ = (algebraMap (X.functionField ⊗[k] K) Y.functionField)
          (algebraMap A X.functionField a ⊗ₜ[k] c) :=
        (functionFieldTensorToBaseChange_tmul H (algebraMap A X.functionField a) c).symm

/-- Shared tower setup for `constantCompositum_functionField_eq_top_of_isPullback` and
`linearDisjoint_functionField_of_isPullback`. -/
private theorem constantCompositum_and_linearDisjoint_functionField_of_isPullback :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
    letI : Algebra k Y.functionField := baseChangeFunctionFieldAlgebra k K Y
    haveI := (isScalarTower_functionField_of_isPullback H).1
    haveI := (isScalarTower_functionField_of_isPullback H).2
    constantCompositum X.functionField K Y.functionField = ⊤ ∧
      (IsScalarTower.toAlgHom k K Y.functionField).fieldRange.LinearDisjoint X.functionField := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have := isDominant_of_isPullback_spec H
  let _ : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
  let _ : Algebra k Y.functionField := baseChangeFunctionFieldAlgebra k K Y
  let _ : Algebra (X.functionField ⊗[k] K) Y.functionField :=
    (functionFieldTensorToBaseChange H).toRingHom.toAlgebra
  obtain ⟨_, _⟩ := isScalarTower_functionField_of_isPullback H
  have : IsScalarTower X.functionField (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower K (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower k (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k X.functionField (X.functionField ⊗[k] K),
        ← IsScalarTower.algebraMap_apply X.functionField (X.functionField ⊗[k] K) Y.functionField,
        ← IsScalarTower.algebraMap_apply k X.functionField Y.functionField]
  have : IsFractionRing (X.functionField ⊗[k] K) Y.functionField :=
    isFractionRing_functionField_tensorProduct_of_isPullback H
  refine ⟨?_, linearDisjoint_of_isFractionRing_tensorProduct
      (k := k) (F := X.functionField) (K := K) (Q := Y.functionField)⟩
  rw [constantCompositum_def]
  exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)

/-- For any field extension `K / k`, `K(Y)` is generated as a field by `k(X)` and `K`. -/
theorem constantCompositum_functionField_eq_top_of_isPullback :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
    constantCompositum X.functionField K Y.functionField = ⊤ :=
  (constantCompositum_and_linearDisjoint_functionField_of_isPullback H).1

/-- For any field extension `K / k`, `K` and `k(X)` are linearly disjoint over `k` in `K(Y)`. -/
theorem linearDisjoint_functionField_of_isPullback :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
    letI : Algebra k Y.functionField := baseChangeFunctionFieldAlgebra k K Y
    haveI := (isScalarTower_functionField_of_isPullback H).1
    haveI := (isScalarTower_functionField_of_isPullback H).2
    (IsScalarTower.toAlgHom k K Y.functionField).fieldRange.LinearDisjoint X.functionField :=
  (constantCompositum_and_linearDisjoint_functionField_of_isPullback H).2

end ArbitraryExtension

end

section DominantBaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X₁ X₂ X₁' X₂' : Scheme.{u}} [X₁.Over (Spec (.of k))] [X₂.Over (Spec (.of k))]
  [X₁'.Over (Spec (.of K))] [X₂'.Over (Spec (.of K))]
  [IsIntegral X₁] [IsIntegral X₂]
  [GeometricallyIntegral (X₁ ↘ Spec (.of k))] [GeometricallyIntegral (X₂ ↘ Spec (.of k))]
  {f : X₁ ⟶ X₂} [f.IsOver (Spec (.of k))] [IsDominant f]
  {g₁ : X₁' ⟶ X₁} {g₂ : X₂' ⟶ X₂} {f' : X₁' ⟶ X₂'} [f'.IsOver (Spec (.of K))]
  (H₁ : IsPullback g₁ (X₁' ↘ Spec (.of K)) (X₁ ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  (H₂ : IsPullback g₂ (X₂' ↘ Spec (.of K)) (X₂ ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  (hf' : f' ≫ g₂ = g₁ ≫ f)

include H₁ H₂ hf'

/-- Pullback of rational functions commutes with base change along any field extension `K / k`. -/
theorem functionFieldMap_comp_of_baseChange :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₁
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₂
    haveI := isDominant_of_isPullback_spec H₁
    haveI := isDominant_of_isPullback_spec H₂
    haveI := isDominant_of_baseChange H₁ H₂ hf'
    f.functionFieldMap ≫ g₁.functionFieldMap = g₂.functionFieldMap ≫ f'.functionFieldMap := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₁
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₂
  have := isDominant_of_isPullback_spec H₁
  have := isDominant_of_isPullback_spec H₂
  have := isDominant_of_baseChange H₁ H₂ hf'
  have : IsDominant (f' ≫ g₂) := inferInstance
  have : IsDominant (g₁ ≫ f) := inferInstance
  have hcomp : (g₁ ≫ f).functionFieldMap = (f' ≫ g₂).functionFieldMap := by
    have key : ∀ {a b : X₁' ⟶ X₂} [IsDominant a] [IsDominant b], a = b →
        a.functionFieldMap = b.functionFieldMap := by
      rintro a b _ _ rfl; rfl
    exact key hf'.symm
  rwa [Scheme.Hom.functionFieldMap_comp, Scheme.Hom.functionFieldMap_comp] at hcomp

/-- Shared tower setup for generic degree and generic separability invariance. -/
private theorem finrank_and_isSeparable_functionField_of_isPullback :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₁
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₂
    haveI := isDominant_of_baseChange H₁ H₂ hf'
    ((letI := f'.functionFieldMap.hom.toAlgebra;
        Module.finrank X₂'.functionField X₁'.functionField) =
      (letI := f.functionFieldMap.hom.toAlgebra;
        Module.finrank X₂.functionField X₁.functionField)) ∧
    ((letI := f.functionFieldMap.hom.toAlgebra;
        Algebra.IsAlgebraic X₂.functionField X₁.functionField) →
      ((letI := f'.functionFieldMap.hom.toAlgebra;
          Algebra.IsSeparable X₂'.functionField X₁'.functionField) ↔
        (letI := f.functionFieldMap.hom.toAlgebra;
          Algebra.IsSeparable X₂.functionField X₁.functionField))) := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₁
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₂
  have := isDominant_of_isPullback_spec H₁
  have := isDominant_of_isPullback_spec H₂
  have := isDominant_of_baseChange H₁ H₂ hf'
  let _ : Algebra X₂.functionField X₁.functionField := f.functionFieldMap.hom.toAlgebra
  let _ : Algebra X₂'.functionField X₁'.functionField := f'.functionFieldMap.hom.toAlgebra
  let _ : Algebra X₁.functionField X₁'.functionField := g₁.functionFieldMap.hom.toAlgebra
  let _ : Algebra X₂.functionField X₂'.functionField := g₂.functionFieldMap.hom.toAlgebra
  let _ : Algebra k X₁'.functionField := baseChangeFunctionFieldAlgebra k K X₁'
  let _ : Algebra X₂.functionField X₁'.functionField :=
    (g₁.functionFieldMap.hom.comp f.functionFieldMap.hom).toAlgebra
  have : IsScalarTower k X₂.functionField X₁.functionField :=
    .of_algebraMap_eq fun c ↦ (f.functionFieldMap_algebraMap k c).symm
  have : IsScalarTower K X₂'.functionField X₁'.functionField :=
    .of_algebraMap_eq fun c ↦ (f'.functionFieldMap_algebraMap K c).symm
  obtain ⟨_, _⟩ := isScalarTower_functionField_of_isPullback H₁
  have : IsScalarTower X₂.functionField X₁.functionField X₁'.functionField :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower X₂.functionField X₂'.functionField X₁'.functionField :=
    .of_algebraMap_eq fun a ↦ congr($(functionFieldMap_comp_of_baseChange H₁ H₂ hf') a)
  exact ⟨finrank_eq_of_constantCompositum_eq_top_of_linearDisjoint
      (linearDisjoint_functionField_of_isPullback H₁)
      (constantCompositum_functionField_eq_top_of_isPullback H₂)
      (constantCompositum_functionField_eq_top_of_isPullback H₁),
    fun hAlg ↦
      have : Algebra.IsAlgebraic X₂.functionField X₁.functionField := hAlg
      isSeparable_iff_of_constantCompositum_eq_top_of_linearDisjoint
        (linearDisjoint_functionField_of_isPullback H₁)
        (constantCompositum_functionField_eq_top_of_isPullback H₂)
        (constantCompositum_functionField_eq_top_of_isPullback H₁)⟩

/-- **Generic degree is invariant under arbitrary field extensions.** Let `f : X₁ ⟶ X₂` be a
dominant `k`-morphism between geometrically integral `k`-schemes, and let `f' : X₁' ⟶ X₂'` be its
base change along an arbitrary field extension `K / k` (algebraic or transcendental, separable or
not). Then `[K(X₁') : K(X₂')] = [k(X₁) : k(X₂)]`. -/
theorem finrank_functionField_eq_of_isPullback :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₁
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₂
    haveI := isDominant_of_baseChange H₁ H₂ hf'
    (letI := f'.functionFieldMap.hom.toAlgebra;
      Module.finrank X₂'.functionField X₁'.functionField) =
      (letI := f.functionFieldMap.hom.toAlgebra;
        Module.finrank X₂.functionField X₁.functionField) :=
  (finrank_and_isSeparable_functionField_of_isPullback H₁ H₂ hf').1

/-- **Generic separability is invariant under arbitrary field extensions.** Let `f : X₁ ⟶ X₂` be a
dominant `k`-morphism between geometrically integral `k`-schemes whose function-field extension is
algebraic, and let `f' : X₁' ⟶ X₂'` be its base change along an arbitrary field extension `K / k`.
Then `K(X₁') / K(X₂')` is separable if and only if `k(X₁) / k(X₂)` is separable. -/
theorem isSeparable_functionField_iff_of_isPullback
    (hAlg : letI := f.functionFieldMap.hom.toAlgebra;
      Algebra.IsAlgebraic X₂.functionField X₁.functionField) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₁
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H₂
    haveI := isDominant_of_baseChange H₁ H₂ hf'
    (letI := f'.functionFieldMap.hom.toAlgebra;
      Algebra.IsSeparable X₂'.functionField X₁'.functionField) ↔
      (letI := f.functionFieldMap.hom.toAlgebra;
        Algebra.IsSeparable X₂.functionField X₁.functionField) :=
  (finrank_and_isSeparable_functionField_of_isPullback H₁ H₂ hf').2 hAlg

end DominantBaseChange

end AlgebraicGeometry

end TauCeti
