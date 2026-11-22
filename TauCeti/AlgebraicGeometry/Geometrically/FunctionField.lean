/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.FieldTheory.AlgebraicClosure
public import TauCeti.FieldTheory.FunctionField.ConstantField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Parameter
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
* `TauCeti.AlgebraicGeometry.functionFieldTensorToBaseChange`,
  `TauCeti.AlgebraicGeometry.isFractionRing_functionField_tensorProduct_of_isPullback`,
  `TauCeti.AlgebraicGeometry.constantCompositum_functionField_eq_top_of_isPullback`,
  `TauCeti.AlgebraicGeometry.linearDisjoint_functionField_of_isPullback`: `K(Y)` as the fraction
  field of `k(X) ⊗[k] K`, constant compositum, and linear disjointness over arbitrary `K / k`.
* `TauCeti.AlgebraicGeometry.finrank_functionField_eq_of_isPullback`,
  `TauCeti.AlgebraicGeometry.isSeparable_functionField_iff_of_isPullback`: invariance of generic
  degree and separability of dominant morphisms under arbitrary field extensions.

The chart arguments use `TauCeti.AlgebraicGeometry.exists_affineOpen_isFractionRing` and
`AlgebraicGeometry.Scheme.Hom.nonempty_functionField_algEquiv_of_isOpenImmersion` (the function
field of an integral scheme is the fraction field of any affine chart), from
`TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`, and
`TauCeti.AlgebraicGeometry.exists_isOpenImmersion_tensorProduct_of_isPullback` (the base change of
an affine chart is an affine chart of the base change), from
`TauCeti/AlgebraicGeometry/Pullback/SpecMap.lean`.
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti

namespace AlgebraicGeometry

universe u

section

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
  obtain ⟨ι, _, -⟩ := exists_isOpenImmersion_tensorProduct_of_isPullback hw
    (IsPullback.of_hasPullback (X ↘ Spec (.of k)) s)
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
  obtain ⟨U, _, _, _, _, _, hw⟩ := exists_affineOpen_isFractionRing (k := k) (X := X)
  -- the base change `Spec (Γ(X, U) ⊗[k] K)` of `U` is an open subscheme of `Y` over `Spec K`
  obtain ⟨ι, _, hι⟩ := exists_isOpenImmersion_tensorProduct_of_isPullback hw H
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
  exact ι.nonempty_functionField_algEquiv_of_isOpenImmersion hι F'

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

section ArbitraryExtension

variable {K : Type u} [Field K] [Algebra k K] {Y : Scheme.{u}} [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include H

omit [IsIntegral X] in
/-- The base change of a geometrically integral `k`-scheme along any `K / k` is integral. -/
theorem isIntegral_of_isPullback_spec : IsIntegral Y :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ H

omit [IsIntegral X] [GeometricallyIntegral (X ↘ Spec (.of k))] in
/-- The projection from the base change along any field extension `K / k` is surjective. -/
theorem surjective_of_isPullback_spec : Surjective g :=
  MorphismProperty.of_isPullback (P := @Surjective) H.flip inferInstance

omit [IsIntegral X] [GeometricallyIntegral (X ↘ Spec (.of k))] in
/-- The projection from the base change along any field extension `K / k` is flat. -/
theorem flat_of_isPullback_spec : Flat g :=
  MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance

omit [IsIntegral X] [GeometricallyIntegral (X ↘ Spec (.of k))] in
/-- The projection from the base change along any field extension `K / k` is dominant. -/
theorem isDominant_of_isPullback_spec : IsDominant g :=
  have := surjective_of_isPullback_spec H; inferInstance

/-- Pullback of rational functions along `g : Y ⟶ X` agrees on `k` with `k → K → K(Y)`. -/
theorem functionFieldMap_baseChange_algebraMap (c : k) :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    g.functionFieldMap (algebraMap k X.functionField c) =
      algebraMap K Y.functionField (algebraMap k K c) := by
  have := isIntegral_of_isPullback_spec H; have := isDominant_of_isPullback_spec H
  have h : Spec.map (CommRingCat.ofHom (algebraMap k X.functionField) ≫ g.functionFieldMap) =
      Spec.map (CommRingCat.ofHom ((algebraMap K Y.functionField).comp (algebraMap k K))) := by
    rw [Spec.map_comp, ← Scheme.fromSpecStalk_genericPoint_comp_over,
      g.SpecMap_functionFieldMap_fromSpecStalk_assoc, H.w,
      reassoc_of% Scheme.fromSpecStalk_genericPoint_comp_over, ← Spec.map_comp,
      CommRingCat.ofHom_comp]
  exact congr($(Spec.map_injective h) c)

/-- The canonical `K`-algebra map `k(X) ⊗[k] K →ₐ[K] K(Y)` for `Y = X ×_k Spec K`. -/
noncomputable def functionFieldTensorToBaseChange :
    haveI := isIntegral_of_isPullback_spec H
    letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    (X.functionField ⊗[k] K) →ₐ[K] Y.functionField :=
  haveI := isIntegral_of_isPullback_spec H
  haveI := isDominant_of_isPullback_spec H
  letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra k Y.functionField :=
    ((algebraMap K Y.functionField).comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K Y.functionField := .of_algebraMap_eq fun _ ↦ rfl
  let φX : X.functionField →ₐ[k] Y.functionField :=
    ⟨g.functionFieldMap.hom, functionFieldMap_baseChange_algebraMap H⟩
  (Algebra.TensorProduct.liftEquivRight k K X.functionField Y.functionField φX).comp
    (Algebra.TensorProduct.commRight k K X.functionField).symm.toAlgHom

/-- On pure tensors, `functionFieldTensorToBaseChange` sends `a ⊗ₜ c` to `g^* a * c`. -/
@[simp]
theorem functionFieldTensorToBaseChange_tmul (a : X.functionField) (c : K) :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    functionFieldTensorToBaseChange H (a ⊗ₜ[k] c) =
      g.functionFieldMap a * algebraMap K Y.functionField c := by
  rw [mul_comm]
  simp [functionFieldTensorToBaseChange]

/-- Embed `Γ(X, U) ⊗[k] K` into `K(Y)` as a fraction-field map compatible with `g` and `K`. -/
private lemma exists_chart_to_baseChange_functionField {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] [Algebra k Γ(X, U)]
    (hw : hU.fromSpec ≫ (X ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    ∃ (_ : IsDomain (Γ(X, U) ⊗[k] K)) (α : (Γ(X, U) ⊗[k] K) →+* Y.functionField),
      (letI := α.toAlgebra; IsFractionRing (Γ(X, U) ⊗[k] K) Y.functionField) ∧
      (∀ a : Γ(X, U), α (a ⊗ₜ[k] 1) = g.functionFieldMap (algebraMap Γ(X, U) X.functionField a)) ∧
      (∀ c : K, α (1 ⊗ₜ[k] c) = algebraMap K Y.functionField c) := by
  have := isIntegral_of_isPullback_spec H; have := isDominant_of_isPullback_spec H
  let A := Γ(X, U); let R := CommRingCat.of (A ⊗[k] K)
  have := hU.isOpenImmersion_fromSpec
  obtain ⟨ι₀, _, hι₀K, hι₀g, -⟩ := exists_isOpenImmersion_spec_tensorProduct_of_isPullback H
    (iY := 𝟙 (Spec (.of k))) (iY' := 𝟙 (Spec (.of K))) (iX := hU.fromSpec)
    rfl ((Category.comp_id _).trans hw.symm)
  let cIso := (Algebra.TensorProduct.comm k K A).toRingEquiv.toCommRingCatIso
  let ι : Spec R ⟶ Y := Spec.map cIso.hom ≫ ι₀
  have hιK : ι ≫ (Y ↘ Spec (.of K)) = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : K →ₐ[k] A ⊗[k] K).toRingHom) := by
    rw [Category.assoc, hι₀K, Category.comp_id, ← Spec.map_comp]
    congr 1
  have hιg : ι ≫ g = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
      hU.fromSpec := by
    rw [Category.assoc, hι₀g, ← Spec.map_comp_assoc]
    congr 2
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion ι
  have hDomR : IsDomain R := (affine_isIntegral_iff R).mp this
  have : IsDominant ι := isDominant_iff_genericPoint_eq.mpr (genericPoint_eq_of_isOpenImmersion ι)
  let φ₀ : R ⟶ (Spec R).functionField := StructureSheaf.toStalk R (genericPoint (Spec R))
  let e : (Spec R).functionField ≃+* Y.functionField :=
    (asIso ι.functionFieldMap).symm.commRingCatIsoToRingEquiv
  let α : (A ⊗[k] K) →+* Y.functionField := e.toRingHom.comp φ₀.hom
  have hα_eq : CommRingCat.ofHom α = φ₀ ≫ inv ι.functionFieldMap := rfl
  have hSpecα : Spec.map (CommRingCat.ofHom α) ≫ ι = Y.fromSpecStalk (genericPoint Y) := by
    have hφ₀ : Spec.map φ₀ = (Spec R).fromSpecStalk (genericPoint (Spec R)) :=
      (_root_.AlgebraicGeometry.Spec.fromSpecStalk_eq' R (genericPoint (Spec R))).symm
    rw [hα_eq, Spec.map_comp_assoc, reassoc_of% hφ₀, ← ι.SpecMap_functionFieldMap_fromSpecStalk,
      Spec.map_inv, IsIso.inv_hom_id_assoc]
  let _ : Algebra (A ⊗[k] K) (Spec R).functionField := φ₀.hom.toAlgebra
  let _ : Algebra (A ⊗[k] K) Y.functionField := α.toAlgebra
  refine ⟨hDomR, α,
      @IsFractionRing.of_algEquiv (A ⊗[k] K) _ (Spec R).functionField Y.functionField _
        φ₀.hom.toAlgebra _ α.toAlgebra (functionField_isFractionRing_of_affine R)
        (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl), fun a ↦ ?_, fun c ↦ ?_⟩
  · have hxU : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
    have h1 : Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
        CommRingCat.ofHom α) ≫ hU.fromSpec =
        Spec.map (X.germToFunctionField U ≫ g.functionFieldMap) ≫ hU.fromSpec := by
      rw [Spec.map_comp_assoc, ← hιg, ← Category.assoc, hSpecα,
        ← g.SpecMap_functionFieldMap_fromSpecStalk, Spec.map_comp_assoc,
        ← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk,
        Scheme.germToFunctionField]
    exact congr($(Spec.map_injective ((cancel_mono hU.fromSpec).mp h1)) a)
  · have h2 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : K →ₐ[k] A ⊗[k] K).toRingHom ≫
        CommRingCat.ofHom α) = Spec.map (CommRingCat.ofHom (algebraMap K Y.functionField)) := by
      rw [Spec.map_comp, ← hιK, ← Category.assoc, hSpecα,
        Scheme.fromSpecStalk_genericPoint_comp_over]
    exact congr($(Spec.map_injective h2) c)

/-- **The function field of any field-extension base change:** `K(Y)` is the fraction field of
`k(X) ⊗[k] K` via `functionFieldTensorToBaseChange H` for arbitrary `K / k`. -/
theorem isFractionRing_functionField_tensorProduct_of_isPullback :
    haveI := isIntegral_of_isPullback_spec H
    letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra (X.functionField ⊗[k] K) Y.functionField :=
      (functionFieldTensorToBaseChange H).toRingHom.toAlgebra
    IsFractionRing (X.functionField ⊗[k] K) Y.functionField := by
  have := isIntegral_of_isPullback_spec H; have := isDominant_of_isPullback_spec H
  obtain ⟨U, hU, _, _, _, _, hw⟩ := exists_affineOpen_isFractionRing (k := k) (X := X)
  let A := Γ(X, U)
  obtain ⟨_, α, hFracA, hα_left, hα_right⟩ := exists_chart_to_baseChange_functionField H hU hw
  let ρ : (A ⊗[k] K) →ₐ[k] (X.functionField ⊗[k] K) :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A X.functionField) (AlgHom.id k K)
  let _ : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra (X.functionField ⊗[k] K) Y.functionField :=
    (functionFieldTensorToBaseChange H).toRingHom.toAlgebra
  let _ : Algebra (A ⊗[k] K) (X.functionField ⊗[k] K) := ρ.toRingHom.toAlgebra
  let _ : Algebra (A ⊗[k] K) Y.functionField := α.toAlgebra
  have : IsFractionRing (A ⊗[k] K) Y.functionField := hFracA
  have hα_eq : α = (algebraMap (X.functionField ⊗[k] K) Y.functionField).comp ρ.toRingHom :=
    RingHom.ext fun z ↦ TensorProduct.inductionOn z (fun a c ↦ by
      have hmul : (a ⊗ₜ[k] c : A ⊗[k] K) = (a ⊗ₜ[k] 1) * (1 ⊗ₜ[k] c) := by simp
      rw [hmul, map_mul, RingHom.comp_apply, map_mul, hα_left, hα_right]
      simp [RingHom.algebraMap_toAlgebra, ρ]) fun _ _ hx hy ↦ by simp [hx, hy]
  have : IsScalarTower (A ⊗[k] K) (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq' hα_eq
  have : IsScalarTower A (A ⊗[k] K) (X.functionField ⊗[k] K) :=
    .of_algebraMap_eq fun a ↦ by simp [RingHom.algebraMap_toAlgebra, ρ]
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] K) (nonZeroDivisors A))
      (X.functionField ⊗[k] K) :=
    IsLocalization.tensorProduct_tensorProduct k K (nonZeroDivisors A) X.functionField
      (by ext; simp [RingHom.algebraMap_toAlgebra, ρ])
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid (A ⊗[k] K) (nonZeroDivisors A))
    (X.functionField ⊗[k] K) Y.functionField

/-- For any field extension `K / k`, `K(Y)` is generated as a field by `k(X)` and `K`. -/
theorem constantCompositum_functionField_eq_top_of_isPullback :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
    constantCompositum X.functionField K Y.functionField = ⊤ := by
  have := isIntegral_of_isPullback_spec H; have := isDominant_of_isPullback_spec H
  let _ : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
  let _ : Algebra (X.functionField ⊗[k] K) Y.functionField :=
    (functionFieldTensorToBaseChange H).toRingHom.toAlgebra
  have : IsScalarTower X.functionField (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower K (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsFractionRing (X.functionField ⊗[k] K) Y.functionField :=
    isFractionRing_functionField_tensorProduct_of_isPullback H
  rw [constantCompositum_def]
  exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)

/-- For any field extension `K / k`, `K` and `k(X)` are linearly disjoint over `k` in `K(Y)`. -/
theorem linearDisjoint_functionField_of_isPullback :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
    letI : Algebra k Y.functionField :=
      ((algebraMap K Y.functionField).comp (algebraMap k K)).toAlgebra
    haveI : IsScalarTower k K Y.functionField := .of_algebraMap_eq fun _ ↦ rfl
    haveI : IsScalarTower k X.functionField Y.functionField :=
      .of_algebraMap_eq fun c ↦ (functionFieldMap_baseChange_algebraMap H c).symm
    (IsScalarTower.toAlgHom k K Y.functionField).fieldRange.LinearDisjoint X.functionField := by
  have := isIntegral_of_isPullback_spec H; have := isDominant_of_isPullback_spec H
  let _ : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
  let _ : Algebra k Y.functionField :=
    ((algebraMap K Y.functionField).comp (algebraMap k K)).toAlgebra
  let _ : Algebra (X.functionField ⊗[k] K) Y.functionField :=
    (functionFieldTensorToBaseChange H).toRingHom.toAlgebra
  have : IsScalarTower k K Y.functionField := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k X.functionField Y.functionField :=
    .of_algebraMap_eq fun c ↦ (functionFieldMap_baseChange_algebraMap H c).symm
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
  exact linearDisjoint_of_isFractionRing_tensorProduct
    (k := k) (F := X.functionField) (K := K) (Q := Y.functionField)

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

omit [GeometricallyIntegral (X₁ ↘ Spec (.of k))] [GeometricallyIntegral (X₂ ↘ Spec (.of k))] in
/-- The base change of a dominant `k`-morphism between integral `k`-schemes along any field
extension `K / k` is dominant. -/
theorem isDominant_of_baseChange : IsDominant f' :=
  have : Flat g₂ := flat_of_isPullback_spec H₂
  IsDominant.of_isPullback_of_flat (IsPullback.of_bot (by simpa [comp_over] using H₁) hf'.symm H₂)

/-- Pullback of rational functions commutes with base change along any field extension `K / k`. -/
theorem functionFieldMap_comp_of_baseChange :
    haveI := isIntegral_of_isPullback_spec H₁
    haveI := isIntegral_of_isPullback_spec H₂
    haveI := isDominant_of_isPullback_spec H₁
    haveI := isDominant_of_isPullback_spec H₂
    haveI := isDominant_of_baseChange H₁ H₂ hf'
    f.functionFieldMap ≫ g₁.functionFieldMap = g₂.functionFieldMap ≫ f'.functionFieldMap := by
  have := isIntegral_of_isPullback_spec H₁; have := isIntegral_of_isPullback_spec H₂
  have := isDominant_of_isPullback_spec H₁; have := isDominant_of_isPullback_spec H₂
  have := isDominant_of_baseChange H₁ H₂ hf'
  rw [← Scheme.Hom.functionFieldMap_comp, eq_comm, Scheme.Hom.eq_functionFieldMap_iff,
    Spec.map_comp_assoc, g₂.SpecMap_functionFieldMap_fromSpecStalk,
    f'.SpecMap_functionFieldMap_fromSpecStalk_assoc, hf']

/-- Shared tower setup for generic degree and generic separability invariance. -/
private theorem finrank_and_isSeparable_functionField_of_isPullback :
    haveI := isIntegral_of_isPullback_spec H₁
    haveI := isIntegral_of_isPullback_spec H₂
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
  have := isIntegral_of_isPullback_spec H₁; have := isIntegral_of_isPullback_spec H₂
  have := isDominant_of_isPullback_spec H₁; have := isDominant_of_isPullback_spec H₂
  have := isDominant_of_baseChange H₁ H₂ hf'
  let _ : Algebra X₂.functionField X₁.functionField := f.functionFieldMap.hom.toAlgebra
  let _ : Algebra X₂'.functionField X₁'.functionField := f'.functionFieldMap.hom.toAlgebra
  let _ : Algebra X₁.functionField X₁'.functionField := g₁.functionFieldMap.hom.toAlgebra
  let _ : Algebra X₂.functionField X₂'.functionField := g₂.functionFieldMap.hom.toAlgebra
  let _ : Algebra k X₁'.functionField :=
    ((algebraMap K X₁'.functionField).comp (algebraMap k K)).toAlgebra
  let _ : Algebra X₂.functionField X₁'.functionField :=
    (g₁.functionFieldMap.hom.comp f.functionFieldMap.hom).toAlgebra
  have : IsScalarTower k X₂.functionField X₁.functionField :=
    .of_algebraMap_eq fun c ↦ (f.functionFieldMap_algebraMap k c).symm
  have : IsScalarTower K X₂'.functionField X₁'.functionField :=
    .of_algebraMap_eq fun c ↦ (f'.functionFieldMap_algebraMap K c).symm
  have : IsScalarTower k K X₁'.functionField := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k X₁.functionField X₁'.functionField :=
    .of_algebraMap_eq fun c ↦ (functionFieldMap_baseChange_algebraMap H₁ c).symm
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
    haveI := isIntegral_of_isPullback_spec H₁
    haveI := isIntegral_of_isPullback_spec H₂
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
    haveI := isIntegral_of_isPullback_spec H₁
    haveI := isIntegral_of_isPullback_spec H₂
    haveI := isDominant_of_baseChange H₁ H₂ hf'
    (letI := f'.functionFieldMap.hom.toAlgebra;
      Algebra.IsSeparable X₂'.functionField X₁'.functionField) ↔
      (letI := f.functionFieldMap.hom.toAlgebra;
        Algebra.IsSeparable X₂.functionField X₁.functionField) :=
  (finrank_and_isSeparable_functionField_of_isPullback H₁ H₂ hf').2 hAlg

end DominantBaseChange

end AlgebraicGeometry

end TauCeti
