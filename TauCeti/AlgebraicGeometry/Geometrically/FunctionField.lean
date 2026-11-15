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
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
public import TauCeti.RingTheory.TensorProduct.IsDomain

/-!
# The function field of a geometrically integral scheme and its base change

Let `X` be an integral scheme over a field `k` that is geometrically integral over `k`. Then for
every field extension `L / k` the ring `k(X) ⊗[k] L` is a domain, and consequently `k` is
algebraically closed in the function field `k(X)`, that is, `k` is the full field of constants of
`k(X)`.

For the first statement, choose a nonempty affine open `U` of `X`. The base change
`Spec (Γ(X, U) ⊗[k] L)` of `U` to `L` is a nonempty open subscheme of the integral scheme
`X ×_k Spec L`, so `Γ(X, U) ⊗[k] L` is a domain, and `k(X) ⊗[k] L` is a localization of it because
`k(X)` is the fraction field of `Γ(X, U)`. The second statement follows by taking for `L` an
algebraic closure of `k` (`TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`).

For an arbitrary field extension `K / k` (algebraic or transcendental, separable or not), the
projection `g : Y ⟶ X` from `Y = X ×_k Spec K` is surjective and dominant, and the canonical
`K`-algebra homomorphism `k(X) ⊗[k] K →ₐ[K] K(Y)` sending `a ⊗ c` to `g^* a · c` presents `K(Y)` as
the fraction field of `k(X) ⊗[k] K` (`isFractionRing_functionField_tensorProduct_of_isPullback`).
When `K / k` is algebraic, `k(X) ⊗[k] K` is already a field, identifying `K(Y)` with any constant
compositum `k(X) · K` (`nonempty_functionField_algEquiv_of_isPullback`).

Consequently, if `f : X₁ ⟶ X₂` is a dominant `k`-morphism between geometrically integral
`k`-schemes and `f' : X₁' ⟶ X₂'` is its base change to an arbitrary field extension `K / k`, then
`f'` is dominant and preserves the function-field degree `[K(X₁') : K(X₂')] = [k(X₁) : k(X₂)]` as
well as separability of algebraic function-field extensions.

The proof is built on Andrew Yang's formalization of geometrically integral morphisms in Mathlib
(`AlgebraicGeometry.GeometricallyIntegral`, in `Mathlib/AlgebraicGeometry/Geometrically/Integral`),
which supplies the integrality of the base change `X ×_k Spec L`.

## Main results

* `AlgebraicGeometry.IsDominant.of_flat` and
  `AlgebraicGeometry.IsDominant.of_isPullback_of_flat`: flat morphisms between irreducible schemes
  are dominant, and pullbacks of dominant morphisms between irreducible schemes along flat
  morphisms are dominant;
* `TauCeti.AlgebraicGeometry.isDomain_functionField_tensorProduct_of_geometricallyIntegral`:
  `k(X) ⊗[k] L` is a domain for every field extension `L / k`;
* `TauCeti.AlgebraicGeometry.isIntegrallyClosedIn_functionField_of_geometricallyIntegral`:
  `k` is algebraically closed in `k(X)`;
* `TauCeti.AlgebraicGeometry.functionFieldTensorToBaseChange` and
  `TauCeti.AlgebraicGeometry.isFractionRing_functionField_tensorProduct_of_isPullback`: for any
  field extension `K / k`, `K(X ×_k Spec K)` is the fraction field of `k(X) ⊗[k] K`;
* `TauCeti.AlgebraicGeometry.nonempty_functionField_algEquiv_of_isPullback` and
  `TauCeti.AlgebraicGeometry.isIntegrallyClosedIn_of_constantCompositum_eq_top`: the algebraic
  constant-compositum specialization `K(Y) ≃ₐ[K] k(X) · K` and exactness of `K` in `k(X) · K`;
* `TauCeti.AlgebraicGeometry.finrank_functionField_eq_of_isPullback` and
  `TauCeti.AlgebraicGeometry.isSeparable_functionField_iff_of_isPullback`: invariance of generic
  degree and separability of dominant morphisms under arbitrary field extensions.
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- Any flat morphism between irreducible schemes sends the generic point to the generic point and
is therefore dominant. -/
theorem IsDominant.of_flat {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (g : X ⟶ Y) [Flat g] : IsDominant g := by
  obtain ⟨z, hz, hgz⟩ := Flat.generalizingMap g ((genericPoint_spec Y).specializes trivial)
  rw [isDominant_iff_genericPoint_eq, ← hgz]
  exact congrArg g (((genericPoint_spec X).specializes trivial).antisymm hz).eq

/-- The pullback of a dominant morphism between irreducible schemes along any flat morphism is
dominant, with no irreducibility or openness assumption on the base change. -/
theorem IsDominant.of_isPullback_of_flat {X Y X' Y' : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [IsDominant f] [Flat gY] (H : IsPullback gX f' f gY) : IsDominant f' := by
  rw [isDominant_iff, denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro y'
  obtain ⟨z', hz', hgz'⟩ := Flat.generalizingMap gY ((genericPoint_spec Y).specializes trivial)
  obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (genericPoint X) z'
    (f.genericPoint_eq_of_isDominant.trans hgz'.symm)
  exact hz'.mem_closed isClosed_closure
    (subset_closure ⟨H.isoPullback.inv w, by simp [← Scheme.Hom.comp_apply, hw]⟩)

/-- A dominant open immersion between irreducible schemes induces an isomorphism on generic
stalks (function fields). -/
instance Scheme.Hom.isIso_functionFieldMap_of_isOpenImmersion {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) [IsOpenImmersion f] [IsDominant f] :
    IsIso f.functionFieldMap := by
  let h : genericPoint Y ⤳ f (genericPoint X) :=
    specializes_of_eq f.genericPoint_eq_of_isDominant.symm
  let ψ : X.functionField ⟶ Y.functionField :=
    inv (f.stalkMap (genericPoint X)) ≫ Y.presheaf.stalkSpecializes h
  have hψ : Spec.map ψ ≫ X.fromSpecStalk (genericPoint X) ≫ f =
      Y.fromSpecStalk (genericPoint Y) := by
    dsimp only [ψ]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp_assoc,
      Spec.map_inv, IsIso.inv_hom_id_assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  · refine ((Scheme.Hom.eq_functionFieldMap_iff (𝟙 Y) _).mpr ?_).trans
      (Scheme.Hom.functionFieldMap_id (X := Y))
    rw [Category.comp_id, Spec.map_comp_assoc, f.SpecMap_functionFieldMap_fromSpecStalk, hψ]
  · refine ((Scheme.Hom.eq_functionFieldMap_iff (𝟙 X) _).mpr ?_).trans
      (Scheme.Hom.functionFieldMap_id (X := X))
    rw [Category.comp_id, ← cancel_mono f, Category.assoc, Spec.map_comp_assoc, hψ,
      f.SpecMap_functionFieldMap_fromSpecStalk]

end AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

section SingleScheme

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

section ArbitraryExtension

variable {K : Type u} [Field K] [Algebra k K] {Y : Scheme.{u}} [Y.Over (Spec (.of K))] {g : Y ⟶ X}

omit [IsIntegral X] in
/-- The base change of a geometrically integral `k`-scheme along any field extension `K / k` is
integral. -/
theorem isIntegral_of_isPullback_spec
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    IsIntegral Y :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ H

omit [IsIntegral X] [GeometricallyIntegral (X ↘ Spec (.of k))] in
/-- The projection from the base change along any field extension `K / k` is surjective. -/
theorem surjective_of_isPullback_spec
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Surjective g := by
  have : g = H.isoPullback.hom ≫ pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by simp
  rw [this]
  infer_instance

omit [IsIntegral X] [GeometricallyIntegral (X ↘ Spec (.of k))] in
/-- The projection from the base change along any field extension `K / k` is flat. -/
theorem flat_of_isPullback_spec
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Flat g := by
  have : g = H.isoPullback.hom ≫ pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by simp
  rw [this]
  infer_instance

omit [IsIntegral X] [GeometricallyIntegral (X ↘ Spec (.of k))] in
/-- The projection from the base change along any field extension `K / k` is dominant. -/
theorem isDominant_of_isPullback_spec
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    IsDominant g :=
  have := surjective_of_isPullback_spec H
  inferInstance

/-- Pullback of rational functions along `g : X ×_k Spec K ⟶ X` agrees on `k` with the structure
algebra map `k → K → K(Y)`. -/
theorem functionFieldMap_baseChange_algebraMap
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (c : k) :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    g.functionFieldMap (algebraMap k X.functionField c) =
      algebraMap K Y.functionField (algebraMap k K c) := by
  have := isIntegral_of_isPullback_spec H
  have := isDominant_of_isPullback_spec H
  have h : Spec.map (CommRingCat.ofHom (algebraMap k X.functionField) ≫ g.functionFieldMap) =
      Spec.map (CommRingCat.ofHom ((algebraMap K Y.functionField).comp (algebraMap k K))) := by
    rw [Spec.map_comp, ← Scheme.fromSpecStalk_genericPoint_comp_over,
      g.SpecMap_functionFieldMap_fromSpecStalk_assoc, H.w,
      reassoc_of% Scheme.fromSpecStalk_genericPoint_comp_over, ← Spec.map_comp,
      CommRingCat.ofHom_comp]
  exact congr($(Spec.map_injective h) c)

/-- The canonical `K`-algebra homomorphism `k(X) ⊗[k] K →ₐ[K] K(Y)` for the base change `Y` of a
geometrically integral `k`-scheme `X` along an arbitrary field extension `K / k`. -/
noncomputable def functionFieldTensorToBaseChange
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    haveI := isIntegral_of_isPullback_spec H
    letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    (X.functionField ⊗[k] K) →ₐ[K] Y.functionField :=
  haveI := isIntegral_of_isPullback_spec H
  haveI := isDominant_of_isPullback_spec H
  letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra k Y.functionField :=
    ((algebraMap K Y.functionField).comp (algebraMap k K)).toAlgebra
  let φX : X.functionField →ₐ[k] Y.functionField :=
    ⟨g.functionFieldMap.hom, functionFieldMap_baseChange_algebraMap H⟩
  let φK : K →ₐ[k] Y.functionField :=
    ⟨algebraMap K Y.functionField, fun _ ↦ rfl⟩
  { __ := (Algebra.TensorProduct.productMap φX φK).toRingHom
    commutes' c := by
      change (Algebra.TensorProduct.productMap φX φK) (1 ⊗ₜ[k] c) = algebraMap K Y.functionField c
      simp [φK] }

/-- On pure tensors, `functionFieldTensorToBaseChange` multiplies the pulled-back rational function
by the scalar from `K`. -/
@[simp]
theorem functionFieldTensorToBaseChange_tmul
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (a : X.functionField) (c : K) :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    functionFieldTensorToBaseChange H (a ⊗ₜ[k] c) =
      g.functionFieldMap a * algebraMap K Y.functionField c := by
  simp [functionFieldTensorToBaseChange]

/-- Embed the coordinate ring `Γ(X, U) ⊗[k] K` of a base-changed affine chart into `K(Y)` as a
fraction-field map compatible with `g.functionFieldMap` and `algebraMap K Y.functionField`. -/
private lemma exists_chart_to_baseChange_functionField
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] [Algebra k Γ(X, U)]
    (hw : hU.fromSpec ≫ (X ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    ∃ (_ : IsDomain (Γ(X, U) ⊗[k] K)) (α : (Γ(X, U) ⊗[k] K) →+* Y.functionField),
      (letI := α.toAlgebra; IsFractionRing (Γ(X, U) ⊗[k] K) Y.functionField) ∧
      (∀ a : Γ(X, U), α (a ⊗ₜ[k] 1) = g.functionFieldMap (algebraMap Γ(X, U) X.functionField a)) ∧
      (∀ c : K, α (1 ⊗ₜ[k] c) = algebraMap K Y.functionField c) := by
  have := isIntegral_of_isPullback_spec H
  have := isDominant_of_isPullback_spec H
  let A := Γ(X, U)
  let s := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let R := CommRingCat.of (A ⊗[k] K)
  let ι : Spec R ⟶ Y :=
    (pullbackSpecIso k A K).inv ≫ (pullback.congrHom hw.symm rfl).hom ≫
      (pullbackRightPullbackFstIso (X ↘ Spec (.of k)) s hU.fromSpec).inv ≫
      pullback.snd _ _ ≫ H.isoPullback.inv
  have hιK : ι ≫ (Y ↘ Spec (.of K)) = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : K →ₐ[k] A ⊗[k] K).toRingHom) := by simp [ι, s]
  have hιg : ι ≫ g = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
      hU.fromSpec := by simp [ι, s]
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion ι
  have hDomR : IsDomain R := (affine_isIntegral_iff R).mp this
  have : IsDominant ι := isDominant_iff_genericPoint_eq.mpr (genericPoint_eq_of_isOpenImmersion ι)
  let φ₀ : R ⟶ (Spec R).functionField := StructureSheaf.toStalk R (genericPoint (Spec R))
  let e : (Spec R).functionField ≃+* Y.functionField :=
    (asIso ι.functionFieldMap).symm.commRingCatIsoToRingEquiv
  let α : (A ⊗[k] K) →+* Y.functionField := e.toRingHom.comp φ₀.hom
  have hSpecα : Spec.map (CommRingCat.ofHom α) ≫ ι = Y.fromSpecStalk (genericPoint Y) := by
    have he : CommRingCat.ofHom α = φ₀ ≫ inv ι.functionFieldMap := rfl
    have hφ₀ : Spec.map φ₀ = (Spec R).fromSpecStalk (genericPoint (Spec R)) :=
      (_root_.AlgebraicGeometry.Spec.fromSpecStalk_eq' R (genericPoint (Spec R))).symm
    rw [he, Spec.map_comp_assoc, reassoc_of% hφ₀,
      ← ι.SpecMap_functionFieldMap_fromSpecStalk, Spec.map_inv, IsIso.inv_hom_id_assoc]
  let _ : Algebra (A ⊗[k] K) (Spec R).functionField := φ₀.hom.toAlgebra
  let _ : Algebra (A ⊗[k] K) Y.functionField := α.toAlgebra
  have hFrac : IsFractionRing (A ⊗[k] K) Y.functionField :=
    @IsFractionRing.of_algEquiv (A ⊗[k] K) _ (Spec R).functionField Y.functionField _
      φ₀.hom.toAlgebra _ α.toAlgebra (functionField_isFractionRing_of_affine R)
      (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl)
  refine ⟨hDomR, α, hFrac, fun a ↦ ?_, fun c ↦ ?_⟩
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

/-- **The function field of any field-extension base change.** Let `X` be a geometrically integral
scheme over `k` and `Y = X ×_k Spec K` its base change to an arbitrary field extension `K / k`
(algebraic or transcendental, separable or not). Then `K(Y)` is the fraction field of
`k(X) ⊗[k] K` via `functionFieldTensorToBaseChange H`. -/
theorem isFractionRing_functionField_tensorProduct_of_isPullback
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    haveI := isIntegral_of_isPullback_spec H
    letI : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra (X.functionField ⊗[k] K) Y.functionField :=
      (functionFieldTensorToBaseChange H).toRingHom.toAlgebra
    IsFractionRing (X.functionField ⊗[k] K) Y.functionField := by
  have := isIntegral_of_isPullback_spec H
  have := isDominant_of_isPullback_spec H
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
  have hα_eq : α = (algebraMap (X.functionField ⊗[k] K) Y.functionField).comp ρ.toRingHom := by
    apply RingHom.ext
    intro z
    refine TensorProduct.inductionOn z (fun a c ↦ ?_) fun x y hx hy ↦ by simp [hx, hy]
    have hmul : (a ⊗ₜ[k] c : A ⊗[k] K) = (a ⊗ₜ[k] 1) * (1 ⊗ₜ[k] c) := by simp
    rw [hmul, map_mul, RingHom.comp_apply, map_mul, hα_left, hα_right]
    simp [RingHom.algebraMap_toAlgebra, ρ]
  have : IsScalarTower (A ⊗[k] K) (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq' hα_eq
  have : IsScalarTower A (A ⊗[k] K) (X.functionField ⊗[k] K) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, ρ]
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] K) (nonZeroDivisors A))
      (X.functionField ⊗[k] K) :=
    IsLocalization.tensorProduct_tensorProduct k K (nonZeroDivisors A) X.functionField
      (by ext; simp [RingHom.algebraMap_toAlgebra, ρ])
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid (A ⊗[k] K) (nonZeroDivisors A))
    (X.functionField ⊗[k] K) Y.functionField

/-- For any field extension `K / k`, the function field `K(Y)` of `Y = X ×_k Spec K` is generated
as a field by `k(X)` and `K`. -/
theorem constantCompositum_functionField_eq_top_of_isPullback
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
    constantCompositum X.functionField K Y.functionField = ⊤ := by
  have := isIntegral_of_isPullback_spec H
  have := isDominant_of_isPullback_spec H
  let _ : Algebra K (X.functionField ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
  let _ : Algebra (X.functionField ⊗[k] K) Y.functionField :=
    (functionFieldTensorToBaseChange H).toRingHom.toAlgebra
  have : IsScalarTower X.functionField (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq fun a ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower K (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq fun c ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsFractionRing (X.functionField ⊗[k] K) Y.functionField :=
    isFractionRing_functionField_tensorProduct_of_isPullback H
  rw [constantCompositum_def]
  exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)

/-- For any field extension `K / k`, `K` and `k(X)` are linearly disjoint over `k` inside the
function field `K(Y)` of `Y = X ×_k Spec K`. -/
theorem linearDisjoint_functionField_of_isPullback
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    haveI := isIntegral_of_isPullback_spec H
    haveI := isDominant_of_isPullback_spec H
    letI : Algebra X.functionField Y.functionField := g.functionFieldMap.hom.toAlgebra
    letI : Algebra k Y.functionField :=
      ((algebraMap K Y.functionField).comp (algebraMap k K)).toAlgebra
    haveI : IsScalarTower k K Y.functionField := .of_algebraMap_eq fun _ ↦ rfl
    haveI : IsScalarTower k X.functionField Y.functionField :=
      .of_algebraMap_eq fun c ↦ (functionFieldMap_baseChange_algebraMap H c).symm
    (IsScalarTower.toAlgHom k K Y.functionField).fieldRange.LinearDisjoint X.functionField := by
  have := isIntegral_of_isPullback_spec H
  have := isDominant_of_isPullback_spec H
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
    .of_algebraMap_eq fun a ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower K (X.functionField ⊗[k] K) Y.functionField :=
    .of_algebraMap_eq fun c ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower k (X.functionField ⊗[k] K) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k X.functionField (X.functionField ⊗[k] K),
        ← IsScalarTower.algebraMap_apply X.functionField (X.functionField ⊗[k] K) Y.functionField,
        ← IsScalarTower.algebraMap_apply k X.functionField Y.functionField]
  have : IsFractionRing (X.functionField ⊗[k] K) Y.functionField :=
    isFractionRing_functionField_tensorProduct_of_isPullback H
  exact linearDisjoint_of_isFractionRing_tensorProduct
    (k := k) (F := X.functionField) (K := K) (Q := Y.functionField)

end ArbitraryExtension

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

end SingleScheme

section DominantBaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X₁ X₂ X₁' X₂' : Scheme.{u}} [X₁.Over (Spec (.of k))] [X₂.Over (Spec (.of k))]
  [X₁'.Over (Spec (.of K))] [X₂'.Over (Spec (.of K))]
  [IsIntegral X₁] [IsIntegral X₂]
  [GeometricallyIntegral (X₁ ↘ Spec (.of k))] [GeometricallyIntegral (X₂ ↘ Spec (.of k))]
  {f : X₁ ⟶ X₂} [f.IsOver (Spec (.of k))] [IsDominant f]
  {g₁ : X₁' ⟶ X₁} {g₂ : X₂' ⟶ X₂} {f' : X₁' ⟶ X₂'} [f'.IsOver (Spec (.of K))]

omit [GeometricallyIntegral (X₁ ↘ Spec (.of k))] [GeometricallyIntegral (X₂ ↘ Spec (.of k))] in
/-- The base change of a dominant `k`-morphism between integral `k`-schemes along any field
extension `K / k` is dominant. -/
theorem isDominant_of_baseChange
    (H₁ : IsPullback g₁ (X₁' ↘ Spec (.of K)) (X₁ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (H₂ : IsPullback g₂ (X₂' ↘ Spec (.of K)) (X₂ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hf' : f' ≫ g₂ = g₁ ≫ f) : IsDominant f' := by
  have : Flat g₂ := flat_of_isPullback_spec H₂
  have Hsq : IsPullback g₁ f' f g₂ :=
    IsPullback.of_bot (by simpa [comp_over] using H₁) hf'.symm H₂
  exact IsDominant.of_isPullback_of_flat Hsq

/-- Pullback of rational functions commutes with base change along any field extension `K / k`. -/
theorem functionFieldMap_comp_of_baseChange
    (H₁ : IsPullback g₁ (X₁' ↘ Spec (.of K)) (X₁ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (H₂ : IsPullback g₂ (X₂' ↘ Spec (.of K)) (X₂ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hf' : f' ≫ g₂ = g₁ ≫ f) :
    haveI := isIntegral_of_isPullback_spec H₁
    haveI := isIntegral_of_isPullback_spec H₂
    haveI := isDominant_of_isPullback_spec H₁
    haveI := isDominant_of_isPullback_spec H₂
    haveI := isDominant_of_baseChange H₁ H₂ hf'
    f.functionFieldMap ≫ g₁.functionFieldMap = g₂.functionFieldMap ≫ f'.functionFieldMap := by
  have := isIntegral_of_isPullback_spec H₁
  have := isIntegral_of_isPullback_spec H₂
  have := isDominant_of_isPullback_spec H₁
  have := isDominant_of_isPullback_spec H₂
  have := isDominant_of_baseChange H₁ H₂ hf'
  rw [← Scheme.Hom.functionFieldMap_comp, eq_comm, Scheme.Hom.eq_functionFieldMap_iff,
    Spec.map_comp_assoc, g₂.SpecMap_functionFieldMap_fromSpecStalk,
    f'.SpecMap_functionFieldMap_fromSpecStalk_assoc, hf']

/-- **Generic degree is invariant under arbitrary field extensions.** Let `f : X₁ ⟶ X₂` be a
dominant `k`-morphism between geometrically integral `k`-schemes, and let `f' : X₁' ⟶ X₂'` be its
base change along an arbitrary field extension `K / k` (algebraic or transcendental, separable or
not). Then `[K(X₁') : K(X₂')] = [k(X₁) : k(X₂)]`. -/
theorem finrank_functionField_eq_of_isPullback
    (H₁ : IsPullback g₁ (X₁' ↘ Spec (.of K)) (X₁ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (H₂ : IsPullback g₂ (X₂' ↘ Spec (.of K)) (X₂ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hf' : f' ≫ g₂ = g₁ ≫ f) :
    haveI := isIntegral_of_isPullback_spec H₁
    haveI := isIntegral_of_isPullback_spec H₂
    haveI := isDominant_of_baseChange H₁ H₂ hf'
    (letI := f'.functionFieldMap.hom.toAlgebra;
      Module.finrank X₂'.functionField X₁'.functionField) =
      (letI := f.functionFieldMap.hom.toAlgebra;
        Module.finrank X₂.functionField X₁.functionField) := by
  have := isIntegral_of_isPullback_spec H₁
  have := isIntegral_of_isPullback_spec H₂
  have := isDominant_of_isPullback_spec H₁
  have := isDominant_of_isPullback_spec H₂
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
  exact finrank_eq_of_constantCompositum_eq_top_of_linearDisjoint
    (linearDisjoint_functionField_of_isPullback H₁)
    (constantCompositum_functionField_eq_top_of_isPullback H₂)
    (constantCompositum_functionField_eq_top_of_isPullback H₁)

/-- **Generic separability is invariant under arbitrary field extensions.** Let `f : X₁ ⟶ X₂` be a
dominant `k`-morphism between geometrically integral `k`-schemes whose function-field extension is
algebraic, and let `f' : X₁' ⟶ X₂'` be its base change along an arbitrary field extension `K / k`.
Then `K(X₁') / K(X₂')` is separable if and only if `k(X₁) / k(X₂)` is separable. -/
theorem isSeparable_functionField_iff_of_isPullback
    (H₁ : IsPullback g₁ (X₁' ↘ Spec (.of K)) (X₁ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (H₂ : IsPullback g₂ (X₂' ↘ Spec (.of K)) (X₂ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hf' : f' ≫ g₂ = g₁ ≫ f)
    (hAlg : letI := f.functionFieldMap.hom.toAlgebra;
      Algebra.IsAlgebraic X₂.functionField X₁.functionField) :
    haveI := isIntegral_of_isPullback_spec H₁
    haveI := isIntegral_of_isPullback_spec H₂
    haveI := isDominant_of_baseChange H₁ H₂ hf'
    (letI := f'.functionFieldMap.hom.toAlgebra;
      Algebra.IsSeparable X₂'.functionField X₁'.functionField) ↔
      (letI := f.functionFieldMap.hom.toAlgebra;
        Algebra.IsSeparable X₂.functionField X₁.functionField) := by
  have := isIntegral_of_isPullback_spec H₁
  have := isIntegral_of_isPullback_spec H₂
  have := isDominant_of_isPullback_spec H₁
  have := isDominant_of_isPullback_spec H₂
  have := isDominant_of_baseChange H₁ H₂ hf'
  let _ : Algebra X₂.functionField X₁.functionField := f.functionFieldMap.hom.toAlgebra
  let _ : Algebra X₂'.functionField X₁'.functionField := f'.functionFieldMap.hom.toAlgebra
  let _ : Algebra X₁.functionField X₁'.functionField := g₁.functionFieldMap.hom.toAlgebra
  let _ : Algebra X₂.functionField X₂'.functionField := g₂.functionFieldMap.hom.toAlgebra
  let _ : Algebra k X₁'.functionField :=
    ((algebraMap K X₁'.functionField).comp (algebraMap k K)).toAlgebra
  let _ : Algebra X₂.functionField X₁'.functionField :=
    (g₁.functionFieldMap.hom.comp f.functionFieldMap.hom).toAlgebra
  have : Algebra.IsAlgebraic X₂.functionField X₁.functionField := hAlg
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
  exact isSeparable_iff_of_constantCompositum_eq_top_of_linearDisjoint
    (linearDisjoint_functionField_of_isPullback H₁)
    (constantCompositum_functionField_eq_top_of_isPullback H₂)
    (constantCompositum_functionField_eq_top_of_isPullback H₁)

end DominantBaseChange

end AlgebraicGeometry

end TauCeti
