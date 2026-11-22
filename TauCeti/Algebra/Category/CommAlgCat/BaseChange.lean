/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Algebra.Category.CommAlgCat.Localization
public import TauCeti.Algebra.Category.CommAlgCat.RestrictScalars
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
public import TauCeti.CategoryTheory.Monoidal.Internal.Module
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Base change of commutative algebras

Extension of scalars sends a commutative `R`-algebra `A` to `S ⊗[R] A`. It is left adjoint
to restriction of scalars, and therefore preserves colimits. In particular, a filtered
presentation of an algebra base changes to a filtered presentation over the new base.

The adjunction packages Mathlib's `Algebra.TensorProduct.liftEquivRight`, with the forward
map given by restriction to `1 ⊗ a` and the inverse by `s ⊗ a ↦ s • f(a)`.

For a submonoid `M` of `R`, `CommAlgCat.localizationFunctor M` is naturally isomorphic to
`CommAlgCat.extendScalars R (Localization M)` (`CommAlgCat.localizationFunctorIsoExtendScalars`).
Moreover, `CommAlgCat.extendScalars R S` is naturally isomorphic to the functor induced by
`ModuleCat.extendScalars (algebraMap R S)` on commutative monoid objects
(`CommAlgCat.extendScalarsIsoMapCommMon`).
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

universe u v w

namespace CommAlgCat

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Extension of scalars for commutative algebras, with scalar ring `S`. -/
noncomputable abbrev extendScalars : CommAlgCat.{w} R ⥤ CommAlgCat.{max v w} S where
  obj A := of S (S ⊗[R] A)
  map f := ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f.hom)
  map_id A := by ext; simp
  map_comp f g := by ext; simp

/-- The algebra underlying extension of scalars is the tensor product. -/
lemma extendScalars_obj (A : CommAlgCat.{w} R) :
    (extendScalars R S).obj A = of S (S ⊗[R] A) :=
  (rfl)

/-- The morphism part of base change tensors a morphism with the identity on `S`. -/
lemma extendScalars_map_hom {A A' : CommAlgCat.{w} R} (f : A ⟶ A') :
    ((extendScalars R S).map f).hom = Algebra.TensorProduct.map (AlgHom.id S S) f.hom :=
  (rfl)

/-- The Hom equivalence for extension and restriction of scalars. -/
noncomputable def extendScalarsHomEquiv (A : CommAlgCat.{max v w} R)
    (B : CommAlgCat.{max v w} S) :
    ((extendScalars R S).obj A ⟶ B) ≃
      (A ⟶ (restrictScalars (algebraMap R S)).obj B) := by
  letI : Algebra R B := Algebra.compHom B (algebraMap R S)
  letI : IsScalarTower R S B := .of_algebraMap_eq' rfl
  exact (ConcreteCategory.homEquiv (C := CommAlgCat S)
    (X := (extendScalars R S).obj A) (Y := B)).trans
    ((Algebra.TensorProduct.liftEquivRight R S A B).symm.trans
      (ConcreteCategory.homEquiv (C := CommAlgCat R)
        (X := A) (Y := (restrictScalars (algebraMap R S)).obj B)).symm)

/-- The adjunction's forward map is evaluation on the second tensor factor. -/
@[simp]
lemma extendScalarsHomEquiv_apply (A : CommAlgCat.{max v w} R)
    (B : CommAlgCat.{max v w} S) (f : (extendScalars R S).obj A ⟶ B) (a : A) :
    (extendScalarsHomEquiv R S A B f).hom a = f.hom (1 ⊗ₜ[R] a) :=
  (rfl)

/-- The adjunction's inverse extends a map by `S`-linearity. -/
@[simp]
lemma extendScalarsHomEquiv_symm_tmul (A : CommAlgCat.{max v w} R)
    (B : CommAlgCat.{max v w} S)
    (f : A ⟶ (restrictScalars (algebraMap R S)).obj B) (s : S) (a : A) :
    ((extendScalarsHomEquiv R S A B).symm f).hom (s ⊗ₜ[R] a) = s • f.hom a := by
  simp [extendScalarsHomEquiv, ConcreteCategory.homEquiv,
    Algebra.TensorProduct.liftEquivRight, Algebra.smul_def]

/-- Tensor-product base change is left adjoint to restriction of scalars. -/
noncomputable def extendRestrictScalarsAdj :
    extendScalars.{u, v, max v w} R S ⊣ restrictScalars (algebraMap R S) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extendScalarsHomEquiv R S
      homEquiv_naturality_left_symm := by
        intro A A' B f g
        apply (extendScalarsHomEquiv R S A B).injective
        ext a
        simp [extendScalarsHomEquiv_apply R S A B,
          extendScalarsHomEquiv_symm_tmul R S A' B, Algebra.TensorProduct.map_tmul]
      homEquiv_naturality_right := by
        intro A B B' f g
        ext a
        rfl }

/-- The adjunction uses the tensor-product Hom equivalence. -/
@[simp]
lemma extendRestrictScalarsAdj_homEquiv (A : CommAlgCat.{max v w} R)
    (B : CommAlgCat.{max v w} S) :
    (extendRestrictScalarsAdj R S).homEquiv A B = extendScalarsHomEquiv R S A B := by
  simp [extendRestrictScalarsAdj]

/-- Base change is a left adjoint, so the general adjunction API makes it preserve colimits. -/
noncomputable instance extendScalars_isLeftAdjoint :
    (extendScalars.{u, v, max v w} R S).IsLeftAdjoint :=
  (extendRestrictScalarsAdj R S).isLeftAdjoint

section Localization

variable {R}

private noncomputable def localizationFunctorAlgEquiv (M : Submonoid R)
    (A : CommAlgCat.{max u w} R) :
    ((localizationFunctor.{u, max u w} M).obj A) ≃ₐ[Localization M]
      (Localization M ⊗[R] A) :=
  let e₁ : ((localizationFunctor.{u, max u w} M).obj A) ≃ₐ[A]
      Localization (Algebra.algebraMapSubmonoid A M) :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid A M) _ _
  let e₂ : ((localizationFunctor.{u, max u w} M).obj A) ≃ₐ[Localization M]
      Localization (Algebra.algebraMapSubmonoid A M) :=
    { e₁.toRingEquiv with
      commutes' := fun z ↦ by
        have h : e₁.toRingHom.comp
            (algebraMap (Localization M) ((localizationFunctor.{u, max u w} M).obj A)) =
            algebraMap (Localization M) (Localization (Algebra.algebraMapSubmonoid A M)) := by
          apply IsLocalization.ringHom_ext M
          ext v
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply R (Localization M)
              ((localizationFunctor.{u, max u w} M).obj A) v,
            ← IsScalarTower.algebraMap_apply R (Localization M)
              (Localization (Algebra.algebraMapSubmonoid A M)) v,
            IsScalarTower.algebraMap_apply R A ((localizationFunctor.{u, max u w} M).obj A) v,
            IsScalarTower.algebraMap_apply R A
              (Localization (Algebra.algebraMapSubmonoid A M)) v]
          exact e₁.commutes _
        exact congr($h z) }
  e₂.trans (Localization.tensorRightAlgEquiv M A).symm

private theorem localizationFunctorAlgEquiv_algebraMap (M : Submonoid R)
    (A : CommAlgCat.{max u w} R) (a : A) :
    localizationFunctorAlgEquiv M A
        (algebraMap A ((localizationFunctor.{u, max u w} M).obj A) a) =
      (1 : Localization M) ⊗ₜ[R] a := by
  dsimp [localizationFunctorAlgEquiv]
  rw [AlgEquiv.symm_apply_eq]
  exact ((IsLocalization.algEquiv (Algebra.algebraMapSubmonoid A M)
    ((localizationFunctor.{u, max u w} M).obj A)
    (Localization (Algebra.algebraMapSubmonoid A M))).commutes a).trans
    (Localization.tensorRightAlgEquiv_apply_one_tmul M a).symm

/-- Algebra localization at `M` is naturally isomorphic to extension of scalars along
`R → Localization M`. -/
noncomputable def localizationFunctorIsoExtendScalars (M : Submonoid R) :
    localizationFunctor.{u, max u w} M ≅ extendScalars.{u, u, max u w} R (Localization M) :=
  NatIso.ofComponents
    (fun A ↦ isoMk (localizationFunctorAlgEquiv M A))
    fun {A B} f ↦ by
      apply hom_ext
      apply AlgHom.toRingHom_injective
      apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid A M)
      ext a
      simp only [hom_comp, AlgHom.coe_comp, Function.comp_apply, RingHom.coe_comp,
        AlgHom.coe_toRingHom, isoMk_hom, hom_ofHom, AlgEquiv.toAlgHom_apply]
      rw [localizationFunctor_map_hom_algebraMap, localizationFunctorAlgEquiv_algebraMap,
        localizationFunctorAlgEquiv_algebraMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- The forward component of `localizationFunctorIsoExtendScalars` sends `algebraMap A _ a` to
`1 ⊗ₜ a`. -/
@[simp]
theorem localizationFunctorIsoExtendScalars_hom_app_algebraMap (M : Submonoid R)
    (A : CommAlgCat.{max u w} R) (a : A) :
    (localizationFunctorIsoExtendScalars M).hom.app A
        (algebraMap A ((localizationFunctor M).obj A) a) =
      (1 : Localization M) ⊗ₜ[R] a :=
  localizationFunctorAlgEquiv_algebraMap M A a

/-- The inverse component of `localizationFunctorIsoExtendScalars` sends `1 ⊗ₜ a` to
`algebraMap A _ a`. -/
@[simp]
theorem localizationFunctorIsoExtendScalars_inv_app_one_tmul (M : Submonoid R)
    (A : CommAlgCat.{max u w} R) (a : A) :
    (localizationFunctorIsoExtendScalars M).inv.app A ((1 : Localization M) ⊗ₜ[R] a) =
      algebraMap A ((localizationFunctor M).obj A) a :=
  (congrArg ((localizationFunctorIsoExtendScalars M).inv.app A)
    (localizationFunctorIsoExtendScalars_hom_app_algebraMap M A a).symm).trans
    (ConcreteCategory.congr_hom ((localizationFunctorIsoExtendScalars M).hom_inv_id_app A) _)

end Localization

end CommAlgCat

namespace CommAlgCat

section Monoidal

open scoped ChangeOfRings MonObj

/-- Component isomorphism identifying `S ⊗[R] A` with the commutative algebra attached to
`(ModuleCat.extendScalars (algebraMap R S)).mapCommMon`. -/
private noncomputable def extendScalarsObjIsoMapCommMonObj (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : CommAlgCat.{u} R) :
    (extendScalars.{u, u, u} R S).obj A ≅
      ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.obj
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapCommMon.obj
          (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj A)) :=
  let φ := algebraMap R S
  let G := ModuleCat.extendScalars.{u, u, u} φ
  let A₀ := ModuleCat.of R A
  let A' := ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj A
  let B := ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.obj (G.mapCommMon.obj A')
  let eLin : (S ⊗[R] A) ≃ₗ[S] B :=
    (ModuleCat.extendScalarsAlgebraMapIso (S := S) A₀).symm.toLinearEquiv
  let eAlg : (S ⊗[R] A) ≃ₐ[S] B :=
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct eLin
      (fun s₁ s₂ a₁ a₂ ↦ by
        have he (s : S) (a : A) : eLin (s ⊗ₜ[R] a) = s ⊗ₜ[R, φ] (a : A'.X) :=
          ModuleCat.extendScalarsAlgebraMapIso_inv_tmul A₀ s a
        symm
        refine (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor_obj_mapCommMon_mul
          G A' _ _).trans ?_
        refine (congrArg (fun z ↦ G.map (MonObj.mul (X := A'.X))
            (Functor.LaxMonoidal.μ G A'.X A'.X z))
          (congrArg₂ (TensorProduct.tmul S (M := G.obj A'.X) (N := G.obj A'.X))
            (he s₁ a₁) (he s₂ a₂))).trans ?_
        refine (congrArg (G.map (MonObj.mul (X := A'.X)))
          (ModuleCat.extendScalars_μ_tmul φ A'.X A'.X s₁ s₂ a₁ a₂)).trans ?_
        refine (ModuleCat.ExtendScalars.map_tmul φ (MonObj.mul (X := A'.X))
          (s₁ * s₂) _).trans ?_
        rw [ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse_obj_mul]
        exact (congrArg (fun x : A₀ ↦ (s₁ * s₂) ⊗ₜ[R, φ] x)
          (LinearMap.mul'_apply (R := R) (a := a₁) (b := a₂))).trans
          (he (s₁ * s₂) (a₁ * a₂)).symm)
      (by
        symm
        refine (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor_obj_mapCommMon_one
          G A').trans ?_
        refine (congrArg (G.map (MonObj.one (X := A'.X)))
          (ModuleCat.extendScalars_ε_apply φ 1)).trans ?_
        refine (ModuleCat.ExtendScalars.map_tmul φ (MonObj.one (X := A'.X)) 1 (1 : R)).trans ?_
        rw [ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse_obj_one]
        exact (congrArg (fun x : A₀ ↦ (1 : S) ⊗ₜ[R, φ] x) (map_one (algebraMap R A))).trans
          (ModuleCat.extendScalarsAlgebraMapIso_inv_tmul A₀ 1 1).symm)
  isoMk eAlg

private theorem extendScalarsObjIsoMapCommMonObj_hom_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : CommAlgCat.{u} R) (s : S) (a : A) :
    dsimp% only (extendScalarsObjIsoMapCommMonObj R S A).hom (s ⊗ₜ[R] a) =
      s ⊗ₜ[R, algebraMap R S] a :=
  (Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply
    (C := ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.obj
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapCommMon.obj
        (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj A))) _ _ _ _).trans
    (ModuleCat.extendScalarsAlgebraMapIso_inv_tmul (ModuleCat.of R A) s a)

/-- Extension of scalars of commutative `R`-algebras along `algebraMap R S` is naturally
isomorphic to the functor induced by `ModuleCat.extendScalars (algebraMap R S)` on commutative
monoid objects. -/
noncomputable def extendScalarsIsoMapCommMon (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] :
    extendScalars.{u, u, u} R S ≅
      ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙
        (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapCommMon ⋙
          ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor :=
  NatIso.ofComponents (extendScalarsObjIsoMapCommMonObj R S) fun {A B} f ↦ by
    have htmul (s : S) (a : A) :
        (extendScalarsObjIsoMapCommMonObj R S B).hom.hom
            (Algebra.TensorProduct.map (AlgHom.id S S) f.hom (s ⊗ₜ[R] a)) =
          ((ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙
              (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapCommMon ⋙
                ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor).map f).hom
            ((extendScalarsObjIsoMapCommMonObj R S A).hom.hom (s ⊗ₜ[R] a)) := by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        extendScalarsObjIsoMapCommMonObj_hom_tmul, extendScalarsObjIsoMapCommMonObj_hom_tmul]
      symm
      refine (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor_map_apply _ _).trans ?_
      exact ModuleCat.ExtendScalars.map_tmul (algebraMap R S)
        (ModuleCat.ofHom f.hom.toLinearMap) s a
    apply hom_ext
    apply AlgHom.toRingHom_injective
    apply Algebra.TensorProduct.ringHom_ext
    · ext s
      simpa [hom_comp, Algebra.TensorProduct.includeLeftRingHom_apply] using htmul s 1
    · ext a
      simpa [hom_comp] using htmul 1 a

-- Normalize `CommAlgCat.of` carrier projections so `@[simp]` matches after projection reduction.
/-- `extendScalarsIsoMapCommMon` sends `s ⊗ a` to `s ⊗ a`. -/
@[simp]
theorem extendScalarsIsoMapCommMon_hom_app_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : CommAlgCat.{u} R) (s : S) (a : A) :
    dsimp% only [Functor.comp_obj] ((extendScalarsIsoMapCommMon R S).hom.app A) (s ⊗ₜ[R] a) =
      s ⊗ₜ[R, algebraMap R S] a :=
  extendScalarsObjIsoMapCommMonObj_hom_tmul R S A s a

/-- The inverse of `extendScalarsIsoMapCommMon` sends `s ⊗ a` to `s ⊗ a`. -/
@[simp]
theorem extendScalarsIsoMapCommMon_inv_app_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : CommAlgCat.{u} R) (s : S) (a : A) :
    dsimp% only [Functor.comp_obj]
        ((extendScalarsIsoMapCommMon R S).inv.app A) (s ⊗ₜ[R, algebraMap R S] a) =
      s ⊗ₜ[R] a :=
  (congrArg ((extendScalarsIsoMapCommMon R S).inv.app A)
    (extendScalarsIsoMapCommMon_hom_app_tmul R S A s a).symm).trans
    (ConcreteCategory.congr_hom ((extendScalarsIsoMapCommMon R S).hom_inv_id_app A) (s ⊗ₜ[R] a))

end Monoidal

end CommAlgCat
