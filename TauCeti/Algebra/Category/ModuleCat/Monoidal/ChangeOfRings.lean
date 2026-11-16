/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# Change of rings and tensor products of modules

Restriction of scalars along a morphism of commutative rings is compatible with the symmetric
braiding on module categories.

For a morphism `f : A →+* P` and a `P`-module `M`, tensoring an extension of scalars with `M`
over `P` is tensoring with `M` over `A`: `M ⊗[P] (P ⊗[A] X) ≅ M ⊗[A] X`, naturally in the
`A`-module `X` (`ModuleCat.extendScalarsCompTensorLeftIso`). Specializing `M` to the monoidal unit
`P` identifies `extendScalars f ⋙ restrictScalars f` with `tensorLeft ((restrictScalars f).obj P)`
(`ModuleCat.extendScalarsCompRestrictScalarsIso`).
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.ModuleCat

universe u

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restriction of scalars between module categories preserves the symmetric braiding. -/
instance restrictScalarsLaxBraided : (_root_.ModuleCat.restrictScalars f).LaxBraided where
  braided _ _ := _root_.ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl

end

end TauCeti.ModuleCat

namespace ModuleCat

open scoped TensorProduct ChangeOfRings

universe u

variable {A P : Type u} [CommRing A] [CommRing P] (f : A →+* P)

/-- The `A`-linear equivalence `M ⊗[P] (P ⊗[A] X) ≃ M ⊗[A] X`, `m ⊗ (s ⊗ x) ↦ (s • m) ⊗ x`,
where `A` acts through `f`. -/
private noncomputable def tensorExtendScalarsLinearEquiv (M : ModuleCat.{u} P)
    (X : ModuleCat.{u} A) :
    (restrictScalars f).obj (M ⊗ (extendScalars f).obj X) ≃ₗ[A]
      ((restrictScalars f).obj M ⊗ X : ModuleCat A) :=
  letI := f.toAlgebra
  letI : Module A M := Module.compHom M f
  haveI : IsScalarTower A P M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A P P M X).restrictScalars A

/-- **Projection formula for extension of scalars.** For `f : A →+* P` and a `P`-module `M`,
`M ⊗[P] (P ⊗[A] X) ≅ M ⊗[A] X` as `A`-modules, naturally in the `A`-module `X`; it sends
`m ⊗ (s ⊗ x)` to `(s • m) ⊗ x`. -/
noncomputable def extendScalarsCompTensorLeftIso (M : ModuleCat.{u} P) :
    extendScalars.{u, u, u} f ⋙ tensorLeft M ⋙ restrictScalars.{u} f ≅
      tensorLeft ((restrictScalars f).obj M) :=
  (NatIso.ofComponents (fun X ↦ (tensorExtendScalarsLinearEquiv f M X).toModuleIso.symm)
    fun _ ↦ by apply MonoidalCategory.tensor_ext; intros; rfl).symm

/-- The forward map of `extendScalarsCompTensorLeftIso` sends `m ⊗ (s ⊗ x)` to `(s • m) ⊗ x`. -/
@[simp]
theorem extendScalarsCompTensorLeftIso_hom_app_tmul (M : ModuleCat.{u} P) (X : ModuleCat.{u} A)
    (m : M) (s : P) (x : X) :
    (Hom.hom : ((restrictScalars f).obj (M ⊗ (extendScalars f).obj X) ⟶
        (restrictScalars f).obj M ⊗ X) → _) ((extendScalarsCompTensorLeftIso f M).hom.app X)
        (TensorProduct.tmul P (M := M) (N := (extendScalars f).obj X) m (s ⊗ₜ[A, f] x)) =
      TensorProduct.tmul A (M := (restrictScalars f).obj M) (N := X) (s • m) x :=
  (rfl)

/-- The inverse of `extendScalarsCompTensorLeftIso` sends `m ⊗ x` to `m ⊗ (1 ⊗ x)`. -/
@[simp]
theorem extendScalarsCompTensorLeftIso_inv_app_tmul (M : ModuleCat.{u} P) (X : ModuleCat.{u} A)
    (m : (restrictScalars f).obj M) (x : X) :
    (Hom.hom : ((restrictScalars f).obj M ⊗ X ⟶
        (restrictScalars f).obj (M ⊗ (extendScalars f).obj X)) → _)
        ((extendScalarsCompTensorLeftIso f M).inv.app X)
        (TensorProduct.tmul A (M := (restrictScalars f).obj M) (N := X) m x) =
      TensorProduct.tmul P (M := M) (N := (extendScalars f).obj X) m ((1 : P) ⊗ₜ[A, f] x) :=
  (rfl)

/-- Extension of scalars followed by restriction of scalars along `f : A →+* P` is naturally
isomorphic to tensoring on the left with `P` viewed as an `A`-module via `f`. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    extendScalars.{u, u, u} f ⋙ restrictScalars.{u} f ≅
      tensorLeft ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) :=
  Functor.isoWhiskerLeft (extendScalars.{u, u, u} f) (restrictScalars.{u} f).leftUnitor.symm ≪≫
    Functor.isoWhiskerLeft (extendScalars.{u, u, u} f)
      (Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso (ModuleCat.{u} P)).symm
        (restrictScalars.{u} f)) ≪≫
    extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))

/-- The forward map of `extendScalarsCompRestrictScalarsIso` sends `s ⊗ x` to `s ⊗ x`. -/
@[simp]
theorem extendScalarsCompRestrictScalarsIso_hom_app_tmul (X : ModuleCat.{u} A)
    (s : P) (x : X) :
    (Hom.hom : ((restrictScalars f).obj ((extendScalars f).obj X) ⟶
        (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X) → _)
        ((extendScalarsCompRestrictScalarsIso f).hom.app X) (s ⊗ₜ[A, f] x) =
      TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X) s x := by
  have h : ((extendScalarsCompRestrictScalarsIso f).hom.app X :
      (restrictScalars f).obj ((extendScalars f).obj X) ⟶
        (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X) =
      (restrictScalars f).map (λ_ ((extendScalars f).obj X)).inv ≫
        (extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).hom.app X := by
    simp only [extendScalarsCompRestrictScalarsIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.leftUnitor_inv_app,
      MonoidalCategory.leftUnitorNatIso_inv_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj, Category.id_comp]
  calc
    _ = ((restrictScalars f).map (λ_ ((extendScalars f).obj X)).inv ≫
          (extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).hom.app X) (s ⊗ₜ[A, f] x) :=
      congrArg (fun g ↦ g (s ⊗ₜ[A, f] x)) h
    _ = ((extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).hom.app X)
          (((restrictScalars f).map (λ_ ((extendScalars f).obj X)).inv) (s ⊗ₜ[A, f] x)) :=
      ModuleCat.comp_apply _ _ _
    _ = ((extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).hom.app X)
          (TensorProduct.tmul P (M := 𝟙_ (ModuleCat.{u} P)) (N := (extendScalars f).obj X)
            (1 : P) (s ⊗ₜ[A, f] x)) :=
      congrArg (((extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).hom.app X) ·)
        ((restrictScalars.map_apply f (λ_ ((extendScalars f).obj X)).inv (s ⊗ₜ[A, f] x)).trans
          (MonoidalCategory.leftUnitor_inv_apply (M := (extendScalars f).obj X) (s ⊗ₜ[A, f] x)))
    _ = TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X)
          (s • (1 : 𝟙_ (ModuleCat.{u} P))) x :=
      extendScalarsCompTensorLeftIso_hom_app_tmul f (𝟙_ (ModuleCat.{u} P)) X (1 : P) s x
    _ = TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X) s x :=
      congrArg (TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)))
        (N := X) · x) (mul_one s)

/-- The inverse of `extendScalarsCompRestrictScalarsIso` sends `s ⊗ x` to `s ⊗ x`. -/
@[simp]
theorem extendScalarsCompRestrictScalarsIso_inv_app_tmul (X : ModuleCat.{u} A)
    (s : (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (x : X) :
    (Hom.hom : ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X ⟶
        (restrictScalars f).obj ((extendScalars f).obj X)) → _)
        ((extendScalarsCompRestrictScalarsIso f).inv.app X)
        (TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X) s x) =
      (s : P) ⊗ₜ[A, f] x := by
  have h : ((extendScalarsCompRestrictScalarsIso f).inv.app X :
      (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X ⟶
        (restrictScalars f).obj ((extendScalars f).obj X)) =
      (extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).inv.app X ≫
        (restrictScalars f).map (λ_ ((extendScalars f).obj X)).hom := by
    simp only [extendScalarsCompRestrictScalarsIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Iso.symm_inv, Functor.leftUnitor_hom_app,
      MonoidalCategory.leftUnitorNatIso_hom_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj]
    exact Category.comp_id _
  exact (congrArg (fun g : (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X ⟶
        (restrictScalars f).obj ((extendScalars f).obj X) ↦
      g (TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X) s x))
      h).trans <|
    (ModuleCat.comp_apply _ _ _).trans <|
    (congrArg (((restrictScalars f).map (λ_ ((extendScalars f).obj X)).hom) ·)
      (extendScalarsCompTensorLeftIso_inv_app_tmul f (𝟙_ (ModuleCat.{u} P)) X s x)).trans <|
    (restrictScalars.map_apply f (λ_ ((extendScalars f).obj X)).hom _).trans <|
    (MonoidalCategory.leftUnitor_hom_apply (M := (extendScalars f).obj X) s
      ((1 : P) ⊗ₜ[A, f] x)).trans <|
    (ExtendScalars.smul_tmul f s (1 : P) x).trans <|
    congrArg (· ⊗ₜ[A, f] x) (mul_one _)

end ModuleCat
