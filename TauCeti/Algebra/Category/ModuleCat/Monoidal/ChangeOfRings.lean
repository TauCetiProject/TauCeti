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
`A`-module `X` (`ModuleCat.extendScalarsCompTensorLeftIso`). This computes `Tor` over `A` by a
projective resolution over `P` after a flat extension of scalars. Specializing to
`M = 𝟙_ (ModuleCat P)` identifies extension followed by restriction of scalars with tensoring by
`P` over `A` (`ModuleCat.extendScalarsCompRestrictScalarsIso`).
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

/-- **Extension followed by restriction of scalars is tensoring with the target ring.** For
`f : A →+* P`, `extendScalars f ⋙ restrictScalars f` is naturally isomorphic to left tensoring
with `(restrictScalars f).obj (𝟙_ (ModuleCat P))`, sending `s ⊗ x` to `s ⊗ x`. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    extendScalars.{u, u, u} f ⋙ restrictScalars.{u} f ≅
      tensorLeft ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) :=
  Functor.isoWhiskerLeft (extendScalars f)
    ((Functor.leftUnitor (restrictScalars f)).symm ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso (ModuleCat.{u} P)).symm
        (restrictScalars f)) ≪≫
    extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))

/-- The forward map of `extendScalarsCompRestrictScalarsIso` sends `s ⊗ x` to `s ⊗ x`. -/
@[simp]
theorem extendScalarsCompRestrictScalarsIso_hom_app_tmul (X : ModuleCat.{u} A)
    (s : P) (x : X) :
    (Hom.hom : ((restrictScalars f).obj ((extendScalars f).obj X) ⟶
        (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X) → _)
        ((extendScalarsCompRestrictScalarsIso f).hom.app X) (s ⊗ₜ[A, f] x) =
      TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X)
        (show (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) from s) x :=
  congr_arg
    (fun t : P ↦
      TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X)
        (show (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) from t) x)
    (mul_one s)

/-- The inverse of `extendScalarsCompRestrictScalarsIso` sends `s ⊗ x` to `s ⊗ x`. -/
@[simp]
theorem extendScalarsCompRestrictScalarsIso_inv_app_tmul (X : ModuleCat.{u} A)
    (s : (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (x : X) :
    (Hom.hom : ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X ⟶
        (restrictScalars f).obj ((extendScalars f).obj X)) → _)
        ((extendScalarsCompRestrictScalarsIso f).inv.app X)
        (TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X) s x) =
      (show P from s) ⊗ₜ[A, f] x :=
  congr_arg (fun t : P ↦ t ⊗ₜ[A, f] x) (mul_one (show P from s))

end ModuleCat
