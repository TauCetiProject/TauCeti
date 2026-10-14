/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor

/-!
# Pullback of quasicoherent algebras

A quasicoherent commutative algebra on a scheme can be viewed as a commutative monoid object in
the symmetric monoidal category of quasicoherent sheaves. This description makes pullback of
algebras functorial: the strong symmetric monoidal pullback of quasicoherent sheaves carries
commutative monoid objects to commutative monoid objects.

This is the algebraic side of base change for relative spectra. The characteristic equations in
this file identify the carrier, unit, multiplication, and morphisms of an algebra pullback with
the already established pullback of the underlying quasicoherent sheaves and its monoidal
comparisons.

The construction is Mathlib's `CategoryTheory.Functor.mapCommMon`, which carries commutative
monoid objects along a lax braided functor, applied to the strong symmetric monoidal structure
on `TauCeti.AlgebraicGeometry.QuasicoherentSheaf.pullback`.

The main declaration is `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.pullback`, pullback of
quasicoherent algebras along a morphism of schemes.
-/

public section

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

attribute [local instance] monoidalCategorySheafOfModules

/-- The symmetry of modules on a scheme, stated for the unfolded sheaf category used by the
quasicoherent full subcategory. -/
local instance pullbackAlgebraSymmetricCategorySheafOfModules :
    SymmetricCategory (_root_.SheafOfModules X.ringCatSheaf) :=
  _root_.AlgebraicGeometry.Scheme.Modules.instSymmetricCategory X

namespace QuasicoherentAlgebra

private def toCommMon : QuasicoherentAlgebra X ⥤ CommMon (QuasicoherentSheaf X) where
  obj A := by
    let E : QuasicoherentSheaf X := ⟨A.obj.X, A.property⟩
    letI : MonObj E := {
      one := ObjectProperty.homMk η[A.obj.X]
      mul := ObjectProperty.homMk μ[A.obj.X]
      one_mul := by
        apply ObjectProperty.hom_ext
        exact MonObj.one_mul A.obj.X
      mul_one := by
        apply ObjectProperty.hom_ext
        exact MonObj.mul_one A.obj.X
      mul_assoc := by
        apply ObjectProperty.hom_ext
        exact MonObj.mul_assoc A.obj.X
    }
    letI : IsCommMonObj E := {
      mul_comm := by
        apply ObjectProperty.hom_ext
        exact IsCommMonObj.mul_comm (X := A.obj.X)
    }
    exact CommMon.mk E
  map {A B} f := by
    refine CommMon.homMk (Mon.Hom.mk' (ObjectProperty.homMk f.hom.hom.hom) ?_ ?_)
    · apply ObjectProperty.hom_ext
      exact IsMonHom.one_hom f.hom.hom.hom
    · apply ObjectProperty.hom_ext
      exact IsMonHom.mul_hom f.hom.hom.hom
  map_id A := by
    apply CommMon.hom_ext
    apply ObjectProperty.hom_ext
    exact CategoryTheory.CommMon.id_hom A.obj
  map_comp f g := by
    apply CommMon.hom_ext
    apply ObjectProperty.hom_ext
    exact CategoryTheory.CommMon.comp_hom f.hom g.hom

private def ofCommMon : CommMon (QuasicoherentSheaf X) ⥤ QuasicoherentAlgebra X where
  obj A := by
    let E : X.Modules := A.X.obj
    letI : MonObj E := {
      one := η[A.X].hom
      mul := μ[A.X].hom
      one_mul := congrArg (fun f ↦ f.hom) (MonObj.one_mul A.X)
      mul_one := congrArg (fun f ↦ f.hom) (MonObj.mul_one A.X)
      mul_assoc := congrArg (fun f ↦ f.hom) (MonObj.mul_assoc A.X)
    }
    letI : IsCommMonObj E := {
      mul_comm := congrArg (fun f ↦ f.hom) (IsCommMonObj.mul_comm (X := A.X))
    }
    exact ⟨CommMon.mk E, A.X.property⟩
  map f := by
    refine ObjectProperty.homMk (CommMon.homMk (Mon.Hom.mk' f.hom.hom.hom ?_ ?_))
    · exact congrArg (fun g ↦ g.hom) (IsMonHom.one_hom f.hom.hom)
    · exact congrArg (fun g ↦ g.hom) (IsMonHom.mul_hom f.hom.hom)
  map_id A := by
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    exact congrArg (fun f ↦ f.hom) (CommMon.id_hom A)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    exact congrArg (fun h ↦ h.hom) (CommMon.comp_hom f g)

end QuasicoherentAlgebra

namespace QuasicoherentAlgebra

variable {X}

/-- Pullback of quasicoherent commutative algebras along a morphism of schemes. -/
def pullback {Y : Scheme.{u}} (f : Y ⟶ X) :
    QuasicoherentAlgebra X ⥤ QuasicoherentAlgebra Y :=
  toCommMon X ⋙
    (QuasicoherentSheaf.pullback f).mapCommMon ⋙
      ofCommMon Y

/-- The carrier of a pulled-back algebra is the pullback of its underlying module. -/
@[simp]
theorem pullback_obj_X {Y : Scheme.{u}} (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    ((pullback f).obj A).obj.X = (Scheme.Modules.pullback f).obj A.obj.X :=
  by
    unfold pullback ofCommMon toCommMon
    exact QuasicoherentSheaf.pullback_obj_obj f _

/-- The unit of a pulled-back algebra is the pullback of its unit, preceded by the
identification of the pulled-back structure sheaf. -/
@[simp]
theorem pullback_obj_one {Y : Scheme.{u}} (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    η[((pullback f).obj A).obj.X] =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map η[A.obj.X] ≫
        eqToHom (pullback_obj_X f A).symm := by
  unfold pullback ofCommMon toCommMon
  change (Functor.LaxMonoidal.ε (QuasicoherentSheaf.pullback f)).hom ≫
    ((QuasicoherentSheaf.pullback f).map _).hom = _
  rw [QuasicoherentSheaf.pullback_ε_hom, QuasicoherentSheaf.pullback_map_hom]
  -- `simp` cannot normalize the mixture of `X.Modules` and underlying sheaf instances.
  refine (Category.assoc (obj := Y.Modules) _ _ _).trans ?_
  refine congrArg ((Scheme.Modules.pullbackObjUnitIso f).inv ≫ ·) ?_
  refine (eqToHom_trans_assoc (C := Y.Modules) _ _ _).trans ?_
  exact Category.id_comp (obj := Y.Modules) _

/-- The multiplication of a pulled-back algebra is the pullback of its multiplication,
preceded by the inverse tensor comparison of module pullback. -/
@[simp]
theorem pullback_obj_mul {Y : Scheme.{u}} (f : Y ⟶ X) (A : QuasicoherentAlgebra X) :
    μ[((pullback f).obj A).obj.X] =
      (eqToHom (pullback_obj_X f A) ⊗ₘ eqToHom (pullback_obj_X f A)) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) ≫
          (Scheme.Modules.pullback f).map μ[A.obj.X] ≫ eqToHom (pullback_obj_X f A).symm := by
  unfold pullback ofCommMon toCommMon
  change (Functor.LaxMonoidal.μ (QuasicoherentSheaf.pullback f) _ _).hom ≫
    ((QuasicoherentSheaf.pullback f).map _).hom = _
  rw [QuasicoherentSheaf.pullback_μ_hom, QuasicoherentSheaf.pullback_map_hom]
  simp only [Scheme.Modules.pullbackToModules_δ]
  -- `simp` cannot normalize the mixture of `X.Modules` and underlying sheaf instances.
  refine (Category.assoc (obj := Y.Modules) _ _ _).trans ?_
  refine congrArg ((eqToHom (pullback_obj_X f A) ⊗ₘ eqToHom (pullback_obj_X f A)) ≫ ·) ?_
  refine (Category.assoc (obj := Y.Modules) _ _ _).trans ?_
  refine congrArg
    (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) ≫ ·) ?_
  refine (eqToHom_trans_assoc (C := Y.Modules) _ _ _).trans ?_
  exact Category.id_comp (obj := Y.Modules) _

/-- Pullback of algebra morphisms has the underlying map given by pullback of module
morphisms, transported along the canonical carrier identifications. -/
@[simp]
theorem pullback_map_hom_hom_hom {Y : Scheme.{u}} (f : Y ⟶ X)
    {A B : QuasicoherentAlgebra X} (g : A ⟶ B) :
    ((pullback f).map g).hom.hom.hom =
      eqToHom (pullback_obj_X f A) ≫ (Scheme.Modules.pullback f).map g.hom.hom.hom ≫
        eqToHom (pullback_obj_X f B).symm := by
  unfold pullback ofCommMon toCommMon
  exact QuasicoherentSheaf.pullback_map_hom f _

end QuasicoherentAlgebra

end

end TauCeti.AlgebraicGeometry
