/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Natural endomorphisms of a module-valued functor act on its values

For a functor `F : D ⥤ ModuleCat R`, the ring `End F` of natural endomorphisms of `F` acts on
every value `F.obj Y` by evaluating components: `η • y = η_Y y`. With this action `F` lifts to a
functor `F.toNatEndModule : D ⥤ ModuleCat (End F)`, since naturality says exactly that each
`F.map f` commutes with the action. The action extends that of `R`
(`CategoryTheory.Functor.natEndModule_isScalarTower`).

When `F` is a fibre functor restricted to a finite piece of a category, `End F` is the finite
algebra out of which the category is reconstructed, and `F.toNatEndModule` is the comparison
functor to its modules.

## Main definitions

* `CategoryTheory.Functor.natEndModule`: the action of `End F` on `F.obj Y`, as a `Module`
  structure for use as a local instance.
* `CategoryTheory.Functor.toNatEndModule`: the lift of `F` to modules over `End F`.
* `CategoryTheory.Functor.toNatEndModuleCompRestrictScalarsIso`: restricting scalars back to `R`
  recovers `F`.

## References

* P. Deligne, J. S. Milne, *Tannakian categories*, §2, the functor `⟨X⟩ → Mod(A_X)` before
  Lemma 2.13.
-/

public section

namespace CategoryTheory.Functor

universe w v u u'

variable {D : Type u} [Category.{v} D]

section Ring

variable {R : Type u'} [Ring R] (F : D ⥤ ModuleCat.{w} R)

/-- The natural endomorphisms of `F` act on each value `F.obj Y` through their components. This
`Module` structure is meant as a local instance. -/
abbrev natEndModule (Y : D) : Module (End F) (F.obj Y) :=
  Module.compHom (F.obj Y)
    { toFun η := (η.asHom.app Y).hom
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl : End F →+* Module.End R (F.obj Y) }

attribute [local instance] natEndModule

/-- A natural endomorphism acts on `F.obj Y` through its component at `Y`. -/
@[simp]
theorem natEndModule_smul {Y : D} (η : End F) (y : F.obj Y) :
    η • y = (η.asHom.app Y).hom y :=
  (rfl)

/-- The lift of `F` to modules over its ring of natural endomorphisms: `F.obj Y` with the action
of `End F` through components. Each `F.map f` is `End F`-linear by naturality. -/
@[expose] noncomputable def toNatEndModule : D ⥤ ModuleCat.{w} (End F) where
  obj Y := ModuleCat.of (End F) (F.obj Y)
  map {Y Y'} f := ModuleCat.ofHom
    { toFun := (F.map f).hom
      map_add' x y := _root_.map_add _ x y
      map_smul' η y := by
        simp only [natEndModule_smul, RingHom.id_apply]
        exact congrArg (fun φ ↦ φ.hom y) (η.asHom.naturality f).symm }

/-- The value of `F.toNatEndModule` at `Y` is `F.obj Y` with the action of `End F` through
components. -/
@[simp]
theorem toNatEndModule_obj (Y : D) : F.toNatEndModule.obj Y = ModuleCat.of (End F) (F.obj Y) :=
  (rfl)

/-- The `End F`-linear map underlying `F.toNatEndModule.map f` is `F.map f`. -/
@[simp]
theorem toNatEndModule_map_hom_apply {Y Y' : D} (f : Y ⟶ Y') (y : F.obj Y) :
    (F.toNatEndModule.map f).hom y = (F.map f).hom y :=
  (rfl)

/-- The lift of a faithful functor to modules over its natural endomorphisms is faithful. -/
instance [F.Faithful] : F.toNatEndModule.Faithful where
  map_injective h := F.map_injective (ModuleCat.hom_ext (LinearMap.ext fun y ↦ by
    have hy := congrArg (fun φ ↦ φ.hom y) h
    simp only [toNatEndModule_map_hom_apply] at hy
    exact hy))

end Ring

section CommRing

variable {R : Type u'} [CommRing R] (F : D ⥤ ModuleCat.{w} R)

attribute [local instance] natEndModule

/-- The action of natural endomorphisms extends the action of `R`. -/
instance natEndModule_isScalarTower (Y : D) : IsScalarTower R (End F) (F.obj Y) where
  smul_assoc c η y := by simp

/-- Restricting the action of `End F` on the values of `F.toNatEndModule` back to `R` recovers
`F`; the components are identities. -/
noncomputable def toNatEndModuleCompRestrictScalarsIso :
    F.toNatEndModule ⋙ ModuleCat.restrictScalars (algebraMap R (End F)) ≅ F :=
  NatIso.ofComponents (fun Y ↦ LinearEquiv.toModuleIso
    (@AddEquiv.toLinearEquiv _ _ _ _ _ _
      ((ModuleCat.restrictScalars (algebraMap R (End F))).obj (F.toNatEndModule.obj Y)).isModule _
      (.refl (F.obj Y)) fun c y ↦ algebraMap_smul (End F) (M := F.obj Y) c y)) fun _ ↦ rfl

/-- The components of `F.toNatEndModuleCompRestrictScalarsIso` are identities. -/
theorem toNatEndModuleCompRestrictScalarsIso_hom_app_hom_apply (Y : D) (y : F.obj Y) :
    (F.toNatEndModuleCompRestrictScalarsIso.hom.app Y).hom y = y :=
  (rfl)

/-- The inverse components of `F.toNatEndModuleCompRestrictScalarsIso` are identities. -/
theorem toNatEndModuleCompRestrictScalarsIso_inv_app_hom_apply (Y : D) (y : F.obj Y) :
    (F.toNatEndModuleCompRestrictScalarsIso.inv.app Y).hom y = y :=
  (rfl)

end CommRing

end CategoryTheory.Functor
