/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal natural automorphisms

Mathlib makes the bundled lax monoidal functors `LaxMonoidalFunctor C D` into a category whose
morphisms are the monoidal natural transformations, so for a lax monoidal functor `F` the group
`Aut (LaxMonoidalFunctor.of F)` is the group of monoidal natural automorphisms of `F`. This file
adds the injective group homomorphism `CategoryTheory.LaxMonoidalFunctor.forgetAut F` to the
group `Aut F` of all natural automorphisms of `F`. Its values are typed as automorphisms of `F`
itself rather than of `(LaxMonoidalFunctor.of F).toFunctor`, so their components compose with
other morphisms out of `F.obj X` without unfolding `LaxMonoidalFunctor.of`.

The group `Aut (LaxMonoidalFunctor.of (𝟭 C))` of monoidal natural automorphisms of the identity
functor of a monoidal category, often written `Aut_⊗(𝟭_C)`, is commutative, like Mathlib's
centre `CategoryTheory.CatCenter C` of all natural endomorphisms of `𝟭 C`. It is the group
acting on the pivotal structures of a rigid monoidal category.

Precomposition by a monoidal equivalence also identifies the categories of lax monoidal
functors and therefore their tensor-automorphism groups. The construction
`CategoryTheory.Equivalence.precomposeLaxMonoidalEquivalence` refines Mathlib’s
`CategoryTheory.Equivalence.congrLeft` to monoidal natural transformations.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.LaxMonoidalFunctor

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The underlying natural automorphism of a monoidal natural automorphism of a lax monoidal
functor `F`, as a group homomorphism `Aut (LaxMonoidalFunctor.of F) →* Aut F`. -/
def forgetAut (F : C ⥤ D) [F.LaxMonoidal] : Aut (LaxMonoidalFunctor.of F) →* Aut F where
  toFun u := Aut.of
    { hom := u.asIso.hom.hom
      inv := u.asIso.inv.hom
      hom_inv_id := congrArg Hom.hom u.asIso.hom_inv_id
      inv_hom_id := congrArg Hom.hom u.asIso.inv_hom_id }
  map_one' := rfl
  map_mul' _ _ := rfl

variable (F : C ⥤ D) [F.LaxMonoidal]

-- The right-hand sides below are typed through `(LaxMonoidalFunctor.of F).toFunctor`, which is
-- `F` only up to unfolding, so these are not `simp` lemmas: `forgetAut` is the normal form.

/-- The underlying natural transformation of `forgetAut F u` is that of `u`. -/
theorem forgetAut_apply_asIso_hom (u : Aut (LaxMonoidalFunctor.of F)) :
    (forgetAut F u).asIso.hom = u.asIso.hom.hom :=
  (rfl)

/-- The underlying natural transformation of the inverse of `forgetAut F u` is that of the
inverse of `u`. -/
theorem forgetAut_apply_asIso_inv (u : Aut (LaxMonoidalFunctor.of F)) :
    (forgetAut F u).asIso.inv = u.asIso.inv.hom :=
  (rfl)

/-- A monoidal natural automorphism is determined by its underlying natural automorphism. -/
theorem forgetAut_injective : Function.Injective (forgetAut F) := fun _ _ h ↦
  Aut.ext (Iso.ext (hom_ext (congrArg (fun w ↦ w.asIso.hom) h)))

/-- The underlying natural automorphism of a monoidal natural automorphism is monoidal. -/
instance isMonoidal_forgetAut_apply_asIso_hom (u : Aut (LaxMonoidalFunctor.of F)) :
    NatTrans.IsMonoidal (forgetAut F u).asIso.hom :=
  u.asIso.hom.isMonoidal

variable (C) in
/-- The monoidal natural automorphisms of the identity functor of a monoidal category commute. -/
instance : IsMulCommutative (Aut (LaxMonoidalFunctor.of (𝟭 C))) :=
  .of_comm fun u v ↦ Aut.ext (Iso.ext (hom_ext (NatTrans.id_comm v.asIso.hom.hom u.asIso.hom.hom)))

end CategoryTheory.LaxMonoidalFunctor

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- Precomposition by a lax monoidal functor, on bundled lax monoidal functors and
monoidal natural transformations. -/
def Functor.precomposeLaxMonoidal (F : C ⥤ D) [F.LaxMonoidal] :
    LaxMonoidalFunctor D E ⥤ LaxMonoidalFunctor C E where
  obj G := .of (F ⋙ G.toFunctor)
  map α := ⟨Functor.whiskerLeft F α.hom, NatTrans.IsMonoidal.whiskerLeft α.hom⟩

/-- Precomposition leaves the underlying functor equal to the ordinary composite. -/
@[simp]
theorem Functor.precomposeLaxMonoidal_obj_toFunctor (F : C ⥤ D) [F.LaxMonoidal]
    (G : LaxMonoidalFunctor D E) :
    ((F.precomposeLaxMonoidal).obj G).toFunctor = F ⋙ G.toFunctor :=
  (rfl)

/-- Precomposition acts on a monoidal natural transformation by ordinary left whiskering.
The two transformations are typed through propositionally identified functor objects. -/
@[simp]
theorem Functor.precomposeLaxMonoidal_map_hom_app (F : C ⥤ D) [F.LaxMonoidal]
    {G G' : LaxMonoidalFunctor D E} (α : G ⟶ G') (X : C) :
    HEq (((F.precomposeLaxMonoidal).map α).hom.app X) (α.hom.app (F.obj X)) :=
  (HEq.rfl)

/-- A monoidal equivalence identifies a lax monoidal functor with its round-trip
precomposition. This is the monoidal version of the inverse of `Equivalence.invFunIdAssoc`. -/
noncomputable def Equivalence.laxMonoidalRoundTripIso (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]
    (F : LaxMonoidalFunctor D E) :
    F ≅ LaxMonoidalFunctor.of (e.inverse ⋙ (e.functor ⋙ F.toFunctor)) := by
  let i : F.toFunctor ≅ e.inverse ⋙ (e.functor ⋙ F.toFunctor) :=
    F.toFunctor.leftUnitor.symm ≪≫
      isoWhiskerRight e.counitIso.symm F.toFunctor ≪≫
      Functor.associator e.inverse e.functor F.toFunctor
  have : NatTrans.IsMonoidal e.counitIso.hom := inferInstanceAs (NatTrans.IsMonoidal e.counit)
  have : NatTrans.IsMonoidal e.counitIso.inv := inferInstance
  have : NatTrans.IsMonoidal i.hom := by
    dsimp only [i, Iso.trans_hom, Iso.symm_hom]
    have : NatTrans.IsMonoidal (isoWhiskerRight e.counitIso.symm F.toFunctor).hom := by
      rw [isoWhiskerRight_hom, Iso.symm_hom]
      infer_instance
    infer_instance
  exact @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _ i ‹NatTrans.IsMonoidal i.hom›

/-- The round-trip comparison is induced by the inverse counit of the equivalence. -/
@[simp]
theorem Equivalence.laxMonoidalRoundTripIso_hom_app (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]
    (F : LaxMonoidalFunctor D E) (X : D) :
    (e.laxMonoidalRoundTripIso F).hom.hom.app X = F.map (e.counitIso.inv.app X) := by
  dsimp [Equivalence.laxMonoidalRoundTripIso, LaxMonoidalFunctor.of,
    LaxMonoidalFunctor.isoMk, LaxMonoidalFunctor.homMk]
  simp

/-- Precomposition by a monoidal equivalence is an equivalence on lax monoidal functors.
The inverse precomposes by the inverse equivalence. -/
noncomputable def Equivalence.precomposeLaxMonoidalEquivalence (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    LaxMonoidalFunctor D E ≌ LaxMonoidalFunctor C E :=
  Equivalence.mk e.functor.precomposeLaxMonoidal e.inverse.precomposeLaxMonoidal
    (NatIso.ofComponents (fun F ↦ e.laxMonoidalRoundTripIso F)
      (fun f ↦ by
        ext X
        -- Unfold the bundled precomposition and its structural isomorphisms together:
        -- the underlying functor of `of` is only definitionally the original functor.
        dsimp [Functor.precomposeLaxMonoidal, Equivalence.laxMonoidalRoundTripIso,
          LaxMonoidalFunctor.of, LaxMonoidalFunctor.isoMk, LaxMonoidalFunctor.homMk]
        simpa only [Category.id_comp, Category.comp_id, Functor.id_obj, Functor.comp_obj] using
          (f.hom.naturality (e.counitIso.inv.app X)).symm))
    (NatIso.ofComponents (fun F ↦ (e.symm.laxMonoidalRoundTripIso F).symm)
      (fun f ↦ by
        ext X
        -- As for the unit, expose the bundled composite before applying naturality.
        dsimp [Functor.precomposeLaxMonoidal, Equivalence.laxMonoidalRoundTripIso,
          LaxMonoidalFunctor.of, LaxMonoidalFunctor.isoMk, LaxMonoidalFunctor.homMk]
        simpa only [Category.id_comp, Category.comp_id, Functor.id_obj, Functor.comp_obj] using
          (f.hom.naturality (e.unitIso.inv.app X)).symm))

/-- The forward functor of monoidal precomposition is precomposition by the given functor. -/
@[simp]
theorem Equivalence.precomposeLaxMonoidalEquivalence_functor (e : C ≌ D)
    [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    (e.precomposeLaxMonoidalEquivalence (E := E)).functor =
      e.functor.precomposeLaxMonoidal :=
  (rfl)

end CategoryTheory
