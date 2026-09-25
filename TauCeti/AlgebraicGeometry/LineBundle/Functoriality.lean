/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.Class

/-!
# Functorial pullback of line bundles

Pulling back an invertible sheaf along an identity morphism leaves it unchanged, and pullback
along a composite agrees with successive pullback. These comparisons make the pullback operation
on isomorphism classes of line bundles contravariantly functorial. This is the functoriality
needed to form the relative Picard functor from line-bundle classes on base changes.

The comparisons are restrictions of Mathlib's `Scheme.Modules.pullbackId` and
`Scheme.Modules.pullbackComp`.
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X Y Z : Scheme.{u}}

/-- Pullback of a line bundle along the identity morphism is naturally isomorphic to the
original line bundle. -/
def pullbackId (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (InvertibleSheaf X) :=
  NatIso.ofComponents (fun L ↦
    ObjectProperty.isoMk (SheafOfModules.isInvertible X)
      ((eqToIso (pullback_obj_obj (𝟙 X) L)) ≪≫
        (Scheme.Modules.pullbackId X).app L.obj)) (by
    intro L K f
    apply ObjectProperty.hom_ext
    simp [ObjectProperty.isoMk, ObjectProperty.homMk, pullback_map,
      Category.assoc, (Scheme.Modules.pullbackId X).hom.naturality f.hom])

/-- The underlying module of successive line-bundle pullbacks is the corresponding successive
module pullback. -/
lemma pullbackComp_obj_obj (f : X ⟶ Y) (g : Y ⟶ Z) (L : InvertibleSheaf Z) :
    ((pullback g ⋙ pullback f).obj L).obj =
      (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj L.obj :=
  (pullback_obj_obj f ((pullback g).obj L)).trans
    (congrArg (Scheme.Modules.pullback f).obj (pullback_obj_obj g L))

/-- Pullback along a composite is naturally isomorphic to successive pullback of line
bundles. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents (fun L ↦
    ObjectProperty.isoMk (SheafOfModules.isInvertible X)
      ((eqToIso (pullbackComp_obj_obj f g L)) ≪≫
        (Scheme.Modules.pullbackComp f g).app L.obj ≪≫
        eqToIso (pullback_obj_obj (f ≫ g) L).symm)) (by
    intro L K φ
    apply ObjectProperty.hom_ext
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.isoMk_hom,
      Iso.trans_hom, eqToIso.hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
      pullback_map, Functor.map_comp, Category.assoc, ObjectProperty.homMk_hom,
      eqToHom_trans_assoc, eqToHom_refl, eqToHom_map, eqToHom_trans,
      Category.id_comp]
    -- The outer transports are shared; regroup inside them to apply module-pullback naturality.
    conv_lhs =>
      enter [2]
      rw [← Category.assoc]
    have h := (Scheme.Modules.pullbackComp f g).hom.naturality φ.hom
    simp only [Functor.comp_map] at h
    rw [h]
    simp only [Category.assoc])

end InvertibleSheaf

namespace LineBundleClass

variable {X Y Z : Scheme.{u}}

/-- Pullback of an isomorphism class of line bundles along a scheme morphism. -/
def pullback (f : X ⟶ Y) (a : LineBundleClass Y) : LineBundleClass X :=
  lift (fun L ↦ mk ((InvertibleSheaf.pullback f).obj L)) (fun _ _ ⟨e⟩ ↦
    mk_eq_mk_iff.mpr ⟨(SheafOfModules.isInvertible X).ι.mapIso
      ((InvertibleSheaf.pullback f).mapIso
        (ObjectProperty.isoMk (SheafOfModules.isInvertible Y) e))⟩) a

/-- Pulling back the class of `L` gives the class of its pulled-back line bundle. -/
@[simp]
lemma pullback_mk (f : X ⟶ Y) (L : InvertibleSheaf Y) :
    pullback f (mk L) = mk ((InvertibleSheaf.pullback f).obj L) :=
  lift_mk L

/-- Pullback by the identity acts identically on line-bundle classes. -/
@[simp]
lemma pullback_id (a : LineBundleClass X) : pullback (𝟙 X) a = a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk]
  exact mk_eq_mk_iff.mpr ⟨(SheafOfModules.isInvertible X).ι.mapIso
    ((InvertibleSheaf.pullbackId X).app L)⟩

/-- Pullback of line-bundle classes is contravariantly functorial under composition. -/
@[simp]
lemma pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a : LineBundleClass Z) :
    pullback f (pullback g a) = pullback (f ≫ g) a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  simp only [pullback_mk]
  exact mk_eq_mk_iff.mpr ⟨(SheafOfModules.isInvertible X).ι.mapIso
    ((InvertibleSheaf.pullbackComp f g).app L)⟩

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
