/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Functorial pullback of finite locally free sheaves

Pulling back a finite locally free sheaf along the identity is naturally isomorphic to the
original sheaf. Pullback along a composite is naturally isomorphic to successive pullback. These
comparisons are the restrictions of the corresponding comparisons for all modules on a scheme.
They are comparison data needed for base-change naturality of the vector-bundle equivalence.

The construction follows the full-subcategory comparisons for invertible sheaves in
`TauCeti/AlgebraicGeometry/LineBundle/Functoriality.lean`; finite local freeness replaces
invertibility throughout.
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocallyFreeSheaf

variable {X Y Z : Scheme.{u}}

/-- Pullback along the identity is naturally isomorphic to the identity functor on finite locally
free sheaves. -/
def pullbackId (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (FiniteLocallyFreeSheaf X) :=
  NatIso.ofComponents (fun E ↦
    ObjectProperty.isoMk (Scheme.Modules.isFiniteLocallyFree X)
      ((eqToIso (pullback_obj_obj (𝟙 X) E)) ≪≫
        (Scheme.Modules.pullbackId X).app E.obj)) (by
    intro E F φ
    apply ObjectProperty.hom_ext
    simp [ObjectProperty.isoMk, ObjectProperty.homMk, pullback_map_hom,
      Category.assoc, (Scheme.Modules.pullbackId X).hom.naturality φ.hom])

/-- On underlying modules, the identity comparison is Mathlib's pullback identity comparison. -/
@[simp]
theorem pullbackId_app_hom_hom (X : Scheme.{u}) (E : FiniteLocallyFreeSheaf X) :
    ((pullbackId X).hom.app E).hom =
      eqToHom (pullback_obj_obj (𝟙 X) E) ≫
        (Scheme.Modules.pullbackId X).hom.app E.obj := by
  simp only [pullbackId, NatIso.ofComponents_hom_app, ObjectProperty.isoMk_hom,
    Iso.trans_hom, eqToIso.hom, ObjectProperty.homMk_hom, Iso.app_hom]

/-- The inverse identity comparison on underlying modules is Mathlib's inverse comparison. -/
@[simp]
theorem pullbackId_inv_app_hom (X : Scheme.{u}) (E : FiniteLocallyFreeSheaf X) :
    ((pullbackId X).inv.app E).hom =
      (Scheme.Modules.pullbackId X).inv.app E.obj ≫
        eqToHom (pullback_obj_obj (𝟙 X) E).symm := by
  simp only [pullbackId, NatIso.ofComponents_inv_app, ObjectProperty.isoMk_inv,
    Iso.trans_inv, eqToIso.inv, ObjectProperty.homMk_hom, Iso.app_inv]

private lemma pullbackComp_obj_obj (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : FiniteLocallyFreeSheaf Z) :
    ((pullback g ⋙ pullback f).obj E).obj =
      (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj E.obj :=
  (pullback_obj_obj f ((pullback g).obj E)).trans
    (congrArg (Scheme.Modules.pullback f).obj (pullback_obj_obj g E))

/-- Pullback along a composite is naturally isomorphic to successive pullback of finite locally
free sheaves. -/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents (fun E ↦
    ObjectProperty.isoMk (Scheme.Modules.isFiniteLocallyFree X)
      ((eqToIso (pullbackComp_obj_obj f g E)) ≪≫
        (Scheme.Modules.pullbackComp f g).app E.obj ≪≫
        eqToIso (pullback_obj_obj (f ≫ g) E).symm)) (by
    intro E F φ
    apply ObjectProperty.hom_ext
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.isoMk_hom,
      Iso.trans_hom, eqToIso.hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
      pullback_map_hom, Functor.map_comp, Category.assoc, ObjectProperty.homMk_hom,
      eqToHom_trans_assoc, eqToHom_refl, eqToHom_map, eqToHom_trans,
      Category.id_comp]
    -- Regroup the composites so module-pullback naturality applies inside the transports.
    have h := (Scheme.Modules.pullbackComp f g).hom.naturality φ.hom
    simp only [Functor.comp_map] at h
    calc
      _ = eqToHom (pullbackComp_obj_obj f g E) ≫
          ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ.hom) ≫
            (Scheme.Modules.pullbackComp f g).hom.app F.obj) ≫
          eqToHom (pullback_obj_obj (f ≫ g) F).symm := by simp only [Category.assoc]
      _ = _ := by rw [h]; simp only [Category.assoc])

/-- On underlying modules, the composition comparison is Mathlib's pullback composition
comparison. -/
@[simp]
theorem pullbackComp_app_hom_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : FiniteLocallyFreeSheaf Z) :
    ((pullbackComp f g).hom.app E).hom =
      eqToHom (by simp only [Functor.comp_obj, pullback_obj_obj]) ≫
        (Scheme.Modules.pullbackComp f g).hom.app E.obj ≫
        eqToHom (pullback_obj_obj (f ≫ g) E).symm := by
  simp only [pullbackComp, NatIso.ofComponents_hom_app, ObjectProperty.isoMk_hom,
    Iso.trans_hom, eqToIso.hom, ObjectProperty.homMk_hom, Iso.app_hom]

/-- The inverse composition comparison on underlying modules is Mathlib's inverse comparison. -/
@[simp]
theorem pullbackComp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : FiniteLocallyFreeSheaf Z) :
    ((pullbackComp f g).inv.app E).hom =
      eqToHom (pullback_obj_obj (f ≫ g) E) ≫
        (Scheme.Modules.pullbackComp f g).inv.app E.obj ≫
        -- Reconstruct this equality because the comparison lemma above is private.
        eqToHom (show (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj E.obj =
          ((pullback g ⋙ pullback f).obj E).obj by
            simp only [Functor.comp_obj, pullback_obj_obj]) := by
  simp only [pullbackComp, NatIso.ofComponents_inv_app, ObjectProperty.isoMk_inv,
    Iso.trans_inv, eqToIso.inv, ObjectProperty.homMk_hom, Iso.app_inv,
    Category.assoc]

end FiniteLocallyFreeSheaf

end

end AlgebraicGeometry

end TauCeti
