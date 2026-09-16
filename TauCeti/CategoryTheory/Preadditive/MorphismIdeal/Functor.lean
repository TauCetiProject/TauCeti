/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic

/-!
# Functoriality of quotients by morphism ideals

An additive functor `F : C ⥤ D` pulls a morphism ideal of `D` back to one of `C`. Consequently,
if `F` carries an ideal `I` into an ideal `J`, it induces an additive functor `C/I ⥤ D/J`.
Natural transformations descend to these quotient functors, and the construction respects
identities and composition.

This is the functorial part of the universal property of an additive quotient. In particular, it
is the mechanism by which an additive functor preserving projective-injective objects will induce
a functor between stable categories.

## Main definitions

* `TauCeti.MorphismIdeal.comap`: the inverse image of a morphism ideal under an additive functor.
* `TauCeti.MorphismIdeal.map`: the functor induced between quotient categories.
* `TauCeti.MorphismIdeal.mapNatTrans`: the natural transformation induced between quotient
  functors.

## Main results

* `TauCeti.MorphismIdeal.map_id` and `TauCeti.MorphismIdeal.map_comp`: quotient functors preserve
  identities and composition.
* `TauCeti.MorphismIdeal.mapNatTrans_id` and
  `TauCeti.MorphismIdeal.mapNatTrans_comp`: descent of natural transformations preserves
  identities and vertical composition.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995),
  Chapter IV, Section 1.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, LMS Lecture Note Series 119, CUP (1988), Section I.2.
-/

public section

universe v u v' u' v'' u''

namespace TauCeti

open CategoryTheory

namespace MorphismIdeal

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable {E : Type u''} [Category.{v''} E] [Preadditive E]

/-! ### Pullback of ideals -/

/-- The inverse image of a morphism ideal under an additive functor. A morphism belongs to
`J.comap F` precisely when its image under `F` belongs to `J`. -/
def comap (J : MorphismIdeal D) (F : C ⥤ D) [F.Additive] : MorphismIdeal C where
  hom X Y := J.hom (F.obj X) (F.obj Y) |>.comap F.mapAddHom
  comp_mem_left := by
    intro X Y Z f g hg
    rw [AddSubgroup.mem_comap, Functor.coe_mapAddHom, F.map_comp]
    exact J.comp_mem_left (F.map f) hg
  comp_mem_right := by
    intro X Y Z f g hf
    rw [AddSubgroup.mem_comap, Functor.coe_mapAddHom, F.map_comp]
    exact J.comp_mem_right (F.map g) hf

@[simp]
theorem mem_comap_hom (J : MorphismIdeal D) (F : C ⥤ D) [F.Additive] {X Y : C}
    {f : X ⟶ Y} : f ∈ (J.comap F).hom X Y ↔ F.map f ∈ J.hom (F.obj X) (F.obj Y) :=
  Iff.rfl

/-- Pullback of ideals is monotone. -/
theorem comap_mono (F : C ⥤ D) [F.Additive] {J J' : MorphismIdeal D} (h : J ≤ J') :
    J.comap F ≤ J'.comap F := by
  intro X Y f hf
  change F.map f ∈ J.hom (F.obj X) (F.obj Y) at hf
  change F.map f ∈ J'.hom (F.obj X) (F.obj Y)
  exact (le_def.1 h) (F.map f) hf

@[simp]
theorem comap_id (I : MorphismIdeal C) : I.comap (𝟭 C) = I := by
  ext
  simp

@[simp]
theorem comap_comp (K : MorphismIdeal E) (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] : K.comap (F ⋙ G) = (K.comap G).comap F := by
  ext
  simp

/-- If `F` carries `I` into `J` and `G` carries `J` into `K`, then `F ⋙ G` carries `I` into
`K`. -/
theorem le_comap_comp (I : MorphismIdeal C) (J : MorphismIdeal D) (K : MorphismIdeal E)
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (hF : I ≤ J.comap F) (hG : J ≤ K.comap G) : I ≤ K.comap (F ⋙ G) := by
  intro X Y f hf
  exact (le_def.1 hG) (F.map f) ((le_def.1 hF) f hf)

/-! ### Functors between quotients -/

/-- An additive functor carrying `I` into `J` induces a functor from `C/I` to `D/J`. -/
noncomputable abbrev map (I : MorphismIdeal C) (J : MorphismIdeal D) (F : C ⥤ D) [F.Additive]
    (hF : I ≤ J.comap F) : I.Quotient ⥤ J.Quotient :=
  I.lift (F ⋙ J.quotientFunctor) <| by
    intro X Y f hf
    rw [CategoryTheory.Functor.mem_kerIdeal_hom, Functor.comp_map,
      J.quotientFunctor_map_eq_zero_iff]
    exact (le_def.1 hF) f hf

@[simp]
theorem quotientFunctor_comp_map (I : MorphismIdeal C) (J : MorphismIdeal D) (F : C ⥤ D)
    [F.Additive] (hF : I ≤ J.comap F) :
    I.quotientFunctor ⋙ I.map J F hF = F ⋙ J.quotientFunctor :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem map_obj_quotientFunctor_obj (I : MorphismIdeal C) (J : MorphismIdeal D) (F : C ⥤ D)
    [F.Additive] (hF : I ≤ J.comap F) (X : C) :
    (I.map J F hF).obj (I.quotientFunctor.obj X) = J.quotientFunctor.obj (F.obj X) :=
  rfl

@[simp]
theorem map_quotientFunctor_map (I : MorphismIdeal C) (J : MorphismIdeal D) (F : C ⥤ D)
    [F.Additive] (hF : I ≤ J.comap F) {X Y : C} (f : X ⟶ Y) :
    (I.map J F hF).map (I.quotientFunctor.map f) = J.quotientFunctor.map (F.map f) :=
  rfl

/-- The identity functor on a category induces the identity functor on every ideal quotient. -/
@[simp]
theorem map_id (I : MorphismIdeal C) :
    I.map I (𝟭 C) (by simp) = 𝟭 I.Quotient := by
  apply CategoryTheory.Quotient.lift_unique' I.rel
  rw [quotientFunctor_comp_map]
  rfl

/-- Compatible functors induce the composite of their functors on ideal quotients. -/
theorem map_comp (I : MorphismIdeal C) (J : MorphismIdeal D) (K : MorphismIdeal E)
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (hF : I ≤ J.comap F) (hG : J ≤ K.comap G) :
    I.map K (F ⋙ G) (I.le_comap_comp J K F G hF hG) =
      I.map J F hF ⋙ J.map K G hG := by
  apply CategoryTheory.Quotient.lift_unique' I.rel
  rw [quotientFunctor_comp_map]
  calc
    (F ⋙ G) ⋙ K.quotientFunctor = F ⋙ (G ⋙ K.quotientFunctor) :=
      rfl
    _ = F ⋙ (J.quotientFunctor ⋙ J.map K G hG) := by rw [quotientFunctor_comp_map]
    _ = (F ⋙ J.quotientFunctor) ⋙ J.map K G hG :=
      rfl
    _ = (I.quotientFunctor ⋙ I.map J F hF) ⋙ J.map K G hG := by
      rw [quotientFunctor_comp_map]
    _ = I.quotientFunctor ⋙ I.map J F hF ⋙ J.map K G hG :=
      rfl

/-! ### Natural transformations between quotient functors -/

/-- A natural transformation between ideal-preserving functors descends to their induced
functors on the quotients. -/
noncomputable def mapNatTrans (I : MorphismIdeal C) (J : MorphismIdeal D) {F G : C ⥤ D}
    [F.Additive] [G.Additive] (hF : I ≤ J.comap F) (hG : I ≤ J.comap G) (α : F ⟶ G) :
    I.map J F hF ⟶ I.map J G hG :=
  CategoryTheory.Quotient.natTransLift I.rel
    { app := fun X ↦ J.quotientFunctor.map (α.app X)
      naturality := by
        intro X Y f
        dsimp
        rw [← J.quotientFunctor.map_comp, ← J.quotientFunctor.map_comp, α.naturality] }

@[simp]
theorem mapNatTrans_app_quotientFunctor_obj (I : MorphismIdeal C) (J : MorphismIdeal D)
    {F G : C ⥤ D} [F.Additive] [G.Additive] (hF : I ≤ J.comap F) (hG : I ≤ J.comap G)
    (α : F ⟶ G) (X : C) :
    (I.mapNatTrans J hF hG α).app (I.quotientFunctor.obj X) =
      J.quotientFunctor.map (α.app X) :=
  by simp [mapNatTrans]

/-- Descent sends an identity natural transformation to an identity. -/
@[simp]
theorem mapNatTrans_id (I : MorphismIdeal C) (J : MorphismIdeal D) (F : C ⥤ D)
    [F.Additive] (hF : I ≤ J.comap F) :
    I.mapNatTrans J hF hF (𝟙 F) = 𝟙 (I.map J F hF) := by
  apply CategoryTheory.Quotient.natTrans_ext
  ext X
  simp

/-- Descent preserves vertical composition of natural transformations. -/
theorem mapNatTrans_comp (I : MorphismIdeal C) (J : MorphismIdeal D) {F G H : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive]
    (hF : I ≤ J.comap F) (hG : I ≤ J.comap G) (hH : I ≤ J.comap H)
    (α : F ⟶ G) (β : G ⟶ H) :
    I.mapNatTrans J hF hG α ≫ I.mapNatTrans J hG hH β =
      I.mapNatTrans J hF hH (α ≫ β) := by
  apply CategoryTheory.Quotient.natTrans_ext
  ext X
  simp

end MorphismIdeal

end TauCeti
