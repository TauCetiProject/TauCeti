/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Closed

/-!
# The simplicial category of pointed simplicial sets

The based mapping simplicial sets form the hom objects of a native `SimplicialCategory`
structure on `PointedSSet`. Composition is composition of the based families of maps,
and the ordinary morphisms identify with its vertices. The hom objects are the underlying
simplicial sets of the existing pointed internal hom, so its tensors and cotensors use
this same enrichment.

The construction restricts Mathlib's `SimplicialObject` enrichment, whose simplices are
`Functor.HomObj` families, to the subcomplex of families preserving the basepoint.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter I.
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace TauCeti.PointedSSet

/-- Based mapping simplicial sets, with composition of families, enrich pointed simplicial
sets over simplicial sets. -/
instance enrichedCategory : EnrichedCategory SSet.{u} PointedSSet.{u} where
  Hom X Y := (basedMaps X Y).toSSet
  id X :=
    { app n := ↾fun _ ↦ ⟨Functor.HomObj.ofNatTrans (𝟙 X.right),
        (mem_basedMaps_iff _).2 (by intros; rfl)⟩ }
  comp X Y Z :=
    { app n := ↾fun φ ↦ ⟨φ.1.1.comp φ.2.1, (mem_basedMaps_iff _).2 (by
        intro m f
        -- The internal-hom wrapper hides concrete composition from rewriting.
        change φ.2.1.app m f (φ.1.1.app m f (X.point m)) = Z.point m
        rw [basedMaps_app_point, basedMaps_app_point])⟩
      naturality n m f := by
        ext φ
        apply Subtype.ext
        rfl }
  id_comp X Y := by
    ext n φ
    apply Subtype.ext
    rfl
  comp_id X Y := by
    ext n φ
    apply Subtype.ext
    rfl
  assoc W X Y Z := by
    ext n φ
    apply Subtype.ext
    rfl

/-- The enrichment uses precisely the existing based mapping object. -/
lemma enrichedHom_eq (X Y : PointedSSet.{u}) :
    (X ⟶[SSet] Y) = ((PointedSSet.ihom X).obj Y).right := (rfl)

/-- Enriched composition is restriction of the ordinary composition of simplicial families. -/
@[reassoc (attr := simp)]
lemma eComp_basedMaps_ι (X Y Z : PointedSSet.{u}) :
    eComp SSet X Y Z ≫ (basedMaps X Z).ι =
      ((basedMaps X Y).ι ⊗ₘ (basedMaps Y Z).ι) ≫ eComp SSet X.right Y.right Z.right := (rfl)

/-- The identity family is the ordinary identity after forgetting basedness. -/
@[reassoc (attr := simp)]
lemma eId_basedMaps_ι (X : PointedSSet.{u}) :
    eId SSet X ≫ (basedMaps X X).ι = eId SSet X.right := (rfl)

/-- The enrichment has the original category of based maps as its underlying category. -/
instance simplicialCategory : SimplicialCategory PointedSSet.{u} where
  homEquiv {X Y} :=
    { toFun f :=
        { app n := ↾fun _ ↦ ⟨Functor.HomObj.ofNatTrans f.right,
            (mem_basedMaps_iff _).2 (by intro m g; exact app_point f m)⟩ }
      invFun φ := Under.homMk (Functor.natTransEquiv (φ ≫ (basedMaps X Y).ι)) (by
        ext n a
        have h := basedMaps_app_point (φ.app n PUnit.unit) (𝟙 n)
        rw [← hom_app X n a, ← hom_app Y n a] at h
        exact h)
      left_inv f := by
        apply Under.UnderMorphism.ext
        exact Functor.natTransEquiv.apply_symm_apply f.right
      right_inv φ := by
        apply (cancel_mono (basedMaps X Y).ι).1
        exact Functor.natTransEquiv.symm_apply_apply (φ ≫ (basedMaps X Y).ι) }
  homEquiv_id X := by rfl
  homEquiv_comp f g := by
    ext n a
    apply Subtype.ext
    rfl

variable {X Y Z : PointedSSet.{u}}

/-- The family associated with a based map is its ordinary underlying simplicial family. -/
@[reassoc (attr := simp)]
lemma eHomEquiv_basedMaps_ι (f : X ⟶ Y) :
    eHomEquiv SSet f ≫ (basedMaps X Y).ι = Functor.natTransEquiv.symm f.right := (rfl)

/-- Recovering a based map from a family recovers its underlying natural transformation. -/
@[simp]
lemma eHomEquiv_symm_right (φ : 𝟙_ SSet.{u} ⟶ (X ⟶[SSet] Y)) :
    ((eHomEquiv SSet).symm φ).right =
      Functor.natTransEquiv (φ ≫ (basedMaps X Y).ι) := (rfl)

/-- Enriched postcomposition agrees with postcomposition in the pointed internal hom. -/
@[simp]
lemma eHomWhiskerLeft_eq (X : PointedSSet.{u}) (g : Y ⟶ Z) :
    eHomWhiskerLeft SSet X g = ((PointedSSet.ihom X).map g).right := (rfl)

/-- Enriched precomposition evaluates a family on the image of each simplex. This is not a
`simp` lemma: `eHomWhiskerRight_eq` rewrites precomposition to the pointed internal hom. -/
lemma eHomWhiskerRight_app_coe_app_apply (f : X ⟶ Y) (Z : PointedSSet.{u})
    {n m : SimplexCategoryᵒᵖ} (φ : (Y ⟶[SSet] Z).obj n) (g : n ⟶ m)
    (x : X.right.obj m) :
    dsimp% ((eHomWhiskerRight SSet f Z).app n φ : (basedMaps X Z).obj n).1.app m g x =
      (φ : (basedMaps Y Z).obj n).1.app m g (f.right.app m x) := (rfl)

/-- Enriched precomposition agrees with precomposition in the pointed internal hom. -/
@[simp]
lemma eHomWhiskerRight_eq (f : X ⟶ Y) (Z : PointedSSet.{u}) :
    eHomWhiskerRight SSet f Z = ((MonoidalClosed.pre f).app Z).right := by
  rw [← MonoidalClosed.curry_uncurry ((MonoidalClosed.pre f).app Z),
    MonoidalClosed.uncurry_pre]
  ext n φ
  apply ihom_obj_right_ext
  intro m g x
  refine (eHomWhiskerRight_app_coe_app_apply f Z φ g x).trans ?_
  symm
  refine (curry_right_app_coe_app_apply
    (f ▷ (ihom Y).obj Z ≫ (ihom.ev Y).app Z) φ g x).trans ?_
  simp only [comp_right_app_apply, whiskerRight_app_smashMk, ihom_ev_app_right_app_smashMk]
  simpa using ihom_obj_right_map_coe_app_apply g φ (𝟙 m) (f.right.app m x)

end TauCeti.PointedSSet
