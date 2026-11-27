/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.FiberHomBaseChange

/-!
# Checks for the base change of the fibre morphism sheaves

* The forward comparison followed by its inverse recovers every section, over every `t : T ⟶ V`.
* The identity coefficient acts trivially before the comparison.
* The comparison commutes with restriction along every arrow of `Over V`.
* The inverse of a modification, and the composite of two modifications, satisfy the naturality
  square of the comparison.
-/

public section

namespace TauCeti.Examples.FiberHomBaseChange

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open scoped Pseudofunctor.StrongTrans
open BandedMorphism

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat}
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}
  [G.IsPrestack J] {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))

/-- The forward comparison followed by its inverse recovers every section. -/
example (X : HomCategory bF bG) (T : (Over V)ᵒᵖ)
    (p : ((J.overMapPullback (Type _) f).obj ((fiberHomSheafFunctor bF bG J U x y).obj X)).obj.obj
      T) :
    (fiberHomBaseChangeIso f x y X).inv.hom.app T
      ((fiberHomBaseChangeIso f x y X).hom.hom.app T p) = p := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.hom_inv_id]
  rfl

/-- The identity coefficient acts trivially before the comparison. -/
example (X : HomCategory bF bG) (T : (Over V)ᵒᵖ)
    (p : (G.presheafHom y ((componentFunctor bF bG U x).obj X)).obj
      (op ((Over.map f).obj T.unop))) :
    (fiberHomBaseChangeIso f x y X).hom.hom.app T (bG.homAct p 1) =
      (fiberHomBaseChangeIso f x y X).hom.hom.app T p :=
  (fiberHomBaseChangeIso_equivariant f x y X T p 1).trans (bG.homAct_one _)

/-- The comparison commutes with restriction along every arrow `g` of `Over V`. -/
example (X : HomCategory bF bG) {T T' : (Over V)ᵒᵖ} (g : T ⟶ T')
    (p : ((J.overMapPullback (Type _) f).obj ((fiberHomSheafFunctor bF bG J U x y).obj X)).obj.obj
      T) :
    (fiberHomBaseChangeIso f x y X).hom.hom.app T'
        (((J.overMapPullback (Type _) f).obj ((fiberHomSheafFunctor bF bG J U x y).obj X)).obj.map
          g p) =
      ((fiberHomSheafFunctor bF bG J V _ _).obj X).obj.map g
        ((fiberHomBaseChangeIso f x y X).hom.hom.app T p) :=
  ConcreteCategory.congr_hom ((fiberHomBaseChangeIso f x y X).hom.hom.naturality g) p

variable [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]

/-- The inverse of a modification satisfies the naturality square of the comparison. -/
example {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (J.overMapPullback (Type _) f).map ((fiberHomSheafFunctor bF bG J U x y).map (homIso m).inv) ≫
        (fiberHomBaseChangeIso f x y X).hom =
      (fiberHomBaseChangeIso f x y Y).hom ≫
        (fiberHomSheafFunctor bF bG J V _ _).map (homIso m).inv :=
  fiberHomBaseChangeIso_modification f x y _

/-- Two composable modifications satisfy the naturality square of the comparison. -/
example {X Y Z : HomCategory bF bG} (m : X ⟶ Y) (n : Y ⟶ Z) :
    (J.overMapPullback (Type _) f).map ((fiberHomSheafFunctor bF bG J U x y).map (m ≫ n)) ≫
        (fiberHomBaseChangeIso f x y Z).hom =
      (fiberHomBaseChangeIso f x y X).hom ≫
        (fiberHomSheafFunctor bF bG J V _ _).map m ≫
          (fiberHomSheafFunctor bF bG J V _ _).map n := by
  rw [fiberHomBaseChangeIso_modification, Functor.map_comp]

end TauCeti.Examples.FiberHomBaseChange
