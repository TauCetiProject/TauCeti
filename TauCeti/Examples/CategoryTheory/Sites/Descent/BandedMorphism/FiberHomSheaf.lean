/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.FiberHomSheaf

/-!
# Checks for the sheaves of fibre morphisms of band-preserving transformations

* The identity modification acts by the identity of the sheaf, and two modifications act by the
  composite of their sheaf maps.
* The sheaf assigned to `X` is Mathlib's sheaf of morphisms from `y` to `X_U x`.
* The inverse of the sheaf isomorphism of `m` is the action of the inverse modification, and the
  forward and inverse maps compose to the identity.
-/

public section

namespace TauCeti.Examples.FiberHomSheaf

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open scoped Pseudofunctor.StrongTrans
open BandedMorphism

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat}
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}
  [G.IsPrestack J] {U : C} (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))

/-- The identity modification acts by the identity of the sheaf. -/
example (X : HomCategory bF bG) :
    (fiberHomSheafFunctor bF bG J U x y).map (𝟙 X) = 𝟙 _ :=
  (fiberHomSheafFunctor bF bG J U x y).map_id X

/-- Two modifications act by the composite of their sheaf maps. -/
example {X Y Z : HomCategory bF bG} (m : X ⟶ Y) (n : Y ⟶ Z) :
    (fiberHomSheafFunctor bF bG J U x y).map (m ≫ n) =
      (fiberHomSheafFunctor bF bG J U x y).map m ≫ (fiberHomSheafFunctor bF bG J U x y).map n :=
  (fiberHomSheafFunctor bF bG J U x y).map_comp m n

/-- The sheaf assigned to `X` is the sheaf of morphisms from `y` to `X_U x`. -/
example (X : HomCategory bF bG) :
    (fiberHomSheafFunctor bF bG J U x y).obj X =
      G.sheafHom J y ((X.obj.app (.mk (op U))).toFunctor.obj x) :=
  fiberHomSheafFunctor_obj x y X

variable [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]

/-- The inverse sheaf map is the action of the inverse modification, and the forward and inverse
maps compose to the identity. -/
example {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (fiberHomSheafMapIso (J := J) x y m).inv =
        (fiberHomSheafFunctor bF bG J U x y).map (homIso m).inv ∧
      (fiberHomSheafFunctor bF bG J U x y).map m ≫
        (fiberHomSheafFunctor bF bG J U x y).map (homIso m).inv = 𝟙 _ := by
  refine ⟨fiberHomSheafMapIso_inv x y m, ?_⟩
  rw [← Functor.map_comp, hom_homIso_inv, CategoryTheory.Functor.map_id]

end TauCeti.Examples.FiberHomSheaf
