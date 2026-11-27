/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.FiberHomSheaf
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe

/-!
# Checks for the sheaves of fibre morphisms of band-preserving transformations

* The identity modification acts by the identity of the sheaf, and two modifications act by the
  composite of their sheaf maps.
* The sheaf assigned to `X` is Mathlib's sheaf of morphisms from `y` to `X_U x`.
* The inverse of the sheaf isomorphism of `m` is the action of the inverse modification, and the
  forward and inverse maps compose to the identity.
* With groupoid fibres, the sections of the sheaf assigned to `X` are isomorphisms, by Mathlib's
  `Groupoid.isoEquivHom`.
* For a gerbe, the sheaf assigned to `X` has sections locally, by `coversTop_presheafHom` and
  `IsGerbe.exists_covering_hom`.
-/

public section

namespace TauCeti.Examples.FiberHomSheaf

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open scoped Pseudofunctor.StrongTrans
open BandedMorphism

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat}
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}
  {U : C} (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))

/-- For a gerbe, the objects of `Over U` over which the sheaf assigned to `X` has a section cover
the slice site. -/
example [G.IsGerbe J] (X : HomCategory bF bG) :
    (J.over U).CoversTop fun T : {T : Over U //
      Nonempty ((G.presheafHom y ((X.obj.app (.mk (op U))).toFunctor.obj x)).obj (op T))} ↦
        T.val :=
  coversTop_presheafHom (IsGerbe.exists_covering_hom (J := J) y _)

variable [G.IsPrestack J]

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

/-- With groupoid fibres, a section of the sheaf assigned to `X` over `t : T ⟶ U` is the same as
an isomorphism `G(t) y ≅ G(t) (X_U x)`. -/
noncomputable example (X : HomCategory bF bG) (T : (Over U)ᵒᵖ) :
    (G.presheafHom y ((X.obj.app (.mk (op U))).toFunctor.obj x)).obj T ≃
      ((G.map T.unop.hom.op.toLoc).toFunctor.obj y ≅
        (G.map T.unop.hom.op.toLoc).toFunctor.obj ((X.obj.app (.mk (op U))).toFunctor.obj x)) :=
  letI := Groupoid.ofIsGroupoid (C := G.obj (.mk (op T.unop.left)))
  (Groupoid.isoEquivHom _ _).symm

end TauCeti.Examples.FiberHomSheaf
