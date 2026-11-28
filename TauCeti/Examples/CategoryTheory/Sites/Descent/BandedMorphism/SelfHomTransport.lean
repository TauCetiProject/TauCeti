/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.SelfHomTransport

/-!
# Checks for the transport of self-morphism sheaves along isomorphisms of objects

* A modification commutes with the transports at its source and target, also for its inverse.
* Transport commutes with the action of the same band coefficient on both section carriers.
* The forward transport followed by its inverse recovers every section.
* Three composable isomorphisms satisfy the cocycle equation for the transport natural
  isomorphisms.
* The functor on the core of the fibre sends `x` to the fibre morphism sheaf functor at `x`.
-/

public section

namespace TauCeti.Examples.SelfHomTransport

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open scoped Pseudofunctor.StrongTrans
open BandedMorphism

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {b : F.AbelianBanding J A} [F.IsPrestack J] {U : C}
  {x x' x'' x''' : F.obj (.mk (op U))}

/-- A modification commutes with the two transports, as a square of sheaf morphisms. -/
example {X Y : HomCategory b b} (m : X ⟶ Y) (e : x ≅ x') :
    (fiberHomSheafFunctor b b J U x x).map m ≫ selfHomSheafTransport Y e =
      selfHomSheafTransport X e ≫ (fiberHomSheafFunctor b b J U x' x').map m :=
  selfHomSheafTransport_naturality m e

/-- The square also holds for the inverse of a modification, when the fibres are groupoids. -/
example [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] {X Y : HomCategory b b} (m : X ⟶ Y)
    (e : x ≅ x') :
    (fiberHomSheafFunctor b b J U x x).map (homIso m).inv ≫ selfHomSheafTransport X e =
      selfHomSheafTransport Y e ≫ (fiberHomSheafFunctor b b J U x' x').map (homIso m).inv :=
  selfHomSheafTransport_naturality _ e

/-- Transport commutes with the action of the same band coefficient on both carriers. -/
example (X : HomCategory b b) (e : x ≅ x') (T : (Over U)ᵒᵖ)
    (p : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ⟶
      (F.map T.unop.hom.op.toLoc).toFunctor.obj ((componentFunctor b b U x).obj X))
    (a : Multiplicative (A.obj.obj (op T.unop.left))) :
    (selfHomSheafTransport X e).hom.app T (b.homAct p a) =
      b.homAct ((selfHomSheafTransport X e).hom.app T p) a :=
  selfHomSheafTransport_equivariant X e T p a

/-- The forward transport followed by the transport along the inverse recovers every section. -/
example (X : HomCategory b b) (e : x ≅ x') :
    selfHomSheafTransport X e ≫ selfHomSheafTransport X e.symm = 𝟙 _ := by
  rw [← selfHomSheafTransportIso_inv, Iso.hom_inv_id]

/-- The cocycle equation for three composable isomorphisms. -/
example (e : x ≅ x') (f : x' ≅ x'') (g : x'' ≅ x''') :
    selfHomSheafTransportNatIso (b := b) (J := J) (e ≪≫ f ≪≫ g) =
      selfHomSheafTransportNatIso e ≪≫ selfHomSheafTransportNatIso f ≪≫
        selfHomSheafTransportNatIso g := by
  rw [selfHomSheafTransportNatIso_trans, selfHomSheafTransportNatIso_trans]

/-- The functor on the core sends `x` to the fibre morphism sheaf functor at `x`. -/
example (x : Core (F.obj (.mk (op U)))) :
    (selfHomSheafObjectFunctor b U).obj x = fiberHomSheafFunctor b b J U x.of x.of :=
  selfHomSheafObjectFunctor_obj x

end TauCeti.Examples.SelfHomTransport
