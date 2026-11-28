/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.FiberHomTransport

/-!
# Checks for sections of the fibre morphism sheaves as transported isomorphisms

* The transported isomorphism of a section and its stated inverse recover the section, and every
  isomorphism `G(t) y ≅ X_T (F(t) x)` is recovered from its preimage.
* The inverse is postcomposition by the inverse restriction comparison, followed by `hom`.
* The transported image of a section under the identity modification is its transported
  isomorphism, and under a modification it is followed by the component of the modification at
  the restricted source object.
-/

public section

namespace TauCeti.Examples.FiberHomTransport

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open scoped Pseudofunctor.StrongTrans
open BandedMorphism

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat}
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}
  [G.IsPrestack J] [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]
  {U : C} (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))

/-- A section is recovered from its transported isomorphism. -/
example (X : HomCategory bF bG) (T : Over U)
    (p : ((fiberHomSheafFunctor bF bG J U x y).obj X).obj.obj (op T)) :
    (fiberHomTransportIsoEquiv x y X T).symm (fiberHomTransportIsoEquiv x y X T p) = p :=
  (fiberHomTransportIsoEquiv x y X T).symm_apply_apply p

/-- An isomorphism `G(t) y ≅ X_T (F(t) x)` is recovered from its section. -/
example (X : HomCategory bF bG) (T : Over U)
    (q : (G.map T.hom.op.toLoc).toFunctor.obj y ≅
      (X.obj.app (.mk (op T.left))).toFunctor.obj ((F.map T.hom.op.toLoc).toFunctor.obj x)) :
    fiberHomTransportIsoEquiv x y X T ((fiberHomTransportIsoEquiv x y X T).symm q) = q :=
  (fiberHomTransportIsoEquiv x y X T).apply_symm_apply q

/-- The inverse is postcomposition by the inverse restriction comparison, followed by `hom`. -/
example (X : HomCategory bF bG) (T : Over U)
    (q : (G.map T.hom.op.toLoc).toFunctor.obj y ≅
      (X.obj.app (.mk (op T.left))).toFunctor.obj ((F.map T.hom.op.toLoc).toFunctor.obj x)) :
    (fiberHomTransportIsoEquiv x y X T).symm q =
      (q ≪≫ (restrictionIso T.hom X.obj x).symm).hom :=
  fiberHomTransportIsoEquiv_symm_apply x y X T q

/-- Under a modification, the transported isomorphism is followed by the component of the
modification at `F(t) x`. -/
example {X Y : HomCategory bF bG} (m : X ⟶ Y) (T : Over U)
    (p : ((fiberHomSheafFunctor bF bG J U x y).obj X).obj.obj (op T)) :
    (fiberHomTransportIsoEquiv x y Y T
        (((fiberHomSheafFunctor bF bG J U x y).map m).hom.app _ p)).hom =
      (fiberHomTransportIsoEquiv x y X T p).hom ≫
        (m.hom.as.app (.mk (op T.left))).toNatTrans.app
          ((F.map T.hom.op.toLoc).toFunctor.obj x) := by
  rw [fiberHomTransportIsoEquiv_modification, Iso.trans_hom, componentIso_hom]

/-- The identity modification does not change transported isomorphisms. -/
example (X : HomCategory bF bG) (T : Over U)
    (p : ((fiberHomSheafFunctor bF bG J U x y).obj X).obj.obj (op T)) :
    fiberHomTransportIsoEquiv x y X T
        (((fiberHomSheafFunctor bF bG J U x y).map (𝟙 X)).hom.app _ p) =
      fiberHomTransportIsoEquiv x y X T p := by
  rw [fiberHomTransportIsoEquiv_modification, componentIso_id, Iso.trans_refl]

end TauCeti.Examples.FiberHomTransport
