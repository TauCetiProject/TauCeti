/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.HomSheaf
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Sheaf

/-!
# Band-preserving morphisms are isomorphisms of the torsors of isomorphisms

Let `η : F ⟶ G` be a strong transformation of prestacks `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` with
groupoid fibres, preserving `A`-bandings `bF` and `bG`. For objects `x`, `y` over `U` that are
locally isomorphic, as any two objects of a gerbe are, the sheaf `Isom(x, y)` on `J.over U` is a
torsor under the restriction of `A` (`AbelianBanding.sheafHomTorsor`). So is
`Isom(η_U x, η_U y)`, and the map of sheaves of morphisms `GerbeMorphismPullback.homSheafMap` is
equivariant for these two torsor structures, because the transports `homMap` commute with the
action of the band (`GerbeMorphismPullback.homMap_homAct`). It is therefore a morphism of torsors,
and every morphism of torsors is an isomorphism, so it is an isomorphism of torsors
(`GerbeMorphismPullback.sheafHomTorsorIso`). This needs no global anchor, and of the gerbe
condition only the local isomorphy of `x` and `y`. For gerbes it is the equivariant form of the
isomorphism of sheaves of morphisms `GerbeMorphismPullback.homSheafIso` (Olsson, Lemma 31.3 and
Remark 31.5).

## Main declarations

* `GerbeMorphismPullback.sheafHomTorsorIso`: the isomorphism of torsors
  `Isom_F(x, y) ≅ Isom_G(η_U x, η_U y)`, with `sheafHomTorsorIso_hom_hom` and
  `sheafHomTorsorIso_id`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Lemma 31.3 and Remark 31.5
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.GerbeMorphismPullback

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{v'}} (bF : F.AbelianBanding J A)
  (bG : G.AbelianBanding J A) (η : StrongTrans F G) [BandPreserving bF bG η]
  [F.IsPrestack J] [G.IsPrestack J] [∀ V : C, IsGroupoid (F.obj (.mk (op V)))]
  [∀ V : C, IsGroupoid (G.obj (.mk (op V)))] {U : C} {x y : F.obj (.mk (op U))}

/-- **The isomorphism of torsors of isomorphisms.** For a band-preserving transformation `η` of
prestacks with groupoid fibres and locally isomorphic objects `x`, `y` over `U`, the map of
sheaves of morphisms `homSheafMap` is an isomorphism of torsors
`Isom_F(x, y) ≅ Isom_G(η_U x, η_U y)` under the restriction of `A` to `Over U`
(Olsson, Lemma 31.3). For gerbes, `IsGerbe.exists_covering_iso x y` supplies `h`. -/
noncomputable def sheafHomTorsorIso
    (h : ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)) :
    bF.sheafHomTorsor x y h ≅
      bG.sheafHomTorsor ((η.app (.mk (op U))).toFunctor.obj x)
        ((η.app (.mk (op U))).toFunctor.obj y) (exists_covering_iso_map η h) :=
  asIso
    { hom := homSheafMap η J x y
      map_smul T a p := by
        simp only [AbelianBanding.sheafHomTorsor_smul, homSheafMap_hom]
        exact (homPresheafMap_app η T _).trans ((homMap_homAct η T.unop.hom bF bG p _).trans
          (congrArg (bG.homAct · _) (homPresheafMap_app η T p).symm)) }

/-- The underlying morphism of sheaves of the isomorphism of torsors is `homSheafMap`. -/
@[simp]
theorem sheafHomTorsorIso_hom_hom
    (h : ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)) :
    (sheafHomTorsorIso bF bG η h).hom.hom = homSheafMap η J x y :=
  (rfl)

omit [G.IsPrestack J] [∀ V : C, IsGroupoid (G.obj (.mk (op V)))] in
/-- For the identity transformation, the isomorphism of torsors is the identity. -/
@[simp]
theorem sheafHomTorsorIso_id
    (h : ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      Nonempty ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)) :
    (sheafHomTorsorIso bF bF (StrongTrans.id F) h).hom = 𝟙 _ := by
  ext1
  apply ObjectProperty.hom_ext
  rw [sheafHomTorsorIso_hom_hom, homSheafMap_hom, homPresheafMap_id, Sheaf.Torsor.id_hom,
    ObjectProperty.FullSubcategory.id_hom]
  -- Both sides are the identity of `F.presheafHom x y`: the underlying sheaf of the torsor is
  -- `F.sheafHom J x y` (`sheafHomTorsor_sheaf`), which `rw` cannot use here because the source
  -- and target torsors appear in the type of the identity.
  rfl

end CategoryTheory.Pseudofunctor.GerbeMorphismPullback
