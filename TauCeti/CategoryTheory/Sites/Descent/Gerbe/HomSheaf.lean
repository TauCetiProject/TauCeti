/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.MorphismPullback
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Band-preserving morphisms of gerbes are isomorphisms on the sheaves of morphisms

Let `η : F ⟶ G` be a strong transformation of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. For
objects `x, y` over `U`, the transports `h_f` of `GerbeMorphismPullback.homMap` along the arrows
`f : V ⟶ U` form a morphism of presheaves on `C/U` from the presheaf of morphisms
`F.presheafHom x y` to `G.presheafHom (η_U x) (η_U y)` (`GerbeMorphismPullback.homPresheafMap`).
Its naturality is the compatibility `homMap_pullHom` of the transports with `pullHom`, which
follows from the composition law of the naturality isomorphisms of `η`
(`StrongTrans.naturalityObjIso_hom_comp'`). At the identity slice it is `η_U.map`
(`homPresheafMap_app_presheafHomObjHomEquiv`).

When `F` and `G` are prestacks this is a morphism of sheaves (`homSheafMap`). When moreover `F`
and `G` are gerbes banded by the same sheaf `A` and `η` preserves the bands, it is injective (the
fibres of `F` are groupoids) and locally surjective (local anchors exist by the gerbe condition),
so it is an isomorphism of sheaves (`isIso_homSheafMap`, `homSheafIso`). Evaluating at the
identity slice, `η_U.map : (x ⟶ y) → (η_U x ⟶ η_U y)` is bijective with no global anchor
(`BandedMorphism.map_bijective`), so every component functor of `η` is full (`BandedMorphism.full`)
(Olsson, Lemma 31.3).

## Main declarations

* `GerbeMorphismPullback.homMap_pullHom`, `GerbeMorphismPullback.homPresheafMap`,
  `GerbeMorphismPullback.homPresheafMap_app_presheafHomObjHomEquiv`,
  `GerbeMorphismPullback.homSheafMap`.
* `GerbeMorphismPullback.homPresheafMap_injective`,
  `GerbeMorphismPullback.homPresheafMap_imageSieve_mem`,
  `GerbeMorphismPullback.isIso_homSheafMap`, `GerbeMorphismPullback.homSheafIso`,
  `BandedMorphism.map_bijective`, `BandedMorphism.full`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Lemma 31.3
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

namespace GerbeMorphismPullback

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (η : StrongTrans F G) {U : C} {x y : F.obj (.mk (op U))}

/-- **Transport commutes with `pullHom`.** For a local morphism `p : F(f) x ⟶ F(f) y` and
`g : W ⟶ V` with `g ≫ f = fg`, transporting the pullback of `p` along `g` is pulling back the
transport of `p`. The morphism `p` need not come from `U`. -/
@[simp]
theorem homMap_pullHom {V W : C} (f : V ⟶ U)
    (p : (F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y)
    (g : W ⟶ V) (fg : W ⟶ U) (h : g ≫ f = fg) :
    homMap η fg (pullHom p g fg fg h h) = pullHom (homMap η f p) g fg fg h h := by
  have hfg : f.op.toLoc ≫ g.op.toLoc = fg.op.toLoc := by
    rw [← h, op_comp, Quiver.Hom.comp_toLoc]
  have e : ∀ {Z} (k : (η.app (.mk (op W))).toFunctor.obj
      ((F.map g.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj y)) ⟶ Z),
      (η.app (.mk (op W))).toFunctor.map
          ((F.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc hfg).inv.toNatTrans.app y) ≫
        (η.app (.mk (op W))).toFunctor.map
          ((F.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc hfg).hom.toNatTrans.app y) ≫ k = k := by
    intro Z k
    rw [← Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id,
      Category.id_comp]
  rw [homMap_def, Iso.inv_comp_eq, homMap_def,
    StrongTrans.naturalityObjIso_hom_comp' η _ _ _ hfg x,
    StrongTrans.naturalityObjIso_hom_comp' η _ _ _ hfg y]
  simp only [pullHom, Category.assoc, Functor.map_comp, e,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc, Iso.hom_inv_id_map_assoc,
    StrongTrans.naturalityObjIso_hom_naturality_assoc]

variable (x y) in
/-- **The map on presheaves of morphisms.** The transports `h_{T.hom}` form a morphism of
presheaves on `C/U` from `F.presheafHom x y` to `G.presheafHom (η_U x) (η_U y)`. -/
noncomputable def homPresheafMap :
    F.presheafHom x y ⟶
      G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
        ((η.app (.mk (op U))).toFunctor.obj y) where
  app T := ↾fun p ↦ homMap η T.unop.hom p
  naturality T₁ T₂ a := by
    ext p
    exact homMap_pullHom η T₁.unop.hom p a.unop.left T₂.unop.hom (Over.w a.unop)

@[simp]
theorem homPresheafMap_app (T : (Over U)ᵒᵖ) (p : (F.presheafHom x y).obj T) :
    dsimp% (homPresheafMap η x y).app T p = homMap η T.unop.hom p :=
  (rfl)

/-- **The identity slice.** At the identity slice `𝟙 U`, the map on presheaves of morphisms is
`η_U.map`, read through `presheafHomObjHomEquiv`. -/
theorem homPresheafMap_app_presheafHomObjHomEquiv (p : x ⟶ y) :
    (homPresheafMap η x y).app (op (Over.mk (𝟙 U))) (F.presheafHomObjHomEquiv p) =
      G.presheafHomObjHomEquiv ((η.app (.mk (op U))).toFunctor.map p) := by
  rw [presheafHomObjHomEquiv_eq_map, presheafHomObjHomEquiv_eq_map, homPresheafMap_app]
  exact homMap_restrict η (𝟙 U) p

/-- For the identity transformation, the map on presheaves of morphisms is the identity. -/
@[simp]
theorem homPresheafMap_id : homPresheafMap (StrongTrans.id F) x y = 𝟙 _ := by
  ext T p
  exact (homPresheafMap_app _ T p).trans (id_homMap _ p)

variable (J : GrothendieckTopology C)

/-- **The map on sheaves of morphisms** of prestacks: `homPresheafMap` as a morphism
`F.sheafHom J x y ⟶ G.sheafHom J (η_U x) (η_U y)` of sheaves on `J.over U`. -/
noncomputable def homSheafMap [F.IsPrestack J] [G.IsPrestack J] (x y : F.obj (.mk (op U))) :
    F.sheafHom J x y ⟶
      G.sheafHom J ((η.app (.mk (op U))).toFunctor.obj x)
        ((η.app (.mk (op U))).toFunctor.obj y) :=
  ObjectProperty.homMk (homPresheafMap η x y)

@[simp]
theorem homSheafMap_hom [F.IsPrestack J] [G.IsPrestack J] :
    (homSheafMap η J x y).hom = homPresheafMap η x y :=
  (rfl)

/-! ### Band-preserving morphisms of gerbes -/

variable {J} {A : Sheaf J AddCommGrpCat.{w}} (bF : F.AbelianBanding J A)
  (bG : G.AbelianBanding J A) [BandPreserving bF bG η]

include bF bG in
/-- **Injectivity.** For a band-preserving transformation whose source has groupoid fibres, every
component of the map on presheaves of morphisms is injective, with no anchor. -/
theorem homPresheafMap_injective [∀ V : C, IsGroupoid (F.obj (.mk (op V)))]
    (T : (Over U)ᵒᵖ) : Function.Injective ((homPresheafMap η x y).app T) := fun p q h ↦
  homMap_injective η T.unop.hom bF bG (by simpa using h)

include bF bG in
/-- **Local surjectivity.** For a band-preserving transformation from a gerbe to a pseudofunctor
with groupoid fibres, the image sieve of every section of the target presheaf of morphisms is
covering: local anchors exist by the gerbe condition. -/
theorem homPresheafMap_imageSieve_mem [F.IsGerbe J] [∀ V : C, IsGroupoid (G.obj (.mk (op V)))]
    (T : Over U) (s : (G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
      ((η.app (.mk (op U))).toFunctor.obj y)).obj (op T)) :
    Presheaf.imageSieve (homPresheafMap η x y) s ∈ J.over U T := by
  obtain ⟨R, hR, hiso⟩ := IsGerbe.exists_covering_iso (J := J)
    ((F.map T.hom.op.toLoc).toFunctor.obj x) ((F.map T.hom.op.toLoc).toFunctor.obj y)
  refine (J.over U).superset_covering ?_ (J.overEquiv_symm_mem_over T R hR)
  intro S a ha
  obtain ⟨e⟩ := hiso a.left ha
  have hS : T.hom.op.toLoc ≫ a.left.op.toLoc = S.hom.op.toLoc := by
    rw [← Over.w a, op_comp, Quiver.Hom.comp_toLoc]
  let c := Cat.Hom.toNatIso (F.mapComp' T.hom.op.toLoc a.left.op.toLoc S.hom.op.toLoc hS)
  obtain ⟨r, hr⟩ := homMap_surjective_of_anchor η S.hom bF bG (c.app x ≪≫ e ≪≫ (c.app y).symm)
    ((G.presheafHom _ _).map a.op s)
  exact ⟨r, (homPresheafMap_app η (op S) r).trans hr⟩

variable (J) [F.IsGerbe J] [G.IsGerbe J]

include bF bG in
/-- The map on sheaves of morphisms of a band-preserving morphism of gerbes is locally
injective. -/
theorem isLocallyInjective_homSheafMap (x y : F.obj (.mk (op U))) :
    Sheaf.IsLocallyInjective (homSheafMap η J x y) :=
  Presheaf.isLocallyInjective_of_injective _ _ (homPresheafMap_injective η bF bG)

include bF bG in
/-- The map on sheaves of morphisms of a band-preserving morphism of gerbes is locally
surjective. -/
theorem isLocallySurjective_homSheafMap (x y : F.obj (.mk (op U))) :
    Sheaf.IsLocallySurjective (homSheafMap η J x y) where
  imageSieve_mem s := homPresheafMap_imageSieve_mem η bF bG _ s

include bF bG in
/-- **The sheaves of morphisms are isomorphic.** For a band-preserving morphism of gerbes, the
map on sheaves of morphisms is an isomorphism (Olsson, Lemma 31.3). -/
theorem isIso_homSheafMap (x y : F.obj (.mk (op U))) : IsIso (homSheafMap η J x y) :=
  (Sheaf.isLocallyBijective_iff_isIso _).1
    ⟨isLocallyInjective_homSheafMap η J bF bG x y, isLocallySurjective_homSheafMap η J bF bG x y⟩

/-- **The isomorphism of sheaves of morphisms** `F.sheafHom J x y ≅ G.sheafHom J (η_U x) (η_U y)`
of a band-preserving morphism of gerbes, with forward map `homSheafMap`. -/
noncomputable def homSheafIso (x y : F.obj (.mk (op U))) :
    F.sheafHom J x y ≅
      G.sheafHom J ((η.app (.mk (op U))).toFunctor.obj x)
        ((η.app (.mk (op U))).toFunctor.obj y) :=
  have := isIso_homSheafMap η J bF bG x y
  asIso (homSheafMap η J x y)

@[simp]
theorem homSheafIso_hom (x y : F.obj (.mk (op U))) :
    (homSheafIso η J bF bG x y).hom = homSheafMap η J x y :=
  (rfl)

/-- **The inverse through an anchor.** Given a local anchor `p : F(f) x ≅ F(f) y` at a slice
`T` with structure arrow `f`, the inverse of the isomorphism of sheaves of morphisms sends `q.hom`
to the anchored preimage `preimageIso p q`. -/
theorem homSheafIso_inv_app (T : (Over U)ᵒᵖ)
    (p : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ≅ (F.map T.unop.hom.op.toLoc).toFunctor.obj y)
    (q : (G.map T.unop.hom.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) ≅
      (G.map T.unop.hom.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y)) :
    (homSheafIso η J bF bG x y).inv.hom.app T q.hom = (preimageIso η T.unop.hom bF bG p q).hom := by
  apply homPresheafMap_injective η bF bG T
  have h := Iso.inv_hom_id_app_apply
    ((sheafToPresheaf (J.over U) _).mapIso (homSheafIso η J bF bG x y)) T q.hom
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, ObjectProperty.ι_map, homSheafIso_hom,
    homSheafMap_hom] at h
  refine h.trans ?_
  rw [homPresheafMap_app, ← mapIso_hom, mapIso_preimageIso]

include bF bG in
/-- Every component of the map on presheaves of morphisms of a band-preserving morphism of gerbes
is bijective. -/
theorem homPresheafMap_bijective (T : (Over U)ᵒᵖ) :
    Function.Bijective ((homPresheafMap η x y).app T) := by
  have h := (((sheafToPresheaf (J.over U) _).mapIso (homSheafIso η J bF bG x y)).app T).isIso_hom
  simp only [Iso.app_hom, Functor.mapIso_hom, ObjectProperty.ι_map, homSheafIso_hom,
    homSheafMap_hom] at h
  exact (isIso_iff_bijective _).1 h

end GerbeMorphismPullback

namespace BandedMorphism

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}} (bF : F.AbelianBanding J A)
  (bG : G.AbelianBanding J A) (η : StrongTrans F G) [BandPreserving bF bG η]
  [F.IsGerbe J] [G.IsGerbe J]

include bF bG in
/-- **Fullness and faithfulness on fibres, with no anchor.** For a band-preserving morphism of
gerbes, `η_U.map : (x ⟶ y) → (η_U x ⟶ η_U y)` is bijective for all `x, y` over `U`. In particular
if there is no morphism `x ⟶ y` then there is no morphism `η_U x ⟶ η_U y`. -/
theorem map_bijective {U : C} (x y : F.obj (.mk (op U))) :
    Function.Bijective
      fun p : x ⟶ y ↦ (η.app (.mk (op U))).toFunctor.map p := by
  have h := (G.presheafHomObjHomEquiv.symm.bijective.comp
    (GerbeMorphismPullback.homPresheafMap_bijective η J bF bG (x := x) (y := y)
      (op (Over.mk (𝟙 U))))).comp F.presheafHomObjHomEquiv.bijective
  convert h using 1
  ext p
  exact ((congrArg G.presheafHomObjHomEquiv.symm
    (GerbeMorphismPullback.homPresheafMap_app_presheafHomObjHomEquiv η p)).trans
    (Equiv.symm_apply_apply _ _)).symm

include bF bG in
/-- **Fullness.** The component functors of a band-preserving morphism of gerbes are full
(Olsson, Lemma 31.3). -/
theorem full (U : C) : (η.app (.mk (op U))).toFunctor.Full where
  map_surjective {x y} := (map_bijective bF bG η x y).2

include bF bG in
/-- The component functors of a band-preserving morphism of gerbes are fully faithful. -/
noncomputable def fullyFaithful (U : C) : (η.app (.mk (op U))).toFunctor.FullyFaithful :=
  have := full bF bG η U
  have := faithful bF bG η (U := U)
  .ofFullyFaithful _

end BandedMorphism

end CategoryTheory.Pseudofunctor
