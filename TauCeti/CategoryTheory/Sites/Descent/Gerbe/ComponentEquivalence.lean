/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.HomSheaf
public import TauCeti.CategoryTheory.Sites.Descent.Gerbe.ObjectDescent
public import TauCeti.CategoryTheory.Sites.Descent.RelativeGerbe

/-!
# Band-preserving morphisms of gerbes are equivalences on fibres

Let `η : F ⟶ G` be a strong transformation of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` whose
components `η_U` are fully faithful. This file finishes the descent of objects begun in
`TauCeti.CategoryTheory.Sites.Descent.Gerbe.ObjectDescent`, and with it the proof that a
band-preserving morphism of gerbes is an equivalence on every fibre (Olsson, Lemma 31.3).

For a family `f_i : X_i ⟶ U`, an object `z` of `G` over `U` and local preimages
`e_i : η_(X_i)(x_i) ≅ G(f_i) z`, the lifted overlaps `F(a) x_i ≅ F(b) x_j` are the gluing
isomorphisms of a descent datum for `F` with objects `x_i`
(`GerbeMorphismDescent.liftedDescentData`); in particular they are compatible with pullback along
deeper base arrows (`GerbeMorphismDescent.liftedOverlapIso_pullHom`). An object `y` over `U` with
an isomorphism `r` from its canonical descent datum to this lifted datum has image `η_U y` whose
restrictions are identified with those of `z` (`GerbeMorphismDescent.imageLocalIso`), compatibly
with the gluing isomorphisms of both (`GerbeMorphismDescent.imageLocalIso_comm`). When the family
covers `U` and `G` is a prestack, these glue to an isomorphism `η_U y ≅ z`
(`GerbeMorphismDescent.globalImageIso`), the unique one with these restrictions.

If moreover `F` is a stack and `η` is locally essentially surjective, the local preimages exist
on the covering local-image sieve of `z` (`StrongTrans.localImageSieve_mem`) and the lifted datum
is effective, so every `z` has a global preimage (`GerbeMorphismDescent.global_preimage`). Hence
every component `η_U` is essentially surjective and an equivalence
(`GerbeMorphismDescent.componentEssSurj`, `GerbeMorphismDescent.componentIsEquivalence`). For a
band-preserving morphism of gerbes all hypotheses hold (`BandedMorphism.fullyFaithful`,
`StrongTrans.isLocallyEssSurj_of_isGerbe`), so its components are equivalences
(`BandedMorphism.isEquivalence`).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.GerbeMorphismDescent`:

* `liftedDescentData`, `liftedOverlapIso_pullHom`;
* `imageDescentIso`, `imageLocalIso`, `imageLocalIso_hom`, `imageLocalIso_inv`,
  `imageLocalIso_comm`;
* `globalImageIso`, `map_globalImageIso_hom`, `map_globalImageIso_inv`, `eq_globalImageIso`;
* `global_preimage`, `componentEssSurj`, `componentIsEquivalence`.

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`: `essSurj`, `isEquivalence`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Lemma 31.3
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.GerbeMorphismDescent

open LocallyDiscreteOpToCat

section Lift

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (η : StrongTrans F G) {U : C} {ι : Type*} {X : ι → C} (f : ∀ i, X i ⟶ U)
  {x : ∀ i, F.obj (.mk (op (X i)))} (z : G.obj (.mk (op U)))
  (e : ∀ i, (η.app (.mk (op (X i)))).toFunctor.obj (x i) ≅ ((G.toDescentData f).obj z).obj i)
  (hη : ∀ V : C, (η.app (.mk (op V))).toFunctor.FullyFaithful)

/-- The **lifted descent datum**: the descent datum for `F` along `f` with objects the local
preimages `x_i` and gluing isomorphisms the lifted overlaps (`liftedOverlapIso`). It is the lift
(`StrongTrans.liftDescentData`) of the canonical descent datum of `z` along `e`. Its body is
exposed so that its objects are the `x_i` by definition. -/
@[expose]
noncomputable def liftedDescentData : F.DescentData f :=
  η.liftDescentData f hη ((G.toDescentData f).obj z) e

/-- The lifted descent datum is `StrongTrans.liftDescentData` of the canonical descent datum
of `z`. -/
theorem liftedDescentData_def :
    liftedDescentData η f z e hη = η.liftDescentData f hη ((G.toDescentData f).obj z) e :=
  (rfl)

/-- The objects of the lifted descent datum are the local preimages `x_i`. -/
@[simp]
theorem liftedDescentData_obj (i : ι) : (liftedDescentData η f z e hη).obj i = x i :=
  (rfl)

/-- The gluing morphisms of the lifted descent datum are the forward arrows of the lifted
overlaps. -/
@[simp]
theorem liftedDescentData_hom {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (liftedDescentData η f z e hη).hom q a b ha hb =
      (liftedOverlapIso η f z e hη q a b ha hb).hom := by
  rw [liftedOverlapIso_def]
  rfl

/-- **Lifted overlaps are compatible with pullback.** For `g : Y' ⟶ Y`, the pullback along `g`
of the lifted overlap at `q`, `a`, `b` is the lifted overlap at `g ≫ q`, `g ≫ a`, `g ≫ b`. -/
theorem liftedOverlapIso_pullHom {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U)
    (hq : g ≫ q = q') {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ f i = q)
    (hb : b ≫ f j = q) (ga : Y' ⟶ X i) (gb : Y' ⟶ X j) (hga : g ≫ a = ga) (hgb : g ≫ b = gb) :
    pullHom (liftedOverlapIso η f z e hη q a b ha hb).hom g ga gb hga hgb =
      (liftedOverlapIso η f z e hη q' ga gb (by rw [← hga, Category.assoc, ha, hq])
        (by rw [← hgb, Category.assoc, hb, hq])).hom := by
  rw [← liftedDescentData_hom, ← liftedDescentData_hom]
  exact (liftedDescentData η f z e hη).pullHom_hom g q q' hq a b ha hb ga gb hga hgb

/-- The image under `η` of the lifted descent datum is isomorphic to the canonical descent datum
of `z`, through the local preimages `e` (`StrongTrans.mapDescentDataLiftDescentDataIso`). -/
noncomputable def mapLiftedDescentDataIso :
    (η.mapDescentData f).obj (liftedDescentData η f z e hη) ≅ (G.toDescentData f).obj z :=
  η.mapDescentDataLiftDescentDataIso f hη _ e

/-- The components of `mapLiftedDescentDataIso` are the local preimages `e_i`. -/
@[simp]
theorem mapLiftedDescentDataIso_hom_hom (i : ι) :
    (mapLiftedDescentDataIso η f z e hη).hom.hom i = (e i).hom :=
  η.mapDescentDataLiftDescentDataIso_hom_hom f hη _ e i

/-- The components of the inverse of `mapLiftedDescentDataIso` are the inverses of the local
preimages `e_i`. -/
@[simp]
theorem mapLiftedDescentDataIso_inv_hom (i : ι) :
    (mapLiftedDescentDataIso η f z e hη).inv.hom i = (e i).inv :=
  η.mapDescentDataLiftDescentDataIso_inv_hom f hη _ e i

variable {f z e hη} (y : F.obj (.mk (op U)))
  (r : (F.toDescentData f).obj y ≅ liftedDescentData η f z e hη)

/-- The isomorphism of descent data for `G` between the canonical descent data of `η_U y` and of
`z`, induced by an isomorphism `r` from the canonical descent datum of `y` to the lifted descent
datum: through the naturality isomorphisms of `η`, the image of `r` under `η` and the local
preimages `e`. -/
noncomputable def imageDescentIso :
    (G.toDescentData f).obj ((η.app (.mk (op U))).toFunctor.obj y) ≅
      (G.toDescentData f).obj z :=
  ((η.toDescentDataCompMapDescentDataIso f).app y).symm ≪≫ (η.mapDescentData f).mapIso r ≪≫
    mapLiftedDescentDataIso η f z e hη

/-- The **local image isomorphism** `G(f_i)(η_U y) ≅ G(f_i) z` on the chart `i`: the inverse
naturality isomorphism `c_(f_i)(y)⁻¹`, then the image under `η_(X_i)` of the component of `r`,
then the local preimage `e_i`. -/
noncomputable def imageLocalIso (i : ι) :
    (G.map (f i).op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y) ≅
      (G.map (f i).op.toLoc).toFunctor.obj z :=
  DescentData.isoApp (imageDescentIso η y r) i

/-- The forward arrow of the local image isomorphism is `c_(f_i)(y)⁻¹`, then `η_(X_i)` of the
component of `r`, then `e_i`. -/
theorem imageLocalIso_hom (i : ι) :
    (imageLocalIso η y r i).hom =
      (η.naturalityObjIso (f i).op.toLoc y).inv ≫
        (η.app (.mk (op (X i)))).toFunctor.map (r.hom.hom i) ≫ (e i).hom := by
  simp [imageLocalIso, imageDescentIso]
  rfl

/-- The inverse arrow of the local image isomorphism is `e_i⁻¹`, then `η_(X_i)` of the inverse
component of `r`, then `c_(f_i)(y)`. -/
theorem imageLocalIso_inv (i : ι) :
    (imageLocalIso η y r i).inv =
      (e i).inv ≫ (η.app (.mk (op (X i)))).toFunctor.map (r.inv.hom i) ≫
        (η.naturalityObjIso (f i).op.toLoc y).hom := by
  simp only [imageLocalIso, imageDescentIso, DescentData.isoApp_trans, DescentData.isoApp_symm,
    Iso.trans_inv, DescentData.isoApp_inv, mapLiftedDescentDataIso_inv_hom, Functor.mapIso_inv,
    Iso.symm_inv, DescentData.isoApp_hom, Iso.app_hom,
    StrongTrans.toDescentDataCompMapDescentDataIso_hom_app_hom, StrongTrans.naturalityObjIso_hom]
  exact Category.assoc _ _ _

/-- The local image isomorphisms commute with the gluing isomorphisms of the canonical descent
data of `η_U y` and of `z` on every common refinement: the `comm` equation of
`DescentData.isoMk`. -/
@[reassoc]
theorem imageLocalIso_comm {Y : C} (q : Y ⟶ U) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (G.map a.op.toLoc).toFunctor.map (imageLocalIso η y r i).hom ≫
        ((G.toDescentData f).obj z).hom q a b ha hb =
      ((G.toDescentData f).obj ((η.app (.mk (op U))).toFunctor.obj y)).hom q a b ha hb ≫
        (G.map b.op.toLoc).toFunctor.map (imageLocalIso η y r j).hom :=
  DescentData.isoApp_hom_comm (imageDescentIso η y r) q a b ha hb

variable {J : GrothendieckTopology C} [G.IsPrestack J] (hf : Sieve.ofArrows X f ∈ J U)

/-- The **global image isomorphism** `η_U y ≅ z`: when the family `f` covers `U` and `G` is a
prestack, the local image isomorphisms glue. -/
noncomputable def globalImageIso : (η.app (.mk (op U))).toFunctor.obj y ≅ z :=
  (G.fullyFaithfulToDescentData f hf).preimageIso (imageDescentIso η y r)

/-- The restriction of the global image isomorphism to the chart `i` is the local image
isomorphism. -/
@[simp]
theorem map_globalImageIso_hom (i : ι) :
    (G.map (f i).op.toLoc).toFunctor.map (globalImageIso η y r hf).hom =
      (imageLocalIso η y r i).hom := by
  have := congrArg (fun φ ↦ DescentData.Hom.hom φ i)
    ((G.fullyFaithfulToDescentData f hf).map_preimage (imageDescentIso η y r).hom)
  rw [imageLocalIso, DescentData.isoApp_hom]
  exact this

/-- The restriction of the inverse of the global image isomorphism to the chart `i` is the
inverse of the local image isomorphism. -/
@[simp]
theorem map_globalImageIso_inv (i : ι) :
    (G.map (f i).op.toLoc).toFunctor.map (globalImageIso η y r hf).inv =
      (imageLocalIso η y r i).inv := by
  have := congrArg (fun φ ↦ DescentData.Hom.hom φ i)
    ((G.fullyFaithfulToDescentData f hf).map_preimage (imageDescentIso η y r).inv)
  rw [imageLocalIso, DescentData.isoApp_inv]
  exact this

/-- **Uniqueness of the global image isomorphism.** An isomorphism `η_U y ≅ z` whose restrictions
to the charts are the local image isomorphisms is the global image isomorphism. -/
theorem eq_globalImageIso (p : (η.app (.mk (op U))).toFunctor.obj y ≅ z)
    (hp : ∀ i, (G.map (f i).op.toLoc).toFunctor.map p.hom = (imageLocalIso η y r i).hom) :
    p = globalImageIso η y r hf := by
  ext
  refine (G.fullyFaithfulToDescentData f hf).map_injective ?_
  ext i
  exact (hp i).trans (map_globalImageIso_hom η y r hf i).symm

end Lift

section Preimage

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (J : GrothendieckTopology C) [F.IsStack J] [G.IsPrestack J] (η : StrongTrans F G)
  [η.IsLocallyEssSurj J] (hη : ∀ V : C, (η.app (.mk (op V))).toFunctor.FullyFaithful)

include J hη in
/-- **Global preimages.** If `F` is a stack, `G` a prestack and `η` is locally essentially
surjective with fully faithful components, every object `z` of `G` over `U` is isomorphic to the
image `η_U y` of an object of `F` over `U`: the lifted descent datum on the local-image sieve of
`z` is effective. -/
theorem global_preimage {U : C} (z : G.obj (.mk (op U))) :
    ∃ y : F.obj (.mk (op U)), Nonempty ((η.app (.mk (op U))).toFunctor.obj y ≅ z) := by
  let R := η.localImageSieve z
  have hR : R ∈ J U := η.localImageSieve_mem J z
  choose x e using fun g : R.arrows.category ↦
    (η.mem_localImageSieve_iff z g.obj.hom).1 g.property
  have hf : Sieve.ofArrows _ (fun g : R.arrows.category ↦ g.obj.hom) ∈ J U := by
    rwa [Sieve.ofArrows_category]
  have := IsStack.essSurj_of_sieve F R hR
  let D := liftedDescentData η (fun g : R.arrows.category ↦ g.obj.hom) z
    (fun g ↦ (e g).some) hη
  exact ⟨_, ⟨globalImageIso η _ ((F.toDescentData _).objObjPreimageIso D) hf⟩⟩

include J hη in
/-- The components of a locally essentially surjective transformation with fully faithful
components, from a stack to a prestack, are essentially surjective. -/
theorem componentEssSurj (U : C) : (η.app (.mk (op U))).toFunctor.EssSurj where
  mem_essImage z := global_preimage J η hη z

include J hη in
/-- The components of a locally essentially surjective transformation with fully faithful
components, from a stack to a prestack, are equivalences of categories. -/
theorem componentIsEquivalence (U : C) : (η.app (.mk (op U))).toFunctor.IsEquivalence :=
  have := (hη U).full
  have := (hη U).faithful
  have := componentEssSurj J η hη U
  { }

end Preimage

end CategoryTheory.Pseudofunctor.GerbeMorphismDescent

namespace CategoryTheory.Pseudofunctor.BandedMorphism

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}} (bF : F.AbelianBanding J A)
  (bG : G.AbelianBanding J A) (η : StrongTrans F G) [BandPreserving bF bG η]
  [F.IsGerbe J] [G.IsGerbe J]

include bF bG in
/-- The component functors of a band-preserving morphism of gerbes are essentially surjective
(Olsson, Lemma 31.3). -/
theorem essSurj (U : C) : (η.app (.mk (op U))).toFunctor.EssSurj :=
  GerbeMorphismDescent.componentEssSurj J η (fullyFaithful bF bG η) U

include bF bG in
/-- **Band-preserving morphisms of gerbes are equivalences on fibres.** The component functors of
a band-preserving morphism of gerbes are equivalences of categories (Olsson, Lemma 31.3). -/
theorem isEquivalence (U : C) : (η.app (.mk (op U))).toFunctor.IsEquivalence :=
  GerbeMorphismDescent.componentIsEquivalence J η (fullyFaithful bF bG η) U

end CategoryTheory.Pseudofunctor.BandedMorphism
