/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.StrongTrans
public import TauCeti.CategoryTheory.Sites.Descent.Stackification.StrongTrans

/-!
# Functoriality of the stackification of prestacks

A strong transformation `φ : F ⟶ G` of prestacks for a Grothendieck topology `J` on a category
with pullbacks induces a strong transformation `TauCeti.Stack.stackificationMap J φ` between the
pseudofunctors `stackification J F` and `stackification J G` of descent data along `w`-small
covering families. Its component at `U` maps a descent datum along a covering family of `U` to the
descent datum along the same family obtained by applying `φ`
(`Stackification.Obj.mapFunctor`, built from `Pseudofunctor.StrongTrans.mapDescentData`), and its
naturality isomorphisms (`TauCeti.Stack.stackificationMapNatIso`) compare the two ways of mapping
and pulling back. As for the pseudofunctor structure of the stackification, everything is
reduced to transports along pullback data: pullback data are mapped along `φ`
(`Stackification.Obj.PullbackData.map`), and mapping commutes with transport
(`Stackification.Obj.PullbackData.mapFunctor_map_transport`).

The construction is functorial: a modification `Γ : φ ⟶ φ'` induces a modification
`stackificationMap₂ J Γ`, compatibly with identities and composites
(`TauCeti.Stack.stackificationMapFunctor`), and `stackificationMap` preserves identities and
composites up to invertible modifications (`TauCeti.Stack.stackificationMapId`,
`TauCeti.Stack.stackificationMapComp`). The unit of the stackification is natural: for `F` and
`G` valued in the universes of their stackifications, `toStackification J F ≫ stackificationMap J φ`
and `φ ≫ toStackification J G` are isomorphic through an invertible modification
(`TauCeti.Stack.toStackificationCompStackificationMapIso`), whose components identify the descent
datum along the identity of `U` given by `M`, mapped along `φ`, with the descent datum given by
`φ M`. This naturality of the unit is a step towards the universal property of the
stackification among stacks (Stacks, Lemmas 02ZN and 0435), which is not proved here.

## Main declarations

* `TauCeti.Stack.stackificationMap`: the strong transformation induced by `φ : F ⟶ G`.
* `TauCeti.Stack.stackificationMap₂`, `TauCeti.Stack.stackificationMapFunctor`: the action on
  modifications.
* `TauCeti.Stack.stackificationMapId`, `TauCeti.Stack.stackificationMapComp`: compatibility with
  identities and composites.
* `TauCeti.Stack.toStackificationCompStackificationMapIso`: naturality of the unit.

## References

* [Stacks Project, Lemma 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Lemma 0435](https://stacks.math.columbia.edu/tag/0435)
-/

public section

noncomputable section

universe w v' u' v u

open CategoryTheory Limits Opposite Bicategory Pseudofunctor LocallyDiscreteOpToCat
  Pseudofunctor.StrongTrans

namespace TauCeti.Stack.Stackification.Obj

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [HasPullbacks C]

/-- A descent datum for `F` along a covering family, mapped along a strong transformation
`φ : F ⟶ G` to a descent datum for `G` along the same family. -/
abbrev mapObj (φ : F ⟶ G) {U : C} (A : Obj.{w} J F U) : Obj.{w} J G U :=
  ⟨A.ι, A.X, A.f, A.mem, (φ.mapDescentData A.f).obj A.D⟩

/-- A morphism of descent data, mapped along a strong transformation `φ`. -/
def Hom.map (φ : F ⟶ G) {U : C} {A B : Obj.{w} J F U} (ψ : Hom A B) :
    Hom (mapObj φ A) (mapObj φ B) where
  hom i j := φ.mapPullHom (ψ.hom i j)
  comm T i i' j j' a a' b b' w w' ha := by
    simp only [← mapPullHom_pullHom, ← mapPullHom_comp]
    rw [ψ.comm a a' b b' w w' ha]

/-- The local evaluations of a mapped morphism are the mapped local evaluations. -/
@[simp]
lemma Hom.app_map (φ : F ⟶ G) {U : C} {A B : Obj.{w} J F U} (ψ : Hom A B) ⦃T : C⦄
    ⦃i : A.ι⦄ ⦃j : B.ι⦄ (a : T ⟶ A.X i) (b : T ⟶ B.X j) (w : a ≫ A.f i = b ≫ B.f j) :
    (ψ.map φ).app a b w = φ.mapPullHom (ψ.app a b w) := by
  rw [← Hom.pullHom_hom (ψ.map φ) (pullback.lift a b w) a b (by simp) (by simp),
    ← Hom.pullHom_hom ψ (pullback.lift a b w) a b (by simp) (by simp)]
  exact (mapPullHom_pullHom _ _ _ _ _ _ _).symm

variable [F.IsPrestack J] [G.IsPrestack J]

/-- Mapping along `φ` preserves identities. -/
lemma Hom.map_id (φ : F ⟶ G) {U : C} (A : Obj.{w} J F U) :
    Hom.map φ (𝟙 A) = 𝟙 (mapObj φ A) :=
  hom_ext fun T i j a b w ↦ by
    rw [Hom.app_map, id_app, id_app]

/-- Mapping along `φ` preserves composition. -/
lemma Hom.map_comp (φ : F ⟶ G) {U : C} {A B E : Obj.{w} J F U} (ψ : A ⟶ B) (χ : B ⟶ E) :
    Hom.map φ (ψ ≫ χ) = (Hom.map φ ψ).comp (Hom.map φ χ) := by
  refine Hom.ext_of_sieve _ B.mem fun T i k a c w h ↦ ?_
  obtain ⟨j, b, hb⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 h
  rw [Hom.app_comp (Hom.map φ ψ) (Hom.map φ χ) a b c w hb (hb.symm.trans w), Hom.app_map,
    Hom.app_map, Hom.app_map, comp_app ψ χ a b c w hb (hb.symm.trans w), mapPullHom_comp]

variable (J) in
/-- The functor between the categories of descent data along `w`-small covering families given by
a strong transformation `φ : F ⟶ G` of prestacks: it maps descent data and their morphisms along
`φ`. -/
abbrev mapFunctor (φ : F ⟶ G) (U : C) : Obj.{w} J F U ⥤ Obj.{w} J G U where
  obj := mapObj φ
  map ψ := Hom.map φ ψ
  map_id := Hom.map_id φ
  map_comp := Hom.map_comp φ

/-- The local evaluations of the image of a morphism under `mapFunctor` are the mapped local
evaluations. -/
lemma app_mapFunctor_map (φ : F ⟶ G) {U : C} {A B : Obj.{w} J F U} (ψ : A ⟶ B) ⦃T : C⦄
    ⦃i : A.ι⦄ ⦃j : B.ι⦄ (a : T ⟶ A.X i) (b : T ⟶ B.X j) (w : a ≫ A.f i = b ≫ B.f j) :
    Hom.app ((mapFunctor J φ U).map ψ) a b w = φ.mapPullHom (Hom.app ψ a b w) :=
  Hom.app_map φ ψ a b w

/-- `mapFunctor` sends the morphism of descent data along a fixed covering family given by a
morphism of descent data to the morphism given by its image under `mapDescentData`. -/
lemma mapFunctor_map_ofDescentDataMap (φ : F ⟶ G) {U : C} {ι : Type w} {X : ι → C}
    {f : ∀ i, X i ⟶ U} {hf : Sieve.ofArrows X f ∈ J U} {D D' : F.DescentData f} (ψ : D ⟶ D') :
    (mapFunctor J φ U).map (ofDescentDataMap (hf := hf) ψ) =
      ofDescentDataMap (hf := hf) ((φ.mapDescentData f).map ψ) :=
  hom_ext fun T i j a b w ↦ by
    rw [app_mapFunctor_map, app_ofDescentDataMap, app_ofDescentDataMap, mapPullHom_comp,
      mapPullHom_map]

omit [HasPullbacks C] [F.IsPrestack J] [G.IsPrestack J] in
/-- The identifications `toObjPullbackIso` of `F`, mapped along `φ`, are those of `G`, through the
naturality isomorphisms of `φ` at `q` and at identities. -/
lemma mapPullHom_toObjPullbackIso_hom_comp (φ : F ⟶ G) {U V : C} (q : V ⟶ U)
    (M : F.obj (.mk (op U))) ⦃T : C⦄ (b : T ⟶ V) (c : T ⟶ U) (h : b ≫ q = c) :
    φ.mapPullHom (toObjPullbackIso q M b c h).hom ≫
        (G.map c.op.toLoc).toFunctor.map
          ((φ.naturality (𝟙 U).op.toLoc).hom.toNatTrans.app M) =
      (G.map b.op.toLoc).toFunctor.map ((φ.naturality (𝟙 V).op.toLoc).hom.toNatTrans.app
          ((F.map q.op.toLoc).toFunctor.obj M)) ≫
        (G.map b.op.toLoc).toFunctor.map ((G.map (𝟙 V).op.toLoc).toFunctor.map
          ((φ.naturality q.op.toLoc).hom.toNatTrans.app M)) ≫
        (toObjPullbackIso q ((φ.app _).toFunctor.obj M) b c h).hom := by
  rw [toObjPullbackIso_hom, toObjPullbackIso_hom, mapPullHom_comp, mapPullHom_comp,
    mapPullHom_mapComp'_inv φ (𝟙 V) b b (Category.comp_id b),
    mapPullHom_mapComp'_inv φ q b c h,
    mapPullHom_mapComp'_hom φ (𝟙 U) c c (Category.comp_id c)]
  -- It remains to commute the naturality isomorphism of `φ` at `q` past the composition
  -- comparison of `G` at `𝟙 V` and `b`, and to cancel the naturality isomorphism at `𝟙 U`. The
  -- objects involved agree only up to unfolding composites in `Cat`, so the identity is applied
  -- by unification.
  have alg {D : Type u'} [Category.{v'} D] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₁' : D} (x : X₀ ⟶ X₁)
      (g₁ : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (g₂ : X₃ ⟶ X₄) (g₃ : X₄ ⟶ X₅) (i : X₅ ⟶ X₆) (j : X₆ ⟶ X₅)
      (a : X₁ ⟶ X₁') (a' : X₁' ⟶ X₃) (hij : i ≫ j = 𝟙 _) (ha : a ≫ a' = g₁ ≫ m) :
      ((x ≫ g₁) ≫ (m ≫ g₂) ≫ g₃ ≫ i) ≫ j = x ≫ a ≫ a' ≫ g₂ ≫ g₃ := by
    simp [reassoc_of% ha, hij]
  exact alg _ _ _ _ _ _ _ _ _
    ((G.map c.op.toLoc).toFunctor.mapIso
      ((Cat.Hom.toNatIso (φ.naturality (𝟙 U).op.toLoc)).app M)).inv_hom_id
    (G.mapComp'_inv_naturality (𝟙 V).op.toLoc b.op.toLoc b.op.toLoc (by simp)
      ((φ.naturality q.op.toLoc).hom.toNatTrans.app M))

variable (J) in
/-- Mapping the descent datum along the identity of `U` given by `M` gives the descent datum
given by `φ M`, through the naturality isomorphism of `φ` at the identity of `U`. -/
def toObjFunctorCompMapFunctorIso (φ : F ⟶ G) (U : C) :
    toObjFunctor.{w} J F U ⋙ mapFunctor.{w} J φ U ≅
      (φ.app (.mk (op U))).toFunctor ⋙ toObjFunctor.{w} J G U :=
  NatIso.ofComponents
    (fun M ↦ (ofDescentDataFunctor (J := J) _ (ofArrows_id_mem U)).mapIso
      ((φ.toDescentDataCompMapDescentDataIso _).app M))
    fun {M M'} x ↦ by
      have h := (ofDescentDataFunctor (J := J) _ (ofArrows_id_mem U)).congr_map
        ((φ.toDescentDataCompMapDescentDataIso (fun _ : PUnit.{w + 1} ↦ 𝟙 U)).hom.naturality x)
      rw [Functor.map_comp, Functor.map_comp] at h
      -- The image of `x` under `toObjFunctor` is `ofDescentDataMap` of its image in descent data
      -- only after unfolding the abbreviations, so `mapFunctor_map_ofDescentDataMap` is matched
      -- by `erw`.
      erw [mapFunctor_map_ofDescentDataMap]
      exact h

/-- The local evaluations of the components of `toObjFunctorCompMapFunctorIso` along a single
morphism `b : T ⟶ U` are the pullbacks of the naturality isomorphism of `φ` at the identity of
`U`. -/
lemma app_toObjFunctorCompMapFunctorIso_hom_app_self (φ : F ⟶ G) {U : C}
    (M : F.obj (.mk (op U))) ⦃T : C⦄ (b : T ⟶ U) (w : b ≫ 𝟙 U = b ≫ 𝟙 U) :
    Hom.app ((toObjFunctorCompMapFunctorIso.{w} J φ U).hom.app M) (i := PUnit.unit)
        (j := PUnit.unit) b b w =
      (G.map b.op.toLoc).toFunctor.map ((φ.naturality (𝟙 U).op.toLoc).hom.toNatTrans.app M) := by
  simp only [toObjFunctorCompMapFunctorIso, NatIso.ofComponents_hom_app, Functor.mapIso_hom,
    Iso.app_hom]
  rw [app_ofDescentDataMap_self (J := J) (F := G), toDescentDataCompMapDescentDataIso_hom_app_hom]
  -- The member of the covering family of `(toObjFunctor J F U).obj M` is `𝟙 U` by definition.
  rfl

variable (J) in
/-- The natural transformation between the functors `mapFunctor` induced by a modification
`Γ : φ ⟶ φ'`: its component at a descent datum applies the components of `Γ` to its objects. -/
def mapFunctor₂ {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') (U : C) :
    mapFunctor.{w} J φ U ⟶ mapFunctor.{w} J φ' U where
  app A := ofDescentDataMap (hf := A.mem) ((mapDescentData₂ A.f Γ).app A.D)
  naturality {A B} ψ := comp_ofDescentDataMap_eq_ofDescentDataMap_comp _ _ _ _
    fun T i j a b w ↦ by
      rw [Hom.app_map, Hom.app_map, mapDescentData₂_app_hom, mapDescentData₂_app_hom]
      exact (map_app_comp_mapPullHom Γ _).symm

/-- The components of `mapFunctor₂ J Γ U` are the morphisms of descent data along the covering
families given by the components of `mapDescentData₂`. -/
lemma mapFunctor₂_app {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') {U : C} (A : Obj.{w} J F U) :
    (mapFunctor₂.{w} J Γ U).app A =
      ofDescentDataMap (hf := A.mem) ((mapDescentData₂ A.f Γ).app A.D) :=
  (rfl)

/-- The local evaluations of the components of `mapFunctor₂ J Γ U`. -/
lemma app_mapFunctor₂_app {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') {U : C} (A : Obj.{w} J F U) ⦃T : C⦄
    ⦃i i' : A.ι⦄ (a : T ⟶ A.X i) (a' : T ⟶ A.X i') (w : a ≫ A.f i = a' ≫ A.f i') :
    Hom.app ((mapFunctor₂.{w} J Γ U).app A) a a' w =
      (G.map a.op.toLoc).toFunctor.map ((Γ.as.app _).toNatTrans.app (A.D.obj i)) ≫
        φ'.mapPullHom (A.D.hom (a ≫ A.f i) a a' rfl w.symm) := by
  rw [mapFunctor₂_app, app_ofDescentDataMap, mapDescentData₂_app_hom]

/-- `mapFunctor₂` sends identity modifications to identities. -/
@[simp]
lemma mapFunctor₂_id (φ : F ⟶ G) (U : C) : mapFunctor₂.{w} J (𝟙 φ) U = 𝟙 _ := by
  ext A : 2
  refine hom_ext fun T i j a b w ↦ ?_
  rw [app_mapFunctor₂_app, NatTrans.id_app, id_app]
  simp

/-- `mapFunctor₂` is compatible with composition of modifications. -/
@[simp]
lemma mapFunctor₂_comp {φ φ' φ'' : F ⟶ G} (Γ : φ ⟶ φ') (Δ : φ' ⟶ φ'') (U : C) :
    mapFunctor₂.{w} J (Γ ≫ Δ) U = mapFunctor₂.{w} J Γ U ≫ mapFunctor₂.{w} J Δ U := by
  ext A : 2
  refine hom_ext fun T i j a b w ↦ ?_
  refine Eq.trans ?_ (comp_app ((mapFunctor₂.{w} J Γ U).app A) ((mapFunctor₂.{w} J Δ U).app A)
    a a b w rfl w).symm
  rw [app_mapFunctor₂_app, app_mapFunctor₂_app, app_mapFunctor₂_app,
    A.D.hom_self _ _ rfl, mapPullHom_id]
  simp

variable (J F) in
/-- Mapping descent data along the identity strong transformation is isomorphic to the identity
functor, through identities. -/
def mapFunctorIdIso (U : C) : mapFunctor.{w} J (𝟙 F) U ≅ 𝟭 (Obj.{w} J F U) :=
  NatIso.ofComponents
    (fun A ↦ (ofDescentDataFunctor (J := J) A.f A.mem).mapIso ((mapDescentDataId F A.f).app A.D))
    fun {A B} ψ ↦ comp_ofDescentDataMap_eq_ofDescentDataMap_comp
      ((mapDescentDataId F A.f).hom.app A.D) ((mapDescentDataId F B.f).hom.app B.D)
      (Hom.map (𝟙 F) ψ) ψ fun T i j a b w ↦ by
      rw [Hom.app_map, id_mapPullHom, mapDescentDataId_hom_app_hom,
        mapDescentDataId_hom_app_hom]
      -- The identities are over objects of the descent data mapped along `𝟙 F`, which are those
      -- of `A` and `B` only up to unfolding the identity strong transformation.
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The local evaluations of the components of `mapFunctorIdIso` are the descent isomorphisms. -/
lemma app_mapFunctorIdIso_hom_app {U : C} (A : Obj.{w} J F U) ⦃T : C⦄ ⦃i i' : A.ι⦄
    (a : T ⟶ A.X i) (a' : T ⟶ A.X i') (w : a ≫ A.f i = a' ≫ A.f i') :
    Hom.app ((mapFunctorIdIso.{w} J F U).hom.app A) a a' w =
      A.D.hom (a ≫ A.f i) a a' rfl w.symm := by
  simp only [mapFunctorIdIso, NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom]
  rw [app_ofDescentDataMap, mapDescentDataId_hom_app_hom]
  -- As in `mapFunctorIdIso`, the identity is over an object of the mapped descent datum.
  erw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

variable (J) in
/-- Mapping descent data along a composite of strong transformations is isomorphic to the
composite of the mapping functors, through identities. -/
def mapFunctorCompIso {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [H.IsPrestack J] (φ : F ⟶ G)
    (ψ : G ⟶ H) (U : C) :
    mapFunctor.{w} J (φ ≫ ψ) U ≅ mapFunctor.{w} J φ U ⋙ mapFunctor.{w} J ψ U :=
  NatIso.ofComponents
    (fun A ↦ (ofDescentDataFunctor (J := J) A.f A.mem).mapIso
      ((φ.mapDescentDataComp A.f ψ).app A.D))
    fun {A B} χ ↦ comp_ofDescentDataMap_eq_ofDescentDataMap_comp
      ((φ.mapDescentDataComp A.f ψ).hom.app A.D) ((φ.mapDescentDataComp B.f ψ).hom.app B.D)
      (Hom.map (φ ≫ ψ) χ) (Hom.map ψ (Hom.map φ χ)) fun T i j a b w ↦ by
      rw [Hom.app_map, Hom.app_map, Hom.app_map, comp_mapPullHom,
        mapDescentDataComp_hom_app_hom, mapDescentDataComp_hom_app_hom]
      simp

/-- The local evaluations of the components of `mapFunctorCompIso` are the descent isomorphisms. -/
lemma app_mapFunctorCompIso_hom_app {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [H.IsPrestack J]
    (φ : F ⟶ G) (ψ : G ⟶ H) {U : C} (A : Obj.{w} J F U) ⦃T : C⦄ ⦃i i' : A.ι⦄
    (a : T ⟶ A.X i) (a' : T ⟶ A.X i') (w : a ≫ A.f i = a' ≫ A.f i') :
    Hom.app ((mapFunctorCompIso.{w} J φ ψ U).hom.app A) a a' w =
      ψ.mapPullHom (φ.mapPullHom (A.D.hom (a ≫ A.f i) a a' rfl w.symm)) := by
  simp only [mapFunctorCompIso, NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom]
  rw [app_ofDescentDataMap, mapDescentDataComp_hom_app_hom]
  simp

end TauCeti.Stack.Stackification.Obj

namespace TauCeti.Stack.Stackification.Obj.PullbackData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [HasPullbacks C] {U V : C} {q : V ⟶ U}
  {A A' : Obj.{w} J F U} {B B' : Obj.{w} J F V}

/-- Pullback data, mapped along a strong transformation `φ`: the identifications are mapped by
`mapPullHom`. -/
abbrev map (φ : F ⟶ G) (P : PullbackData q A B) : PullbackData q (mapObj φ A) (mapObj φ B) where
  α := P.α
  β := P.β
  w := P.w
  iso T j b c h :=
    { hom := φ.mapPullHom (P.iso b c h).hom
      inv := φ.mapPullHom (P.iso b c h).inv
      hom_inv_id := by rw [← mapPullHom_comp, Iso.hom_inv_id, mapPullHom_id]
      inv_hom_id := by rw [← mapPullHom_comp, Iso.inv_hom_id, mapPullHom_id] }
  pullHom_iso T j b c h T' g gb gc hgb hgc := by
    rw [← mapPullHom_pullHom, P.pullHom_iso]
  hom_eq T j j' q' b b' hb hb' c c' h h' := by
    simp only [← mapPullHom_comp]
    rw [← P.hom_eq q' b b' hb hb' c c' h h']

omit [HasPullbacks C] in
/-- Mapping the pullback data `refl A` gives `refl` of the mapped descent datum. -/
@[simp]
lemma map_refl (φ : F ⟶ G) (A : Obj.{w} J F U) : (refl A).map φ = refl (mapObj φ A) :=
  (rfl)

variable [F.IsPrestack J] [G.IsPrestack J]

/-- `mapFunctor` commutes with transport along pullback data. -/
lemma mapFunctor_map_transport (φ : F ⟶ G) (P : PullbackData q A B) (P' : PullbackData q A' B')
    (ψ : A ⟶ A') :
    (mapFunctor J φ V).map (transport P P' ψ) =
      transport (P.map φ) (P'.map φ) ((mapFunctor J φ U).map ψ) :=
  hom_ext fun T j j' b b' w ↦ by
    rw [app_mapFunctor_map, app_transport _ _ _ _ _ _ _ _ rfl rfl,
      app_transport (P.map φ) (P'.map φ) _ _ _ _ (b ≫ P.β j) (b' ≫ P'.β j') rfl rfl,
      transportApp_def,
      transportApp_def, mapPullHom_comp, mapPullHom_comp, app_mapFunctor_map]

omit [F.IsPrestack J] in
/-- Mapping a composite of pullback data does not change transport onto it. -/
lemma transport_map_trans (φ : F ⟶ G) {W : C} {r : W ⟶ V} {E : Obj.{w} J G W}
    {E' : Obj.{w} J F W} (P : PullbackData (r ≫ q) (mapObj φ A) E) (R : PullbackData r B' E')
    (Q : PullbackData q A' B') (ψ : mapObj φ A ⟶ mapObj φ A') :
    transport P ((R.trans Q _ rfl).map φ) ψ = transport P ((R.map φ).trans (Q.map φ) _ rfl) ψ :=
  hom_ext fun T k k' e e' w ↦ by
    rw [app_transport _ _ _ _ _ _ (e ≫ P.β k) (e' ≫ (R.trans Q _ rfl).β k') rfl rfl,
      transportApp_def, app_transport_trans (r ≫ q) rfl P (R.map φ) (Q.map φ) ψ e e' w _ rfl _
        rfl (e' ≫ R.β k' ≫ Q.β (R.α k')) (Category.assoc _ _ _)]
    simp only [map]
    rw [trans_iso, Iso.trans_inv, ← mapPullHom_comp]
    -- The local sections `e' ≫ (R.trans Q _ rfl).β k'` and `e' ≫ R.β k' ≫ Q.β (R.α k')` agree
    -- by `trans_β`, but they live in types that are equal only after unfolding the index map of
    -- `R.trans Q`, so the last step is definitional.
    rfl

/-- The components of `mapFunctor₂ J Γ` are compatible with transport along mapped pullback
data. -/
lemma transport_mapFunctor₂_app {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') (P : PullbackData q A B) :
    transport (P.map φ) (P.map φ') ((mapFunctor₂.{w} J Γ U).app A) =
      (mapFunctor₂.{w} J Γ V).app B :=
  hom_ext fun T j j' b b' w ↦ by
    rw [app_transport (P.map φ) (P.map φ') _ _ _ _ (b ≫ P.β j) (b' ≫ P.β j') rfl rfl,
      transportApp_def, app_mapFunctor₂_app, app_mapFunctor₂_app,
      P.hom_eq (b ≫ B.f j) b b' rfl w.symm _ _ rfl rfl]
    simp only [mapPullHom_comp, Category.assoc]
    rw [← map_app_comp_mapPullHom_assoc Γ]

/-- The components of `mapFunctorIdIso` are compatible with transport along pullback data. -/
lemma transport_mapFunctorIdIso_hom_app (P : PullbackData q A B) :
    transport (P.map (𝟙 F)) P ((mapFunctorIdIso.{w} J F U).hom.app A) =
      (mapFunctorIdIso.{w} J F V).hom.app B :=
  hom_ext fun T j j' b b' w ↦ by
    rw [app_transport (P.map (𝟙 F)) P _ _ _ _ (b ≫ P.β j) (b' ≫ P.β j') rfl rfl,
      transportApp_def, app_mapFunctorIdIso_hom_app, app_mapFunctorIdIso_hom_app,
      P.hom_eq (b ≫ B.f j) b b' rfl w.symm _ _ rfl rfl]
    -- The identifications of `P.map (𝟙 F)` are those of `P` up to unfolding `mapPullHom`
    -- along the identity.
    simp only [id_mapPullHom]
    rfl

/-- The components of `mapFunctorCompIso` are compatible with transport along pullback data. -/
lemma transport_mapFunctorCompIso_hom_app {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    [H.IsPrestack J] (φ : F ⟶ G) (ψ : G ⟶ H) (P : PullbackData q A B) :
    transport (P.map (φ ≫ ψ)) ((P.map φ).map ψ) ((mapFunctorCompIso.{w} J φ ψ U).hom.app A) =
      (mapFunctorCompIso.{w} J φ ψ V).hom.app B :=
  hom_ext fun T j j' b b' w ↦ by
    rw [app_transport (P.map (φ ≫ ψ)) ((P.map φ).map ψ) _ _ _ _ (b ≫ P.β j) (b' ≫ P.β j') rfl
        rfl, transportApp_def, app_mapFunctorCompIso_hom_app, app_mapFunctorCompIso_hom_app,
      P.hom_eq (b ≫ B.f j) b b' rfl w.symm _ _ rfl rfl]
    simp only [comp_mapPullHom, mapPullHom_comp]
    -- The two sides differ only in the objects of the mapped descent data, which agree up to
    -- unfolding the composite strong transformation.
    rfl

end TauCeti.Stack.Stackification.Obj.PullbackData

namespace TauCeti.Stack

open Stackification Obj PullbackData

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasPullbacks C]
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [F.IsPrestack J] [G.IsPrestack J]

/-- The naturality isomorphisms of the functors `mapFunctor` between descent data along `w`-small
covering families: for `q : V ⟶ U`, mapping the pullback of a descent datum along `φ` is
isomorphic to pulling back the mapped descent datum. -/
def stackificationMapNatIso (φ : F ⟶ G) {U V : C} (q : V ⟶ U) :
    pullFunctor J F q ⋙ mapFunctor.{w} J φ V ≅ mapFunctor.{w} J φ U ⋙ pullFunctor J G q :=
  NatIso.ofComponents
    (fun A ↦ isoOfData ((pullbackData q A).map φ) (pullbackData q (mapObj φ A)))
    fun {A A'} ψ ↦ by
      rw [isoOfData_hom, isoOfData_hom]
      -- The maps of the composites `_ ⋙ _` are those of `pullFunctor` and `mapFunctor` only after
      -- unfolding these abbreviations, so `mapFunctor_map_transport` is matched by `erw`.
      erw [mapFunctor_map_transport, pullFunctor_map]
      simp only [transport_comp, Category.comp_id, Category.id_comp]

/-- The components of `stackificationMapNatIso` are transports of identities. -/
lemma stackificationMapNatIso_hom_app (φ : F ⟶ G) {U V : C} (q : V ⟶ U) (A : Obj.{w} J F U) :
    (stackificationMapNatIso.{w} J φ q).hom.app A =
      transport ((pullbackData q A).map φ) (pullbackData q (mapObj φ A)) (𝟙 _) := by
  simp only [stackificationMapNatIso, NatIso.ofComponents_hom_app, isoOfData_hom]

/-- The inverse components of `stackificationMapNatIso` are transports of identities. -/
lemma stackificationMapNatIso_inv_app (φ : F ⟶ G) {U V : C} (q : V ⟶ U) (A : Obj.{w} J F U) :
    (stackificationMapNatIso.{w} J φ q).inv.app A =
      transport (pullbackData q (mapObj φ A)) ((pullbackData q A).map φ) (𝟙 _) := by
  simp only [stackificationMapNatIso, NatIso.ofComponents_inv_app, isoOfData_inv]

/-- The unit condition for the naturality isomorphisms `stackificationMapNatIso`. -/
lemma stackificationMapNatIso_hom_app_comp_pullFunctorId_hom_app (φ : F ⟶ G) {U : C}
    (A : Obj.{w} J F U) :
    (stackificationMapNatIso.{w} J φ (𝟙 U)).hom.app A ≫
        (pullFunctorId J G U).hom.app (mapObj φ A) =
      (mapFunctor.{w} J φ U).map ((pullFunctorId J F U).hom.app A) := by
  rw [stackificationMapNatIso_hom_app, pullFunctorId_hom_app, pullFunctorId_hom_app,
    mapFunctor_map_transport, transport_comp, map_refl, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- The composition condition for the naturality isomorphisms `stackificationMapNatIso`. -/
lemma stackificationMapNatIso_hom_app_comp_pullFunctorComp_hom_app (φ : F ⟶ G) {U V W : C}
    (q : V ⟶ U) (r : W ⟶ V) (A : Obj.{w} J F U) :
    (stackificationMapNatIso.{w} J φ (r ≫ q)).hom.app A ≫
        (pullFunctorComp J G q r (r ≫ q) rfl).hom.app (mapObj φ A) =
      (mapFunctor.{w} J φ W).map ((pullFunctorComp J F q r (r ≫ q) rfl).hom.app A) ≫
        (stackificationMapNatIso.{w} J φ r).hom.app (pullObj q A) ≫
          (pullFunctor J G r).map ((stackificationMapNatIso.{w} J φ q).hom.app A) := by
  rw [stackificationMapNatIso_hom_app, stackificationMapNatIso_hom_app,
    stackificationMapNatIso_hom_app, pullFunctorComp_hom_app, pullFunctorComp_hom_app,
    mapFunctor_map_transport, CategoryTheory.Functor.map_id, transport_map_trans, pullFunctor_map,
    transport_transport _ _ _ _ _ (r ≫ q) rfl, ← transport_id ((pullbackData q A).map φ),
    transport_transport _ _ _ _ _ (r ≫ q) rfl]
  simp only [transport_comp, Category.comp_id]
  -- The two sides differ only in writing `pullObj q (mapObj φ A)` as
  -- `(mapFunctor J φ U ⋙ pullFunctor J G q).obj A`, which appears in the type of a pullback datum,
  -- so the last composite of transports is formed by unification.
  exact ((transport_comp _ _ _ _ _).trans (congrArg _ (Category.comp_id _))).symm

/-- The strong transformation `stackification J F ⟶ stackification J G` induced by a strong
transformation `φ : F ⟶ G` of prestacks: its component at `U` maps descent data along `w`-small
covering families of `U` along `φ` (`Stackification.Obj.mapFunctor`). -/
-- The body is exposed so that the components and naturality isomorphisms are definitionally
-- `mapFunctor` and `stackificationMapNatIso`: the statements of the component formulas below do
-- not typecheck otherwise.
@[expose] def stackificationMap (φ : F ⟶ G) :
    stackification.{w} J F ⟶ stackification.{w} J G where
  app a := (mapFunctor.{w} J φ a.as.unop).toCatHom
  naturality f := Cat.Hom.isoMk (stackificationMapNatIso.{w} J φ f.as.unop)
  naturality_naturality η :=
    Pseudofunctor.naturality_naturality_of_locallyDiscrete (stackification.{w} J F)
      (stackification.{w} J G) (fun a ↦ (mapFunctor.{w} J φ a.as.unop).toCatHom)
      (fun f ↦ Cat.Hom.isoMk (stackificationMapNatIso.{w} J φ f.as.unop)) η
  naturality_id _ :=
    Cat.comp_whiskerLeft_eq_whiskerRight_comp_leftUnitor_hom_comp_rightUnitor_inv _ _ _
      fun A ↦
        -- The components of `(stackification J F).mapId a` are those of `pullFunctorId`
        -- (`stackification_mapId_hom_toNatTrans_app`), so this is the unit condition up to
        -- unfolding `Cat.Hom.isoMk` and `toCatHom`.
        stackificationMapNatIso_hom_app_comp_pullFunctorId_hom_app.{w} J φ A
  naturality_comp f g :=
    Cat.comp_whiskerLeft_eq_whiskerRight_comp_associators _ _ _ _ _ fun A ↦
      -- As in `naturality_id`, through the components `pullFunctorComp` of
      -- `(stackification J F).mapComp f g` (`stackification_mapComp_hom_toNatTrans_app`).
      stackificationMapNatIso_hom_app_comp_pullFunctorComp_hom_app.{w} J φ f.as.unop g.as.unop A

/-- The component of `stackificationMap J φ` at `U` is `mapFunctor`. -/
@[simp]
lemma stackificationMap_app_toFunctor (φ : F ⟶ G) (a : LocallyDiscrete Cᵒᵖ) :
    ((stackificationMap.{w} J φ).app a).toFunctor = mapFunctor.{w} J φ a.as.unop :=
  (rfl)

/-- The naturality isomorphisms of `stackificationMap J φ` are `stackificationMapNatIso`. -/
@[simp]
lemma stackificationMap_naturality_hom_toNatTrans_app (φ : F ⟶ G) {a b : LocallyDiscrete Cᵒᵖ}
    (f : a ⟶ b) (A : Obj.{w} J F a.as.unop) :
    ((stackificationMap.{w} J φ).naturality f).hom.toNatTrans.app A =
      (stackificationMapNatIso.{w} J φ f.as.unop).hom.app A :=
  (rfl)

/-- The inverse naturality isomorphisms of `stackificationMap J φ` are those of
`stackificationMapNatIso`. -/
@[simp]
lemma stackificationMap_naturality_inv_toNatTrans_app (φ : F ⟶ G) {a b : LocallyDiscrete Cᵒᵖ}
    (f : a ⟶ b) (A : Obj.{w} J F a.as.unop) :
    ((stackificationMap.{w} J φ).naturality f).inv.toNatTrans.app A =
      (stackificationMapNatIso.{w} J φ f.as.unop).inv.app A :=
  (rfl)

/-- The components of `toObjFunctorCompMapFunctorIso` are compatible with pullback along `q`: with
the naturality isomorphism of `φ` at `q`, they are transports of one another along the pullback
data `toObjPullbackData`. -/
lemma toObjFunctorCompMapFunctorIso_hom_app_comp_map (φ : F ⟶ G) {U V : C} (q : V ⟶ U)
    (M : F.obj (.mk (op U))) :
    (toObjFunctorCompMapFunctorIso.{w} J φ V).hom.app ((F.map q.op.toLoc).toFunctor.obj M) ≫
        (toObjFunctor.{w} J G V).map ((φ.naturality q.op.toLoc).hom.toNatTrans.app M) =
      transport ((toObjPullbackData q M).map φ)
        (toObjPullbackData q ((φ.app _).toFunctor.obj M))
        ((toObjFunctorCompMapFunctorIso.{w} J φ U).hom.app M) :=
  hom_ext fun T i j b b' w ↦ by
    cases i; cases j
    obtain rfl : b = b' := by simpa using w
    refine (comp_app ((toObjFunctorCompMapFunctorIso.{w} J φ V).hom.app _)
      ((toObjFunctor.{w} J G V).map ((φ.naturality q.op.toLoc).hom.toNatTrans.app M))
      (j := PUnit.unit) b b b w rfl rfl).trans ?_
    rw [app_toObjFunctorCompMapFunctorIso_hom_app_self,
      app_toObjFunctor_map_self,
      app_transport ((toObjPullbackData q M).map φ)
        (toObjPullbackData q ((φ.app _).toFunctor.obj M)) _ b b w (b ≫ q) (b ≫ q) (by simp)
        (by simp), transportApp_def, app_toObjFunctorCompMapFunctorIso_hom_app_self]
    simp only [PullbackData.map, toObjPullbackData_iso]
    -- The objects of the two sides agree only up to unfolding composites in `Cat`, so the
    -- identification of `mapPullHom_toObjPullbackIso_hom_comp` is applied by unification.
    have alg {D : Type u'} [Category.{v'} D] {X₀ X₁ X₂ X₃ X₃' : D} {x : X₀ ⟶ X₁} {y : X₁ ⟶ X₂}
        {a : X₀ ⟶ X₃'} {a' : X₃' ⟶ X₃} (e : X₂ ≅ X₃) (h : a ≫ a' = x ≫ y ≫ e.hom) :
        x ≫ y = a ≫ a' ≫ e.inv := by
      simp [reassoc_of% h]
    exact alg _ (mapPullHom_toObjPullbackIso_hom_comp φ q M b (b ≫ q) rfl)

/-- The components of `mapFunctor₂ J Γ` are compatible with the naturality isomorphisms
`stackificationMapNatIso`. -/
lemma mapFunctor₂_app_comp_stackificationMapNatIso_hom_app {φ φ' : F ⟶ G} (Γ : φ ⟶ φ')
    {U V : C} (q : V ⟶ U) (A : Obj.{w} J F U) :
    (mapFunctor₂.{w} J Γ V).app (pullObj q A) ≫ (stackificationMapNatIso.{w} J φ' q).hom.app A =
      (stackificationMapNatIso.{w} J φ q).hom.app A ≫
        (pullFunctor J G q).map ((mapFunctor₂.{w} J Γ U).app A) := by
  rw [stackificationMapNatIso_hom_app, stackificationMapNatIso_hom_app, pullFunctor_map,
    ← transport_mapFunctor₂_app Γ (pullbackData q A), transport_comp, transport_comp,
    Category.comp_id, Category.id_comp]

/-- The modification `stackificationMap J φ ⟶ stackificationMap J φ'` induced by a modification
`Γ : φ ⟶ φ'` of strong transformations of prestacks: its components apply the components of `Γ`
to the objects of descent data (`Stackification.Obj.mapFunctor₂`). -/
def stackificationMap₂ {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') :
    stackificationMap.{w} J φ ⟶ stackificationMap.{w} J φ' where
  as :=
    { app a := (mapFunctor₂.{w} J Γ a.as.unop).toCatHom₂
      naturality f := Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun A ↦
        -- This is `mapFunctor₂_app_comp_stackificationMapNatIso_hom_app` up to unfolding the
        -- components of `stackificationMap` and `stackification`.
        mapFunctor₂_app_comp_stackificationMapNatIso_hom_app.{w} J Γ f.as.unop A }

/-- The components of `stackificationMap₂ J Γ` are those of `mapFunctor₂`. -/
@[simp]
lemma stackificationMap₂_as_app_toNatTrans_app {φ φ' : F ⟶ G} (Γ : φ ⟶ φ')
    (a : LocallyDiscrete Cᵒᵖ) (A : Obj.{w} J F a.as.unop) :
    ((stackificationMap₂.{w} J Γ).as.app a).toNatTrans.app A =
      (mapFunctor₂.{w} J Γ a.as.unop).app A :=
  (rfl)

variable (F G) in
/-- The stackification of prestacks acts functorially on strong transformations and their
modifications. -/
-- The body is exposed, as is that of `stackificationMap`, so that the images of strong
-- transformations and modifications are definitionally `stackificationMap` and
-- `stackificationMap₂`: the statement of `stackificationMapFunctor_map` does not typecheck
-- otherwise.
@[expose] def stackificationMapFunctor :
    (F ⟶ G) ⥤ (stackification.{w} J F ⟶ stackification.{w} J G) where
  obj := stackificationMap.{w} J
  map := stackificationMap₂.{w} J
  map_id φ := by
    ext a : 2
    exact mapFunctor₂_id.{w} (J := J) φ a.as.unop
  map_comp Γ Δ := by
    ext a : 2
    exact mapFunctor₂_comp.{w} (J := J) Γ Δ a.as.unop

/-- `stackificationMapFunctor` sends a strong transformation to its stackification. -/
@[simp]
lemma stackificationMapFunctor_obj (φ : F ⟶ G) :
    (stackificationMapFunctor.{w} J F G).obj φ = stackificationMap.{w} J φ :=
  (rfl)

/-- `stackificationMapFunctor` sends a modification to its stackification. -/
@[simp]
lemma stackificationMapFunctor_map {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') :
    (stackificationMapFunctor.{w} J F G).map Γ = stackificationMap₂.{w} J Γ :=
  (rfl)

/-- The components of `mapFunctorIdIso` are compatible with the naturality isomorphisms
`stackificationMapNatIso`. -/
lemma mapFunctorIdIso_hom_app_pullObj {U V : C} (q : V ⟶ U) (A : Obj.{w} J F U) :
    (mapFunctorIdIso.{w} J F V).hom.app (pullObj q A) =
      (stackificationMapNatIso.{w} J (𝟙 F) q).hom.app A ≫
        (pullFunctor J F q).map ((mapFunctorIdIso.{w} J F U).hom.app A) := by
  rw [stackificationMapNatIso_hom_app, pullFunctor_map, transport_comp, Category.id_comp]
  -- The target of the transport is `pullbackData q ((𝟭 _).obj A)`, which is `pullbackData q A`
  -- by definition.
  exact (transport_mapFunctorIdIso_hom_app (pullbackData q A)).symm

/-- The components of `mapFunctorCompIso` are compatible with the naturality isomorphisms
`stackificationMapNatIso`. -/
lemma mapFunctorCompIso_hom_app_comp_stackificationMapNatIso_hom_app
    {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [H.IsPrestack J] (φ : F ⟶ G) (ψ : G ⟶ H)
    {U V : C} (q : V ⟶ U) (A : Obj.{w} J F U) :
    (mapFunctorCompIso.{w} J φ ψ V).hom.app (pullObj q A) ≫
        (mapFunctor.{w} J ψ V).map ((stackificationMapNatIso.{w} J φ q).hom.app A) ≫
          (stackificationMapNatIso.{w} J ψ q).hom.app (mapObj φ A) =
      (stackificationMapNatIso.{w} J (φ ≫ ψ) q).hom.app A ≫
        (pullFunctor J H q).map ((mapFunctorCompIso.{w} J φ ψ U).hom.app A) := by
  rw [stackificationMapNatIso_hom_app, stackificationMapNatIso_hom_app,
    stackificationMapNatIso_hom_app, pullFunctor_map, mapFunctor_map_transport,
    CategoryTheory.Functor.map_id, ← transport_mapFunctorCompIso_hom_app φ ψ (pullbackData q A),
    transport_comp]
  -- The identities are over `(mapFunctor J ψ U).obj (mapObj φ A)`, which is
  -- `mapObj ψ (mapObj φ A)` only after unfolding, so the transports are composed by `erw`.
  erw [transport_comp, transport_comp]
  simp only [Category.comp_id, Category.id_comp]
  -- The two sides differ only in writing `mapObj ψ (mapObj φ A)` as a value of a composite.
  rfl

variable (F) in
/-- The stackification of the identity strong transformation is the identity, up to the invertible
modification with components `mapFunctorIdIso`. -/
def stackificationMapId : stackificationMap.{w} J (𝟙 F) ≅ 𝟙 (stackification.{w} J F) :=
  isoMk (fun a ↦ Cat.Hom.isoMk (mapFunctorIdIso.{w} J F a.as.unop))
    fun f ↦ Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun A ↦ by
      rw [categoryStruct_id_naturality_hom]
      -- The unitors of `Cat` have identity components.
      erw [Cat.Hom₂.comp_app]
      simp only [Cat.rightUnitor_hom_app, Cat.leftUnitor_inv_app, eqToHom_refl]
      -- This is `mapFunctorIdIso_hom_app_pullObj` up to unfolding `Cat.Hom.isoMk` and the
      -- components of `stackificationMap` and `stackification`.
      exact ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (Category.comp_id _)).trans
        (mapFunctorIdIso_hom_app_pullObj.{w} J f.as.unop A)

/-- The components of `stackificationMapId` are those of `mapFunctorIdIso`. -/
@[simp]
lemma stackificationMapId_hom_as_app_toNatTrans_app (a : LocallyDiscrete Cᵒᵖ)
    (A : Obj.{w} J F a.as.unop) :
    ((stackificationMapId.{w} J F).hom.as.app a).toNatTrans.app A =
      (mapFunctorIdIso.{w} J F a.as.unop).hom.app A :=
  (rfl)

/-- The inverse components of `stackificationMapId` are those of `mapFunctorIdIso`. -/
@[simp]
lemma stackificationMapId_inv_as_app_toNatTrans_app (a : LocallyDiscrete Cᵒᵖ)
    (A : Obj.{w} J F a.as.unop) :
    ((stackificationMapId.{w} J F).inv.as.app a).toNatTrans.app A =
      (mapFunctorIdIso.{w} J F a.as.unop).inv.app A :=
  (rfl)

/-- The stackification of a composite of strong transformations is the composite of their
stackifications, up to the invertible modification with components `mapFunctorCompIso`. -/
def stackificationMapComp {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} [H.IsPrestack J]
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    stackificationMap.{w} J (φ ≫ ψ) ≅ stackificationMap.{w} J φ ≫ stackificationMap.{w} J ψ :=
  isoMk (fun a ↦ Cat.Hom.isoMk (mapFunctorCompIso.{w} J φ ψ a.as.unop))
    fun f ↦ Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun A ↦ by
      rw [comp_naturality_hom_app]
      -- This is `mapFunctorCompIso_hom_app_comp_stackificationMapNatIso_hom_app` up to unfolding
      -- `Cat.Hom.isoMk` and the components of `stackificationMap` and `stackification`.
      exact mapFunctorCompIso_hom_app_comp_stackificationMapNatIso_hom_app.{w} J φ ψ f.as.unop A

/-- The components of `stackificationMapComp` are those of `mapFunctorCompIso`. -/
@[simp]
lemma stackificationMapComp_hom_as_app_toNatTrans_app {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    [H.IsPrestack J] (φ : F ⟶ G) (ψ : G ⟶ H) (a : LocallyDiscrete Cᵒᵖ)
    (A : Obj.{w} J F a.as.unop) :
    ((stackificationMapComp.{w} J φ ψ).hom.as.app a).toNatTrans.app A =
      (mapFunctorCompIso.{w} J φ ψ a.as.unop).hom.app A :=
  (rfl)

/-- The inverse components of `stackificationMapComp` are those of `mapFunctorCompIso`. -/
@[simp]
lemma stackificationMapComp_inv_as_app_toNatTrans_app {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    [H.IsPrestack J] (φ : F ⟶ G) (ψ : G ⟶ H) (a : LocallyDiscrete Cᵒᵖ)
    (A : Obj.{w} J F a.as.unop) :
    ((stackificationMapComp.{w} J φ ψ).inv.as.app a).toNatTrans.app A =
      (mapFunctorCompIso.{w} J φ ψ a.as.unop).inv.app A :=
  (rfl)

/-- The naturality square of the components `toObjFunctorCompMapFunctorIso` with respect to the
naturality isomorphisms of `toObjFunctor` (`toStackificationNatIso`), of `mapFunctor`
(`stackificationMapNatIso`) and of `φ`. For `F` and `G` valued in the universes of their
stackifications, it is the naturality condition of `toStackificationCompStackificationMapIso`. -/
lemma toObjFunctorCompMapFunctorIso_hom_app_naturality (φ : F ⟶ G) {U V : C} (q : V ⟶ U)
    (M : F.obj (.mk (op U))) :
    (toObjFunctorCompMapFunctorIso.{w} J φ V).hom.app ((F.map q.op.toLoc).toFunctor.obj M) ≫
        (toObjFunctor.{w} J G V).map ((φ.naturality q.op.toLoc).hom.toNatTrans.app M) ≫
          (toStackificationNatIso.{w} J G q).hom.app ((φ.app _).toFunctor.obj M) =
      (mapFunctor.{w} J φ V).map ((toStackificationNatIso.{w} J F q).hom.app M) ≫
        (stackificationMapNatIso.{w} J φ q).hom.app ((toObjFunctor.{w} J F U).obj M) ≫
          (pullFunctor J G q).map ((toObjFunctorCompMapFunctorIso.{w} J φ U).hom.app M) := by
  rw [← Category.assoc, toObjFunctorCompMapFunctorIso_hom_app_comp_map,
    toStackificationNatIso_hom_app, toStackificationNatIso_hom_app,
    stackificationMapNatIso_hom_app, pullFunctor_map, mapFunctor_map_transport,
    CategoryTheory.Functor.map_id, transport_comp, transport_comp]
  -- The last composite of transports is formed by unification, as the pullback data are stated
  -- for `((φ.app _).toFunctor ⋙ toObjFunctor J G U).obj M` on one side and
  -- `(toObjFunctor J G U).obj ((φ.app _).toFunctor.obj M)` on the other.
  refine Eq.trans ?_ (transport_comp _ _ _ _ _).symm
  simp only [Category.comp_id, Category.id_comp]
  -- The two sides differ only in these two ways of writing the same object.
  rfl

end TauCeti.Stack

namespace TauCeti.Stack

open Stackification Obj

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasPullbacks C]
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max w v', max (w + 1) u v v' u'}} [F.IsPrestack J]
  [G.IsPrestack J]

/-- The unit of the stackification is natural in strong transformations of prestacks: for
`φ : F ⟶ G`, the invertible modification between `toStackification J F ≫ stackificationMap J φ`
and `φ ≫ toStackification J G`, whose components are `toObjFunctorCompMapFunctorIso`. -/
def toStackificationCompStackificationMapIso (φ : F ⟶ G) :
    toStackification.{w, v', u'} J F ≫ stackificationMap.{w} J φ ≅
      φ ≫ toStackification.{w, v', u'} J G :=
  isoMk (fun a ↦ Cat.Hom.isoMk (toObjFunctorCompMapFunctorIso.{w} J φ a.as.unop))
    fun {a b} f ↦ Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun M ↦ by
      rw [comp_naturality_hom_app, comp_naturality_hom_app]
      -- This is `toObjFunctorCompMapFunctorIso_hom_app_naturality` up to unfolding
      -- `Cat.Hom.isoMk` and the components of `toStackification`, `stackificationMap` and
      -- `stackification J G`.
      exact (toObjFunctorCompMapFunctorIso_hom_app_naturality.{w} J φ f.as.unop M).trans
        (Category.assoc _ _ _).symm

/-- The components of `toStackificationCompStackificationMapIso` are those of
`toObjFunctorCompMapFunctorIso`. -/
@[simp]
lemma toStackificationCompStackificationMapIso_hom_as_app_toNatTrans_app (φ : F ⟶ G)
    (a : LocallyDiscrete Cᵒᵖ) (M : F.obj a) :
    ((toStackificationCompStackificationMapIso.{w, v', u'} J φ).hom.as.app a).toNatTrans.app M =
      (toObjFunctorCompMapFunctorIso.{w} J φ a.as.unop).hom.app M :=
  (rfl)

/-- The inverse components of `toStackificationCompStackificationMapIso` are those of
`toObjFunctorCompMapFunctorIso`. -/
@[simp]
lemma toStackificationCompStackificationMapIso_inv_as_app_toNatTrans_app (φ : F ⟶ G)
    (a : LocallyDiscrete Cᵒᵖ) (M : F.obj a) :
    ((toStackificationCompStackificationMapIso.{w, v', u'} J φ).inv.as.app a).toNatTrans.app M =
      (toObjFunctorCompMapFunctorIso.{w} J φ a.as.unop).inv.app M :=
  (rfl)

end TauCeti.Stack
