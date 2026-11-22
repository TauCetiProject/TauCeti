/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import TauCeti.CategoryTheory.Sites.Descent.Stackification.Unit

/-!
# The unit of the stackification as a strong transformation

For a prestack `F` for a Grothendieck topology `J` on a category with pullbacks, the functors
`Obj.toObjFunctor J F U : F.obj U ⥤ Obj J F U`, which send `M` to the descent datum along the
identity of `U` given by `M`, are pseudonatural in `U`. They form the unit
`TauCeti.Stack.toStackification : F ⟶ stackification J F` of the stackification (Stacks,
Lemma 02ZN), a strong transformation, whenever the universes of `F` are those of
`stackification J F`; this holds for the big site of schemes `Scheme.{u}` with `w = u` and `F`
valued in `Cat.{u, u + 1}`.

The naturality isomorphism at `q : V ⟶ U` identifies the embedding of `q^* M` with the pullback
along `q` of the embedding of `M` (`TauCeti.Stack.toStackificationNatIso`). It is the isomorphism
`Obj.PullbackData.isoOfData` between two identifications of descent data over `V` with pullbacks
along `q`, the canonical one `Obj.pullbackData` and `Obj.toObjPullbackData q M`, whose
identifications are composites of the comparison isomorphisms `F.mapComp'`. The unit and
composition conditions reduce, through the transport rules of
`TauCeti.CategoryTheory.Sites.Descent.Stackification.Pseudofunctor`, to the facts that embedding
the unit and composition isomorphisms of `F` transports identities
(`Obj.transport_toObjPullbackData_refl`, `Obj.transport_toObjPullbackData_trans`).

Every object of the stackification is locally in the image of the unit: the pullback of a descent
datum `A` along a member `A.f i` of its covering family is the embedding of `A.D.obj i`
(`Obj.toObjIsoPullObj`), so the pullback of `A` along every member of the covering sieve of `A`
is in the essential image of `toObjFunctor` (`TauCeti.Stack.stackification_locally_essSurj`).
Together with the full faithfulness of `toObjFunctor` (`Obj.fullyFaithfulToObjFunctor`), this is
the part of Stacks, Lemma 02ZN describing the unit. The universal property of the unit with respect
to stacks and the stack property of `stackification J F` are not proved here.

## Main declarations

* `TauCeti.Stack.toStackification`: the unit `F ⟶ stackification J F`.
* `TauCeti.Stack.toStackificationNatIso`: its naturality isomorphisms, for arbitrary universes.
* `TauCeti.Stack.stackification_locally_essSurj`: every descent datum is locally in the image of
  the unit.

## References

* [Stacks Project, Lemma 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
-/

public section

noncomputable section

universe w v' u' v u

open CategoryTheory Limits Opposite Bicategory Pseudofunctor LocallyDiscreteOpToCat

namespace TauCeti.Stack.Stackification.Obj

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- The identification of `b^* ((𝟙 V)^* (q^* M))` with `c^* ((𝟙 U)^* M)` for `b ≫ q = c`. -/
def toObjPullbackIso {U V : C} (q : V ⟶ U) (M : F.obj (.mk (op U))) ⦃T : C⦄ (b : T ⟶ V)
    (c : T ⟶ U) (h : b ≫ q = c) :
    (F.map b.op.toLoc).toFunctor.obj
        ((F.map (𝟙 V).op.toLoc).toFunctor.obj ((F.map q.op.toLoc).toFunctor.obj M)) ≅
      (F.map c.op.toLoc).toFunctor.obj ((F.map (𝟙 U).op.toLoc).toFunctor.obj M) :=
  (Cat.Hom.toNatIso (F.mapComp' (𝟙 V).op.toLoc b.op.toLoc b.op.toLoc (by simp))).symm.app _ ≪≫
    (Cat.Hom.toNatIso (F.mapComp' q.op.toLoc b.op.toLoc c.op.toLoc
      (by rw [← h]; rfl))).symm.app M ≪≫
    (Cat.Hom.toNatIso (F.mapComp' (𝟙 U).op.toLoc c.op.toLoc c.op.toLoc (by simp))).app M

lemma toObjPullbackIso_hom {U V : C} (q : V ⟶ U) (M : F.obj (.mk (op U))) ⦃T : C⦄ (b : T ⟶ V)
    (c : T ⟶ U) (h : b ≫ q = c) :
    (toObjPullbackIso q M b c h).hom =
      (F.mapComp' (𝟙 V).op.toLoc b.op.toLoc b.op.toLoc (by simp)).inv.toNatTrans.app _ ≫
      (F.mapComp' q.op.toLoc b.op.toLoc c.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app M ≫
      (F.mapComp' (𝟙 U).op.toLoc c.op.toLoc c.op.toLoc (by simp)).hom.toNatTrans.app M :=
  (rfl)

/-- The identifications `toObjPullbackIso` are natural in `M`. -/
@[reassoc]
lemma toObjPullbackIso_hom_naturality {U V : C} (q : V ⟶ U) {M M' : F.obj (.mk (op U))}
    (φ : M ⟶ M') ⦃T : C⦄ (b : T ⟶ V) (c : T ⟶ U) (h : b ≫ q = c) :
    (F.map b.op.toLoc).toFunctor.map
        ((F.map (𝟙 V).op.toLoc).toFunctor.map ((F.map q.op.toLoc).toFunctor.map φ)) ≫
      (toObjPullbackIso q M' b c h).hom =
    (toObjPullbackIso q M b c h).hom ≫
      (F.map c.op.toLoc).toFunctor.map ((F.map (𝟙 U).op.toLoc).toFunctor.map φ) := by
  rw [toObjPullbackIso_hom, toObjPullbackIso_hom]
  simp only [Category.assoc, mapComp'_inv_naturality_assoc, mapComp'_hom_naturality]

/-- Along the identity, `toObjPullbackIso` is the pullback of the unit isomorphism of `F`. -/
lemma toObjPullbackIso_id_hom {U : C} (M : F.obj (.mk (op U))) ⦃T : C⦄ (b : T ⟶ U) :
    (toObjPullbackIso (𝟙 U) M b b (Category.comp_id b)).hom =
      (F.map b.op.toLoc).toFunctor.map ((F.map (𝟙 U).op.toLoc).toFunctor.map
        ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M)) := by
  rw [toObjPullbackIso_hom, Cat.Hom.inv_hom_id_toNatTrans_app]
  erw [Category.comp_id]
  have h₁ := F.mapComp'_id_comp_inv_app (b₀ := .mk (op U)) b.op.toLoc
    ((F.map (𝟙 U).op.toLoc).toFunctor.obj M)
  rw [← mapId'_eq_mapId] at h₁
  have h₂ : (F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app
      ((F.map (𝟙 U).op.toLoc).toFunctor.obj M) = (F.map (𝟙 U).op.toLoc).toFunctor.map
        ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M) := by
    rw [← cancel_mono ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M)]
    exact (F.mapId'_hom_naturality _ _ _).symm
  exact h₁.trans ((F.map b.op.toLoc).toFunctor.congr_map h₂)

/-- The identifications `toObjPullbackIso` are compatible with the composition isomorphisms
of `F`. -/
lemma toObjPullbackIso_comp_hom {U V W : C} (q : V ⟶ U) (r : W ⟶ V) (M : F.obj (.mk (op U)))
    ⦃T : C⦄ (b : T ⟶ W) (c : T ⟶ U) (h : b ≫ r ≫ q = c) :
    (F.map b.op.toLoc).toFunctor.map ((F.map (𝟙 W).op.toLoc).toFunctor.map
        ((F.mapComp' q.op.toLoc r.op.toLoc (r ≫ q).op.toLoc rfl).hom.toNatTrans.app M)) ≫
      (toObjPullbackIso r ((F.map q.op.toLoc).toFunctor.obj M) b (b ≫ r) rfl).hom ≫
      (toObjPullbackIso q M (b ≫ r) c (by rw [← h, Category.assoc])).hom =
    (toObjPullbackIso (r ≫ q) M b c h).hom := by
  simp only [toObjPullbackIso_hom, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  erw [mapComp'_inv_naturality_assoc]
  rw [← F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc q.op.toLoc r.op.toLoc b.op.toLoc
    (r ≫ q).op.toLoc (b ≫ r).op.toLoc c.op.toLoc rfl rfl (by rw [← h]; rfl)]
  rw [← Functor.map_comp_assoc, Cat.Hom.hom_inv_id_toNatTrans_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

private lemma comp_hom_hom_inv_inv {D : Type*} [Category* D] {X Y Z Z' : D} (x : X ⟶ Y)
    (a : Y ≅ Z) (b : Z ≅ Z') : (x ≫ a.hom ≫ b.hom) ≫ b.inv ≫ a.inv = x := by
  simp

variable [HasPullbacks C] [F.IsPrestack J]

/-- The local evaluations of the image of a morphism under `toObjFunctor`. -/
lemma app_toObjFunctor_map {U : C} {M M' : F.obj (.mk (op U))} (φ : M ⟶ M') ⦃T : C⦄
    (a b : T ⟶ U) (w : a ≫ 𝟙 U = b ≫ 𝟙 U) :
    Hom.app ((toObjFunctor.{w} J F U).map φ) (i := PUnit.unit) (j := PUnit.unit) a b w =
      (F.map a.op.toLoc).toFunctor.map ((F.map (𝟙 U).op.toLoc).toFunctor.map φ) ≫
        ((toObjFunctor.{w} J F U).obj M').D.hom (i₁ := PUnit.unit) (i₂ := PUnit.unit) (a ≫ 𝟙 U)
          a b rfl w.symm :=
  app_ofDescentDataMap (J := J) (hf := ofArrows_id_mem.{w} U)
    ((F.toDescentData (fun _ : PUnit.{w + 1} ↦ 𝟙 U)).map φ) (i := PUnit.unit) (j := PUnit.unit)
    a b w

/-- The descent datum given by `q^* M` over `V` is identified with the pullback along `q` of the
descent datum given by `M` over `U`. -/
-- The body is exposed so that the index map and the morphisms `β` are definitionally the identity
-- and `q`, as needed to state `toObjPullbackData_iso`.
@[expose] def toObjPullbackData {U V : C} (q : V ⟶ U) (M : F.obj (.mk (op U))) :
    PullbackData q ((toObjFunctor.{w} J F U).obj M)
      ((toObjFunctor.{w} J F V).obj ((F.map q.op.toLoc).toFunctor.obj M)) where
  α j := j
  β _ := q
  w _ := by simp
  iso T _ b c h := toObjPullbackIso q M b c h
  pullHom_iso T _ b c h T' g gb gc hgb hgc := by
    rw [toObjPullbackIso_hom, toObjPullbackIso_hom]
    erw [pullHom_comp (f₂ := b) (M₂ := (F.map q.op.toLoc).toFunctor.obj M) _ _ g gb gb gc hgb
      hgb hgc, pullHom_comp (f₂ := c) (M₂ := M) _ _ g gb gc gc hgb hgc hgc]
    erw [pullHom_mapComp'_inv, pullHom_mapComp'_inv, pullHom_mapComp'_hom]
    all_goals first | rfl | exact h | simp
  hom_eq T j j' q' b b' hb hb' c c' h h' := by
    obtain rfl : b = q' := by simpa using hb
    obtain rfl : b' = b := by simpa using hb'
    obtain rfl : c' = c := h'.symm.trans h
    rw [DescentData.hom_self _ _ _ hb]
    erw [DescentData.hom_self _ _ _ rfl, Category.id_comp]
    exact (toObjPullbackIso q M b' c' h).hom_inv_id.symm

open PullbackData

/-- The identifications of `toObjPullbackData` are the isomorphisms `toObjPullbackIso`. -/
lemma toObjPullbackData_iso {U V : C} (q : V ⟶ U) (M : F.obj (.mk (op U))) ⦃T : C⦄
    (b : T ⟶ V) (c : T ⟶ U) (h : b ≫ q = c) :
    (toObjPullbackData.{w} (J := J) q M).iso (j := PUnit.unit) b c h = toObjPullbackIso q M b c h :=
  (rfl)

/-- Pulling back a morphism along `q` and embedding it is transporting its embedding along
`toObjPullbackData`. -/
lemma toObjFunctor_map_map {U V : C} (q : V ⟶ U) {M M' : F.obj (.mk (op U))} (φ : M ⟶ M') :
    (toObjFunctor.{w} J F V).map ((F.map q.op.toLoc).toFunctor.map φ) =
      transport (toObjPullbackData q M) (toObjPullbackData q M')
        ((toObjFunctor.{w} J F U).map φ) :=
  hom_ext fun T i j b b' w ↦ by
    cases i; cases j
    obtain rfl : b = b' := by simpa using w
    rw [app_transport _ _ _ _ _ _ _ _ rfl rfl, transportApp_def]
    erw [app_toObjFunctor_map, app_toObjFunctor_map, toObjPullbackData_iso,
      toObjPullbackData_iso]
    erw [DescentData.hom_self _ _ _ rfl, DescentData.hom_self _ _ _ rfl, Category.comp_id,
      Category.comp_id, ← toObjPullbackIso_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Embedding the unit isomorphism `(𝟙 U)^* M ⟶ M` of `F` is transporting the identity along
`toObjPullbackData (𝟙 U) M` and `PullbackData.refl`. -/
lemma transport_toObjPullbackData_refl {U : C} (M : F.obj (.mk (op U))) :
    transport (toObjPullbackData (𝟙 U) M) (refl _) (𝟙 _) =
      (toObjFunctor.{w} J F U).map ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M) :=
  hom_ext fun T i j b b' w ↦ by
    cases i; cases j
    obtain rfl : b = b' := by simpa using w
    refine (app_transport (toObjPullbackData (𝟙 U) M) (refl _) (𝟙 _) b b w b b
      (Category.comp_id b) (Category.comp_id b)).trans ?_
    erw [transportApp_def, app_toObjFunctor_map, toObjPullbackData_iso, id_app]
    simp only [PullbackData.refl, DescentData.iso_inv]
    erw [DescentData.hom_self _ _ _ rfl]
    erw [Category.comp_id]
    exact (Category.comp_id _).trans ((toObjPullbackIso_id_hom M b).trans (Category.comp_id _).symm)

/-- Embedding the composition isomorphism `(r ≫ q)^* M ⟶ r^* (q^* M)` of `F` is transporting the
identity along `toObjPullbackData (r ≫ q) M` and the composite of `toObjPullbackData r (q^* M)` and
`toObjPullbackData q M`. -/
lemma transport_toObjPullbackData_trans {U V W : C} (q : V ⟶ U) (r : W ⟶ V)
    (M : F.obj (.mk (op U))) :
    transport (toObjPullbackData (r ≫ q) M)
        ((toObjPullbackData r ((F.map q.op.toLoc).toFunctor.obj M)).trans
          (toObjPullbackData q M) (r ≫ q) rfl) (𝟙 _) =
      (toObjFunctor.{w} J F W).map
        ((F.mapComp' q.op.toLoc r.op.toLoc (r ≫ q).op.toLoc rfl).hom.toNatTrans.app M) :=
  hom_ext fun T i j b b' w ↦ by
    cases i; cases j
    obtain rfl : b = b' := by simpa using w
    refine (app_transport (toObjPullbackData (r ≫ q) M)
      ((toObjPullbackData r ((F.map q.op.toLoc).toFunctor.obj M)).trans
        (toObjPullbackData q M) (r ≫ q) rfl) (𝟙 _) b b w (b ≫ r ≫ q) (b ≫ r ≫ q)
      rfl rfl).trans ?_
    erw [transportApp_def, app_toObjFunctor_map, toObjPullbackData_iso, id_app]
    simp only [PullbackData.trans, Iso.trans_inv]
    erw [DescentData.hom_self _ _ _ rfl]
    erw [DescentData.hom_self _ _ _ rfl, toObjPullbackData_iso, toObjPullbackData_iso]
    erw [Category.id_comp, Category.comp_id, ← toObjPullbackIso_comp_hom q r M b _ rfl]
    exact comp_hom_hom_inv_inv _ _ _

/-- The pullback of a descent datum `A` along a member `A.f i` of its covering family is
identified with the descent datum along the identity given by `A.D.obj i`. -/
-- The body is exposed so that the morphisms `β` are definitionally identities when the
-- compatibility with the descent data is checked.
@[expose] def selfPullbackData {U : C} (A : Obj.{w} J F U) (i : A.ι) :
    PullbackData (A.f i) A ((toObjFunctor.{w} J F (A.X i)).obj (A.D.obj i)) where
  α _ := i
  β _ := 𝟙 _
  w _ := rfl
  iso T _ b c h :=
    (Cat.Hom.toNatIso (F.mapComp' (𝟙 (A.X i)).op.toLoc b.op.toLoc c.op.toLoc
      (by rw [← h]; rfl))).symm.app (A.D.obj i)
  pullHom_iso T _ b c h T' g gb gc hgb hgc := pullHom_mapComp'_inv _ _ _ _ h _ _ _ hgb hgc
  hom_eq T j j' q' b b' hb hb' c c' h h' := by
    cases j; cases j'
    have e₁ : b = q' := by simpa using hb
    have e₂ : b' = q' := by simpa using hb'
    have e₃ : b = c := by simpa using h
    have e₄ : b' = c' := by simpa using h'
    subst e₁ e₃ e₄ e₂
    erw [DescentData.hom_self _ _ _ rfl, DescentData.hom_self _ _ _ hb, Category.id_comp]
    exact (Iso.hom_inv_id _).symm

/-- The pullback of a descent datum `A` along a member `A.f i` of its covering family is
isomorphic to the image of `A.D.obj i` under `toObjFunctor`. -/
def toObjIsoPullObj {U : C} (A : Obj.{w} J F U) (i : A.ι) :
    (toObjFunctor.{w} J F (A.X i)).obj (A.D.obj i) ≅ pullObj (A.f i) A :=
  isoOfData (selfPullbackData A i) (pullbackData (A.f i) A)

end TauCeti.Stack.Stackification.Obj

namespace TauCeti.Stack

open Stackification Obj PullbackData

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasPullbacks C]

section

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) [F.IsPrestack J]

/-- The naturality isomorphisms of the unit of the stackification: for `q : V ⟶ U`, embedding
`q^* M` is isomorphic to pulling back the embedding of `M` along `q`. -/
def toStackificationNatIso {U V : C} (q : V ⟶ U) :
    (F.map q.op.toLoc).toFunctor ⋙ toObjFunctor.{w} J F V ≅
      toObjFunctor.{w} J F U ⋙ pullFunctor J F q :=
  NatIso.ofComponents (fun M ↦ isoOfData (toObjPullbackData q M) (pullbackData q _))
    fun {M M'} φ ↦ by
      rw [isoOfData_hom, isoOfData_hom]
      erw [toObjFunctor_map_map, pullFunctor_map]
      rw [transport_comp, transport_comp, Category.comp_id, Category.id_comp]

/-- The components of `toStackificationNatIso` are transports of identities. -/
lemma toStackificationNatIso_hom_app {U V : C} (q : V ⟶ U) (M : F.obj (.mk (op U))) :
    (toStackificationNatIso.{w} J F q).hom.app M =
      transport (toObjPullbackData q M) (pullbackData q _) (𝟙 _) := by
  simp only [toStackificationNatIso, NatIso.ofComponents_hom_app, isoOfData_hom]

/-- The unit condition for the naturality isomorphisms `toStackificationNatIso`. -/
lemma toStackificationNatIso_hom_app_comp_pullFunctorId_hom_app {U : C}
    (M : F.obj (.mk (op U))) :
    (toStackificationNatIso.{w} J F (𝟙 U)).hom.app M ≫
        (pullFunctorId J F U).hom.app ((toObjFunctor.{w} J F U).obj M) =
      (toObjFunctor.{w} J F U).map ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M) := by
  rw [toStackificationNatIso_hom_app, pullFunctorId_hom_app, transport_comp, Category.comp_id,
    transport_toObjPullbackData_refl]

/-- The composition condition for the naturality isomorphisms `toStackificationNatIso`. -/
lemma toStackificationNatIso_hom_app_comp_pullFunctorComp_hom_app {U V W : C} (q : V ⟶ U)
    (r : W ⟶ V) (M : F.obj (.mk (op U))) :
    (toStackificationNatIso.{w} J F (r ≫ q)).hom.app M ≫
        (pullFunctorComp J F q r (r ≫ q) rfl).hom.app ((toObjFunctor.{w} J F U).obj M) =
      (toObjFunctor.{w} J F W).map
          ((F.mapComp' q.op.toLoc r.op.toLoc (r ≫ q).op.toLoc rfl).hom.toNatTrans.app M) ≫
        (toStackificationNatIso.{w} J F r).hom.app ((F.map q.op.toLoc).toFunctor.obj M) ≫
          (pullFunctor J F r).map ((toStackificationNatIso.{w} J F q).hom.app M) := by
  rw [toStackificationNatIso_hom_app, toStackificationNatIso_hom_app,
    toStackificationNatIso_hom_app, pullFunctorComp_hom_app, transport_comp, Category.comp_id,
    pullFunctor_map, transport_transport _ _ _ _ _ (r ≫ q) rfl,
    ← transport_id (toObjPullbackData q M),
    transport_transport _ _ _ _ _ (r ≫ q) rfl, transport_comp, Category.comp_id,
    ← transport_toObjPullbackData_trans, transport_comp, Category.comp_id]
  rfl

/-- Every descent datum `A` over `U` is locally in the image of `toObjFunctor`: its pullback
along every member of the covering sieve generated by its covering family is isomorphic to the
descent datum given by an object of `F` (part of Stacks, Lemma 02ZN). -/
theorem stackification_locally_essSurj {U : C} (A : Obj.{w} J F U) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (g : V ⟶ U), R g →
      ∃ M : F.obj (.mk (op V)), Nonempty ((pullFunctor J F g).obj A ≅
        (toObjFunctor.{w} J F V).obj M) := by
  refine ⟨_, A.mem, fun V g hg ↦ ?_⟩
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  exact ⟨(F.map h.op.toLoc).toFunctor.obj (A.D.obj i),
    ⟨(pullFunctorComp J F (A.f i) h _ rfl).app A ≪≫
      (pullFunctor J F h).mapIso (toObjIsoPullObj A i).symm ≪≫
      (toStackificationNatIso.{w} J F h).symm.app (A.D.obj i)⟩⟩

end

section

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max w v', max (w + 1) u v v' u'}) [F.IsPrestack J]

/-- The unit `F ⟶ stackification J F` of the stackification of a prestack `F`, as a strong
transformation: its component at `U` embeds the fibre of `F` over `U` as the descent data along
the identity of `U` (`Stackification.Obj.toObjFunctor`). -/
-- The body is exposed so that the components and naturality isomorphisms are definitionally
-- `toObjFunctor` and `toStackificationNatIso`, as needed to state the component formulas below.
@[expose] def toStackification :
    StrongTrans F (stackification.{w, max w v', max (w + 1) u v v' u', v, u} J F) where
  app a := (toObjFunctor.{w} J F a.as.unop).toCatHom
  naturality f := Cat.Hom.isoMk (toStackificationNatIso.{w} J F f.as.unop)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    exact Bicategory.id_whiskerRight_comp_eq_comp_whiskerLeft_id _ _ _ _ _
  naturality_id a := by
    refine Cat.Hom₂.ext.{max w v', max (w + 1) u v v' u'} (NatTrans.ext (funext fun M ↦ ?_))
    have h := toStackificationNatIso_hom_app_comp_pullFunctorId_hom_app.{w} (J := J) (F := F)
      (U := a.as.unop) M
    rw [show F.mapId' (𝟙 a.as.unop).op.toLoc (by simp) = F.mapId a from F.mapId'_eq_mapId a] at h
    refine h.trans ?_
    change _ = _ ≫ 𝟙 _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact (Category.comp_id _).symm
  naturality_comp f g := by
    refine Cat.Hom₂.ext.{max w v', max (w + 1) u v v' u'} (NatTrans.ext (funext fun M ↦ ?_))
    have h := toStackificationNatIso_hom_app_comp_pullFunctorComp_hom_app.{w} (J := J) (F := F)
      f.as.unop g.as.unop M
    rw [show F.mapComp' f.as.unop.op.toLoc g.as.unop.op.toLoc (g.as.unop ≫ f.as.unop).op.toLoc rfl =
      F.mapComp f g from F.mapComp'_eq_mapComp f g] at h
    refine h.trans ?_
    change _ = _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    rfl

/-- The component of the unit at `U` is the embedding `toObjFunctor`. -/
@[simp]
lemma toStackification_app_toFunctor (a : LocallyDiscrete Cᵒᵖ) :
    ((toStackification.{w, v', u'} J F).app a).toFunctor = toObjFunctor.{w} J F a.as.unop :=
  (rfl)

/-- The naturality isomorphisms of the unit are the isomorphisms `toStackificationNatIso`. -/
@[simp]
lemma toStackification_naturality_hom_toNatTrans_app {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (M : F.obj a) :
    ((toStackification.{w, v', u'} J F).naturality f).hom.toNatTrans.app M =
      (toStackificationNatIso.{w} J F f.as.unop).hom.app M :=
  (rfl)

/-- The inverse naturality isomorphisms of the unit are those of `toStackificationNatIso`. -/
@[simp]
lemma toStackification_naturality_inv_toNatTrans_app {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (M : F.obj a) :
    ((toStackification.{w, v', u'} J F).naturality f).inv.toNatTrans.app M =
      (toStackificationNatIso.{w} J F f.as.unop).inv.app M :=
  (rfl)

end

end TauCeti.Stack

end
