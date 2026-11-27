/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.StrongTrans

/-!
# Precomposition with a locally essentially surjective strong transformation

Let `η : F ⟶ P` be a strong transformation of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` which is
locally essentially surjective for a Grothendieck topology `J` (`StrongTrans.IsLocallyEssSurj`):
every object of `P` over `U` is isomorphic to an image under `η` after pullback along every arrow
of some covering sieve of `U`. For a prestack `G` for `J`, precomposition with `η`,
`Bicategory.precomp G η : (P ⟶ G) ⥤ (F ⟶ G)`, sends a modification `Δ : Φ ⟶ Φ'` to its
restriction `η ◁ Δ`. This file shows that it is faithful (`StrongTrans.faithful_precomp`), and
full when the components of `η` are full (`StrongTrans.full_precomp`).

A component of `Δ` at an object `A` of `P` over `U` is determined by its pullbacks along a covering
sieve of `U`, as `G` is a prestack; along the arrows `g` of the sieve on which `g^* A` is in the
essential image of `η`, these pullbacks are determined by the naturality of `Δ` and by its values
at images under `η`, that is, by `η ◁ Δ`. Conversely, when the components of `η` are full, the
components of a modification `Γ : η ≫ Φ ⟶ η ≫ Φ'` are natural with respect to all morphisms
between images under `η`, so they extend to the objects in the essential image of `η`, and these
extensions glue along the covering sieves to a modification `Φ ⟶ Φ'` restricting to `Γ`.

Applied to the unit of the stackification of a prestack, which has fully faithful components and
is locally essentially surjective, this gives the full faithfulness part of the universal property
of the stackification (`TauCeti.Stack.stackificationUniversal`).

## Main declarations

* `CategoryTheory.Pseudofunctor.StrongTrans.IsLocallyEssSurj`: local essential surjectivity
  of a strong transformation for a Grothendieck topology.
* `CategoryTheory.Pseudofunctor.StrongTrans.localImageSieve`: the sieve of arrows along which an
  object of `G` lifts along `η` up to isomorphism; `η` is locally essentially surjective exactly
  when these sieves are covering (`isLocallyEssSurj_iff_localImageSieve_mem`).
* `CategoryTheory.Pseudofunctor.StrongTrans.faithful_precomp`,
  `CategoryTheory.Pseudofunctor.StrongTrans.full_precomp`: precomposition with a locally
  essentially surjective strong transformation, respectively one whose components are also full,
  is faithful, respectively full, on strong transformations into a prestack.

## References

* [Stacks Project, Lemma 0435](https://stacks.math.columbia.edu/tag/0435)
-/

public section

noncomputable section

universe v' u' v u

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- A strong transformation `η : F ⟶ G` is *locally essentially surjective* for a Grothendieck
topology `J` if every object of `G` over `U` lifts along `η` up to isomorphism after pullback
along every arrow of some `J`-covering sieve of `U`. -/
class IsLocallyEssSurj (η : StrongTrans F G) (J : GrothendieckTopology C) : Prop where
  /-- Every object `y` of `G` over `U` lifts along `η`, up to isomorphism, after pullback along
  every arrow of some covering sieve of `U`. -/
  exists_covering_lift {U : C} (y : G.obj (.mk (op U))) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f → ∃ x : F.obj (.mk (op V)),
      Nonempty ((η.app (.mk (op V))).toFunctor.obj x ≅ (G.map f.op.toLoc).toFunctor.obj y)

section LocalImageSieve

variable {J : GrothendieckTopology C} (η : StrongTrans F G)

/-- An isomorphism `e : G(g)(η_V x) ≅ G(g)(G(f) z)` between the restrictions along `g : W ⟶ V`
of `η_V x` and `G(f) z` gives an isomorphism `η_W (F(g) x) ≅ G(g ≫ f) z`, through `c_g(x)` and
the composition isomorphism of `G`. -/
noncomputable def restrictImageIso {U V W : C} {z : G.obj (.mk (op U))} {f : V ⟶ U}
    {x : F.obj (.mk (op V))} (g : W ⟶ V)
    (e : (G.map g.op.toLoc).toFunctor.obj ((η.app (.mk (op V))).toFunctor.obj x) ≅
      (G.map g.op.toLoc).toFunctor.obj ((G.map f.op.toLoc).toFunctor.obj z)) :
    (η.app (.mk (op W))).toFunctor.obj ((F.map g.op.toLoc).toFunctor.obj x) ≅
      (G.map (g ≫ f).op.toLoc).toFunctor.obj z :=
  η.naturalityObjIso g.op.toLoc x ≪≫ e ≪≫
    ((Cat.Hom.toNatIso (G.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc)).app z).symm

/-- The forward arrow of `restrictImageIso`, as the composite of its three factors. -/
theorem restrictImageIso_hom {U V W : C} {z : G.obj (.mk (op U))} {f : V ⟶ U}
    {x : F.obj (.mk (op V))} (g : W ⟶ V)
    (e : (G.map g.op.toLoc).toFunctor.obj ((η.app (.mk (op V))).toFunctor.obj x) ≅
      (G.map g.op.toLoc).toFunctor.obj ((G.map f.op.toLoc).toFunctor.obj z)) :
    (η.restrictImageIso g e).hom =
      (η.naturalityObjIso g.op.toLoc x).hom ≫ e.hom ≫
        (G.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc).inv.toNatTrans.app z := by
  simp [restrictImageIso]

/-- The **local-image sieve** of `z` over `U`: the arrows `f : V ⟶ U` such that `G(f) z` is
isomorphic to the image `η_V x` of some object `x` over `V`, that is, lies in the essential image
of `η_V`. -/
def localImageSieve {U : C} (z : G.obj (.mk (op U))) : Sieve U where
  arrows V f := (η.app (.mk (op V))).toFunctor.essImage ((G.map f.op.toLoc).toFunctor.obj z)
  downward_closed := fun ⟨_, ⟨e⟩⟩ g ↦
    ⟨_, ⟨η.restrictImageIso g ((G.map g.op.toLoc).toFunctor.mapIso e)⟩⟩

theorem mem_localImageSieve_iff {U V : C} (z : G.obj (.mk (op U))) (f : V ⟶ U) :
    η.localImageSieve z f ↔ ∃ x : F.obj (.mk (op V)),
      Nonempty ((η.app (.mk (op V))).toFunctor.obj x ≅ (G.map f.op.toLoc).toFunctor.obj z) :=
  Iff.rfl

/-- The identity of `U` lies in the local-image sieve of `z` exactly when `z` is isomorphic to
`η_U y` for some `y` over `U`. -/
theorem id_mem_localImageSieve_iff {U : C} (z : G.obj (.mk (op U))) :
    η.localImageSieve z (𝟙 U) ↔
      ∃ y : F.obj (.mk (op U)), Nonempty ((η.app (.mk (op U))).toFunctor.obj y ≅ z) := by
  let d := (Cat.Hom.toNatIso (G.mapId' (𝟙 U).op.toLoc (by simp))).app z
  exact ⟨fun ⟨y, ⟨e⟩⟩ ↦ ⟨y, ⟨e ≪≫ d⟩⟩, fun ⟨y, ⟨e⟩⟩ ↦ ⟨y, ⟨e ≪≫ d.symm⟩⟩⟩

/-- A strong transformation is locally essentially surjective exactly when the local-image sieve
of every object of `G` is covering. -/
theorem isLocallyEssSurj_iff_localImageSieve_mem :
    η.IsLocallyEssSurj J ↔ ∀ {U : C} (z : G.obj (.mk (op U))), η.localImageSieve z ∈ J U :=
  ⟨fun _ _ z ↦
    have ⟨_, hR, h⟩ := IsLocallyEssSurj.exists_covering_lift (η := η) (J := J) z
    J.superset_covering (fun _ f hf ↦ h f hf) hR,
    fun h ↦ ⟨fun z ↦ ⟨_, h z, fun _ _ hf ↦ hf⟩⟩⟩

variable (J) in
/-- **The local-image sieve is covering** when `η` is locally essentially surjective, in
particular when `F` and `G` are gerbes (`StrongTrans.isLocallyEssSurj_of_isGerbe`). -/
theorem localImageSieve_mem [η.IsLocallyEssSurj J] {U : C} (z : G.obj (.mk (op U))) :
    η.localImageSieve z ∈ J U :=
  (η.isLocallyEssSurj_iff_localImageSieve_mem.1 inferInstance) z

end LocalImageSieve

variable {P : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {η : F ⟶ P} {Φ Φ' : P ⟶ G} (Γ : η ≫ Φ ⟶ η ≫ Φ')

/-- The component at `M` of a modification `Γ : η ≫ Φ ⟶ η ≫ Φ'`, with its source and target
written as images of `η M`. -/
private def appObj {a : LocallyDiscrete Cᵒᵖ} (M : F.obj a) :
    (Φ.app a).toFunctor.obj ((η.app a).toFunctor.obj M) ⟶
      (Φ'.app a).toFunctor.obj ((η.app a).toFunctor.obj M) :=
  (Γ.as.app a).toNatTrans.app M

/-- The naturality square of a modification `Γ : η ≫ Φ ⟶ η ≫ Φ'` along `f`, on an object. -/
private lemma appObj_comp_naturalityObjIso_hom {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (M : F.obj a) :
    appObj Γ ((F.map f).toFunctor.obj M) ≫ (Φ'.app b).toFunctor.map (η.naturalityObjIso f M).hom ≫
        (Φ'.naturalityObjIso f ((η.app a).toFunctor.obj M)).hom =
      (Φ.app b).toFunctor.map (η.naturalityObjIso f M).hom ≫
        (Φ.naturalityObjIso f ((η.app a).toFunctor.obj M)).hom ≫
          (G.map f).toFunctor.map (appObj Γ M) := by
  have h := app_comp_naturalityObjIso_hom Γ f M
  simp only [naturalityObjIso_hom, comp_naturality_hom_app] at h
  rw [naturalityObjIso_hom, naturalityObjIso_hom, naturalityObjIso_hom]
  -- `h` is the claim, up to unfolding `appObj` and the composites in `Cat`.
  exact h.trans (Category.assoc _ _ _)

/-- The pullback along `f` of a component of a modification `Γ : η ≫ Φ ⟶ η ≫ Φ'`. -/
private lemma map_appObj {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (M : F.obj a) :
    (G.map f).toFunctor.map (appObj Γ M) =
      (Φ.naturalityObjIso f ((η.app a).toFunctor.obj M)).inv ≫
        (Φ.app b).toFunctor.map (η.naturalityObjIso f M).inv ≫
          appObj Γ ((F.map f).toFunctor.obj M) ≫
            (Φ'.app b).toFunctor.map (η.naturalityObjIso f M).hom ≫
              (Φ'.naturalityObjIso f ((η.app a).toFunctor.obj M)).hom := by
  rw [appObj_comp_naturalityObjIso_hom, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]

/-- The value at an object in the essential image of `η` of the modification `Φ ⟶ Φ'` extending
`Γ : η ≫ Φ ⟶ η ≫ Φ'`. -/
private def localApp {a : LocallyDiscrete Cᵒᵖ} {B : P.obj a}
    (hB : (η.app a).toFunctor.essImage B) :
    (Φ.app a).toFunctor.obj B ⟶ (Φ'.app a).toFunctor.obj B :=
  (Φ.app a).toFunctor.map hB.getIso.inv ≫ appObj Γ hB.witness ≫
    (Φ'.app a).toFunctor.map hB.getIso.hom

section Full

variable [∀ a, (η.app a).toFunctor.Full]

/-- The components of a modification `Γ : η ≫ Φ ⟶ η ≫ Φ'` are natural with respect to all
morphisms between objects in the image of `η`, not only images of morphisms. -/
private lemma appObj_naturality {a : LocallyDiscrete Cᵒᵖ} {M M' : F.obj a}
    (z : (η.app a).toFunctor.obj M ⟶ (η.app a).toFunctor.obj M') :
    (Φ.app a).toFunctor.map z ≫ appObj Γ M' = appObj Γ M ≫ (Φ'.app a).toFunctor.map z := by
  obtain ⟨y, rfl⟩ := (η.app a).toFunctor.map_surjective z
  exact (Γ.as.app a).toNatTrans.naturality y

/-- `localApp` may be computed from any presentation of its object as an image under `η`. -/
private lemma localApp_eq {a : LocallyDiscrete Cᵒᵖ} {B : P.obj a}
    (hB : (η.app a).toFunctor.essImage B) {M : F.obj a} (e : (η.app a).toFunctor.obj M ≅ B) :
    localApp Γ hB = (Φ.app a).toFunctor.map e.inv ≫ appObj Γ M ≫
      (Φ'.app a).toFunctor.map e.hom := by
  have h := appObj_naturality Γ (hB.getIso.hom ≫ e.inv)
  have he : e.inv = hB.getIso.inv ≫ hB.getIso.hom ≫ e.inv := by simp
  rw [localApp, he, Functor.map_comp, Category.assoc, reassoc_of% h, ← Functor.map_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The values `localApp` are natural. -/
private lemma localApp_naturality {a : LocallyDiscrete Cᵒᵖ} {B B' : P.obj a}
    (hB : (η.app a).toFunctor.essImage B) (hB' : (η.app a).toFunctor.essImage B') (x : B ⟶ B') :
    (Φ.app a).toFunctor.map x ≫ localApp Γ hB' = localApp Γ hB ≫ (Φ'.app a).toFunctor.map x := by
  have h := appObj_naturality Γ (hB.getIso.hom ≫ x ≫ hB'.getIso.inv)
  have hx : x ≫ hB'.getIso.inv = hB.getIso.inv ≫ hB.getIso.hom ≫ x ≫ hB'.getIso.inv := by simp
  rw [localApp, localApp, ← Functor.map_comp_assoc, hx, Functor.map_comp, Category.assoc,
    reassoc_of% h]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]

/-- The values `localApp` are compatible with pullbacks. -/
private lemma map_localApp {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) {B : P.obj a}
    (hB : (η.app a).toFunctor.essImage B) :
    (G.map f).toFunctor.map (localApp Γ hB) =
      (Φ.naturalityObjIso f B).inv ≫ localApp Γ (map_obj_mem_essImage η f hB) ≫
        (Φ'.naturalityObjIso f B).hom := by
  rw [localApp_eq Γ (map_obj_mem_essImage η f hB)
    (η.naturalityObjIso f _ ≪≫ (P.map f).toFunctor.mapIso hB.getIso), localApp]
  simp only [Functor.map_comp, map_appObj, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [naturalityObjIso_inv_naturality_assoc, naturalityObjIso_hom_naturality]

end Full

section Prestack

open LocallyDiscreteOpToCat

section Glue

variable [∀ a, (η.app a).toFunctor.Full]

/-- The local values `localApp` along the arrows of `η.localImageSieve A` are compatible. -/
private lemma pullHom_localApp {U T T' : C} (A : P.obj (.mk (op U))) (g : T ⟶ U)
    (hg : η.localImageSieve A g) (h : T' ⟶ T) :
    pullHom ((Φ.naturalityObjIso g.op.toLoc A).inv ≫ localApp Γ hg ≫
        (Φ'.naturalityObjIso g.op.toLoc A).hom) h (h ≫ g) (h ≫ g) =
      (Φ.naturalityObjIso (h ≫ g).op.toLoc A).inv ≫
        localApp Γ ((η.localImageSieve A).downward_closed hg h) ≫
          (Φ'.naturalityObjIso (h ≫ g).op.toLoc A).hom := by
  rw [pullHom_naturalityObjIso, map_localApp Γ h.op.toLoc hg]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% (localApp_naturality Γ ((η.localImageSieve A).downward_closed hg h)
    (map_obj_mem_essImage η h.op.toLoc hg) (P.compIso g.op h.op (h ≫ g).op op_comp.symm A).hom),
    ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]

variable (η) in
/-- The component at `A` of the modification `Φ ⟶ Φ'` extending `Γ : η ≫ Φ ⟶ η ≫ Φ'`, glued from
the local values `localApp`. -/
private lemma exists_glueApp (J : GrothendieckTopology C) [η.IsLocallyEssSurj J] [G.IsPrestack J]
    {U : C} (A : P.obj (.mk (op U))) :
    ∃ φ : (Φ.app _).toFunctor.obj A ⟶ (Φ'.app _).toFunctor.obj A,
      ∀ ⦃T : C⦄ (g : T ⟶ U) (hg : η.localImageSieve A g),
        (G.map g.op.toLoc).toFunctor.map φ = (Φ.naturalityObjIso g.op.toLoc A).inv ≫
          localApp Γ hg ≫ (Φ'.naturalityObjIso g.op.toLoc A).hom :=
  IsPrestack.exists_map_eq (η.localImageSieve_mem J A)
    (fun _ g hg ↦ (Φ.naturalityObjIso g.op.toLoc A).inv ≫ localApp Γ hg ≫
      (Φ'.naturalityObjIso g.op.toLoc A).hom)
    (fun _ g hg _ h _ _ e ↦ by
      subst e
      exact pullHom_localApp Γ A g hg h)

variable (J : GrothendieckTopology C) [η.IsLocallyEssSurj J] [G.IsPrestack J]

/-- The component at `A` of the modification `Φ ⟶ Φ'` extending `Γ : η ≫ Φ ⟶ η ≫ Φ'`. -/
private def glueApp {U : C} (A : P.obj (.mk (op U))) :
    (Φ.app _).toFunctor.obj A ⟶ (Φ'.app _).toFunctor.obj A :=
  (exists_glueApp η Γ J A).choose

/-- The pullbacks of the glued component are the local values `localApp`. -/
private lemma map_glueApp {U T : C} (A : P.obj (.mk (op U))) (g : T ⟶ U)
    (hg : η.localImageSieve A g) :
    (G.map g.op.toLoc).toFunctor.map (glueApp Γ J A) = (Φ.naturalityObjIso g.op.toLoc A).inv ≫
      localApp Γ hg ≫ (Φ'.naturalityObjIso g.op.toLoc A).hom :=
  (exists_glueApp η Γ J A).choose_spec g hg

/-- At an object in the essential image of `η`, the glued component is `localApp`. -/
private lemma glueApp_eq_localApp {U : C} {A : P.obj (.mk (op U))}
    (hA : (η.app _).toFunctor.essImage A) : glueApp Γ J A = localApp Γ hA :=
  IsPrestack.hom_ext (η.localImageSieve_mem J A) fun _ g hg ↦
    (map_glueApp Γ J A g hg).trans (map_localApp Γ g.op.toLoc hA).symm

/-- The glued components are natural. -/
private lemma glueApp_naturality {U : C} {A A' : P.obj (.mk (op U))} (x : A ⟶ A') :
    (Φ.app _).toFunctor.map x ≫ glueApp Γ J A' = glueApp Γ J A ≫ (Φ'.app _).toFunctor.map x :=
  IsPrestack.hom_ext
    (J.intersection_covering (η.localImageSieve_mem J A) (η.localImageSieve_mem J A'))
    fun _ g ⟨hg, hg'⟩ ↦ by
      rw [Functor.map_comp, Functor.map_comp, map_glueApp Γ J A g hg, map_glueApp Γ J A' g hg',
        naturalityObjIso_inv_naturality_assoc, reassoc_of% (localApp_naturality Γ hg hg'),
        Category.assoc, Category.assoc, naturalityObjIso_hom_naturality]

/-- The glued components are compatible with the naturality isomorphisms of `Φ` and `Φ'`. -/
private lemma glueApp_comp_naturalityObjIso_hom {U V : C} (q : V ⟶ U) (A : P.obj (.mk (op U))) :
    glueApp Γ J ((P.map q.op.toLoc).toFunctor.obj A) ≫ (Φ'.naturalityObjIso q.op.toLoc A).hom =
      (Φ.naturalityObjIso q.op.toLoc A).hom ≫
        (G.map q.op.toLoc).toFunctor.map (glueApp Γ J A) := by
  rw [← Iso.eq_comp_inv]
  refine IsPrestack.hom_ext (η.localImageSieve_mem J ((P.map q.op.toLoc).toFunctor.obj A))
    fun W r hr ↦ ?_
  have hrq : η.localImageSieve A (r ≫ q) :=
    Functor.essImage.ofIso (P.compIso q.op r.op (r ≫ q).op op_comp.symm A).symm hr
  have h₁ := pullHom_naturalityObjIso Φ Φ' q r A ((Φ.naturalityObjIso q.op.toLoc A).hom ≫
    (G.map q.op.toLoc).toFunctor.map (glueApp Γ J A) ≫ (Φ'.naturalityObjIso q.op.toLoc A).inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] at h₁
  rw [pullHom_map, map_glueApp Γ J A _ hrq] at h₁
  -- Cancel the naturality isomorphisms along `r ≫ q`.
  have h₂ : localApp Γ hrq =
      (Φ.app _).toFunctor.map (P.compIso q.op r.op (r ≫ q).op op_comp.symm A).hom ≫
      (Φ.naturalityObjIso r.op.toLoc _).hom ≫ (G.map r.op.toLoc).toFunctor.map
        ((Φ.naturalityObjIso q.op.toLoc A).hom ≫ (G.map q.op.toLoc).toFunctor.map (glueApp Γ J A) ≫
          (Φ'.naturalityObjIso q.op.toLoc A).inv) ≫
        (Φ'.naturalityObjIso r.op.toLoc _).inv ≫
          (Φ'.app _).toFunctor.map (P.compIso q.op r.op (r ≫ q).op op_comp.symm A).inv := by
    rw [← cancel_epi (Φ.naturalityObjIso (r ≫ q).op.toLoc A).inv,
      ← cancel_mono (Φ'.naturalityObjIso (r ≫ q).op.toLoc A).hom]
    simpa only [Category.assoc] using h₁
  -- Compare with `localApp` at the pullback of `q^* A` along `r`.
  have h₃ : localApp Γ hr = (Φ.naturalityObjIso r.op.toLoc _).hom ≫
      (G.map r.op.toLoc).toFunctor.map ((Φ.naturalityObjIso q.op.toLoc A).hom ≫
        (G.map q.op.toLoc).toFunctor.map (glueApp Γ J A) ≫
          (Φ'.naturalityObjIso q.op.toLoc A).inv) ≫
        (Φ'.naturalityObjIso r.op.toLoc _).inv := by
    have h := localApp_naturality Γ hrq hr (P.compIso q.op r.op (r ≫ q).op op_comp.symm A).hom
    rw [h₂] at h
    rw [← cancel_epi ((Φ.app _).toFunctor.map
      (P.compIso q.op r.op (r ≫ q).op op_comp.symm A).hom), h]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
      Category.comp_id]
  rw [map_glueApp Γ J _ r hr, h₃]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The modification `Φ ⟶ Φ'` extending `Γ : η ≫ Φ ⟶ η ≫ Φ'`, glued from its values at the
objects in the essential image of `η`. -/
private def glue : Φ ⟶ Φ' where
  as :=
    { app a := ⟨{ app A := glueApp Γ J (U := a.as.unop) A
                  naturality _ _ x := glueApp_naturality Γ J x }⟩
      naturality f := Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun A ↦ by
        have h := glueApp_comp_naturalityObjIso_hom Γ J f.as.unop A
        rw [naturalityObjIso_hom, naturalityObjIso_hom] at h
        -- `h` is the claim, up to unfolding the components of `glue`.
        exact h }

/-- The glued modification extends `Γ`. -/
private lemma whiskerLeft_glue : η ◁ glue Γ J = Γ := by
  ext ⟨⟨U⟩⟩ : 2
  refine NatTrans.ext (funext fun M ↦ ?_)
  -- The component of `η ◁ glue Γ J` at `M` is `glueApp Γ J` at `η M`, by definition of `glue`.
  refine (glueApp_eq_localApp Γ J (A := (η.app _).toFunctor.obj M)
    (Functor.obj_mem_essImage _ M)).trans ?_
  rw [localApp_eq Γ _ (Iso.refl _)]
  simp only [Iso.refl_inv, Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id]
  -- `appObj Γ M` is the component of `Γ` at `M` by definition.
  rfl

end Glue

/-- The pullback of a component of a modification `Δ : Φ ⟶ Φ'` to an object in the essential
image of `η` is determined by the whiskered modification `η ◁ Δ`. -/
private lemma map_app_eq (Δ : Φ ⟶ Φ') {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (A : P.obj a)
    {M : F.obj b} (e : (η.app b).toFunctor.obj M ≅ (P.map f).toFunctor.obj A) :
    (G.map f).toFunctor.map ((Δ.as.app a).toNatTrans.app A) =
      (Φ.naturalityObjIso f A).inv ≫ (Φ.app b).toFunctor.map e.inv ≫
        (Δ.as.app b).toNatTrans.app ((η.app b).toFunctor.obj M) ≫ (Φ'.app b).toFunctor.map e.hom ≫
          (Φ'.naturalityObjIso f A).hom := by
  rw [← cancel_epi (Φ.naturalityObjIso f A).hom, ← app_comp_naturalityObjIso_hom,
    Iso.hom_inv_id_assoc, reassoc_of% ((Δ.as.app b).toNatTrans.naturality e.inv),
    ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

variable (G η) in
/-- **Precomposition with a locally essentially surjective transformation is faithful** on
strong transformations into a prestack: a modification `Δ : Φ ⟶ Φ'` between strong
transformations `P ⟶ G` is determined by its restriction `η ◁ Δ` along a locally essentially
surjective `η : F ⟶ P`, when `G` is a prestack. -/
theorem faithful_precomp (J : GrothendieckTopology C) [η.IsLocallyEssSurj J] [G.IsPrestack J] :
    (precomp G η).Faithful where
  map_injective {Φ Φ'} Δ Δ' h := by
    ext ⟨⟨U⟩⟩ : 2
    refine NatTrans.ext (funext fun A ↦ ?_)
    refine IsPrestack.hom_ext (η.localImageSieve_mem J A) fun T g hg ↦ ?_
    have hM : (Δ.as.app _).toNatTrans.app ((η.app _).toFunctor.obj hg.witness) =
        (Δ'.as.app _).toNatTrans.app ((η.app _).toFunctor.obj hg.witness) := by
      have h' := congrArg (fun t ↦ (t.as.app (.mk (op T))).toNatTrans.app hg.witness) h
      simp only [precomp_map, whiskerLeft_as_app, Cat.whiskerLeft_app] at h'
      -- `h'` is the claim, its type written through `precomp G η` rather than `Φ` and `η`.
      exact h'
    rw [map_app_eq Δ g.op.toLoc A hg.getIso, map_app_eq Δ' g.op.toLoc A hg.getIso, hM]

variable (G η) in
/-- **Precomposition with a locally essentially surjective transformation with full components is
full** on strong transformations into a prestack: if the components of `η : F ⟶ P` are full and
`η` is locally essentially surjective, every modification `η ≫ Φ ⟶ η ≫ Φ'` between strong
transformations `P ⟶ G` into a prestack `G` is the restriction of a modification `Φ ⟶ Φ'`. -/
theorem full_precomp (J : GrothendieckTopology C) [∀ a, (η.app a).toFunctor.Full]
    [η.IsLocallyEssSurj J] [G.IsPrestack J] : (precomp G η).Full where
  map_surjective Γ := ⟨glue Γ J, whiskerLeft_glue Γ J⟩

end Prestack

end CategoryTheory.Pseudofunctor.StrongTrans
