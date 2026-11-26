/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.LocallyDiscrete
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe
public import TauCeti.CategoryTheory.Sites.Descent.TwoFiberProduct
public import TauCeti.CategoryTheory.Sites.Descent.Yoneda

/-!
# Relative gerbes

Let `η : F ⟶ G` be a strong transformation of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` and `J`
a Grothendieck topology on `C`. Following Stacks, Lemma 8.11.3 and Definition 8.11.4 (06NY), `η`
is a *relative gerbe* for `J` (`StrongTrans.IsRelativeGerbe`) if

* every object `y` of `G` over `U` lifts along `η` up to isomorphism after pullback along every
  arrow of some `J`-covering sieve of `U`: `η` is *locally essentially surjective*
  (`StrongTrans.IsLocallyEssSurj`), and
* for objects `x`, `x'` of `F` over `U`, every isomorphism `b : η x ≅ η x'` lifts after pullback
  along every arrow `f : V ⟶ U` of some `J`-covering sieve of `U` to an isomorphism
  `F(f) x ≅ F(f) x'` whose image under `η` is the pullback `G(f) b`, read through the naturality
  isomorphisms of `η`. In other words, the maps that `η` induces on the presheaves of
  isomorphisms are locally surjective.

Local essential surjectivity alone does not suffice: on a category with the trivial topology `⊥`,
in which only maximal sieves cover, a relative gerbe is a transformation whose components are
essentially surjective and surjective on isomorphisms (`StrongTrans.isRelativeGerbe_bot_iff`), and
for the inclusion of a proper subgroup `H < G` the induced transformation of constant
pseudofunctors with fibres the one-object groupoids of `H` and of `G` is locally essentially
surjective but no relative gerbe (`TauCeti.not_isRelativeGerbe_bot_constSingleObjMap_subtype`).
Every transformation whose components are equivalences, in particular every identity, is a
relative gerbe.

Stacks states the equivalent form that the projection of the iso-comma stack of `η` to `G` is a
gerbe over `G`, for the topology induced from `C`. Here this is tested on each object `y` of `G`
over `U`: the *relative fibre* `StrongTrans.relativeFiber η y` is the 2-fibre product
`TauCeti.Stack.twoFiberProduct` of the restriction of `η` to the slice `Over U` with the strong
transformation `ofPresheaf (yoneda.obj (Over.mk (𝟙 U))) ⟶ G.over U` that the 2-Yoneda lemma
attaches to `y`. Its objects over `V ⟶ U` are, up to the unique morphism `V ⟶ Over.mk (𝟙 U)`,
pairs of an object `x` of `F` over `V` and an isomorphism `η x ≅ y|_V`: in the language of fibred
categories, the 2-fibre product of `η` with the morphism `y : U ⟶ G`, which is the fibre over `y` of
that projection. When `F` is a stack with groupoid fibres and `G` is a prestack, `η` is a relative
gerbe exactly when every relative fibre is a gerbe for `J.over U`
(`StrongTrans.isRelativeGerbe_iff_isGerbe_relativeFiber`). The iso-comma stack itself is not
constructed here.

The relative fibre uses the 2-Yoneda lemma, which needs the morphisms of the fibres of `G` to lie in
the universe `v` of the morphisms of `C`; this holds for pseudofunctors with values in
`Cat.{u, u + 1}` on the big site `Over S` of a scheme `S : Scheme.{u}`.

## Main declarations

* `CategoryTheory.Pseudofunctor.StrongTrans.IsLocallyEssSurj`,
  `CategoryTheory.Pseudofunctor.StrongTrans.IsRelativeGerbe`: locally essentially surjective
  transformations and relative gerbes, with the two local lifting statements `exists_covering_lift`
  and `exists_covering_liftIso`.
* `CategoryTheory.Pseudofunctor.StrongTrans.isRelativeGerbe_of_isEquivalence`,
  `CategoryTheory.Pseudofunctor.StrongTrans.isRelativeGerbe_id`: transformations whose components
  are equivalences, and identities, are relative gerbes.
* `CategoryTheory.Pseudofunctor.StrongTrans.isLocallyEssSurj_bot_iff`,
  `CategoryTheory.Pseudofunctor.StrongTrans.isRelativeGerbe_bot_iff`: the two notions for the
  trivial topology.
* `CategoryTheory.Pseudofunctor.StrongTrans.relativeFiber`: the relative fibre over an object, a
  stack (`isStack_relativeFiber`) with groupoid fibres (`isGroupoid_relativeFiber_obj`).
* `CategoryTheory.Pseudofunctor.StrongTrans.isRelativeGerbe_iff_isGerbe_relativeFiber`: `η` is a
  relative gerbe if and only if its relative fibres are gerbes.
* `TauCeti.constSingleObjMap`, `TauCeti.isLocallyEssSurj_constSingleObjMap`,
  `TauCeti.isRelativeGerbe_bot_constSingleObjMap_iff`,
  `TauCeti.not_isRelativeGerbe_bot_constSingleObjMap_subtype`: the transformation of constant
  pseudofunctors with one-object fibres induced by a monoid homomorphism `φ`, which is locally
  essentially surjective for every topology; for groups and the trivial topology on a nonempty
  category it is a relative gerbe if and only if `φ` is surjective.

## References

* [Stacks Project, Section 06NY](https://stacks.math.columbia.edu/tag/06NY), Lemma 8.11.3 and
  Definition 8.11.4
-/

@[expose] public section

universe w w' v u v' u'

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

/-- A strong transformation `η : F ⟶ G` is a *relative gerbe* for a Grothendieck topology `J`
(Stacks, Lemma 8.11.3 (2) and Definition 8.11.4 (06NY)) if it is locally essentially surjective
and, for objects `x`, `x'` of `F` over `U`, every isomorphism `η x ≅ η x'` lifts to an isomorphism
`F(f) x ≅ F(f) x'` after pullback along every arrow `f` of some covering sieve of `U`. -/
class IsRelativeGerbe (η : StrongTrans F G) (J : GrothendieckTopology C) : Prop
    extends η.IsLocallyEssSurj J where
  /-- Every isomorphism `b : η x ≅ η x'` lifts after pullback along every arrow `f : V ⟶ U` of
  some covering sieve of `U`: there is an isomorphism `a : F(f) x ≅ F(f) x'` whose image under
  `η` is the pullback `G(f) b`, read through the naturality isomorphisms of `η` at `f`. -/
  exists_covering_liftIso {U : C} {x x' : F.obj (.mk (op U))}
    (b : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj x') :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      ∃ a : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj x',
        (η.app (.mk (op V))).toFunctor.map a.hom =
          (η.naturality f.op.toLoc).hom.toNatTrans.app x ≫
            (G.map f.op.toLoc).toFunctor.map b.hom ≫ (η.naturality f.op.toLoc).inv.toNatTrans.app x'

variable {J : GrothendieckTopology C} (η : StrongTrans F G)

/-- A strong transformation whose components are essentially surjective is locally essentially
surjective, for every topology. -/
theorem isLocallyEssSurj_of_essSurj (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.EssSurj) :
    η.IsLocallyEssSurj J where
  exists_covering_lift {U} y := ⟨⊤, J.top_mem U, fun V f _ ↦
    have := hη V
    ⟨(η.app (.mk (op V))).toFunctor.objPreimage ((G.map f.op.toLoc).toFunctor.obj y),
      ⟨(η.app (.mk (op V))).toFunctor.objObjPreimageIso _⟩⟩⟩

/-- A strong transformation whose components are equivalences of categories is a relative gerbe,
for every topology. -/
theorem isRelativeGerbe_of_isEquivalence
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.IsEquivalence) : η.IsRelativeGerbe J where
  toIsLocallyEssSurj := isLocallyEssSurj_of_essSurj η fun U ↦ have := hη U; inferInstance
  exists_covering_liftIso {U} x x' b := ⟨⊤, J.top_mem U, fun V f _ ↦ by
    have := hη V
    exact ⟨(η.app (.mk (op V))).toFunctor.preimageIso
      (η.naturalityObjIso f.op.toLoc x ≪≫ (G.map f.op.toLoc).toFunctor.mapIso b ≪≫
        (η.naturalityObjIso f.op.toLoc x').symm), by simp⟩⟩

/-- The identity transformation of any pseudofunctor is a relative gerbe. -/
instance isRelativeGerbe_id (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) :
    (StrongTrans.id F).IsRelativeGerbe J :=
  isRelativeGerbe_of_isEquivalence _ fun _ ↦ Functor.isEquivalence_refl

/-- For the trivial topology, in which only maximal sieves cover, a strong transformation is
locally essentially surjective if and only if its components are essentially surjective. -/
theorem isLocallyEssSurj_bot_iff :
    η.IsLocallyEssSurj ⊥ ↔ ∀ U : C, (η.app (.mk (op U))).toFunctor.EssSurj := by
  refine ⟨fun _ U ↦ ⟨fun y ↦ ?_⟩, isLocallyEssSurj_of_essSurj η⟩
  obtain ⟨R, hR, h⟩ := IsLocallyEssSurj.exists_covering_lift (η := η) (J := ⊥) y
  rw [GrothendieckTopology.bot_covering] at hR
  subst hR
  obtain ⟨x, ⟨e⟩⟩ := h (𝟙 U) trivial
  exact ⟨x, ⟨e ≪≫ (Cat.Hom.toNatIso (G.mapId' (𝟙 U).op.toLoc)).app y⟩⟩

/-- For the trivial topology, in which only maximal sieves cover, a strong transformation is a
relative gerbe if and only if its components are essentially surjective and every isomorphism
`η x ≅ η x'` is the image of an isomorphism `x ≅ x'`. -/
theorem isRelativeGerbe_bot_iff :
    η.IsRelativeGerbe ⊥ ↔ (∀ U : C, (η.app (.mk (op U))).toFunctor.EssSurj) ∧
      ∀ (U : C) (x x' : F.obj (.mk (op U)))
        (b : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj x'),
        ∃ a : x ≅ x', (η.app (.mk (op U))).toFunctor.map a.hom = b.hom := by
  refine ⟨fun _ ↦ ⟨(isLocallyEssSurj_bot_iff η).1 inferInstance, fun U x x' b ↦ ?_⟩,
    fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · obtain ⟨R, hR, h⟩ := IsRelativeGerbe.exists_covering_liftIso (J := ⊥) b
    rw [GrothendieckTopology.bot_covering] at hR
    subst hR
    obtain ⟨a, ha⟩ := h (𝟙 U) trivial
    let m := Cat.Hom.toNatIso (F.mapId' (𝟙 U).op.toLoc)
    refine ⟨(m.app x).symm ≪≫ a ≪≫ m.app x', ?_⟩
    have hx := naturality_id'_inv_app η (𝟙 U).op.toLoc rfl x
    have hx' := naturality_id'_inv_app η (𝟙 U).op.toLoc rfl x'
    rw [← cancel_epi ((η.naturality (𝟙 U).op.toLoc).inv.toNatTrans.app x)] at ha
    simp only [Cat.Hom.inv_hom_id_toNatTrans_app_assoc] at ha
    rw [hx, hx', Category.assoc,
      reassoc_of% ((G.mapId' (𝟙 U).op.toLoc).hom.toNatTrans.naturality b.hom), cancel_epi] at ha
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, m, Iso.app_hom, Iso.app_inv,
      Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, reassoc_of% ha]
    simp [← Functor.map_comp]
  · exact { toIsLocallyEssSurj := (isLocallyEssSurj_bot_iff η).2 h₁
            exists_covering_liftIso {U} x x' b := ⟨⊤, (⊥ : GrothendieckTopology C).top_mem U,
              fun V f _ ↦ h₂ V _ _ ((Cat.Hom.toNatIso (η.naturality f.op.toLoc)).app x ≪≫
                (G.map f.op.toLoc).toFunctor.mapIso b ≪≫
                  ((Cat.Hom.toNatIso (η.naturality f.op.toLoc)).app x').symm)⟩ }

/-! ### The relative fibre -/

section RelativeFiber

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v, max w' v}}
  (η : StrongTrans F G)

attribute [local instance] uliftCategory

/-- The *relative fibre* of `η : F ⟶ G` over an object `y` of `G` over `U`: the 2-fibre product,
on the slice `Over U`, of the restriction of `η` with the strong transformation
`ofPresheaf (yoneda.obj (Over.mk (𝟙 U))) ⟶ G.over U` attached to `y` by the 2-Yoneda lemma. Its
objects over `V : Over U` are triples of an object `x` of `F` over `V.left`, the unique morphism
`g : V ⟶ Over.mk (𝟙 U)` and an isomorphism `η x ≅ G(g) y`: in the language of fibred categories,
the 2-fibre product of `η` with the morphism `y : U ⟶ G`. -/
def relativeFiber {U : C} (y : G.obj (.mk (op U))) :
    LocallyDiscrete (Over U)ᵒᵖ ⥤ᵖ Cat.{v, max w' v} :=
  TauCeti.Stack.twoFiberProduct.{w'} ((Over.forget U).op.toPseudofunctor.whiskerLeft η)
    ((G.over U).yonedaPullbackObj (Over.mk (𝟙 U)) y)

variable {η} {J : GrothendieckTopology C}

/-- The relative fibres of a transformation out of a pseudofunctor with groupoid fibres have
groupoid fibres. -/
instance isGroupoid_relativeFiber_obj [∀ U : C, IsGroupoid (F.obj (.mk (op U)))] {U : C}
    (y : G.obj (.mk (op U))) (V : LocallyDiscrete (Over U)ᵒᵖ) :
    IsGroupoid ((η.relativeFiber y).obj V) :=
  have : IsGroupoid ((F.over U).obj V) :=
    inferInstanceAs (IsGroupoid (F.obj (.mk (op V.as.unop.left))))
  TauCeti.Stack.twoFiberProduct.isGroupoid_obj _ _ V

/-- The relative fibres of a transformation from a stack to a prestack are stacks for the
restricted topology. -/
instance isStack_relativeFiber [F.IsStack J] [G.IsPrestack J] {U : C} (y : G.obj (.mk (op U))) :
    (η.relativeFiber y).IsStack (J.over U) := by
  -- The representable presheaf of the terminal object `Over.mk (𝟙 U)` is a sheaf, as all of its
  -- values are singletons.
  have : (ofPresheaf.{w'} (yoneda.obj (Over.mk (𝟙 U)))).IsStack (J.over U) :=
    (isStack_ofPresheaf_iff _ _).2 fun _ _ _ _ _ ↦ ⟨Over.mkIdTerminal.from _,
      fun _ _ _ ↦ Over.mkIdTerminal.hom_ext _ _, fun _ _ ↦ Over.mkIdTerminal.hom_ext _ _⟩
  exact TauCeti.Stack.twoFiberProduct.isStack _ _

/-- A strong transformation whose relative fibres are gerbes is locally essentially surjective:
the lifts of an object `y` are the local objects of its relative fibre. -/
theorem isLocallyEssSurj_of_isGerbe_relativeFiber
    (h : ∀ (U : C) (y : G.obj (.mk (op U))), (η.relativeFiber y).IsGerbe (J.over U)) :
    η.IsLocallyEssSurj J where
  exists_covering_lift {U} y := by
    have := h U y
    obtain ⟨R, hR, hR'⟩ := IsGerbe.exists_covering_nonempty (F := η.relativeFiber y)
      (J := J.over U) (Over.mk (𝟙 U))
    refine ⟨Sieve.overEquiv _ R, (J.mem_over_iff R).1 hR, fun V f hf ↦ ?_⟩
    obtain ⟨⟨x, g, e⟩⟩ := hR' _ ((Sieve.overEquiv_iff R f).1 hf)
    have hg : g.down.as.left = f := by simpa using Over.w g.down.as
    exact ⟨x, ⟨e ≪≫ eqToIso (congrArg (fun k : V ⟶ U ↦ (G.map k.op.toLoc).toFunctor.obj y) hg)⟩⟩

/-- If the relative fibre of `η` over `η x'` is a gerbe, an isomorphism `b : η x ≅ η x'` lifts
locally, along the local isomorphisms between the objects `(x, b)` and `(x', 𝟙)` of that fibre. -/
private lemma exists_covering_liftIso_of_isGerbe_relativeFiber {U : C}
    {x x' : F.obj (.mk (op U))}
    [(η.relativeFiber ((η.app (.mk (op U))).toFunctor.obj x')).IsGerbe (J.over U)]
    (b : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj x') :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      ∃ a : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj x',
        (η.app (.mk (op V))).toFunctor.map a.hom =
          (η.naturality f.op.toLoc).hom.toNatTrans.app x ≫
            (G.map f.op.toLoc).toFunctor.map b.hom ≫
              (η.naturality f.op.toLoc).inv.toNatTrans.app x' := by
  let α' := (Over.forget U).op.toPseudofunctor.whiskerLeft η
  let β' := (G.over U).yonedaPullbackObj (Over.mk (𝟙 U)) ((η.app (.mk (op U))).toFunctor.obj x')
  let ε : (η.app (.mk (op U))).toFunctor.obj x' ≅
      (G.map (𝟙 U).op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x') :=
    ((Cat.Hom.toNatIso (G.mapId' (𝟙 U).op.toLoc)).app _).symm
  let s₀ : (ofPresheaf.{w'} (yoneda.obj (Over.mk (𝟙 U)))).obj (.mk (op (Over.mk (𝟙 U)))) :=
    ⟨⟨𝟙 _⟩⟩
  let P : (η.relativeFiber ((η.app (.mk (op U))).toFunctor.obj x')).obj
    (.mk (op (Over.mk (𝟙 U)))) := ⟨x, s₀, b ≪≫ ε⟩
  let Q : (η.relativeFiber ((η.app (.mk (op U))).toFunctor.obj x')).obj
    (.mk (op (Over.mk (𝟙 U)))) := ⟨x', s₀, ε⟩
  obtain ⟨R, hR, hR'⟩ := IsGerbe.exists_covering_iso (J := J.over U) P Q
  refine ⟨Sieve.overEquiv _ R, (J.mem_over_iff R).1 hR, fun V f hf ↦ ?_⟩
  let g : Over.mk (f ≫ (Over.mk (𝟙 U)).hom) ⟶ Over.mk (𝟙 U) := Over.homMk f
  obtain ⟨φ⟩ := hR' g ((Sieve.overEquiv_iff R f).1 hf)
  refine ⟨(Limits.CategoricalPullback.π₁ _ _).mapIso φ, ?_⟩
  -- The second component of `φ` is an endomorphism in a discrete category.
  have hsnd : (β'.app _).toFunctor.map φ.hom.snd = 𝟙 _ := by
    rw [Subsingleton.elim φ.hom.snd (𝟙 _)]
    exact Functor.map_id _ _
  have key : (η.app (.mk (op V))).toFunctor.map φ.hom.fst =
      (TauCeti.Stack.twoFiberProduct.mapIso α' β' g.op P).hom ≫
        (TauCeti.Stack.twoFiberProduct.mapIso α' β' g.op Q).inv :=
    (Iso.eq_comp_inv _).2 (φ.hom.w.trans ((congrArg (_ ≫ ·) hsnd).trans (Category.comp_id _)))
  refine key.trans ((TauCeti.Stack.twoFiberProduct.mapIso_hom_comp_mapIso_inv α' β' g.op
    (s := s₀) (b ≪≫ ε) ε).trans ?_)
  have hb : (b ≪≫ ε).hom ≫ ε.inv = b.hom := by
    rw [Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- The naturality isomorphisms of the restriction `α'` of `η` and the pullbacks of `G.over U`
  -- are those of `η` and `G`, by definition.
  exact congrArg (fun t ↦ (η.naturality f.op.toLoc).hom.toNatTrans.app x ≫
    (G.map f.op.toLoc).toFunctor.map t ≫ (η.naturality f.op.toLoc).inv.toNatTrans.app x') hb

/-- A strong transformation whose relative fibres are gerbes is a relative gerbe. -/
theorem isRelativeGerbe_of_isGerbe_relativeFiber
    (h : ∀ (U : C) (y : G.obj (.mk (op U))), (η.relativeFiber y).IsGerbe (J.over U)) :
    η.IsRelativeGerbe J where
  toIsLocallyEssSurj := isLocallyEssSurj_of_isGerbe_relativeFiber h
  exists_covering_liftIso {U} _ x' b :=
    have := h U ((η.app (.mk (op U))).toFunctor.obj x')
    exists_covering_liftIso_of_isGerbe_relativeFiber b

/-- The relative fibres of a relative gerbe from a stack with groupoid fibres to a prestack are
gerbes for the restricted topology. -/
instance isGerbe_relativeFiber [η.IsRelativeGerbe J] [F.IsStack J] [G.IsPrestack J]
    [∀ U : C, IsGroupoid (F.obj (.mk (op U)))] {U : C} (y : G.obj (.mk (op U))) :
    (η.relativeFiber y).IsGerbe (J.over U) where
  isGroupoid _ := inferInstance
  exists_covering_nonempty V := by
    obtain ⟨R, hR, hR'⟩ := IsLocallyEssSurj.exists_covering_lift (η := η) (J := J)
      ((G.map V.hom.op.toLoc).toFunctor.obj y)
    refine ⟨(Sieve.overEquiv V).symm R, J.overEquiv_symm_mem_over V R hR, fun W g hg ↦ ?_⟩
    obtain ⟨x, ⟨e⟩⟩ := hR' g.left ((Sieve.overEquiv_symm_iff R g).1 hg)
    exact ⟨⟨x, ⟨⟨Over.homMk W.hom⟩⟩, e ≪≫ ((Cat.Hom.toNatIso (G.mapComp' V.hom.op.toLoc
      g.left.op.toLoc W.hom.op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w g]))).app
        y).symm⟩⟩
  exists_covering_iso {V} P Q := by
    obtain ⟨x, g, e⟩ := P
    obtain ⟨x', g', e'⟩ := Q
    obtain rfl : g = g' := ULift.ext (Discrete.ext (Over.mkIdTerminal.hom_ext _ _))
    obtain ⟨R, hR, hR'⟩ := IsRelativeGerbe.exists_covering_liftIso (J := J) (U := V.left)
      (e ≪≫ e'.symm)
    refine ⟨(Sieve.overEquiv V).symm R, J.overEquiv_symm_mem_over V R hR, fun W h hh ↦ ?_⟩
    obtain ⟨a, ha⟩ := hR' h.left ((Sieve.overEquiv_symm_iff R h).1 hh)
    exact ⟨TauCeti.Stack.twoFiberProduct.mapObjIsoMk _ _ h.op e e' a ha⟩

/-- A strong transformation `η : F ⟶ G` from a stack with groupoid fibres to a prestack is a
relative gerbe if and only if its relative fibre over every object of `G` is a gerbe (Stacks,
Lemma 8.11.3 (06NY), with the gerbe condition on the iso-comma stack tested over each object). -/
theorem isRelativeGerbe_iff_isGerbe_relativeFiber [F.IsStack J] [G.IsPrestack J]
    [∀ U : C, IsGroupoid (F.obj (.mk (op U)))] :
    η.IsRelativeGerbe J ↔
      ∀ (U : C) (y : G.obj (.mk (op U))), (η.relativeFiber y).IsGerbe (J.over U) :=
  ⟨fun _ _ _ ↦ inferInstance, isRelativeGerbe_of_isGerbe_relativeFiber⟩

end RelativeFiber

end CategoryTheory.Pseudofunctor.StrongTrans

/-! ### Local essential surjectivity does not suffice -/

namespace TauCeti

open CategoryTheory Pseudofunctor
open scoped Pseudofunctor.StrongTrans

section Monoid

variable (C : Type u) [Category.{v} C] {M N : Type w} [Monoid M] [Monoid N]

/-- The constant pseudofunctor on `C` with fibre the one-object category `SingleObj M` of a
monoid `M`, and identities as pullbacks. -/
abbrev constSingleObj (M : Type w) [Monoid M] : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, 0} :=
  ((Functor.const Cᵒᵖ).obj (Cat.of (SingleObj M))).toPseudofunctor.comp (𝟭 Cat).toPseudofunctor'

/-- The strong transformation of constant pseudofunctors on `C` with one-object fibres induced by
a monoid homomorphism `φ : M →* N`: each component is the functor `SingleObj M ⥤ SingleObj N` of
`φ`. -/
def constSingleObjMap (φ : M →* N) : constSingleObj C M ⟶ constSingleObj C N :=
  (𝟭 Cat).toPseudofunctor'.mapNatTrans ((Functor.const Cᵒᵖ).map (SingleObj.mapHom M N φ).toCatHom)

variable {C}

/-- The transformation of constant pseudofunctors with one-object fibres induced by any monoid
homomorphism is locally essentially surjective, for every topology: the fibres have one object. -/
theorem isLocallyEssSurj_constSingleObjMap (φ : M →* N) (J : GrothendieckTopology C) :
    StrongTrans.IsLocallyEssSurj (constSingleObjMap C φ) J :=
  StrongTrans.isLocallyEssSurj_of_essSurj _ fun _ ↦ ⟨fun _ ↦ ⟨SingleObj.star M, ⟨Iso.refl _⟩⟩⟩

end Monoid

variable {C : Type u} [Category.{v} C] {M N : Type w} [Group M] [Group N]

/-- On a nonempty category with the trivial topology, the transformation of constant
pseudofunctors with one-object fibres induced by a group homomorphism `φ` is a relative gerbe if
and only if `φ` is surjective. -/
theorem isRelativeGerbe_bot_constSingleObjMap_iff [Nonempty C] (φ : M →* N) :
    StrongTrans.IsRelativeGerbe (constSingleObjMap C φ) ⊥ ↔ Function.Surjective φ := by
  rw [StrongTrans.isRelativeGerbe_bot_iff]
  refine ⟨fun ⟨_, h⟩ n ↦ ?_, fun h ↦ ⟨fun _ ↦ ⟨fun _ ↦ ⟨SingleObj.star M, ⟨Iso.refl _⟩⟩⟩,
    fun U x x' b ↦ ?_⟩⟩
  · obtain ⟨a, ha⟩ := h (Classical.arbitrary C) (SingleObj.star M) (SingleObj.star M)
      ((Groupoid.isoEquivHom (SingleObj.star N) (SingleObj.star N)).symm n)
    exact ⟨a.hom, ha⟩
  · obtain ⟨m, hm⟩ := h b.hom
    exact ⟨(Groupoid.isoEquivHom (SingleObj.star M) (SingleObj.star M)).symm m, hm⟩

/-- On a nonempty category with the trivial topology, for instance the category with one object
and only the maximal cover, the transformation of constant pseudofunctors with one-object fibres
induced by the inclusion of a proper subgroup `H` of `G` is no relative gerbe, although it is
locally essentially surjective (`isLocallyEssSurj_constSingleObjMap`). -/
theorem not_isRelativeGerbe_bot_constSingleObjMap_subtype [Nonempty C] {G : Type w} [Group G]
    {H : Subgroup G} (hH : H ≠ ⊤) :
    ¬ StrongTrans.IsRelativeGerbe (constSingleObjMap C H.subtype) ⊥ := by
  rw [isRelativeGerbe_bot_constSingleObjMap_iff]
  exact fun h ↦ hH (eq_top_iff.2 fun g _ ↦ by obtain ⟨⟨g', hg'⟩, rfl⟩ := h g; exact hg')

end TauCeti
