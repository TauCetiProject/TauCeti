/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism

/-!
# Band-preserving transformations on restricted isomorphisms

Let `η : F ⟶ G` be a strong transformation of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, with
component functors `η_U`. For `f : V ⟶ U` and `x` over `U`, the strong naturality isomorphism
`η(f) : F(f) ⋙ η_V ≅ η_U ⋙ G(f)` has the component `c_f(x) : η_V (F(f) x) ≅ G(f) (η_U x)`
(`GerbeMorphismPullback.comparison`). Conjugating by these components carries isomorphisms and
morphisms `F(f) x ⟶ F(f) y` between restrictions of objects over `U` to isomorphisms and
morphisms `G(f) (η_U x) ⟶ G(f) (η_U y)` (`GerbeMorphismPullback.mapIso`,
`GerbeMorphismPullback.homMap`). On restrictions of global morphisms `p : x ⟶ y` this is
`G(f) (η_U p)` (`homMap_restrict`, `mapIso_restrict`), but it is defined on every local morphism,
whether or not it comes from `U`.

When `η` preserves `A`-bandings `bF` and `bG`, the map on isomorphisms is compatible with the
action of the coefficients `A(V)` (`mapIso_act`), keeps differences (`mapIso_difference`) and is
injective (`mapIso_injective`); given a local anchor `p : F(f) x ≅ F(f) y` it has the inverse
`GerbeMorphismPullback.preimageIso`, independent of the anchor, and is a bijection
(`GerbeMorphismPullback.isomEquiv`). These are the local forms of the statements of
`BandedMorphism`, used to show that a band-preserving morphism of gerbes induces isomorphisms of
the sheaves of morphisms (Olsson, Lemma 31.3).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.GerbeMorphismPullback`:

* `comparison`: the strong naturality component `c_f(x)`.
* `mapIso`, `homMap`: transport of local isomorphisms and morphisms, with `mapIso_hom`,
  `homMap_restrict`, `mapIso_restrict`, `homMap_id`, `homMap_comp`, `mapIso_refl`, and
  `homMap_id_trans`, `mapIso_id_trans` for the identity transformation.
* `mapIso_act`, `mapIso_difference`, `mapIso_injective`, `homMap_injective`: compatibility with
  the bands.
* `preimageIso`, `map_preimageIso`, `preimageIso_mapIso`, `preimageIso_eq`, `preimageIso_act`,
  `preimageIso_restrict`, `isomEquiv`, `homMap_surjective_of_anchor`: the anchored inverse.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Lemma 31.3
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.GerbeMorphismPullback

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (η : StrongTrans F G) {U V : C} (f : V ⟶ U) {x y z : F.obj (.mk (op U))}

/-! ### Transport without bands -/

/-- The component `c_f(x) : η_V (F(f) x) ≅ G(f) (η_U x)` of the strong naturality isomorphism
`η(f) : F(f) ⋙ η_V ≅ η_U ⋙ G(f)`. -/
def comparison (x : F.obj (.mk (op U))) :
    (η.app (.mk (op V))).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj x) ≅
      (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) :=
  (Cat.Hom.toNatIso (η.naturality f.op.toLoc)).app x

theorem comparison_eq (x : F.obj (.mk (op U))) :
    comparison η f x = (Cat.Hom.toNatIso (η.naturality f.op.toLoc)).app x :=
  (rfl)

/-- The comparison is natural in global morphisms `p : x ⟶ y`. -/
@[reassoc]
theorem comparison_hom_naturality (p : x ⟶ y) :
    (η.app (.mk (op V))).toFunctor.map ((F.map f.op.toLoc).toFunctor.map p) ≫
        (comparison η f y).hom =
      (comparison η f x).hom ≫
        (G.map f.op.toLoc).toFunctor.map ((η.app (.mk (op U))).toFunctor.map p) :=
  (Cat.Hom.toNatIso (η.naturality f.op.toLoc)).hom.naturality p

/-- The transport `h_f(p) = c_f(x)⁻¹ ≫ η_V(p) ≫ c_f(y)` of a local morphism
`p : F(f) x ⟶ F(f) y`. -/
def homMap (p : (F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y) :
    (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) ⟶
      (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y) :=
  (comparison η f x).inv ≫ (η.app (.mk (op V))).toFunctor.map p ≫ (comparison η f y).hom

theorem homMap_def
    (p : (F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y) :
    homMap η f p =
      (comparison η f x).inv ≫ (η.app (.mk (op V))).toFunctor.map p ≫ (comparison η f y).hom :=
  (rfl)

/-- On the restriction of a global morphism `p : x ⟶ y`, the transport is `G(f) (η_U p)`. -/
@[simp]
theorem homMap_restrict (p : x ⟶ y) :
    homMap η f ((F.map f.op.toLoc).toFunctor.map p) =
      (G.map f.op.toLoc).toFunctor.map ((η.app (.mk (op U))).toFunctor.map p) := by
  rw [homMap_def, comparison_hom_naturality, Iso.inv_hom_id_assoc]

@[simp]
theorem homMap_id (x : F.obj (.mk (op U))) :
    homMap η f (𝟙 ((F.map f.op.toLoc).toFunctor.obj x)) = 𝟙 _ := by
  simp [homMap_def]

@[simp]
theorem homMap_comp
    (p : (F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y)
    (q : (F.map f.op.toLoc).toFunctor.obj y ⟶ (F.map f.op.toLoc).toFunctor.obj z) :
    homMap η f (p ≫ q) = homMap η f p ≫ homMap η f q := by
  simp [homMap_def]

/-- The transport `M_f(p) = c_f(x)⁻¹ ≪≫ η_V(p) ≪≫ c_f(y)` of a local isomorphism
`p : F(f) x ≅ F(f) y`. -/
def mapIso (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :
    (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) ≅
      (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y) :=
  (comparison η f x).symm ≪≫ (η.app (.mk (op V))).toFunctor.mapIso p ≪≫ comparison η f y

/-- The transported isomorphism has the transported morphism as its underlying morphism. -/
@[simp]
theorem mapIso_hom
    (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :
    (mapIso η f p).hom = homMap η f p.hom :=
  (rfl)

@[simp]
theorem mapIso_inv
    (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :
    (mapIso η f p).inv = homMap η f p.inv := by
  simp [mapIso, homMap_def]

/-- On the restriction of a global isomorphism `p : x ≅ y`, the transport is `G(f) (η_U p)`. -/
@[simp]
theorem mapIso_restrict (p : x ≅ y) :
    mapIso η f ((F.map f.op.toLoc).toFunctor.mapIso p) =
      (G.map f.op.toLoc).toFunctor.mapIso ((η.app (.mk (op U))).toFunctor.mapIso p) :=
  Iso.ext (homMap_restrict η f p.hom)

@[simp]
theorem mapIso_refl (x : F.obj (.mk (op U))) :
    mapIso η f (Iso.refl ((F.map f.op.toLoc).toFunctor.obj x)) = Iso.refl _ :=
  Iso.ext (homMap_id η f x)

theorem mapIso_trans
    (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)
    (q : (F.map f.op.toLoc).toFunctor.obj y ≅ (F.map f.op.toLoc).toFunctor.obj z) :
    mapIso η f (p ≪≫ q) = mapIso η f p ≪≫ mapIso η f q :=
  Iso.ext (homMap_comp η f p.hom q.hom)

/-- For the identity transformation, the comparison is the identity. -/
@[simp]
theorem comparison_id_hom (x : F.obj (.mk (op U))) :
    (comparison (StrongTrans.id F) f x).hom = 𝟙 _ := by
  simp [comparison, StrongTrans.id]

/-- For the identity transformation, the transport of a local morphism is the morphism itself. -/
@[simp]
theorem homMap_id_trans
    (p : (F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y) :
    homMap (StrongTrans.id F) f p = p := by
  simp [homMap_def, comparison, StrongTrans.id]

/-- For the identity transformation, the transport of a local isomorphism is the isomorphism
itself. -/
@[simp]
theorem mapIso_id_trans
    (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :
    mapIso (StrongTrans.id F) f p = p :=
  Iso.ext (homMap_id_trans f p.hom)

/-! ### Compatibility with the bands -/

variable {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}}
  (bF : F.AbelianBanding J A) (bG : G.AbelianBanding J A)

/-- Conjugation by `c_f(x)` keeps the band automorphism of every coefficient of `A(V)`. -/
theorem autMulEquivOfIso_comparison_mulEquiv (x : F.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op V))) :
    Aut.autMulEquivOfIso (comparison η f x)
        (bG.mulEquiv V ((η.app (.mk (op V))).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj x))
          a) =
      bG.mulEquiv V ((G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x)) a :=
  bG.autMulEquivOfIso_mulEquiv _ a

variable [BandPreserving bF bG η]

/-- **Compatibility with the action.** The transport of the action of `a ∈ A(V)` on a local
isomorphism is the action of `a` on its transport. -/
theorem mapIso_act
    (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)
    (a : Multiplicative (A.obj.obj (op V))) :
    mapIso η f (bF.act p a) = bG.act (mapIso η f p) a := by
  ext
  simp only [mapIso_hom, AbelianBanding.act_hom, homMap_def, Functor.map_comp, Category.assoc,
    BandPreserving.map_mulEquiv_hom bG η]
  rw [bG.mulEquiv_hom_comp (comparison η f y) a]

/-- **Compatibility with the difference.** The difference of transported local isomorphisms is the
difference of the local isomorphisms. -/
theorem mapIso_difference
    (p q : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :
    bG.difference (mapIso η f p) (mapIso η f q) = bF.difference p q := by
  rw [AbelianBanding.difference_eq_iff, ← mapIso_act η f bF bG, AbelianBanding.act_difference]

include bF bG in
/-- **Injectivity on local isomorphisms**, with no anchor. -/
theorem mapIso_injective :
    Function.Injective fun
      p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y ↦
        mapIso η f p := by
  intro p q h
  have hd := mapIso_difference η f bF bG p q
  simp only at h
  rw [h, AbelianBanding.difference_self] at hd
  rw [← bF.act_difference p q, ← hd, AbelianBanding.act_one]

include bF bG in
/-- **Injectivity on local morphisms** when the fibre of `F` over `V` is a groupoid, for instance
when `F` is a gerbe. -/
theorem homMap_injective [IsGroupoid (F.obj (.mk (op V)))] :
    Function.Injective fun
      p : (F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y ↦
        homMap η f p := by
  intro p q h
  have h' : mapIso η f (asIso p) = mapIso η f (asIso q) := Iso.ext (by simpa using h)
  simpa using congrArg Iso.hom (mapIso_injective η f bF bG h')

/-- **The anchored inverse on local isomorphisms.** Given a local anchor
`p : F(f) x ≅ F(f) y`, the preimage of `q : G(f) (η_U x) ≅ G(f) (η_U y)` is the
`BandedMorphism.preimageIso` of `c_f(x) ≪≫ q ≪≫ c_f(y)⁻¹`. -/
def preimageIso (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)
    (q : (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) ≅
      (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y)) :
    (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y :=
  BandedMorphism.preimageIso bF bG η p (comparison η f x ≪≫ q ≪≫ (comparison η f y).symm)

/-- `M_f` maps the preimage of `q` to `q`. -/
@[simp]
theorem map_preimageIso
    (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)
    (q : (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) ≅
      (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y)) :
    mapIso η f (preimageIso η f bF bG p q) = q := by
  rw [mapIso, preimageIso, BandedMorphism.map_preimageIso]
  ext
  simp

/-- The preimage of the transport of `q` is `q`. -/
@[simp]
theorem preimageIso_mapIso
    (p q : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :
    preimageIso η f bF bG p (mapIso η f q) = q :=
  mapIso_injective η f bF bG (map_preimageIso η f bF bG p _)

/-- The preimage does not depend on the anchor. -/
theorem preimageIso_eq
    (p p' : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)
    (q : (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) ≅
      (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y)) :
    preimageIso η f bF bG p q = preimageIso η f bF bG p' q :=
  mapIso_injective η f bF bG (by simp only [map_preimageIso])

/-- The preimage is compatible with the action of the coefficients. -/
theorem preimageIso_act
    (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)
    (q : (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) ≅
      (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y))
    (a : Multiplicative (A.obj.obj (op V))) :
    preimageIso η f bF bG p (bG.act q a) = bF.act (preimageIso η f bF bG p q) a :=
  mapIso_injective η f bF bG (by simp only [map_preimageIso, mapIso_act η f bF bG])

/-- On restrictions of a global anchor `p : x ≅ y` and of a global `q : η_U x ≅ η_U y`, the
preimage is the restriction of the global preimage `BandedMorphism.preimageIso p q`. -/
theorem preimageIso_restrict (p : x ≅ y)
    (q : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj y) :
    preimageIso η f bF bG ((F.map f.op.toLoc).toFunctor.mapIso p)
        ((G.map f.op.toLoc).toFunctor.mapIso q) =
      (F.map f.op.toLoc).toFunctor.mapIso (BandedMorphism.preimageIso bF bG η p q) :=
  mapIso_injective η f bF bG (by
    simp only [map_preimageIso, mapIso_restrict, BandedMorphism.map_preimageIso])

/-- **The anchored bijection on local isomorphisms.** Given a local anchor
`p : F(f) x ≅ F(f) y`, `M_f` is a bijection `(F(f) x ≅ F(f) y) ≃ (G(f) (η_U x) ≅ G(f) (η_U y))`
with inverse `preimageIso p`. -/
def isomEquiv (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :
    ((F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) ≃
      ((G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) ≅
        (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y)) where
  toFun := mapIso η f
  invFun := preimageIso η f bF bG p
  left_inv := preimageIso_mapIso η f bF bG p
  right_inv := map_preimageIso η f bF bG p

@[simp]
theorem isomEquiv_apply
    (p q : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :
    isomEquiv η f bF bG p q = mapIso η f q :=
  (rfl)

@[simp]
theorem isomEquiv_symm_apply
    (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y)
    (q : (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj x) ≅
      (G.map f.op.toLoc).toFunctor.obj ((η.app (.mk (op U))).toFunctor.obj y)) :
    (isomEquiv η f bF bG p).symm q = preimageIso η f bF bG p q :=
  (rfl)

include bF bG in
/-- **Surjectivity on local morphisms with an anchor.** When the fibre of `G` over `V` is a
groupoid and `F(f) x ≅ F(f) y` is inhabited, every morphism `G(f) (η_U x) ⟶ G(f) (η_U y)` is the
transport of a local morphism. -/
theorem homMap_surjective_of_anchor [IsGroupoid (G.obj (.mk (op V)))]
    (p : (F.map f.op.toLoc).toFunctor.obj x ≅ (F.map f.op.toLoc).toFunctor.obj y) :
    Function.Surjective fun
      r : (F.map f.op.toLoc).toFunctor.obj x ⟶ (F.map f.op.toLoc).toFunctor.obj y ↦
        homMap η f r := by
  intro q
  exact ⟨(preimageIso η f bF bG p (asIso q)).hom,
    congrArg Iso.hom (map_preimageIso η f bF bG p (asIso q))⟩

end CategoryTheory.Pseudofunctor.GerbeMorphismPullback
