/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Basic

/-!
# Band-preserving transformations on isomorphisms and automorphisms

Let `bF` and `bG` be `A`-bandings of pseudofunctors `F` and `G`, for one sheaf of abelian groups
`A`, and let `η : F ⟶ G` be a strong transformation preserving the bands. Write `η_U` for its
component functor over `U`. Since `η_U` carries band automorphisms to band automorphisms, it is
compatible with the action of the coefficients `A(U)` on the isomorphisms `x ≅ y` of the fibre
(`BandedMorphism.map_act`) and leaves their differences unchanged
(`BandedMorphism.map_difference`). As the action is free, `η_U` is injective on isomorphisms
(`BandedMorphism.mapIso_injective`), hence faithful when the fibre of `F` over `U` is a groupoid,
for instance when `F` is a gerbe (`BandedMorphism.faithful`).

Given an isomorphism `p : x ≅ y` (an anchor; it is data, never inferred from local
nonemptiness), every isomorphism `q : η_U x ≅ η_U y` has the preimage
`p • (q - η_U p)` (`BandedMorphism.preimageIso`), independent of the anchor. So `η_U` is a bijection
`(x ≅ y) ≃ (η_U x ≅ η_U y)` as soon as `x ≅ y` is inhabited (`BandedMorphism.isomEquiv`), and full
on that pair when the fibre of `G` over `U` is a groupoid
(`BandedMorphism.hom_surjective_of_anchor`). On automorphisms, `η_U` is the composite of the two
band identifications (`BandedMorphism.autEquiv`).

Composition of band-preserving transformations is
`CategoryTheory.Pseudofunctor.BandPreserving.comp`. For the identity transformation the anchored
inverse is the identity (`BandedMorphism.preimageIso_id`), and for a composite `η ≫ θ` it is the
anchored inverse of `η` after that of `θ` at the image anchor (`BandedMorphism.preimageIso_comp`);
the same holds for the bijections on isomorphisms and the equivalences on automorphisms.

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `map_act`, `map_difference`: compatibility with the action and the difference.
* `mapIso_injective`, `faithful`: injectivity on isomorphisms and faithfulness.
* `preimageIso`, `map_preimageIso`, `preimageIso_map`, `preimageIso_eq`, `preimageIso_act`: the
  anchored inverse on isomorphisms.
* `isomEquiv`: the bijection `(x ≅ y) ≃ (η_U x ≅ η_U y)` given an anchor.
* `hom_surjective_of_anchor`: fullness on a pair with an anchor.
* `autEquiv`, `autEquiv_apply`: the multiplicative equivalence `Aut x ≃* Aut (η_U x)`, equal to
  `η_U.mapAut`.
* `preimageIso_id`, `preimageIso_comp`, `isomEquiv_id`, `isomEquiv_comp`, `autEquiv_id`,
  `autEquiv_comp`: the identity transformation and composites.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Lemma 31.3
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.BandedMorphism

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}} (bF : F.AbelianBanding J A)
  (bG : G.AbelianBanding J A) (η : StrongTrans F G) [BandPreserving bF bG η] {U : C}
  {x y : F.obj (.mk (op U))}

/-- **Compatibility with the action.** The component functor `η_U` carries the action of a
coefficient on an isomorphism to the action of the same coefficient on its image. -/
theorem map_act (p : x ≅ y) (a : Multiplicative (A.obj.obj (op U))) :
    (η.app (.mk (op U))).toFunctor.mapIso (bF.act p a) =
      bG.act ((η.app (.mk (op U))).toFunctor.mapIso p) a := by
  ext
  simp [BandPreserving.map_mulEquiv_hom bG η]

/-- **Compatibility with the difference.** The difference of the images of `p` and `q` under `η_U`
is the difference of `p` and `q`. -/
theorem map_difference (p q : x ≅ y) :
    bG.difference ((η.app (.mk (op U))).toFunctor.mapIso p)
        ((η.app (.mk (op U))).toFunctor.mapIso q) = bF.difference p q := by
  rw [AbelianBanding.difference_eq_iff, ← map_act bF bG η, AbelianBanding.act_difference]

include bF bG in
/-- **Injectivity on isomorphisms.** Isomorphisms with the same image under `η_U` are equal: their
difference is `1`. -/
theorem mapIso_injective :
    Function.Injective fun p : x ≅ y ↦ (η.app (.mk (op U))).toFunctor.mapIso p := by
  intro p q h
  have hd := map_difference bF bG η p q
  simp only at h
  rw [h, AbelianBanding.difference_self] at hd
  rw [← bF.act_difference p q, ← hd, AbelianBanding.act_one]

include bF bG in
/-- **Faithfulness.** When the fibre of `F` over `U` is a groupoid, for instance when `F` is a
gerbe, the component functor `η_U` of a band-preserving transformation is faithful. -/
theorem faithful [IsGroupoid (F.obj (.mk (op U)))] :
    (η.app (.mk (op U))).toFunctor.Faithful where
  map_injective {x y} f g h := by
    have h' : (η.app (.mk (op U))).toFunctor.mapIso (asIso f) =
        (η.app (.mk (op U))).toFunctor.mapIso (asIso g) := Iso.ext (by simpa using h)
    simpa using congrArg Iso.hom (mapIso_injective bF bG η h')

/-- **The anchored inverse on isomorphisms.** Given an isomorphism `p : x ≅ y`, the preimage of
`q : η_U x ≅ η_U y` is the action on `p` of the difference of `η_U p` and `q`. -/
def preimageIso (p : x ≅ y)
    (q : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj y) : x ≅ y :=
  bF.act p (bG.difference ((η.app (.mk (op U))).toFunctor.mapIso p) q)

omit [BandPreserving bF bG η] in
theorem preimageIso_def (p : x ≅ y)
    (q : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj y) :
    preimageIso bF bG η p q =
      bF.act p (bG.difference ((η.app (.mk (op U))).toFunctor.mapIso p) q) :=
  (rfl)

/-- `η_U` maps the preimage of `q` to `q`. -/
@[simp]
theorem map_preimageIso (p : x ≅ y)
    (q : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj y) :
    (η.app (.mk (op U))).toFunctor.mapIso (preimageIso bF bG η p q) = q := by
  rw [preimageIso_def, map_act bF bG η, AbelianBanding.act_difference]

/-- The preimage of the image of `q` is `q`. -/
@[simp]
theorem preimageIso_map (p q : x ≅ y) :
    preimageIso bF bG η p ((η.app (.mk (op U))).toFunctor.mapIso q) = q := by
  rw [preimageIso_def, map_difference bF bG η, AbelianBanding.act_difference]

/-- The preimage does not depend on the anchor. -/
theorem preimageIso_eq (p p' : x ≅ y)
    (q : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj y) :
    preimageIso bF bG η p q = preimageIso bF bG η p' q :=
  mapIso_injective bF bG η (by simp only [map_preimageIso])

/-- The preimage is compatible with the action of the coefficients. -/
theorem preimageIso_act (p : x ≅ y)
    (q : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj y)
    (a : Multiplicative (A.obj.obj (op U))) :
    preimageIso bF bG η p (bG.act q a) = bF.act (preimageIso bF bG η p q) a :=
  mapIso_injective bF bG η (by simp only [map_preimageIso, map_act bF bG η])

/-- **The anchored bijection on isomorphisms.** Given an isomorphism `p : x ≅ y`, the component
functor `η_U` is a bijection `(x ≅ y) ≃ (η_U x ≅ η_U y)`, with inverse `preimageIso p`. -/
def isomEquiv (p : x ≅ y) :
    (x ≅ y) ≃ ((η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj y) where
  toFun q := (η.app (.mk (op U))).toFunctor.mapIso q
  invFun := preimageIso bF bG η p
  left_inv := preimageIso_map bF bG η p
  right_inv := map_preimageIso bF bG η p

@[simp]
theorem isomEquiv_apply (p q : x ≅ y) :
    isomEquiv bF bG η p q = (η.app (.mk (op U))).toFunctor.mapIso q :=
  (rfl)

@[simp]
theorem isomEquiv_symm_apply (p : x ≅ y)
    (q : (η.app (.mk (op U))).toFunctor.obj x ≅ (η.app (.mk (op U))).toFunctor.obj y) :
    (isomEquiv bF bG η p).symm q = preimageIso bF bG η p q :=
  (rfl)

/-- The anchored bijection does not depend on the anchor. -/
theorem isomEquiv_eq (p p' : x ≅ y) : isomEquiv bF bG η p = isomEquiv bF bG η p' :=
  Equiv.ext fun _ ↦ rfl

include bF bG in
/-- **Fullness on an anchored pair.** When the fibre of `G` over `U` is a groupoid and `x ≅ y` is
inhabited, every morphism `η_U x ⟶ η_U y` is the image of a morphism `x ⟶ y`. -/
theorem hom_surjective_of_anchor [IsGroupoid (G.obj (.mk (op U)))] (p : x ≅ y) :
    Function.Surjective fun f : x ⟶ y ↦ (η.app (.mk (op U))).toFunctor.map f := by
  intro q
  refine ⟨(preimageIso bF bG η p (asIso q)).hom, ?_⟩
  exact congrArg Iso.hom (map_preimageIso bF bG η p (asIso q))

/-- **Automorphisms.** The composite of the band identifications `Aut x ≃* A(U) ≃* Aut (η_U x)`. It
is the map `η_U.mapAut` (`BandedMorphism.autEquiv_apply`). -/
def autEquiv (x : F.obj (.mk (op U))) : Aut x ≃* Aut ((η.app (.mk (op U))).toFunctor.obj x) :=
  (bF.mulEquiv U x).symm.trans (bG.mulEquiv U ((η.app (.mk (op U))).toFunctor.obj x))

omit [BandPreserving bF bG η] in
@[simp]
theorem autEquiv_mulEquiv (x : F.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))) :
    autEquiv bF bG η x (bF.mulEquiv U x a) =
      bG.mulEquiv U ((η.app (.mk (op U))).toFunctor.obj x) a := by
  simp [autEquiv]

omit [BandPreserving bF bG η] in
@[simp]
theorem autEquiv_symm_mulEquiv (x : F.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))) :
    (autEquiv bF bG η x).symm (bG.mulEquiv U ((η.app (.mk (op U))).toFunctor.obj x) a) =
      bF.mulEquiv U x a := by
  rw [MulEquiv.symm_apply_eq, autEquiv_mulEquiv]

/-- The automorphism equivalence is `η_U.mapAut`, by band preservation. -/
theorem autEquiv_apply (x : F.obj (.mk (op U))) (g : Aut x) :
    autEquiv bF bG η x g = (η.app (.mk (op U))).toFunctor.mapAut x g := by
  obtain ⟨a, rfl⟩ := (bF.mulEquiv U x).surjective g
  rw [autEquiv_mulEquiv, BandPreserving.mapAut_mulEquiv (bG := bG) (η := η)]

end CategoryTheory.Pseudofunctor.BandedMorphism

namespace CategoryTheory.Pseudofunctor.BandedMorphism

/-! ### The identity transformation and composites -/

open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C] {F G H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}} (bF : F.AbelianBanding J A)
  (bG : G.AbelianBanding J A) (bH : H.AbelianBanding J A) {U : C} {x y : F.obj (.mk (op U))}

/-- For the identity transformation, the anchored bijection on isomorphisms is the identity. -/
@[simp]
theorem isomEquiv_id (p : x ≅ y) : isomEquiv bF bF (StrongTrans.id F) p = Equiv.refl (x ≅ y) :=
  -- The component of `StrongTrans.id F` is `𝟙`, whose functor is `𝟭` (`Cat.Hom.id_toFunctor`), so
  -- `isomEquiv_apply` gives `mapIso q = q` by `rfl`. The statement itself only type-checks
  -- through this reduction, which is why it cannot be reached by rewriting.
  Equiv.ext fun _ ↦ rfl

/-- For the identity transformation, the anchored inverse of `q` is `q`, for every anchor. -/
@[simp]
theorem preimageIso_id (p q : x ≅ y) : preimageIso bF bF (StrongTrans.id F) p q = q :=
  -- `q` is its own image under the identity functor (`Cat.Hom.id_toFunctor`) by `rfl`, so this is
  -- `preimageIso_map` at `q`.
  preimageIso_map bF bF (StrongTrans.id F) p q

/-- For the identity transformation, the equivalence on automorphisms is the identity. -/
@[simp]
theorem autEquiv_id (x : F.obj (.mk (op U))) :
    autEquiv bF bF (StrongTrans.id F) x = MulEquiv.refl (Aut x) :=
  MulEquiv.ext fun g ↦ by
    obtain ⟨a, rfl⟩ := (bF.mulEquiv U x).surjective g
    -- The identity functor fixes `x` by `rfl` (`Cat.Hom.id_obj`).
    exact autEquiv_mulEquiv bF bF (StrongTrans.id F) x a

/-- **Composites, on isomorphisms.** The anchored bijection of `η ≫ θ` at `p` is that of `η` at
`p` followed by that of `θ` at `η_U p`. -/
theorem isomEquiv_comp (η : F ⟶ G) (θ : G ⟶ H) [BandPreserving bF bG η] [BandPreserving bG bH θ]
    (p : x ≅ y) :
    haveI : BandPreserving bF bH (η ≫ θ) := BandPreserving.comp bG η θ
    isomEquiv bF bH (η ≫ θ) p =
      (isomEquiv bF bG η p).trans (isomEquiv bG bH θ ((η.app (.mk (op U))).toFunctor.mapIso p)) :=
  -- The component of `η ≫ θ` is `η_U ≫ θ_U` (`StrongTrans.comp_app`), whose functor is
  -- `η_U ⋙ θ_U` (`Cat.Hom.comp_toFunctor`), and both hold by `rfl`. The statement itself only
  -- type-checks through these reductions, which is why it cannot be reached by rewriting.
  Equiv.ext fun _ ↦ rfl

/-- **Composites, anchored inverse.** The anchored inverse of `η ≫ θ` at `p` is the anchored
inverse of `η` at `p` applied to the anchored inverse of `θ` at `η_U p`. -/
theorem preimageIso_comp (η : F ⟶ G) (θ : G ⟶ H) [BandPreserving bF bG η]
    [BandPreserving bG bH θ] (p : x ≅ y)
    (q : ((η ≫ θ).app (.mk (op U))).toFunctor.obj x ≅ ((η ≫ θ).app (.mk (op U))).toFunctor.obj y) :
    haveI : BandPreserving bF bH (η ≫ θ) := BandPreserving.comp bG η θ
    preimageIso bF bH (η ≫ θ) p q =
      preimageIso bF bG η p
        (preimageIso bG bH θ ((η.app (.mk (op U))).toFunctor.mapIso p) q) := by
  have : BandPreserving bF bH (η ≫ θ) := BandPreserving.comp bG η θ
  rw [← isomEquiv_symm_apply, isomEquiv_comp bF bG bH η θ p]
  -- `rw [Equiv.symm_trans_apply]` fails: the codomains agree only up to `StrongTrans.comp_app`.
  exact Equiv.symm_trans_apply _ _ q

/-- **Composites, on automorphisms.** The equivalence on automorphisms of `η ≫ θ` is that of `η`
followed by that of `θ`. -/
theorem autEquiv_comp (η : F ⟶ G) (θ : G ⟶ H) (x : F.obj (.mk (op U))) :
    autEquiv bF bH (η ≫ θ) x =
      (autEquiv bF bG η x).trans (autEquiv bG bH θ ((η.app (.mk (op U))).toFunctor.obj x)) :=
  MulEquiv.ext fun g ↦ by
    obtain ⟨a, rfl⟩ := (bF.mulEquiv U x).surjective g
    -- `(η ≫ θ)_U x` is `θ_U (η_U x)` by `rfl` (`StrongTrans.comp_app`, `Cat.Hom.comp_obj`).
    exact (autEquiv_mulEquiv bF bH (η ≫ θ) x a).trans
      ((congrArg (autEquiv bG bH θ _) (autEquiv_mulEquiv bF bG η x a)).trans
        (autEquiv_mulEquiv bG bH θ _ a)).symm

end CategoryTheory.Pseudofunctor.BandedMorphism
