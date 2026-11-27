/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.PreTorsor

/-!
# Contracted products of torsors with sheaves of sets with an action

Let `G` be a sheaf of groups on a site `(C, J)`, `P` a `G`-torsor and `X` a sheaf of sets with a
left action of `G`. The *contracted product* `P ×^G X` is the sheafification of the presheaf
`U ↦ (P(U) × X(U)) / G(U)`, the quotient by the diagonal action `g • (p, x) = (g • p, g • x)`.
It is the sheaf-theoretic form of the associated bundle of a principal bundle: a torsor `P`
twists `X` into a sheaf `P ×^G X` which is locally isomorphic to `X`, and which is `X` itself
when `P` is trivial.

This file develops the contracted product of a torsor with a sheaf of sets with an action and
characterizes it. The quotient map `P × X → P ×^G X` is universal among `G`-invariant morphisms
to sheaves of sets. Over any object `U` over which `P` has a section `p`, the map `x ↦ [p, x]`
is a bijection `X(U) ≃ (P ×^G X)(U)`; in particular two classes `[p, x]` and `[p', x']` over `U`
agree exactly when `(p', x') = g • (p, x)` for some `g`. As a consequence:

* a global section of `P` gives an isomorphism `X ≅ P ×^G X`, and for the trivial torsor
  `G ×^G X ≅ X`;
* if `G` acts trivially on `X`, then `P ×^G X ≅ X` for every torsor `P`;
* the contracted product is functorial in `X`;
* for a morphism `φ : G ⟶ G'` of sheaves of groups, the torsor `Torsor.map φ P` obtained by
  extending the structure group has underlying sheaf `P ×^G G'`, where `G` acts on `G'` by
  `g • a = a * φ(g)⁻¹`.

The torsor `Torsor.map φ P` is itself built here from the same quotient presheaf, specialised to
`MulActionSheaf.mulRight φ`: it carries an action of `G'` by left multiplication on the second
factor, and `p ↦ [p, 1]` is a `φ`-equivariant morphism `P → P ×^G G'` which is universal among
`φ`-equivariant morphisms from `P` to `G'`-torsors. The induced map on `H¹` is in
`NonabelianCohomology.Map`.

## Main declarations

* `CategoryTheory.Sheaf.MulActionSheaf G`: a sheaf of sets with a left action of `G`, and the
  category of these, whose morphisms are the `G`-equivariant morphisms of sheaves.
* `CategoryTheory.Sheaf.MulActionSheaf.mulRight φ`: the sheaf `G'` with `G` acting through
  `φ : G ⟶ G'` by right multiplication with the inverse.
* `CategoryTheory.Sheaf.Torsor.contractedProduct P X`: the contracted product `P ×^G X`.
* `CategoryTheory.Sheaf.Torsor.toContractedProduct P X`: the quotient map `P × X → P ×^G X`,
  with `Torsor.contractedProductDesc` and `Torsor.contractedProduct_hom_ext` (the universal
  property).
* `CategoryTheory.Sheaf.Torsor.contractedProductMk p x`: the class `[p, x]`, with
  `Torsor.contractedProductMk_smul`.
* `CategoryTheory.Sheaf.Torsor.contractedProductObjEquiv p`: the bijection
  `X(U) ≃ (P ×^G X)(U)`, `x ↦ [p, x]`, for a section `p` of `P` over `U`.
* `CategoryTheory.Sheaf.Torsor.contractedProductMk_eq_contractedProductMk_iff`: equality of
  classes.
* `CategoryTheory.Sheaf.Torsor.contractedProductCompIsoOfSection`: compatible sections of `P`
  along a functor `u` identify the restrictions of `X` and of `P ×^G X` along `u`.
* `CategoryTheory.Sheaf.Torsor.contractedProductIsoOfSection`,
  `CategoryTheory.Sheaf.Torsor.contractedProductTrivialIso`,
  `CategoryTheory.Sheaf.Torsor.contractedProductIsoOfSMulEqSelf` and
  `CategoryTheory.Sheaf.Torsor.contractedProductMulRightIso`: the identifications above.
* `CategoryTheory.Sheaf.Torsor.contractedProductMap` and
  `CategoryTheory.Sheaf.Torsor.contractedProductFunctor P`: `X ↦ P ×^G X` as a functor.
* `CategoryTheory.Sheaf.Torsor.map φ P`: the `G'`-torsor `P ×^G G'` obtained by extending the
  structure group along `φ : G ⟶ G'`.
* `CategoryTheory.Sheaf.Torsor.toMap φ P`: the `φ`-equivariant morphism `P → P ×^G G'`.
* `CategoryTheory.Sheaf.Torsor.mapLift`: a `φ`-equivariant morphism `P → R` to a `G'`-torsor
  induces a morphism of `G'`-torsors `P ×^G G' ⟶ R`; `Torsor.map_hom_ext` is its uniqueness.

## References

* J. Giraud, *Cohomologie non abélienne*, Chapitre III, §1.3, for the contracted product of a
  torsor with an object with an action of the structure group.
* B. Poonen, *Rational points on varieties*, §§5.12.5 and 6.5.6, for contracted products and
  the twisting of objects by torsors.
-/

public noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G G' : Sheaf J GrpCat.{w}}

/-- A sheaf of sets with a left action of a sheaf of groups `G`: the sections of `G` over each
object act on the sections of the sheaf, compatibly with restriction. -/
structure MulActionSheaf (G : Sheaf J GrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf J (Type w)
  /-- The action of the sections of `G` on the sections of the sheaf. -/
  [mulAction (U : Cᵒᵖ) : MulAction (G.obj.obj U) (sheaf.obj.obj U)]
  /-- The action commutes with restriction. -/
  map_smul ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (g : G.obj.obj U) (x : sheaf.obj.obj U) :
    sheaf.obj.map f (g • x) = G.obj.map f g • sheaf.obj.map f x

attribute [instance] MulActionSheaf.mulAction

namespace MulActionSheaf

/-- A morphism of sheaves of sets with an action of `G`: a `G`-equivariant morphism of the
underlying sheaves. -/
@[ext]
structure Hom (X Y : MulActionSheaf G) where
  /-- The underlying morphism of sheaves. -/
  hom : X.sheaf ⟶ Y.sheaf
  /-- The morphism is `G`-equivariant. -/
  map_smul (U : Cᵒᵖ) (g : G.obj.obj U) (x : X.sheaf.obj.obj U) :
    hom.hom.app U (g • x) = g • hom.hom.app U x

instance : Category (MulActionSheaf G) where
  Hom := Hom
  id X := ⟨𝟙 _, fun _ _ _ ↦ rfl⟩
  comp f g := ⟨f.hom ≫ g.hom, fun U a x ↦ by simp [f.map_smul, g.map_smul]⟩

variable {X Y Z : MulActionSheaf G}

@[ext]
lemma hom_ext {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
lemma id_hom (X : MulActionSheaf G) : Hom.hom (𝟙 X) = 𝟙 X.sheaf := rfl

@[simp]
lemma comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The sheaf `G'`, viewed as a sheaf of sets, with `G` acting through a morphism
`φ : G ⟶ G'` of sheaves of groups by right multiplication with the inverse,
`g • a = a * φ(g)⁻¹`. This action commutes with left multiplication by `G'`, and contracting a
`G`-torsor with it extends the structure group along `φ`
(see `Torsor.contractedProductMulRightIso`).

The body is exposed because the sections of `mulRight φ` are, by definition, the sections of
`G'`; statements about it apply group operations of `G'` to them. Use `mulRight_smul` rather
than unfolding it. -/
@[expose] def mulRight (φ : G ⟶ G') : MulActionSheaf G where
  sheaf := (sheafCompose J (forget GrpCat.{w})).obj G'
  mulAction U := MulAction.compHom (G'.obj.obj U)
    ((MulEquiv.inv' (G'.obj.obj U)).toMonoidHom.comp (φ.hom.app U).hom)
  map_smul U _ f g (a : G'.obj.obj U) :=
    (map_mul (G'.obj.map f).hom a _).trans (congrArg ((G'.obj.map f).hom a * ·)
      ((map_inv (G'.obj.map f).hom _).trans
        (congrArg (·⁻¹) (NatTrans.naturality_apply φ.hom f g).symm)))

/-- `G` acts on `mulRight φ` by right multiplication with the inverse of the image under `φ`. -/
@[simp]
lemma mulRight_smul (φ : G ⟶ G') {U : Cᵒᵖ} (g : G.obj.obj U)
    (a : (mulRight φ).sheaf.obj.obj U) :
    g • a = @HMul.hMul (G'.obj.obj U) (G'.obj.obj U) _ _ a (φ.hom.app U g)⁻¹ :=
  rfl

end MulActionSheaf

namespace Torsor

variable (P : Torsor G) (X : MulActionSheaf G)

/-- The relation on `P(U) × X(U)` generating the contracted product: `(p, x)` is related to
`(g • p, g • x)`. -/
private def ContractedRel (U : Cᵒᵖ) (a b : P.sheaf.obj.obj U × X.sheaf.obj.obj U) : Prop :=
  ∃ g : G.obj.obj U, b = (g • a.1, g • a.2)

/-- The presheaf `U ↦ (P(U) × X(U)) / G(U)` whose sheafification is the contracted product. -/
private def contractedPresheaf : Cᵒᵖ ⥤ Type w where
  obj U := Quot (ContractedRel P X U)
  map {U V} f := ↾Quot.map (fun a ↦ (P.sheaf.obj.map f a.1, X.sheaf.obj.map f a.2)) (by
    rintro a _ ⟨g, rfl⟩
    exact ⟨G.obj.map f g, Prod.ext (P.map_smul f g a.1) (X.map_smul f g a.2)⟩)
  map_id U := by
    ext y
    induction y using Quot.ind
    exact congrArg (Quot.mk _) (Prod.ext (by simp) (by simp))
  map_comp f g := by
    ext y
    induction y using Quot.ind
    exact congrArg (Quot.mk _) (Prod.ext (by simp) (by simp))

/-- The quotient map from `P × X` to the contracted presheaf. -/
private def toContractedPresheaf : P.sheaf.obj ⊗ X.sheaf.obj ⟶ contractedPresheaf P X where
  app U := ↾fun a : P.sheaf.obj.obj U × X.sheaf.obj.obj U ↦ Quot.mk _ a
  naturality _ _ _ := rfl

/-- Over an object over which `P` has a section `p`, the map `x ↦ [p, x]` to the contracted
presheaf is bijective, because `G` acts simply transitively on `P`. -/
private lemma bijective_mk {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) :
    Function.Bijective fun x : X.sheaf.obj.obj U ↦
      (Quot.mk _ (p, x) : (contractedPresheaf P X).obj U) := by
  refine ⟨fun x y h ↦ ?_, fun z ↦ ?_⟩
  · -- The class of `(q, z)` determines `z` up to the element `g` with `g • p = q`.
    let inv : Quot (ContractedRel P X U) → Prop :=
      Quot.lift (fun a ↦ ∃ g : G.obj.obj U, g • p = a.1 ∧ a.2 = g • y) (by
        rintro a _ ⟨k, rfl⟩
        refine propext ⟨fun ⟨g, hg, hgy⟩ ↦ ⟨k * g, by rw [mul_smul, hg], ?_⟩,
          fun ⟨g, hg, hgy⟩ ↦ ⟨k⁻¹ * g, by rw [mul_smul, hg, inv_smul_smul], ?_⟩⟩
        · simp [hgy, mul_smul]
        · simp [← hgy, mul_smul])
    obtain ⟨g, hg, rfl⟩ : inv (Quot.mk _ (p, x)) :=
      (congrArg inv h).mpr ⟨1, one_smul _ _, by simp⟩
    obtain rfl : g = 1 := P.smul_left_injective p (hg.trans (one_smul _ _).symm)
    exact one_smul _ _
  · induction z using Quot.ind with | mk a => ?_
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G.obj.obj U) p a.1
    exact ⟨g⁻¹ • a.2, Quot.sound ⟨g, Prod.ext hg.symm (smul_inv_smul g a.2).symm⟩⟩

variable [HasWeakSheafify J (Type w)]

/-- The contracted product `P ×^G X` of a `G`-torsor `P` with a sheaf of sets `X` with an action
of `G`: the sheafification of the quotient of `P × X` by the diagonal action of `G`.
Use `toContractedProduct`, `contractedProductMk`, `contractedProductDesc`,
`contractedProduct_hom_ext` and `contractedProductObjEquiv` rather than unfolding it. -/
def contractedProduct : Sheaf J (Type w) :=
  (presheafToSheaf J (Type w)).obj (contractedPresheaf P X)

/-- The quotient map `P × X → P ×^G X`, `(p, x) ↦ [p, x]`. -/
def toContractedProduct : P.sheaf ⊗ X.sheaf ⟶ P.contractedProduct X :=
  ObjectProperty.homMk (toContractedPresheaf P X ≫ toSheafify J (contractedPresheaf P X))

variable {P X} in
/-- The class `[p, x]` in the contracted product of sections `p` of `P` and `x` of `X` over the
same object. -/
def contractedProductMk {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U) :
    (P.contractedProduct X).obj.obj U :=
  (toSheafify J (contractedPresheaf P X)).app U (Quot.mk _ (p, x))

/-- The quotient map sends `(p, x)` to the class `[p, x]`. -/
lemma toContractedProduct_hom_app {U : Cᵒᵖ} (a : P.sheaf.obj.obj U × X.sheaf.obj.obj U) :
    (P.toContractedProduct X).hom.app U a = contractedProductMk a.1 a.2 :=
  (rfl)

variable {P X}

/-- The classes of `(g • p, g • x)` and `(p, x)` in the contracted product agree. -/
@[simp]
lemma contractedProductMk_smul {U : Cᵒᵖ} (g : G.obj.obj U) (p : P.sheaf.obj.obj U)
    (x : X.sheaf.obj.obj U) :
    contractedProductMk (g • p) (g • x) = contractedProductMk p x :=
  congrArg ((toSheafify J (contractedPresheaf P X)).app U) (Quot.sound ⟨g, rfl⟩).symm

/-- The class `[p, x]` commutes with restriction: the restriction of `[p, x]` is the class of the
restrictions of `p` and `x`. -/
@[simp]
lemma contractedProduct_map_contractedProductMk {U V : Cᵒᵖ} (f : U ⟶ V)
    (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U) :
    (P.contractedProduct X).obj.map f (contractedProductMk p x) =
      contractedProductMk (P.sheaf.obj.map f p) (X.sheaf.obj.map f x) :=
  (NatTrans.naturality_apply (toSheafify J (contractedPresheaf P X)) f (Quot.mk _ (p, x))).symm

/-- Morphisms out of the contracted product are determined by their composite with the
quotient map `P × X → P ×^G X`. -/
lemma contractedProduct_hom_ext {Y : Sheaf J (Type w)} {f f' : P.contractedProduct X ⟶ Y}
    (h : P.toContractedProduct X ≫ f = P.toContractedProduct X ≫ f') : f = f' := by
  refine ObjectProperty.hom_ext _ (sheafify_hom_ext J _ _ Y.property ?_)
  ext U y
  induction y using Quot.ind with | mk a => ?_
  exact congrArg (fun k ↦ k.hom.app U a) h

/-- A `G`-invariant morphism `u : P × X → Y` to a sheaf of sets factors through the contracted
product, sending `[p, x]` to `u (p, x)`. -/
def contractedProductDesc {Y : Sheaf J (Type w)} (u : P.sheaf ⊗ X.sheaf ⟶ Y)
    (hu : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U),
      u.hom.app U (g • p, g • x) = u.hom.app U (p, x)) :
    P.contractedProduct X ⟶ Y :=
  ObjectProperty.homMk (sheafifyLift J
    { app U := ↾Quot.lift (fun a ↦ u.hom.app U a) (by
        rintro a _ ⟨g, rfl⟩
        exact (hu U g a.1 a.2).symm)
      naturality U V f := by
        ext y
        induction y using Quot.ind with | mk a => ?_
        exact NatTrans.naturality_apply u.hom f a }
    Y.property)

/-- The morphism induced by a `G`-invariant `u : P × X → Y` restricts to `u` along the quotient
map. -/
@[reassoc (attr := simp)]
lemma toContractedProduct_contractedProductDesc {Y : Sheaf J (Type w)}
    (u : P.sheaf ⊗ X.sheaf ⟶ Y)
    (hu : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U),
      u.hom.app U (g • p, g • x) = u.hom.app U (p, x)) :
    P.toContractedProduct X ≫ contractedProductDesc u hu = u := by
  ext U a
  exact congrArg (fun k : contractedPresheaf P X ⟶ Y.obj ↦ k.app U (Quot.mk _ a))
    (toSheafify_sheafifyLift J _ Y.property)

/-- Elementwise form of `toContractedProduct_contractedProductDesc`. -/
@[simp]
lemma contractedProductDesc_hom_app_contractedProductMk {Y : Sheaf J (Type w)}
    (u : P.sheaf ⊗ X.sheaf ⟶ Y)
    (hu : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U),
      u.hom.app U (g • p, g • x) = u.hom.app U (p, x))
    {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U) :
    (contractedProductDesc u hu).hom.app U (contractedProductMk p x) = u.hom.app U (p, x) :=
  congrArg (fun k ↦ k.hom.app U (p, x)) (toContractedProduct_contractedProductDesc u hu)

/-- The quotient map composed with `P × f`, for an equivariant `f : X ⟶ Y`, is `G`-invariant. -/
private lemma whiskerLeft_toContractedProduct_smul {Y : MulActionSheaf G} (f : X ⟶ Y)
    (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U) :
    (P.sheaf ◁ f.hom ≫ P.toContractedProduct Y).hom.app U (g • p, g • x) =
      (P.sheaf ◁ f.hom ≫ P.toContractedProduct Y).hom.app U (p, x) :=
  (congrArg (contractedProductMk (g • p)) (f.map_smul U g x)).trans (contractedProductMk_smul g p _)

/-- The morphism of contracted products `P ×^G X ⟶ P ×^G Y`, `[p, x] ↦ [p, f x]`, induced by an
equivariant morphism `f : X ⟶ Y`. -/
def contractedProductMap {Y : MulActionSheaf G} (f : X ⟶ Y) :
    P.contractedProduct X ⟶ P.contractedProduct Y :=
  contractedProductDesc _ (whiskerLeft_toContractedProduct_smul f)

/-- The morphism of contracted products induced by an equivariant `f : X ⟶ Y` restricts to
`P × f` along the quotient maps. -/
@[reassoc (attr := simp)]
lemma toContractedProduct_contractedProductMap {Y : MulActionSheaf G} (f : X ⟶ Y) :
    P.toContractedProduct X ≫ contractedProductMap f =
      P.sheaf ◁ f.hom ≫ P.toContractedProduct Y :=
  toContractedProduct_contractedProductDesc _ (whiskerLeft_toContractedProduct_smul f)

/-- The morphism of contracted products induced by an equivariant `f : X ⟶ Y` sends `[p, x]` to
`[p, f x]`. -/
@[simp]
lemma contractedProductMap_hom_app_contractedProductMk {Y : MulActionSheaf G}
    (f : X ⟶ Y) {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U) :
    (contractedProductMap f).hom.app U (contractedProductMk p x) =
      contractedProductMk p (f.hom.hom.app U x) :=
  contractedProductDesc_hom_app_contractedProductMk _ (whiskerLeft_toContractedProduct_smul f) p x

@[simp]
lemma contractedProductMap_id : contractedProductMap (P := P) (𝟙 X) = 𝟙 _ :=
  contractedProduct_hom_ext (by simp)

@[reassoc, simp]
lemma contractedProductMap_comp {Y Z : MulActionSheaf G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    contractedProductMap (P := P) (f ≫ g) = contractedProductMap f ≫ contractedProductMap g :=
  contractedProduct_hom_ext (by simp)

/-- The contracted product `X ↦ P ×^G X` as a functor from sheaves of sets with an action of
`G` to sheaves of sets, acting on morphisms by `contractedProductMap`. Its body is exposed so
that its values are `contractedProduct` and `contractedProductMap` by definition. -/
@[expose, simps]
def contractedProductFunctor (P : Torsor G) : MulActionSheaf G ⥤ Sheaf J (Type w) where
  obj X := P.contractedProduct X
  map f := contractedProductMap f
  map_id _ := contractedProductMap_id
  map_comp := contractedProductMap_comp

variable [J.WEqualsLocallyBijective (Type w)]

/-- Over an object over which `P` has a section `p`, the map `x ↦ [p, x]` to the contracted
product is injective: two of its values agree locally in the contracted presheaf, hence their
arguments agree locally, hence agree because `X` is a sheaf. -/
private lemma injective_toContractedProduct_app {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) :
    Function.Injective (contractedProductMk (X := X) p) :=
  fun _ _ h ↦ (((isSheaf_iff_isSheaf_of_type J _).1 X.sheaf.property).isSeparated _
    (Presheaf.equalizerSieve_mem J (toSheafify J (contractedPresheaf P X)) _ _ h)).ext
      fun _ f hf ↦ (bijective_mk P X (P.sheaf.obj.map f.op p)).1 hf

/-- Over an object over which `P` has a section `p`, the map `x ↦ [p, x]` to the contracted
product is surjective. A section `z` is locally the class of `(p, x_f)` for unique `x_f`; by
uniqueness these local sections of `X` are compatible, and their gluing `x` satisfies
`[p, x] = z` locally, hence everywhere. -/
private lemma surjective_toContractedProduct_app {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) :
    Function.Surjective (contractedProductMk (X := X) p) := by
  intro z
  let η := toSheafify J (contractedPresheaf P X)
  have hX := (isSheaf_iff_isSheaf_of_type J _).1 X.sheaf.property
  have hQ := (isSheaf_iff_isSheaf_of_type J _).1 (P.contractedProduct X).property
  let S := Presheaf.imageSieve η z
  -- Over `f : V ⟶ U` in `S`, the local preimage of `z` is the class of `(p|V, x_f)`.
  let x : Presieve.FamilyOfElements X.sheaf.obj S.arrows := fun V f hf ↦
    (Equiv.ofBijective _ (bijective_mk P X (P.sheaf.obj.map f.op p))).symm
      (Presheaf.localPreimage η z f hf)
  have hx {V : C} (f : V ⟶ U.unop) (hf : S f) :
      contractedProductMk (P.sheaf.obj.map f.op p) (x f hf) =
        (P.contractedProduct X).obj.map f.op z := by
    refine (congrArg (η.app _) ((Equiv.ofBijective _ (bijective_mk P X _)).apply_symm_apply
      _)).trans ?_
    exact Presheaf.app_localPreimage η z f hf
  have hcompat : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W f g hf
    refine injective_toContractedProduct_app (P.sheaf.obj.map (g ≫ f).op p) ?_
    dsimp only
    rw [hx, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ← hx f hf,
      contractedProduct_map_contractedProductMk]
  obtain ⟨y, hy, -⟩ := hX S (Presheaf.imageSieve_mem J η z) x hcompat
  refine ⟨y, (hQ.isSeparated _ (Presheaf.imageSieve_mem J η z)).ext fun V f hf ↦ ?_⟩
  rw [← hx f hf, ← hy f hf]
  exact contractedProduct_map_contractedProductMk f.op p y

/-- For a section `p` of `P` over `U`, the bijection `X(U) ≃ (P ×^G X)(U)`, `x ↦ [p, x]`.
Together with `contractedProduct_map_contractedProductMk`, it is the sectionwise form of the
statement that the contracted product is locally isomorphic to `X`. -/
def contractedProductObjEquiv {U : Cᵒᵖ} (p : P.sheaf.obj.obj U) :
    X.sheaf.obj.obj U ≃ (P.contractedProduct X).obj.obj U :=
  Equiv.ofBijective _
    ⟨injective_toContractedProduct_app p, surjective_toContractedProduct_app p⟩

@[simp]
lemma contractedProductObjEquiv_apply {U : Cᵒᵖ} (p : P.sheaf.obj.obj U)
    (x : X.sheaf.obj.obj U) :
    contractedProductObjEquiv p x = contractedProductMk p x :=
  (rfl)

@[simp]
lemma contractedProductObjEquiv_symm_apply_toContractedProduct {U : Cᵒᵖ}
    (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U) :
    (contractedProductObjEquiv p).symm (contractedProductMk p x) = x :=
  (contractedProductObjEquiv p).symm_apply_apply x

/-- Two classes `[p, x]` and `[p', x']` in the contracted product over the same object agree if
and only if `(p', x') = g • (p, x)` for some section `g` of `G`. -/
lemma contractedProductMk_eq_contractedProductMk_iff {U : Cᵒᵖ} {p p' : P.sheaf.obj.obj U}
    {x x' : X.sheaf.obj.obj U} :
    contractedProductMk p x = contractedProductMk p' x' ↔
      ∃ g : G.obj.obj U, p' = g • p ∧ x' = g • x := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (G.obj.obj U) p p'
    refine ⟨g, rfl, ?_⟩
    have h' := h.trans ((contractedProductMk_smul g⁻¹ (g • p) x').symm.trans
      (by rw [inv_smul_smul]))
    rw [injective_toContractedProduct_app p h', smul_inv_smul]
  · rintro ⟨g, rfl, rfl⟩
    exact (contractedProductMk_smul g p x).symm

variable (X) in
/-- The morphism `X → P ×^G X`, `x ↦ [s, x]`, for a global section `s` of `P`. -/
private def ofSection (s : P.sheaf.obj.sections) : X.sheaf ⟶ P.contractedProduct X :=
  ObjectProperty.homMk
    { app U := ↾fun x ↦ contractedProductObjEquiv (s.val U) x
      naturality U V f := by
        ext x
        dsimp
        rw [contractedProductObjEquiv_apply, contractedProductObjEquiv_apply,
          contractedProduct_map_contractedProductMk, s.property f] }

variable (P X) in
/-- A global section `s` of `P` identifies `X` with the contracted product, `x ↦ [s, x]`. -/
def contractedProductIsoOfSection (s : P.sheaf.obj.sections) : X.sheaf ≅ P.contractedProduct X :=
  have : IsIso (ofSection X s) :=
    isIso_of_bijective_app P _ fun U _ ↦ (contractedProductObjEquiv (s.val (op U))).bijective
  asIso (ofSection X s)

@[simp]
lemma contractedProductIsoOfSection_hom_hom_app (s : P.sheaf.obj.sections) {U : Cᵒᵖ}
    (x : X.sheaf.obj.obj U) :
    (P.contractedProductIsoOfSection X s).hom.hom.app U x =
      contractedProductMk (s.val U) x :=
  (rfl)

variable (X) in
/-- Compatible sections `s` of `P` along a functor `u : D ⥤ C` identify the restrictions of `X` and
of the contracted product along `u`, by `x ↦ [s d, x]` over `u d`. This is the form, relative to
`u`, of `contractedProductIsoOfSection`: for instance, a section of `P` over an object `T` of a
big site identifies `X` and `P ×^G X` over every object over `T`. -/
def contractedProductCompIsoOfSection {D : Type*} [Category D] (u : D ⥤ C)
    (s : ∀ d : D, P.sheaf.obj.obj (op (u.obj d)))
    (hs : ∀ ⦃d d' : D⦄ (f : d ⟶ d'), P.sheaf.obj.map (u.map f).op (s d') = s d) :
    u.op ⋙ X.sheaf.obj ≅ u.op ⋙ (P.contractedProduct X).obj :=
  NatIso.ofComponents (fun d ↦ (contractedProductObjEquiv (X := X) (s d.unop)).toIso)
    fun {d d'} f ↦ by
      ext x
      exact (congrArg (contractedProductMk · _) (hs f.unop)).symm.trans
        (contractedProduct_map_contractedProductMk _ _ _).symm

/-- The isomorphism `contractedProductCompIsoOfSection` sends `x` over `u d` to `[s d, x]`. -/
-- Apply before `Functor.comp_obj` and `Functor.op_obj` normalize the types of the component.
@[simp↓]
lemma contractedProductCompIsoOfSection_hom_app_apply {D : Type*} [Category D] (u : D ⥤ C)
    (s : ∀ d : D, P.sheaf.obj.obj (op (u.obj d)))
    (hs : ∀ ⦃d d' : D⦄ (f : d ⟶ d'), P.sheaf.obj.map (u.map f).op (s d') = s d) (d : Dᵒᵖ)
    (x : X.sheaf.obj.obj (op (u.obj d.unop))) :
    (P.contractedProductCompIsoOfSection X u s hs).hom.app d x = contractedProductMk (s d.unop) x :=
  (rfl)

variable (X) in
/-- The contracted product with the trivial torsor: `G ×^G X ≅ X`, `[g, x] ↦ g⁻¹ • x`. -/
def contractedProductTrivialIso : (trivial G).contractedProduct X ≅ X.sheaf :=
  ((trivial G).contractedProductIsoOfSection X
    ⟨fun U ↦ (1 : G.obj.obj U), fun f ↦ map_one (G.obj.map f).hom⟩).symm

/-- The isomorphism `G ×^G X ≅ X` sends `[g, x]` to `g⁻¹ • x`. -/
@[simp]
lemma contractedProductTrivialIso_hom_hom_app_contractedProductMk {U : Cᵒᵖ}
    (g : G.obj.obj U) (x : X.sheaf.obj.obj U) :
    (contractedProductTrivialIso X).hom.hom.app U
        (contractedProductMk (P := trivial G) g x) = g⁻¹ • x := by
  let e := (trivial G).contractedProductIsoOfSection X
    ⟨fun U ↦ (1 : G.obj.obj U), fun f ↦ map_one (G.obj.map f).hom⟩
  -- `[1, g⁻¹ • x] = [g • 1, g • g⁻¹ • x] = [g, x]`.
  have h : e.hom.hom.app U (g⁻¹ • x) = contractedProductMk (P := trivial G) g x := by
    refine (contractedProductIsoOfSection_hom_hom_app _ _).trans
      (contractedProductMk_eq_contractedProductMk_iff.2 ⟨g, ?_, (smul_inv_smul g x).symm⟩)
    exact (mul_one g).symm
  exact (congrArg (e.inv.hom.app U) h.symm).trans
    (congrArg (fun k ↦ k.hom.app U (g⁻¹ • x)) e.hom_inv_id)

variable (P) in
/-- If `G` acts trivially on `X`, then the contracted product of any `G`-torsor with `X` is `X`
itself, `[p, x] ↦ x`. -/
def contractedProductIsoOfSMulEqSelf
    (hX : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (x : X.sheaf.obj.obj U), g • x = x) :
    P.contractedProduct X ≅ X.sheaf :=
  letI f := contractedProductDesc (P := P) (snd P.sheaf X.sheaf) fun U g _ x ↦ hX U g x
  have : IsIso f :=
    isIso_of_bijective_app P _ fun U ⟨p⟩ ↦ by
      -- Composed with the bijection `x ↦ [p, x]`, the morphism is the identity of `X(U)`.
      refine (Function.Bijective.of_comp_iff _
        (contractedProductObjEquiv (X := X) p).bijective).1 ?_
      convert Function.bijective_id
      ext x
      exact contractedProductDesc_hom_app_contractedProductMk _ _ p x
  asIso f

/-- If `G` acts trivially on `X`, the isomorphism `P ×^G X ≅ X` sends `[p, x]` to `x`. -/
@[simp]
lemma contractedProductIsoOfSMulEqSelf_hom_hom_app_contractedProductMk
    (hX : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (x : X.sheaf.obj.obj U), g • x = x) {U : Cᵒᵖ}
    (p : P.sheaf.obj.obj U) (x : X.sheaf.obj.obj U) :
    (P.contractedProductIsoOfSMulEqSelf hX).hom.hom.app U
        (contractedProductMk p x) = x :=
  contractedProductDesc_hom_app_contractedProductMk (P := P) (snd P.sheaf X.sheaf)
    (fun U g _ x ↦ hX U g x) p x

end Torsor

/-! ### Extending the structure group -/

namespace Torsor

variable (φ : G ⟶ G') (P : Torsor G)

/-- The contracted product of `P` with `MulActionSheaf.mulRight φ` before sheafification, a
`G'`-pretorsor under left multiplication on the second factor, `a • [p, b] = [p, a * b]`. -/
private def contracted : PreTorsor G' where
  presheaf := contractedPresheaf P (MulActionSheaf.mulRight φ)
  mulAction U :=
    { smul a := Quot.map (fun x : P.sheaf.obj.obj U × G'.obj.obj U ↦ (x.1, a * x.2)) (by
        rintro x _ ⟨g, rfl⟩
        exact ⟨g, Prod.ext rfl (mul_assoc a x.2 (φ.hom.app U g)⁻¹).symm⟩)
      one_smul y := by
        induction y using Quot.ind with | mk x => ?_
        exact congrArg (Quot.mk _) (Prod.ext rfl (one_mul (M := G'.obj.obj U) x.2))
      mul_smul a b y := by
        induction y using Quot.ind with | mk x => ?_
        exact congrArg (Quot.mk _) (Prod.ext rfl (mul_assoc a b x.2)) }
  map_smul U V f a y := by
    induction y using Quot.ind with | mk x => ?_
    exact congrArg (Quot.mk _) (Prod.ext rfl (map_mul (G'.obj.map f).hom a x.2))
  coversTop X := J.superset_covering (by
    rintro Y a ⟨⟨V, ⟨p⟩⟩, ⟨b⟩⟩
    exact ⟨⟨V, ⟨Quot.mk _ (p, (1 : G'.obj.obj (op V)))⟩⟩, ⟨b⟩⟩) (P.coversTop X)
  bijective U := by
    refine ⟨fun ⟨a, y⟩ ⟨b, y'⟩ h ↦ ?_, fun ⟨z, y⟩ ↦ ?_⟩
    · obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 h
      induction y using Quot.ind with | mk x => ?_
      obtain ⟨p, (c : G'.obj.obj U)⟩ := x
      have h₂ : a * c = b * c := (bijective_mk P _ p).1 h₁
      exact Prod.ext (mul_right_cancel h₂) rfl
    · induction y using Quot.ind with | mk x => ?_
      obtain ⟨p, (b : G'.obj.obj U)⟩ := x
      obtain ⟨(c : G'.obj.obj U), rfl⟩ := (bijective_mk P _ p).2 z
      exact ⟨(c * b⁻¹, Quot.mk _ (p, b)),
        Prod.ext (congrArg (Quot.mk _) (Prod.ext rfl (inv_mul_cancel_right c b))) rfl⟩

/-- The map `p ↦ [p, 1]` from `P` to the contracted product before sheafification. -/
private def toContracted : P.sheaf.obj ⟶ (contracted φ P).presheaf where
  app U := ↾fun p ↦ Quot.mk _ (p, (1 : G'.obj.obj U))
  naturality U V f := by
    ext p
    exact congrArg (Quot.mk _) (Prod.ext rfl (map_one (G'.obj.map f).hom).symm)

/-- The map `p ↦ [p, 1]` is `φ`-equivariant: the classes of `(g • p, 1)` and `(p, φ(g))`
agree. -/
private lemma toContracted_smul {U : Cᵒᵖ} (g : G.obj.obj U) (p : P.sheaf.obj.obj U) :
    (toContracted φ P).app U (g • p) = φ.hom.app U g • (toContracted φ P).app U p :=
  (Quot.sound ⟨g, Prod.ext rfl ((MulActionSheaf.mulRight_smul φ g _).trans
    ((congrArg (· * _) (mul_one (M := G'.obj.obj U) _)).trans
      (mul_inv_cancel (G := G'.obj.obj U) _))).symm⟩).symm

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

/-- The contracted product `P ×^G G'` of a `G`-torsor `P` along a morphism `φ : G ⟶ G'` of
sheaves of groups: the `G'`-torsor obtained from `P` by extending its structure group along `φ`.
Use `toMap`, `toMap_smul`, `mapLift`, `map_hom_ext` and `contractedProductMulRightIso` rather
than unfolding it. -/
def map : Torsor G' :=
  (contracted φ P).sheafify

/-- The morphism `P → P ×^G G'`, `p ↦ [p, 1]`. -/
def toMap : P.sheaf ⟶ (P.map φ).sheaf :=
  ObjectProperty.homMk (toContracted φ P ≫ (contracted φ P).toSheafify)

/-- The morphism `P → P ×^G G'` is `φ`-equivariant. -/
@[simp]
lemma toMap_smul {U : Cᵒᵖ} (g : G.obj.obj U) (p : P.sheaf.obj.obj U) :
    (P.toMap φ).hom.app U (g • p) = φ.hom.app U g • (P.toMap φ).hom.app U p :=
  (congrArg ((contracted φ P).toSheafify.app U) (toContracted_smul φ P g p)).trans
    ((contracted φ P).toSheafify_smul (φ.hom.app U g) _)

variable {φ P}

/-- Morphisms of `G'`-torsors out of `P ×^G G'` are determined by their composite with the
morphism `P → P ×^G G'`. -/
lemma map_hom_ext {R : Torsor G'} {f f' : P.map φ ⟶ R}
    (h : P.toMap φ ≫ f.hom = P.toMap φ ≫ f'.hom) : f = f' := by
  refine (contracted φ P).sheafify_hom_ext ?_
  ext U y
  induction y using Quot.ind with | mk x => ?_
  obtain ⟨p, (a : G'.obj.obj U)⟩ := x
  -- The class of `(p, a)` is `a • [p, 1]`, and `f`, `f'` agree on `[p, 1]`.
  have hx : (Quot.mk _ (p, a) : (contracted φ P).presheaf.obj U) =
      a • (toContracted φ P).app U p :=
    congrArg (Quot.mk _) (Prod.ext rfl (mul_one a).symm)
  have h' : f.hom.hom.app U ((P.toMap φ).hom.app U p) =
      f'.hom.hom.app U ((P.toMap φ).hom.app U p) :=
    congrArg (fun g ↦ g.hom.app U p) h
  have key (g : P.map φ ⟶ R) :
      ((contracted φ P).toSheafify ≫ g.hom.hom).app U (Quot.mk _ (p, a)) =
        a • g.hom.hom.app U ((P.toMap φ).hom.app U p) :=
    (congrArg (g.hom.hom.app U) ((congrArg _ hx).trans
      ((contracted φ P).toSheafify_smul _ _))).trans (g.map_smul U _ _)
  exact (key f).trans ((congrArg _ h').trans (key f').symm)

/-- A `φ`-equivariant morphism `u : P → R` to a `G'`-torsor induces a morphism of `G'`-torsors
`P ×^G G' ⟶ R`, sending `[p, a]` to `a • u p`. -/
def mapLift {R : Torsor G'} (u : P.sheaf ⟶ R.sheaf)
    (hu : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U),
      u.hom.app U (g • p) = φ.hom.app U g • u.hom.app U p) :
    P.map φ ⟶ R :=
  (contracted φ P).sheafifyLift
    { app U := ↾Quot.lift (fun x : P.sheaf.obj.obj U × G'.obj.obj U ↦ x.2 • u.hom.app U x.1) (by
        rintro ⟨p, b⟩ _ ⟨g, rfl⟩
        -- `mulRight_smul` turns the `G`-action on `b` into right multiplication in `G'`.
        dsimp only
        rw [MulActionSheaf.mulRight_smul, hu, smul_smul]
        exact congrArg (· • _) (inv_mul_cancel_right (G := G'.obj.obj U) b _).symm)
      naturality U V f := by
        ext y
        induction y using Quot.ind with | mk x => ?_
        obtain ⟨p, (a : G'.obj.obj U)⟩ := x
        exact ((R.map_smul f a (u.hom.app U p)).trans
          (congrArg _ (NatTrans.naturality_apply u.hom f p).symm)).symm }
    fun U a y ↦ by
      induction y using Quot.ind with | mk x => ?_
      obtain ⟨p, (b : G'.obj.obj U)⟩ := x
      exact mul_smul a b (u.hom.app U p)

/-- The morphism induced by a `φ`-equivariant `u : P → R` restricts to `u` along
`P → P ×^G G'`. -/
@[reassoc (attr := simp)]
lemma toMap_mapLift {R : Torsor G'} (u : P.sheaf ⟶ R.sheaf)
    (hu : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U),
      u.hom.app U (g • p) = φ.hom.app U g • u.hom.app U p) :
    P.toMap φ ≫ (P.mapLift u hu).hom = u := by
  ext U p
  exact ((contracted φ P).sheafifyLift_hom_app_toSheafify _ _ _).trans (one_smul _ _)

variable (φ P)

/-- The `φ`-equivariant pairing `P × G' → Torsor.map φ P`, `(p, a) ↦ a • [p, 1]`. -/
private def mulRightPairing :
    P.sheaf ⊗ (MulActionSheaf.mulRight φ).sheaf ⟶ (P.map φ).sheaf :=
  ObjectProperty.homMk
    { app U := ↾fun a : P.sheaf.obj.obj U × G'.obj.obj U ↦ a.2 • (P.toMap φ).hom.app U a.1
      naturality U V f := by
        ext a
        exact ((P.map φ).map_smul f a.2 _).trans
          (congrArg _ (NatTrans.naturality_apply (P.toMap φ).hom f a.1).symm) |>.symm }

/-- The pairing `(p, a) ↦ a • [p, 1]` is invariant under `g • (p, a) = (g • p, a * φ(g)⁻¹)`:
`(a * φ(g)⁻¹) • [g • p, 1] = (a * φ(g)⁻¹) • φ(g) • [p, 1] = a • [p, 1]`. -/
private lemma mulRightPairing_smul (U : Cᵒᵖ) (g : G.obj.obj U)
    (p : P.sheaf.obj.obj U) (a : (MulActionSheaf.mulRight φ).sheaf.obj.obj U) :
    (mulRightPairing φ P).hom.app U (g • p, g • a) = (mulRightPairing φ P).hom.app U (p, a) :=
  ((congrArg (_ • ·) (toMap_smul φ P g p)).trans (mul_smul _ _ _).symm).trans
    (congrArg (· • (P.toMap φ).hom.app U p) (@inv_mul_cancel_right (G'.obj.obj U) _ a _))

/-- Extending the structure group of `P` along `φ : G ⟶ G'` is contracting `P` with `G'`, on
which `G` acts by `g • a = a * φ(g)⁻¹`: the underlying sheaf of `Torsor.map φ P` is
`P ×^G G'`, by `[p, a] ↦ a • [p, 1]`. -/
def contractedProductMulRightIso :
    P.contractedProduct (MulActionSheaf.mulRight φ) ≅ (P.map φ).sheaf :=
  letI f := contractedProductDesc _ (mulRightPairing_smul φ P)
  have : IsIso f :=
    isIso_of_bijective_app P _ fun U ⟨p⟩ ↦ by
      -- Composed with the bijection `a ↦ [p, a]`, the morphism is `a ↦ a • [p, 1]`, which is
      -- bijective because `Torsor.map φ P` is a `G'`-torsor.
      have h (a : G'.obj.obj (op U)) : f.hom.app _ (contractedProductObjEquiv p a) =
          a • (P.toMap φ).hom.app _ p :=
        contractedProductDesc_hom_app_contractedProductMk _ (mulRightPairing_smul φ P) p a
      refine (Function.Bijective.of_comp_iff _
        (contractedProductObjEquiv (X := MulActionSheaf.mulRight φ) p).bijective).1
          ⟨fun a b hab ↦ (P.map φ).smul_left_injective ((P.toMap φ).hom.app _ p) ?_, fun q ↦ ?_⟩
      · exact (h a).symm.trans (hab.trans (h b))
      · obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (G'.obj.obj (op U)) ((P.toMap φ).hom.app _ p) q
        exact ⟨a, (h a).trans ha⟩
  asIso f

variable {φ P}

/-- The identification of `P ×^G G'` with `Torsor.map φ P` sends `[p, a]` to `a • [p, 1]`. -/
@[simp]
lemma contractedProductMulRightIso_hom_hom_app_contractedProductMk {U : Cᵒᵖ}
    (p : P.sheaf.obj.obj U) (a : G'.obj.obj U) :
    (P.contractedProductMulRightIso φ).hom.hom.app U
        (contractedProductMk (X := MulActionSheaf.mulRight φ) p a) =
      a • (P.toMap φ).hom.app U p :=
  contractedProductDesc_hom_app_contractedProductMk _ (mulRightPairing_smul φ P) p a

end Torsor

end CategoryTheory.Sheaf
