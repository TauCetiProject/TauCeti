/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import TauCeti.Algebra.Category.ModuleCat.CentralCharacter.Action
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map

/-!
# Strict character fibers over an action category

Let a monoid `G` act on an `R`-algebra `A` by algebra automorphisms, through
`a : G →* (A ≃ₐ[R] A)`, and on a type `X` of parameters. Suppose every parameter `x` carries a
character `χ x` of the center of `A`, compatibly with the two actions:
`χ (g • x) = χ x ∘ (a g)⁻¹` on the center. Twisting a module by `g`, that is, restricting its
scalars along `(a g)⁻¹`, then carries the strict character fiber of `χ x` to that of `χ (g • x)`.
An automorphism need not fix any character, so the twists move between different fibers rather
than acting on a single one, and they assemble into a family of categories over the action
category `G ⋉ X` (Mathlib's `CategoryTheory.ActionCategory G X`), whose arrows `x ⟶ g • x` are
labelled by `g`. When `G` is a group, `G ⋉ X` is the action groupoid.

The ambient family is `TauCeti.actionCategoryTwist X a'` for the action
`a' = (MulSemiringAction.toRingAut (A ≃ₐ[R] A) A).comp a` of `G` by the underlying ring
automorphisms: the twisting action of `G` on all of `ModuleCat A` as a pseudofunctor out of
`G ⋉ X`, sending an arrow labelled `g` to restriction of
scalars along `(a g)⁻¹`, with unit and composition comparisons `ModuleCat.restrictScalarsId'App`
and `ModuleCat.restrictScalarsComp'App`. This file restricts it to the character fibers.

* `TauCeti.discreteCentralCharacterObjectProperty X a χ` is the property of objects of
  `actionCategoryTwist X a'` cutting out the strict discrete character fiber
  `discreteCentralCharacterModules (χ x)` over each `x`. It is closed under the transport
  functors (`TauCeti.isClosedUnderMapObj_discreteCentralCharacterObjectProperty`).
* `TauCeti.discreteCentralCharacterFamily X a ha χ hχ` is the family of strict discrete
  character fibers, Mathlib's `Pseudofunctor.ObjectProperty.fullsubcategory` for this property,
  with the twist functors as transport and the same unit and composition comparisons. Its
  transport functors are `R`-linear.
* `TauCeti.discreteCentralCharacterFamilyι X a ha χ hχ` is the inclusion of the fibers into all
  modules, Mathlib's `Pseudofunctor.ObjectProperty.ι`: a strong transformation to
  `actionCategoryTwist X a'` with identity naturality isomorphisms. It expresses that the
  inclusions of the fibers are equivariant for the twists moving the characters.

For instance `X` may be a space of parameters `p` of central characters `χ p`, with a group
acting both on the parameters and, compatibly, on the algebra; arrows of `G ⋉ X` then transport
the category of modules with character `χ p` to that with character `χ (g • p)`.

The unit and composition comparisons are computed at arbitrary arrows, not only at syntactic
identities and composites (`TauCeti.discreteCentralCharacterFamily_mapId'_app` and
`TauCeti.discreteCentralCharacterFamily_mapComp'_app`). Hence for every commutative square
`t ≫ r = l ≫ b` of `G ⋉ X`, the comparison `F t ≫ F r ≅ F l ≫ F b` of Mathlib's
`Pseudofunctor.isoMapOfCommSq` is a composite of two restriction-of-scalars comparisons, with
identity underlying linear maps (`TauCeti.discreteCentralCharacterFamily_isoMapOfCommSq_app`).

The family recovers the fiberwise actions. If the image of `φ : K →* G` fixes a point `x`, the
restriction of the family along `CategoryTheory.ActionCategory.singleObjFunctor φ x` is the
coherent twisting action of `K` through `a ∘ φ` on the fiber of `x`: the two agree as actions,
associators and unitors included
(`TauCeti.monoidalLeftAction_comp_discreteCentralCharacterFamily`), and as pseudofunctors
(`TauCeti.comp_discreteCentralCharacterFamily_eq_pseudofunctor`).

For a semidirect product `G = H ⋊[β] S`, with product `(h, σ) (k, τ) = (h β σ (k), σ τ)`, the
action `a` is usually assembled by `SemidirectProduct.lift` from actions of `H` and of `S`. Its
hypotheses then reduce to the two factors
(`TauCeti.continuous_symm_of_inl_of_inr` and
`TauCeti.smul_eq_comp_centerCongr_symm_of_inl_of_inr`). The arrow labelled `(h, σ)` is the arrow
labelled `σ` followed by the arrow labelled `h`, so its transport is `T_h ∘ T_σ` up to
`Pseudofunctor.mapComp'`. The two kinds of arrows commute up to `β`:
`CategoryTheory.ActionCategory.commSq_inl_inr` gives the commutative square behind the covariance
comparison `T_h ⋙ T_σ ≅ T_σ ⋙ T_(β σ h)`, whose components are computed by
`TauCeti.discreteCentralCharacterFamily_isoMapOfCommSq_app`. When `H` fixes a point, the
restriction along `SemidirectProduct.inl` is the action of `H` on its fiber.

## References

* Edward Frenkel, [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  §1.3, for categories of modules with a fixed central character and their twists by
  automorphisms.
-/

@[expose] public section

universe v u

open CategoryTheory Bicategory MonoidalCategory MonoidalLeftAction

namespace TauCeti

variable {G : Type*} [Monoid G] {X : Type*} [MulAction G X]
  {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {a : G →* (A ≃ₐ[R] A)}

variable [TopologicalSpace A] (ha : ∀ g, Continuous (a g).symm)
  (χ : X → (Subalgebra.center R A →ₐ[R] R))
  (hχ : ∀ (g : G) (x : X), χ (g • x) = (χ x).comp (centerCongr (a g)).symm.toAlgHom)

omit [TopologicalSpace A] in
include hχ in
/-- Along an arrow `x ⟶ y` of `G ⋉ X` labelled `g`, the character of `y` is that of `x`
transported by `(a g)⁻¹`. -/
lemma eq_comp_centerCongr_symm_of_hom {x y : LocallyDiscrete (ActionCategory G X)} (f : x ⟶ y) :
    χ y.as.back = (χ x.as.back).comp (centerCongr (a f.as.hom)).symm.toAlgHom := by
  have hf : f.as.hom • x.as.back = y.as.back := f.as.map_val
  rw [← hf, hχ]

variable (X a)

omit [TopologicalSpace A] in
/-- The strict discrete character fibers `x ↦ discreteCentralCharacterModules (χ x)`, as a
property of objects of the twisting family `actionCategoryTwist` of the underlying ring
automorphisms. -/
def discreteCentralCharacterObjectProperty :
    Pseudofunctor.ObjectProperty
      (actionCategoryTwist.{v} X ((MulSemiringAction.toRingAut (A ≃ₐ[R] A) A).comp a)) where
  prop x := discreteCentralCharacterModules.{v} (χ x.as.back)

include ha hχ in
/-- The twists carry each strict discrete character fiber to the fiber of the transported
character. -/
theorem isClosedUnderMapObj_discreteCentralCharacterObjectProperty :
    (discreteCentralCharacterObjectProperty.{v} X a χ).IsClosedUnderMapObj where
  map_obj {_ _ _} hM f := by
    dsimp only [discreteCentralCharacterObjectProperty, actionCategoryTwist_map_toFunctor] at hM ⊢
    rw [eq_comp_centerCongr_symm_of_hom χ hχ f]
    exact discreteCentralCharacterModules_restrictScalars _ _ (ha _) hM

/-- The strict discrete character fibers `x ↦ discreteCentralCharacterModules (χ x)` over the
action category `G ⋉ X`, with the twists along `(a g)⁻¹` as transport functors. It is the
restriction of `actionCategoryTwist` to these fibers, so its unit and composition comparisons
are restrictions of those of `ModuleCat.restrictScalars`. -/
noncomputable def discreteCentralCharacterFamily :
    LocallyDiscrete (ActionCategory G X) ⥤ᵖ Cat.{v, max u (v + 1)} :=
  haveI := isClosedUnderMapObj_discreteCentralCharacterObjectProperty X a ha χ hχ
  (discreteCentralCharacterObjectProperty.{v} X a χ).fullsubcategory

/-- The inclusion of the strict discrete character fibers into all modules is equivariant: it is
a strong transformation from `discreteCentralCharacterFamily` to `actionCategoryTwist` whose
components are the inclusions and whose naturality isomorphisms are identities
(`discreteCentralCharacterFamilyι_naturality_hom_app` and
`discreteCentralCharacterFamilyι_naturality_inv_app`). -/
noncomputable def discreteCentralCharacterFamilyι :
    Pseudofunctor.StrongTrans (discreteCentralCharacterFamily.{v} X a ha χ hχ)
      (actionCategoryTwist.{v} X ((MulSemiringAction.toRingAut (A ≃ₐ[R] A) A).comp a)) :=
  haveI := isClosedUnderMapObj_discreteCentralCharacterObjectProperty X a ha χ hχ
  (discreteCentralCharacterObjectProperty.{v} X a χ).ι

variable {X a ha χ hχ}

@[simp]
lemma discreteCentralCharacterFamily_obj (x : LocallyDiscrete (ActionCategory G X)) :
    (discreteCentralCharacterFamily.{v} X a ha χ hχ).obj x =
      Cat.of (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory :=
  rfl

/-- The underlying module of a transported fiber object is the restriction of scalars along the
inverse of the label. -/
@[simp]
lemma discreteCentralCharacterFamily_map_toFunctor_obj_obj
    {x y : LocallyDiscrete (ActionCategory G X)} (f : x ⟶ y)
    (M : (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory) :
    (((discreteCentralCharacterFamily.{v} X a ha χ hχ).map f).toFunctor.obj M).obj =
      (ModuleCat.restrictScalars (a f.as.hom).symm.toRingHom).obj M.obj :=
  rfl

/-- Transport between fibers does not change the underlying maps of modules. -/
@[simp]
lemma discreteCentralCharacterFamily_map_toFunctor_map_hom
    {x y : LocallyDiscrete (ActionCategory G X)} (f : x ⟶ y)
    {M N : (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory} (φ : M ⟶ N) :
    (((discreteCentralCharacterFamily.{v} X a ha χ hχ).map f).toFunctor.map φ).hom =
      (ModuleCat.restrictScalars (a f.as.hom).symm.toRingHom).map φ.hom :=
  rfl

/-- Forgetting after transport between fibers is restriction of scalars after forgetting. -/
lemma discreteCentralCharacterFamily_map_toFunctor_comp_ι
    {x y : LocallyDiscrete (ActionCategory G X)} (f : x ⟶ y) :
    ((discreteCentralCharacterFamily.{v} X a ha χ hχ).map f).toFunctor ⋙
        (discreteCentralCharacterModules (χ y.as.back)).ι =
      (discreteCentralCharacterModules (χ x.as.back)).ι ⋙
        ModuleCat.restrictScalars (a f.as.hom).symm.toRingHom :=
  rfl

/-- The transport functor of the fiber family along an arrow labelled `g` is the twist functor
`discreteCentralCharacterTwist` along `a g`, followed by the identification of the transported
character with the character of the target. -/
lemma discreteCentralCharacterFamily_map_toFunctor_eq
    {x y : LocallyDiscrete (ActionCategory G X)} (f : x ⟶ y) :
    (((discreteCentralCharacterFamily.{v} X a ha χ hχ).map f).toFunctor :
        (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory ⥤
          (discreteCentralCharacterModules.{v} (χ y.as.back)).FullSubcategory) =
      discreteCentralCharacterTwist (χ x.as.back) (a f.as.hom) (ha _) ⋙
        ObjectProperty.ιOfLE (eq_comp_centerCongr_symm_of_hom χ hχ f ▸ le_rfl) :=
  rfl

/-- The unit comparison of the fiber family is the restriction of
`ModuleCat.restrictScalarsId'App`. -/
lemma discreteCentralCharacterFamily_mapId_app (x : LocallyDiscrete (ActionCategory G X))
    (M : (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory) :
    (discreteCentralCharacterModules (χ x.as.back)).ι.mapIso
        ((Cat.Hom.toNatIso ((discreteCentralCharacterFamily.{v} X a ha χ hχ).mapId x)).app M) =
      ModuleCat.restrictScalarsId'App (a 1).symm.toRingHom
        (by ext; simp [← AlgEquiv.aut_inv]) M.obj :=
  Iso.ext rfl

/-- The composition comparison of the fiber family at `f ≫ g` is the restriction of
`ModuleCat.restrictScalarsComp'App` for `(a (g.hom * f.hom))⁻¹ = (a f.hom)⁻¹ ∘ (a g.hom)⁻¹`. -/
lemma discreteCentralCharacterFamily_mapComp_app {x y z : LocallyDiscrete (ActionCategory G X)}
    (f : x ⟶ y) (g : y ⟶ z)
    (M : (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory) :
    (discreteCentralCharacterModules (χ z.as.back)).ι.mapIso
        ((Cat.Hom.toNatIso ((discreteCentralCharacterFamily.{v} X a ha χ hχ).mapComp f g)).app
          M) =
      ModuleCat.restrictScalarsComp'App (a g.as.hom).symm.toRingHom (a f.as.hom).symm.toRingHom
        (a (g.as.hom * f.as.hom)).symm.toRingHom
        (by ext; simp [← AlgEquiv.aut_inv, mul_inv_rev]) M.obj :=
  Iso.ext (congrArg Iso.hom (actionCategoryTwist_mapComp_app f g M.obj))

/-- The composition comparison of the fiber family at a factorization `f ≫ g = fg` is the
restriction of `ModuleCat.restrictScalarsComp'App` for `(a fg.hom)⁻¹ = (a f.hom)⁻¹ ∘ (a g.hom)⁻¹`.
The composite `fg` need not be syntactically `f ≫ g`. -/
lemma discreteCentralCharacterFamily_mapComp'_app {x y z : LocallyDiscrete (ActionCategory G X)}
    (f : x ⟶ y) (g : y ⟶ z) (fg : x ⟶ z) (h : f ≫ g = fg)
    (M : (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory) :
    (discreteCentralCharacterModules (χ z.as.back)).ι.mapIso
        ((Cat.Hom.toNatIso ((discreteCentralCharacterFamily.{v} X a ha χ hχ).mapComp' f g fg h)).app
          M) =
      ModuleCat.restrictScalarsComp'App (a g.as.hom).symm.toRingHom (a f.as.hom).symm.toRingHom
        (a fg.as.hom).symm.toRingHom
        (by subst h; ext; simp [← AlgEquiv.aut_inv, mul_inv_rev]) M.obj := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  exact discreteCentralCharacterFamily_mapComp_app f g M

/-- The unit comparison of the fiber family at an arrow `f = 𝟙 x` is the restriction of
`ModuleCat.restrictScalarsId'App` for `(a f.hom)⁻¹ = id`. The arrow `f` need not be syntactically
`𝟙 x`. -/
lemma discreteCentralCharacterFamily_mapId'_app {x : LocallyDiscrete (ActionCategory G X)}
    (f : x ⟶ x) (hf : f = 𝟙 x)
    (M : (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory) :
    (discreteCentralCharacterModules (χ x.as.back)).ι.mapIso
        ((Cat.Hom.toNatIso ((discreteCentralCharacterFamily.{v} X a ha χ hχ).mapId' f hf)).app M) =
      ModuleCat.restrictScalarsId'App (a f.as.hom).symm.toRingHom
        (by subst hf; ext; simp [← AlgEquiv.aut_inv]) M.obj := by
  subst hf
  rw [Pseudofunctor.mapId'_eq_mapId]
  exact discreteCentralCharacterFamily_mapId_app x M

/-- For a commutative square `t ≫ r = l ≫ b` of the action category, the comparison
`F t ≫ F r ≅ F l ≫ F b` of the fiber family is the inverse of the composition comparison of
`ModuleCat.restrictScalars` at `t ≫ r` followed by the one at `l ≫ b`. In particular its
underlying linear maps are identities. -/
lemma discreteCentralCharacterFamily_isoMapOfCommSq_app
    {x₁ x₂ y₁ y₂ : LocallyDiscrete (ActionCategory G X)} {t : x₁ ⟶ y₁} {l : x₁ ⟶ x₂}
    {r : y₁ ⟶ y₂} {b : x₂ ⟶ y₂} (sq : CommSq t l r b)
    (M : (discreteCentralCharacterModules.{v} (χ x₁.as.back)).FullSubcategory) :
    (discreteCentralCharacterModules (χ y₂.as.back)).ι.mapIso
        ((Cat.Hom.toNatIso
          ((discreteCentralCharacterFamily.{v} X a ha χ hχ).isoMapOfCommSq sq)).app M) =
      (ModuleCat.restrictScalarsComp'App (a r.as.hom).symm.toRingHom (a t.as.hom).symm.toRingHom
        (a (t ≫ r).as.hom).symm.toRingHom
        (by ext; simp [← AlgEquiv.aut_inv, mul_inv_rev]) M.obj).symm ≪≫
      ModuleCat.restrictScalarsComp'App (a b.as.hom).symm.toRingHom (a l.as.hom).symm.toRingHom
        (a (t ≫ r).as.hom).symm.toRingHom
        (by rw [sq.w]; ext; simp [← AlgEquiv.aut_inv, mul_inv_rev]) M.obj := by
  rw [Pseudofunctor.isoMapOfCommSq_eq _ _ (t ≫ r) rfl]
  -- The component of a composite of isomorphisms of `Cat` is the composite of the components.
  exact Iso.ext (((discreteCentralCharacterModules (χ y₂.as.back)).ι.map_comp _ _).trans
    (congrArg₂ (· ≫ ·)
      (congrArg Iso.inv (discreteCentralCharacterFamily_mapComp'_app t r _ rfl M))
      (congrArg Iso.hom (discreteCentralCharacterFamily_mapComp'_app l b _ sq.w.symm M))))

@[simp]
lemma discreteCentralCharacterFamilyι_app_toFunctor (x : LocallyDiscrete (ActionCategory G X)) :
    ((discreteCentralCharacterFamilyι.{v} X a ha χ hχ).app x).toFunctor =
      (discreteCentralCharacterModules (χ x.as.back)).ι :=
  rfl

/-- The naturality isomorphisms of the inclusion of the fibers are identities. -/
@[simp]
lemma discreteCentralCharacterFamilyι_naturality_hom_app
    {x y : LocallyDiscrete (ActionCategory G X)} (f : x ⟶ y)
    (M : (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory) :
    ((discreteCentralCharacterFamilyι.{v} X a ha χ hχ).naturality f).hom.toNatTrans.app M =
      𝟙 _ :=
  rfl

/-- The inverses of the naturality isomorphisms of the inclusion of the fibers are identities. -/
@[simp]
lemma discreteCentralCharacterFamilyι_naturality_inv_app
    {x y : LocallyDiscrete (ActionCategory G X)} (f : x ⟶ y)
    (M : (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory) :
    ((discreteCentralCharacterFamilyι.{v} X a ha χ hχ).naturality f).inv.toNatTrans.app M =
      𝟙 _ :=
  rfl

/-- The transport functors between strict character fibers are additive. The categories of the
fibers are given explicitly: the values of `discreteCentralCharacterFamily` are only
definitionally the full subcategories, so instance search does not find their structure. -/
lemma additive_discreteCentralCharacterFamily_map
    {x y : LocallyDiscrete (ActionCategory G X)} (f : x ⟶ y) :
    @Functor.Additive (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory
      (discreteCentralCharacterModules.{v} (χ y.as.back)).FullSubcategory
      (ObjectProperty.FullSubcategory.category _) (ObjectProperty.FullSubcategory.category _)
      (Preadditive.fullSubcategory _) (Preadditive.fullSubcategory _)
      ((discreteCentralCharacterFamily.{v} X a ha χ hχ).map f).toFunctor where
  map_add {_ _ φ ψ} := by
    ext1
    exact (ModuleCat.restrictScalars (a f.as.hom).symm.toRingHom).map_add (f := φ.hom) (g := ψ.hom)

open ModuleCat.Algebra in
/-- The transport functors between strict character fibers are `R`-linear. As for
`additive_discreteCentralCharacterFamily_map`, the categories of the fibers are given
explicitly. -/
lemma linear_discreteCentralCharacterFamily_map {x y : LocallyDiscrete (ActionCategory G X)}
    (f : x ⟶ y) :
    @Functor.Linear R _ (discreteCentralCharacterModules.{v} (χ x.as.back)).FullSubcategory
      (discreteCentralCharacterModules.{v} (χ y.as.back)).FullSubcategory
      (ObjectProperty.FullSubcategory.category _) (ObjectProperty.FullSubcategory.category _)
      (Preadditive.fullSubcategory _) (Preadditive.fullSubcategory _)
      (Linear.fullSubcategory _) (Linear.fullSubcategory _)
      ((discreteCentralCharacterFamily.{v} X a ha χ hχ).map f).toFunctor where
  map_smul φ r := by
    ext1
    exact (ModuleCat.restrictScalars (a f.as.hom).symm.toAlgHom.toRingHom).map_smul r φ.hom

section Restriction

variable {K : Type*} [Monoid K] (φ : K →* G) (x : X) (hx : ∀ k, φ k • x = x)

omit [TopologicalSpace A] in
include hx in
/-- The elements of `K` fix the character of a point fixed by the image of `φ : K →* G`. -/
lemma comp_centerCongr_symm_eq_of_smul_eq
    (hχ : ∀ (g : G) (x : X), χ (g • x) = (χ x).comp (centerCongr (a g)).symm.toAlgHom)
    (k : K) : (χ x).comp (centerCongr (a.comp φ k)).symm.toAlgHom = χ x := by
  rw [MonoidHom.comp_apply, ← hχ, hx]

/-- At a point `x` fixed by the image of `φ : K →* G`, the restriction of the fiber family along
`CategoryTheory.ActionCategory.singleObjFunctor` is the coherent twisting action of `K` through
`a ∘ φ` on the fiber of `x`, `MonoidHom.discreteCentralCharacterMonoidalLeftAction`. The two
actions agree in all their data: action functors, associators and unitors. -/
theorem monoidalLeftAction_comp_discreteCentralCharacterFamily :
    ((ActionCategory.singleObjFunctor φ x hx).toPseudofunctor.comp
        (discreteCentralCharacterFamily.{v} X a ha χ hχ)).monoidalLeftAction =
      (a.comp φ).discreteCentralCharacterMonoidalLeftAction (χ x) (fun _ => ha _)
        (comp_centerCongr_symm_eq_of_smul_eq φ x hx hχ) := by
  unfold Pseudofunctor.monoidalLeftAction MonoidHom.discreteCentralCharacterMonoidalLeftAction
  -- The action functors and the unitors agree definitionally. The remaining fields are the
  -- actions of the morphisms of `Discrete K`, which are identities, and the associators.
  congr
  case e_actionHomLeft =>
    funext c c' f M
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
    rfl
  case e_actionHom =>
    funext c c' M N f g
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
    rfl
  case e_actionAssocIso =>
    funext c c' M
    rw [Pseudofunctor.comp_mapComp_eq_mapComp']
    refine Iso.ext ((discreteCentralCharacterModules (χ x)).ι.map_injective ?_)
    -- Both associators are restrictions of `ModuleCat.restrictScalarsComp'App` along the
    -- same ring isomorphisms `(a (φ c))⁻¹` and `(a (φ c'))⁻¹`.
    exact (congrArg Iso.hom (discreteCentralCharacterFamily_mapComp'_app _ _ _
      (obj_ext_of_isDiscrete
        ((ActionCategory.singleObjFunctor φ x hx).toPseudofunctor.mapComp c' c).hom).symm M)).trans
      (congrArg Iso.hom (MonoidHom.discreteCentralCharacterMonoidalLeftAction_assoc (a.comp φ)
        (χ x) (fun _ => ha _) (comp_centerCongr_symm_eq_of_smul_eq φ x hx hχ) c.as c'.as M)).symm
  case e_actionUnitIso =>
    funext M
    rw [Pseudofunctor.comp_mapId_eq_mapId']
    refine Iso.ext ((discreteCentralCharacterModules (χ x)).ι.map_injective ?_)
    -- Both unitors are restrictions of `ModuleCat.restrictScalarsId'App` along `(a (φ 1))⁻¹`.
    exact (congrArg Iso.hom (discreteCentralCharacterFamily_mapId'_app _
      (obj_ext_of_isDiscrete
        ((ActionCategory.singleObjFunctor φ x hx).toPseudofunctor.mapId _).hom) M)).trans
      (congrArg Iso.hom (MonoidHom.discreteCentralCharacterMonoidalLeftAction_unit (a.comp φ)
        (χ x) (fun _ => ha _) (comp_centerCongr_symm_eq_of_smul_eq φ x hx hχ) M)).symm

/-- At a point `x` fixed by the image of `φ : K →* G`, the restriction of the fiber family along
`CategoryTheory.ActionCategory.singleObjFunctor` is the pseudofunctor of the coherent twisting
action of `K` on the fiber of `x`, including its unit and composition comparisons. -/
theorem comp_discreteCentralCharacterFamily_eq_pseudofunctor :
    (ActionCategory.singleObjFunctor φ x hx).toPseudofunctor.comp
        (discreteCentralCharacterFamily.{v} X a ha χ hχ) =
      letI := (a.comp φ).discreteCentralCharacterMonoidalLeftAction (χ x) (fun _ => ha _)
        (comp_centerCongr_symm_eq_of_smul_eq φ x hx hχ)
      MonoidalLeftAction.pseudofunctor K
        (discreteCentralCharacterModules.{v} (χ x)).FullSubcategory := by
  rw [← monoidalLeftAction_comp_discreteCentralCharacterFamily]
  exact (Pseudofunctor.pseudofunctor_monoidalLeftAction _).symm

end Restriction

section SemidirectProduct

open SemidirectProduct

variable {H S : Type*} [Group H] [Group S] {β : S →* MulAut H} {Y : Type*}
  [MulAction (H ⋊[β] S) Y] {b : H ⋊[β] S →* (A ≃ₐ[R] A)}

/-- An action of a semidirect product `H ⋊[β] S` by algebra automorphisms has continuous inverse
automorphisms as soon as the elements of `H` and of `S` do. -/
lemma continuous_symm_of_inl_of_inr (hH : ∀ h, Continuous (b (inl h)).symm)
    (hS : ∀ σ, Continuous (b (inr σ)).symm) (g : H ⋊[β] S) : Continuous (b g).symm := by
  obtain ⟨h, σ⟩ := g
  rw [mk_eq_inl_mul_inr, map_mul]
  exact (hS σ).comp (hH h)

omit [TopologicalSpace A] in
/-- A family of characters over an action of a semidirect product `H ⋊[β] S` is compatible with
the automorphisms `b` as soon as it is compatible with those of the elements of `H` and of `S`.
For instance, the elements of `H` may fix every point and act trivially on the center, while the
elements of `S` move both. -/
lemma smul_eq_comp_centerCongr_symm_of_inl_of_inr
    {ψ : Y → (Subalgebra.center R A →ₐ[R] R)}
    (hH : ∀ (h : H) (y : Y),
      ψ ((inl h : H ⋊[β] S) • y) = (ψ y).comp (centerCongr (b (inl h))).symm.toAlgHom)
    (hS : ∀ (σ : S) (y : Y),
      ψ ((inr σ : H ⋊[β] S) • y) = (ψ y).comp (centerCongr (b (inr σ))).symm.toAlgHom)
    (g : H ⋊[β] S) (y : Y) : ψ (g • y) = (ψ y).comp (centerCongr (b g)).symm.toAlgHom := by
  obtain ⟨h, σ⟩ := g
  rw [mk_eq_inl_mul_inr, mul_smul, hH, hS]
  ext z
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom]
  -- `(b (inl h) * b (inr σ))⁻¹ = (b (inr σ))⁻¹ ∘ (b (inl h))⁻¹` on the center.
  congr 1
  ext
  simp [← AlgEquiv.aut_inv, mul_inv_rev, AlgEquiv.mul_apply]

end SemidirectProduct

end TauCeti
