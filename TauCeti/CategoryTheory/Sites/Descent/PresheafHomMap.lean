/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Functoriality of the presheaves of morphisms in both variables

For a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` and objects `M N` of its fibre over `S`,
Mathlib's presheaf of local morphisms `F.presheafHom M N` on `Over S` is contravariant in `M` and
covariant in `N`: morphisms `φ : M' ⟶ M` and `ψ : N ⟶ N'` act on a local morphism
`p : t^* M ⟶ t^* N` over `t : T ⟶ S` by `t^* φ ≫ p ≫ t^* ψ`
(`Pseudofunctor.presheafHomMap`), precomposition with `φ` (`Pseudofunctor.presheafHomPrecomp`)
followed by postcomposition with `ψ` (`Pseudofunctor.presheafHomPostcomp`). This is compatible
with identities and composition, and for isomorphisms `e : M ≅ M'` and `e' : N ≅ N'` it gives an
isomorphism of presheaves `F.presheafHom M N ≅ F.presheafHom M' N'`
(`Pseudofunctor.presheafHomIso`), and of sheaves when `F` is a prestack
(`Pseudofunctor.sheafHomIso`), compatible with identities, composites and inverses of
isomorphisms.

## Main declarations

* `CategoryTheory.Pseudofunctor.presheafHomPrecomp φ N`, with `presheafHomPrecomp_app_apply` and
  `presheafHomPrecomp_id`.
* `CategoryTheory.Pseudofunctor.presheafHomMap φ ψ`, with `presheafHomMap_app_apply`,
  `presheafHomMap_id`, `presheafHomMap_comp` and `presheafHomMap_id_left`.
* `CategoryTheory.Pseudofunctor.presheafHomIso e e'` and
  `CategoryTheory.Pseudofunctor.sheafHomIso J e e'`, with their `_refl`, `_trans` and `_symm`
  lemmas.
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {S : C}

/-- **Precomposition with a morphism `φ : M' ⟶ M`** as a morphism of presheaves of morphisms
`F.presheafHom M N ⟶ F.presheafHom M' N`: at `(T, t)` a local morphism `p : t^* M ⟶ t^* N` goes
to `t^* φ ≫ p`. -/
def presheafHomPrecomp {M M' : F.obj (.mk (op S))} (φ : M' ⟶ M) (N : F.obj (.mk (op S))) :
    F.presheafHom M N ⟶ F.presheafHom M' N where
  app T := TypeCat.ofHom fun p ↦ (F.map T.unop.hom.op.toLoc).toFunctor.map φ ≫ p
  naturality T T' g := by
    ext p
    dsimp
    rw [pullHom_comp _ _ g.unop.left T'.unop.hom T'.unop.hom T'.unop.hom (Over.w g.unop)
      (Over.w g.unop) (Over.w g.unop), pullHom_map]

theorem presheafHomPrecomp_app_apply {M M' : F.obj (.mk (op S))} (φ : M' ⟶ M)
    (N : F.obj (.mk (op S))) (T : (Over S)ᵒᵖ) (p : (F.presheafHom M N).obj T) :
    (F.presheafHomPrecomp φ N).app T p = (F.map T.unop.hom.op.toLoc).toFunctor.map φ ≫ p :=
  (rfl)

variable {F} in
/-- Precomposition with the pullbacks of `φ` is composition of the global section
`presheafHomGlobalSection φ` with local morphisms. -/
lemma presheafHomPrecomp_eq_lift_comp_presheafHomComp {M' M N : F.obj (.mk (op S))}
    (φ : M' ⟶ M) :
    F.presheafHomPrecomp φ N = CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.toUnit _ ≫ presheafHomGlobalSection φ) (𝟙 _) ≫
        presheafHomComp M' M N := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun a ↦ ?_)
  rw [presheafHomPrecomp_app_apply, NatTrans.comp_app, ConcreteCategory.comp_apply,
    presheafHomComp_app_apply]
  -- There is no component lemma for Cartesian lift in this functor category. The change
  -- computes its pointwise pairing: the first projection evaluates the composite through
  -- toUnit at the unique terminal element, and the second evaluates the identity at a.
  -- The component lemmas above do not rewrite these projections of the pairing.
  change _ = (presheafHomGlobalSection φ).app T _ ≫ a
  rw [presheafHomGlobalSection_app_apply]

@[simp]
theorem presheafHomPrecomp_id (M N : F.obj (.mk (op S))) :
    F.presheafHomPrecomp (𝟙 M) N = 𝟙 (F.presheafHom M N) := by
  ext T p
  simp [presheafHomPrecomp]

/-- **The action of morphisms on presheaves of morphisms**: for `φ : M' ⟶ M` and `ψ : N ⟶ N'`,
the morphism of presheaves `F.presheafHom M N ⟶ F.presheafHom M' N'` sending a local morphism
`p : t^* M ⟶ t^* N` over `t : T ⟶ S` to `t^* φ ≫ p ≫ t^* ψ`, precomposition with `φ` followed by
postcomposition with `ψ`. -/
def presheafHomMap {M M' N N' : F.obj (.mk (op S))} (φ : M' ⟶ M) (ψ : N ⟶ N') :
    F.presheafHom M N ⟶ F.presheafHom M' N' :=
  F.presheafHomPrecomp φ N ≫ F.presheafHomPostcomp M' ψ

theorem presheafHomMap_app_apply {M M' N N' : F.obj (.mk (op S))} (φ : M' ⟶ M) (ψ : N ⟶ N')
    (T : (Over S)ᵒᵖ) (p : (F.presheafHom M N).obj T) :
    (F.presheafHomMap φ ψ).app T p =
      (F.map T.unop.hom.op.toLoc).toFunctor.map φ ≫ p ≫
        (F.map T.unop.hom.op.toLoc).toFunctor.map ψ := by
  simp only [presheafHomMap, NatTrans.comp_app, ConcreteCategory.comp_apply,
    presheafHomPrecomp_app_apply, presheafHomPostcomp_app_apply, Category.assoc]

@[simp]
theorem presheafHomMap_id (M N : F.obj (.mk (op S))) :
    F.presheafHomMap (𝟙 M) (𝟙 N) = 𝟙 _ := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun p ↦ ?_)
  rw [presheafHomMap_app_apply]
  simp

/-- `presheafHomMap` is compatible with composition, contravariantly in the source and covariantly
in the target. -/
theorem presheafHomMap_comp {M M' M'' N N' N'' : F.obj (.mk (op S))} (φ : M' ⟶ M)
    (φ' : M'' ⟶ M') (ψ : N ⟶ N') (ψ' : N' ⟶ N'') :
    F.presheafHomMap (φ' ≫ φ) (ψ ≫ ψ') = F.presheafHomMap φ ψ ≫ F.presheafHomMap φ' ψ' := by
  refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun p ↦ ?_)
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, presheafHomMap_app_apply,
    presheafHomMap_app_apply, presheafHomMap_app_apply]
  simp

/-- With the identity in the source, `presheafHomMap` is postcomposition. -/
theorem presheafHomMap_id_left (M : F.obj (.mk (op S))) {N N' : F.obj (.mk (op S))}
    (ψ : N ⟶ N') : F.presheafHomMap (𝟙 M) ψ = F.presheafHomPostcomp M ψ := by
  rw [presheafHomMap, presheafHomPrecomp_id, Category.id_comp]

/-- **Isomorphisms act on presheaves of morphisms by isomorphisms**: for `e : M ≅ M'` and
`e' : N ≅ N'`, the isomorphism `F.presheafHom M N ≅ F.presheafHom M' N'` sending `p` over `t` to
`t^* e⁻¹ ≫ p ≫ t^* e'`. -/
def presheafHomIso {M M' N N' : F.obj (.mk (op S))} (e : M ≅ M') (e' : N ≅ N') :
    F.presheafHom M N ≅ F.presheafHom M' N' where
  hom := F.presheafHomMap e.inv e'.hom
  inv := F.presheafHomMap e.hom e'.inv
  hom_inv_id := by rw [← presheafHomMap_comp, e.hom_inv_id, e'.hom_inv_id, presheafHomMap_id]
  inv_hom_id := by rw [← presheafHomMap_comp, e.inv_hom_id, e'.inv_hom_id, presheafHomMap_id]

@[simp]
theorem presheafHomIso_hom {M M' N N' : F.obj (.mk (op S))} (e : M ≅ M') (e' : N ≅ N') :
    (F.presheafHomIso e e').hom = F.presheafHomMap e.inv e'.hom :=
  (rfl)

@[simp]
theorem presheafHomIso_inv {M M' N N' : F.obj (.mk (op S))} (e : M ≅ M') (e' : N ≅ N') :
    (F.presheafHomIso e e').inv = F.presheafHomMap e.hom e'.inv :=
  (rfl)

@[simp]
theorem presheafHomIso_refl (M N : F.obj (.mk (op S))) :
    F.presheafHomIso (Iso.refl M) (Iso.refl N) = Iso.refl _ := by
  ext1
  exact presheafHomMap_id F M N

/-- `presheafHomIso` is compatible with composition of isomorphisms. -/
theorem presheafHomIso_trans {M M' M'' N N' N'' : F.obj (.mk (op S))} (e : M ≅ M')
    (f : M' ≅ M'') (e' : N ≅ N') (f' : N' ≅ N'') :
    F.presheafHomIso (e ≪≫ f) (e' ≪≫ f') = F.presheafHomIso e e' ≪≫ F.presheafHomIso f f' := by
  ext1
  exact presheafHomMap_comp F _ _ _ _

@[simp]
theorem presheafHomIso_symm {M M' N N' : F.obj (.mk (op S))} (e : M ≅ M') (e' : N ≅ N') :
    (F.presheafHomIso e e').symm = F.presheafHomIso e.symm e'.symm :=
  (rfl)

/-- **Isomorphisms act on sheaves of morphisms by isomorphisms**: for a prestack `F`, the
isomorphism `F.sheafHom J M N ≅ F.sheafHom J M' N'` of `presheafHomIso e e'`. -/
def sheafHomIso (J : GrothendieckTopology C) [F.IsPrestack J] {M M' N N' : F.obj (.mk (op S))}
    (e : M ≅ M') (e' : N ≅ N') : F.sheafHom J M N ≅ F.sheafHom J M' N' :=
  (fullyFaithfulSheafToPresheaf (J.over S) (Type _)).preimageIso (F.presheafHomIso e e')

@[simp]
theorem sheafHomIso_hom_hom (J : GrothendieckTopology C) [F.IsPrestack J]
    {M M' N N' : F.obj (.mk (op S))} (e : M ≅ M') (e' : N ≅ N') :
    (F.sheafHomIso J e e').hom.hom = F.presheafHomMap e.inv e'.hom :=
  (rfl)

@[simp]
theorem sheafHomIso_inv_hom (J : GrothendieckTopology C) [F.IsPrestack J]
    {M M' N N' : F.obj (.mk (op S))} (e : M ≅ M') (e' : N ≅ N') :
    (F.sheafHomIso J e e').inv.hom = F.presheafHomMap e.hom e'.inv :=
  (rfl)

@[simp]
theorem sheafHomIso_refl (J : GrothendieckTopology C) [F.IsPrestack J] (M N : F.obj (.mk (op S))) :
    F.sheafHomIso J (Iso.refl M) (Iso.refl N) = Iso.refl _ := by
  ext1
  exact Sheaf.hom_ext (presheafHomMap_id F M N)

/-- `sheafHomIso` is compatible with composition of isomorphisms. -/
theorem sheafHomIso_trans (J : GrothendieckTopology C) [F.IsPrestack J]
    {M M' M'' N N' N'' : F.obj (.mk (op S))} (e : M ≅ M') (f : M' ≅ M'') (e' : N ≅ N')
    (f' : N' ≅ N'') :
    F.sheafHomIso J (e ≪≫ f) (e' ≪≫ f') = F.sheafHomIso J e e' ≪≫ F.sheafHomIso J f f' := by
  ext1
  exact Sheaf.hom_ext (presheafHomMap_comp F _ _ _ _)

@[simp]
theorem sheafHomIso_symm (J : GrothendieckTopology C) [F.IsPrestack J]
    {M M' N N' : F.obj (.mk (op S))} (e : M ≅ M') (e' : N ≅ N') :
    (F.sheafHomIso J e e').symm = F.sheafHomIso J e.symm e'.symm :=
  (rfl)

end CategoryTheory.Pseudofunctor
