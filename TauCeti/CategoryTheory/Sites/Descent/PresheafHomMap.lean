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
(`Pseudofunctor.presheafHomMap`). This is compatible with identities and composition, and for
isomorphisms `e : M ≅ M'` and `e' : N ≅ N'` it gives an isomorphism of presheaves
`F.presheafHom M N ≅ F.presheafHom M' N'` (`Pseudofunctor.presheafHomIso`), and of sheaves when `F`
is a prestack (`Pseudofunctor.sheafHomIso`). Postcomposition alone is
`Pseudofunctor.presheafHomPostcomp`.

## Main declarations

* `CategoryTheory.Pseudofunctor.presheafHomMap φ ψ`, with `presheafHomMap_app_apply`,
  `presheafHomMap_id`, `presheafHomMap_comp` and `presheafHomMap_id_left`.
* `CategoryTheory.Pseudofunctor.presheafHomIso e e'` and
  `CategoryTheory.Pseudofunctor.sheafHomIso J e e'`.
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {S : C}

/-- **The action of morphisms on presheaves of morphisms**: for `φ : M' ⟶ M` and `ψ : N ⟶ N'`,
the morphism of presheaves `F.presheafHom M N ⟶ F.presheafHom M' N'` sending a local morphism
`p : t^* M ⟶ t^* N` over `t : T ⟶ S` to `t^* φ ≫ p ≫ t^* ψ`. -/
@[expose]
def presheafHomMap {M M' N N' : F.obj (.mk (op S))} (φ : M' ⟶ M) (ψ : N ⟶ N') :
    F.presheafHom M N ⟶ F.presheafHom M' N' where
  app T := TypeCat.ofHom fun p ↦
    (F.map T.unop.hom.op.toLoc).toFunctor.map φ ≫ p ≫ (F.map T.unop.hom.op.toLoc).toFunctor.map ψ
  naturality T T' g := by
    ext p
    dsimp
    rw [pullHom_comp _ _ g.unop.left T'.unop.hom T'.unop.hom T'.unop.hom (Over.w g.unop)
      (Over.w g.unop) (Over.w g.unop), pullHom_comp _ _ g.unop.left T'.unop.hom T'.unop.hom
      T'.unop.hom (Over.w g.unop) (Over.w g.unop) (Over.w g.unop), pullHom_map, pullHom_map]

theorem presheafHomMap_app_apply {M M' N N' : F.obj (.mk (op S))} (φ : M' ⟶ M) (ψ : N ⟶ N')
    (T : (Over S)ᵒᵖ) (p : (F.presheafHom M N).obj T) :
    (F.presheafHomMap φ ψ).app T p =
      (F.map T.unop.hom.op.toLoc).toFunctor.map φ ≫ p ≫
        (F.map T.unop.hom.op.toLoc).toFunctor.map ψ :=
  (rfl)

@[simp]
theorem presheafHomMap_id (M N : F.obj (.mk (op S))) :
    F.presheafHomMap (𝟙 M) (𝟙 N) = 𝟙 _ := by
  ext T p
  simp [presheafHomMap]

/-- `presheafHomMap` is compatible with composition, contravariantly in the source and covariantly
in the target. -/
theorem presheafHomMap_comp {M M' M'' N N' N'' : F.obj (.mk (op S))} (φ : M' ⟶ M)
    (φ' : M'' ⟶ M') (ψ : N ⟶ N') (ψ' : N' ⟶ N'') :
    F.presheafHomMap (φ' ≫ φ) (ψ ≫ ψ') = F.presheafHomMap φ ψ ≫ F.presheafHomMap φ' ψ' := by
  ext T p
  simp [presheafHomMap]

/-- With the identity in the source, `presheafHomMap` is postcomposition. -/
theorem presheafHomMap_id_left (M : F.obj (.mk (op S))) {N N' : F.obj (.mk (op S))}
    (ψ : N ⟶ N') : F.presheafHomMap (𝟙 M) ψ = F.presheafHomPostcomp M ψ := by
  ext T p
  simp only [presheafHomMap, TypeCat.hom_ofHom, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (F.presheafHomPostcomp_app_apply M ψ T p).symm

/-- **Isomorphisms act on presheaves of morphisms by isomorphisms**: for `e : M ≅ M'` and
`e' : N ≅ N'`, the isomorphism `F.presheafHom M N ≅ F.presheafHom M' N'` sending `p` over `t` to
`t^* e⁻¹ ≫ p ≫ t^* e'`. -/
@[expose, simps]
def presheafHomIso {M M' N N' : F.obj (.mk (op S))} (e : M ≅ M') (e' : N ≅ N') :
    F.presheafHom M N ≅ F.presheafHom M' N' where
  hom := F.presheafHomMap e.inv e'.hom
  inv := F.presheafHomMap e.hom e'.inv
  hom_inv_id := by rw [← presheafHomMap_comp, e.hom_inv_id, e'.hom_inv_id, presheafHomMap_id]
  inv_hom_id := by rw [← presheafHomMap_comp, e.inv_hom_id, e'.inv_hom_id, presheafHomMap_id]

/-- **Isomorphisms act on sheaves of morphisms by isomorphisms**: for a prestack `F`, the
isomorphism `F.sheafHom J M N ≅ F.sheafHom J M' N'` of `presheafHomIso e e'`. -/
@[expose]
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

end CategoryTheory.Pseudofunctor
