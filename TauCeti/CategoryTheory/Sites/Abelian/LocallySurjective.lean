/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Epimorphisms of abelian sheaves are locally surjective

The local image of a morphism of abelian sheaves is an abelian subsheaf of its target. Factoring
an epimorphism through it shows local surjectivity. This argument works with arbitrary site and
coefficient universes, without a comparison between local bijectivity and sheafification.
Its underlying subsheaf is Mathlib's sheafification of `Subfunctor.range`, as in `Sheaf.image`
for sheaves of types; closure under addition supplies the abelian group structure.

This supplies the exactness of restriction to a localized site.
-/

public section

open CategoryTheory Limits Opposite Functor

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)

private def localImageSubgroup (X : Cᵒᵖ) : AddSubgroup (G.obj.obj X) where
  carrier := {s | Presheaf.imageSieve φ.hom s ∈ J X.unop}
  zero_mem' := by
    -- Membership in the local image is the covering condition on the image sieve.
    change Presheaf.imageSieve φ.hom 0 ∈ J X.unop
    have h := Presheaf.imageSieve_app φ.hom (0 : F.obj.obj X)
    rw [map_zero] at h
    rw [h]
    exact J.top_mem _
  add_mem' {x y} hx hy := by
    refine J.superset_covering ?_ (J.intersection_covering hx hy)
    rintro Y f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a + b, by simp [ha, hb]⟩
  neg_mem' {x} hx := by
    refine J.superset_covering ?_ hx
    rintro Y f ⟨a, ha⟩
    exact ⟨-a, by simp [ha]⟩

private def localImagePresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj X := AddCommGrpCat.of (localImageSubgroup φ X)
  map {X Y} f := AddCommGrpCat.ofHom
    { toFun := fun s ↦ ⟨G.obj.map f s, by
        -- The subtype predicate is transported by pulling back its image sieve.
        change Presheaf.imageSieve φ.hom (G.obj.map f s.val) ∈ J Y.unop
        rw [← Presheaf.pullback_imageSieve]
        exact J.pullback_stable f.unop s.property⟩
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  map_id X := by ext; simp
  map_comp f g := by ext; simp

private def localImage : Sheaf J AddCommGrpCat.{w} :=
  ⟨localImagePresheaf φ, by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{w})
    rw [isSheaf_iff_isSheaf_of_type]
    exact (Subfunctor.range (whiskerRight φ.hom (forget AddCommGrpCat.{w}))).sheafify_isSheaf
      ((isSheaf_iff_isSheaf_of_type J _).1
        ((sheafCompose J (forget AddCommGrpCat.{w})).obj G).property)⟩

private def localImageι : localImage φ ⟶ G :=
  ⟨{ app X := AddCommGrpCat.ofHom (localImageSubgroup φ X).subtype }⟩

private instance : Mono (localImageι φ) := by
  apply (sheafToPresheaf J AddCommGrpCat.{w}).mono_of_mono_map
  have (X : Cᵒᵖ) : Mono (((sheafToPresheaf J AddCommGrpCat.{w}).map (localImageι φ)).app X) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

private def toLocalImage : F ⟶ localImage φ :=
  ⟨{ app X := AddCommGrpCat.ofHom
      { toFun := fun s ↦ ⟨φ.hom.app X s, by
          -- A section in the image has the maximal image sieve.
          change Presheaf.imageSieve φ.hom (φ.hom.app X s) ∈ J X.unop
          rw [Presheaf.imageSieve_app]
          exact J.top_mem _⟩
        map_zero' := by ext; simp
        map_add' := by intros; ext; simp }
     naturality X Y f := by
       ext s
       exact Subtype.ext (NatTrans.naturality_apply φ.hom f s) }⟩

/-- An epimorphism of abelian sheaves is locally surjective whenever the category of abelian
sheaves is balanced, for instance when it is abelian. Beyond this hypothesis, the argument
places no restriction on the relative sizes of the site and the coefficient universe. -/
theorem isLocallySurjective_of_epi_addCommGrp [Balanced (Sheaf J AddCommGrpCat.{w})] [Epi φ] :
    IsLocallySurjective φ := by
  have h : toLocalImage φ ≫ localImageι φ = φ := by rfl
  have : Epi (localImageι φ) := epi_of_epi_fac h
  have : IsIso (localImageι φ) := isIso_of_mono_of_epi _
  constructor
  intro X s
  let t := (inv (localImageι φ)).hom.app (op X) s
  have ht : (localImageι φ).hom.app (op X) t = s := by
    -- Read the composite of sheaf morphisms as a composite on sections.
    change ((inv (localImageι φ) ≫ localImageι φ).hom.app (op X)) s = s
    simp
  rw [← ht]
  exact t.property

end CategoryTheory.Sheaf
