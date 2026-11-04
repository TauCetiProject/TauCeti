/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Sections over projective objects of a topos

An object `U` of a topos is weakly contractible when every epimorphism onto `U` splits; since
epimorphisms of a topos are stable under pullback, these are exactly the projective objects, and
this file works with Mathlib's `Projective` in the topos `Sheaf J (Type w)`. It shows that taking
sections over such an object is exact on sheaves of abelian groups, and more generally preserves
epimorphisms of sheaves with values in a concrete category.

The input is that epimorphisms of sheaves with values in a concrete category are epimorphisms of
the underlying sheaves of sets (`CategoryTheory.Sheaf.preservesEpimorphisms_sheafCompose_forget`):
both are the locally surjective morphisms. Consequently the free sheaf on a projective sheaf of
sets, the left adjoint of this forgetful functor applied to it, is again projective
(`CategoryTheory.Sheaf.projective_composeAndSheafify_obj`). For sheaves of abelian groups this
is the free abelian sheaf `ℤ[U]`, and morphisms out of it are the sections over `U`; Mathlib's
`preservesHomology_preadditiveCoyonedaObj_of_projective` and
`Abelian.Ext.eq_zero_of_projective` then show that sections over `U` are exact and that the
higher `Ext` groups out of `ℤ[U]` vanish.

When `U` is the sheaf represented by an object `X` of a subcanonical site, sections over `U`
are the values `F(X)`. In that case the evaluation `F ↦ F(X)` carries epimorphisms of sheaves to
surjections (`CategoryTheory.Sheaf.surjective_app_of_epi`), is exact on abelian sheaves and on
sheaves of modules over a ring (`CategoryTheory.Sheaf.preservesFiniteColimits_sheafSections_obj`),
and the higher sheaf cohomology over `X` of every abelian sheaf vanishes
(`CategoryTheory.Sheaf.subsingleton_H'_succ_of_projective`).

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Definition 3.2.1 and the proof
  of Proposition 3.2.3.
-/

public section

universe w' w v u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Concrete

variable {A : Type u'} [Category.{w} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [HasSheafify J A] [J.HasSheafCompose (forget A)] [J.WEqualsLocallyBijective A]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [Balanced (Sheaf J A)]

/-- An epimorphism of sheaves with values in a concrete category is an epimorphism of the
underlying sheaves of sets: both are the locally surjective morphisms. -/
instance preservesEpimorphisms_sheafCompose_forget :
    (sheafCompose J (forget A)).PreservesEpimorphisms where
  preserves φ _ := by
    have : IsLocallySurjective φ := (isLocallySurjective_iff_epi' (φ := φ)).2 ‹_›
    have : IsLocallySurjective ((sheafCompose J (forget A)).map φ) :=
      (Presheaf.isLocallySurjective_iff_whisker_forget J φ.hom).1 this
    exact epi_of_isLocallySurjective' _

/-- Sections over a projective sheaf of sets `U`, that is, morphisms from `U` to the underlying
sheaf of sets, carry epimorphisms of sheaves with values in a concrete category to surjections. -/
theorem preservesEpimorphisms_sheafCompose_comp_coyoneda_obj (U : Sheaf J (Type w))
    [Projective U] : (sheafCompose J (forget A) ⋙ coyoneda.obj (op U)).PreservesEpimorphisms := by
  have := (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj U).1 ‹_›
  infer_instance

/-- The free sheaf on a projective sheaf of sets is projective. Here the free sheaf is obtained by
sheafifying the objectwise free objects, the left adjoint of the forgetful functor to sheaves of
sets. -/
theorem projective_composeAndSheafify_obj {G : Type w ⥤ A} (adj : G ⊣ forget A)
    (U : Sheaf J (Type w)) [Projective U] : Projective ((composeAndSheafify J G).obj U) :=
  (Sheaf.adjunction J adj).map_projective U ‹_›

end Concrete

section AddCommGrp

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The free abelian sheaf `ℤ[U]` on a projective sheaf of sets `U` is projective. Morphisms out of
`ℤ[U]` are the sections over `U`, so with Mathlib's
`preservesHomology_preadditiveCoyonedaObj_of_projective` this says that sections over `U` are
exact on abelian sheaves. -/
instance projective_composeAndSheafify_free_obj (U : Sheaf J (Type w)) [Projective U] :
    Projective ((composeAndSheafify J AddCommGrpCat.free).obj U) :=
  projective_composeAndSheafify_obj AddCommGrpCat.adj U

end AddCommGrp

section Representable

variable [J.Subcanonical]

section Concrete

variable {A : Type u'} [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{v} A FA]
  [HasSheafify J A] [J.HasSheafCompose (forget A)] [J.WEqualsLocallyBijective A]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A] [Balanced (Sheaf J A)]

/-- If the sheaf represented by `X` is projective, an epimorphism of sheaves with values in a
concrete category is surjective on sections over `X`. -/
theorem surjective_app_of_epi (X : C) [Projective (J.yoneda.obj X)] {F G : Sheaf J A}
    (φ : F ⟶ G) [Epi φ] : Function.Surjective (φ.hom.app (op X)) := by
  intro x
  -- Lift the morphism from the representable sheaf classifying `x` along the underlying
  -- epimorphism of sheaves of sets.
  let s : J.yoneda.obj X ⟶ (sheafCompose J (forget A)).obj G := J.yonedaEquiv.symm x
  refine ⟨J.yonedaEquiv (Projective.factorThru s ((sheafCompose J (forget A)).map φ)), ?_⟩
  -- The values of the underlying sheaf of sets of `G` are definitionally those of `G`.
  change J.yonedaEquiv (Projective.factorThru s _ ≫ (sheafCompose J (forget A)).map φ) = x
  rw [Projective.factorThru_comp]
  exact (J.yonedaEquiv (X := X) (F := (sheafCompose J (forget A)).obj G)).apply_symm_apply x

include FA CA in
/-- If the sheaf represented by `X` is projective, taking sections over `X` preserves
epimorphisms of sheaves with values in a concrete category. -/
theorem preservesEpimorphisms_sheafSections_obj (X : C) [Projective (J.yoneda.obj X)] :
    ((sheafSections J A).obj (op X)).PreservesEpimorphisms where
  preserves φ _ := ConcreteCategory.epi_of_surjective _ (surjective_app_of_epi X φ)

include FA CA in
/-- **Sections over a weakly contractible object are exact.** If the sheaf represented by `X` is
projective, taking sections over `X` preserves finite colimits of sheaves with values in an
abelian concrete category, such as abelian sheaves or sheaves of modules over a ring. Limits of
sheaves are computed on sections (`sheafSectionsNatIsoEvaluation`), so this is the exactness of
`F ↦ F(X)`. -/
instance preservesFiniteColimits_sheafSections_obj [Abelian A] (X : C)
    [Projective (J.yoneda.obj X)] :
    PreservesFiniteColimits ((sheafSections J A).obj (op X)) := by
  -- Work with the evaluation of underlying presheaves, which carries the additivity and
  -- limit-preservation instances.
  let e := sheafSectionsNatIsoEvaluation (J := J) (A := A) (X := X)
  have := preservesEpimorphisms_sheafSections_obj (A := A) (J := J) X
  have := Functor.PreservesEpimorphisms.of_iso e
  have : (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op X)).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have := Functor.preservesFiniteColimits_of_preservesHomology
    (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op X))
  exact preservesFiniteColimits_of_natIso e.symm

end Concrete

section AddCommGrp

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- If the sheaf represented by `X` is projective, the higher sheaf cohomology over `X` of every
abelian sheaf vanishes. -/
instance subsingleton_H'_succ_of_projective [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C) [Projective (J.yoneda.obj X)] (n : ℕ) :
    Subsingleton (F.H' (n + 1) X) :=
  -- Mathlib's `H'` is `Ext` out of the sheafified free abelian presheaf on `yoneda.obj X`,
  -- which is definitionally the free abelian sheaf on the representable sheaf `J.yoneda.obj X`.
  Abelian.Ext.subsingleton_of_projective
    ((composeAndSheafify J AddCommGrpCat.free).obj (J.yoneda.obj X)) F n

end AddCommGrp

end Representable

end CategoryTheory.Sheaf
