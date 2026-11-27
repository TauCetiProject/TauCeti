/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.FullSubcategory
public import TauCeti.AlgebraicTopology.SimplicialNerve.Basic
public import TauCeti.CategoryTheory.Enriched.Basic

/-!
# Full simplicial subcategories and their simplicial nerves

A simplicial functor `F : EnrichedFunctor SSet C D` that is injective on objects and induces
isomorphisms on all mapping simplicial sets identifies `SimplicialNerve C` with the full enhanced
subcategory of `SimplicialNerve D` spanned by the vertices in the image of `F`
(`CategoryTheory.SimplicialNerve.fullSubcategoryIso`).

## Main results

* `CategoryTheory.SimplicialNerve.range_simplicialNerveMap_le`: every vertex in the range of
  `simplicialNerveMap F` satisfies any predicate holding on the object image of `F`.
* `CategoryTheory.SimplicialNerve.fullSubcategoryIso`: an object-injective simplicial functor
  inducing isomorphisms on mapping spaces identifies `SimplicialNerve C` with the corresponding
  full enhanced subcategory of `SimplicialNerve D`.
* `CategoryTheory.SimplicialNerve.fullSubcategoryIso_hom_ι`,
  `CategoryTheory.SimplicialNerve.fullSubcategoryIso_hom_app_val`: the isomorphism intertwines
  the full enhanced subcategory inclusion with `simplicialNerveMap F` and acts on simplices by
  postcomposition with `F`.
* `CategoryTheory.SimplicialNerve.mono_simplicialNerveMap`: an object-injective simplicial functor
  inducing isomorphisms on mapping spaces induces a monomorphism on simplicial nerves.
* `CategoryTheory.SimplicialNerve.range_simplicialNerveMap`: the range of `simplicialNerveMap F`
  for a simplicial functor inducing isomorphisms on mapping spaces equals that full enhanced
  subcategory.
-/

public section

open CategoryTheory EnrichedCategory Opposite Simplicial

universe v u

namespace CategoryTheory.SimplicialNerve

variable {C D : Type u} [Category.{v} C] [SimplicialCategory C]
  [Category.{v} D] [SimplicialCategory D]

/-- Every vertex in the image of `simplicialNerveMap F` satisfies any predicate holding on the
object image of `F`. -/
lemma range_simplicialNerveMap_le (F : EnrichedFunctor SSet.{v} C D)
    (P : D → Prop) (hP : ∀ c, P (F.obj c)) :
    SSet.Subcomplex.range (simplicialNerveMap F) ≤
      (SimplicialNerve D).fullEnhancedSubcategory fun x ↦ P (vertexEquiv D x) := by
  rw [SSet.range_le_fullEnhancedSubcategory_iff]
  intro x
  rw [vertexEquiv_simplicialNerveMap_app]
  exact hP _

-- To avoid constructing naturality of the inverse on simplices by hand, we factor
-- `simplicialNerveMap F` through the full enhanced subcategory inclusion and show each component is
-- bijective by lifting enriched functors `C[Δ^n] ⥤ D` along `F` via `EnrichedFunctor.lift`, then
-- deduce that the factorization is an isomorphism via `NatIso.isIso_of_isIso_app`.
private noncomputable def simplicialNerveMapToFullSubcategory (F : EnrichedFunctor SSet.{v} C D)
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj) :
    SimplicialNerve C ⟶
      ((SimplicialNerve D).fullEnhancedSubcategory fun x ↦ P (vertexEquiv D x) :
        SSet.{max u v}) :=
  SSet.Subcomplex.lift (simplicialNerveMap F)
    (range_simplicialNerveMap_le F P fun c ↦ (hP _).2 ⟨c, rfl⟩)

private lemma simplicialNerveMapToFullSubcategory_ι (F : EnrichedFunctor SSet.{v} C D)
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj) :
    simplicialNerveMapToFullSubcategory F P hP ≫ SSet.Subcomplex.ι _ =
      simplicialNerveMap F :=
  SSet.Subcomplex.lift_ι _ _

private lemma simplicialNerveMapToFullSubcategory_app_val (F : EnrichedFunctor SSet.{v} C D)
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj)
    (n : SimplexCategoryᵒᵖ) (H : (SimplicialNerve C).obj n) :
    ((simplicialNerveMapToFullSubcategory F P hP).app n H).val = H.comp SSet F :=
  (SSet.Subcomplex.lift_app_coe _ _ _).trans (simplicialNerveMap_app F n H)

private lemma exists_obj_eq (F : EnrichedFunctor SSet.{v} C D)
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj) {n : SimplexCategoryᵒᵖ}
    (G : ((SimplicialNerve D).fullEnhancedSubcategory fun x ↦ P (vertexEquiv D x)).obj n)
    (k : SimplicialThickening (ULift.{v} (Fin (n.unop.len + 1)))) :
    ∃ c : C, F.obj c = G.val.obj k :=
  (hP _).1 <| by
    have h := (SSet.mem_fullEnhancedSubcategory_obj_iff _ _).1 G.property
      (SimplexCategory.const ⦋0⦌ n.unop k.as.down)
    rw [vertexEquiv_apply, map_apply_obj] at h
    exact h

private noncomputable def liftSimplicialNerve (F : EnrichedFunctor SSet.{v} C D)
    [∀ a b : C, IsIso (F.map a b)] (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj)
    {n : SimplexCategoryᵒᵖ}
    (G : ((SimplicialNerve D).fullEnhancedSubcategory fun x ↦ P (vertexEquiv D x)).obj n) :
    (SimplicialNerve C).obj n :=
  EnrichedFunctor.lift F G.val (fun k ↦ Classical.choose (exists_obj_eq F P hP G k))
    (fun k ↦ Classical.choose_spec (exists_obj_eq F P hP G k))

private lemma liftSimplicialNerve_rightInverse (F : EnrichedFunctor SSet.{v} C D)
    [∀ a b : C, IsIso (F.map a b)] (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj)
    (n : SimplexCategoryᵒᵖ)
    (G : ((SimplicialNerve D).fullEnhancedSubcategory fun x ↦ P (vertexEquiv D x)).obj n) :
    (simplicialNerveMapToFullSubcategory F P hP).app n (liftSimplicialNerve F P hP G) = G :=
  Subtype.ext <|
    (simplicialNerveMapToFullSubcategory_app_val F P hP n _).trans
      (EnrichedFunctor.lift_comp F G.val _ _)

private lemma surjective_simplicialNerveMapToFullSubcategory_app (F : EnrichedFunctor SSet.{v} C D)
    [∀ a b : C, IsIso (F.map a b)] (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj)
    (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((simplicialNerveMapToFullSubcategory F P hP).app n) :=
  fun G ↦ ⟨liftSimplicialNerve F P hP G, liftSimplicialNerve_rightInverse F P hP n G⟩

private lemma injective_simplicialNerveMapToFullSubcategory_app (F : EnrichedFunctor SSet.{v} C D)
    (hobj : Function.Injective F.obj) [∀ a b : C, IsIso (F.map a b)]
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj)
    (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((simplicialNerveMapToFullSubcategory F P hP).app n) := by
  have hL (H : (SimplicialNerve C).obj n) :
      liftSimplicialNerve F P hP ((simplicialNerveMapToFullSubcategory F P hP).app n H) = H := by
    refine (EnrichedFunctor.lift_unique H (fun k ↦ hobj ?_)
      (simplicialNerveMapToFullSubcategory_app_val F P hP n H).symm).symm
    rw [Classical.choose_spec (exists_obj_eq F P hP _ k),
      simplicialNerveMapToFullSubcategory_app_val]
    exact (EnrichedFunctor.comp_obj SSet H F k).symm
  intro H₁ H₂ hH
  rw [← hL H₁, ← hL H₂, hH]

/-- An object-injective simplicial functor inducing isomorphisms on all mapping simplicial sets
identifies `SimplicialNerve C` with the full enhanced subcategory of `SimplicialNerve D` spanned by
its object image. -/
noncomputable def fullSubcategoryIso (F : EnrichedFunctor SSet.{v} C D)
    (hobj : Function.Injective F.obj) [∀ a b : C, IsIso (F.map a b)]
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj) :
    SimplicialNerve C ≅
      ((SimplicialNerve D).fullEnhancedSubcategory fun x ↦ P (vertexEquiv D x) :
        SSet.{max u v}) :=
  haveI : ∀ n : SimplexCategoryᵒᵖ,
      IsIso ((simplicialNerveMapToFullSubcategory F P hP).app n) := fun n ↦
    (isIso_iff_bijective _).2
      ⟨injective_simplicialNerveMapToFullSubcategory_app F hobj P hP n,
       surjective_simplicialNerveMapToFullSubcategory_app F P hP n⟩
  haveI : IsIso (simplicialNerveMapToFullSubcategory F P hP) :=
    NatIso.isIso_of_isIso_app _
  asIso (simplicialNerveMapToFullSubcategory F P hP)

/-- Under `fullSubcategoryIso`, the inclusion of the full enhanced subcategory corresponds to
`simplicialNerveMap F`. -/
@[reassoc (attr := simp)]
lemma fullSubcategoryIso_hom_ι (F : EnrichedFunctor SSet.{v} C D)
    (hobj : Function.Injective F.obj) [∀ a b : C, IsIso (F.map a b)]
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj) :
    (fullSubcategoryIso F hobj P hP).hom ≫ SSet.Subcomplex.ι _ = simplicialNerveMap F :=
  simplicialNerveMapToFullSubcategory_ι F P hP

/-- An object-injective simplicial functor inducing isomorphisms on all mapping simplicial sets
induces a monomorphism on simplicial nerves. -/
theorem mono_simplicialNerveMap (F : EnrichedFunctor SSet.{v} C D)
    (hobj : Function.Injective F.obj) [∀ a b : C, IsIso (F.map a b)] :
    Mono (simplicialNerveMap F) := by
  rw [← fullSubcategoryIso_hom_ι F hobj (· ∈ Set.range F.obj) fun _ ↦ Iff.rfl]
  exact mono_comp _ _

/-- On arbitrary simplices, the underlying simplex of `(fullSubcategoryIso F hobj P hP).hom` is
postcomposition with `F`. -/
@[simp]
lemma fullSubcategoryIso_hom_app_val (F : EnrichedFunctor SSet.{v} C D)
    (hobj : Function.Injective F.obj) [∀ a b : C, IsIso (F.map a b)]
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj)
    (n : SimplexCategoryᵒᵖ) (H : (SimplicialNerve C).obj n) :
    dsimp% ((fullSubcategoryIso F hobj P hP).hom.app n H).val = EnrichedFunctor.comp SSet H F :=
  simplicialNerveMapToFullSubcategory_app_val F P hP n H

/-- The range of `simplicialNerveMap F` is the full enhanced subcategory spanned by the object
image of `F`. -/
lemma range_simplicialNerveMap (F : EnrichedFunctor SSet.{v} C D)
    [∀ a b : C, IsIso (F.map a b)]
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj) :
    SSet.Subcomplex.range (simplicialNerveMap F) =
      (SimplicialNerve D).fullEnhancedSubcategory fun x ↦ P (vertexEquiv D x) := by
  have (n : SimplexCategoryᵒᵖ) : Epi ((simplicialNerveMapToFullSubcategory F P hP).app n) :=
    (epi_iff_surjective _).2 (surjective_simplicialNerveMapToFullSubcategory_app F P hP n)
  have : Epi (simplicialNerveMapToFullSubcategory F P hP) :=
    NatTrans.epi_of_epi_app _
  rw [← simplicialNerveMapToFullSubcategory_ι F P hP, SSet.Subcomplex.range_comp,
    SSet.Subcomplex.range_eq_top, SSet.Subcomplex.image_top]
  exact Subfunctor.range_ι _

end CategoryTheory.SimplicialNerve
