/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.FullSubcategory
public import TauCeti.AlgebraicTopology.SimplicialNerve.Basic

/-!
# Full simplicial subcategories and their simplicial nerves

A simplicial functor `F : EnrichedFunctor SSet C D` that is injective on objects and induces
isomorphisms on all mapping simplicial sets identifies `SimplicialNerve C` with the full enhanced
subcategory of `SimplicialNerve D` spanned by the vertices in the image of `F`
(`CategoryTheory.SimplicialNerve.fullSubcategoryIso`).

To avoid constructing naturality of the inverse on simplices by hand, we factor
`simplicialNerveMap F` through the full enhanced subcategory inclusion and show each component is
bijective by lifting enriched functors `C[Δ^n] ⥤ D` along `F`, then deduce that the factorization is
an isomorphism via `NatIso.isIso_of_isIso_app`.

## Main results

* `CategoryTheory.SimplicialNerve.vertexEquiv_simplicialNerveMap_app`: `simplicialNerveMap F` acts
  on vertices by `F.obj`.
* `CategoryTheory.SimplicialNerve.range_simplicialNerveMap_le`: every vertex in the range of
  `simplicialNerveMap F` lies in the image of `F`.
* `CategoryTheory.SimplicialNerve.fullSubcategoryIso`: an object-injective simplicial functor
  inducing isomorphisms on mapping spaces identifies `SimplicialNerve C` with the corresponding
  full enhanced subcategory of `SimplicialNerve D`.
* `CategoryTheory.SimplicialNerve.fullSubcategoryIso_hom_ι`: the isomorphism intertwines the full
  enhanced subcategory inclusion with `simplicialNerveMap F`.
* `CategoryTheory.SimplicialNerve.range_simplicialNerveMap`: the range of `simplicialNerveMap F`
  equals that full enhanced subcategory.
-/

public section

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe v' w' v u

namespace CategoryTheory

section Transport

private lemma eId_comp_eqToHom {V : Type v'} [Category.{w'} V] [MonoidalCategory V]
    {D : Type u} [EnrichedCategory V D] {d d' : D} (h : d = d') :
    eId V d ≫ eqToHom (by rw [h]) = eId V d' := by
  subst h
  simp

private lemma tensorHom_eqToHom_comp_eComp {V : Type v'} [Category.{w'} V] [MonoidalCategory V]
    {D : Type u} [EnrichedCategory V D] {a a' b b' c c' : D}
    (ha : a = a') (hb : b = b') (hc : c = c') :
    (eqToHom (by rw [ha, hb]) ⊗ₘ eqToHom (by rw [hb, hc])) ≫ eComp V a' b' c' =
      eComp V a b c ≫ eqToHom (by rw [ha, hc]) := by
  subst ha hb hc
  simp

private lemma F_map_eqToHom_inv {V : Type v'} [Category.{w'} V] [MonoidalCategory V]
    {C D : Type u} [EnrichedCategory V C] [EnrichedCategory V D]
    (F : EnrichedFunctor V C D) [∀ a b : C, IsIso (F.map a b)]
    {a a' b b' : C} (ha : a = a') (hb : b = b') :
    F.map a' b' ≫ eqToHom (by rw [ha, hb]) ≫ inv (F.map a b) =
      eqToHom (by rw [ha, hb]) := by
  subst ha hb
  simp

end Transport

namespace SimplicialNerve

variable {C D : Type u} [Category.{v} C] [SimplicialCategory C]
  [Category.{v} D] [SimplicialCategory D]

/-- `simplicialNerveMap F` acts on vertices by `F.obj`. -/
lemma vertexEquiv_simplicialNerveMap_app (F : EnrichedFunctor SSet.{v} C D)
    (x : (SimplicialNerve C) _⦋0⦌) :
    vertexEquiv D ((simplicialNerveMap F).app (op ⦋0⦌) x) = F.obj (vertexEquiv C x) := by
  rw [vertexEquiv_apply, vertexEquiv_apply, simplicialNerveMap_app]
  rfl

/-- Lift an enriched functor into `D` whose objects lie in the image of `F` along `F`, when `F`
induces isomorphisms on all mapping simplicial sets. -/
private noncomputable def liftSimplex
    (F : EnrichedFunctor SSet.{v} C D) [∀ a b : C, IsIso (F.map a b)]
    {A : Type*} [EnrichedCategory SSet.{v} A]
    (G : EnrichedFunctor SSet.{v} A D) (hG : ∀ k : A, ∃ c : C, F.obj c = G.obj k) :
    EnrichedFunctor SSet.{v} A C where
  obj k := Classical.choose (hG k)
  map i j := G.map i j ≫
    eqToHom (by rw [Classical.choose_spec (hG i), Classical.choose_spec (hG j)]) ≫
    inv (F.map (Classical.choose (hG i)) (Classical.choose (hG j)))
  map_id i := by
    rw [← cancel_mono (F.map _ _)]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, F.map_id,
      G.map_id_assoc, eId_comp_eqToHom (Classical.choose_spec (hG i)).symm]
  map_comp i j k := by
    rw [← cancel_mono (F.map _ _)]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, F.map_comp,
      tensorHom_comp_tensorHom_assoc, G.map_comp_assoc]
    rw [← tensorHom_comp_tensorHom_assoc,
      tensorHom_eqToHom_comp_eComp (Classical.choose_spec (hG i)).symm
        (Classical.choose_spec (hG j)).symm (Classical.choose_spec (hG k)).symm]

private lemma liftSimplex_congr
    (F : EnrichedFunctor SSet.{v} C D) [∀ a b : C, IsIso (F.map a b)]
    {A : Type*} [EnrichedCategory SSet.{v} A]
    {G₁ G₂ : EnrichedFunctor SSet.{v} A D} (h : G₁ = G₂)
    (h₁ : ∀ k : A, ∃ c : C, F.obj c = G₁.obj k)
    (h₂ : ∀ k : A, ∃ c : C, F.obj c = G₂.obj k) :
    liftSimplex F G₁ h₁ = liftSimplex F G₂ h₂ := by
  subst h
  rfl

private lemma comp_eqToHom_eq {V : Type v'} [Category.{w'} V]
    {X Y Z : V} (f : X ⟶ Y) (h₁ : Y = Z) (h₂ : Z = Y) :
    (f ≫ eqToHom h₁) ≫ eqToHom h₂ = f := by
  subst h₁
  simp

private lemma liftSimplex_comp
    (F : EnrichedFunctor SSet.{v} C D) [∀ a b : C, IsIso (F.map a b)]
    {A : Type*} [EnrichedCategory SSet.{v} A]
    (G : EnrichedFunctor SSet.{v} A D) (hG : ∀ k : A, ∃ c : C, F.obj c = G.obj k) :
    (liftSimplex F G hG).comp SSet F = G := by
  refine EnrichedFunctor.ext SSet (fun k ↦ Classical.choose_spec (hG k)) fun i j ↦ ?_
  have h1 : ((liftSimplex F G hG).comp SSet F).map i j =
      G.map i j ≫ eqToHom (by
        dsimp only [liftSimplex, EnrichedFunctor.comp]
        rw [Classical.choose_spec (hG i), Classical.choose_spec (hG j)]) := by
    dsimp only [liftSimplex, EnrichedFunctor.comp]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (congrArg (· ≫ eqToHom _) h1).trans (comp_eqToHom_eq _ _ _)

private lemma liftSimplex_of_comp
    (F : EnrichedFunctor SSet.{v} C D) (hobj : Function.Injective F.obj)
    [∀ a b : C, IsIso (F.map a b)]
    {A : Type*} [EnrichedCategory SSet.{v} A]
    (H : EnrichedFunctor SSet.{v} A C)
    (hH : ∀ k : A, ∃ c : C, F.obj c = (H.comp SSet F).obj k) :
    liftSimplex F (H.comp SSet F) hH = H := by
  have hc : ∀ k, Classical.choose (hH k) = H.obj k :=
    fun k ↦ hobj (Classical.choose_spec (hH k))
  refine EnrichedFunctor.ext SSet hc fun i j ↦ ?_
  have h1 : (liftSimplex F (H.comp SSet F) hH).map i j =
      H.map i j ≫ eqToHom (by dsimp only [liftSimplex]; rw [hc i, hc j]) := by
    dsimp only [liftSimplex, EnrichedFunctor.comp]
    simp only [Category.assoc]
    exact congrArg (H.map i j ≫ ·) (F_map_eqToHom_inv F (hc i) (hc j))
  exact (congrArg (· ≫ eqToHom _) h1).trans (comp_eqToHom_eq _ _ _)

/-- Every vertex in the image of `simplicialNerveMap F` lies in the object image of `F`. -/
lemma range_simplicialNerveMap_le (F : EnrichedFunctor SSet.{v} C D)
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj) :
    SSet.Subcomplex.range (simplicialNerveMap F) ≤
      (SimplicialNerve D).fullEnhancedSubcategory fun x ↦ P (vertexEquiv D x) := by
  rw [SSet.range_le_fullEnhancedSubcategory_iff]
  intro x
  exact (hP _).2 ⟨vertexEquiv C x, (vertexEquiv_simplicialNerveMap_app F x).symm⟩

private lemma subcomplex_lift_simplicialNerveMap_app_val (F : EnrichedFunctor SSet.{v} C D)
    {B : (SimplicialNerve D).Subcomplex} (h : SSet.Subcomplex.range (simplicialNerveMap F) ≤ B)
    (n : SimplexCategoryᵒᵖ) (H : (SimplicialNerve C).obj n) :
    ((SSet.Subcomplex.lift (simplicialNerveMap F) h).app n H).val = H.comp SSet F :=
  (SSet.Subcomplex.lift_app_coe _ _ _).trans (simplicialNerveMap_app F n H)

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
      IsIso ((SSet.Subcomplex.lift (simplicialNerveMap F)
        (range_simplicialNerveMap_le F P hP)).app n) := fun n ↦ by
    rw [isIso_iff_bijective, Function.bijective_iff_has_inverse]
    have hmem : ∀ (G : ((SimplicialNerve D).fullEnhancedSubcategory
        fun x ↦ P (vertexEquiv D x)).obj n)
        (k : SimplicialThickening (ULift.{v} (Fin (n.unop.len + 1)))),
        ∃ c : C, F.obj c = G.val.obj k := fun G k ↦
      (hP _).1 <| by
        have h := (SSet.mem_fullEnhancedSubcategory_obj_iff _ _).1 G.property
          (SimplexCategory.const ⦋0⦌ n.unop k.as.down)
        rw [vertexEquiv_apply, map_apply_obj] at h
        exact h
    refine ⟨fun G ↦ liftSimplex F G.val (hmem G), fun H ↦ ?_, fun G ↦ Subtype.ext ?_⟩
    · have hval := subcomplex_lift_simplicialNerveMap_app_val F
        (range_simplicialNerveMap_le F P hP) n H
      have hH : ∀ k, ∃ c : C, F.obj c = (H.comp SSet F).obj k :=
        fun k ↦ hval ▸ hmem _ k
      exact (liftSimplex_congr F hval _ hH).trans (liftSimplex_of_comp F hobj H hH)
    · exact (subcomplex_lift_simplicialNerveMap_app_val F
        (range_simplicialNerveMap_le F P hP) n _).trans (liftSimplex_comp F G.val (hmem G))
  haveI : IsIso (SSet.Subcomplex.lift (simplicialNerveMap F)
      (range_simplicialNerveMap_le F P hP)) := NatIso.isIso_of_isIso_app _
  asIso (SSet.Subcomplex.lift (simplicialNerveMap F) (range_simplicialNerveMap_le F P hP))

/-- Under `fullSubcategoryIso`, the inclusion of the full enhanced subcategory corresponds to
`simplicialNerveMap F`. -/
@[reassoc (attr := simp)]
lemma fullSubcategoryIso_hom_ι (F : EnrichedFunctor SSet.{v} C D)
    (hobj : Function.Injective F.obj) [∀ a b : C, IsIso (F.map a b)]
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj) :
    (fullSubcategoryIso F hobj P hP).hom ≫ SSet.Subcomplex.ι _ = simplicialNerveMap F :=
  SSet.Subcomplex.lift_ι (simplicialNerveMap F) (range_simplicialNerveMap_le F P hP)

/-- The range of `simplicialNerveMap F` is the full enhanced subcategory spanned by the object
image of `F`. -/
lemma range_simplicialNerveMap (F : EnrichedFunctor SSet.{v} C D)
    (hobj : Function.Injective F.obj) [∀ a b : C, IsIso (F.map a b)]
    (P : D → Prop) (hP : ∀ d, P d ↔ d ∈ Set.range F.obj) :
    SSet.Subcomplex.range (simplicialNerveMap F) =
      (SimplicialNerve D).fullEnhancedSubcategory fun x ↦ P (vertexEquiv D x) := by
  rw [← fullSubcategoryIso_hom_ι F hobj P hP, SSet.Subcomplex.range_comp,
    SSet.Subcomplex.range_eq_top, SSet.Subcomplex.image_top]
  exact Subfunctor.range_ι _

end SimplicialNerve

end CategoryTheory
