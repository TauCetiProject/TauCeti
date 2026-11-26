/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Comparisons between cohomology theories of functors

Let `F : C ⥤ AddCommGrpCat` and `F' : C' ⥤ AddCommGrpCat` be coefficient functors on two
categories. A *comparison* from `F` to `F'` is a functor `φ : C' ⥤ C` with a natural
transformation `β : φ ⋙ F ⟶ F'`. For functors `N : C ⥤ AddCommGrpCat`, `N' : C' ⥤ AddCommGrpCat`
and a map `α : N' ⟶ φ ⋙ N` it gives the homomorphisms

`Extⁿ(N, F) ⟶ Extⁿ(φ ⋙ N, φ ⋙ F) ⟶ Extⁿ(φ ⋙ N, F') ⟶ Extⁿ(N', F')`

that restrict along `φ` (an exact functor between the categories of functors), push forward by `β`
and pull back by `α`. This is `CategoryTheory.Functor.extComparison φ β α n`. The comparison is
*bijective along `α`* (`CategoryTheory.Functor.IsExtComparisonBijective`) if these maps are
bijective in every degree. Isomorphisms give bijective comparisons for the identity functor
(`CategoryTheory.Functor.isExtComparisonBijective_id_of_isIso`), and bijective comparisons compose
(`CategoryTheory.Functor.IsExtComparisonBijective.comp`).

Comparison maps are natural in the source and in the coefficients
(`CategoryTheory.Functor.mk₀_comp_extComparison` and
`CategoryTheory.Functor.extComparison_comp_mk₀`), compose
(`CategoryTheory.Functor.extComparison_extComparison`), reduce to pull-back and push-forward for
the identity functor (`CategoryTheory.Functor.extComparison_id_apply`), and a natural
transformation `η : φ ⟶ ψ` can be moved from the coefficients to the source
(`CategoryTheory.Functor.extComparison_whiskerRight_comp`). The proofs rest on Mathlib's
compatibility of `CategoryTheory.Abelian.Ext.mapExactFunctor` with composition of classes, of
functors, and with natural transformations.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Etale/Basic.lean` (declarations `New.Variety.Comparison`,
  `New.Variety.Comparison.pull`, `New.Variety.Comparison.pull_push`,
  `New.Variety.Comparison.id_pull`, `New.Variety.Comparison.pull_whiskerRight`,
  `New.Variety.Comparison.map_pull_eq_pull_map`, `New.Variety.Comparison.pull_trans`);
  Apache 2.0, Copyright 2026 Anthropic, PBC. The statements are adapted from these declarations,
  with the comparison unbundled into the functor `φ` and the map `β`.
-/

public section

open CategoryTheory Abelian

universe t t' t'' w v u v' u' v'' u''

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {C'' : Type u''} [Category.{v''} C'']
  [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C' ⥤ AddCommGrpCat.{w})]
  [HasExt.{t''} (C'' ⥤ AddCommGrpCat.{w})]
  {F G N M : C ⥤ AddCommGrpCat.{w}} {F' G' N' M' : C' ⥤ AddCommGrpCat.{w}}
  {F'' N'' : C'' ⥤ AddCommGrpCat.{w}} {n : ℕ}

/-- The *comparison map* `Extⁿ(N, F) ⟶ Extⁿ(N', F')` of a comparison `(φ, β)` from `F` on `C` to
`F'` on `C'`, along `α : N' ⟶ φ ⋙ N`: restrict a class along `φ`, push it forward by
`β : φ ⋙ F ⟶ F'` and pull it back by `α`. -/
noncomputable def extComparison (φ : C' ⥤ C) (β : φ ⋙ F ⟶ F') (α : N' ⟶ φ ⋙ N) (n : ℕ) :
    Ext.{t} N F n →+ Ext.{t'} N' F' n :=
  ((Ext.mk₀ α).precomp F' (zero_add n)).comp
    (((Ext.mk₀ β).postcomp (φ ⋙ N) (add_zero n)).comp
      (((whiskeringLeft C' C AddCommGrpCat.{w}).obj φ).mapExtAddHom N F n))

/-- The comparison map restricts along `φ`, composes with `β` and precomposes with `α`. -/
lemma extComparison_apply (φ : C' ⥤ C) (β : φ ⋙ F ⟶ F') (α : N' ⟶ φ ⋙ N) (x : Ext.{t} N F n) :
    extComparison φ β α n x = (Ext.mk₀ α).comp
      ((x.mapExactFunctor ((whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)).comp (Ext.mk₀ β)
        (add_zero n)) (zero_add n) :=
  (rfl)

/-- A comparison `(φ, β)` is *bijective along* `α` if its comparison maps are bijective in every
degree. -/
def IsExtComparisonBijective (φ : C' ⥤ C) (β : φ ⋙ F ⟶ F') (α : N' ⟶ φ ⋙ N) : Prop :=
  ∀ n : ℕ, Function.Bijective (extComparison.{t, t'} φ β α n)

/-- For the identity functor the comparison map is push-forward along `β` followed by pull-back
along `α`. -/
lemma extComparison_id_apply (β : F ⟶ G) (α : M ⟶ N) (x : Ext.{t} N F n) :
    extComparison (𝟭 C) β α n x =
      (Ext.mk₀ α).comp (x.comp (Ext.mk₀ β) (add_zero n)) (zero_add n) := by
  -- `Ext.id_mapExactFunctor` is stated for `𝟭 (C ⥤ AddCommGrpCat)`, which is
  -- `(whiskeringLeft C C _).obj (𝟭 C)` by `rfl` (Mathlib's `Functor.whiskeringLeft_obj_id`).
  -- The type of `Ext.mapExactFunctor` depends on the functor, so that equality is used
  -- definitionally here.
  have hid : x.mapExactFunctor ((whiskeringLeft C C AddCommGrpCat.{w}).obj (𝟭 C)) = x :=
    Ext.id_mapExactFunctor x
  rw [extComparison_apply, hid]

/-- For the identity functor, isomorphisms `β` and `α` give a bijective comparison: its inverse
is the comparison along their inverses. -/
lemma isExtComparisonBijective_id_of_isIso (β : F ⟶ G) (α : M ⟶ N) [IsIso β] [IsIso α] :
    IsExtComparisonBijective.{t, t} (𝟭 C) β α := fun n ↦ by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨extComparison (𝟭 C) (CategoryTheory.inv β) (CategoryTheory.inv α) n, fun x ↦ ?_,
      fun x ↦ ?_⟩ <;>
  simp only [extComparison_id_apply, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    Ext.mk₀_comp_mk₀, IsIso.hom_inv_id, IsIso.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_mk₀_id]

/-- Comparison maps are natural in the source: if `a' : M' ⟶ N'` lies over `γ : M ⟶ N`, in the
sense that `a' ≫ a = b ≫ φ.whiskerLeft γ`, then pulling back along `a'` after the comparison map
along `a` is the comparison map along `b` after pulling back along `γ`. -/
lemma mk₀_comp_extComparison (φ : C' ⥤ C) (β : φ ⋙ F ⟶ F') {a' : M' ⟶ N'} {a : N' ⟶ φ ⋙ N}
    {γ : M ⟶ N} {b : M' ⟶ φ ⋙ M} (h : a' ≫ a = b ≫ φ.whiskerLeft γ) (x : Ext.{t} N F n) :
    (Ext.mk₀ a').comp (extComparison φ β a n x) (zero_add n) =
      extComparison φ β b n ((Ext.mk₀ γ).comp x (zero_add n)) := by
  rw [extComparison_apply, extComparison_apply, Ext.mk₀_comp_mk₀_assoc, h,
    ← Ext.mk₀_comp_mk₀_assoc, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, whiskeringLeft_obj_map]

/-- Comparison maps are natural in the coefficients: if `γ : F ⟶ G` and `γ' : F' ⟶ G'` are
compatible with `β` and `β'`, in the sense that `φ.whiskerLeft γ ≫ β' = β ≫ γ'`, then the
comparison map for `β'` after pushing forward along `γ` is pushing forward along `γ'` after the
comparison map for `β`. -/
lemma extComparison_comp_mk₀ (φ : C' ⥤ C) {β : φ ⋙ F ⟶ F'} {β' : φ ⋙ G ⟶ G'} {γ : F ⟶ G}
    {γ' : F' ⟶ G'} (h : φ.whiskerLeft γ ≫ β' = β ≫ γ') (α : N' ⟶ φ ⋙ N) (x : Ext.{t} N F n) :
    extComparison φ β' α n (x.comp (Ext.mk₀ γ) (add_zero n)) =
      (extComparison φ β α n x).comp (Ext.mk₀ γ') (add_zero n) := by
  simp only [extComparison_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [whiskeringLeft_obj_map, h]

/-- Comparison maps compose: the comparison map of `(ψ, β')` along `α'` after that of `(φ, β)`
along `α` is the comparison map of the composite `(ψ ⋙ φ, ψ.whiskerLeft β ≫ β')` along
`α' ≫ ψ.whiskerLeft α`. -/
lemma extComparison_extComparison (φ : C' ⥤ C) (ψ : C'' ⥤ C') (β : φ ⋙ F ⟶ F')
    (β' : ψ ⋙ F' ⟶ F'') (α : N' ⟶ φ ⋙ N) (α' : N'' ⟶ ψ ⋙ N') (x : Ext.{t} N F n) :
    extComparison ψ β' α' n (extComparison φ β α n x) =
      extComparison (ψ ⋙ φ) (ψ.whiskerLeft β ≫ β') (α' ≫ ψ.whiskerLeft α) n x := by
  -- `Ext.comp_mapExactFunctor` is stated for the composite of the two restriction functors,
  -- which is `(whiskeringLeft C'' C _).obj (ψ ⋙ φ)` by `rfl` (Mathlib's
  -- `Functor.whiskeringLeft_obj_comp`).
  -- The type of `Ext.mapExactFunctor` depends on the functor, so that equality is used
  -- definitionally here.
  have h : x.mapExactFunctor ((whiskeringLeft C'' C AddCommGrpCat.{w}).obj (ψ ⋙ φ)) =
      (x.mapExactFunctor ((whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)).mapExactFunctor
        ((whiskeringLeft C'' C' AddCommGrpCat.{w}).obj ψ) :=
    Ext.comp_mapExactFunctor x ((whiskeringLeft C' C _).obj φ) ((whiskeringLeft C'' C' _).obj ψ)
  simp only [extComparison_apply, h, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    whiskeringLeft_obj_map]

/-- Bijective comparisons compose: if `(φ, β)` is bijective along `α` and `(ψ, β')` is bijective
along `α'`, the composite `(ψ ⋙ φ, ψ.whiskerLeft β ≫ β')` is bijective along
`α' ≫ ψ.whiskerLeft α`. -/
lemma IsExtComparisonBijective.comp {φ : C' ⥤ C} {ψ : C'' ⥤ C'} {β : φ ⋙ F ⟶ F'}
    {β' : ψ ⋙ F' ⟶ F''} {α : N' ⟶ φ ⋙ N} {α' : N'' ⟶ ψ ⋙ N'}
    (h : IsExtComparisonBijective.{t, t'} φ β α) (h' : IsExtComparisonBijective.{t', t''} ψ β' α') :
    IsExtComparisonBijective.{t, t''} (ψ ⋙ φ) (ψ.whiskerLeft β ≫ β') (α' ≫ ψ.whiskerLeft α) :=
  fun n ↦ by
    have : ⇑(extComparison.{t, t''} (ψ ⋙ φ) (ψ.whiskerLeft β ≫ β') (α' ≫ ψ.whiskerLeft α) n) =
        extComparison ψ β' α' n ∘ extComparison φ β α n :=
      funext fun x ↦ (extComparison_extComparison φ ψ β β' α α' x).symm
    rw [this]
    exact (h' n).comp (h n)

/-- A natural transformation `η : φ ⟶ ψ` can be moved from the coefficients to the source: the
comparison map of `(φ, F.whiskerRight η ≫ β)` along `α` is that of `(ψ, β)` along
`α ≫ N.whiskerRight η`. -/
lemma extComparison_whiskerRight_comp {φ ψ : C' ⥤ C} (η : φ ⟶ ψ) (β : ψ ⋙ F ⟶ F')
    (α : N' ⟶ φ ⋙ N) (x : Ext.{t} N F n) :
    extComparison φ (whiskerRight η F ≫ β) α n x =
      extComparison ψ β (α ≫ whiskerRight η N) n x := by
  have h : (x.mapExactFunctor ((whiskeringLeft C' C AddCommGrpCat.{w}).obj φ)).comp
      (Ext.mk₀ (whiskerRight η F)) (add_zero n) =
      (Ext.mk₀ (whiskerRight η N)).comp
        (x.mapExactFunctor ((whiskeringLeft C' C AddCommGrpCat.{w}).obj ψ)) (zero_add n) :=
    Ext.mapExactFunctor_comp_mk₀_natTransApp x ((whiskeringLeft C' C AddCommGrpCat.{w}).map η)
  rw [extComparison_apply, extComparison_apply, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero _ (Ext.mk₀ (whiskerRight η F)), h,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc]

end CategoryTheory.Functor
