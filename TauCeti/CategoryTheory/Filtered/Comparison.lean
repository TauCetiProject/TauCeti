/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Comparison isomorphisms for functors inverting a cofiltered category

Let `J` be a cofiltered category, possibly empty, and let `F : J ⥤ C` send every morphism to
an isomorphism. Two objects `i j : J` are dominated by a common object `k`, with maps
`u : k ⟶ i` and `v : k ⟶ j`, and the isomorphism `inv (F.map u) ≫ F.map v` does not depend on
the choice of `k`, `u` and `v`. This gives canonical comparison isomorphisms
`F.cofilteredComparison i j : F.obj i ≅ F.obj j`.

These comparisons are the identity on `i`, invert when `i` and `j` are exchanged, satisfy the
cocycle law for three objects, and agree with `F.map` on morphisms of `J`. They commute with
postcomposition by any functor, and with a natural transformation `F ⟶ G ⋙ F'` along a
functor `G : J ⥤ J'` between cofiltered categories.

A typical use compares constructions depending on an auxiliary choice, when the choices form
a cofiltered category and refining a choice induces an isomorphism: the comparison of two
choices is then independent of the common refinement used to compute it.

The independence of the dominating object is Mathlib's
`CategoryTheory.Functor.IsEventuallyConstantTo.coneπApp_eq`.

## Main declarations

* `CategoryTheory.Functor.cofilteredComparison`: the comparison isomorphism.
* `CategoryTheory.Functor.cofilteredComparison_hom_eq`: its computation through any
  dominating object.
* `CategoryTheory.Functor.cofilteredComparison_trans`: the cocycle law.
* `CategoryTheory.Functor.cofilteredComparison_hom_comp_app`: compatibility with natural
  transformations along functors between cofiltered categories.
-/

public section

namespace CategoryTheory

open IsCofiltered

variable {J C : Type*} [Category* J] [Category* C]

/-- A composite of functors sends a morphism to an isomorphism when the first functor does. -/
instance Functor.isIso_comp_map {D : Type*} [Category* D] (F : J ⥤ C) (H : C ⥤ D) {i j : J}
    (f : i ⟶ j) [IsIso (F.map f)] : IsIso ((F ⋙ H).map f) :=
  inferInstanceAs (IsIso (H.map (F.map f)))

namespace Functor

variable [IsCofilteredOrEmpty J] (F : J ⥤ C) [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)]

/-- The comparison isomorphism `F.obj i ≅ F.obj j` for a functor out of a cofiltered category
sending every morphism to an isomorphism, computed through `IsCofiltered.min i j`.
By `cofilteredComparison_hom_eq`, any other object dominating `i` and `j` gives the same
isomorphism. -/
noncomputable def cofilteredComparison (i j : J) : F.obj i ≅ F.obj j :=
  (asIso (F.map (minToLeft i j))).symm ≪≫ asIso (F.map (minToRight i j))

/-- The comparison isomorphism is computed through any object dominating both objects. -/
theorem cofilteredComparison_hom_eq {i j k : J} (u : k ⟶ i) (v : k ⟶ j) :
    (F.cofilteredComparison i j).hom = CategoryTheory.inv (F.map u) ≫ F.map v := by
  have : IsCofiltered J := { nonempty := ⟨i⟩ }
  have h : F.IsEventuallyConstantTo i := fun _ _ ↦ inferInstance
  have inv_eq {k : J} (α : k ⟶ i) : (h.isoMap α ⟨𝟙 i⟩).inv = CategoryTheory.inv (F.map α) :=
    IsIso.eq_inv_of_hom_inv_id (h.isoMap_hom_inv_id α _)
  have h₁ := h.coneπApp_eq j _ (minToLeft i j) (minToRight i j)
  have h₂ := h.coneπApp_eq j k u v
  rw [inv_eq] at h₁ h₂
  simpa [cofilteredComparison, ← h₁] using h₂

/-- On a morphism of `J`, the comparison isomorphism is the image of that morphism. -/
theorem cofilteredComparison_hom_eq_map {i j : J} (u : i ⟶ j) :
    (F.cofilteredComparison i j).hom = F.map u := by
  simpa using F.cofilteredComparison_hom_eq (𝟙 i) u

@[simp]
theorem cofilteredComparison_refl (i : J) : F.cofilteredComparison i i = Iso.refl _ := by
  ext
  simpa using F.cofilteredComparison_hom_eq_map (𝟙 i)

/-- The cocycle law for comparison isomorphisms. -/
@[simp]
theorem cofilteredComparison_trans (i j k : J) :
    F.cofilteredComparison i j ≪≫ F.cofilteredComparison j k = F.cofilteredComparison i k := by
  let u : min (min i j) k ⟶ min i j := minToLeft _ _
  ext
  simp [F.cofilteredComparison_hom_eq (u ≫ minToLeft i j) (u ≫ minToRight i j),
    F.cofilteredComparison_hom_eq (u ≫ minToRight i j) (minToRight (min i j) k),
    F.cofilteredComparison_hom_eq (u ≫ minToLeft i j) (minToRight (min i j) k)]

@[reassoc (attr := simp)]
theorem cofilteredComparison_hom_comp_hom (i j k : J) :
    (F.cofilteredComparison i j).hom ≫ (F.cofilteredComparison j k).hom =
      (F.cofilteredComparison i k).hom :=
  congr_arg Iso.hom (F.cofilteredComparison_trans i j k)

@[reassoc (attr := simp)]
theorem map_comp_cofilteredComparison_hom {i j : J} (u : i ⟶ j) (k : J) :
    F.map u ≫ (F.cofilteredComparison j k).hom = (F.cofilteredComparison i k).hom := by
  simp [← F.cofilteredComparison_hom_eq_map u]

@[reassoc (attr := simp)]
theorem cofilteredComparison_hom_comp_map (i : J) {j k : J} (v : j ⟶ k) :
    (F.cofilteredComparison i j).hom ≫ F.map v = (F.cofilteredComparison i k).hom := by
  simp [← F.cofilteredComparison_hom_eq_map v]

@[simp]
theorem cofilteredComparison_inv (i j : J) :
    (F.cofilteredComparison i j).inv = (F.cofilteredComparison j i).hom :=
  Iso.inv_ext (by simp)

@[simp]
theorem cofilteredComparison_symm (i j : J) :
    (F.cofilteredComparison i j).symm = F.cofilteredComparison j i := by
  ext
  simp

/-- Postcomposing with any functor carries comparison isomorphisms to comparison
isomorphisms. -/
@[simp]
theorem cofilteredComparison_comp {D : Type*} [Category* D] (H : C ⥤ D) (i j : J) :
    (F ⋙ H).cofilteredComparison i j = H.mapIso (F.cofilteredComparison i j) := by
  ext
  simp [cofilteredComparison_hom_eq _ (minToLeft i j) (minToRight i j)]

/-- Comparison isomorphisms commute with a natural transformation `F ⟶ G ⋙ F'` along a
functor `G` between cofiltered categories. -/
@[reassoc]
theorem cofilteredComparison_hom_comp_app {J' : Type*} [Category* J'] [IsCofilteredOrEmpty J']
    (G : J ⥤ J') (F' : J' ⥤ C) [∀ (i j : J') (f : i ⟶ j), IsIso (F'.map f)]
    (τ : F ⟶ G ⋙ F') (i j : J) :
    (F.cofilteredComparison i j).hom ≫ τ.app j =
      τ.app i ≫ (F'.cofilteredComparison (G.obj i) (G.obj j)).hom := by
  rw [F.cofilteredComparison_hom_eq (minToLeft i j) (minToRight i j),
    F'.cofilteredComparison_hom_eq (G.map (minToLeft i j)) (G.map (minToRight i j))]
  simp [IsIso.inv_comp_eq]

end Functor

end CategoryTheory
