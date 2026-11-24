/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.FullSubcategory
public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.PiZero

/-!
# Fully faithful maps of simplicial sets

A map of simplicial sets `f : X ⟶ Y` is *fully faithful* (`SSet.IsFullyFaithful f`) when, for all
vertices `x` and `y` of `X`, the induced map of right mapping spaces
`Hom^R_X(x, y) ⟶ Hom^R_Y(f x, f y)` is a weak equivalence for the Kan–Quillen model structure.
For quasicategories this is the notion of a fully faithful functor of `∞`-categories: the right
mapping spaces model the spaces of maps, and a weak equivalence is an isomorphism in the homotopy
category of spaces. It is the mapping-space condition in the characterization of the categorical
equivalences of quasicategories as the fully faithful and essentially surjective maps, which is
not proved here.

Fully faithful maps are closed under composition and have the right cancellation property, and
every isomorphism is fully faithful. The inclusion of a full enhanced subcategory is fully
faithful: a simplex of a right mapping space has only its two endpoints as vertices, so the right
mapping spaces of the full enhanced subcategory are those of the ambient simplicial set. The right
mapping spaces of the nerve of a category are discrete on its morphisms, and the nerve of a fully
faithful functor is fully faithful.

Weak equivalences are bijective on connected components, and the connected components of the
right mapping spaces of a quasicategory are the morphisms of its homotopy category
(`SSet.rightMappingSpace.π₀Equiv`). Hence a fully faithful map of quasicategories is fully faithful
on homotopy categories, and, if it is also essentially surjective on homotopy categories, it induces
an equivalence of homotopy categories. Since the equivalences of a quasicategory are the edges
whose classes are invertible in the homotopy category, a fully faithful map of quasicategories
reflects equivalences.

## Main definitions

* `SSet.IsFullyFaithful f`: the maps induced by `f` on right mapping spaces are weak equivalences.

## Main results

* `SSet.IsFullyFaithful.comp`, `SSet.IsFullyFaithful.of_comp`: composition and right
  cancellation.
* `SSet.IsFullyFaithful.fullEnhancedSubcategory_ι`: the inclusion of a full enhanced subcategory is
  fully faithful.
* `SSet.IsFullyFaithful.nerveMap`: the nerve of a fully faithful functor is fully faithful.
* `SSet.IsFullyFaithful.faithful_mapHomotopyCategory`,
  `SSet.IsFullyFaithful.full_mapHomotopyCategory`: a fully faithful map of quasicategories is fully
  faithful on homotopy categories, and `SSet.IsFullyFaithful.isEquivalence_mapHomotopyCategory`:
  it induces an equivalence of homotopy categories when it is also essentially surjective on them.
* `SSet.Edge.isEquivalence_map_iff_of_isFullyFaithful`: a fully faithful map of quasicategories
  reflects equivalences.

## References

* J. Lurie, *Higher Topos Theory*, Definition 1.2.10.1 and §1.2.2.
-/

public section

open CategoryTheory HomotopicalAlgebra Opposite Simplicial

open scoped SSet.modelCategoryQuillen

universe u v w

namespace SSet

variable {X Y Z : SSet.{u}}

/-- A map of simplicial sets `f : X ⟶ Y` is fully faithful when, for all vertices `x` and `y` of
`X`, the induced map of right mapping spaces `Hom^R_X(x, y) ⟶ Hom^R_Y(f x, f y)` is a weak
equivalence. -/
class IsFullyFaithful (f : X ⟶ Y) : Prop where
  weakEquivalence_map (x y : X _⦋0⦌) : WeakEquivalence (rightMappingSpace.map x y f)

attribute [instance] IsFullyFaithful.weakEquivalence_map

namespace IsFullyFaithful

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A map inducing isomorphisms on all right mapping spaces is fully faithful. -/
lemma of_isIso_map (h : ∀ x y : X _⦋0⦌, IsIso (rightMappingSpace.map x y f)) :
    IsFullyFaithful f :=
  ⟨fun x y ↦ have := h x y; inferInstance⟩

instance of_isIso [IsIso f] : IsFullyFaithful f :=
  of_isIso_map f fun _ _ ↦ inferInstance

instance comp [IsFullyFaithful f] [IsFullyFaithful g] : IsFullyFaithful (f ≫ g) :=
  ⟨fun x y ↦ by
    rw [rightMappingSpace.map_comp]
    infer_instance⟩

/-- If `g` and `f ≫ g` are fully faithful, so is `f`. -/
lemma of_comp [IsFullyFaithful g] [IsFullyFaithful (f ≫ g)] : IsFullyFaithful f :=
  ⟨fun x y ↦ by
    have := weakEquivalence_map (f := f ≫ g) x y
    rw [rightMappingSpace.map_comp] at this
    exact weakEquivalence_of_postcomp _ (rightMappingSpace.map (f.app _ x) (f.app _ y) g)⟩

/-- The inclusion of a full enhanced subcategory is fully faithful: a simplex of a right mapping
space between vertices satisfying `P` has only these two vertices, so it lies in the full enhanced
subcategory. -/
instance fullEnhancedSubcategory_ι (P : X _⦋0⦌ → Prop) :
    IsFullyFaithful (X.fullEnhancedSubcategory P).ι :=
  of_isIso_map _ fun x y ↦ rightMappingSpace.isIso_map_ι x y fun n s ↦
    (mem_fullEnhancedSubcategory_obj_iff_forall_fin P (s.val : X _⦋n + 1⦌)).2 fun i ↦ by
      cases i using Fin.lastCases with
      | last =>
        rw [rightMappingSpace.map_const_last s]
        exact (mem_fullEnhancedSubcategory_obj_zero_iff P y.val).1 y.property
      | cast j =>
        rw [rightMappingSpace.map_const_castSucc s j]
        exact (mem_fullEnhancedSubcategory_obj_zero_iff P x.val).1 x.property

/-- The nerve of a fully faithful functor is fully faithful. -/
instance nerveMap {C D : Type v} [Category.{w} C] [Category.{w} D] (F : C ⥤ D) [F.Full]
    [F.Faithful] : IsFullyFaithful (nerveMap F) := by
  refine of_isIso_map _ fun x y ↦ (rightMappingSpace.isIso_map_iff_bijective _).2 ?_
  -- Edges of nerves are morphisms, on which the nerve of `F` acts by `F.map`.
  obtain ⟨a, rfl⟩ := nerveEquiv.symm.surjective x
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective y
  have hE : Function.Bijective (nerve.edgeMk : (a ⟶ b) → _) :=
    ⟨Function.LeftInverse.injective (g := nerve.homEquiv) fun _ ↦ nerve.homEquiv_edgeMk _,
      nerve.edgeMk_surjective⟩
  have hcomp : nerve.homEquiv ∘ (fun e ↦ e.map (CategoryTheory.nerveMap F)) ∘ nerve.edgeMk =
      fun f : a ⟶ b ↦ F.map f :=
    funext fun f ↦ nerve.homEquiv_edgeMk_map_nerveMap f F
  exact (Function.Bijective.of_comp_iff _ hE).1
    ((Function.Bijective.of_comp_iff' nerve.homEquiv.bijective _).1
      (hcomp ▸ ⟨F.map_injective, F.map_surjective⟩))

/-! ### Homotopy categories -/

section HomotopyCategory

variable [X.Quasicategory] [Y.Quasicategory] [IsFullyFaithful f]

/-- Under `rightMappingSpace.π₀Equiv`, the action of `mapHomotopyCategory f` on morphisms from `x`
to `y` is the bijection induced on connected components by the weak equivalence
`Hom^R_X(x, y) ⟶ Hom^R_Y(f x, f y)`. -/
private theorem bijective_map_mapHomotopyCategory (x y : X _⦋0⦌) :
    Function.Bijective ((mapHomotopyCategory f).map :
      (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) → _) := by
  have h : ((mapHomotopyCategory f).map :
      (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) → _) =
      rightMappingSpace.π₀Equiv _ _ ∘ mapπ₀ (rightMappingSpace.map x y f) ∘
        (rightMappingSpace.π₀Equiv x y).symm := by
    funext φ
    rw [Function.comp_apply, Function.comp_apply, rightMappingSpace.π₀Equiv_mapπ₀_map,
      Equiv.apply_symm_apply]
  rw [h]
  exact (Equiv.bijective _).comp
    ((bijective_mapπ₀_of_weakEquivalence _).comp (Equiv.bijective _))

/-- A fully faithful map of quasicategories is faithful on homotopy categories. -/
instance faithful_mapHomotopyCategory : (mapHomotopyCategory f).Faithful where
  map_injective {a b} := by
    induction a with | mk x => ?_
    induction b with | mk y => ?_
    exact (bijective_map_mapHomotopyCategory f x y).1

/-- A fully faithful map of quasicategories is full on homotopy categories. -/
instance full_mapHomotopyCategory : (mapHomotopyCategory f).Full where
  map_surjective {a b} := by
    induction a with | mk x => ?_
    induction b with | mk y => ?_
    exact (bijective_map_mapHomotopyCategory f x y).2

/-- A fully faithful and essentially surjective map of quasicategories induces an equivalence of
homotopy categories. -/
instance isEquivalence_mapHomotopyCategory [(mapHomotopyCategory f).EssSurj] :
    (mapHomotopyCategory f).IsEquivalence where

end HomotopyCategory

end IsFullyFaithful

/-- **Fully faithful maps reflect equivalences**: for a fully faithful map `f` of quasicategories,
an edge of the source is an equivalence exactly when its image under `f` is. -/
theorem Edge.isEquivalence_map_iff_of_isFullyFaithful [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y) [IsFullyFaithful f] {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    (e.map f).IsEquivalence ↔ e.IsEquivalence := by
  rw [Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk,
    Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk, ← mapHomotopyCategory_map_homMk]
  exact isIso_iff_of_reflects_iso _ _

end SSet
