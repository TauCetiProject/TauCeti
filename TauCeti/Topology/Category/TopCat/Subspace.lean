/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Subspace inclusions in `TopCat`

The canonical inclusions of subspaces are monomorphisms, the inclusions of nested subspaces
compose to an inclusion, the restrictions of a map to subspaces commute with the inclusions, and
`TopCat.ofHom_restrictPreimage_univ_eq` rewrites `ofHom (f.restrictPreimage Set.univ)` on
`Set.univ` as the subtype morphism `x ↦ ⟨f x.1, Set.mem_univ _⟩`, which
`TopCat.ofHom_restrictPreimage_univ_comp_isoOfHomeo_hom` identifies with `f` along
`Set.univ ≃ₜ X`. These supply the monomorphism hypotheses for the subspace inclusions in the
Mayer–Vietoris pushout square, the functoriality of homology along nested subspaces, and the
naturality of the Mayer–Vietoris sequences.
-/

public section

open CategoryTheory Topology

universe u

namespace TopCat

variable {α : Type u} [TopologicalSpace α]

/-- The inclusion of a subspace is a monomorphism of topological spaces. -/
instance mono_ofHom_subtypeVal (S : Set α) : Mono (ofHom (ContinuousMap.subtypeVal S)) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The inclusion of one subspace in another is a monomorphism of topological spaces. -/
instance mono_ofHom_inclusion {S T : Set α} (h : S ⊆ T) :
    Mono (ofHom (ContinuousMap.inclusion h)) :=
  (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective h)

/-- Composing the inclusions `r ⊆ s` and `s ⊆ t` gives the inclusion `r ⊆ t`. -/
@[reassoc (attr := simp)]
lemma ofHom_inclusion_comp_ofHom_inclusion {r s t : Set α} (hrs : r ⊆ s) (hst : s ⊆ t) :
    ofHom (ContinuousMap.inclusion hrs) ≫ ofHom (ContinuousMap.inclusion hst) =
      ofHom (ContinuousMap.inclusion (hrs.trans hst)) := by
  rw [← ofHom_comp, ContinuousMap.inclusion_comp_inclusion]

/-- Composing the inclusion `r ⊆ s` with the coercion `s → α` gives the coercion `r → α`. -/
@[reassoc (attr := simp)]
lemma ofHom_inclusion_comp_ofHom_subtypeVal {r s : Set α} (hrs : r ⊆ s) :
    ofHom (ContinuousMap.inclusion hrs) ≫ ofHom (ContinuousMap.subtypeVal s) =
      ofHom (ContinuousMap.subtypeVal r) := by
  rw [← ofHom_comp, ContinuousMap.subtypeVal_comp_inclusion]

section Restrict

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- Restricting `f` to a map `A ⟶ B` of subspaces commutes with the inclusions of `A` and `B`. -/
@[reassoc]
lemma ofHom_subtypeVal_comp {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    ofHom (ContinuousMap.subtypeVal A) ≫ f =
      ofHom ⟨hf.restrict, f.hom.continuous.restrict hf⟩ ≫ ofHom (ContinuousMap.subtypeVal B) :=
  rfl

/-- Restricting `f` to nested subspaces commutes with the inclusions between them. -/
@[reassoc]
lemma ofHom_inclusion_comp {A A' : Set X} {B B' : Set Y} (hA : A ⊆ A') (hB : B ⊆ B')
    (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B') :
    ofHom (ContinuousMap.inclusion hA) ≫ ofHom ⟨hf'.restrict, f.hom.continuous.restrict hf'⟩ =
      ofHom ⟨hf.restrict, f.hom.continuous.restrict hf⟩ ≫ ofHom (ContinuousMap.inclusion hB) :=
  rfl

end Restrict

/-- `TopCat.ofHom (f.restrictPreimage Set.univ)` typed on `Set.univ` is the subtype-restricted
morphism `x ↦ ⟨f x.1, Set.mem_univ _⟩`. -/
lemma ofHom_restrictPreimage_univ_eq {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    (ofHom (f.restrictPreimage Set.univ) : of (Set.univ : Set X) ⟶ of (Set.univ : Set Y)) =
      ofHom ⟨fun x ↦ ⟨f x.val, Set.mem_univ _⟩,
        (f.continuous.comp continuous_subtypeVal).subtype_mk _⟩ := by
  ext x; exact Set.restrictPreimage_coe Set.univ f x

/-- Restricting `f` to `Set.univ` commutes with the homeomorphisms `Set.univ ≃ₜ X` and
`Set.univ ≃ₜ Y`. -/
@[reassoc]
lemma ofHom_restrictPreimage_univ_comp_isoOfHomeo_hom {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    (ofHom (f.restrictPreimage Set.univ) : of (Set.univ : Set X) ⟶ of (Set.univ : Set Y)) ≫
        (isoOfHomeo (Homeomorph.Set.univ Y)).hom =
      (isoOfHomeo (Homeomorph.Set.univ X)).hom ≫ ofHom f := by
  ext x; exact Set.restrictPreimage_coe Set.univ f x

variable (U V : Set α)

/-- The square of inclusions of `U ∩ V`, `U` and `V` into `α` commutes. -/
lemma commSq_ofHom_inter :
    CommSq (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V))))
      (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))
      (ofHom (ContinuousMap.subtypeVal U)) (ofHom (ContinuousMap.subtypeVal V)) :=
  ⟨rfl⟩

end TopCat
