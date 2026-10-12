/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.CategoryTheory.CommSq

/-!
# Subspace inclusions in `TopCat`

The canonical inclusions of subspaces are monomorphisms, the inclusions of nested subspaces
compose to an inclusion, and the restrictions of a map to subspaces commute with the
inclusions. These supply the monomorphism hypotheses for the subspace inclusions in the
Mayer–Vietoris pushout square, the functoriality of homology along nested subspaces, and the
naturality of the Mayer–Vietoris sequences.
-/

public section

open CategoryTheory Topology

universe u

namespace TopCat

variable {X : TopCat.{u}}

/-- The inclusion of a subspace is a monomorphism of topological spaces. -/
instance mono_ofHom_subtypeVal (S : Set X) : Mono (ofHom (ContinuousMap.subtypeVal S)) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The inclusion of one subspace in another is a monomorphism of topological spaces. -/
instance mono_ofHom_inclusion {S T : Set X} (h : S ⊆ T) :
    Mono (ofHom (ContinuousMap.inclusion h)) :=
  (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective h)

/-- Composing the inclusions `r ⊆ s` and `s ⊆ t` gives the inclusion `r ⊆ t`. -/
@[reassoc (attr := simp)]
lemma ofHom_inclusion_comp_ofHom_inclusion {α : Type u} [TopologicalSpace α] {r s t : Set α}
    (hrs : r ⊆ s) (hst : s ⊆ t) :
    ofHom (ContinuousMap.inclusion hrs) ≫ ofHom (ContinuousMap.inclusion hst) =
      ofHom (ContinuousMap.inclusion (hrs.trans hst)) := by
  rw [← ofHom_comp, ContinuousMap.inclusion_comp_inclusion]

section Restrict

variable {Y : TopCat.{u}} (f : X ⟶ Y)

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

variable (U V : Set X)

/-- The square of inclusions of `U ∩ V`, `U` and `V` into `X` commutes. -/
lemma commSq_ofHom_inter :
    CommSq (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V))))
      (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))
      (ofHom (ContinuousMap.subtypeVal U)) (ofHom (ContinuousMap.subtypeVal V)) :=
  ⟨rfl⟩

end TopCat
