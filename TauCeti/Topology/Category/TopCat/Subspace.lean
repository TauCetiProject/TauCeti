/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Cones

/-!
# Subspace inclusions in `TopCat`

The canonical inclusions of subspaces are monomorphisms, and the inclusions of nested subspaces
compose to an inclusion. These supply the monomorphism hypotheses for the subspace inclusions in
the Mayer–Vietoris pushout square, and the functoriality of homology along nested subspaces.

The subspaces of a monotone family of subsets form a diagram `TauCeti.subspaceDiagram`, with the
cocone `TauCeti.subspaceCocone` of inclusions into a subspace containing all of them. When the
family is directed and covers that subspace by relatively open sets, every compact subset of the
subspace lies in one member (`TauCeti.exists_subset_range_subspaceCocone_ι_app`).
-/

public section

open CategoryTheory Limits Topology

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

variable (U V : Set X)

/-- The square of inclusions of `U ∩ V`, `U` and `V` into `X` commutes. -/
lemma commSq_ofHom_inter :
    CommSq (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V))))
      (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))
      (ofHom (ContinuousMap.subtypeVal U)) (ofHom (ContinuousMap.subtypeVal V)) :=
  ⟨rfl⟩

end TopCat

namespace TauCeti

open TopCat

section Subspace

variable {Y : TopCat.{u}} {J : Type*} [Preorder J] {U : J → Set Y} (hU : Monotone U)
  {V : Set Y} (hUV : ∀ j, U j ⊆ V)

/-- The subspaces of a monotone family of subsets of a space, with the inclusions between them. -/
@[expose, simps]
def subspaceDiagram : J ⥤ TopCat.{u} where
  obj j := of (U j)
  map f := ofHom (ContinuousMap.inclusion (hU f.le))

/-- The inclusions of the subspaces of a monotone family of subsets into a subspace containing all
of them. -/
@[expose, simps]
def subspaceCocone : Cocone (subspaceDiagram hU) where
  pt := of V
  ι := { app j := ofHom (ContinuousMap.inclusion (hUV j)) }

variable [IsDirected J (· ≤ ·)] [Nonempty J]
  (hopen : ∀ j, IsOpen (Subtype.val ⁻¹' U j : Set V)) (hcover : V ⊆ ⋃ j, U j)

include hopen hcover in
/-- A compact subset of `V` lies in one member of an increasing cover of `V` by subsets open in
`V`. -/
lemma exists_subset_range_subspaceCocone_ι_app (K : Set (subspaceCocone hU hUV).pt)
    (hK : IsCompact K) : ∃ j, K ⊆ Set.range ((subspaceCocone hU hUV).ι.app j) := by
  obtain ⟨j, hj⟩ := hK.elim_directed_cover (fun j ↦ (Subtype.val ⁻¹' U j : Set V)) hopen
    (fun x _ ↦ Set.mem_iUnion.2 (Set.mem_iUnion.1 (hcover x.2) : ∃ j, x.1 ∈ U j))
    (Monotone.directed_le fun _ _ h ↦ Set.preimage_mono (hU h))
  exact ⟨j, fun x hx ↦ ⟨⟨x.1, hj hx⟩, rfl⟩⟩

end Subspace

end TauCeti
