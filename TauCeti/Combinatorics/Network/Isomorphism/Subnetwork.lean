/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Isomorphism.Basic
public import TauCeti.Combinatorics.Network.Subnetwork

/-!
# Subnetworks under network isomorphisms

An isomorphism of bounded networks induces an order isomorphism of their subnetworks by
transporting the selected vertices and arrow identities. In particular, isolated selected
vertices are retained. Transport commutes with induced and singleton subnetworks, restriction,
and deletion; unions and intersections are preserved by the order isomorphism.

Each subnetwork is itself isomorphic to its image, with both bounds inherited unchanged.
Consequently the assignment, feasibility, excess, and walk transport of network isomorphisms
also applies to these networks on their actual selected vertex types. None of the constructions
here requires finiteness or algebraic structure on the bounds.
-/

public section

namespace TauCeti.Network.Iso

universe u u' u'' w

variable {K : Type w} [LE K] {V : Type u} {W : Type u'} {X : Type u''}
variable {N : Network K V} {N' : Network K W} {N'' : Network K X}

/-- The image of the two selected sets, with the endpoint condition transported. -/
private def mapSubnetwork (e : N ≃ₙ N') (S : N.Subnetwork) : N'.Subnetwork where
  vertexSet := e.vertexEquiv '' S.vertexSet
  arrowSet := e.totalHomEquiv '' S.arrowSet
  source_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a.1, S.source_mem a ha, congrArg Sigma.fst (e.totalHomEquiv_apply a).symm⟩
  target_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a.2.1, S.target_mem a ha,
      congrArg (fun a ↦ a.2.1) (e.totalHomEquiv_apply a).symm⟩

/-- Transport of subnetworks, preserving and reflecting inclusion of both selected sets. -/
def subnetworkOrderIso (e : N ≃ₙ N') : N.Subnetwork ≃o N'.Subnetwork where
  toFun := mapSubnetwork e
  invFun := mapSubnetwork e.symm
  left_inv S := by
    apply Subnetwork.ext <;>
      simp only [mapSubnetwork, totalHomEquiv_symm, symm_vertexEquiv,
        Equiv.symm_image_image]
  right_inv S := by
    apply Subnetwork.ext <;>
      simp only [mapSubnetwork, totalHomEquiv_symm, symm_vertexEquiv,
        Equiv.image_symm_image]
  map_rel_iff' := by
    intro S T
    exact and_congr (Set.image_subset_image_iff e.vertexEquiv.injective)
      (Set.image_subset_image_iff e.totalHomEquiv.injective)

/-- The selected vertices of an image subnetwork are the image of its selected vertices. -/
@[simp]
theorem subnetworkOrderIso_vertexSet (e : N ≃ₙ N') (S : N.Subnetwork) :
    (e.subnetworkOrderIso S).vertexSet = e.vertexEquiv '' S.vertexSet :=
  (rfl)

/-- The selected arrows of an image subnetwork are the image of its selected arrow identities. -/
@[simp]
theorem subnetworkOrderIso_arrowSet (e : N ≃ₙ N') (S : N.Subnetwork) :
    (e.subnetworkOrderIso S).arrowSet = e.totalHomEquiv '' S.arrowSet :=
  (rfl)

/-- Inverse subnetwork transport is transport along the inverse network isomorphism. -/
@[simp]
theorem subnetworkOrderIso_symm (e : N ≃ₙ N') :
    e.symm.subnetworkOrderIso = e.subnetworkOrderIso.symm := by
  apply DFunLike.ext
  intro S
  rfl

/-- Identity transport fixes every subnetwork. -/
@[simp]
theorem subnetworkOrderIso_refl (N : Network K V) :
    (refl N).subnetworkOrderIso = OrderIso.refl N.Subnetwork := by
  apply DFunLike.ext
  intro S
  apply Subnetwork.ext <;> simp

/-- Subnetwork transport commutes with composition of network isomorphisms. -/
@[simp]
theorem subnetworkOrderIso_trans (e : N ≃ₙ N') (f : N' ≃ₙ N'') :
    (e.trans f).subnetworkOrderIso = e.subnetworkOrderIso.trans f.subnetworkOrderIso := by
  apply DFunLike.ext
  intro S
  apply Subnetwork.ext <;> simp [Set.image_image]

/-- Inducing on selected vertices commutes with network isomorphisms. -/
@[simp]
theorem subnetworkOrderIso_induced (e : N ≃ₙ N') (A : Set V) :
    e.subnetworkOrderIso (N.inducedSubnetwork A) =
      N'.inducedSubnetwork (e.vertexEquiv '' A) := by
  apply Subnetwork.ext
  · simp
  · ext a
    obtain ⟨⟨x, y, a⟩, rfl⟩ := e.totalHomEquiv.surjective a
    rw [subnetworkOrderIso_arrowSet, e.totalHomEquiv.injective.mem_set_image]
    simp

/-- Transport retains the selected isolated vertex of a singleton subnetwork. -/
@[simp]
theorem subnetworkOrderIso_singleton (e : N ≃ₙ N') (x : V) :
    e.subnetworkOrderIso (N.singletonSubnetwork x) =
      N'.singletonSubnetwork (e.vertexEquiv x) := by
  apply Subnetwork.ext <;> simp

/-- Restricting selected vertices commutes with transport. -/
@[simp]
theorem subnetworkOrderIso_restrictVertices (e : N ≃ₙ N') (S : N.Subnetwork) (A : Set V) :
    e.subnetworkOrderIso (S.restrictVertices A) =
      (e.subnetworkOrderIso S).restrictVertices (e.vertexEquiv '' A) := by
  apply Subnetwork.ext
  · simp only [subnetworkOrderIso_vertexSet, Subnetwork.vertexSet_restrictVertices,
      Set.image_inter e.vertexEquiv.injective]
  · ext a
    obtain ⟨⟨x, y, a⟩, rfl⟩ := e.totalHomEquiv.surjective a
    rw [subnetworkOrderIso_arrowSet, e.totalHomEquiv.injective.mem_set_image]
    simp only [Subnetwork.mem_arrowSet_restrictVertices, subnetworkOrderIso_arrowSet,
      e.totalHomEquiv.injective.mem_set_image]
    rw [totalHomEquiv_apply]
    simp

/-- Restricting selected arrow identities commutes with transport. -/
@[simp]
theorem subnetworkOrderIso_restrictArrows (e : N ≃ₙ N') (S : N.Subnetwork)
    (A : Set (Σ x y, N.Hom x y)) :
    e.subnetworkOrderIso (S.restrictArrows A) =
      (e.subnetworkOrderIso S).restrictArrows (e.totalHomEquiv '' A) := by
  apply Subnetwork.ext
  · simp
  · simp only [subnetworkOrderIso_arrowSet, Subnetwork.arrowSet_restrictArrows,
      Set.image_inter e.totalHomEquiv.injective]

/-- Vertex deletion commutes with transport. -/
@[simp]
theorem subnetworkOrderIso_deleteVerts (e : N ≃ₙ N') (S : N.Subnetwork) (A : Set V) :
    e.subnetworkOrderIso (S.deleteVerts A) =
      (e.subnetworkOrderIso S).deleteVerts (e.vertexEquiv '' A) := by
  apply Subnetwork.ext
  · simp only [subnetworkOrderIso_vertexSet, Subnetwork.vertexSet_deleteVerts,
      Set.image_sdiff e.vertexEquiv.injective]
  · ext a
    obtain ⟨⟨x, y, a⟩, rfl⟩ := e.totalHomEquiv.surjective a
    rw [subnetworkOrderIso_arrowSet, e.totalHomEquiv.injective.mem_set_image]
    simp only [Subnetwork.mem_arrowSet_deleteVerts, subnetworkOrderIso_arrowSet,
      e.totalHomEquiv.injective.mem_set_image]
    rw [totalHomEquiv_apply]
    simp

/-- Arrow deletion commutes with transport, including loops and parallel arrows. -/
@[simp]
theorem subnetworkOrderIso_deleteArrows (e : N ≃ₙ N') (S : N.Subnetwork)
    (A : Set (Σ x y, N.Hom x y)) :
    e.subnetworkOrderIso (S.deleteArrows A) =
      (e.subnetworkOrderIso S).deleteArrows (e.totalHomEquiv '' A) := by
  apply Subnetwork.ext
  · simp
  · simp only [subnetworkOrderIso_arrowSet, Subnetwork.arrowSet_deleteArrows,
      Set.image_sdiff e.totalHomEquiv.injective]

/-- Restriction of a network isomorphism to a subnetwork and its image. The vertex type consists
only of selected vertices, and each selected arrow keeps both of its original bounds. -/
def subnetworkIso (e : N ≃ₙ N') (S : N.Subnetwork) :
    S.toNetwork ≃ₙ (e.subnetworkOrderIso S).toNetwork := by
  have hV (x : V) : x ∈ S.vertexSet ↔ e.vertexEquiv x ∈
      (e.subnetworkOrderIso S).vertexSet := by simp
  let eV := e.vertexEquiv.subtypeEquiv hV
  have heV (x : S.vertexSet) :
      eV x = ⟨e.vertexEquiv x, (hV x).mp x.property⟩ :=
    Equiv.subtypeEquiv_apply _ _ _
  have hA (x y : S.vertexSet) (a : N.Hom x y) :
      (⟨x.val, y.val, a⟩ : Σ x y, N.Hom x y) ∈ S.arrowSet ↔
        (⟨e.vertexEquiv x, e.vertexEquiv y, e.homEquiv x y a⟩ :
          Σ x y, N'.Hom x y) ∈ (e.subnetworkOrderIso S).arrowSet := by
    rw [subnetworkOrderIso_arrowSet, ← e.totalHomEquiv_apply ⟨x, y, a⟩]
    exact e.totalHomEquiv.injective.mem_set_image.symm
  let eA (x y : S.vertexSet) : S.Hom x y ≃
      {a : N'.Hom (e.vertexEquiv x) (e.vertexEquiv y) //
        (⟨e.vertexEquiv x, e.vertexEquiv y, a⟩ : Σ x y, N'.Hom x y) ∈
          (e.subnetworkOrderIso S).arrowSet} :=
    (e.homEquiv x y).subtypeEquiv (hA x y)
  have heA (x y : S.vertexSet) (a : S.Hom x y) :
      eA x y a = ⟨e.homEquiv x y a.val, (hA x y a.val).mp a.property⟩ :=
    Equiv.subtypeEquiv_apply _ _ _
  -- Explicit forward maps make the dependent endpoints and inherited bound formulas reduce.
  -- The generic subtype equivalences still supply the inverses and the inverse laws.
  refine {
    vertexEquiv := {
      toFun x := ⟨e.vertexEquiv x, (hV x).mp x.property⟩
      invFun := eV.symm
      left_inv x := (congrArg eV.symm (heV x)).symm.trans (eV.symm_apply_apply x)
      right_inv y := (heV (eV.symm y)).symm.trans (eV.apply_symm_apply y) }
    homEquiv := fun x y ↦ {
      toFun a := ⟨e.homEquiv x y a.val, (hA x y a.val).mp a.property⟩
      invFun := (eA x y).symm
      left_inv a := (congrArg (eA x y).symm (heA x y a)).symm.trans
        ((eA x y).symm_apply_apply a)
      right_inv a := (heA x y ((eA x y).symm a)).symm.trans
        ((eA x y).apply_symm_apply a) }
    map_lower := fun a ↦ e.map_lower a.val
    map_upper := fun a ↦ e.map_upper a.val }

/-- The restricted isomorphism uses the ambient vertex equivalence. -/
@[simp]
theorem subnetworkIso_vertexEquiv_apply (e : N ≃ₙ N') (S : N.Subnetwork)
    (x : S.vertexSet) : ((e.subnetworkIso S).vertexEquiv x : W) = e.vertexEquiv x :=
  (rfl)

/-- The restricted isomorphism uses the ambient arrow equivalence on each selected arrow,
after identifying its endpoints with the ambient images. -/
theorem subnetworkIso_homEquiv_apply (e : N ≃ₙ N') (S : N.Subnetwork)
    (x y : S.vertexSet) (a : S.Hom x y) :
    @Quiver.homOfEq W ⟨N'.Hom⟩ _ _ _ _ ((e.subnetworkIso S).homEquiv x y a).val
      (subnetworkIso_vertexEquiv_apply e S x) (subnetworkIso_vertexEquiv_apply e S y) =
        e.homEquiv x y a.val :=
  (rfl)

end TauCeti.Network.Iso
